/* TCP Inigo congestion control.
 *
 * This is an implementation of TCP Inigo, which takes the measure of
 * the extent of congestion introduced in DCTCP and applies it to
 * networks outside the data center.
 *
 * https://www.soe.ucsc.edu/research/technical-reports/UCSC-SOE-14-14
 *
 * The motivation behind the RTT fairness functionality comes from
 * the 2nd DCTCP paper listed below.
 *
 * The motivation behind the stabilize functionality comes from:
 *
 * Alizadeh, Mohammad, et al.
 * "Stability analysis of QCN: the averaging principle."
 * Proceedings of the ACM SIGMETRICS joint international conference
 * on Measurement and modeling of computer systems. ACM, 2011.
 * http://sedcl.stanford.edu.oca.ucsc.edu/files/qcn-analysis.pdf
 *
 * Authors:
 *
 *	Andrew Shewmaker <agshew@gmail.com>
 *
 * Forked from DataCenter TCP (DCTCP) congestion control.
 *
 * http://simula.stanford.edu/~alizade/Site/DCTCP.html
 *
 * DCTCP is an enhancement to the TCP congestion control algorithm
 * designed for data centers. DCTCP leverages Explicit Congestion
 * Notification (ECN) in the network to provide multi-bit feedback to
 * the end hosts. DCTCP's goal is to meet the following three data
 * center transport requirements:
 *
 *  - High burst tolerance (incast due to partition/aggregate)
 *  - Low latency (short flows, queries)
 *  - High throughput (continuous data updates, large file transfers)
 *    with commodity shallow buffered switches
 *
 * The algorithm is described in detail in the following two papers:
 *
 * 1) Mohammad Alizadeh, Albert Greenberg, David A. Maltz, Jitendra Padhye,
 *    Parveen Patel, Balaji Prabhakar, Sudipta Sengupta, and Murari Sridharan:
 *      "Data Center TCP (DCTCP)", Data Center Networks session
 *      Proc. ACM SIGCOMM, New Delhi, 2010.
 *   http://simula.stanford.edu/~alizade/Site/DCTCP_files/dctcp-final.pdf
 *
 * 2) Mohammad Alizadeh, Adel Javanmard, and Balaji Prabhakar:
 *      "Analysis of DCTCP: Stability, Convergence, and Fairness"
 *      Proc. ACM SIGMETRICS, San Jose, 2011.
 *   http://simula.stanford.edu/~alizade/Site/DCTCP_files/dctcp_analysis-full.pdf
 *
 * Initial prototype from Abdul Kabbani, Masato Yasuda and Mohammad Alizadeh.
 *
 * DCTCP Authors:
 *
 *	Daniel Borkmann <dborkman@redhat.com>
 *	Florian Westphal <fw@strlen.de>
 *	Glenn Judd <glenn.judd@morganstanley.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or (at
 * your option) any later version.
 */

#include <linux/module.h>
#include <linux/mm.h>
#include <net/tcp.h>
#include <linux/inet_diag.h>

#define DCTCP_MAX_ALPHA	1024U
#define INIGO_MIN_FAIRNESS 4U
#define INIGO_MAX_FAIRNESS 100U
#define INIGO_MAX_MARK 1024U

struct inigo {
	u32 acked_bytes_ecn;
	u32 acked_bytes_total;
	u32 prior_snd_una;
	u32 prior_rcv_nxt;
	u16 dctcp_alpha;
	u32 next_seq;
	u8 ce_state;
	u32 delayed_ack_reserved;
	u32 rtt_min;
	u16 rtt_alpha;
	u32 rtts_late;
	u32 rtts_observed;
};

static unsigned int dctcp_shift_g __read_mostly = 4; /* g = 1/2^4 */
module_param(dctcp_shift_g, uint, 0644);
MODULE_PARM_DESC(dctcp_shift_g, "parameter g for updating dctcp_alpha");

static unsigned int dctcp_alpha_on_init __read_mostly = 0;
module_param(dctcp_alpha_on_init, uint, 0644);
MODULE_PARM_DESC(dctcp_alpha_on_init, "parameter for initial alpha value, "
		 " defaults to 0 out of 1024");

static unsigned int dctcp_clamp_alpha_on_loss __read_mostly;
module_param(dctcp_clamp_alpha_on_loss, uint, 0644);
MODULE_PARM_DESC(dctcp_clamp_alpha_on_loss,
		 "parameter for clamping alpha on loss");

static unsigned int suspect_rtt  __read_mostly = 10;
module_param(suspect_rtt, uint, 0644);
MODULE_PARM_DESC(suspect_rtt, "throw out RTTs smaller than X microseconds,"
		 " defaults to 10");

static unsigned int markthresh __read_mostly = 180;
module_param(markthresh, uint, 0644);
MODULE_PARM_DESC(markthresh, "delay marking threshhold, default=180 out of 1024");

static unsigned int min_rtt_samples_needed __read_mostly = 30;
module_param(min_rtt_samples_needed, uint, 0644);
MODULE_PARM_DESC(min_rtt_samples_needed, "minimum number of RTT samples needed"
		 " to exit slowstart, default=30");

static unsigned int minor_congestion __read_mostly = 10;
module_param(minor_congestion, uint, 0644);
MODULE_PARM_DESC(minor_congestion, "anything below X is considered minor,"
		 " and slowstart will continue, default=10 out of 1024");

static unsigned int rtt_fairness  __read_mostly = 0;
module_param(rtt_fairness, uint, 0644);
MODULE_PARM_DESC(rtt_fairness, "If non-zero, react to congestion every x acks,"
		 " 3 < x < 101. Defaults to 0, indicating once per window");

static bool stabilize  __read_mostly = false;
module_param(stabilize, bool, 0644);
MODULE_PARM_DESC(stabilize, "stabilize congestion response by alternating normal response"
			 " with averaged response, defaults to false");


static void dctcp_reset(const struct tcp_sock *tp, struct inigo *ca)
{
	ca->next_seq = tp->snd_nxt;

	ca->acked_bytes_ecn = 0;
	ca->acked_bytes_total = 0;
}

static void inigo_init(struct sock *sk)
{
	const struct tcp_sock *tp = tcp_sk(sk);
	struct inigo *ca = inet_csk_ca(sk);

	if (rtt_fairness != 0)
		rtt_fairness = clamp(rtt_fairness, INIGO_MIN_FAIRNESS, INIGO_MAX_FAIRNESS);

	ca->rtt_min = USEC_PER_SEC;
	ca->rtt_alpha = min(dctcp_alpha_on_init, DCTCP_MAX_ALPHA);
	ca->rtts_late = 0;
	ca->rtts_observed = 0;

	if ((tp->ecn_flags & TCP_ECN_OK) ||
	    (sk->sk_state == TCP_LISTEN ||
	     sk->sk_state == TCP_CLOSE)) {
		ca->prior_snd_una = tp->snd_una;
		ca->prior_rcv_nxt = tp->rcv_nxt;

		ca->dctcp_alpha = min(dctcp_alpha_on_init, DCTCP_MAX_ALPHA);

		ca->delayed_ack_reserved = 0;
		ca->ce_state = 0;

		dctcp_reset(tp, ca);
		return;
	}

	/* No ECN support? Fall back to other congestion control methods.
	 * Also need to clear ECT from sk since it is set during 3WHS for DCTCP.
	 */
	ca->dctcp_alpha = 0;
	INET_ECN_dontxmit(sk);
}

static u32 inigo_ssthresh(struct sock *sk)
{
	const struct inigo *ca = inet_csk_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);
	u32 alpha = max(ca->dctcp_alpha, ca->rtt_alpha);

	if (alpha < minor_congestion)
		return tp->snd_cwnd;

	if (rtt_fairness &&
	    tp->snd_cwnd_cnt > INIGO_MIN_FAIRNESS &&
	    tp->snd_cwnd_cnt % rtt_fairness == 0)
		return max(tp->snd_cwnd - ((tp->snd_cwnd * alpha) >> 11U) / rtt_fairness, 2U);

	return max(tp->snd_cwnd - ((tp->snd_cwnd * alpha) >> 11U), 2U);
}

/* Minimal DCTP CE state machine:
 *
 * S:	0 <- last pkt was non-CE
 *	1 <- last pkt was CE
 */

static void dctcp_ce_state_0_to_1(struct sock *sk)
{
	struct inigo *ca = inet_csk_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);

	/* State has changed from CE=0 to CE=1 and delayed
	 * ACK has not sent yet.
	 */
	if (!ca->ce_state && ca->delayed_ack_reserved) {
		u32 tmp_rcv_nxt;

		/* Save current rcv_nxt. */
		tmp_rcv_nxt = tp->rcv_nxt;

		/* Generate previous ack with CE=0. */
		tp->ecn_flags &= ~TCP_ECN_DEMAND_CWR;
		tp->rcv_nxt = ca->prior_rcv_nxt;

		tcp_send_ack(sk);

		/* Recover current rcv_nxt. */
		tp->rcv_nxt = tmp_rcv_nxt;
	}

	ca->prior_rcv_nxt = tp->rcv_nxt;
	ca->ce_state = 1;

	tp->ecn_flags |= TCP_ECN_DEMAND_CWR;
}

static void dctcp_ce_state_1_to_0(struct sock *sk)
{
	struct inigo *ca = inet_csk_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);

	/* State has changed from CE=1 to CE=0 and delayed
	 * ACK has not sent yet.
	 */
	if (ca->ce_state && ca->delayed_ack_reserved) {
		u32 tmp_rcv_nxt;

		/* Save current rcv_nxt. */
		tmp_rcv_nxt = tp->rcv_nxt;

		/* Generate previous ack with CE=1. */
		tp->ecn_flags |= TCP_ECN_DEMAND_CWR;
		tp->rcv_nxt = ca->prior_rcv_nxt;

		tcp_send_ack(sk);

		/* Recover current rcv_nxt. */
		tp->rcv_nxt = tmp_rcv_nxt;
	}

	ca->prior_rcv_nxt = tp->rcv_nxt;
	ca->ce_state = 0;

	tp->ecn_flags &= ~TCP_ECN_DEMAND_CWR;
}

static void inigo_update_dctcp_alpha(struct sock *sk, u32 flags)
{
	const struct tcp_sock *tp = tcp_sk(sk);
	struct inigo *ca = inet_csk_ca(sk);
	u32 acked_bytes = tp->snd_una - ca->prior_snd_una;

	/* If ack did not advance snd_una, count dupack as MSS size.
	 * If ack did update window, do not count it at all.
	 */
	if (acked_bytes == 0 && !(flags & CA_ACK_WIN_UPDATE))
		acked_bytes = inet_csk(sk)->icsk_ack.rcv_mss;
	if (acked_bytes) {
		ca->acked_bytes_total += acked_bytes;
		ca->prior_snd_una = tp->snd_una;

		if (flags & CA_ACK_ECE)
			ca->acked_bytes_ecn += acked_bytes;
	}

	/* Expired RTT */
	if (!before(tp->snd_una, ca->next_seq)) {
		/* For avoiding denominator == 1. */
		if (ca->acked_bytes_total == 0)
			ca->acked_bytes_total = 1;

		/* alpha = (1 - g) * alpha + g * F */
		ca->dctcp_alpha = ca->dctcp_alpha -
				  (ca->dctcp_alpha >> dctcp_shift_g) +
				  (ca->acked_bytes_ecn << (10U - dctcp_shift_g)) /
				  ca->acked_bytes_total;

		if (ca->dctcp_alpha > DCTCP_MAX_ALPHA)
			/* Clamp dctcp_alpha to max. */
			ca->dctcp_alpha = DCTCP_MAX_ALPHA;

		dctcp_reset(tp, ca);
	}
}

static void inigo_update_rtt_alpha(struct inigo *ca)
{
	if (!ca->rtts_observed)
		return;

	ca->rtt_alpha = ca->rtt_alpha -
			(ca->rtt_alpha >> dctcp_shift_g) +
			(ca->rtts_late << (10U - dctcp_shift_g)) /
			ca->rtts_observed;

	if (ca->rtt_alpha > DCTCP_MAX_ALPHA)
		ca->rtt_alpha = DCTCP_MAX_ALPHA;

	ca->rtts_late = 0;
	ca->rtts_observed = 0;
}

static void inigo_state(struct sock *sk, u8 new_state)
{
	if (dctcp_clamp_alpha_on_loss && new_state == TCP_CA_Loss) {
		struct inigo *ca = inet_csk_ca(sk);
		/* If this extension is enabled, we clamp dctcp_alpha to
		 * max on packet loss; the motivation is that dctcp_alpha
		 * is an indicator to the extend of congestion and packet
		 * loss is an indicator of extreme congestion; setting
		 * this in practice turned out to be beneficial, and
		 * effectively assumes total congestion which reduces the
		 * window by half.
		 */
		ca->dctcp_alpha = DCTCP_MAX_ALPHA;
	}
}

static void dctcp_update_ack_reserved(struct sock *sk, enum tcp_ca_event ev)
{
	struct inigo *ca = inet_csk_ca(sk);

	switch (ev) {
	case CA_EVENT_DELAYED_ACK:
		if (!ca->delayed_ack_reserved)
			ca->delayed_ack_reserved = 1;
		break;
	case CA_EVENT_NON_DELAYED_ACK:
		if (ca->delayed_ack_reserved)
			ca->delayed_ack_reserved = 0;
		break;
	default:
		/* Don't care for the rest. */
		break;
	}
}

static void inigo_cwnd_event(struct sock *sk, enum tcp_ca_event ev)
{
	switch (ev) {
	case CA_EVENT_ECN_IS_CE:
		dctcp_ce_state_0_to_1(sk);
		break;
	case CA_EVENT_ECN_NO_CE:
		dctcp_ce_state_1_to_0(sk);
		break;
	case CA_EVENT_DELAYED_ACK:
	case CA_EVENT_NON_DELAYED_ACK:
		dctcp_update_ack_reserved(sk, ev);
		break;
	default:
		/* Don't care for the rest. */
		break;
	}
}

/* The cwnd reduction in CWR and Recovery use the PRR algorithm
 * https://datatracker.ietf.org/doc/draft-ietf-tcpm-proportional-rate-reduction/
 * It computes the number of packets to send (sndcnt) based on packets newly
 * delivered:
 *   1) If the packets in flight is larger than ssthresh, PRR spreads the
 *      cwnd reductions across a full RTT.
 *   2) If packets in flight is lower than ssthresh (such as due to excess
 *      losses and/or application stalls), do not perform any further cwnd
 *      reductions, but instead slow start up to ssthresh.
 */
static void inigo_init_cwnd_reduction(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	tp->high_seq = tp->snd_nxt;
	tp->tlp_high_seq = 0;
	tp->snd_cwnd_cnt = 0;
	tp->prior_cwnd = tp->snd_cwnd;
	tp->prr_delivered = 0;
	tp->prr_out = 0;
	tp->snd_ssthresh = inigo_ssthresh(sk);
}

/* Enter CWR state. Disable cwnd undo since congestion is proven with ECN or Delay */
void inigo_enter_cwr(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	tp->prior_ssthresh = 0;
	if (inet_csk(sk)->icsk_ca_state < TCP_CA_CWR) {
		tp->undo_marker = 0;
		inigo_init_cwnd_reduction(sk);
		tcp_set_ca_state(sk, TCP_CA_CWR);
	}
}

u32 inigo_slow_start(struct tcp_sock *tp, u32 acked)
{
	u32 cwnd = tp->snd_cwnd + acked;

	if (cwnd > tp->snd_ssthresh)
		cwnd = tp->snd_ssthresh + 1;
	acked -= cwnd - tp->snd_cwnd;
	tp->snd_cwnd = min(cwnd, tp->snd_cwnd_clamp);

	return acked;
}

void inigo_cong_avoid_ai(struct sock *sk, u32 w, u32 acked)
{
	struct inigo *ca = inet_csk_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);
	u32 interval;

	if (tp->snd_cwnd_cnt >= w) {
		if (tp->snd_cwnd < tp->snd_cwnd_clamp)
			tp->snd_cwnd++;
	}

	if (tp->snd_cwnd_cnt > INIGO_MIN_FAIRNESS) {
		if (rtt_fairness == 0)
			interval = w;
		else
			interval = rtt_fairness;

		if (tp->snd_cwnd_cnt % interval == 0 || tp->snd_cwnd_cnt >= w) {
			inigo_update_rtt_alpha(ca);

			if (ca->rtt_alpha > minor_congestion)
				inigo_enter_cwr(sk);
		}
		else if (stabilize && tp->snd_cwnd_cnt % (interval >> 1) == 0) {
			tp->snd_cwnd = (tp->prior_cwnd + w + 1)/2;
		}
	}

	if (tp->snd_cwnd_cnt < w) {
		tp->snd_cwnd_cnt += acked;
	}
}

void inigo_cong_avoid(struct sock *sk, u32 ack, u32 acked)
{
	struct inigo *ca = inet_csk_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);
	u32 alpha = max(ca->dctcp_alpha, ca->rtt_alpha);

	if (!tcp_is_cwnd_limited(sk)) {
		return;
	}

	/* ssthresh should be increased when minor congestion is detected */
	if (tp->snd_cwnd == tp->snd_ssthresh && alpha < minor_congestion) {
		tp->snd_ssthresh = tp->snd_ssthresh << 1;
		pr_debug_ratelimited("tcp_inigo: continuing slowstart snd_ssthresh=%u, alpha=%u\n",
				tp->snd_ssthresh, alpha);
	}

	/* In "safe" area, increase. */
	if (tp->snd_cwnd <= tp->snd_ssthresh) {
		acked = inigo_slow_start(tp, acked);
		if (!acked)
			return;
	}
	/* In dangerous area, increase slowly. */
	inigo_cong_avoid_ai(sk, tp->snd_cwnd, acked);
}

static void inigo_pkts_acked(struct sock *sk, u32 num_acked, s32 rtt)
{
	struct inigo *ca = inet_csk_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);

	/* Some calls are for duplicates without timetamps */
	if (rtt <= 0)
		return;

	ca->rtts_observed++;

	ca->rtt_min = min((u32) rtt, ca->rtt_min);
	if (ca->rtt_min < suspect_rtt) {
		pr_debug_ratelimited("tcp_inigo: rtt_min=%u is suspiciously low, setting to rtt=%u\n",
					ca->rtt_min, (u32) rtt);
		ca->rtt_min = rtt;
	}

	/* Mimic DCTCP's ECN marking threshhold of approximately 0.17*BDP */
	if ((u32) rtt > (ca->rtt_min + (markthresh * ca->rtt_min / INIGO_MAX_MARK))) {
		u32 rtt_samples_needed = ca->rtts_observed * markthresh / INIGO_MAX_MARK;
		ca->rtts_late++;

		/* Don't prematurely exit slowstart */
		if (tp->snd_cwnd < tp->snd_ssthresh &&
		    ca->rtts_late > max(rtt_samples_needed, min_rtt_samples_needed)) {
			pr_debug_ratelimited("tcp_inigo: exiting slowstart? rtts_late=%u, snd_cwnd=%u\n",
					ca->rtts_late, tp->snd_cwnd);
			inigo_update_rtt_alpha(ca);
			if (ca->rtt_alpha > minor_congestion) {
				tp->snd_ssthresh = tp->snd_cwnd;
				pr_debug_ratelimited("tcp_inigo: yes, exiting slowstart alpha=%u\n", ca->rtt_alpha);
			}
		}
	}
}

/* Put in include/uapi/linux/inet_diag.h */
/* INET_DIAG_INIGOINFO */

#define INET_DIAG_INIGOINFO 10

struct tcp_inigo_info {
	__u16   dctcp_enabled;
	__u8   dctcp_ce_state;
	__u16   dctcp_alpha;
	__u32   dctcp_ab_ecn;
	__u32   dctcp_ab_tot;
	__u32   rtt_min;
	__u16   rtt_alpha;
	__u32   rtts_late;
	__u32   rtts_observed;
};

static void inigo_get_info(struct sock *sk, u32 ext, struct sk_buff *skb)
{
	struct tcp_sock *tp = tcp_sk(sk);
	const struct inigo *ca = inet_csk_ca(sk);

	/* Fill it also in case of VEGASINFO due to req struct limits.
	 * We can still correctly retrieve it later.
	 */
	if (ext & (1 << (INET_DIAG_INIGOINFO - 1)) ||
	    ext & (1 << (INET_DIAG_VEGASINFO - 1))) {
		struct tcp_inigo_info info;

		memset(&info, 0, sizeof(info));
		if ((tp->ecn_flags & TCP_ECN_OK)) {
			info.dctcp_enabled = 1;
			info.dctcp_ce_state = (u8) ca->ce_state;
			info.dctcp_alpha = ca->dctcp_alpha;
			info.dctcp_ab_ecn = ca->acked_bytes_ecn;
			info.dctcp_ab_tot = ca->acked_bytes_total;
			info.rtt_min = ca->rtt_min;
			info.rtt_alpha = ca->rtt_alpha;
			info.rtts_late = ca->rtts_late;
			info.rtts_observed = ca->rtts_observed;
		} else {
			info.dctcp_enabled = 0;
			info.dctcp_ce_state = (u8) 0;
			info.dctcp_alpha = ca->dctcp_alpha;
			info.dctcp_ab_ecn = ca->acked_bytes_ecn;
			info.dctcp_ab_tot = ca->acked_bytes_total;
			info.rtt_min = ca->rtt_min;
			info.rtt_alpha = ca->rtt_alpha;
			info.rtts_late = ca->rtts_late;
			info.rtts_observed = ca->rtts_observed;
		}

		nla_put(skb, INET_DIAG_INIGOINFO, sizeof(info), &info);
	}
}

static struct tcp_congestion_ops inigo __read_mostly = {
	.init		= inigo_init,
	.in_ack_event   = inigo_update_dctcp_alpha,
	.cwnd_event	= inigo_cwnd_event,
	.ssthresh	= inigo_ssthresh,
	.cong_avoid	= inigo_cong_avoid,
	.pkts_acked 	= inigo_pkts_acked,
	.set_state	= inigo_state,
	.get_info	= inigo_get_info,
	.owner		= THIS_MODULE,
	.name		= "inigo",
};

static int __init inigo_register(void)
{
	BUILD_BUG_ON(sizeof(struct inigo) > ICSK_CA_PRIV_SIZE);
	return tcp_register_congestion_control(&inigo);
}

static void __exit inigo_unregister(void)
{
	tcp_unregister_congestion_control(&inigo);
}

module_init(inigo_register);
module_exit(inigo_unregister);

MODULE_AUTHOR("Andrew Shewmaker <ashewmaker@gmail.com>");
MODULE_AUTHOR("Daniel Borkmann <dborkman@redhat.com>");
MODULE_AUTHOR("Florian Westphal <fw@strlen.de>");
MODULE_AUTHOR("Glenn Judd <glenn.judd@morganstanley.com>");

MODULE_LICENSE("GPL v2");
MODULE_DESCRIPTION("TCP Inigo");
