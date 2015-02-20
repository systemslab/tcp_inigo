/* TCP Inigo congestion control.
 *
 * This is an implementation of TCP Inigo, which takes the measure of
 * the extent of congestion introduced in DCTCP and applies it to
 * networks outside the data center, including wireless.
 *
 * https://www.soe.ucsc.edu/research/technical-reports/UCSC-SOE-14-14
 *
 * The motivation behind the "dampen" functionality comes from:
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

struct inigo {
	u32 acked_bytes_ecn;
	u32 acked_bytes_total;
	u32 prior_snd_una;
	u32 prior_rcv_nxt;
	u32 dctcp_alpha;
	u32 next_seq;
	u32 ce_state;
	u32 delayed_ack_reserved;
	u32 rtt_min;
	u32 rtt_alpha;
	u32 delayed_cnt;
};

static unsigned int dctcp_shift_g __read_mostly = 4; /* g = 1/2^4 */
module_param(dctcp_shift_g, uint, 0644);
MODULE_PARM_DESC(dctcp_shift_g, "parameter g for updating dctcp_alpha");

static unsigned int dctcp_alpha_on_init __read_mostly = DCTCP_MAX_ALPHA;
module_param(dctcp_alpha_on_init, uint, 0644);
MODULE_PARM_DESC(dctcp_alpha_on_init, "parameter for initial alpha value");

static unsigned int dctcp_clamp_alpha_on_loss __read_mostly;
module_param(dctcp_clamp_alpha_on_loss, uint, 0644);
MODULE_PARM_DESC(dctcp_clamp_alpha_on_loss,
		 "parameter for clamping alpha on loss");

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

	if ((tp->ecn_flags & TCP_ECN_OK) ||
	    (sk->sk_state == TCP_LISTEN ||
	     sk->sk_state == TCP_CLOSE)) {
		ca->prior_snd_una = tp->snd_una;
		ca->prior_rcv_nxt = tp->rcv_nxt;

		ca->dctcp_alpha = min(dctcp_alpha_on_init, DCTCP_MAX_ALPHA);

		ca->rtt_min = USEC_PER_SEC;
		ca->rtt_alpha = min(dctcp_alpha_on_init, DCTCP_MAX_ALPHA);

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

	pr_debug_ratelimited("tcp_inigo: ssthresh: snd_cwnd=%u, snd_ssthresh=%u, alpha=%u, return=%u", tp->snd_cwnd, tp->snd_ssthresh, alpha, max(tp->snd_cwnd - ((tp->snd_cwnd * alpha) >> 11U), 2U));
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

static void inigo_update_alpha(struct sock *sk, u32 flags)
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

void inigo_cong_avoid_ai(struct inigo *ca, struct tcp_sock *tp, u32 w)
{
	u32 alpha_old;

	if (tp->snd_cwnd_cnt >= w) {
		if (tp->snd_cwnd < tp->snd_cwnd_clamp)
			tp->snd_cwnd++;

		alpha_old = ca->rtt_alpha;

		ca->rtt_alpha = ca->rtt_alpha -
				(alpha_old >> dctcp_shift_g) +
				(ca->delayed_cnt << (10U - dctcp_shift_g)) /
				tp->snd_cwnd_cnt;

		if (ca->rtt_alpha > DCTCP_MAX_ALPHA)
			ca->rtt_alpha = DCTCP_MAX_ALPHA;

		pr_debug_ratelimited("tcp_inigo: cong_avoid_ai: delayed_cnt=%u, w=%u, rtt_alpha=%u", ca->delayed_cnt, w, ca->rtt_alpha);
		tp->snd_cwnd_cnt = 0;
		ca->delayed_cnt = 0;
	} else {
		tp->snd_cwnd_cnt++;
		pr_debug_ratelimited("tcp_inigo: cong_avoid_ai: snd_cwnd_cnt=%u, w=%u", tp->snd_cwnd_cnt, w);
	}
}

void inigo_cong_avoid(struct sock *sk, u32 ack, u32 acked)
{
	struct inigo *ca = inet_csk_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);

/* This seems to prevent both slowstart and congavoid ...
	if (!tcp_is_cwnd_limited(sk)) {
		pr_debug_ratelimited("tcp_inigo: cong_avoid: !tcp_is_cwnd_limited, snd_cwnd=%u, snd_ssthresh=%u, max_packets_out=%u", tp->snd_cwnd, tp->snd_ssthresh, tp->max_packets_out);
		return;
	}
 */

	/* In "safe" area, increase. */
	if (tp->snd_cwnd <= tp->snd_ssthresh) {
		tcp_slow_start(tp, acked);
		pr_debug_ratelimited("tcp_inigo: cong_avoid: slowstart snd_cwnd=%u, snd_ssthresh=%u", tp->snd_cwnd, tp->snd_ssthresh);
	/* In dangerous area, increase slowly. */
	} else {
		pr_debug_ratelimited("tcp_inigo: cong_avoid: congavoid snd_cwnd=%u, snd_ssthresh=%u", tp->snd_cwnd, tp->snd_ssthresh);
		inigo_cong_avoid_ai(ca, tp, tp->snd_cwnd);
	}
}

static void inigo_pkts_acked(struct sock *sk, u32 num_acked, s32 rtt)
{
	struct inigo *ca = inet_csk_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);

	/* Some calls are for duplicates without timetamps */
	if (rtt <= 0)
		return;

	ca->rtt_min = min((u32) rtt, ca->rtt_min);

	/* Mimic DCTCP's ECN marking threshhold of approximately 0.17*BDP
	 * 11/64 = 0.171875
	 */
	if ((u32) rtt > (ca->rtt_min + (11 * ca->rtt_min >> 6))) {
		ca->delayed_cnt++;
		pr_debug_ratelimited("tcp_inigo: pkts_acked: delayed_cnt=%u, snd_cwnd_cnt=%u", ca->delayed_cnt, tp->snd_cwnd_cnt);

		/* Don't want to prematurely exit slowstart. 0.17*snd_cwnd >= 2 */
		if (tp->snd_cwnd >= 18 &&
		    tp->snd_cwnd <= tp->snd_ssthresh &&
		    ca->delayed_cnt >= (11 * tp->snd_cwnd >> 6)) {
			pr_debug_ratelimited("tcp_inigo: pkts_acked: set ssthresh delayed_cnt=%u, snd_cwnd=%u, thresh=%u", ca->delayed_cnt, tp->snd_cwnd, 11 * tp->snd_cwnd >> 6);
			//NET_INC_STATS_BH(sock_net(sk), LINUX_MIB_TCPHYSTARTDELAYDETECT);
			//NET_ADD_STATS_BH(sock_net(sk), LINUX_MIB_TCPHYSTARTDELAYCWND, tp->snd_cwnd);
			tp->snd_ssthresh = tp->snd_cwnd;
			ca->delayed_cnt = 0;
		} else {
			pr_debug_ratelimited("tcp_inigo: pkts_acked: leave ssthresh delayed_cnt=%u, snd_cwnd=%u, thresh=%u", ca->delayed_cnt, tp->snd_cwnd, 11 * tp->snd_cwnd >> 6);
		}
	} else {
		pr_debug_ratelimited("tcp_inigo: pkts_acked: not delayed rtt=%d <= rtt_min=%u + thresh=%u", rtt, ca->rtt_min, (11 * ca->rtt_min >> 6));
	}
}

/* Put in include/uapi/linux/inet_diag.h */
/* INET_DIAG_INIGOINFO */

#define INET_DIAG_INIGOINFO 10

struct tcp_inigo_info {
        __u16   dctcp_enabled;
        __u16   dctcp_ce_state;
        __u32   dctcp_alpha;
        __u32   dctcp_ab_ecn;
        __u32   dctcp_ab_tot;
        __u32   rtt_min;
        __u32   rtt_alpha;
        __u32   delayed_cnt;
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
			info.dctcp_ce_state = (u16) ca->ce_state;
			info.dctcp_alpha = ca->dctcp_alpha;
			info.dctcp_ab_ecn = ca->acked_bytes_ecn;
			info.dctcp_ab_tot = ca->acked_bytes_total;
			info.rtt_min = ca->rtt_min;
			info.rtt_alpha = ca->rtt_alpha;
			info.delayed_cnt = ca->delayed_cnt;
		} else {
			info.dctcp_enabled = 0;
			info.dctcp_ce_state = (u16) 0;
			info.dctcp_alpha = ca->dctcp_alpha;
			info.dctcp_ab_ecn = ca->acked_bytes_ecn;
			info.dctcp_ab_tot = ca->acked_bytes_total;
			info.rtt_min = ca->rtt_min;
			info.rtt_alpha = ca->rtt_alpha;
			info.delayed_cnt = ca->delayed_cnt;
		}

		nla_put(skb, INET_DIAG_INIGOINFO, sizeof(info), &info);
	}
}

static struct tcp_congestion_ops inigo __read_mostly = {
	.init		= inigo_init,
	.in_ack_event   = inigo_update_alpha,
	.cwnd_event	= inigo_cwnd_event,
	.ssthresh	= inigo_ssthresh,
	.cong_avoid	= inigo_cong_avoid,
	.pkts_acked 	= inigo_pkts_acked,
	.set_state	= inigo_state,
	.get_info	= inigo_get_info,
	.flags		= TCP_CONG_NEEDS_ECN,
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
