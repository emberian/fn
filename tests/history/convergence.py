"""Peering convergence over observed histories (H7; RELEASE-PLAN §2.2 H row for peering: "convergence model
(divergence 0; digest chain equal; no article accepted twice)").

Operations (from_observe.adapt): `post` and `transfer` (IHAVE) acceptances, `read` by Message-ID, `withdraw`
(an authorized cancel's local outcome), `crash`. Each node is judged on its own operations; divergence is
judged across nodes. The checks, each an anomaly kind:

  V1 accepted twice   one node accepts (240 or 235) the same Message-ID twice, with no authorized withdrawal
                      between (RFC 3977 8.3.2 / RFC 5537 3.3: a node that has an article refuses a second
                      offer of it, 435/437 for IHAVE, 441 for POST)
  V2 accepted, absent a node accepted an article (post or transfer) and a later read on that node answers
                      430/423 with no authorized withdrawal and no crash between (a transfer's 235 means the
                      node has it, RFC 3977 8.3.2)
  V3 changed          a later read on the accepting node serves another body than the one it accepted
  V4 divergence       two nodes serve the same Message-ID with different bodies (the body digest: Path and
                      Xref are the node's own, the body is the article's)

Withdrawn articles, crashes and uncertain outcomes excuse V2/V3 as in durable.py; V4 compares only reads
whose digest was observed. The checker never infers a topology: which node should have received an article
is the natives' own assertion, not this checker's.
"""
from .history import anomaly, pair

ACCEPTED = {'post': 240, 'transfer': 235}


def check(history):
    ops = pair(history)
    accepts = [o for o in ops if o.f in ACCEPTED and o.type == 'ok' and o.value.get('message_id')]
    reads = [o for o in ops if o.f == 'read' and o.type == 'ok' and o.value.get('message_id')]
    withdrawals = [o for o in ops if o.f == 'withdraw' and o.type == 'ok' and o.value.get('authorized') is True]
    crashes = [o for o in ops if o.f == 'crash' and o.type == 'ok']
    result = []

    def withdrawn_between(node, mid, start, end):
        return any(w.node == node and w.value.get('message_id') == mid and start < w.completion.index < end
                   for w in withdrawals)

    def crashed_between(node, start, end):
        return any(c.node == node and start <= c.completion.index < end for c in crashes)

    by_key = {}
    for o in sorted(accepts, key=lambda o: o.completion.index):
        key = (o.node, o.value['message_id'])
        first = by_key.get(key)
        if first is not None and not withdrawn_between(o.node, key[1], first.completion.index, o.invoke.index):
            result.append(anomaly('V1', 'article accepted twice on one node', first, o))
        else:
            by_key[key] = o
    for accepted in accepts:
        mid, node = accepted.value['message_id'], accepted.node
        for read in reads:
            if read.node != node or read.value.get('message_id') != mid:
                continue
            if read.invoke.index <= accepted.completion.index:
                continue
            if withdrawn_between(node, mid, accepted.invoke.index, read.invoke.index):
                continue
            if crashed_between(node, accepted.completion.index, read.invoke.index):
                continue        # durable.py judges recovery
            code = read.value.get('code')
            if code in (430, 423):
                result.append(anomaly('V2', 'accepted article read as absent on the accepting node', accepted, read))
            elif code in (220, 222) and accepted.value.get('digest') and read.value.get('digest') \
                    and read.value['digest'] != accepted.value['digest']:
                result.append(anomaly('V3', 'accepted article served with another body', accepted, read))
    seen = {}
    for read in reads:
        digest = read.value.get('digest')
        if not digest or read.value.get('code') not in (220, 222):
            continue
        mid = read.value['message_id']
        prior = seen.setdefault(mid, read)
        if prior.node != read.node and prior.value['digest'] != digest:
            result.append(anomaly('V4', 'two nodes serve one Message-ID with different bodies', prior, read))
    return result
