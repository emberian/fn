"""Durable POST observations under the honest-persistence profile (MODEL.md)."""
from .history import HistoryError, anomaly, pair


def check(history):
    ops = pair(history)
    posts = [o for o in ops if o.f == 'post' and not o.value.get('observed_only')]
    reads = [o for o in ops if o.f == 'read' and o.type == 'ok'
             and not o.value.get('observed_only')]
    result = []
    for o in posts + reads:
        required = {'message_id', 'digest'} if o.f == 'post' else {'message_id', 'code'}
        if required - o.value.keys():
            raise HistoryError('durable-evidence', o.invoke.index, str(required - o.value.keys()))
    for post in posts:
        v = post.value
        same = lambda o: o.node == post.node and o.value.get('message_id') == v['message_id']
        relevant = [r for r in reads if same(r) and r.invoke.index > post.completion.index]
        settled = None
        for read in relevant:
            withdrawals = [o for o in ops if o.f == 'withdraw' and o.type == 'ok' and same(o)
                           and o.value.get('authorized') is True
                           and post.invoke.index < o.completion.index < read.invoke.index]
            if withdrawals:
                continue
            crashes = [o for o in ops if o.f == 'crash' and o.type == 'ok' and o.node == post.node
                       and post.completion.index <= o.completion.index < read.invoke.index]
            recoveries = [o for o in ops if o.f == 'recover' and o.type == 'ok' and o.node == post.node
                          and o.value.get('posture') == 'ready' and o.completion.index < read.invoke.index
                          and crashes and crashes[-1].completion.index < o.invoke.index]
            absent = read.value['code'] in {430, 423}
            present = read.value['code'] in {220, 221, 222, 223}
            if not (absent or present):
                continue
            digest = read.value.get('digest')
            wrong = present and digest is not None and digest != v['digest']
            if post.type == 'ok' and recoveries and (absent or wrong):
                result.append(anomaly('D1', 'lost acknowledged post' if absent else
                                      'changed acknowledged post', post, crashes[0], recoveries[-1], read))
            alternatives = [p for p in posts if p != post and same(p) and p.type != 'fail'
                            and p.invoke.index < read.completion.index]
            if (post.type == 'fail' and v.get('reason') not in {'duplicate', 'conflict'}
                    and not alternatives and present):
                result.append(anomaly('D2', 'refused post later readable', post, read))
            if post.type == 'info' and recoveries:
                retried = any(p.invoke.index > post.invoke.index for p in alternatives)
                if retried:
                    continue
                outcome = 'absent' if absent else 'accepted'
                if wrong or settled is not None and settled[0] != outcome:
                    witnesses = [settled[1]] if settled else []
                    result.append(anomaly('D3', 'uncertain post has inconsistent settlement',
                                          post, *witnesses, read))
                settled = (outcome, read)
    return result
