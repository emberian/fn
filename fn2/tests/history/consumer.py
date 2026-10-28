"""Consumer protocol safety witnesses, from specs/consumer-progress.md."""
import json

from .history import HistoryError, anomaly, pair

CONSUMER = {'register', 'rebase', 'unregister', 'ack', 'position', 'poll', 'wait'}


def key(op):
    v = op.value
    return (op.node, v['consumer'], v['epoch'], json.dumps(v['scope'], sort_keys=True))


def before(a, b):
    return a.completion.index < b.invoke.index


def check(history, *, slack_ns=0):
    if type(slack_ns) is not int or slack_ns < 0:
        raise ValueError('slack_ns must be a nonnegative integer')
    ops = pair(history)
    cs = [o for o in ops if o.f in CONSUMER and not o.value.get('observed_only')]
    for o in cs:
        required = {'consumer', 'epoch', 'scope'}
        if o.f == 'ack' or o.type == 'ok' and o.f in {'register', 'rebase', 'position'}:
            required.add('position')
        if o.f in {'poll', 'wait'}:
            required.add('cursor')
            if o.type == 'ok':
                required.update(('position', 'events', 'more'))
        if o.f == 'wait':
            required.add('deadline')
        if required - o.value.keys():
            raise HistoryError('consumer-evidence', o.invoke.index,
                               str(sorted(required - o.value.keys())))
        for field in ('position', 'cursor', 'deadline'):
            if field in o.value and (type(o.value[field]) is not int or o.value[field] < 0):
                raise HistoryError('consumer-evidence', o.invoke.index, field)
    result = []
    groups = {}
    for o in cs:
        groups.setdefault(key(o), []).append(o)

    def covering(group, p, page, overlap=False):
        for a in group:
            eligible = a.invoke.index < page.completion.index if overlap else before(a, page)
            if a.f != 'ack' or a.value['position'] < p or not eligible:
                continue
            if a.type == 'ok':
                return True
            if a.type == 'info' and any(x.f == 'position' and x.type == 'ok'
                    and before(a, x) and x.value['position'] >= a.value['position']
                    for x in group):
                return True
        return False

    for group in groups.values():
        for o in group:
            v = o.value
            if o.type != 'ok':
                continue
            prior = [a for a in group if before(a, o)]
            acks = [a for a in prior if a.f == 'ack' and a.type == 'ok']
            confirmed = [a for a in prior if a.f == 'position' and a.type == 'ok']
            floor_ops = acks + confirmed
            floor = max((a.value['position'] for a in floor_ops), default=0)
            if o.f == 'ack':
                # Old registrations and scopes remain separate for progress checks.
                fenced = [a for a in cs if a.node == o.node
                          and a.value['consumer'] == v['consumer'] and before(a, o)
                          and a.type == 'ok' and
                          (a.f == 'unregister' and key(a) == key(o) or
                           a.f in {'register', 'rebase'} and key(a) != key(o)
                           and any(b.f in {'register', 'rebase'} and key(b) == key(o)
                                   and before(b, a) for b in cs))]
                if fenced:
                    result.append(anomaly('C5', 'old epoch/scope ack accepted', fenced[-1], o))
                elif v['position'] < floor:
                    result.append(anomaly('C1', 'lower ack accepted', max(floor_ops, key=lambda a: a.value['position']), o))
            if o.f == 'position':
                bases = [a for a in prior if a.f in {'register', 'rebase', 'position'}
                         and a.type == 'ok']
                base = bases[-1].value['position'] if bases else 0
                possible = [a for a in group if a.f == 'ack' and a.type in {'ok', 'info'}
                            and a.invoke.index < o.completion.index]
                ceiling = max([base, floor] + [a.value['position'] for a in possible])
                polls = [a for a in prior if a.f in {'poll', 'wait'} and a.type == 'ok'
                         and (not bases or before(bases[-1], a))]
                targets = {base, floor} | {a.value['position'] for a in possible}
                if v['position'] < floor:
                    result.append(anomaly('C1', 'durable ack regressed', max(floor_ops, key=lambda a: a.value['position']), o))
                elif v['position'] > ceiling or v['position'] not in targets:
                    kind = 'C6' if polls else 'C1'
                    witness = polls[-1:] or possible[-1:] or bases[-1:]
                    result.append(anomaly(kind, 'position changed without a possible ack', *witness, o))
            if o.f not in {'poll', 'wait'}:
                continue
            events, cursor, end = v['events'], v['cursor'], v['position']
            positions = [p for p, mid in events]
            if (end < cursor or any(p > end for p in positions)
                    or any(a >= b for a, b in zip(positions, positions[1:]))):
                result.append(anomaly('C2', 'invalid scanned page order/continuation', o))
            if any(p <= cursor for p in positions):
                result.append(anomaly('C4' if o.f == 'wait' else 'C2',
                                      'event not after request cursor', o))
            if any(p <= floor for p in positions) and acks:
                result.append(anomaly('C3', 'acked event redelivered', acks[-1], o))
            for old in prior:
                if old.f not in {'poll', 'wait'} or old.type != 'ok':
                    continue
                for p, mid in old.value['events']:
                    if p <= floor or covering(group, p, o, overlap=True):
                        continue
                    if cursor >= p or end >= p and [p, mid] not in [list(e) for e in events]:
                        result.append(anomaly('C2', 'unacked event skipped', old, o))
            if o.f == 'wait' and not events:
                if o.completion.time < v['deadline']:
                    result.append(anomaly('C4', 'empty wait before deadline', o))
                else:
                    for post in ops:
                        if (post.f != 'post' or post.type != 'ok' or post.node != o.node
                                or post.completion.time >= min(o.invoke.time + slack_ns, v['deadline'])):
                            continue
                        for visible in post.value.get('visible', []):
                            if (visible['consumer'] == v['consumer'] and visible['epoch'] == v['epoch']
                                    and visible['scope'] == v['scope']
                                    and visible['position'] > max(cursor, floor)
                                    and not covering(group, visible['position'], o, overlap=True)):
                                result.append(anomaly('C4', 'lost wake', post, o))
    return list(dict.fromkeys(result))
