"""Seeded spec histories and isolated mutation controls; no implementation calls."""
import random

from .history import Record


class Builder:
    def __init__(self, seed=0, history=()):
        self.random = random.Random(seed)
        self.history = list(history)
        self.time = self.history[-1].time if self.history else 0
        self.next_index = self.history[-1].index + 1 if self.history else 0

    def record(self, process, phase, f, value, *, at=None):
        self.time = max(self.time + self.random.randrange(1, 20), at or 0)
        r = Record(process, phase, f, value, self.time, self.next_index)
        self.next_index += 1
        self.history.append(r)
        return r

    def op(self, f, value, phase='ok', response=None, process='client', *, at=None):
        self.record(process, 'invoke', f, value)
        return self.record(process, phase, f, response or {}, at=at)

    def restart(self, node='default'):
        self.op('crash', {'node': node, 'cut': 'after-publication'}, process='nemesis')
        self.op('recover', {'node': node, 'posture': 'ready'}, process='nemesis')


def registration(name='c', epoch=1, node='default', view=0):
    return dict(node=node, consumer=name, epoch=epoch,
                scope=dict(history=node, incarnation='original', principal='owner',
                           query='fn.test', query_version=1, view_version=view))


def valid(seed):
    b = Builder(seed)
    count = b.random.randrange(2, 5)
    consumers = [registration(f'c{i}') for i in range(count)]
    progress = [0] * count
    published = []
    b.op('recover', {'posture': 'ready'}, process='nemesis')
    for c in consumers:
        b.op('register', c, response={'position': 0}, process=c['consumer'])
    for turn in range(b.random.randrange(4, 10)):
        p, mid = turn + 1, f'<{seed}-{turn}@history.test>'
        visible = [dict(consumer=c['consumer'], epoch=c['epoch'], scope=c['scope'], position=p)
                   for c in consumers]
        post = dict(message_id=mid, digest=f'body-{seed}-{turn}', visible=visible)
        b.op('post', post, response={'code': 240}, process='poster')
        published.append([p, mid])
        order = list(range(count))
        b.random.shuffle(order)
        for i in order:
            c = consumers[i]
            page = [e for e in published if e[0] > progress[i]]
            f = b.random.choice(['poll', 'wait'])
            req = c | {'cursor': progress[i]}
            if f == 'wait':
                req['deadline'] = b.time + 500
            b.op(f, req, response={'events': page, 'position': p, 'more': False}, process=c['consumer'])
            if b.random.choice([True, False]):
                b.op('poll', c | {'cursor': progress[i]}, response={
                    'events': page, 'position': p, 'more': False}, process=c['consumer'])
            if b.random.randrange(3):
                info = b.random.randrange(4) == 0
                b.op('ack', c | {'position': p}, phase='info' if info else 'ok', process=c['consumer'])
                if info:
                    b.restart()
                progress[i] = p
                b.op('position', c, response={'position': p}, process=c['consumer'])
        if b.random.randrange(3) == 0:
            b.restart()
            for n, message in published:
                b.op('read', {'message_id': message}, response={
                    'code': 220, 'digest': f'body-{seed}-{n-1}'}, process='reader')
    # A crash completes multiple outstanding processes as info, including a POST.
    uncertain = dict(message_id=f'<unknown-{seed}@history.test>', digest='unknown-body')
    b.record('poster', 'invoke', 'post', uncertain)
    b.record('reader', 'invoke', 'read', {'message_id': uncertain['message_id']})
    b.restart()
    accepted = b.random.choice([True, False])
    answer = {'code': 220, 'digest': 'unknown-body'} if accepted else {'code': 430}
    for _ in range(2):
        b.op('read', {'message_id': uncertain['message_id']}, response=answer, process='reader')
    refused = {'message_id': f'<refused-{seed}@history.test>', 'digest': 'refused-body'}
    b.op('post', refused, phase='fail', response={'code': 441, 'reason': 'malformed'})
    b.op('read', {'message_id': refused['message_id']}, response={'code': 430})
    # Scoped reset and delayed token probe, independent of old progress.
    old = consumers[0]
    b.op('unregister', old)
    new = registration(old['consumer'], 2)
    b.op('register', new, response={'position': 0})
    b.op('ack', old | {'position': progress[0]}, phase='fail', response={'reason': 'scope'})
    rebased = registration(old['consumer'], 2, view=1)
    b.op('rebase', rebased, response={'position': 0})
    b.op('position', rebased, response={'position': 0})
    return b.history


def _mutation(seed):
    b = Builder(seed ^ 0xBA5E, valid(seed))
    c = registration(f'mutant-{seed}', node='mutation')
    b.op('register', c, response={'position': 0})
    return b, c


def lowered_ack(seed):
    b, c = _mutation(seed)
    b.op('ack', c | {'position': 2})
    b.op('ack', c | {'position': 1})
    return b.history


def skipped_redelivery(seed):
    b, c = _mutation(seed)
    b.op('poll', c | {'cursor': 0}, response={'events': [[1, '<lost>']], 'position': 1, 'more': False})
    b.op('poll', c | {'cursor': 2}, response={'events': [], 'position': 2, 'more': False})
    return b.history


def redelivery_after_ack(seed):
    b, c = _mutation(seed)
    b.op('ack', c | {'position': 2})
    b.op('poll', c | {'cursor': 0}, response={'events': [[1, '<again>']], 'position': 1, 'more': False})
    return b.history


def lost_wake(seed):
    b, c = _mutation(seed)
    b.op('post', {'node': 'mutation', 'message_id': '<wake>', 'digest': 'wake',
                 'visible': [dict(consumer=c['consumer'], epoch=c['epoch'], scope=c['scope'], position=1)]},
         response={'code': 240})
    deadline = b.time + 1000
    b.op('wait', c | {'cursor': 0, 'deadline': deadline},
         response={'events': [], 'position': 0, 'more': False}, at=deadline)
    return b.history


def old_epoch_ack(seed):
    b, c = _mutation(seed)
    b.op('unregister', c)
    b.op('register', c | {'epoch': 2}, response={'position': 0})
    b.op('ack', c | {'position': 0})
    return b.history


def poll_moves_position(seed):
    b, c = _mutation(seed)
    b.op('position', c, response={'position': 0})
    b.op('poll', c | {'cursor': 0}, response={'events': [[1, '<poll>']], 'position': 1, 'more': False})
    b.op('position', c, response={'position': 1})
    return b.history


def _post_mutation(seed, phase):
    b = Builder(seed, valid(seed))
    v = {'node': 'mutation', 'message_id': f'<mutant-{seed}>', 'digest': 'payload'}
    b.op('post', v, phase=phase, response={'code': 240 if phase == 'ok' else 441,
                                        'reason': 'refused' if phase == 'fail' else None})
    return b, v


def lost_acknowledged_post(seed):
    b, v = _post_mutation(seed, 'ok')
    b.restart('mutation')
    b.op('read', {'node': 'mutation', 'message_id': v['message_id']}, response={'code': 430})
    return b.history


def refused_readable(seed):
    b, v = _post_mutation(seed, 'fail')
    b.op('read', {'node': 'mutation', 'message_id': v['message_id']}, response={'code': 220, 'digest': 'payload'})
    return b.history


def inconsistent_uncertain(seed):
    b, v = _post_mutation(seed, 'info')
    b.restart('mutation')
    for answer in ({'code': 430}, {'code': 220, 'digest': 'payload'}):
        b.op('read', {'node': 'mutation', 'message_id': v['message_id']}, response=answer)
    return b.history


VIOLATIONS = dict(zip(('C1', 'C2', 'C3', 'C4', 'C5', 'C6', 'D1', 'D2', 'D3'),
                     (lowered_ack, skipped_redelivery, redelivery_after_ack, lost_wake,
                      old_epoch_ack, poll_moves_position, lost_acknowledged_post,
                      refused_readable, inconsistent_uncertain)))
