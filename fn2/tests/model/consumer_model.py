"""Spec-derived local consumer oracle; no fn1 implementation dependencies.

SPEC-MAP (specs/consumer-progress.md, line numbers at HS):
 cursor/identity 16-65; register 76-80; poll 70-101, 639-660;
 ack 103-107; position 108-110, recovery 151-164; rebase 111-116;
 unregister 114-117; three outcomes 118-121; status 624-636;
 bound-poll/bound-ack 329-373; wait/bound-wait 384-407;
 refusal words/JSON 414-457; withdrawals 459-499.

Profile: one retained group, one article per page, <=16 Store records scanned,
no concurrent mutations, poll from durable ack (the H3 workload). Sequence
positions are Store positions, never group numbers. Nonarticle gaps are legal.
The fixture supplies independently observed Store positions and frontier; it
must not derive them by counting articles. General multi-item/remote requests,
reclamation, uncertain persistence and consumer application transactions are
outside this determinate profile. A historical cursor API would need a different
workload: H3's C3 intentionally does not apply to historical reads.
"""
from copy import deepcopy
from dataclasses import asdict, dataclass, replace
import struct


@dataclass(frozen=True)
class Cursor:
    history: str
    incarnation: str
    consumer: str
    epoch: int
    principal: str
    query: str
    query_version: int = 1
    view_version: int = 0
    position: int = 0

    @property
    def scope(self):
        return {k: v for k, v in asdict(self).items()
                if k not in ('consumer', 'epoch', 'position')}

    def encode(self):
        ids = [getattr(self, k).encode('latin1') for k in
               ('history', 'incarnation', 'consumer', 'principal', 'query')]
        if not all(1 <= len(x) <= 64 for x in ids):
            raise ValueError('cursor ID length')
        return b'fncu\1' + b''.join(bytes([len(x)]) + x for x in ids) + struct.pack(
            '>4I', self.query_version, self.view_version, self.epoch, self.position)

    @classmethod
    def decode(cls, raw):
        if not 31 <= len(raw) <= 346 or raw[:5] != b'fncu\1':
            raise ValueError('cursor length/magic/version')
        offset, ids = 5, []
        for _ in range(5):
            n = raw[offset]; offset += 1
            if not 1 <= n <= 64 or offset + n > len(raw) - 16:
                raise ValueError('cursor ID length')
            ids.append(raw[offset:offset+n].decode('latin1')); offset += n
        if len(raw) != offset + 16:
            raise ValueError('cursor trailing/truncated integers')
        qv, vv, epoch, pos = struct.unpack('>4I', raw[offset:])
        return cls(ids[0], ids[1], ids[2], epoch, ids[3], ids[4], qv, vv, pos)


@dataclass(frozen=True)
class Event:
    position: int
    message_id: str
    group: str = 'surface.test'
    kind: str = 'article'


@dataclass(frozen=True)
class Request:
    verb: str
    consumer: str
    cursor: Cursor | None = None
    query: str = 'surface.test'
    query_version: int = 1
    view_version: int = 0
    secret: str | None = None
    timeout: int = 0


class Expect:
    """A rule's precondition, public request, reply predicate and checked update.

    `_frontier_after` is a separate public status observation in the serialized
    fixture, not an invented JSON field; it witnesses publication-free reads,
    refusals and idempotent requests. Position probes witness progress itself.
    """
    def __init__(self, model, request):
        self.model, self.request = model, request
        self.precondition = 'serialized, retained-content, determinate local profile'
        self.before = model.consumers.get(request.consumer)
        self.reasons = model.refusals(request)

    def check(self, reply):
        m, r, old = self.model, self.request, self.before
        read_only = self.reasons or r.verb in ('position', 'status', 'poll', 'bound-poll', 'wait', 'bound-wait')
        idempotent = (r.verb == 'register' and old is not None) or (r.verb.endswith('ack') and r.cursor == old)
        effect_error = ('no-mutation: read/refusal/idempotent operation changed frontier'
                        if (read_only or idempotent) and reply.get('_frontier_after') != m.frontier else None)
        if reply.get('command') != r.verb:
            return 'command: reply belongs to a different verb'
        if self.reasons:
            return effect_error if reply.get('outcome') == 'refused' and reply.get('reason') in self.reasons else (
                'refusal: expected one of ' + ', '.join(sorted(self.reasons)))
        if reply.get('outcome') != 'accepted' or reply.get('reason') is not None:
            return 'outcome: determinate rule requires accepted, never uncertain'
        if effect_error:
            return effect_error
        if r.verb == 'unregister':
            return None
        if r.verb == 'status':
            counts = (reply.get('committed_ack'), reply.get('journal_frontier'),
                      reply.get('journal_event_distance'))
            return None if counts == (old.position, m.frontier, m.frontier-old.position) else 'status: durable counts'
        cursor = reply.get('cursor')
        if not isinstance(cursor, Cursor):
            return 'cursor: missing decoded fncu'
        if r.verb in ('register', 'rebase') and (old is None or r.verb == 'rebase'):
            want = Cursor(m.history, m.incarnation, r.consumer, cursor.epoch,
                          m.principal, r.query, r.query_version, r.view_version)
            if cursor != want or (cursor.epoch in m.epochs and not (
                    r.verb == 'rebase' and old and cursor.epoch == old.epoch)):
                return 'register: fresh epoch, scope and zero position'
        elif r.verb in ('ack', 'bound-ack'):
            if cursor != r.cursor:
                return 'ack: forward target/equal idempotence'
        elif r.verb in ('poll', 'bound-poll', 'wait', 'bound-wait'):
            expected_cursor, event = m.page(old)
            if cursor != expected_cursor:
                return 'poll: scanned prefix/order; no skip or redelivery'
            kind, ident = ('empty', None) if event is None else (event.kind, event.message_id)
            # The JSON line carries no `more` (spec 448-452); a live adapter that
            # derives it from its own frontier read must not present it as observed.
            if 'more' in reply and (type(reply['more']) is not bool or
                                    reply['more'] != (cursor.position < m.frontier)):
                return 'poll: more must describe the pinned frontier'
            if kind == 'empty' and reply.get('report_bytes') != b'':
                return 'poll: empty report must contain no bytes'
            if (reply.get('report'), reply.get('message_id')) != (kind, ident):
                return 'poll: next unacked event/withdrawal kind'
            if kind == 'withdrawn' and reply.get('report_bytes') != b'FNWD\1' + ident.encode('ascii'):
                return 'withdrawal: exact FNWD1 report, no article content'
            if r.verb.endswith('wait') and event is None and reply.get('elapsed', -1) < r.timeout:
                return 'wait: early empty return'
        elif cursor != old:
            return 'position: mutation without accepted ack (including refusal/poll)'
        return None

    def update(self, reply):
        problem = self.check(reply)
        if problem:
            raise AssertionError(problem)
        r, m = self.request, self.model
        if self.reasons:
            return
        if r.verb in ('register', 'rebase', 'ack', 'bound-ack'):
            m.consumers[r.consumer] = reply['cursor']
            m.epochs.add(reply['cursor'].epoch)
        elif r.verb == 'unregister':
            del m.consumers[r.consumer]


class ConsumerModel:
    VERBS = ('register', 'poll', 'ack', 'position', 'rebase', 'unregister',
             'status', 'bound-poll', 'bound-ack', 'wait', 'bound-wait')

    def __init__(self, *, history='history', incarnation='incarnation', principal='owner',
                 events=(), frontier=0, groups=('surface.test',)):
        self.history, self.incarnation, self.principal = history, incarnation, principal
        self.events, self.frontier, self.groups = list(events), frontier, set(groups)
        self.consumers, self.bindings, self.waiters = {}, {}, set()
        self.withdrawn, self.epochs = set(), set()

    def rule(self, verb, consumer, **kwargs):
        if verb not in self.VERBS:
            raise ValueError('unknown consumer verb: ' + verb)
        return Expect(self, Request(verb, consumer, **kwargs))

    def refusals(self, r):
        """No invented precedence: every independently applicable named refusal.

        The spec names credential/access/bound/scope but does not order multiple
        defects. A single defect still admits exactly its one reason word.
        """
        old, reasons = self.consumers.get(r.consumer), set()
        if r.verb in ('register', 'rebase') and r.query not in self.groups:
            reasons.add('no-such-group')
        if r.verb == 'register':
            if old and (old.query, old.query_version, old.view_version) != (
                    r.query, r.query_version, r.view_version):
                reasons.add('scope')
            return reasons
        if old is None:
            return reasons | {'unknown-consumer'}
        if r.verb in ('poll', 'ack', 'wait', 'bound-poll', 'bound-ack', 'bound-wait'):
            binding = self.bindings.get(r.consumer)
            if r.verb.startswith('bound-'):
                if binding is None:
                    reasons.add('unbound')
                else:
                    secret, allowed = binding
                    if r.secret != secret:
                        reasons.add('credential')
                    if not allowed:
                        reasons.add('access')
            elif binding is not None:
                reasons.add('bound')
        if r.verb.endswith('ack'):
            if r.cursor is None or replace(r.cursor, position=old.position) != old or not (
                    old.position <= r.cursor.position <= self.frontier):
                reasons.add('scope')
        if r.verb == 'rebase' and (r.query_version, r.view_version) == (old.query_version, old.view_version):
            raise ValueError('rebase precondition: explicit new query/view version')
        if r.verb.endswith('wait') and len(self.waiters) >= 12:
            reasons.add('waiters')
        return reasons

    def page(self, cursor):
        end = min(self.frontier, cursor.position + 16)
        for event in self.events:
            if cursor.position < event.position <= end and event.group == cursor.query:
                if event.message_id in self.withdrawn:
                    event = replace(event, kind='withdrawn')
                return replace(cursor, position=event.position), event
        return replace(cursor, position=end), None


def to_h3(trace, node='consumer-target'):
    """HS S->H morphism (MODEL.md definitions 1-3), preserving observed outcomes.

    Trace rows are (request, request_scope_cursor, observed_reply). The scope is
    captured BEFORE dispatch. Register/rebase use the newly observed scope;
    ack keeps its request target and foreign scope. Bound verbs erase only the
    credential carrier. Status projects to position, since H3 has no status verb.
    No expected reply or private target state is consulted. `more` is supplied by
    the observer using its separately read pinned frontier, never guessed here.
    """
    history = []
    for request, context, reply in trace:
        verb = request.verb.removeprefix('bound-')
        if verb == 'status':
            verb = 'position'
        scope_cursor = request.cursor if verb == 'ack' else context
        if verb in ('register', 'rebase') and reply.get('outcome') == 'accepted':
            scope_cursor = reply['cursor']
        value = dict(consumer=request.consumer, node=node, epoch=scope_cursor.epoch,
                     scope=scope_cursor.scope)
        if verb == 'ack':
            value['position'] = request.cursor.position
        if verb in ('poll', 'wait'):
            value['cursor'] = context.position
        start = history[-1]['time'] + 1 if history else 0
        if verb == 'wait':
            value['deadline'] = start + request.timeout * 1_000_000_000
        history.append(dict(process='consumer', type='invoke', f=verb,
                            value=deepcopy(value), time=start, index=len(history)))
        outcome = reply.get('outcome')
        if outcome == 'accepted':
            if verb == 'position' and request.verb == 'status':
                value['position'] = reply['committed_ack']
            elif 'cursor' in reply and verb != 'ack':
                value['position'] = reply['cursor'].position
            if verb in ('poll', 'wait'):
                value['events'] = [] if reply['report'] == 'empty' else [
                    [reply['cursor'].position, reply['message_id']]]
                value['more'] = reply['more'] if 'more' in reply else reply['_more_from_frontier']
                value['event_kinds'] = {str(p): reply['report'] for p, _ in value['events']}
        else:
            value['reason'] = reply.get('reason')
        end = start + max(1, int(reply.get('elapsed', 0) * 1_000_000_000))
        history.append(dict(process='consumer', type={'accepted': 'ok', 'refused': 'fail'}.get(outcome, 'info'),
                            f=verb, value=deepcopy(value), time=end, index=len(history)))
    return history
