"""BP S oracle: carry obligations, their Store pins, boundaries and routes (RELEASE-PLAN §2.2 row "BP / TCPCL").

SPEC-MAP (line numbers at 335878b2b)
 verb / expected exit, named reason, effect          source
 accepted 0, refused 1/no change, usage 5            docs/operator.md:1232-1242
 carry JOURNAL list|inspect WORK: one line per work: docs/operator.md:723-745 (list's fields: its
   message-id, peer, status, pinned=yes|no, hold    Message-ID, peer, status, Store pin, hold, last
   (none, paused, dropped with the reason, waived      attempt); the line order is unspecified (a set)
   waived-by=uid:N waiver=REASON), last attempt
 carry pause|resume WORK|*                           docs/operator.md:740-745; specs/bp-node-machine.md
 carry drop WORK REASON...: final; keeps the pin      docs/operator.md:747-752
 carry drop WORK --abandon REASON...: the waiver,    docs/operator.md:754-766 (not-held when the store
   journaled with who waived it, then the pin          holds no pin; a receipt after it is refused)
   released through the receipt's own release
 bp-obligation request WORK ...: refused before any  docs/operator.md:740-752 (carry-paused,
   attempt while paused/dropped (carry-paused,         carry-dropped, forward-pin-not-durable)
   carry-dropped) or without a durable pin
   (forward-pin-not-durable); otherwise one durable
   attempt, the job queued only to a routed boundary specs/bp-node-machine.md:1597-1640 (no route:
   (no route: `decision=no-route`, the obligation     not queued, the obligation stays; the route
   stays); a contact that never connected is exit 7   table); specs/host.md "BP run classes" (7)
 bp-obligation undertake WORK CHARGE: the forward    docs/operator.md:723-726 (the store keeps it until
   pin; status prints `pinned=yes|no`                  the peer's receipt comes back)
 bp-obligation receipt (unsigned): refused, nothing  docs/operator.md:752 (only the peer's receipt
   released                                            releases the store's pin)
 bp-boundary add NAME PATH BP-EID PORT [contact P]   specs/bp-node-machine.md:2974-3000 (EID shape:
   [carries E...] [releases-for E...]: one peer-list  RFC 9171 §4.2.5.1; dtn:none refused; lower-case
   word per EID; a malformed EID is refused            scheme; each list read back exactly)
 bp-route add PATTERN BOUNDARY [PRIORITY] | remove   specs/bp-node-machine.md:1597-1640 (a route to
   PATTERN BOUNDARY: a route to anything but a         anything else routes nothing; no default route;
   current boundary routes nothing                     PRIORITY uint32, lower preferred)

THE INVARIANT (RELEASE-PLAN §2.2): an obligation's Store pin is released only by a receipt or a recorded
waiver. Every observation reads every work's `pinned=` and the model moves a pin only at undertake
(no -> yes) and at an accepted `drop --abandon` (yes -> no); nothing else may move it.

Reply shape: `carry`, `bp-route` and `bp-boundary` print the operator's tagged line (operator_model);
a carry refusal names `reason=X`, an administration refusal `refused: X`, usage `(ADMINISTRATION X)` or
its tag. `bp-obligation` prints no tagged line: its refusals are the exit (1) and, where the docs name
one, `reason=X`. Where the docs name the class only, the tag is fn1's as recorded by the seat's probe
(hbox image c14e9e8e, developer image; build/coordinator/fn2/lanes/h-quests/bpp.json, bpprobe.py):
unknown-work, already-paused, not-paused, already-dropped, dropped (pause/resume of a dropped work),
already-waived, invalid-carry-command (usage), bp-route and bp-boundary (usage), no-such-peer.

Scope: one store and one FNWF journal, no node running (`carry` needs the BP node stopped, docs/operator.md
:727), at most five works on one peer EID, the loopback boundary profile with a contact nothing listens
on. OUT OF SCOPE: a signed receipt (the receipt releases; needs a hybrid principal), recovery of a waiver
cut between its two steps (the bp_carry_abandon native), TCPCL sessions, bundles and custody transfer
(F8 under the simulator; the dtn7-rs golden fixtures), `fenced` attempts and `bp-obligation recover`.
After a request is attempted the status word and the attempt/transport fields are not modelled.
"""
from copy import deepcopy
from dataclasses import dataclass
import os
import re

from .operator_model import reason_word, result_line
from .peering_model import peer_reason

PEER = 'dtn://fn-b/'
ADJUDICATIONS = ()  # Seat adds rows only from a recorded fn1 reply.
WORDS = {0: 'accepted', 1: 'refused', 3: 'uncertain', 4: 'fault', 5: 'usage', 7: None}
FIELDS = ('message-id', 'peer', 'status', 'pinned', 'hold', 'reason', 'waived-by', 'waiver', 'attempt', 'transport')


def bp_reason(text):
    """A carry or request refusal's `reason=X`: on the tagged line, or on the `store: ACL2 refused` line.
    A store open prints its own `OWNER-OPEN ... reason=absent` first, which names nothing here."""
    found = re.findall(r'^(?:refused operator \S+ |store: ).*?\breason=([A-Za-z0-9-]+)', text, re.M)
    return found[-1].lower() if found else reason_word(text)


def eid_shape(word):
    """RFC 9171 §4.2.5.1 with fn's local rules (specs/bp-node-machine.md:2981-2990)."""
    if word == 'dtn:none' or len(word) > 256:
        return False
    if re.fullmatch(r'ipn:(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)', word):
        return all(int(n) < 1 << 64 for n in word[4:].split('.'))
    return bool(re.fullmatch(r'dtn://[A-Za-z0-9._~!$&\'()*+,;=%-]+/[\x21-\x7e]*', word))


def route_shape(word):
    return eid_shape(word[:-1] + 'x' if word.endswith('*') else word) and (
        not word.endswith('*') or word.startswith('dtn://'))


def carry_line(line):
    """`carry WORK k=v ...` -> (WORK, {field: value}); values run to the next known field."""
    match = re.fullmatch(r'carry (\S+) (.*)', line)
    if not match:
        return None
    parts = re.split(r' (?=(?:' + '|'.join(FIELDS) + r')=)', ' ' + match[2])
    fields = {}
    for part in parts:
        if part:
            key, _, value = part.partition('=')
            fields[key] = value
    return match[1], fields


@dataclass(frozen=True)
class Request:
    verb: str
    args: tuple = ()

    @property
    def words(self):
        return tuple(self.verb.split()) + self.args


class Expect:
    def __init__(self, model, request):
        self.model, self.request = model, request
        self.exit, self.reason, self.argument_class = model.verdict(request)

    def check(self, reply):
        v, text = self.request.verb, reply.get('text', '')
        if reply.get('exit') != self.exit:
            return f'{v}: expected exit {self.exit}' + (f', reason {self.reason}' if self.reason else '')
        if not v.startswith('bp-obligation'):
            line = result_line(text)
            if line is None or line[0] != WORDS[self.exit]:
                return f'{v}: expected the tagged line `{WORDS[self.exit]} operator ...`'
        if self.reason:
            named = bp_reason(text) if v.startswith(('carry', 'bp-obligation')) else peer_reason(text)
            if named != self.reason:
                return f'{v}: expected named refusal {self.reason}, observed {named}'
        if self.exit == 0 or self.argument_class == 'attempted':
            return self.model.check_report(self.request, reply)
        return None

    def recorded_difference(self, reply, target='fake'):
        if target not in ('fn1', 'fn2') or self.check(reply) is None:
            return None
        for row in ADJUDICATIONS:
            if target == 'fn2' and row['class'] != 'spec-ambiguity':
                continue
            if (row['verb'] == self.request.verb and row['argument_class'] == self.argument_class
                    and row['exit'] == reply['exit']):
                return dict(deepcopy(row), target=target, request=self.request, observed_reply=dict(reply))
        return None

    def update(self, reply, target='fake'):
        recorded = self.recorded_difference(reply, target)
        problem = self.check(reply)
        if problem and recorded is None:
            raise AssertionError(problem)
        if recorded is None and (self.exit == 0 or self.argument_class == 'attempted'):
            self.model.apply(self.request)
        return recorded


class BpModel:
    VERBS = ('carry list', 'carry inspect', 'carry pause', 'carry resume', 'carry drop', 'carry abandon',
             'bp-obligation undertake', 'bp-obligation status', 'bp-obligation request',
             'bp-obligation receipt', 'bp-boundary add', 'bp-route add', 'bp-route remove')

    def __init__(self, uid=None):
        self.uid = os.geteuid() if uid is None else uid
        self.works, self.boundaries, self.routes = {}, {}, {}

    def enqueued(self, work, msgid):
        """The fixture's `app-journal workflow-enqueue` (the producer), accepted: one outstanding work."""
        self.works[work] = dict(msgid=msgid, peer=PEER, status='outstanding', pinned=False, hold='none',
                                reason=None, waiver=None, attempted=False)

    def rule(self, verb, *args):
        if verb not in self.VERBS:
            raise ValueError('outside bp slice: ' + verb)
        return Expect(self, Request(verb, tuple(str(a) for a in args)))

    def verdict(self, r):
        v, a = r.verb, r.args
        def bad(reason, cls, code=1):
            return code, reason, cls
        # The operator's universal argv preflight (specs/native-admin.md:8-15); bp-obligation has none.
        if not v.startswith('bp-obligation') and any(not w or not w.isascii() for w in a):
            return bad('argv-malformed', 'malformed-argv', 5)
        work = self.works.get(a[0]) if a else None
        if v == 'carry list':
            return 0, None, 'valid'
        if v in ('carry drop', 'carry abandon') and len(a) < 2:
            return bad('invalid-carry-command', 'no-reason', 5)
        if v in ('carry pause', 'carry resume') and a[0] == '*':
            eligible = [w for w in self.works.values() if w['hold'] == ('none' if v == 'carry pause' else 'paused')]
            if not eligible:
                return bad('already-paused' if v == 'carry pause' else 'not-paused', 'none-eligible')
            return 0, None, 'valid'
        if v.startswith('carry ') and work is None:
            return bad('unknown-work', 'unknown-work')
        if v == 'carry pause':
            if work['hold'] in ('dropped', 'waived'):
                return bad('dropped', 'closed')
            if work['hold'] == 'paused':
                return bad('already-paused', 'paused')
        if v == 'carry resume':
            if work['hold'] in ('dropped', 'waived'):
                return bad('dropped', 'closed')
            if work['hold'] != 'paused':
                return bad('not-paused', 'not-paused')
        if v == 'carry drop' and work['hold'] in ('dropped', 'waived'):
            return bad('already-dropped', 'closed')
        if v == 'carry abandon':
            if work['hold'] == 'waived':
                return bad('already-waived', 'waived')
            if not work['pinned']:
                return bad('not-held', 'unpinned')
        if v == 'bp-obligation undertake':
            if work is None or work['pinned'] or work['hold'] == 'waived':
                return bad('', 'inadmissible')
        if v == 'bp-obligation status':
            return 0, None, 'valid'
        if v == 'bp-obligation request':
            if work is None:
                return bad('', 'unknown-work')
            if work['hold'] == 'paused':
                return bad('carry-paused', 'paused')
            if work['hold'] in ('dropped', 'waived'):
                return bad('carry-dropped', 'closed')
            if not work['pinned']:
                return bad('forward-pin-not-durable', 'unpinned')
            return (7, None, 'attempted') if self.next_hop(work['peer'])[1] else (1, None, 'attempted')
        if v == 'bp-obligation receipt':
            return bad('', 'unsigned')
        if v == 'bp-boundary add':
            if len(a) < 4 or not eid_shape(a[2]) or not re.fullmatch(r'[1-9][0-9]*', a[3]):
                return bad('bp-boundary', 'invalid-boundary', 5)
            lists = self.boundary_lists(a[4:])
            if lists is None:
                return bad('bp-boundary', 'invalid-boundary', 5)
        if v == 'bp-route add':
            if len(a) not in (2, 3) or not route_shape(a[0]) or (len(a) == 3 and not (
                    re.fullmatch(r'0|[1-9][0-9]*', a[2]) and int(a[2]) < 1 << 32)):
                return bad('bp-route', 'invalid-route', 5)
        if v == 'bp-route remove':
            if len(a) != 2:
                return bad('bp-route', 'invalid-route', 5)
            if (a[0], a[1]) not in self.routes:
                return bad('no-such-peer', 'unknown-route')
        return 0, None, 'valid'

    @staticmethod
    def boundary_lists(words):
        """[contact PORT] [carries E...] [releases-for E...] -> (contact, carries, releases) or None."""
        words, contact, lists = list(words), None, {'carries': [], 'releases-for': []}
        if words[:1] == ['contact']:
            if len(words) < 2 or not re.fullmatch(r'[1-9][0-9]*', words[1]):
                return None
            contact, words = words[1], words[2:]
        for key in ('carries', 'releases-for'):
            if words[:1] == [key]:
                words = words[1:]
                while words and words[0] not in lists:
                    lists[key].append(words.pop(0))
                if not lists[key] or len(set(lists[key])) != len(lists[key]) or not all(map(eid_shape, lists[key])):
                    return None
        return None if words else (contact, lists['carries'], lists['releases-for'])

    def next_hop(self, dest):
        """specs/bp-node-machine.md:1624-1631: no matching pattern is no-route; matching routes naming no
        current boundary are no-live-hop; else the least of (priority, exact before prefix, pattern,
        name). Returns (decision, boundary-or-None)."""
        matching = [(priority, 0 if not pattern.endswith('*') else 1, pattern, boundary)
                    for (pattern, boundary), priority in self.routes.items()
                    if dest == pattern or (pattern.endswith('*') and dest.startswith(pattern[:-1]))]
        if not matching:
            return 'no-route', None
        live = [m for m in matching if m[3] in self.boundaries]
        return ('routed', min(live)[3]) if live else ('no-live-hop', None)

    def check_lines(self, text, names):
        rows = {}
        for line in text.splitlines():
            parsed = carry_line(line)
            if parsed:
                if parsed[0] in rows:
                    return f'carry: work {parsed[0]} listed twice'
                rows[parsed[0]] = parsed[1]
        if set(rows) != set(names):
            return f'carry: expected works {sorted(names)}, observed {sorted(rows)}'
        for name in names:
            w, got = self.works[name], rows[name]
            wanted = {'message-id': w['msgid'], 'peer': w['peer'], 'pinned': 'yes' if w['pinned'] else 'no',
                      'hold': w['hold']}
            if not w['attempted']:
                wanted['status'] = 'outstanding'
            if w['reason'] is not None:
                wanted['reason'] = w['reason']
            if w['waiver'] is not None:
                wanted.update({'waived-by': 'uid:%d' % self.uid, 'waiver': w['waiver']})
            for key, value in wanted.items():
                if got.get(key) != value:
                    return f'carry {name}: {key}={got.get(key)}, expected {value}'
            extra = set(got) - set(wanted) - {'status', 'attempt', 'transport'}
            if extra or (not w['attempted'] and ({'attempt', 'transport'} & set(got))):
                return f'carry {name}: unexpected fields {sorted(set(got) - set(wanted))}'
        return None

    def check_report(self, r, reply):
        v, a, text = r.verb, r.args, reply['text']
        if v == 'carry list':
            return self.check_lines(text, self.works)
        if v == 'carry inspect':
            return self.check_lines(text, [a[0]])
        if v == 'bp-obligation status':
            w = self.works.get(a[0])
            found = re.findall(r'^BP obligation owner work=(\S+) status=(\S+) pinned=(yes|no)$', text, re.M)
            if len(found) != 1 or found[0][0] != a[0]:
                return 'status: expected one `BP obligation owner work=W status=S pinned=X` line'
            _, status, pinned = found[0]
            if w is None:
                return None if (status, pinned) == ('absent', 'no') else 'status: an unknown work is absent, unpinned'
            if pinned != ('yes' if w['pinned'] else 'no') or (not w['attempted'] and status != 'outstanding'):
                return f'status: pinned={pinned} status={status}'
        if v == 'bp-obligation request':
            decision, hop = self.next_hop(self.works[a[0]]['peer'])
            if f'BP obligation request durable attempt work={a[0]} attempt={a[1]} ' not in text:
                return 'request: expected the durable attempt line'
            if hop is None and 'decision=' + decision not in text:
                return f'request: an unrouted destination is not queued (decision={decision})'
            if hop is not None and ('decision=no-' in text or 'BP queue accepted work=' + a[0] not in text):
                return 'request: a routed destination is queued to its boundary'
        return None

    def check_boundaries(self, text):
        """peer list: each boundary's line begins `NAME path-identity=PATH address=EID` and carries each
        listed EID once (specs/bp-node-machine.md:2988-2993); other words are fn's NNTP-half rendering."""
        rows = {line.split(' ', 1)[0]: line for line in text.splitlines() if ' path-identity=' in line}
        if set(rows) != set(self.boundaries):
            return f'peer list: boundaries {sorted(rows)}, expected {sorted(self.boundaries)}'
        for name, (path, eid, carries, releases) in self.boundaries.items():
            line = rows[name]
            if not line.startswith(f'{name} path-identity={path} address={eid} '):
                return f'peer list: {name} line {line!r}'
            for key, values in (('carries', carries), ('releases-for', releases)):
                listed = re.findall(r'\b' + key + r'=(\S+(?: (?!\S+=)\S+)*)', line)
                words = listed[0].split(' ') if listed else []
                if words != values:
                    return f'peer list: {name} {key} {words}, expected {values}'
        return None

    def apply(self, r):
        v, a = r.verb, r.args
        w = self.works.get(a[0]) if a else None
        if v in ('carry pause', 'carry resume'):
            targets = self.works.values() if a[0] == '*' else [w]
            for t in targets:
                if v == 'carry pause' and t['hold'] == 'none':
                    t['hold'] = 'paused'
                elif v == 'carry resume' and t['hold'] == 'paused':
                    t['hold'] = 'none'
        elif v == 'carry drop':
            w.update(hold='dropped', reason=' '.join(a[1:]))
        elif v == 'carry abandon':
            # `drop --abandon` is a drop that also waives (docs/operator.md:754: "also gives up the
            # obligation"): a work not dropped before takes the waiver's words as its drop reason too.
            w.update(hold='waived', waiver=' '.join(a[1:]), pinned=False, reason=w['reason'] or ' '.join(a[1:]))
        elif v == 'bp-obligation undertake':
            w['pinned'] = True
        elif v == 'bp-obligation request':
            w['attempted'] = True
        elif v == 'bp-boundary add':
            contact, carries, releases = self.boundary_lists(a[4:])
            self.boundaries[a[0]] = (a[1], a[2], carries, releases)
        elif v == 'bp-route add':
            self.routes[(a[0], a[1])] = int(a[2]) if len(a) == 3 else 100
        elif v == 'bp-route remove':
            del self.routes[(a[0], a[1])]
