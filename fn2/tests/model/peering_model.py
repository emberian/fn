"""Peering S oracle: the peer table, composed with the single NNTP model (RELEASE-PLAN §2.2 row "peering").

SPEC-MAP (line numbers at 335878b2b)
 verb / expected exit, named reason, effect          source
 accepted 0, refused 1/no change, usage 5            docs/operator.md:1232-1242
 peer add NAME PATH HOST PORT IN OUT AUTH-KIND       specs/peering.md:2749-2753 (grammar, AUTH-KIND
   AUTH-VALUE STREAMING: one record, replaces a        source-address|principal, 64 lowercase hex);
   record of that name and drops its extensions      specs/peering.md:2444,2469 (add replaces)
 peer remove: no-such-peer                           specs/peering.md:140-143
 peer list: one line per record, the add order of    docs/operator-internals.md:552-569
   words, `-` for an absent half, budget-octets
   (whole 4096-octet pages) and budget-count last
 peer set NAME --FLAG V...: named fields only, the   specs/peering.md:2433-2455; docs/peering-with-
   extensions kept; no-such-peer, needs-send (a        a-friend.md:134-137 (unknown-flag)
   streaming word or login with nothing sent),
   unknown-flag
 peer feed NAME pause|resume: live, idempotent row;  specs/peering.md:1237-1247; docs/operator.md:1355-
   a paused peer is not dialled; its queue stays,      1360
   resume delivers what queued
 peer distributions NAME WILDMAT: RFC 5537 §3.6;     docs/operator.md:725-738 (internals 571-583)
   no header: every peer; a second request replaces
 peer budget NAME OCTETS COUNT                       specs/peering.md:186-200
 peer pull NAME SECONDS [ROUNDS]: a round asks       specs/peering.md:265-289,336-345
   NEWNEWS over the inbound accept-groups, ARTICLE
   only after the local 335; 0 stops
 peer pull-login NAME FILE|- true|false              specs/peering.md:2459-2470
 peer catch-up NAME SECONDS: a funded node admits    specs/peering.md:355-368 (init writes the
   it (init's profile); 0 stops                        profile)
 peer login NAME LOGIN FILE: the password twice on   specs/peering.md:2449-2455
   stdin, then `peer set NAME --login FILE`
 transit on a peer connection (a source-address      specs/peering.md:2736-2790 (the role is decided at
   record with an inbound half: the kernel address     accept by the address); specs/nntp.md:2412-2443
   decides the role); scope = accept-groups and live (NNT-045); specs/peering.md:146-153,756-765
 outbound feed: an article is fed when one of its    specs/peering.md:146-153; specs/nntp.md:2445-2452
   accepted local groups matches feed-groups; MODE     (MODE STREAM 203: CHECK+TAKETHIS; 500/501:
   STREAM per the record's streaming word              IHAVE on the same connection)
 AUTHINFO / GROUP / STAT / BODY / IHAVE / CHECK /     nntp_model.SPECS (the sole wire oracle)
   TAKETHIS / MODE STREAM

Reply shape: the exit and the tagged line `WORD operator peer ...` (operator_model.result_line). A refusal
names its tag after `refused: ` (offline, `administrative configuration refused: NO-SUCH-PEER`) or after
`REFUSED` (live, `REFUSED needs-send`); usage names it in `(ADMINISTRATION TAG)`. Where the docs name the
class only, the tag is fn1's as recorded by the seat's probe (hbox image c14e9e8e, TREE_SHA d377d4559;
build/coordinator/fn2/lanes/h-quests/pp.json, peerprobe.py): syntax (add's words), feed, distributions,
budget, pull, pull-login, catch-up (each verb's malformed argument, usage); port (`peer set --port 0`,
refused); passwords-differ (`peer login`, refused).

Scope (this slice): the peer-table verbs on one live node; transit on the loopback peer connection;
the outbound feed to scripted peers (CHECK/TAKETHIS or IHAVE, pause/resume, distributions, feed-groups);
one NEWNEWS pull from a scripted peer. OUT OF SCOPE: TLS words (`--tls`, server name, anchor: the
protected_peering native), invitations (keygen/invite/accept/confirm), catch-up rounds (two nodes and
the digest chain: forms H and the peer_catchup native), the legacy eight-word add, retire's drain, BP
boundaries (the bp family). pull-login's FILE must name an existing credential file (spec 2461); the
slice selects only `-`, never a missing file (fn1 accepts one: not generated, not adjudicated).

Timing (a work bound, not a product ceiling): a fed or pulled article must reach the scripted peer or
the node within SETTLE seconds; an article accepted after a pause returned is never offered before the
resume was asked. Delivery is at-least-once and order-free; a removed peer's queued articles may still
drain (specs/peering.md:141-143) and are then permitted, never required.
"""
from copy import deepcopy
from dataclasses import dataclass
import ipaddress
import re

from .nntp_model import NntpModel, headers, wildmat
from .operator_model import result_line

GROUPS = ('hz.peer', 'hz.test', 'hz.other')
PRINCIPAL = 'ab' * 32
SETTLE = 20.0
# Rows only from recorded fn1 replies (seat probe, hbox image c14e9e8e, TREE_SHA d377d4559;
# build/coordinator/fn2/lanes/h-quests/wp2-peering.json).
ADJUDICATIONS = (
    dict(group='P01', kind='effect', verb='feed', argument_class='transferred', effect='feed-by-newsgroups',
         spec='specs/peering.md:150-152 (an article is fed to a peer when at least one of its accepted local '
              'groups matches feed-groups)',
         fn1_reply=dict(offered=['<pull-3@surface.invalid>'], to=['fa', 'fb']),
         observed='a pulled article, Newsgroups hz.peer,hz.test, filed in hz.peer only (accept-groups hz.peer; '
                  'GROUP hz.test agrees), was offered to both scripted feed peers, whose feed-groups are '
                  'hz.test,hz.other: fn1 matches feed-groups against the Newsgroups names, not the local '
                  'memberships',
         **{'class': 'fn1-bug'}),
)
SET_FLAGS = ('--host', '--port', '--take', '--send', '--streaming', '--tls', '--server-name', '--anchor',
             '--login', '--allow-clear', '--principal', '--source-address')
WORDS = {0: 'accepted', 1: 'refused', 3: 'uncertain', 4: 'fault', 5: 'usage'}


def peer_reason(text):
    """The named tag of a peer verb's tagged line, lower case, or None."""
    line = result_line(text)
    if line is None:
        return None
    found = re.findall(r'(?:^|: )(?:accepted|refused|usage|fault|uncertain) operator \S+ (.*)$', text, re.M)
    rest = found[-1] if found else ''
    named = re.search(r'refused: ([A-Za-z0-9-]+)\s*$', rest)
    return named[1].lower() if named else line[2]


def distribution_fed(pattern, article):
    """RFC 5537 §3.6 / docs/operator.md:725-738: without a Distribution header every peer is fed; a
    header names comma-separated distributions compared without case; malformed feeds no filter."""
    if pattern is None:
        return True
    field = headers(article).get('distribution')
    if field is None:
        return True
    names = [n.strip().lower() for n in field.decode('ascii', 'replace').split(',')]
    if not names or any(not re.fullmatch(r'[a-z0-9+_-]+', n) for n in names):
        return False
    return any(wildmat(pattern.lower(), n) for n in names)


def hostname(word):
    try:
        ipaddress.IPv4Address(word)
        return True
    except ValueError:
        return bool(re.fullmatch(r'(?=.{1,253}$)[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?'
                                 r'(?:\.[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?)*', word))


def ipv4(word):
    try:
        ipaddress.IPv4Address(word)
        return True
    except ValueError:
        return False


def pattern_ok(word):
    if word == '-':
        return True
    try:
        wildmat(word, '')
        return True
    except ValueError:
        return False


@dataclass(frozen=True)
class Request:
    verb: str
    args: tuple = ()
    password: str | None = None

    @property
    def words(self):
        return tuple(self.verb.split()) + self.args


class Expect:
    def __init__(self, model, request):
        self.model, self.request = model, request
        self.exit, self.reason, self.argument_class = model.verdict(request)

    def check(self, reply):
        if reply.get('exit') != self.exit:
            return f'{self.request.verb}: expected exit {self.exit}' + (f', reason {self.reason}' if self.reason else '')
        line = result_line(reply.get('text', ''))
        # The subject is the verb's (`peer`) or, for the universal argv preflight, `request`.
        if line is None or line[0] != WORDS[self.exit]:
            return f'{self.request.verb}: expected the tagged line `{WORDS[self.exit]} operator ...`'
        if self.reason and peer_reason(reply['text']) != self.reason:
            return f'{self.request.verb}: expected named refusal {self.reason}, observed {peer_reason(reply["text"])}'
        if not self.reason and self.request.verb == 'peer list':
            return self.model.check_list(reply['text'])
        return None

    def recorded_difference(self, reply, target='fake'):
        if target not in ('fn1', 'fn2') or self.check(reply) is None:
            return None
        for row in ADJUDICATIONS:
            if target == 'fn2' and row['class'] != 'spec-ambiguity':
                continue
            if (row['verb'] == self.request.verb and row['argument_class'] == self.argument_class
                    and row['exit'] == reply['exit'] and row['reason'] == peer_reason(reply['text'])):
                return dict(deepcopy(row), target=target, request=self.request, observed_reply=dict(reply))
        return None

    def update(self, reply, target='fake'):
        recorded = self.recorded_difference(reply, target)
        problem = self.check(reply)
        if problem and recorded is None:
            raise AssertionError(problem)
        if not self.reason and recorded is None:
            self.model.apply(self.request)
        return recorded


class PeeringModel:
    VERBS = ('peer add', 'peer remove', 'peer list', 'peer set', 'peer feed', 'peer distributions',
             'peer budget', 'peer pull', 'peer pull-login', 'peer catch-up', 'peer login')

    def __init__(self):
        self.wire = NntpModel({g: {} for g in GROUPS}, [], {}, {'posting': True})
        self.peers = {}
        # Feed bookkeeping per scripted-peer port: queued (must arrive unless removed), permitted
        # (may arrive), paused_after (accepted while paused: never before the resume was asked).
        self.queued, self.permitted, self.held_back, self.release_at = {}, set(), {}, {}

    # -- the CLI -------------------------------------------------------------------------------
    def rule(self, verb, *args, password=None):
        if verb not in self.VERBS:
            raise ValueError('outside peering slice: ' + verb)
        return Expect(self, Request(verb, tuple(str(a) for a in args), password))

    def verdict(self, r):
        v, a = r.verb, r.args
        def bad(reason, cls, code=1):
            return code, reason, cls
        if any(not w or not w.isascii() for w in r.words):
            return bad('argv-malformed', 'malformed-argv', 5)
        if v == 'peer list':
            return (0, None, 'valid') if not a else bad('syntax', 'arity', 5)
        decimal = lambda w: bool(re.fullmatch(r'0|[1-9][0-9]*', w))
        if not a:
            return bad('syntax', 'arity', 5)
        if v == 'peer add':
            if len(a) != 9:
                return bad('syntax', 'arity', 5)
            name, path, host, port, inbound, outbound, kind, value, streaming = a
            if (not hostname(host) or not decimal(port) or not 0 < int(port) < 65536
                    or not pattern_ok(inbound) or not pattern_ok(outbound) or streaming not in ('true', 'false')
                    or not (kind == 'principal' and re.fullmatch(r'[0-9a-f]{64}', value)
                            or kind == 'source-address' and ipv4(value))):
                return bad('syntax', 'invalid-record', 5)
            return 0, None, 'valid'
        if v == 'peer feed' and (len(a) != 2 or a[1] not in ('pause', 'resume')):
            return bad('feed', 'invalid-feed', 5)
        if v == 'peer distributions' and (len(a) != 2 or a[1] == '-' or not pattern_ok(a[1])):
            return bad('distributions', 'invalid-wildmat', 5)
        if v == 'peer budget' and (len(a) != 3 or not decimal(a[1]) or not decimal(a[2])):
            return bad('budget', 'non-number', 5)
        if v == 'peer pull' and (len(a) not in (2, 3) or not all(decimal(w) for w in a[1:])):
            return bad('pull', 'non-number', 5)
        if v == 'peer pull-login' and (len(a) != 3 or a[2] not in ('true', 'false')):
            return bad('pull-login', 'invalid-flag', 5)
        if v == 'peer catch-up' and (len(a) != 2 or not decimal(a[1])):
            return bad('catch-up', 'non-number', 5)
        if v == 'peer set':
            words = a[1:]
            if not a or len(words) % 2 or not words:
                return bad('syntax', 'arity', 5)
            flags = words[0::2]
            if any(f not in SET_FLAGS for f in flags):
                return bad('unknown-flag', 'unknown-flag', 5)
        if a[0] not in self.peers:
            return bad('no-such-peer', 'unknown-peer')
        record = self.peers[a[0]]
        if v == 'peer set':
            edits = dict(zip(a[1::2], a[2::2]))
            if '--port' in edits and (not decimal(edits['--port']) or not 0 < int(edits['--port']) < 65536):
                return bad('port', 'invalid-port')
            outbound = edits.get('--send', record['outbound'])
            if outbound == '-' and ('--streaming' in edits or '--login' in edits):
                return bad('needs-send', 'nothing-sent')
        if v == 'peer login':
            if len(a) != 3:
                return bad('syntax', 'arity', 5)
            if record['outbound'] == '-':
                return bad('needs-send', 'nothing-sent')
            if not isinstance(r.password, tuple) or len(r.password) != 2 or r.password[0] != r.password[1]:
                return bad('passwords-differ', 'passwords-differ')
        return 0, None, 'valid'

    def line(self, name):
        p = self.peers[name]
        text = (f"{name} path-identity={p['path']} address={p['host']} port={p['port']} security={p['security']} "
                f"inbound={p['inbound']} outbound={p['outbound']} auth={p['kind']}:{p['value']}")
        if p['budget'] is not None:
            text += f" budget-octets={p['budget'][0]} budget-count={p['budget'][1]}"
        return text

    def check_list(self, text):
        rows = [row for row in text.splitlines() if ' path-identity=' in row]
        wanted = sorted(self.line(n) for n in self.peers)
        if sorted(rows) != wanted:
            return f'peer list: expected exactly {wanted}, observed {sorted(rows)}'
        return None

    def apply(self, r):
        v, a = r.verb, r.args
        if v == 'peer add':
            name, path, host, port, inbound, outbound, kind, value, streaming = a
            self.drop_feed(name)
            self.peers[name] = dict(path=path, host=host, port=port, security='clear', inbound=inbound,
                                    outbound=outbound, kind=kind, value=value, streaming=streaming == 'true',
                                    budget=None, paused=False, distributions=None, pull=0, catch_up=0,
                                    pull_login=None, login=None)
        elif v == 'peer remove':
            self.drop_feed(a[0])
            del self.peers[a[0]]
        elif v == 'peer set':
            p = self.peers[a[0]]
            for flag, value in zip(a[1::2], a[2::2]):
                if flag == '--source-address':
                    p.update(kind='source-address', value=value)
                elif flag == '--principal':
                    p.update(kind='principal', value=value)
                elif flag in ('--streaming', '--allow-clear'):
                    p[flag[2:].replace('-', '_')] = value == 'true'
                else:
                    p[{'--take': 'inbound', '--send': 'outbound'}.get(flag, flag[2:].replace('-', '_'))] = value
        elif v == 'peer feed':
            p = self.peers[a[0]]
            p['paused'] = a[1] == 'pause'
        elif v == 'peer distributions':
            self.peers[a[0]]['distributions'] = a[1]
        elif v == 'peer budget':
            self.peers[a[0]]['budget'] = (int(a[1]) // 4096 * 4096, int(a[2]))
        elif v == 'peer pull':
            self.peers[a[0]]['pull'] = int(a[1])
        elif v == 'peer pull-login':
            self.peers[a[0]]['pull_login'] = (a[1], a[2] == 'true')
        elif v == 'peer catch-up':
            self.peers[a[0]]['catch_up'] = int(a[1])
        elif v == 'peer login':
            self.peers[a[0]]['login'] = a[2]
        self.refresh_wire()

    # -- the wire seams ---------------------------------------------------------------------------
    def transit_peer(self):
        """The record a loopback connection is resolved to: a source-address 127.0.0.1 record with an
        inbound half. Exactly one such record is in the fixture's profile."""
        found = [n for n, p in self.peers.items()
                 if p['kind'] == 'source-address' and p['value'] == '127.0.0.1' and p['inbound'] != '-']
        if len(found) > 1:
            raise ValueError('two loopback transit records are outside the profile')
        return found[0] if found else None

    def refresh_wire(self):
        name = self.transit_peer()
        if name is None:
            self.wire.policy.pop('peers', None)
            self.wire.policy.pop('peer_accept', None)
        else:
            self.wire.policy['peers'] = ['127.0.0.1']
            self.wire.policy['peer_accept'] = self.peers[name]['inbound']

    def drop_feed(self, name):
        """A removed or replaced record's undelivered queue may still drain: permitted, not required."""
        p = self.peers.get(name)
        if p is None:
            return
        port = int(p['port'])
        self.permitted |= self.queued.pop(port, set()) | self.held_back.pop(port, set())

    def local_accept(self, ident, article, groups):
        """A completed local acceptance (operator post): file it on the wire and queue every feed."""
        self.wire.add_article(ident, article, list(groups))
        self.queue(ident, article, groups)

    def transferred(self, ident, article, local, target='fake'):
        """A completed transfer (transit or pull) filed in LOCAL: queue the feeds its local memberships
        name. For fn1 only, P01: fn1 feeds by the Newsgroups names, so the model follows that recorded
        effect (and a fixed fn1 then fails the next feed check: a stale row is loud). Returns the row."""
        names = [g.strip() for g in headers(article).get('newsgroups', b'').decode().split(',')]
        if target == 'fn1' and set(names) != set(local):
            self.queue(ident, article, names)
            return next(r for r in ADJUDICATIONS if r['group'] == 'P01')
        self.queue(ident, article, local)
        return None

    def queue(self, ident, article, groups):
        for p in self.peers.values():
            if p['outbound'] == '-' or not any(wildmat(p['outbound'], g) for g in groups):
                continue
            if not distribution_fed(p['distributions'], article):
                continue
            port = int(p['port'])
            if p['paused']:
                self.held_back.setdefault(port, set()).add(ident)
            else:
                self.queued.setdefault(port, set()).add(ident)

    def resumed(self, name, asked_at):
        """`peer feed NAME resume` accepted, asked at monotonic ASKED_AT: what queued while paused is due,
        and none of it may have reached the peer before ASKED_AT."""
        port = int(self.peers[name]['port'])
        for ident in self.held_back.pop(port, set()):
            self.queued.setdefault(port, set()).add(ident)
            self.release_at[(port, ident)] = asked_at

    def offer_verbs(self, name, mode_stream_ok):
        """The offer commands of a fed article: CHECK then TAKETHIS after MODE STREAM 203; IHAVE when the
        record does not stream or the peer answers 500/501 (specs/nntp.md:2445-2452)."""
        return ('CHECK', 'TAKETHIS') if self.peers[name]['streaming'] and mode_stream_ok else ('IHAVE',)

    def due(self, port):
        return set(self.queued.get(port, set()))

    def check_feed(self, port, received):
        """RECEIVED: ident -> monotonic time first offered. Every queued article arrived; nothing arrived
        that was never fed to this peer; nothing held back by a pause arrived before its resume."""
        due = self.queued.get(port, set())
        allowed = due | self.permitted | self.held_back.get(port, set())
        missing = sorted(due - set(received))
        extra = sorted(set(received) - allowed)
        early = sorted(i for i, t in received.items()
                       if i in self.held_back.get(port, set()) or t < self.release_at.get((port, i), t))
        if missing:
            return f'feed: queued articles never offered: {missing}'
        if extra:
            return f'feed: offered articles the model never fed this peer: {extra}'
        if early:
            return f'feed: offered while the feed was paused: {early}'
        return None

    def pull_round(self, name, own):
        """The scripted peer's own articles (ident -> octets) a NEWNEWS round lists: the ones whose
        Newsgroups names hold one in the record's accept-groups and live enter (by the node's own IHAVE
        verdict, so a held one is a duplicate); the rest never do. Returns (entering, never)."""
        p = self.peers[name]
        entering, never = {}, set()
        for ident, data in own.items():
            if ident in self.wire.articles:
                continue
            groups = [g.strip() for g in headers(data).get('newsgroups', b'').decode().split(',')]
            scope = [g for g in groups if g in self.wire.groups and not self.wire.flags[g].get('retired')
                     and p['inbound'] != '-' and wildmat(p['inbound'], g)]
            if scope:
                entering[ident] = (data, scope)
            else:
                never.add(ident)
        return entering, never
