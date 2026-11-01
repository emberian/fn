"""HZ operator state, composed into the existing NNTP model (rows 76-77).

SPEC-MAP (line numbers at 287655a40)
 verb / expected exit, named reason, effect       source
 all accepted 0, refused 1/no change, usage 5     docs/operator.md:1232-1242
 every empty/non-ASCII argv: 5 ARGV-MALFORMED     specs/native-admin.md:8-15
 group create/retire: served/retired, retained    docs/operator.md:246-259;
   duplicate-group, no-such-group                specs/reconfiguration.md:470-508
 group describe: exact text; no-such-group,      specs/nntp.md:188-235
   description-row, description-blank
 group policy y/n; no-such-group, group-status   specs/nntp.md:1046-1089
 group moderate/off: queue, moderators,          specs/nntp.md:1099-1135;
   moderation-queue / no-such-group              docs/operator.md:271-311
 moderation list: held/approved/rejected rows;   specs/nntp.md:1186-1203;
   approve publishes, reject withdraws envelope; docs/operator.md:289-305
   not-a-moderator
 motd set/clear: LIST MOTD exact lines           specs/nntp.md:188-235
 capacity: charge-capacity; below-reserved       docs/operator.md:1365-1368;
   refusal capacity-below-reserved               specs/reconfiguration.md:482-484
 retention set / expire: release authorization,  specs/storage.md:1266-1285,
   no content removal without reclaim           1420-1424; docs/operator.md:1194
 account invite/list: single hex code; pending   specs/nntp.md:1795-1815,1903-1914;
   expiry, no password/code in listing           docs/operator.md:334-364
 account/principal set-password: override,      docs/operator.md:315-332,383-386;
   posting flag, live reload; list public only   specs/nntp.md:1597-1610,2006-2010
 account access read/post wildmats; hide groups  docs/operator.md:388-410;
   and refuse POST, malformed patterns refused   specs/nntp.md:1919-1964
 account/principal delete: file credential       docs/operator.md:367-386;
   first, then tombstone; moderator dependency   specs/nntp.md:1816-1837
 AUTHINFO / GROUP / POST / LIST / STAT / BODY     nntp_model.SPECS (sole wire oracle)

Reply shape: the exit code, and the tagged result line `WORD operator SUBJECT
[REASON]` whose WORD names that exit (docs/operator.md:1232-1242; result_line).
A refusal's reason is a tag (reason_word), never a word found in usage prose.
Where the docs name the class (refused 1, usage 5) but not the tag, the tag is
fn1's as recorded by the HZ2 probe (hbox image c14e9e8e, TREE_SHA d377d4559;
build/coordinator/fn2/lanes/h-quests/wp2-operator.json): ARGV-MALFORMED (usage),
SYNTAX (usage: capacity not a u32 decimal), ACCESS-PATTERN (usage: a malformed
wildmat); refused: duplicate-group, no-such-group, capacity-below-reserved,
moderation-queue, not-a-moderator, account-unknown. The fixed witnesses agree
with fn1 on every reply (the probe: 62 CLI calls, zero disagreements) once
ADJUDICATIONS' O01 (group retire keeps the group served) is applied. A malformed group
name is SYNTAX (usage), as the live S run found. Tags no witness reaches yet
stay provisional: reserved-group-name, description-blank/-row,
group-status, not-held, already-approved/-rejected, account-in-use, retention.
All per-verb refusal witnesses also exercise the explicitly named universal
ARGV-MALFORMED preflight; they are not assertions about inferred fn1 text.

Next slice (OUT OF SCOPE): authority, subscribe-default, account hash,
principal bind/unbind, consumer bind/unbind/show (consumer S owns those), and
every other operator family row. This small profile does not reclaim content,
exercise expiry's clock, prove password cryptography, or compare injected
private-account headers. The wire model uses source bodies as an uninterpreted
stored_articles projection; BODY/STAT and group membership remain checked.

Design note for Astra: I keep state transitions in this CLI model and reuse
NntpModel's existing state/environment seams, with a fresh connection after
each effect. A second wire renderer in the oracle would drift on pinned views;
the independent finite fake renderer is only a mutation control. General old
session reload schedules belong to the existing NNTP/TLS forms.
"""
from copy import deepcopy
from dataclasses import dataclass
import re

from .nntp_model import NntpModel, wildmat

# Rows only from recorded fn1 replies (HZ2 probe, hbox image c14e9e8e, TREE_SHA
# d377d4559; build/coordinator/fn2/lanes/h-quests/wp2-operator.json, hz-micro.py).
ADJUDICATIONS = (
    dict(group='O01', kind='effect', verb='group retire', argument_class='valid', effect='served-while-retired',
         spec='docs/operator.md:248-256 (retire: stop serving the group)',
         fn1_reply=dict(exit=0, tagged='accepted operator group ACCEPTED'),
         observed='the configuration retires the group (group create is then accepted and restores its '
                  'description) but the reader wire keeps serving it: LIST ACTIVE lists it and GROUP answers '
                  '211 at once, after 3 s and after a restart; LIST NEWSGROUPS shows (no description)',
         **{'class': 'fn1-bug'}),
)
GROUP = 'hz.test'
INITIAL_GROUPS = (GROUP, 'hz.mod', 'hz.mod.moderation', 'control.cancel')
PASSWORD = 'hz-fixture-password'  # FAKE-SECRET
NEW_PASSWORD = 'hz-replacement-password'  # FAKE-SECRET


WORDS = {0: 'accepted', 1: 'refused', 3: 'uncertain', 4: 'fault', 5: 'usage'}


def result_line(text):
    """The CLI's tagged result line, `WORD operator SUBJECT[ REASON]`.

    docs/operator.md:1232-1242 ties WORD to the exit code; fn1 renders it in
    host/native/operator.lisp fnn-operator-emit-status as the last stderr line,
    after any hint and after the unterminated `Password: ` prompts (hence the
    `: ` prefix). Returns (word, subject, reason-or-None), or None when the
    reply carries no tagged line (fn1's `store` sub-verbs inspect and import
    print their own report instead).
    """
    found = re.findall(r'(?:^|: )(accepted|refused|uncertain|fault|usage) operator (\S+)(?: (.*))?$', text, re.M)
    if not found:
        return None
    word, subject, rest = found[-1]
    # The administration layer's result renders as `(ADMINISTRATION X)`, or as
    # its status echoed before the tag: `REFUSED duplicate-group`, `ACCEPTED`.
    tokens = [t for t in re.findall(r'[A-Za-z0-9][A-Za-z0-9-]*', rest)
              if t not in ('ADMINISTRATION', 'ACCEPTED', 'REFUSED', 'USAGE')]
    return word, subject, tokens[0].lower() if tokens else None


def reason_word(text):
    """The named reason as a tag, never a matching word in prose.

    In order: the one `reason=X` key (export, import, bless-snapshot, which
    fn1 also forwards inside the tagged line, `refused operator import import
    refused reason=X`; docs/install.md `reason=interrupted-import`); else the
    tagged line's REASON (`(ADMINISTRATION X)` names X); else a report line
    `refused X ...` (store inspect --group). Two distinct `reason=` keys name
    nothing.
    """
    keyed = set(re.findall(r'\breason=([A-Za-z0-9-]+)', text))
    if keyed:
        return keyed.pop().lower() if len(keyed) == 1 else None
    line = result_line(text)
    if line and line[2]:
        return line[2]
    found = re.findall(r'^refused ([a-z][a-z0-9-]*)\b', text, re.M)
    return found[0] if len(found) == 1 else None


def result_problem(reply, exit_code, reason, *, tagged=True):
    """Exit, the tagged line's word for it, and the exact named reason.

    TAGGED: the verb must print the tagged line; otherwise a tagged line, when
    present, must still carry the exit's word.
    """
    if reply.get('exit') != exit_code:
        return f'expected exit {exit_code}' + (f', reason {reason}' if reason else '')
    line = result_line(reply.get('text', ''))
    if (line is None and tagged) or (line is not None and line[0] != WORDS.get(exit_code)):
        return f'expected the tagged result line `{WORDS.get(exit_code)} operator ...`'
    if reason and reason_word(reply.get('text', '')) != reason:
        return f'expected named refusal {reason}, observed {reason_word(reply.get("text", ""))}'
    return None


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
        problem = result_problem(reply, self.exit, self.reason)
        if problem:
            return f'{self.request.verb}: {problem}'
        if not self.reason:
            return self.model.check_report(self.request, reply['text'])
        return None

    def recorded_difference(self, reply, target='fake'):
        if target not in ('fn1', 'fn2'):
            return None
        if not self.reason:
            # An effect row: the verb is accepted as the model says, and the
            # target is recorded NOT to apply its effect. The model then follows
            # the recorded effect, so every later wire read checks it (a fixed
            # target fails the next observation: a stale row is loud).
            if self.check(reply) is not None:
                return None
            for row in ADJUDICATIONS:
                if (row.get('kind') == 'effect' and row['verb'] == self.request.verb
                        and (target == 'fn1' or row['class'] == 'spec-ambiguity')):
                    return dict(deepcopy(row), target=target, request=self.request,
                                observed_reply=dict(reply))
            return None
        if self.check(reply) is None:
            return None
        for row in ADJUDICATIONS:
            if row.get('kind') == 'effect':
                continue
            if target == 'fn2' and row['class'] != 'spec-ambiguity':
                continue
            if (row['verb'] == self.request.verb and row['argument_class'] == self.argument_class
                    and row['exit'] == reply['exit'] and row['reason'] == reason_word(reply['text'])):
                return dict(deepcopy(row), target=target, request=self.request,
                            observed_reply=dict(reply))
        return None

    def update(self, reply, target='fake'):
        recorded = self.recorded_difference(reply, target)
        problem = self.check(reply)
        if problem and recorded is None:
            raise AssertionError(problem)
        # A recorded refusal remains a refusal. Never apply an unobserved effect.
        if not self.reason:
            if recorded is None:
                self.model.apply(self.request, reply)
            else:
                self.model.apply_recorded(recorded['effect'], self.request)
        return recorded


def moderate_off(a):
    """`group moderate G --off`: --off as a flag of its own, never as the value of --queue or --moderators."""
    return any(w == '--off' and (i == 0 or a[i - 1] not in ('--queue', '--moderators')) for i, w in enumerate(a))


class OperatorModel:
    VERBS = ('group create', 'group retire', 'group describe', 'group policy',
             'group moderate', 'moderation list', 'moderation approve', 'moderation reject',
             'motd set', 'motd clear', 'capacity', 'retention set', 'retention expire',
             'account invite', 'account list', 'account set-password', 'account access',
             'account delete', 'principal list', 'principal set-password', 'principal delete')

    def __init__(self):
        self.wire = NntpModel({g: {} for g in INITIAL_GROUPS}, [], {}, {'posting': True})
        self.groups = self.wire.flags
        self.principals, self.accounts, self.access, self.pending = {}, {}, {}, []
        self.deleted, self.held, self.file_logins_seen = set(), {}, set()
        self.motd, self.capacity, self.retention = [], None, ('keep-forever',)
        self.expiry = {}
        # O01: groups the configuration retired while the recorded target keeps
        # serving them on the wire, with each one's description held back.
        self.served_retired = {}

    def rule(self, verb, *args, password=None):
        if verb not in self.VERBS:
            raise ValueError('outside operator slice: ' + verb)
        return Expect(self, Request(verb, tuple(str(a) for a in args), password))

    def verdict(self, r):
        v, a = r.verb, r.args
        def bad(reason, cls, code=1):
            return code, reason, cls
        if any(not w or not w.isascii() for w in r.words):
            return bad('argv-malformed', 'malformed-argv', 5)
        live = lambda name: (name in self.groups and not self.groups[name].get('retired')
                             and name not in self.served_retired)
        named = lambda name: re.fullmatch(r'[A-Za-z0-9_+-]+(?:\.[A-Za-z0-9_+-]+)*', name) is not None
        # H7d (argv fuzz on fn1, image c14e9e8e): a malformed group name is usage before any state is read,
        # tagged per verb as fn1 tags it; `group policy` takes only y/n, any other status is usage SYNTAX.
        if v in ('group retire', 'group policy') and not named(a[0]):
            return bad('syntax', 'invalid-group', 5)
        if v in ('group describe', 'group moderate') and not named(a[0]):
            return bad('group-name', 'invalid-group', 5)
        if v == 'group moderate' and '--queue' in a and not named(a[a.index('--queue') + 1]):
            return bad('group-name', 'invalid-group', 5)
        if v == 'group policy' and a[1:] not in (('y',), ('n',)):
            return bad('syntax', 'invalid-status', 5)
        if v == 'group create':
            if not named(a[0]):
                return bad('syntax', 'invalid-group', 5)
            # RFC 5536 §3.1.4 (docs/operator.md:255-256): first component
            # `example`, or exactly `poster`. Tag provisional (fn1's init tag).
            if a[0].lower().split('.')[0] == 'example' or a[0].lower() == 'poster':
                return bad('reserved-group-name', 'reserved-group')
            if live(a[0]):
                return bad('duplicate-group', 'duplicate-group')
        # moderation list names no refusal (specs/nntp.md:1186-1192); fn1 reports
        # an unmoderated or absent group as `moderated=no` (HZ2 live run).
        # `retention expire {GROUP | *}` names a policy, not a served group (docs/operator-internals.md:510-514;
        # fn1 accepts it for a group no store holds, H7d): no existence check.
        if v in ('group retire', 'group describe', 'group policy', 'group moderate'):
            if not live(a[0]):
                return bad('no-such-group', 'unknown-group')
        if v == 'group describe' and (not ' '.join(a[1:]).strip() or any(ord(c) < 32 or ord(c) > 126 for c in ' '.join(a[1:]))):
            return bad('description-blank' if not ' '.join(a[1:]).strip() else 'description-row', 'invalid-description')
        if v == 'group moderate' and not moderate_off(a):
            q = a[a.index('--queue')+1] if '--queue' in a else a[0] + '.moderation'
            if not live(q) or q == a[0] or self.groups[q].get('moderated'):
                return bad('moderation-queue', 'invalid-queue')
        if v.startswith('moderation ') and v != 'moderation list':
            held = self.held.get(a[0])
            if held is None:
                return bad('not-held', 'unknown-article')
            moderator = a[a.index('--moderator') + 1]
            if moderator not in self.groups[held['group']].get('moderators', []):
                return bad('not-a-moderator', 'non-moderator')
            if held['state'] != 'held':
                return bad('already-' + held['state'], 'closed-envelope')
        if v == 'capacity' and not re.fullmatch(r'0|[1-9][0-9]*', a[0]):
            return bad('syntax', 'non-number', 5)
        if v == 'capacity' and int(a[0]) > 4294967295:
            return bad('syntax', 'above-u32', 5)
        if v == 'capacity' and int(a[0]) == 0 and self.wire.articles:
            return bad('capacity-below-reserved', 'below-reserved')
        if v == 'retention set' and a not in (('keep-forever',), ('released-by-all-holders',)) and not (
                len(a) == 2 and a[0] == 'release-after' and a[1].isdecimal()):
            return bad('retention', 'invalid-retention', 5)
        if v == 'retention expire' and (not (a[0] == '*' or named(a[0])) or a[1:] != ('clear',) and not (
                len(a) == 3 and a[1] in ('keep', 'default', 'purge', 'octets') and a[2].isdecimal()
                and int(a[2]) <= 4294967295)):
            return bad('retention', 'invalid-expiry', 5)
        if v == 'account access' and a != ('show',):
            # H7d: a call without its --read and --post values is SYNTAX; a malformed pattern is ACCESS-PATTERN.
            flags = [i for i, w in enumerate(a) if w in ('--read', '--post')]
            if len(a) != 5 or sorted(a[i] for i in flags) != ['--post', '--read'] or any(i + 1 >= len(a) for i in flags):
                return bad('syntax', 'invalid-access', 5)
            try:
                wildmat(a[a.index('--read')+1], '')
                wildmat(a[a.index('--post')+1], '')
            except (ValueError, IndexError):
                return bad('access-pattern', 'invalid-wildmat', 5)
        if v in ('account delete', 'principal delete'):
            if a[0] not in self.principals and a[0] not in self.accounts:
                return bad('account-unknown', 'unknown-account')
            if a[0] not in self.principals and any(a[0] in f.get('moderators', []) for f in self.groups.values()):
                return bad('account-in-use', 'moderator-dependency')
        return 0, None, 'valid'

    def check_report(self, r, text):
        v, a = r.verb, r.args
        if v == 'account invite':
            codes = re.findall(r'^[0-9a-f]{32}$', text, re.M)
            if len(codes) != 1 or codes[0] in self.pending:
                return 'invite: expected one fresh 32-hex code'
        if v in ('account list', 'account access') and (v == 'account list' or a == ('show',)):
            for login in self.accounts:
                if not re.search(r'^redeemed ' + re.escape(login) + r' [0-9a-f]{64}$', text, re.M):
                    return 'list: missing redeemed account ' + login
            for login in self.deleted:
                if 'deleted ' + login not in text.splitlines():
                    return 'list: missing deleted account ' + login
            for login, (read, post) in self.access.items():
                if 'access ' + login + ' read ' + read + ' post ' + post not in text.splitlines():
                    return 'list: missing access row'
            if len(re.findall(r'^pending expires \d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ$', text, re.M)) != len(self.pending):
                return 'list: pending count/UTC expiry'
            if any(code in text for code in self.pending):
                return 'list: invitation code disclosure'
        if v == 'principal list':
            rows = re.findall(r'^(\S+) principal=([0-9a-f]{64}) posting=(true|false)(?: .*)?$', text, re.M)
            wanted = {login: 'true' if row['posting'] else 'false' for login, row in self.principals.items()}
            if {login: posting for login, _, posting in rows} != wanted or len(rows) != len(wanted):
                return 'principal list: exact login set, principal and posting flag'
        if v in ('account list', 'principal list'):
            for row in (*self.principals.values(), *self.accounts.values()):
                if row['password'] in text:
                    return 'list: password disclosure'
        if v == 'moderation list' and not self.groups.get(a[0], {}).get('moderated'):
            if f'moderation group={a[0]} moderated=no' not in text.splitlines():
                return 'moderation list: an unmoderated group reports moderated=no'
            return None
        if v == 'moderation list':
            f = self.groups[a[0]]
            expected = [h for h in self.held.values() if h['group'] == a[0]]
            count = sum(h['state'] == 'held' for h in expected)
            if f'moderation group={a[0]} queue={f.get("queue", a[0] + ".moderation")} held={count}' not in text.splitlines():
                return 'moderation list: group/queue/held count'
            for ident, h in self.held.items():
                if h['group'] == a[0] and not any(h['state'] in line.split() and ident in line and h['envelope'] in line for line in text.splitlines()):
                    return 'moderation list: missing envelope state/identity'
        return None

    def refresh_accounts(self):
        self.wire.accounts = deepcopy(self.accounts)
        self.wire.accounts.update(deepcopy(self.principals))
        for login, (read, post) in self.access.items():
            if login == '':
                self.wire.policy['anonymous_access'] = {'read': read, 'post': post}
            elif login in self.wire.accounts:
                self.wire.accounts[login].update(read=read, post=post)

    def apply(self, r, reply):
        v, a, w = r.verb, r.args, self.wire
        if v == 'group create':
            self.groups.setdefault(a[0], {}).pop('retired', None)
            held = self.served_retired.pop(a[0], None)
            if held is not None:
                self.groups[a[0]]['description'] = held
            w.groups.setdefault(a[0], [])
            w.watermarks.setdefault(a[0], 0)
            w.issued.setdefault(a[0], [])
        elif v == 'group retire':
            w.retire_group(a[0])
        elif v == 'group describe':
            self.groups[a[0]]['description'] = ' '.join(a[1:])
        elif v == 'group policy':
            self.groups[a[0]]['posting'] = a[1]
        elif v == 'group moderate':
            f = self.groups[a[0]]
            if moderate_off(a):
                for key in ('moderated', 'moderators', 'queue'):
                    f.pop(key, None)
            else:
                f.update(moderated=True, moderators=a[a.index('--moderators')+1].split(','),
                         queue=a[a.index('--queue')+1] if '--queue' in a else a[0] + '.moderation')
        elif v in ('motd set', 'motd clear'):
            self.motd = list(a) if v == 'motd set' else []
            w.policy['motd'] = list(self.motd)
        elif v == 'capacity':
            self.capacity = int(a[0])
        elif v == 'retention set':
            self.retention = a
        elif v == 'retention expire':
            if a[1:] == ('clear',):
                self.expiry.pop(a[0], None)
            else:
                self.expiry[a[0]] = a[1:]
        elif v == 'account invite':
            self.pending.append(re.findall(r'^[0-9a-f]{32}$', reply['text'], re.M)[0])
        elif v in ('account set-password', 'principal set-password'):
            self.principals[a[0]] = {'password': r.password, 'posting': '--no-posting' not in a}
            self.file_logins_seen.add(a[0])
        elif v == 'account access' and a != ('show',):
            self.access['' if a[0] == '--anonymous' else a[0]] = (a[a.index('--read')+1], a[a.index('--post')+1])
        elif v in ('account delete', 'principal delete'):
            if a[0] in self.principals:
                del self.principals[a[0]]
            else:
                del self.accounts[a[0]]
                self.deleted.add(a[0])
        elif v in ('moderation approve', 'moderation reject'):
            h = self.held[a[0]]
            h['state'] = 'approved' if v.endswith('approve') else 'rejected'
            if v.endswith('approve'):
                w.add_article(a[0], h['source'], [h['group']])
            else:
                w.withdraw(h['envelope'])
                # NNT-010/PKT-575: reject files a cancel under this derived ID.
                cancel = '<fn-withdraw.' + h['envelope'][1:]
                w.add_article(cancel, b'\r\n', ['control.cancel'])
        self.refresh_accounts()

    def apply_recorded(self, effect, r):
        """The effect an adjudication row records the target applying instead."""
        if effect == 'served-while-retired':
            # Retired in the configuration (create comes back as it was) but
            # still on the reader wire, its description shown as absent.
            self.served_retired[r.args[0]] = self.groups[r.args[0]].pop('description', None)
        else:
            raise ValueError('unknown recorded effect ' + effect)

    def redeemed(self, code, login, password):
        self.pending.remove(code)
        self.accounts[login] = {'password': password, 'posting': True}
        self.refresh_accounts()
