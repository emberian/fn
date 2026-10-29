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

Where a source specifies a refusal without assigning its CLI name/exit,
this profile provisionally uses exit 1 and these words: group-name for invalid
create names, no-such-group for absent retire/moderation list, account-access
for malformed wildmats, account-unknown for absent delete, account-in-use for
a moderator deletion. Non-count capacity is provisionally usage 5/capacity;
malformed retention grammar is usage 5/retention. Unspecified moderation
absence/closed-state words not-held/already-approved/already-rejected are
provisional (carried native examples name the latter two). Principal list
uses the provisional public row shape LOGIN principal=HEX posting=BOOL;
specs/nntp.md:1597-1603 requires a public-only report but leaves its layout open. The seat must record actual
fn1 replies before adjudicating these choices. ADJUDICATIONS starts EMPTY.
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

ADJUDICATIONS = ()
GROUP = 'hz.test'
INITIAL_GROUPS = (GROUP, 'hz.mod', 'hz.mod.moderation', 'control.cancel')
PASSWORD = 'hz-fixture-password'  # FAKE-SECRET
NEW_PASSWORD = 'hz-replacement-password'  # FAKE-SECRET


def reason_word(text):
    """A recorded reason is a tag, never a matching word in explanatory prose."""
    found = re.findall(r'\(ADMINISTRATION ([A-Z][A-Z0-9-]*)\)', text)
    return found[0] if len(found) == 1 else None


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
        if reply['exit'] != self.exit:
            return f'{self.request.verb}: expected exit {self.exit}, reason {self.reason}'
        if self.reason and self.reason.lower() not in re.findall(r'[a-z][a-z0-9-]*', reply['text'].lower()):
            return 'expected named refusal ' + self.reason
        if not self.reason:
            return self.model.check_report(self.request, reply['text'])
        return None

    def recorded_difference(self, reply, target='fake'):
        if target not in ('fn1', 'fn2') or not self.reason or self.check(reply) is None:
            return None
        for row in ADJUDICATIONS:
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
            self.model.apply(self.request, reply)
        return recorded


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
        live = lambda name: name in self.groups and not self.groups[name].get('retired')
        if v == 'group create':
            if not re.fullmatch(r'[A-Za-z0-9_+-]+(?:\.[A-Za-z0-9_+-]+)*', a[0]) or a[0].startswith(('example', 'poster')):
                return bad('group-name', 'invalid-group')
            if live(a[0]):
                return bad('duplicate-group', 'duplicate-group')
        if v in ('group retire', 'group describe', 'group policy', 'group moderate', 'retention expire', 'moderation list'):
            if not live(a[0]):
                return bad('no-such-group', 'unknown-group')
        if v == 'group describe' and (not ' '.join(a[1:]).strip() or any(ord(c) < 32 or ord(c) > 126 for c in ' '.join(a[1:]))):
            return bad('description-blank' if not ' '.join(a[1:]).strip() else 'description-row', 'invalid-description')
        if v == 'group policy' and a[1] not in ('y', 'n'):
            return bad('group-status', 'invalid-status')
        if v == 'group moderate' and '--off' not in a:
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
            return bad('capacity', 'non-number', 5)
        if v == 'capacity' and int(a[0]) > 4294967295:
            return bad('capacity', 'above-u32', 5)
        if v == 'capacity' and int(a[0]) == 0 and self.wire.articles:
            return bad('capacity-below-reserved', 'below-reserved')
        if v == 'retention set' and a not in (('keep-forever',), ('released-by-all-holders',)) and not (
                len(a) == 2 and a[0] == 'release-after' and a[1].isdecimal()):
            return bad('retention', 'invalid-retention', 5)
        if v == 'retention expire' and a[1:] != ('clear',) and not (
                len(a) == 3 and a[1] in ('keep', 'default', 'purge', 'octets') and a[2].isdecimal()):
            return bad('retention', 'invalid-expiry', 5)
        if v == 'account access' and a != ('show',):
            try:
                wildmat(a[a.index('--read')+1], '')
                wildmat(a[a.index('--post')+1], '')
            except (ValueError, IndexError):
                return bad('account-access', 'invalid-wildmat')
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
            if '--off' in a:
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

    def redeemed(self, code, login, password):
        self.pending.remove(code)
        self.accounts[login] = {'password': password, 'posting': True}
        self.refresh_accounts()
