"""HW: independent live policy state, composed with the one NNTP wire oracle.

SPEC-MAP (line numbers at 095433a9f)
===============================
Keys / decision                         Source / wire effect
exposure-{connections,per-address,       specs/nntp.md:2301-2384: admission 400
 steps-per-second,first-seconds,         and close, step wait, silent deadlines,
 idle-seconds,auth-failures,              address 481 budget, principal post wait;
 posts-per-minute}, anonymous,           loopback/public defaults differ. uint32
 exposure-trusted                       row width: 2352-2357; trusted: 2364-2376.
tls-handshakes-per-source-per-minute,    docs/operator.md:608-685; specs/host.md:
 tls-handshakes-in-flight,               1629-1637: 30/min, 16 slots, 5000 ms;
 tls-handshake-ms,                       source/proxy overrides default none;
 tls-handshake-source-overrides,         malformed overrides: override-address,
 tls-proxy-trusted-peers                 >64 entries: overrides-full.
log-batch-records, log-batch-octets       specs/storage.md:443-451: batch work;
                                        fn2/docs/design/RELEASE-PLAN.md:89: 64 / 16 MiB.
barrier-deadline-ms, barrier-stall-ms,    specs/host.md:815-823: positive ms,
 clock-event-ms                         5000/30000/1000, issued batch pins them.
compress-min-octets                     fn2/docs/design/RELEASE-PLAN.md:89; threshold/off=0
                                        grammar is NOT specified there (gap).
disk-reserve-octets                     specs/host.md:939-950: 64 MiB, disk-full
                                        write shedding; not a wire byte ceiling.
relay-date-skew, refused-offer-capacity, specs/peering.md:1005-1045: 86400/4096/0;
 relay-require-path                     dated-future refusal / remembered offer /
                                        require Path when 1.
path-identity, posting-policy,           specs/native-admin.md:21-29;
 complaints-to                          specs/identity.md:427; specs/nntp.md:
                                        1232-1241,1301-1306: Path, signed login,
                                        Injection-Info; unset/open/unset.
max-transactions, max-history-octets,    specs/storage.md:66-106: sealed profile
 max-article-octets                     defaults, requested != funded != ceiling;
                                        below-current-use, profile-invalid,
                                        above-representation-ceiling, resource
                                        refusals. specs/reconfiguration.md:
                                        1622-1648: completion-reserve and A is
                                        recorded for restart, never live-funded.
set exit / printed line                 docs/operator.md:1233-1241: 0 accepted,
                                        1 refused with named reason, unchanged.
                                        Success: any line (no literal specified
                                        by docs/operator.md:428-673).
unknown key / non-count value            specs/host.md:1779: unknown-policy-key /
                                        policy-value-not-a-number; no mutation.
init-only fields / accepted TOML keys    specs/storage.md:46-64,83-85,113-128;
                                        specs/native-config.md:6-45,109-122,
                                        218-250; fn2/docs/design/RELEASE-PLAN.md:88-90.

The cited specs do not specify generic invalid-range reason words, every text
grammar, or all count lower bounds. Generic range/text refusal `policy` with
exit 1, positive batch / TLS counts and zero-off compression remain provisional
profile choices. docs/operator.md:1236,1239 distinguishes refused from usage
but does not assign every malformed policy value to one: HY records those
exit-5 replies as ambiguities, not model corrections. Named count refusals
(specs/host.md:1779) and override-address (docs/operator.md:657-662) remain
exit 1. ADJUDICATIONS separates recorded fn1 bugs from these ambiguities;
fn2 permits only ambiguities, fake targets none. No implementation is imported.
Store defaults are explicit fixture inputs. Accepted sets require exit 0 and
accept any line; no literal success text is specified. Refusals require exit 1
and the reason word, without assuming an otherwise unspecified line format.
"""
from copy import deepcopy
from dataclasses import dataclass
import ipaddress
import re

U32 = (1 << 32) - 1
# HY, recorded on fn1 image c14e9e8e / TREE_SHA d377d4559. Full witnesses
# are data; matching never depends on the variable explanatory key-list prose.
_FN1_USAGE = (
    'usage: fn operator CONFIG policy set KEY VALUE, KEY one of: path-identity IDENTITY | '
    'posting-policy bound-logins|open | complaints-to ADDR | anonymous none|open | '
    'exposure-connections N | exposure-per-address N | exposure-steps-per-second N | '
    'exposure-idle-seconds N | exposure-first-seconds N | exposure-auth-failures N | '
    'exposure-posts-per-minute N | exposure-trusted CIDR[,CIDR...]|none | '
    'relay-date-skew SECONDS | refused-offer-capacity N | relay-require-path 0|1 | '
    'log-batch-records N | log-batch-octets N | barrier-deadline-ms N | barrier-stall-ms N | '
    'clock-event-ms N | compress-min-octets N | disk-reserve-octets N | max-transactions N | '
    'max-history-octets N | max-article-octets N (each applies to a running node at once, '
    'the three store limits as their answer says: now, at the next start, or refused by name)\n')
ADJUDICATIONS = (
    {
        'group': 'L01', 'seat_group': 'G0', 'class': 'fn1-bug',
        'command': 'greeting', 'spec_lines': 'specs/nntp.md:2315-2320',
        'spec_status': b'400 too many authentication failures from this address\r\n',
        'fn1_status': b'400 too many authentication failures from this address; try again later\r\n',
        'eof': True,
        'reasoning': 'The auth-failure line lacks the suffix that the two capacity lines specify.',
    },
    {
        'group': 'L02', 'seat_group': 'G1', 'class': 'fn1-bug',
        'spec_lines': 'specs/host.md:1779; docs/operator.md:612-615,1236',
        'keys': ('tls-handshakes-per-source-per-minute', 'tls-handshakes-in-flight',
                 'tls-handshake-ms', 'log-batch-records', 'log-batch-octets',
                 'barrier-deadline-ms', 'barrier-stall-ms', 'clock-event-ms',
                 'disk-reserve-octets'),
        'value_classes': ('non-number', 'negative'),
        'exit': 1, 'reason': 'UNKNOWN-POLICY-KEY',
        'witness': 'policy set: no key by that name; the keys are path-identity, posting-policy, exposure-connections, exposure-per-address, exposure-steps-per-second, exposure-idle-seconds, exposure-first-seconds, exposure-auth-failures, exposure-posts-per-minute, relay-date-skew, refused-offer-capacity, relay-require-path, max-transactions, max-history-octets, max-article-octets (docs/operator.md)\nrefused operator policy (ADMINISTRATION UNKNOWN-POLICY-KEY)\n',
        'reasoning': 'Known counted keys accept valid values; non-counts owe policy-value-not-a-number.',
    },
    {
        'group': 'L03', 'seat_group': 'G2', 'class': 'spec-ambiguity',
        'spec_lines': 'docs/operator.md:1236,1239',
        'keys': ('exposure-trusted', 'anonymous', 'path-identity', 'posting-policy', 'complaints-to'),
        'value_classes': ('malformed-text',), 'exit': 5, 'reason': 'POLICY',
        'witness': _FN1_USAGE + 'usage operator policy (ADMINISTRATION POLICY)\n',
        'reasoning': 'Wrong command permits a usage reading, but no rule assigns these invalid values to exit 5.',
    },
    {
        'group': 'L04', 'seat_group': 'G3', 'class': 'fn1-bug',
        'spec_lines': 'docs/operator.md:657-662,1236,1239',
        'keys': ('tls-handshake-source-overrides',),
        'value_classes': ('malformed-text',), 'exit': 5, 'reason': 'OVERRIDE-ADDRESS',
        'witness': _FN1_USAGE + 'usage operator policy (ADMINISTRATION OVERRIDE-ADDRESS)\n',
        'reasoning': 'An unparseable entry is explicitly refused override-address; refused is exit 1.',
    },
    {
        'group': 'L05', 'seat_group': 'G4', 'class': 'spec-ambiguity',
        'spec_lines': 'specs/peering.md:1030-1043; specs/host.md:1779; docs/operator.md:1236,1239',
        'keys': ('relay-require-path',),
        'value_classes': ('non-number', 'negative', 'above-maximum'),
        'exit': 5, 'reason': 'POLICY',
        'witness': _FN1_USAGE + 'usage operator policy (ADMINISTRATION POLICY)\n',
        'reasoning': 'The 0/1 Path switch can be read as an enum or a count; invalid-value exit is unspecified.',
        'alternative': 'Non-count inputs are fn1-bug if HST-037 counted-key wording includes this switch.',
    },
    {
        'group': 'L06', 'seat_group': 'G5', 'class': 'spec-ambiguity',
        'spec_lines': 'specs/peering.md:1033-1036; docs/operator.md:1236,1239',
        'keys': ('relay-date-skew',), 'value_classes': ('above-maximum',),
        'exit': 5, 'reason': 'POLICY',
        'witness': _FN1_USAGE + 'usage operator policy (ADMINISTRATION POLICY)\n',
        'reasoning': 'The 86400 maximum is specified; the exit for a decimal count above it is not.',
    },
)
# These are fixture choices, not universal defaults. Pin R as well as H so
# init's profile resolution cannot silently choose an R larger than our H.
# specs/storage.md:46-128 makes these operator inputs subject to profile
# relations; docs/operator-internals.md:210-215 spells out R <= H and
# docs/operator.md:1321-1327 specifies init's named refusal. 24 MiB is the
# documented development history size, not a number learned from fn1 replies.
INIT_RECORD_OCTETS = 24 * 1024 * 1024
STORE_DEFAULTS = {'max-transactions': 4096,
                  'max-history-octets': max(16 * 1024 * 1024, INIT_RECORD_OCTETS),
                  'max-article-octets': 32768}  # explicit init fixture, not universal defaults
STORE_INIT = {'max-record-octets': INIT_RECORD_OCTETS, **STORE_DEFAULTS}
INIT_FIXED = ('max-record-octets', 'max-groups-per-article', 'max-open-suffix',
              'max-consumers', 'max-config-generations', 'max-credentials',
              'max-bp-rows', 'max-group-name-octets', 'max-policy-members', 'profile', 'budget')
TOML_KEYS = {
    'store': ('path',), 'listener': ('host', 'port', 'tls_cert', 'tls_key', 'tls_port'),
    'auth': ('required', 'protected_only', 'path'), 'posting': ('enabled', 'agent'),
    'anchor': ('server',), 'acl2': ('path', 'slots'), 'log': ('path',), 'control': ('path',),
    'alerts': ('command', 'headroom_min_percent', 'refusal_rate_per_minute', 'cooldown_seconds'),
    'web': ('port', 'host', 'site', 'domain', 'proxied', 'tls', 'idle_seconds', 'max_sessions'),
    'tls': ('key_exchange',),
    'resources': ('cold_heap_octets', 'cold_workers', 'cold_descriptors', 'cold_read_ids',
                  'cold_file_ids', 'output_heap_octets', 'output_quantum_heap_octets', 'reclaim_live'),
    'ops': ('mission', 'unit', 'scope', 'keep_releases', 'log_max_bytes', 'log_keep', 'memory_max'),
}


@dataclass(frozen=True)
class OperatorExpectation:
    exit: int
    reason: str | None = None

    def check(self, result):
        if result['exit'] != self.exit:
            return f'operator: expected exit {self.exit}'
        words = re.findall(r'[a-z][a-z0-9-]*', result['text'].lower())
        if self.reason and self.reason.lower() not in words:
            return 'operator: expected named refusal ' + self.reason
        return None


def init_history_expectation(history_octets, record_octets):
    """The H >= R relation, for an otherwise valid explicit init fixture.

    This does not model the remaining profile or machine-budget refusals.
    Refusal is exit 1, distinct from a configuration grammar/usage error (5).
    """
    if history_octets < record_octets:
        return OperatorExpectation(1, 'MAX-HISTORY-OCTETS-BELOW-MAX-RECORD-OCTETS')
    return OperatorExpectation(0)


@dataclass(frozen=True)
class Key:
    kind: str
    default: int | str
    effect: str
    minimum: int = 0
    maximum: int = U32
    choices: tuple = ()
    public: int | str | None = None


KEYS = {
    'exposure-connections': Key('count', 31, 'capacity 400 + close'),
    'exposure-per-address': Key('count', 'total', 'address capacity 400 + close', public=8),
    'exposure-steps-per-second': Key('count', 0, 'wait per address / second', public=64),
    'exposure-first-seconds': Key('count', 0, 'first-command silent close', public=60),
    'exposure-idle-seconds': Key('count', 0, 'idle silent close', public=600),
    'exposure-auth-failures': Key('count', 0, '481 budget / address / minute', public=10),
    'exposure-posts-per-minute': Key('count', 0, 'wait per principal / minute', public=60),
    'exposure-trusted': Key('ranges', 'none', 'exempt address connection bound'),
    'anonymous': Key('enum', 'open', '480 authentication gate', choices=('none', 'open'), public='none'),
    'tls-handshakes-per-source-per-minute': Key('count', 30, 'TLS source token bucket', 1),
    'tls-handshakes-in-flight': Key('count', 16, 'TLS global admission', 1),
    'tls-handshake-ms': Key('count', 5000, 'TLS handshake close deadline', 1),
    'tls-handshake-source-overrides': Key('overrides', 'none', 'TLS source budget exceptions'),
    'tls-proxy-trusted-peers': Key('ranges', 'none', 'TLS PROXY header required'),
    'log-batch-records': Key('count', 64, 'commit batch count', 1),
    'log-batch-octets': Key('count', 16777216, 'commit batch octets', 1),
    'barrier-deadline-ms': Key('count', 5000, 'write shedding', 1),
    'barrier-stall-ms': Key('count', 30000, 'barrier stall', 1),
    'clock-event-ms': Key('count', 1000, 'committer clock cadence', 1),
    'compress-min-octets': Key('count', 0, 'compression threshold (zero off)'),
    'disk-reserve-octets': Key('count', 67108864, 'disk full write shedding', 1),
    'relay-date-skew': Key('count', 86400, 'future dated relay refusal', 0, 86400),
    'refused-offer-capacity': Key('count', 4096, 'per-peer remembered refusals'),
    'relay-require-path': Key('count', 0, 'missing relay Path refusal', 0, 1),
    'path-identity': Key('identity', 'unset', 'Path and Injection-Info identity'),
    'posting-policy': Key('enum', 'open', 'bound login signature gate', choices=('open', 'bound-logins')),
    'complaints-to': Key('mailbox', 'unset', 'Injection-Info complaints address'),
    **{k: Key('store', v, 'requested/funded Store admission', 1) for k, v in STORE_DEFAULTS.items()},
}


def ranges(value):
    if value == 'none':
        return []
    result = []
    for word in value.split(','):
        address, slash, bits = word.partition('/')
        address = '127.0.0.1' if address == 'localhost' else address
        ip = ipaddress.ip_address(address)
        # Listener grammar, not DNS or IPv4-mapped IPv6 (NNT-041).
        if ip.is_unspecified or (ip.version == 6 and ip.ipv4_mapped):
            raise ValueError('wildcard/mapped source')
        result.append(ipaddress.ip_network(str(ip) + ('/' + bits if slash else ''), strict=False))
    return result


def parse_value(key, value):
    """Return (typed value, refusal word); no state change on refusal."""
    if key not in KEYS:
        return None, 'unknown-policy-key'
    spec = KEYS[key]
    if not isinstance(value, str) or not value or not value.isascii():
        return None, 'policy'
    if spec.kind in ('count', 'store'):
        if not re.fullmatch(r'0|[1-9][0-9]*', value):
            return None, 'policy-value-not-a-number'
        number = int(value)
        if number > spec.maximum and spec.kind == 'store':
            return None, 'above-representation-ceiling'
        if not spec.minimum <= number <= spec.maximum:
            return None, 'profile-invalid' if spec.kind == 'store' else 'policy'
        return number, None
    if spec.kind == 'enum':
        good = value in spec.choices
    elif spec.kind == 'identity':
        good = bool(re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9.-]*', value))
    elif spec.kind == 'mailbox':
        atom = r"[A-Za-z0-9!#$%&'*+/=?^_`{|}~-]+"
        dot = atom + r'(?:\.' + atom + r')*'
        good = bool(re.fullmatch(dot + '@' + dot, value))
    elif spec.kind == 'ranges':
        try:
            ranges(value)
            good = True
        except ValueError:
            good = False
    else:
        if value == 'none':
            return value, None
        entries = value.split(',')
        if len(entries) > 64:
            return None, 'overrides-full'
        try:
            for entry in entries:
                addr, rate = entry.split('=')
                ip = ipaddress.ip_address(addr.split('/')[0])
                if '/' in addr and (ip.version != 6 or addr.split('/')[1] != '64'):
                    raise ValueError('override mask')
                if not re.fullmatch(r'[1-9][0-9]*', rate) or int(rate) > U32:
                    raise ValueError('override rate')
        except ValueError:
            return None, 'override-address'
        good = True
    return (value, None) if good else (None, 'policy')


# Named predicates are shared by the table, never a key-only exemption.
VALUE_CLASSES = {
    'non-number': lambda key, value: (
        parse_value(key, value)[1] == 'policy-value-not-a-number'
        and re.fullmatch(r'-[0-9]+', value) is None),
    'negative': lambda key, value: re.fullmatch(r'-[0-9]+', value) is not None,
    'malformed-text': lambda key, value: (
        KEYS[key].kind not in ('count', 'store')
        and parse_value(key, value)[1] in ('policy', 'override-address')),
    'above-maximum': lambda key, value: (
        re.fullmatch(r'0|[1-9][0-9]*', value) is not None
        and KEYS[key].maximum < int(value) <= U32),
}


def permitted_adjudications(target):
    return (row for row in ADJUDICATIONS if target == 'fn1'
            or target == 'fn2' and row['class'] == 'spec-ambiguity')


def recorded_greeting(expected, status, *, eof, target='fake', request=None):
    """Exact G0 bytes + EOF, only where the spec expects the auth refusal.

    The checked spec reply has the same 400/close effects. It is used only for
    the commit; the trace and evidence retain the original observed bytes.
    """
    if request is not None or expected.check(status, None, eof=eof).ok:
        return None
    for row in permitted_adjudications(target):
        if (row.get('command') == 'greeting' and status == row['fn1_status']
                and eof is row['eof'] and expected.rule == 'capacity'
                and expected.close_after_reply
                and expected.check(row['spec_status'], None, eof=eof).ok):
            return dict(deepcopy(row), target=target,
                        observed_reply=dict(status=status, eof=eof))
    return None


class LimitsModel:
    def __init__(self, *, public=False, store_defaults=None):
        self.public = public
        self.rows = {}
        self.store_defaults = dict(STORE_DEFAULTS if store_defaults is None else store_defaults)
        self.funded = dict(self.store_defaults)

    def get(self, key):
        if key in self.rows:
            return self.rows[key]
        spec = KEYS[key]
        if spec.kind == 'store':
            return self.store_defaults[key]
        default = spec.public if self.public and spec.public is not None else spec.default
        return self.get('exposure-connections') if default == 'total' else default

    def set(self, key, value):
        return SetExpectation(self, key, value)

    def trusted(self, address):
        ip = ipaddress.ip_address(address)
        return any(ip in net for net in ranges(self.get('exposure-trusted')))


class SetExpectation:
    def __init__(self, model, key, value):
        self.model, self.key, self.value = model, key, value
        self.parsed, self.reason = parse_value(key, value)

    def check(self, result):
        if self.reason:
            if result['exit'] != 1 or self.reason not in re.findall(r'[a-z][a-z0-9-]*', result['text'].lower()):
                return 'policy-set: expected named refusal ' + self.reason
        elif result['exit'] != 0:
            return 'policy-set: expected accepted'
        return None

    def recorded_difference(self, result, target='fake'):
        if not self.reason or self.check(result) is None:
            return None
        # Match the parenthesized reason exactly, not a word in explanatory
        # prose (in particular, "policy" also occurs in the command prefix).
        reasons = re.findall(r'\(ADMINISTRATION ([A-Z][A-Z0-9-]*)\)', result['text'])
        for row in permitted_adjudications(target):
            if (self.key in row.get('keys', ()) and result['exit'] == row['exit']
                    and reasons == [row['reason']]
                    and any(VALUE_CLASSES[name](self.key, self.value)
                            for name in row['value_classes'])):
                return dict(deepcopy(row), key=self.key, value=self.value,
                            target=target, observed_reply=dict(result))
        return None

    def update(self, result, target='fake'):
        recorded = self.recorded_difference(result, target)
        error = self.check(result)
        if error and recorded is None:
            raise AssertionError(error)
        if result['exit'] == 0:
            self.model.rows[self.key] = self.parsed
            if KEYS[self.key].kind == 'store':
                # The fixture generates same-value Store sets, plus invalid
                # values. Other funded decisions need measured resource inputs.
                if 'applied' in result['text'].lower():
                    self.model.funded[self.key] = self.parsed
        return recorded
