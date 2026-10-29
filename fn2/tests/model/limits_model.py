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

Contract gaps are explicit, not fn1 adjudications: the cited specs do not
specify generic invalid-range reason words, every text grammar, or all count
lower bounds. Generic range/text refusal `policy`, positive batch / TLS counts
and zero-off compression are provisional profile choices. They must NOT be
called observed fn1 behavior. No implementation module is imported.
All mismatches fail; ADJUDICATIONS starts empty pending recorded seat replies.
Store defaults are explicit fixture inputs. Accepted sets require exit 0 and
accept any line; no literal success text is specified. Refusals require exit 1
and the reason word, without assuming an otherwise unspecified line format.
"""
from dataclasses import dataclass
import ipaddress
import re

U32 = (1 << 32) - 1
ADJUDICATIONS = ()
STORE_DEFAULTS = {'max-transactions': 4096, 'max-history-octets': 16777216,
                  'max-article-octets': 32768}  # explicit init fixture, not universal defaults
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

    def update(self, result):
        error = self.check(result)
        if error:
            raise AssertionError(error)
        if not self.reason:
            self.model.rows[self.key] = self.parsed
            if KEYS[self.key].kind == 'store':
                # The fixture generates same-value Store sets, plus invalid
                # values. Other funded decisions need measured resource inputs.
                if 'applied' in result['text'].lower():
                    self.model.funded[self.key] = self.parsed
