# Native operator configuration

Status: executable native profile. This is an operator-startup profile, separate
from the durable group and peer configuration records replayed by the node.

`fn-native-config-load` is the semantic subject. Its input is one raw vector
of at most 16,384 octets. It returns either `(:accepted configuration)` or
`(:refused reason)`. The raw native host reads bounded bytes and invokes that
function; it does not parse TOML, supply a default, validate a field, or
compute a configuration path.

The profile is intentionally smaller than TOML. It accepts ASCII source only,
blank lines and full-line `#` comments, the eight documented table headers,
simple ASCII identifier keys, `true`/`false`, up-to-five-digit decimal
integers, and quoted printable-ASCII strings without escapes, backslashes, or
inline comments. Duplicate tables and keys, unknown tables and keys, malformed
values, non-ASCII/invalid UTF-8 octets, more than 128 lines, and every other
TOML feature are refused. This is an explicit fn profile refusal, not a claim
to accept general TOML.

The complete documented surface is parsed and retained in the normalized
configuration:

| Table | Keys | Validation/default |
| --- | --- | --- |
| `store` | `path` | Required nonempty path, at most 512 octets. |
| `listener` | `host`, `port`, `tls_cert`, `tls_key` | Host defaults to `127.0.0.1` and is a numeric IPv4 address other than `0.0.0.0`, or one of the aliases `localhost` (the IPv4 loopback) and `::1` (`fn-native-config-listener-hostp`); names are never resolved and the wildcard is refused, so a node binds exactly the address it was given. Port defaults to 1119 and is 1..65535; TLS paths are paired or absent. |
| `auth` | `required`, `protected_only`, `path` | Booleans default false; path defaults to `<store>/auth.toml`. |
| `posting` | `enabled`, `agent` | `enabled` defaults true. `agent` is parsed and retained, has no default, and is refused by `run` (below). |
| `anchor` | `server` | Optional bounded server name. |
| `acl2` | `path`, `slots` | Parsed so a migration cannot silently discard it; a direct saved image cannot consume either. |
| `log` | `path` | Optional bounded path; `run` admits it only when absolute. |
| `control` | `path` | Optional bounded path, default `<store>/control.sock`. |

Every path is bounded to 512 octets, ordinary text to 256, and an anchor name
to 128. `fn-native-config-operator-availablep` is a separate ACL2 decision
that refuses use of settings whose native consumer does not exist; it is
`fn-native-config-unsupported-key` returning nil, and `run` refuses a
profile with `usage operator run (UNSUPPORTED-PROFILE KEY)`, KEY the first of
`protected_only`, `enabled`, `agent`, `anchor`, `log`, `acl2` the owner cannot
consume. The native owner consumes `auth.required` and the selected
`auth.path` through `books/native-auth-profile.lisp`. It also consumes the
paired TLS paths and admits `auth.protected_only` when a certificate path is
present. It consumes an absolute `[log] path`: `run` opens it append-only
(`O_APPEND|O_CREAT|O_NOFOLLOW`, mode 0640) before the store, and the owner
writes there, instead of to stderr, one line per served post, control post
and accepted connection, each rendered by `books/owner-log.lisp` with the
reply's outcome word first; fn never truncates or rotates the file. A
relative path is refused (`log`), since the service's working directory is
not part of the profile.

`[posting] agent` is refused (`agent`) whatever it says, the former default
`fn-operator@localhost` included, and that is a decision, not a missing
consumer. The injecting agent a served POST writes into Path and
Injection-Info (RFC 5537 section 3.2.1, RFC 5536 section 3.2.8) is the
node's `<path-identity>`, and fn keeps it in one slot: the replayed
configuration policy `path-identity` (`fn operator CONFIG policy set
path-identity IDENTITY`), which peer loop suppression reads too. The owner
installs it through `fn-oag-post-config` (books/owner-agent.lisp), and
`fn-oag-served-post-names-the-pinned-agent` with
`fn-oag-configured-open-pins-the-path-identity` carry it to every injected
article's Injection-Info, the read under the served-connection invariant the
owner does not yet carry (`fn-served-connp` of the connection's served state;
the premise PRF-006 records for `fn-ocfg-read-tls-prefix`). A value in fn.toml could only disagree with Path.
An agent with `@` is not a `<path-identity>` at all.

The anchor server and `[acl2]` remain unavailable rather than being silently
ignored. Both Boolean posting policies and the bounded control path
are consumed by the local control service. Path presence does not make a socket protected: the native
operator must first load and key-check an OpenSSL 3 context, and each owner
connection becomes protected only after its own successful handshake and the
model's `:tls-established` transition. Missing, malformed and mismatched
certificate/key material fails before the listener opens.

The credential registry is a second bounded ACL2 profile. It accepts at most
65,536 ASCII octets, 1,024 lines and 128 canonical `[login."NAME"]` tables.
Each table has exactly one 32-octet lowercase-hex principal, 16-octet
lowercase-hex salt, 32-octet lowercase-hex digest and Boolean posting field.
Duplicate names or fields, unknown syntax, wrong widths, and the legacy
cleartext `secret` field are refused. The parser reuses the native profile's
line, whitespace, quoted-value and Boolean primitives; ACL2 alone decodes hex,
builds `fn-authsec-verifier` and assigns the posting bit. A missing file is an
observed empty registry, matching the existing operator behavior.

Credentials and policy are loaded once after Store/feed recovery and before
the listener opens. Each accepted connection then pins the resulting existing
`fn-auth-config` in its served session. Credential replacement while the
process is running is not a reload operation in this version; a restart is
required, and no live-generation claim follows from atomic file replacement.
The TLS context is likewise loaded once and shared across connection-specific
OpenSSL sessions; a failed peer handshake does not reload it or stop the
listener.

The owner convergence consumer uses ACL2 projections for store root, listener
host/port, control path, posting enablement, max connections (32), and
clock-error bound (1000 ms). The last two numeric values are ACL2 profile
defaults, not values computed by the raw host. `host/native-config-host.lisp`
exposes `fn-native-config-host-load` and the ACL2-owned byte bound for the
native wrapper; `host/native/config.lisp` registers the diagnostic protocol
`config check PROFILE-PATH` when included by the saved-image build.
