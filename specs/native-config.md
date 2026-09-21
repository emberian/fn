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
| `listener` | `host`, `port`, `tls_cert`, `tls_key` | Host defaults to `127.0.0.1` and must be `127.0.0.1`, `::1`, or `localhost`; port defaults to 1119 and is 1..65535; TLS paths are paired or absent. |
| `auth` | `required`, `protected_only`, `path` | Booleans default false; path defaults to `<store>/auth.toml`. |
| `posting` | `enabled`, `agent` | Defaults true and `fn-operator@localhost`. |
| `anchor` | `server` | Optional bounded server name. |
| `acl2` | `path`, `slots` | Parsed so a migration cannot silently discard it; a direct saved image cannot consume either. |
| `log` | `path` | Optional bounded path. |
| `control` | `path` | Optional bounded path, default `<store>/control.sock`. |

Every path is bounded to 512 octets, ordinary text to 256, and an anchor name
to 128. `fn-native-config-operator-availablep` is a separate ACL2 decision
that refuses use of settings whose native consumer does not exist yet. The
native owner now consumes `auth.required` and the selected `auth.path` through
`books/native-auth-profile.lisp`. It also consumes the paired TLS paths and
admits `auth.protected_only` when a certificate path is present. Non-default
posting agent, anchor, log, and `[acl2]` remain unavailable rather than being
silently ignored. Both Boolean posting policies and the bounded control path
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
