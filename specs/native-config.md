# Native operator configuration

Status: executable W14 profile. This is an operator-startup profile, separate
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
that refuses use of settings whose native consumer does not exist yet. It
currently admits only the store/listener core defaults: TLS, auth, non-default
posting policy, anchor, log, and `[acl2]` are not silently ignored. It does
not claim that a saved image has already wired a configured owner; build
integration and that consumer remain separate work.

The owner convergence consumer uses ACL2 projections for store root, listener
host/port, control path, max connections (32), clock-error bound (1000 ms),
TLS paths, and authentication policy. The last two numeric values are ACL2
profile defaults, not values computed by the raw host. `host/native-config-host.lisp`
exposes `fn-native-config-host-load` and the ACL2-owned byte bound for the
native wrapper; `host/native/config.lisp` registers the diagnostic protocol
`config check PROFILE-PATH` when included by the saved-image build.
