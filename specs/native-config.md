# Native operator configuration

Status: executable native profile. This is an operator-startup profile, separate
from the durable group and peer configuration records replayed by the node.

`fn-native-config-load` is the semantic subject. Its input is one raw vector
of at most 16,384 octets. It returns either `(:accepted configuration)` or
`(:refused reason)`. The raw native host reads bounded bytes and invokes that
function; it does not parse TOML, supply a default, validate a field, or
compute a configuration path.
`fn-native-operator-run` maps a refused configuration load to `:usage` and
CLI exit 5 before a Store request or listener bind; this is distinct from a
request refusal (exit 1).

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
`fn-auth-configp` record in its served session. Credential replacement while the
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


### Explicit cold resources (P12 staged grammar)

`[resources]` accepts `cold_heap_octets`, `cold_workers`,
`cold_descriptors`, `cold_read_ids` and `cold_file_ids` together. All five are positive
naturals representable in u64; a partial table, zero or overflow is
refused. Absence remains absent in the normalized record, and `show`
preserves the exact supplied values through the loader round trip.
Resolving relative configuration paths preserves this explicit policy and
the listener's selected TLS port. It changes only path fields; it cannot
erase the resource policy and thereby bypass its operator refusal.
These fields describe an operational cold-resource policy, separate from
the durable Store profile. At this source frontier `run` refuses an explicit
policy as `cold_resources`: the supported allocator baseline and launcher
consumer have not yet landed. Parsing/showing it is not a funding verdict.
The pending consumer must reserve peak persistent table capacity, worker
stack/runtime, protected read buffers and retained cached buffers, and
charge each registered incarnation until physical close. Native pressure,
actual pread stall, completion/cache/close observations are SCN-1002.
Checkpoint/recovery rescue and compressed decoder highwater need additional
grounded funding; this grammar does not establish them.

The file-incarnation namespace is distinct from the read namespace. The
operator limits each independently, with no wrapped identity reuse; the
local file allocator refuses before opening beyond `cold_file_ids`.

### Retire operator observation (PKT-895)

`retire [--drain SECONDS]` asks the live owner to retire and observes its
socket/store-lock state. ACL2's `fn-nret-observation-step` bounds this
observation to the accepted drain window plus a 60-second operator allowance,
starting before the request, using monotonic host ticks and their positive
rate. The poll interval is one second. This is local operator policy, independent
of the live owner's current barrier policy; it does not bound physical fence
completion or prove that the process stops within that time.

At or past the boundary, a live or held owner produces uncertainty (exit 3).
The operator leaves the owner, retained resources and custody obligations
untouched and prints `retire uncertain reason=observation-deadline`.
An offline or stale observation permits report inspection, including at the
exact boundary. Success still requires a fresh regular report; an unchanged
prior report or no report produces uncertainty. Invalid clock/request inputs
and unknown observations produce a fault with `reason=invalid-observation`;
they cannot produce a stopped/report decision or a deadline-expiry claim.

### Operator diagnostic outcomes

The heap launcher's operator profile observation may fall back to an absent
profile only for a condition ACL2's closed failure classifier names as a
refusal. A failed core call, corrupt durable profile, uncertain outcome or
unlisted condition propagates before any accepting `heap=` line is printed.
This applies to the nested store-profile reader as well as the operator plan,
initializer profile resolution and resource-policy projections. A genuinely
absent store still has no profile; the command subsequently reports its own
refusal under the no-store reservation.

The initial-group encoder's named `:bad` result is a refusal. A malformed
result, or disagreement between the host and core's frame header/trailer
widths, is a fault. These checks preserve HST-008/HST-009's shared outcome
classes; they do not manufacture a policy refusal from an image defect.

## Resumable developer init (STO-10005)

`store ROOT init` may resume interrupted initialization. Under its exclusive
writer lock, it supplies the requested decoded profile, the immutable sealed
profile and exact generation-one record bytes to ACL2's
`fn-nir-resume-decision`. The recorded initial change list must match the
requested initial groups. A new clock stamp and later configuration/limit
changes do not change that initial intent. Profile or group mismatch is a
named refusal before resume directory creation, staged publication, genesis
work or node-secret creation. Initial root/lock acquisition precedes this
check. Corrupt generation-one evidence faults; missing generation one when
configuration history exists faults. Absence with no history is the legal
interrupted-before-publication case.

The keystones prove compatibility across independent clock stamps and named
refusal of distinct initial changes under exact decode premises; literal
real-codec witnesses include each premise removal.
The actual host fixture discriminates prior init's silent success on profile
mismatch. This does not add a streaming history loader or prove physical init
syscall order: the existing bounded history observation and init publication
program retain their separate contracts. Operator init's staged-publication
verb retains its existing path refusal.
### Explicit output resources in the canonical rendering

The optional pair `resources.output_heap_octets` and
`resources.output_quantum_heap_octets` is rendered in the same resources table
as cold resources. Both values survive whole-config and individual-key
`operator show`; loading the rendering preserves the complete normalized
record, including absence of either resource policy. The renderable invariant
carries the loader's output-policy predicate: two positive u64 naturals, with
total heap at least twice the quantum heap. Parsing and rendering this pair
does not enable its pending operational consumer or change the operator's
`output_resources` refusal. Existing round-trip and accepted-load keystones
cover these fields; output-only and combined cold/output fixtures discriminate
the representation boundary.

Relative-path normalization also preserves both resource policies before
rendering the resolved configuration for `fn-native-operator-run-at`. It
cannot turn an explicit unsupported output policy into an absent default;
the actual operator still receives the policy and refuses it by name.

## Current operation observation

`fn operator CONFIG operation` selects the existing authenticated local status
transport, report kind 14. ACL2 reads the canonical pending admission and writer
state under the owner gate, renders fixed scalar fields within the status-page
octet budget, and retains the normal immutable report buffer for paging. It
never serializes the borrowed operation/source graph, walks the Store, issues
an allocation token or changes custody. Oversized scalar rendering produces an
explicit unavailable/budget report rather than partial fields. An offline query
reports owner-not-running without opening or replaying the Store. Held charges
are the pending operation's five-dimensional resource vector, not total live
heap or proof of complete physical accounting. SCN-1120 exercises the literal
source route; PRF-1292 retains the pending guard/size-proof obligations.


## Trusted development attachment

`FN_NATIVE_DEV_REPL` is a developer-only selector naming an absolute Unix socket
path. Production selector validation refuses it before owner startup. The
opted-in owner installs one local evaluator worker with same-UID authentication,
0600 socket mode, one request at a time, bounded UTF-8 input and captured output,
and inode/device-checked cleanup. It never removes a pre-existing path.
Developer forms are explicitly trusted code, separate from all Store, NNTP, BP
and operator wire grammars. They run through the owner serialization/fence
boundary; this facility does not promise semantic invariants after arbitrary
code edits or forceful cancellation of evaluation. `SCN-1121` exercises the
actual socket evaluator and production selector, with named owner/I/O adapters;
full native owner composition and ordinary ACL2 event admission remain separate
execution checks. There is no new proof or image qualification claim.
