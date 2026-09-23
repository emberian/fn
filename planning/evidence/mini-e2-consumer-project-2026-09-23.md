# Bounded E2 poll projection for Mini

`books/consumer-poll-projection.lisp` defines `fn-cpj-project`, the exact
function called by the read-only native `consumer-project CURSOR.fncu
ACCEPTED.fn-e` verb in `host/native/signature-command.lisp`. It caps inputs
at 346 and 196608 octets before decoding. ACL2 requires an exact v1 cursor,
schema-1 `fn-e` parent, bound canonical child `fn-r` and verdict, matching
cursor position and parent sequence, authored source identity and record
metadata, and a recorded `:verified` verdict. The one-line
`fn-consumer-project-v1` output carries the exact cursor scope, Store
sequence/txid, source ID, Message-ID, authored source, received article,
verdict principal and exact verdict event. The host formats only these
ACL2-selected values; it does not re-derive their identities or verdict.

This command works on supplied files, so its success establishes only the
structural relation of those files. Historical admission at a particular
fn Store requires the separate authenticated local `consumer poll` route to
have returned these exact bytes. Portable cryptographic authorship still
requires `hybrid-verify-source` under independently pinned full public keys.
Mini operation authority and its immutable reply are decided by Mini after
both joins. Poll does not acknowledge processing; `consumer ack` remains a
later explicit durable declaration.

The projection book and its witness book certified on hbox with ACL2
toolchain identity `d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`
in incremental run `run-20260923T225942Z-cb54`, manifest
`planning/evidence/manifests/certify-20260923T225949Z-405350.json` (59 installed
content-matched dependencies, two certified roots). The witness uses a
constructed signed-carrier composite and refuses a wrong cursor position,
legacy parent, malformed parent, wrong authored identity and oversized
cursor. `make check` passed at these bytes. `fn-cpj-project` was admitted as
an executable definition in that earlier source-matched run; its guard was
then a separate obligation. Current integrated `fn-cp-cursor-decode` has a verified guard.
No native image containing this verb has yet been built or run.

On the integrated cursor codec, `fn-cpj-project` now uses the verified
`fn-cbor-at-mostp` preflight with ACL2-owned bound getters and has a verified
guard. Local shape lemmas carry a successful decoded cursor as a list and a
bound parent event's sequence as a number; no codec is opened book-wide.
The [current-source book and witness](manifests/certify-20260923T231356Z-1459023.json)
both passed with the qualified w25 ACL2 toolchain, identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`.
Bounded dotted inputs still refuse with `:limit`, as the witness checks.
