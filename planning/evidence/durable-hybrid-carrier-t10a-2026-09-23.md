# Durable selected FN-Authorship carrier, T10a

The selected kind-4 accepted-event codec now has two exact schemas. Existing
schema 0 remains eleven ordered items and retains its original constructor and
encoder bound. Schema 1 is thirteen items: the original parent/record/verdict
fields, exact authored-source octets, and their ACL2-derived subject identity.
The embedded `fn-r` article carries the received `FN-Authorship` projection;
its content identity and charge are over those received bytes. The owner's
observed acceptance stamp remains in that embedded record.

The host-called `fnn-hybrid-control-author` invokes ACL2 carrier rendering,
obtains independent libsodium Ed25519 and OpenSSL ML-DSA-65 observations,
then calls `fn-hsig-authorized-carried-submission-event`. That ACL2 function
requires both observations, the enrolled ordered public-key snapshot, exact
source, received projection, metadata identities and charge before it emits
the one atomic event. `fn-replay-identity-step` calls
`fn-hsig-article-event-snapshot-bindsp` for the decoded event during both
publication and recovery. Schema 1 binds the carrier projection, exact source
identity, record metadata, enrolled principal/key set, both signature
components' shape and the recorded principal. Recovery preserves the
historical verdict; it does not re-run current-key authorization or the native
primitives. The native libraries, key custody, and historical observation
honesty remain explicit trust boundaries.

The first source cut, commit `0a5961c0`, qualified on hbox via
`python3 tools/farm.py submit hbox --affected-by books/stx-accept-records.lisp
--affected-by books/hybrid-store.lisp --jobs 2 --remote-root
/tank/fn/lanes/authorship-durable-t10a`. Its
[manifest](manifests/certify-20260923T183613Z-4087526.json) records ACL2
8.7/SBCL 2.6.8, toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
171 selected roots, 284 closure books, 107 installed from one matching cache
origin, 177 newly certified and zero failures in 266.995 seconds. The codec
digest was `1ab94189123dbcc7d62ce544c5ede25367fdd9bb95c936e30d4b8568cc326485`;
the hybrid-store digest was
`923d41aab732691295e2b7e8d134dec35d0a1f82c4b44d3ddc238088594ddc09`.
This manifest predates the later record-metadata binder tightening and direct
Store commit/reopen witness; it is not a final qualification for those bytes.

The selected ACL2 tests exercise both schema decodes, a version-0 migration
round trip, exact-source and keyset substitution refusals, wrong source
identity, and wrong embedded record charge beneath otherwise structurally
bound parents. The direct Store trace drives enrollment, schema-1
prepare/finish and reopen, then checks the received article and historical
principal verdict. The helper's guard is verified with explicit octet and
length checks before deriving the obligation identity; its local hint keeps
the article parser and identity definitions closed. This is a boundary check
of caller metadata, not a cryptographic proof.

The final hbox affected closure is
[certify-20260923T190606Z-4132534.json](manifests/certify-20260923T190606Z-4132534.json),
invoked with `python3 tools/farm.py submit hbox --jobs 2
--affected-by books/hybrid-store.lisp --remote-root
/tank/fn/lanes/authorship-durable-green-t10a`. It records ACL2 8.7/SBCL
2.6.8, the toolchain identity above, 164 selected roots and 280 closure
books at exact source digests, zero failures, with all 280 books installed
from five matching cache origins. The provenance includes the fresh
[source-book run](manifests/certify-20260923T185910Z-4120035.json),
which certified 165 books but exposed four test-root failures, and the
[repaired-test run](manifests/certify-20260923T190501Z-4129980.json),
which certified those four roots. Both fixture failures came from using
`defconst` to call the constrained digest; `make-event` now computes those
fixed witness values. The final manifest is a cache-qualified closure, not
a second fresh proof run. Its hybrid-store source digest is
`0b5a962b12d6214b99ffbf227551ae946c604311d3464f90772e3ecd0d28bc89`.
`make check` passes after regenerating the ledger from these sources.

The native saved-image witness still awaits the root's combined image. The
reader's pinned `HDR :fn-verified` path is a separate T10b packet. Neither
ACL2 tests nor this manifest establish signature unforgeability, filesystem
power-loss behavior, or key succession policy. Replay binds the recorded
v1 verdict and does not re-evaluate current signature capability.

Root integrated this packet with current BP A2 and contact sources. The dependency-shifted roots passed in hbox `run-20260923T191026Z-9415`; all changed and dependent roots then had exact-source green evidence. The original direct guard-fix certificate for `hybrid-store` is archived as [certify-20260923T185829Z-4119104.json](manifests/certify-20260923T185829Z-4119104.json), independently of later cache reinstall manifests. Static `make check` passed. Saved-image acceptance/reopen and the joined HDR reader remain pending.
