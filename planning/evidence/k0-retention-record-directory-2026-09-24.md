# K0 retention record-directory cut (2026-09-24)

The ACL2-authored retention Store event now uses the shared exact Store
decoder.  `fn-srci-store-retention-event-round-trip` proves its canonical
payload round trip, and `fn-bsrp-retention-host-arguments-are-typed-record-input`
proves that the actual protected-prefix/trailer frame and transaction name
form a typed P-RECORD input.  Together with
`fn-bs-k0-record-attempted-cut-establishes-relation`, this reaches the actual
pair-10 `:record-attempted` cut from a related staged input and fresh stage.

`fn-bsrp-record-dir-eio-run-has-actual-failed-cut` identifies the stopped
`fn-bs-run` pair 11 after P-RECORD's `:fsync-dir :transactions`.  The physical
choice is explicit.  `fn-bsrp-record-directory-eio-applied-cut-fences-related-attempt`
uses the K8 transaction-fence relation theorem: `:apply` appends the candidate
to the durable record prefix, preserves the relation to the attempted kernel
state, drains transaction-directory pending operations and makes the
`:record-dir :error` callback fenced.  Its test book has a reachable second
retention publication and an exact-conclusion counterexample for each of the
related-input, typed-frame and fresh-staging premises.  The `:drop` theorem
proves the same interpreter stop and fence with the old durable prefix and
final entry unchanged.  Its relation and typed-frame premises have no
independent teeth for that physical old-prefix conclusion; this theorem is a
conditional composition result, not a separate minimal-premise keystone.

This is the model boundary corresponding to `fnn-publish` in
`host/native/io.lisp:1548-1596`: after link and `:record-attempted`, the host
fsyncs the transaction directory, reports `:record-directory :error` on EIO,
and returns indeterminate while fenced.  `fnn-owner-publish-prepared` in
`host/native/owner.lisp:656-682` calls that publisher.  The separate certified
owner preparation theorem `fn-orpr-host-retention-prepare-branches` (commit
`86bc8d41`, selected hbox manifest `certify-20260924T062249Z-1003562`)
constructs the event and distinguishes refusal from staged preparation at the
exact configured-owner caller.  A theorem joining that owner call to every
physical byte cut is still open.

The selected persvati runs used ACL2 8.7 through
`/home/ember/fn-gates/toolchains/w25/acl2-literal`, toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`,
one ACL2 job, and source digests in their archived manifests:

| Run / manifest | Result |
| --- | --- |
| `run-20260924T055941Z-00c2` / `certify-20260924T055944Z-938612` | Store event decoder, retention codec invariants and test passed (1.974, 3.784, 1.969 seconds). |
| `run-20260924T060116Z-ab6f` / `certify-20260924T060121Z-954398` | One-time current-source parent bootstrap: 29 certificates passed, including the changed record provenance export. |
| `run-20260924T062256Z-65db` / `certify-20260924T062303Z-1163452` | New K0 book, K8 stable-prefix/fence parents and provenance test passed; new test failed because it incorrectly expected the live view to hide a pending link. |
| `run-20260924T062544Z-ab75` / `certify-20260924T062549Z-1188755` | Corrected test passed after checking the durable entry rather than the live lookup. |
| `run-20260924T063006Z-99c7` / `certify-20260924T063012Z-1231429` | Final test with three independent exact applied-conclusion premise teeth passed (3.937 seconds). |

These are source-matched ACL2 certificates and executable logical witnesses.
They do not prove filesystem EIO scheduling, power-loss behavior, actual
native syscall equivalence, a byte relation at every served call entry, all
P-RECORD cuts, the whole owner publication sequence, or topic/identity
recovery for every physical image.  Native fault campaigns are separate
evidence and must name their observed cut and error classification.
