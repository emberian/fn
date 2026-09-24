# Receiver-local authorship at protected transit ingress

The e160 A→B preflight found a precise composition failure: B received A's
exact signed carrier and `hybrid-verify-source` passed, but B stored the
article as legacy `fn-r`; its consumer poll could not be projected as a
historical kind-4 verdict, and `HDR :fn-verified` remained absent. The
original bytes, cursor, report and refusal are retained in the e160 gate's
`build/freeze/e1e2-preflight-artifacts/`. This packet changes the *new*
receiver acceptance path, not that historical observation.

`fnn-owner-drain-one` for wanted protected NNTP transit and
`fnn-owner-complete-bp-transit-submission` for pinned BP transit both call
`fnn-owner-attempt-transit` under their existing durable intent and resolution
sequence. Its `fn-owner-peer-carrier-form` call distinguishes absent from
malformed-present `FN-Authorship`. The former keeps legacy acceptance; the
latter refuses. For a new syntactically valid carrier,
`fn-owner-peer-carrier-plan` selects the receiver's current per-principal
enrollment from its carried Store snapshots, requiring byte-exact principal
and ordered keys. Native Ed25519 and ML-DSA-65 primitives observe the exact
ACL2 preimage against those selected keys. `fn-owner-peer-carried-event`
reselects the current snapshot in the serialized owner and asks
`fn-pa-authorized-event` to construct the existing schema-1 kind-4 event.
`fnn-owner-identity-commit` performs the ordinary Store publication. The
configured peer supplies transport provenance; it is not author authority.

The duplicate check precedes current enrollment so an exact already-stored
article can return the Store's historical `:duplicate` result after rotation
or revocation without rewriting it. That check compares Message-ID, payload
and groups; it does **not** distinguish an earlier kind-4 event from an
earlier legacy `fn-r`. Consequently, a byte-identical old legacy article
remains legacy with no historical verdict. The raw called-path test checks
that the duplicate performs neither primitive verification nor kind-4
publication. This is no upgrade or backfill path; a *new* carrier under a
revoked or mismatched local enrollment refuses. An already stored kind-4
verdict retains its historical snapshot and bytes.

The ACL2 book and test passed on persvati w25, ACL2 8.7, jobs 2, 120-second
per-book bound without closure, in
[`certify-20260924T063723Z-1296100.json`](manifests/certify-20260924T063723Z-1296100.json).
This exact-source run certified its requested book and test; its remote
certificate-cache publication failed because the invocation accidentally
named hbox's `/tank/fn/certcache` on persvati. The manifest itself reports
`passed`, and no cache publication is claimed. An earlier correct-cache
scoped run passed the same definitions before the comment-only duplicate
clarification. These proofs establish bounded parser separation and current
plan selection, not primitive security or full Store/owner invariance.

`tests/native_peer_authored_accept_raw.lisp` and the updated BP raw transit
regression passed under local SBCL; they check both real caller branches,
intent/resolution ordering, malformed and absent carrier behavior, current
enrollment refusal, dual observation gating and kind-4 publication handoff.
The combined raw log is `build/peer-authored-host-tests.log`, SHA-256
`07feac800ff5c1811c063cc214086a0d9506c315709912e249dcea847f60ef4d`.
The raw host test stubs ACL2 values and does not stand in for a saved image.

On hbox, OpenSSL 3.5.8 plus SBCL ran
`tests/native_peer_raw_key_component.lisp` from the source-matched staged
`host/native/signatures.lisp` (SHA-256
`a8a1b940b5b074090b336d733be05027fb187915c177d4a8b1c25b4c74a5e98f`).
PEM-signature verification agreed with raw enrolled-key import/verification;
substituting another raw key and changing one signature byte each refused.
The log is `/tank/fn/gates/peer-authored-component-20260924/raw-key-component.log`,
SHA-256 `367fa734c4c9ce194e66af20b5edb4aa0502d5fe5b369baaeeebf9664467d5fc`.
The second public key was generated only in that scratch gate. The existing
broad signature script reached the new raw assertions but then failed its
unrelated standalone TLS-reset fixture check; this narrower component test
is the claimed primitive observation.

Still open: a source-matched saved image must demonstrate A→B protected
transit, B-local enrollment, kind-4 poll and `consumer-project`, persisted
`HDR :fn-verified` across restart/rotation, plus the BP transit composition.
The full affected ACL2 owner/Store closure and physical crash correspondence
are separate from these scoped results. No live node was modified.
