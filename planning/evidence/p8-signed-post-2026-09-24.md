# P8: a signed POST over NNTP gets the transit classification

The p8-verdict lane found that a served POST carrying an `FN-Authorship`
carrier was stored through the unsigned arm (`fnn-owner-attempt`) and got no
durable verdict, while protected transit and the control socket's
`hybrid-author` did. This lane routes the served POST through the same ACL2
decision transit uses.

## The classification as implemented

`host/native/owner.lisp` `fnn-owner-attempt-served` (line 884) is called by
the served NNTP POST arm of `fnn-owner-drain-one` (line 1173) and by
`fnn-owner-complete-bound-submission` (line 1247; local control `post` and BP
application submissions). It calls `fnn-owner-attempt-transit`, the attempt
protected NNTP and BP transit call, and asks ACL2 for the poster's word:

- `fn-pa-carrier-form` over the staged (injected) octets: `:absent` is
  `fnn-owner-attempt`, the unsigned arm, with its word unchanged
  (`fn-pa-served-word word nil = word`).
- `fn-pa-current-plan` over those octets and this Store's keyring snapshots
  (`host/owner-host.lisp` `fn-owner-peer-carrier-plan`, line 1177). Present
  and valid under the current enrollment, with both native observations
  verified: `fn-pa-authorized-event` builds the kind-4 event
  (`fn-owner-peer-carried-event`, line 1190), `fnn-owner-identity-commit`
  publishes it and the owner's `(:complete)` finishes it
  (`fn-owner-finish`, line 531).
- Present and invalid: `fn-pa-served-word` (`fn-owner-served-carried-word`,
  line 1186) relays the plan's reason (`:article`, `:carrier`,
  `:carrier-shape`, `:local-enrollment`), the primitive observation's
  `:signature`, or the Store's `:conflict`; each is a Store refusal word in
  `books/nntp-post.lisp` with its own 441 line. The host computes none of it.

Transit is unchanged: it still reports `:refused` with the reason as a log
detail and answers 439.

## Theorems (books/owner-signed-post.lisp, prefix `fn-osp-`)

- `fn-osp-authorized-event-binds-the-post`: if `fn-pa-authorized-event`
  returns an event, the plan is `:ok`, the event is a kind-4 acceptance, and its
  decoded verdict event names the POST's Message-ID and the plan's
  generation. Lemmas: `fn-record-round-trip-succeeds`, `fn-stxa-bindsp`.
- `fn-osp-signed-post-finish-records-its-verdict` (keystone, valid arm): if
  that event is the Store's completion record and completion is enabled,
  then after `fn-own-step o '(:complete)` the Store's verdict lookup at the
  POST's Message-ID is that event's verdict at the plan's generation. Lemma:
  `fn-sn-finish-of-a-kind-4-acceptance-records-its-verdict`.
- `fn-osp-reader-after-signed-post-reports-its-verdict`: a reader opened
  after that `(:complete)` has `fn-stx-reader-verdict` at the Message-ID
  equal to that verdict's item. This is the HDR `:fn-verified` field by
  `fn-own-read-hdr-fn-verified-is-the-pinned-verdict`. Lemma:
  `fn-own-reader-opened-after-completion-pins-the-finished-verdicts`.
- `fn-osp-finished-post-outcome-is-durable`: after that finish,
  `fn-own-outcome-completion` of `:durable` is `:durable` (the 240).
- `fn-osp-served-refusal-renders-its-reason` (keystone, refused arm, over
  `fn-own-outcome`): for a relayed reason with no completion consumed after
  the take, the reply is `fn-nntp-post-outcome`'s line for that reason, and
  Store, ledger, feeds and connections are unchanged.
- `fn-osp-plan-refusal-is-a-served-reason`: a refused plan is never
  carrier-absent, and its reason is in the relayed set.

Not proved: that the prepared and published completion record is the event
ACL2 built. This is the same premise the P8 finish keystone takes. That the
recorded token is `:verified` in general needs an `fn-stxe` codec round
trip, which no book has. The test book shows it on the witness.

## Teeth (tests/acl2/owner-signed-post-tests.lisp)

The witness is a reachable served trace: `fn-own-read` of POST and a
carrier built from real carrier fixtures, then `(:take)`, the plan over the
injected octets (`(:ok ... 1)`), the event, the Store's identity
prepare/publish, `(:complete)`, `fn-own-outcome` 240, and a new reader's
`fn-own-read` of `HDR :fn-verified` answering `0 verified <principal>
keyring 1`. Must-fails:

- finish theorem: no enrollment (no event); a different authorized event
  that is not the completion record (generation 2); the gate closed.
- reader: the connection bound is full; the gate is closed.
- refusal: a Store word that is not relayed (`:duplicate`); the completion
  consumed; another connection; no submission in flight; the connection gone.

## Certification

- persvati, w25 ACL2 8.7, 2 jobs, 300 s, incremental:
  [`certify-20260924T174552Z-2994202`](manifests/certify-20260924T174552Z-2994202.json)
  certified the new book's closure (12 books). It was run at an uncommitted
  tree whose `books/owner-signed-post` was only its includes, to seed the REPL.
  [`certify-20260924T175653Z-3095992`](manifests/certify-20260924T175653Z-3095992.json),
  run `run-20260924T175630Z-4d05` at `9a9a94f0`: `--affected-by`
  `books/nntp-post`, `books/peer-authored-accept`, `books/owner-signed-post`,
  201 certified, passed, 438 s wall. Times: `owner-signed-post` 4.5 s, its
  tests 4.2 s, `peer-authored-accept-tests` 2.0 s, `nntp-post-tests` 1.8 s.
  Two dependents this lane does not edit ran over 10 s at 2 jobs:
  `byte-store-record-provenance` 13.6 s and `bp-handoff-status` 10.3 s.
- hbox, w28, 4 jobs, 600 s: the 113 default image roots at `9b2bd6b6`,
  [`certify-20260924T180628Z-1764223`](manifests/certify-20260924T180628Z-1764223.json)
  (run `run-20260924T180556Z-b6ea`), 61 certified and the rest installed from
  the cache, passed. Times over 10 s: `owner-invariants` 10.7 s and
  `bp-report-deletion` 10.1 s.

## Native (hbox scratch `/tank/fn/scratch/p8-signed-post/tree-9b2bd6b6`)

The developer image was built from that tree after `proof_artifacts acquire`
and `validate --profile default` (113 roots loaded, artifact set
`b9b40795…`), with `FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`
under `swarm-build`. Launcher `195381af1b5bc426…`, core
`abbee83471089e6b…`, build log `9288c8349e8c93d3…`.

| run | result | log SHA-256 |
| --- | --- | --- |
| `tests.test_native_hybrid_author` (`FN_RUN_HYBRID_E2E=1`) | 6/6, 13.5 s | `e3059aa3cb6adee1a6c975dd8bb4a2c293e784cf296cfd131ab21f499f0ce57c` |
| `tests.test_native_auth` | 4/4, 6.1 s | `cd9eb8307cc02b67dce1fe7c72f30d360006870c49164a9438380c4879d313fb` |
| `tests/native_peer_authored_accept_raw.lisp` (local SBCL, stubbed ACL2) | passed | `cfbbb03e0e989c04f14fe81d201003f78dfa206c0ec144ce4c205438f7da9256` |

The new case `test_signed_post_over_nntp_gets_the_transit_classification`
runs these steps, all over NNTP with no control socket after enrollment:

1. A tampered carrier gets `441 posting failed; the author signature does
   not verify`.
2. An unenrolled signer gets `441 posting failed; the signer has no current
   enrollment here (local-enrollment)`.
3. A malformed `FN-Authorship` gets `441 posting failed; the FN-Authorship
   carrier is malformed`.
4. A valid carrier gets 240, and `HDR :fn-verified` on a new connection
   answers `0 verified 5555…55 keyring 1`.
5. An unsigned POST gets 240.
6. HDR for the refused Message-IDs answers 430.
7. After a restart, the verdict is still `verified keyring 1`.

The first run of this module failed on a fixture defect: the tampered and
valid carriers were written to one output path. The fix is in the committed
test, and the logged run is the second. `tests.test_native_peering` skipped
all five of its cases in this tree because the source-matched hash variables
were not set. Those skips are not evidence. The logs are in
[`p8-signed-post/`](p8-signed-post/) with `SHA256SUMS`.

## Decision recorded, not changed

An agent correctly signs an article, but this node has not enrolled the
agent's principal. The node refuses the article with `local-enrollment`
(441 here, 439 on transit). It does not store the article unsigned. D02's
scope now includes served POST. The entry in
[decisions](../decisions.md) is marked pending ember.

## What this does not establish

- This was a lane developer image, not a qualification cut or the deployed
  node.
- The primitive signature observations are trusted (A-SIG-OBSERVE is still
  only proposed).
- No verifier outside fn checked these articles.
