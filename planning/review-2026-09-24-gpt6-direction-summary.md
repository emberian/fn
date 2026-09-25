# gpt-6's chat summary of the 2026-09-24 direction review, and its source ledger

Forwarded by ember on 2026-09-25 (~08:20 UTC). The handoff document it
accompanies is `planning/review-2026-09-24-gpt6-direction.md` (same review
boundary: source at 70eda24b, incorporated through da67220d, deployed image
18c91321). This file holds the two parts the tree lacked: the reviewer's
chat-style assessment, and the handoff's source ledger with pinned links.
Where today's work answers a point, the coordinator's scorecard is in the
session log of 2026-09-25 (dev at the P3 merge), not here: this file is the
reviewer's words only.

## The chat assessment

fn is materially more on-track than at the last review; there is now much
more evidence of an actual usable system. The remaining danger is less "too
ambitious" than letting important semantics be decided accidentally by
whatever makes the next integration test pass.

What changed the assessment: the 18c91321 qualification (40/40 probe, 50
cut observations, 90 production SIGKILLs with nothing torn, lost or reused;
the in-place upgrade to the scale profile); the M4 experiment isolating the
policy that blocked the relayed topology; the independent verifier
`tools/fn_verify.py`; the carried prepare/advance work (5.5 to 3.5 ms per
POST at N=120) backed by caller correspondences. The unit of progress should
become: a person or agent completes a useful operation through the actual
interface, including refusal, interruption, recovery and retry, and the
critical guarantees follow that same path. No general audit cycle before
advancing M4, M5 or the human interface.

Calls on the decisions (implementation guidance, not a reopened
questionnaire):

| Decision | Assessment | The condition that matters |
| --- | --- | --- |
| D23 relay allowlists, receiver-side author enrollment, opaque carriage | right direction; architecturally important | permission to carry an origin's data must not become permission to issue a receipt that releases an obligation |
| D24 carry the peer invariant | agree | establish and preserve the premise; prove correspondence for the complete result/effect boundary the host uses |
| D25 duplicate/conflict on poster bytes | agree with the semantic target | removing four named fields is not an inverse of injection; generated Date needs explicit handling |
| D26 two-job ratchet | agree | wider runs are measurements, not regression verdicts; account for other load |
| P5 shared-owner faults may stop the service | agree with the qualified property | contain connection-local faults; fence uncertainty about shared authority |
| D02 signed POST on the normal interface | definitely retain | signing works through the ordinary interface, not an operator side door |
| kind-8 bounded retries; duplicate re-offer acknowledged | reasonable default | exhaustion is visible unresolved work; transport completion stays distinct from application receipt |
| special-purpose group names allowed | workable as an explicit local-agreement profile | never advertise as ordinary names; never derive control authority from spelling |
| scale-profile upgrade | done and reasonable | a larger admission bound is not evidence of capacity at that bound |

The easy calls: the retry count, diagnostic wording once semantics are
right, the proof-run job band, the small deployment's resource profile. The
lasting ones: what identifies the same submission, who may cause which
authoritative action, and what history can safely disappear.

D23 as four independent questions (is this neighbour admitted; may it
carry items claiming this origin in this scope; does this author/keyset
have permission for this local publication; does this receipt issuer have
authority to discharge this exact obligation), with distinct identity types
for a BP source EID, a signing principal and a neighbour's configured name.
An origin allowlist is a delegation, not origin authentication; keep
"received from R, claims source S, allowed under policy P, verification
result V" in the durable evidence. Opaque carriage must not require every
intermediate node to enrol every author, must keep "unknown local binding",
"unsupported profile" and "failed check" distinct, and needs an explicit
resource policy. Permission to transport Alice's article is not permission
to assert Bob's retention receipt: a finite trusted-relay receipt profile is
workable for the experiment if its claim says release rests on that trust;
through an untrusted intermediary the receipt itself must be bound to the
authorized issuer, exact work, subject, requester and terms. The next M4
gate begins at the native workflow (durable attempt, native request ADU,
FNBS, a real relay across an interrupted contact, the receiver's own
admission and commit, the receipt back, the exact pin released), with a
control work whose pin stays and an unauthorized issuer whose arrival
releases nothing; expected-refusal assertions are diagnostics, not the
milestone.

D25: keep the poster's source, the accepted record and the served
projection distinct; idempotency belongs to the stable identity and source.
A supplied Message-ID with no Date injected twice gets two generated Dates,
so the four-field rule is not enough and removing every Date is wrong; the
missing information is provenance. `fn-inj-reinjectionp` is the right
starting point. RFC 5537 §3.5 item 11: never modify a supplied
Injection-Date and never add one when Date and Message-ID were supplied.
The tests: same source with Date present and absent; one changed authored
byte; retry after lost reply and restart; a second identical post with a
new Message-ID. Clients persist the Message-ID before sending.

M5: physical packing, state/history compaction and content reclamation are
three capabilities with different invariants; the current pack is the
first. Expose pack/reclaim through the production operator path, check
temporary space first, say which limit it relieves; then choose the
logical-history representation deliberately (submission outcomes, unresolved
handoffs, key-policy evidence, number frontiers, reader pins,
anti-resurrection history are not one expendable cache). A committed-history
boundary detects some suffix losses; an allocation frontier is not that
boundary; an old valid snapshot needs a freshness reference outside itself.
Bounded long-lived behaviour under stated retention, release and workload
assumptions; explicit refusal is compatible with D03.

D24 and D26: carry the invariant; prove correspondence for the complete
result the host consumes; memoization is a different optimization with
different costs. Two jobs in a run is not an idle machine; keep
edit-to-certified-verdict as the productivity metric; split books for
locality, not for a dashboard.

The standing defaults: P5 names the fault domain (the EPIPE handling is the
right kind); retries bound automatic effort and never erase the work, and
the budget must not reset on restart; support TCPCL Completed on the
sender; RFC 5536's special names are patterns (first/only `to` or
`control`, any component `all` or `ctl`, exactly `junk`), never authority.

The next cycle: four complete outcomes in parallel (posting with stable
retry semantics at the served boundary; a native request through a real
relay with actual receipt return; a production node that maintains itself
without weakening promises; people and agents on one current qualified
image), plus one small repair: a compact current view per capability
(contract, host-called subject, proof identity, tested image and profile,
latest positive result, remaining obstruction, next operation) with the
historical evidence kept immutable. Keep "source implemented, theorem
established, image qualified, behaviour deployed" as four coordinates.

Bottom line: keep going; the project does not need a smaller vision. The
foundation to protect: the same source remains the same source; carrying a
claim does not grant authority over it; an acknowledgment means exactly the
commitment it names; reclaiming representation does not erase obligations.

## Source ledger (from the handoff)

- [R1] Deployment: planning/evidence/node-hbox-18c91321-2026-09-24.md at 70eda24b
- [R2] Image qualification: planning/evidence/qual-18c91321-2026-09-24.md
- [R3] M4 direct/real-relay experiment: planning/evidence/m4-app-receipt-2026-09-24.md
- [R4] Independent verifier: tools/fn_verify.py
- [R5] Carried prepare/advance and POST cost: planning/evidence/commit-path-2-2026-09-24.md
- [R6] Compaction preservation and limits: planning/evidence/m5-compaction-2026-09-24.md
- [R7] Decisions D23 to D26 and the standing defaults: commit 0e4b318e
- [R8] BP session admission: books/bp-session-admission.lisp
- [R9] BP request/receipt handoff: books/bp-app-handoff.lisp
- [R10] Exact Store duplicate/conflict predicates: books/store-node-existing-invariants.lisp
- [R11] Injection definitions and input policy: books/injection.lisp
- [R12] The exact reinjection relation: fn-inj-prefix, fn-inj-reinjectionp, fn-inj-decide
- [R13] Served-path index measurements: planning/evidence/t17-msgid-index-2026-09-24.md
- [R14] D26 implementation: commits da67220d and 28d1c279
- [R15] Proof-cost improvements without statement changes: commit 54b9b49e
- [R16] Web client developer-image evidence: planning/evidence/m6-web-2026-09-24.md
- [R17] README.md
- [R18] planning/now.md and planning/how-we-work.md
- [S1] RFC 5537 §3.5; [S2] RFC 5536 §3.1.4; [S3] RFC 9174 §5.2.4, Table 6
