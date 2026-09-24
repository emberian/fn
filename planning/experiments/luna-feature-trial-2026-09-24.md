# GPT-6-Luna feature trial, 2026-09-24

This is a source and review record for three small, independently useful fn
features. The isolated base is `eb2c55fd7b50fee84787dc7380f58ba7c4e3fdea`.
An unrelated cherry-pick briefly affected the shared `dev` checkout and was
resolved separately; this trial never edited that checkout.
All three implementation lanes use GPT-6-Luna at high reasoning effort. The
reviewer uses GPT-6-Sol, with GPT-6-Astra root assistance. The trial is an
Astra-assisted, Sol-led pilot, not a controlled model comparison. Costs below
include implementation, repairs, review, certification and integration work
as observed. The session counters at 03:00 UTC are cumulative context usage,
not billable-request tokens or a final currency total.

| Lane | Intended feature | Acceptance observations |
| --- | --- | --- |
| Web number windows | The loopback human reader offers older/newer links over at most 40 local article *numbers* per request. | A browser can traverse older and newer windows, including a window containing only holes; exact `OVER` ranges remain bounded and a later arrival does not silently move an explicit window. HTTP and NNTP socket tests verify the called path. |
| Offline cursor inspection | Native `consumer-inspect CURSOR.fncu` reads a bounded regular file and invokes the existing ACL2 `fn-cp-cursor-decode`. | Exact 346-octet encoded bound, valid field display, malformed/overbound refusal, and explicit wording that token contents prove no Store currentness, acceptance or processing. No local-control authority is acquired. |
| Local consumer status | Same-UID local-control `consumer status CONTROL ID` asks ACL2 for the registered consumer's committed ACK, committed Store journal frontier and event distance. | ACL2 checks the local principal/query/view scope, derives all three values, and has a bounded distinct FNCT reply. Native CLI prints those values without Store mutation; unknown/scope-mismatched IDs refuse. Called-path and native tests exercise the result. |

Source and tests are separate from image evidence: a passing Python or raw-host
test does not show the feature on a source-matched saved native image. The
shared image run is coordinated by the native qualification lane after the
isolated trial source converges. No change to `/tank/fn/node` is authorized by
this trial.

## Review and integration log

- 02:31 UTC: Reviewer created `lane/luna-feature-review` worktree from the
  isolated base and read the relevant project guide, architecture, milestone,
  decision, working-loop, web and consumer contracts. The three Luna lanes
  supplied planned interfaces before first commits.
- Early web review: numeric anchors must come from the requested window, not
  returned rows, so an all-hole window remains traversable. The lane's working
  diff follows this design and uses socket plus HTTP tests. Requested an
  entirely empty group witness.
- Early cursor review: the decoder allows a 512-octet preflight, but the
  encoder's exact maximum is 346 octets. The lane accepted the correction and
  changed its file-read ceiling to ACL2's existing
  `fn-cpj-max-cursor-octets`, with a 346/347 boundary test planned.
- Early status review: existing FNCT kind-5 replies permit only an accepted
  `fncu` cursor body. The lane changed the plan to a distinct fixed
  scalar reply; the consumer Store lane confirmed ACK comes from the durable
  scoped registration and frontier from the committed consumer projection.
- Root found an interface collision outside the trial base: the pending topic
  native tail already reserves FNCT request/reply kinds 7/8. The status lane
  changed its distinct reply assignment from kind 7 to kind 9. This is a
  concrete cross-lane review repair, with root providing the finding.
- Root also found that the first status proof target ID `PRF-066` collides
  with topic admission work pending outside the trial base; reader work already
  uses `PRF-067`. The status lane is moving its target to `PRF-068` and
  updating references. Both collisions show why the isolated base alone was
  insufficient to choose shared identifiers. They are integration-context
  costs shared by the trial brief and review, not evidence that Luna could not
  implement either codec or registry entry. The reviewer also did not discover
  them until root scanned the pending branches.
- Status review found that the first proposed `fn-col-status-event-distance`
  equation mostly unfolded the constructor; its companion status/position
  equation needed typed Store-state assumptions not present in the served
  scope test. The lane left the arithmetic equation as a supporting,
  non-registry fact, removed the status/position equation, and added a
  bounded kind-9 codec roundtrip target. A redundant `ACK<=frontier` premise
  was removed; the gap-type counterexample initially violated two premises,
  so the reviewer supplied an isolating negative-gap witness. Root's local
  `make check` found an unclosed form in the first native control edit. The
  local proof REPL also failed to launch with the first tool configuration;
  neither is certification evidence. The status lane owns those repairs.
- Before executing the raw host test, the reviewer found that its mock status
  omitted the `:status` tag and that its refusal case changed an unused mock
  variable. The lane owns both fixture corrections. These findings affect
  review and repair cost, even though the feature semantics did not change.
- Status source `76fd2161` and the raw fixture repair `a080f96b` were
  integrated into the isolated trial as `c4b087c3` and `acc47fa4`. The lane
  reports `git diff --check`, focused Lisp parse, ledger check, and
  `tests/test_native_owner_consumer_local_raw.sh` passing. Its first broad
  `make check` found an unclosed native-control form; after repair, the
  reviewer ran `make check` on the combined trial and it exited 0. The
  affected ACL2/test roots are being certified once on hbox under
  `run-20260924T024400Z-7fb1` (the submit reported 127 of 131 dependencies
  installed from cache); the manifest and native image evidence are pending.
- The first status roundtrip theorem did not certify. In bounded proof REPL
  work, the exact 13-byte `fn-frame-inputp` shape goal proved in 0.02 s and
  2,215 prover steps; two bridge attempts still left a `NTHCDR 4` u32-tail
  length goal. The lane removed the proposed general roundtrip from the book,
  left `PRF-068` in progress without a keystone event, and retained concrete
  accepted/refused/malformed/overbound codec tests. The ACL2 behavior and
  its test book still require certification at their final bytes. This is an
  explicit proof gap and part of review cost, not a claim that the native
  status result is unsound.
- Hbox status retry `run-20260924T025418Z-2d65` exited 1; manifest
  `certify-20260924T025423Z-769145.json` shows the corrected ACK owner-local
  test passed while `fn-ncl-status-reply-encode` failed guard verification:
  scalar uint validity did not establish `true-listp` for the encoded payload
  passed to `fn-frame-protected`. The lane owns a local guard hint using the
  existing `fn-cp-u32-bytes-true-listp` lemma. That retry,
  `run-20260924T025645Z-e51e` / manifest
  `certify-20260924T025650Z-770557.json`, exited 1 at the same protected-frame
  `true-listp` guard goal. The lane is replacing its copied frame construction
  with `fn-nctrl-seal`, the preexisting equivalent sealer with guard `t`, and
  retry `run-20260924T025802Z-a71e` / manifest
  `certify-20260924T025807Z-771664.json` passed the encoder guard, then
  failed at the status decoder guard after the generic frame decoder expanded
  (~3.19 million prover steps). An explicit `:guard t` declaration for the
  status open/decode wrappers did not fix the decoder: final Luna run
  `run-20260924T025929Z-1431` / manifest
  `certify-20260924T025934Z-772895.json` again failed that guard (8.247 s,
  3,452,572 steps). The Luna lane stopped proof work and handed off at
  `e0066871`; this was a substantive proof/guard repair cost, not a passing
  source packet. The user then directed that Luna implement bounded features,
  fixtures and UI while Sol owns fn proof development and certification
  failures in future trials.
- Sol's `dfcdad5c` moves payload octet validation before the status field
  parser and checks all parsed uint32 fields before arithmetic. The call order
  was a real guard defect: the old decoder tried to parse a payload that the
  frame result had not yet shown to be an octet list. Scoped hbox run
  `run-20260924T030407Z-c9a5` certified the control book and exposed two
  preexisting new-test fixture mistakes: space is a printable ID, and an ACL2
  `defconst` cannot evaluate the frame-digest attachment. Sol changed the
  invalid ID to newline and kept frame construction inside `assert-event`.
  Scoped `run-20260924T030609Z-3a66` / manifest
  `certify-20260924T030612Z-780267.json` exited 0: the exact control book was
  reused from its successful prior certificate, and the changed control test
  book certified. This is Sol-authored implementation/test repair, not a Luna
  proof success. The general status reply roundtrip theorem remains open.
  Interactive proof work also hit a separate tooling limit: the local ACL2
  launcher was unqualified, while hbox `proof_repl.py` required one complete
  cached dependency set and refused the composed 87-book set that
  `farm.py submit` had installed successfully. The scoped farm results above
  establish the guard repair; the REPL refusal is not a model proof failure.
- Web packet `270be16d` was integrated as `d955097f`; its annotation cleanup
  `b94bc38b` was integrated as `a9d9dd90`. The lane's Python 3.9.25 run passed
  15 tests in 7.718 s, and Python 3.14 passed the same 15 in 7.734 s. The
  reviewer independently ran `python3 -m unittest tests.test_fn_web` on the
  integrated trial and got 15/15 in 7.675 s. Tests use HTTP plus the fake
  node's actual NNTP socket. An initial lane run failed two newly written
  assertion wordings; after repair and the empty-group case, the suite passed.
  The observed session creation was 02:27:51.670Z; the first commit was
  02:32:45Z and annotation cleanup 02:33:56Z. Those roughly five and six
  minute intervals are wall clock to source packets, not active compute time
  or accepted feature cost. The reviewer mistakenly flagged Python 3.9 union annotations,
  then retracted the concern after finding the existing postponed-annotation
  import. The cleanup commit changes annotations only, so this was review
  churn, not a behavior repair.
- Cursor packet `28f49e0f` was integrated as `f3ae65e4`. The observed session
  creation was 02:28:08.403Z and commit at 02:34:13Z, roughly six minutes
  wall clock to the source packet, with no private proof, build or native test
  run. This is not accepted feature cost. One precommit reviewer correction changed the file ceiling from the
  decoder's 512-octet preflight to the encoder's exact 346-octet maximum. The
  exact value came from a preexisting ACL2 accessor and would have improved the
  lane brief; this correction was cheap and before source packet acceptance.
  The registered native verb calls `fn-cp-cursor-decode`; three binary fixtures and
  a gated native test cover the boundary and malformed cases. The test remains
  pending a source-matched shared image.
- Root found one real web behavior gap after the first packet: fn can report an
  empty group as `211 0 watermark watermark-1` with watermark above 1. The
  first fake-node empty-group witness used `211 0 1 0`, so it missed a spurious
  Newer link from the empty initial window. The web lane repaired it in
  `c22ba496` (integrated as `acc3e615`) by gating navigation on a nonempty
  GROUP span. The new socket fixture supplies `211 0 100 99`; an explicit
  requested range still issues its exact `OVER`. This is one real behavior
  repair round. The lane's 15 tests passed in 7.674 s; the reviewer reran them
  on the integrated trial in 7.690 s, all passing.
- Native web coverage was widened in test-only Luna packet `30fb2e48`
  (integrated `e9d2d442`): one scratch native owner receives two HTTP posts,
  and exact 1–1/2–2 number windows show the selected article and adjacent
  Older/Newer links. Python 3.9 and 3.14 compile checks passed; this test has
  not yet run on the source-matched shared image. The fake socket suite carries
  the sparse and 40-slot cases, so the native case does not need 41 posts.
  Root noticed the test edit had removed its earlier HTML escaping witness by
  replacing `<visible>` body text with plain text; Luna restored that
  assertion in test-only `90fbe689` (integrated `db4774fc`). Both Python 3.9
  and 3.14 compile checks and `git diff --check` passed. This is a test
  regression repair found during review, not a product behavior change.
- The trial also includes native qualification's independent BP report-cut
  repair `57633aa4` and its earlier-image evidence `e7475075`, cherry-picked
  as `2a4c4e8b` and `af5c1e53`. They are not Luna feature contributions.

## Measured resource scope

The sanitized [03:00 UTC session aggregate](luna-feature-usage-0300.json)
records the four named Codex threads only, with first and last cumulative
snapshots and no transcript content. At that cutoff the three Luna lanes used
34,088,020 input tokens and 104,908 output tokens (34,192,928 total); the
Sol reviewer used 36,199,088 input and 42,981 output (36,242,069 total).
Cached input is already included in input, and reasoning output in output;
neither is added again. The cursor measurement follow-up is excluded from its
feature-phase row. Root/Astra assistance, native qualification, integration
after 03:00 UTC and measurement overhead are outside these four rows.

Using the official [standard short-context API price table](https://developers.openai.com/api/docs/pricing)
only as a like-token-mix proxy, root estimated approximately $0.45 for the
three Luna threads and $8.07 for the Sol reviewer through 03:00 UTC. These
are not a bill or quota reading: service tier and actual per-request context
sizes are not fully available in the session records. The review/coordination
cost dominates this pilot's proxy despite quick Luna source packets, so this
trial does not yet demonstrate a lower cost per accepted fn feature. The
  status proof/guard loop was the largest measured Luna lane; moving proof work
  to Sol in future fn trials is the user's adopted direction.

Root landed the status source and Sol repair on `dev` at `e160442f` and ran
`make check` successfully. The reviewer initially submitted a 12-job
persvati treewide qualification, overlooking the shared four-job trial budget.
The exact run process group was verified and terminated before a manifest;
completed immutable cache entries were retained. This is reviewer
coordination cost. The corrected four-job hbox run
`run-20260924T031246Z-1771` on frozen `e160442f` passed with manifest
`certify-20260924T031327Z-785374.json`: 343 default, DTN and ACL2-test
roots, 594 of 597 exact-source/toolchain books loaded from cache and three
newly certified. The native qualifier is building one image pair from that
gate; image behavior is still pending.

Source commits, repairs, test commands, manifests, image revision and final
per-feature disposition will be appended as the packets finish. Reviewer
implementation changes, if any, will be labeled separately.
