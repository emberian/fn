# FAILURE-SCOPE (Fable deputy): the generated lifecycle + failure-scope protocol

Owner: FAILURE-SCOPE (Fable), 2026-10-03, taking over the work Astra (Codex) was to own
(whole-system-correctness-2026-10-03.md section 10.6 step 2; Astra's 6.1 + 6.2). First consumer:
t45 (lane/codex-fence-boundary, base d52815d5d = Astra's t43, unlanded). Review: failure-scope-review-1.md.

## Target (decisions/host-into-acl2-2026-10-03.md)

The declarations expand to executable, guard-verified ACL2 for every DECISION of the protocol: what a
class of failure does, the exit-code escalation, the thread lifecycle machine, the inbox admission word,
the stop/join settlement. The host keeps primitives: take/release a mutex, start/join a thread,
signal/handle a condition (the host names the observed CLASS; ACL2 decides), the syscall. Until
TCB-SHRINK reports, the emitted wrapper is ACL2 words plus a thin host envelope that only orders handler
clauses and installs the fence while the mutex is held.

## One family, two forms, both carrying failure: and workflow:

```
(def-section NAME
  :actor ACTOR                 ; who may run it (R9): committer | publisher | exporter | mux | accept |
                               ; control | feed | pull | cold | web | bp
  :class :control|:reader|:transit|:poster|:commit|:inspect   ; the gate class
  :admits :live | :cleanup     ; :live refuses once STOPPING (today fnn-owner-serialized); :cleanup may
                               ; run after the fence (fault-service, orcp-finish / orc-finish, the
                               ; pending-extent release, publication-done)
  :effects (:owner :durable :arena :log)   ; R2: a durable effect runs inside the fence boundary; by
                               ; construction every section does
  :failure ((:indeterminate :fence)    ; exit 3 installed BEFORE unlock
            (:fault :fault)            ; exit 4 before unlock; fn-owner-fault CID when a connection is named
            (:refusal :pass)           ; the known fnn-store-error class passes, caller-scoped
            (:other :fault)))          ; serious-condition / os-error inside a section

(def-actor NAME
  :loop ...                    ; the thread's body: a handwritten leaf with declared effects
  :register (:roster SLOT :receipt t)   ; registration lasts until the OWNER observes termination (the
                               ; join is the receipt); a thread never deregisters as its own last act
                               ; (Astra B3, r71 F10)
  :admit (:inbox LOCK :or-close)        ; admit-to-live-inbox-or-close: the receiver's lock decides
                               ; :admitted | :closed; the loser closes and settles (B2, r71 F9)
  :stop (:join :settle)        ; stop closes admission, joins, settles; a normal stop exit affirms the
                               ; stop predicate
  :failure ((:indeterminate :fence) (:fault :fault)
            (:refusal :log | :return-if-stopping | (:outcome WORD)) (:other :fault))  ; the top boundary
  :end-connection LABEL)       ; the connection-local scope = HOST-LIFECYCLE's fnn-connection-scoped
                               ; (indeterminate/fault re-signal to the owner boundary; refusal ->
                               ; :refused; os/socket -> :uncertain, this connection only). ONE home.
```

## Generated

In ACL2 (logic mode, guard-verified, theorems with teeth):
- `fn-fs-classify (SCOPE CLASS)` -> `(:fence 3) | (:fault 4) | :pass | :return`;
- `fn-ort-stop-exit-escalate (CURRENT NEW)`: a fence (3) is never masked (specs/host.md "a fence
  dominates"), then a fault (4), else the first outcome stands (sweep S015);
- the actor lifecycle machine registered -> running -> receipt -> joined, and the admission word;
- theorems: no parent class consumes :indeterminate/:fault (the condition hierarchy is bound: the
  host's typecase names the observed class, ACL2 decides); a section's failure transition happens inside
  its exclusion step; a stopped exit affirms STOPPING.

In the host: fnn-owner-gated / fnn-owner-serialized become ONE emitted wrapper (gate enter, body,
result install, cleanup, fence) whose clause ORDER is emitted from the scope, so LOCK-CHECK's R7 passes
strictly by construction; thread start / register / join primitives.

## Consumption

- OWNER-OFFLOCK's receipt words (:proceed / :uncertain / :fault / :drop) are the :failure keys of the
  syncer section (its WHERE, my WHAT).
- HOST-LIFECYCLE's `fnn-connection-scoped` is `:end-connection`'s expansion; no second helper.
- LOCK-CHECK polices the hand-written remainder; the enclave grows as sections convert.

## t45 now (hand fix, `; GEN: def-section failure:` / `; GEN: def-actor ... :failure` markers)

- fnn-owner-gated classifies its body exactly as fnn-owner-shared-action-locked does: one boundary,
  cleanup included, the fence installed before the mutex is released; fnn-owner-serialized = gated +
  the stopping refusal (no second wrap). Closes r71 F1/F2, S017, S019, S020 and t43's residual.
- the committer (S016 / Astra B1), the publisher, the exporter, tcpcl listen (S023) and node-secret
  create/rotate (r72 F6) get the ordered four-arm shape.
- monotone exit escalation through ACL2 `fn-ort-stop-exit-escalate` (books/owner-retire-settlement.lisp,
  the only book change); the syncer's stopping branch fences the store and escalates on a :stop step (S015).
- the reclaim's capture and install/swap quanta run through the stopping-checked form; its cleanup
  finishes the pass, then affirms the fence, then raises (S017, F1); the control reply's "owner fenced"
  becomes true.
- natives: the reclaim's install EIO after the rename (`state-checkpoint-replaced:eio` on the live owner:
  operator exit 3 + owner exit 3), the same cut through `store compact` (S019), a committer-thread
  fault/indeterminate selector (S016), node-secret fsync-dir EIO (F6). S020's observable is the unfenced
  window (structure test). S015's native (stalled barrier + SIGTERM + failed barrier) attempted last.

Overlap: HOST-LIFECYCLE's branch edits the publisher's and exporter's roster tails (F10/F12); t45
touches only the handler clauses beside them (adjacent hunks).

## Review 1 (failure-scope-review-1.md): the four must-fixes, adopted

- M1 (fail-open typecase): the host names the CONCRETE class (`fnn-condition-class`, `class-of`), ACL2's
  tables are closed (`books/failure-scope.lisp` `*fn-fs-*-classes*`; an unlisted class is a fault, tooth
  `fn-fs-an-unlisted-store-error-subclass-is-a-fault`); a structure test checks every host condition under
  fnn-store-error / fnn-os-error is named in a table.
- M2 (class alone does not say where): `*fnn-section-step*` is the boundary's last durable step, written only by
  the namespace primitives (`fnn-link`, `fnn-replace`, `fnn-rename-no-replace`, `fnn-unlink`, `fnn-mkdir`
  through `fnn-durable-step`), bound per boundary; `fn-fs-classify (class step)`: an OS error after a step is
  the fence (r72 F6 closes). The generator's `:effects` cut list will replace the primitive-level step with
  the declared program's cut (def-entry's `(:durable PROGRAM)`), one declaration with LOCK-CHECK's R2.
- M3 (exits that are no condition): `fnn-owner-gated` binds `*fnn-boundary-outcome*`; its unwind-protect
  installs a fault under the mutex when the body neither completed nor was classified; 17 early returns that
  crossed a quantum boundary were moved inside (a `block` in the quantum, or the value in place) and a
  structure test scans every host file for a return-from/return/throw that crosses a boundary. The fence
  step is STOPPING + the exit code under the roster mutex, before any log line. Declared exits (`:exits`)
  come with the generator; today none is admitted.
- M4 (cleanup set): pending-extent release is NOT admitted after a fence (t43 keeps it at 0 when stopping);
  the reclaim's stage unlink is refused after a fence (recovery's sweep removes it) and a failed unlink is
  recorded, never `ignore-errors`; orcp-finish runs before the raise. Unpins, the cold-worker and committer
  joins and the journal/FNFD close observation are the post-fence settlement (unchanged in t45).
- Q2: the exit is a lattice (`fn-fs-stop-exit-escalate`, ok < refused/usage < fault < fenced; proved
  monotone, fence never masked, ok the bottom); the dominated outcome is logged (`stopping: exit A dominated
  by exit B`).
- Q3: receipts = the owner's join (HOST-LIFECYCLE landed the exporter/publisher tails that way); the
  generator keeps it. S1 (`:admit` = r71 F9's closed bit under the inbox lock) is the generator's first
  def-actor obligation, after t45.

## t45 REPORT (lane/codex-fence-boundary, base d52815d5d = Astra's t43; READY sha in the message)

What landed (host/native/owner.lisp, io.lisp, tcpcl.lisp, admin.lisp, bp-node.lisp, hybrid-control.lisp,
peer-invite.lisp, operator.lisp; books/failure-scope.lisp NEW, books/owner-export-request.lisp; build.lisp,
build-dtn.lisp, image-world*, tools/extract/world*; host/interfaces.lisp; specs/host.md; docs/operator-internals.md;
planning/proofs.json PRF-1248; tests):
- r71 F1 / S017: the reclaim's capture and install/swap quanta are `fnn-owner-serialized` (stopping-checked, inside the
  fence); the cleanup runs orcp-finish FIRST (S017 b), refuses the stage unlink after a fence and records a failed
  unlink (review M4), affirms the fence, then raises; the control reply's "owner fenced" is true (native).
- r71 F2 / S019 / t43 rows 233-235: the release's, the publisher's and the exporter's parent catches are ONE arm each,
  ACL2 deciding (`fnn-owner-thread-escape`, `fn-fs-classify-job`); the publication's write arm names only the known
  I/O refusal; the done quantum is live. An uncertain archive publication is `archive-uncertain` (exit 3).
- S015: exit escalation is ACL2's lattice; the syncer's stopping branch fences on a :stop step.
- S016 / Astra B1: the committer's refusal arm is gone; one arm, ACL2 decides; a non-stopping refusal escaping the
  pipeline is contained as a fault (a defect of the pipeline, not a client event: the committer serves no connection).
- S020: closed by construction (every gated body is inside the fence); the quantum's early answer is a `block`.
- S023: tcpcl listen re-signals an uncertain outcome and a fault out of its accept loop; a lost connection stays this
  session's uncertain code; a known refusal this session's refused code.
- r72 F6: `fnn-node-secret-durable` (create and rotate): the barrier after the publication is uncertain (native).
- X08: `fnn-owner-admission-pending` is a named refusal of its request (store-error subclass in the closed table).
- 17 early returns that crossed a quantum boundary (admin, bp-node, hybrid-control, peer-invite, chunk-read) moved
  inside; a tree-wide structure test forbids the shape from now on (review M3).

What ran: structure tests `tests.test_native_owner.NativeOwnerHandlerStructureTests` 15/15 locally (the 8 new or
updated ones FAIL on d52815d5d: 6 failures + 3 errors in the base-tree copy); `tools/native_program_check.py` PASS;
`interface_emit --write/--check` and the natives: run ids below.

LOCK-CHECK (R7, checker at lane/lock-check fb4423550 run from a scratch copy over this tree): base tree 87, this tree
86 with today's contracts, 85 with these two declarations, which LOCK-CHECK should take instead of baseline rows:
`fence_boundaries += fnn-owner-gated`; `fence_functions += fnn-owner-thread-escape, fnn-owner-classify-escape-locked`;
`failure_scopes`: fnn-owner-classify-escape-locked (fence), fnn-owner-thread-escape (fence), fnn-owner-export-captured
(result). The remaining R7 rows in these functions are the checker's pattern limits, not defects: (1) `unfenced-gated`
rows (fault-service, serialized-with-control-turn, release-extents x2, maybe-publish-quantum, reclaim-dry-run x2,
reclaim-intern, reclaim-pass) persist because the kind keys on `gated_macros`, and `fnn-owner-gated` now CONTAINS
the fence by expansion (ask: a `fenced: true` flag on the gated macro, or expand it); (2) `overfence` rows on the
committer, release, publisher and exporter persist because a `serious-condition` arm whose body calls an
ACL2-deciding classifier is read as "routes refusals to the fence" (ask: a `classifies` failure scope -- fault and
indeterminate are routed by the closed table, a refusal is not fenced -- which is the shape every generated boundary
will have). Other rules: total 370 on both trees; R1b +1 (`*fnn-section-step*`, a special bound per boundary, see
below); the rest are moved fingerprints of changed functions.

Residuals, owned here unless named: S015's native (a stalled barrier that then FAILS after a graceful stop) has no
EIO selector for the barrier: structure test only. S017 (b)/(c) need a core fault injection at the swap: structure.
`*fnn-section-step*` is thread-local only where a boundary binds it (every owner quantum, the committer, the
publisher, the exporter, a command); a thread with no boundary of its own that calls a namespace primitive (feed/pull
journal rotation on its own thread, the log writer) writes the global, read only by the process's top-level
classifier -- def-actor binds it per actor (next). HOST-LIFECYCLE's maybe-publish 4-arm wrapper converts to one
thread-escape call after both land. OWNER-OFFLOCK drops the COMPLETE's inner shared-action-locked at its rebase.

## CONTINUATION (wind-down 2026-10-03, ember: push everything to dev, fix forward)

STATE: lane/codex-fence-boundary pushed; head = the sha in the runner message / the ledger (`repair.py list --owner
failure-scope`), base d52815d5d (Astra's t43, unlanded: merge t43 with it). All ten items (r71-F1/F2, S015-S020,
S023, X08, r72-F6) are state=ready at that sha; one READY, one merge.
- GREEN locally: `tests.test_native_owner.NativeOwnerHandlerStructureTests` 15/15 (8 new/updated, each red on
  d52815d5d); `tools/native_program_check.py` PASS; `interface_emit --write/--check` 0 on persvati (fetched and
  committed); `tools/extract/world.py` regenerated (books/image-world*, tools/extract/world*).
- NOT YET: natives. Run native-6ea819b75cdc (persvati) aborted at interfaces-check (the registry regen landed in
  the commit after); nothing has run on the final head. Relaunch: `tools/hbox_native.sh --box auto --detach
  --images developer,production,dtn-developer <head> tests.test_native_fence_boundary tests.test_native_owner
  tests.test_native_control tests.test_native_checkpoint_auto tests.test_native_expiry.DeveloperExpiryTests
  tests.test_native_maintenance_live tests.test_native_store_export tests.test_native_admin
  tests.test_native_peer_invite tests.test_native_hybrid_author tests.test_bp_node_native
  tests.test_native_owner_scheduler tests.test_native_slow_disk tests.test_bp_service_native`. The new natives
  (tests/test_native_fence_boundary.py) have never run: expect to fix forward their fixture details (the
  committer cases assume a batching development profile; the reclaim case asserts p0 reclaimed OR readable).
- Certification: farm run-20261003T022549Z-f421 (persvati, certify-20261003T022733Z-2852118) certified the 10-book
  closure of books/failure-scope + owner-export-request at the PREVIOUS book bytes; the last commit changed only a
  comment in failure-scope.lisp (its hash): resubmit `farm.py submit auto --affected-by books/failure-scope.lisp`.
- Expected fix-forward spots: (1) fnn-owner-gated now wraps every bare gated body in the fence; any bare body that
  signalled a non-store serious condition BY DESIGN (none found by review, but the natives are the proof) now
  stops the node; (2) the committer faults the service on a non-stopping refusal escaping the pipeline; if a
  native shows a legitimate refusal there, log-and-continue is the alternative (never the old silent death);
  (3) `*fnn-section-step*` is a special: bound in every owner quantum, the committer, publisher, exporter; a
  thread with no boundary writes the global (feed/pull journal rotation): def-actor binds it per actor.
- LOCK-CHECK: R7 base 87 -> 86 here (85 with the declarations in the t45 REPORT above); the remaining rows in the
  changed functions need the `classifies` scope and a `fenced` gated-macro flag (asks above, in the REPORT).
- Review must-fixes M1-M4 and Q2/Q3: APPLIED in t45 (section above); S1 (def-actor :admit = r71 F9's closed bit)
  NOT started.
- GENERATOR DESIGN STATE: the declaration family (def-section / def-actor) is the sketch at the top of this file
  with the review's amendments; its ACL2 half exists (books/failure-scope.lisp: fn-fs-classify, -classify-job,
  -exit-code, the stop-exit lattice; all proved with teeth, PRF-1248 row planned); its host half is the hand
  envelope in owner.lisp (fnn-owner-gated / fnn-owner-classify-escape-locked / fnn-owner-thread-escape, each
  marked `; GEN: def-section ...` / `; GEN: def-actor ...`). Not started: the macro that emits those from a
  declaration, def-actor's register/admit/stop (r71 F9/F10/F12, B2/B3), the mux adopt/stop conversion, and the
  `:effects` cut list shared with LOCK-CHECK's R2 (today the window is the primitive-level rename/link ->
  fsync-dir). TCB-SHRINK's primitive interface decides whether the envelope's remaining host part (handler
  ordering, the mutex) is emitted or hand-kept.
- Coordination done: OWNER-OFFLOCK (d7fe7f5c8) trial-merged with 11b37c6a1: one conflict (the committer loop; they
  take mine) and will drop COMPLETE's inner shared-action-locked; HOST-LIFECYCLE agreed on the adjacent hunks and
  their maybe-publish 4-arm wrapper is mine to convert after both land.

## Questions for the reviewer

1. The :cleanup admission set after a fence (fault-service, orcp-finish / orc-finish, pending release,
   publication-done refused): closed?
2. Escalation 3 > 4 > first-wins: agreed?
3. The receipt is the owner's join observation, never the thread's self-deregistration (HOST-LIFECYCLE
   already moved the exporter and publisher that way); the generator keeps it.
