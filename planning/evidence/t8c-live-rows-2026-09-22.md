# T8c: the two live-configuration rows of the dabebb84 matrix (2026-09-22)

Lane `t8c/live-rows`, worktree `build/lanes/t8c-live-rows`, from the WIP
checkpoint 8fcb57ad (the first incarnation's work) merged with dev 097c3274.
Subject rows: `V0-CFG-LIVE` and `V0-CFG-LIVE-REFUSE` of
`planning/evidence/v0-runs/20260922T204325.546307Z-0a8b592-0bffc80c1571/`.
The run's deploy directory (and the node logs in it) no longer exists on hbox;
report step 151 kept only the first line of the log tail.  Every cause below
was therefore reproduced again, on hbox, against copies of the matrix store
`/home/hbox/fn-native-matrix/a/store` (`cp -a`, so the matrix store itself was
not written), under `/home/hbox/fn-t8c/r-*/`, with the dabebb84 cores
(production `fn-host.core` sha256 6e9ab804..., the matrix's; developer
`fn-host-developer.core` sha256 e5030c47...), runtime `/tank/fn/sbcl/bin/sbcl`,
`FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`.  Script:
`/home/hbox/fn-t8c/repro.sh`.  Every owner started was stopped by its
recorded pid; nothing is left running.  `/tank/fn/node` was not touched.

## Row 1, V0-CFG-LIVE: exit 3, then GROUP got no reply

The owner DIED.  "No reply" is `ConnectionRefusedError` in the matrix's probe
(step 142), not a hang and not a silent refusal.  Reproduced on the
production core: operator exit 3 (`uncertain operator group`), owner exit 4,
log `fault operator run`, no configuration record written.

Three defects stacked on this row in the image, and a fourth open item:

1. **The live arm faulted the owner on every request** (not explained by T8,
   and still present on dev).  dabebb84 `host/native/admin.lisp:123` read
   `fn-owner-open`'s answer through `fnn-owner-action`, which faults on
   anything but a keyword (`host/native/owner.lisp:71`); `fn-owner-open`
   answers the new connection's integer id or NIL (`host/owner-host.lisp:1001`).
   Diagnosed with a handler that logs the condition:
   `FNN-STORE-FAULT: owner returned non-action from FN-OWNER-OPEN`.
   Fix: read it through `fnn-owner-core` as the socket path does
   (`host/native/owner.lisp:1053`), faulting only on a value that is neither
   NIL nor a non-negative integer.
2. **The owner's own terminal word was lost, so the caller said uncertain.**
   The fault fences the owner (`fnn-owner-shared-action-locked`), whose stop
   hooks run `fnn-control-stop` synchronously in the worker's thread, which
   shuts every client socket including the one about to carry the reply
   (dabebb84 `host/native/control.lisp:164`; hook at `:388-391`).  The client
   reads a closed connection and correctly reports uncertain (exit 3) where the
   owner had classified fault (exit 4).  Fix (`fnn-control-answering`): a
   worker withdraws its socket from the stop set once its whole frame is read;
   it is no longer blocked on that socket, its send runs under the reply
   deadline, and `fnn-control-close` still joins it.  The fault and uncertain
   handlers now also log the condition to the owner's stderr (the matrix's
   death note reads that log).  So this row was two defects in the owner and
   one correct client: an uncertain outcome that also killed the connection.
3. T8's octet-label defect (fixed on dev by 4931dcb4): with (1) and (2)
   patched but not T8's bridge, `group create` is refused (exit 1), nothing
   published, owner alive.
4. T8b, open: with (1), (2) and T8 patched, `group create` exits 0, record
   `00000009.cfg` is published, the owner stays up, and `GROUP fn.matrix.live`
   answers `411` until a restart (books/owner-config.lisp OPEN item 3).  The
   row will stay a disagreement (refused, expected accepted) until T8b lands.

Measured (developer core, `LOADS=` host patches extracted from this tree;
`patch-t8.lisp` is dev's `fn-native-admin-plan-deltas` and bridge):

| patches | operator | owner | records |
| --- | --- | --- | --- |
| none (production core) | exit 3 uncertain | died, exit 4 | 8 |
| control only | exit 4 fault | died, exit 4, reason logged | 8 |
| admin + control | exit 1 refused | alive, exit 0 on SIGTERM | 8 |
| admin + control + T8 | exit 0 accepted | alive; GROUP 411 | 9 |

## Row 2, V0-CFG-LIVE-REFUSE: accepted, generation 7

Not two writers on one store.  The offline executor ran AFTER node A's owner
had died in row 1, so the writer lock was free and acceptance was correct.
With an owner alive the same image refuses: production core, owner live,
offline `group create` over the same store: exit 1, `refused operator group
store is already locked`, nothing written, owner still serving (`GROUP
fn.letters` 211) and stops with exit 0.  The row's expectation ("refused")
was right; the harness was wrong to run the offline half without asking
whether the owner was alive.  `tools/v0_matrix.py` now asks
(`self.alive(self.a)`) after the live verb, appends the death to the
observation and records V0-CFG-LIVE-REFUSE not-exercised with that blocker.

The ACL2 decision at the publication boundary was vacuous: `fnn-admin-authorize`
passed a literal `t` as LOCK-OWNED.  It now passes `fnn-admin-lock-observation`
(the store is writable and holds its lock descriptor), so ACL2's existing
`:lock` refusal is reachable from the host and is reported as a refusal
(`fnn-refuse`, exit 1).  The earlier refusal, at the nonblocking flock when the
store is opened (`fnn-open-lock`, host/native/io.lisp), is unchanged.

## Theorem

`fn-native-admin-publication-is-authorized-only-under-the-lock`
(books/native-admin.lisp): for all inputs, if
`fn-native-admin-publication-authorize` answers `:accepted`, LOCK-OWNED is
true; and if its result carries a publication state (jpub), LOCK-OWNED is
true.  Subject: `fn-native-admin-publication-authorize`, returned with
LOCK-OWNED unchanged by the program-mode wrapper
`fn-store-cfg-native-admin-authorize` (host/store-node-host.lisp:110), called at
host/native/admin.lisp:62-65 for both the offline executor and the live arm.
Every write goes through `fnn-immutable-publish-effect`, gated at
host/native/immutable-publish.lisp:24 on a jpub equal to `(fn-jpub-initial t)`,
which is non-NIL.  Cited under PRF-028 in planning/proof-events.json.  It is
proved by unfolding the definition (the whole accepting subtree sits under the
lock test); its weight is that the host now supplies a real observation.

Teeth (tests/acl2/native-admin-tests.lisp): the witness is accepted with the
exact executor-admitted jpub; the same inputs with LOCK-OWNED NIL are refused
`:lock` with no jpub; `must-fail` with the acceptance hypothesis dropped, and
with the jpub hypothesis replaced by its negation, both refuted by that
value.  Loaded in a proof_repl session over the whole book (the theorem and
the test book, both must-fails returning T).

## Harness tests

On hbox with wrapper images over the dabebb84 developer core
(`/home/hbox/fn-t8c/fn-host-patched`: this tree's host patches plus T8;
`fn-host-t8only`: dev's state), `tests.test_native_live_reconfiguration.LiveReconfigurationImageTests`:

* patched: 4 run, OK (1 expected failure, the T8b served-before-restart test).
* T8 only: `test_the_live_verb_answers_and_the_owner_keeps_serving` and T8's
  own `test_a_live_peer_add_leaves_a_pinned_reader_unchanged_and_is_durable`
  FAIL with `uncertain operator group`.  T8's image test was never run on an
  image (it skipped); it fails on dev's code.
* `test_an_offline_mutation_is_refused_at_the_lock_while_the_owner_lives`
  passes on both (exit 1, `already locked`, then accepted with no owner).

Defect (2) already had a failing test nobody ran on the image:
`tests.test_native_operator_verbs...test_the_production_image_refuses_the_selector`
on the dabebb84 production image fails 3 of 3 (`3 != 4 : uncertain operator
post`); with only the control patch on the production core it passes 3 of 3.

After merging dev bb0affe6 (t5/host rewrote the developer selectors and the
control stop; `fnn-control-answering` and the logged handlers merged
without conflict), the host patches were re-extracted from the merged tree
and the live-reconfiguration image tests rerun on hbox: 4 run, OK (1
expected failure).  The operator-verbs production-selector test no longer
witnesses defect (2) after the merge: t5's `fnn-developer-selector-gate`
refuses the selector at startup, before any control request, so on the
dabebb84 core that test now times out waiting for an owner that the old image
starts.  No remaining developer selector makes a control request end in
`fault` rather than `uncertain` (`recordbarrier` and `postpublish` both end
uncertain, exit 3, patched or not), so on the next image defect (2) has a
source check (`test_a_request_being_answered_is_not_shut_by_the_stop_it_caused`)
and the measurements above, and no image test.  That gap is open.

Local: `tests/test_native_admin_authorize_boundary.sh` PASS (both lock
observations pinned); `tests.test_native_live_reconfiguration` source tests
and `tests.test_native_v0_matrix` (41, including the dead-owner case) OK.

## Certification

`python3 tools/farm.py submit persvati books/native-admin
tests/acl2/native-admin-tests books/native-config-observation
books/native-control books/native-hybrid-control books/native-operator
tests/acl2/native-config-observation-tests tests/acl2/native-control-host-tests
tests/acl2/native-control-tests tests/acl2/native-hybrid-control-tests
tests/acl2/native-operator-host-tests tests/acl2/native-operator-tests
--closure --jobs 4 --timeout-seconds 1800 --remote-root
/home/ember/fn-gates/t8c-live --acl2
/home/ember/fn-gates/toolchains/w25/acl2-literal --cache
/home/ember/fn-certcache`, run `run-20260922T221435Z-52de`, exit 0, 103
books passed, no failures (tree 207a42ed; the later merge of dev bb0affe6
changes no book in this closure).  Manifest
`planning/evidence/manifests/certify-20260922T221439Z-474314.json`.
(`--affected-by books/native-admin` was refused by certify_books because it
selects host roots.)  `tools/green_check.py --changed-since 097c3274
--strict`: the lane's two books and every book dependent on native-admin
are green; the one book it names not green, `books/byte-store-programs`,
came in with dev.

## Not verified

No image carries these fixes until the next freeze.  The hbox runs load raw
host patches into the dabebb84 developer core; they are not the image the
next freeze will build.  V0-CFG-LIVE stays a disagreement until T8b.
