# BP listener reconfiguration off the owner mutex

Item: LOCK-R2-LISTENER-RECONFIG-STDOUT. Design only; no code in this lane.
Facts below are read from `origin/lane/lock-ownership` (c719d9672).

## What runs under O today

`fnn-bpnc-execute` (bp-control.lisp:90) runs `fnn-quantum-bp` around
`fnn-owner-live-reconfigure-locked` (the durable config publish, which is the
sibling item LOCK-R2-LIVE-RECONFIGURE-IO and stays) and then
`fnn-bplc-reconfigure` (bp-listener-control.lisp:92). That runs `fn-owner-bplc-begin`
(`fnn-owner-core`, reads the owner config), the death cuts, and `fnn-bplc-drive`:
`fnn-tcl-listen`, `socket-close`, `fnn-out`. The drive is already a loop of
"ACL2 names ONE primitive (`fn-bplc-action`), host performs it, ACL2 steps the
model (`fn-bplc-step`)". Only `begin` needs owner state. The model is a
host-held carry on the listener node, stepped by the BP thread, which also runs
the control pump and the accept loop (bp-control.lisp:160-206), so nothing
interleaves with it. `fnn-core` calls on it already run outside O at startup
(`fnn-bplc-start`) and in the accept loop.

The 13 `fnn-emit` sites under O, by caller (checker run with a site printer):
- listener: `fnn-bpnc-execute` (bp-control.lisp:104), 1 site, reaching cut, bind line, runtime line;
- served BP node: `fnn-bpnode-receipt-result` (bp-node.lisp:202), the release-refused line, 1 site;
- one-shot commands on a PRIVATE owner (`fnn-bpo-call-with-owner-journal`,
  `fnn-quantum-command`, bp-obligation.lisp): `fnn-bpo-call-with-owner-journal`:57,
  `fnn-bpo-request-publish`:175/178/185/188, `fnn-carry-execute`:372,
  `fnn-command-bpo-owner-{receipt:124, recover:271/274, status:71, undertake:86}`, 11 sites.

## 1. Plan / act / settle

Plan (section, unchanged name `fnn-quantum-bp`): live-reconfigure, then
`fn-owner-bplc-begin` stores the target in the model (phase :stable -> :binding,
pending/retiring lists computed by `fn-bplc-begin`). The thunk returns
`:accepted` and no I/O. The cut `:configuration-published` moves after release.
Act (no lock): `fnn-bplc-drive` exactly as now, one `fn-bplc-action` primitive
at a time, stdout lines included. Settle: only on FAILURE (below); a success needs
no section because the model is not owner state and `fn-bplc-step` is pure.

In-between state: durable config at generation G+1; model `:binding` /
`:binding-active` / `:retiring` at generation G with ports unchanged. This is
the state a crash at `:configuration-published` leaves today and
`fn-bplc-recover` re-derives from the config. Safety, from the book:
`fn-bplc-accept-plan` demands phase :stable (no acceptance mid-change);
`fn-bplc-turn-plan` demands :stable before another reconfiguration, and control
requests are pumped by the same thread that is driving, so none can start;
`fn-bplc-failed-completion-fences-without-rollback` and
`fn-bplc-bind-and-retire-account-exact-descriptor-completions` already cover the
steps. What other sections now SEE: they run during the drive instead of waiting
on it, against the already-published config. Nothing in them reads the model.

## 2. Fencing equivalence: route the failure into a settle section

Choice: `fnn-bpnc-execute` calls `(handler-case (drive) (serious-condition (c)
(fnn-quantum-bp owner nil (lambda () (error c)))))`. The settle thunk re-signals
the ORIGINAL condition, so the one envelope classifies it
(`fnn-owner-shared-action-locked` -> `fnn-owner-classify-escape-locked` ->
`fn-fs-classify class step`, books/failure-scope.lisp:92) and installs the fence
before the settle's mutex is released, then re-raises it as the same
`fnn-store-indeterminate` / `fnn-store-fault` / refusal to the same handler
(`fnn-bpnc-handle`). Same function, same class, same lock discipline as today;
the rejected options are `fnn-owner-thread-escape` (reads a stale thread-level
`*fnn-section-step*`) and binding the step around it (fences after the mutex,
off the envelope, and forks the classifier call).
Equivalence argument: `fn-fs-classify` reads (class, step). The class is the
condition's own, so identical. The step in the old section at drive time is nil:
the publish ends in `fnn-fsync-dir`, which clears it (io.lisp:638), and the
drive's own primitives (listen, close) set none; the settle envelope binds nil.
Make that an invariant, not a coincidence: the plan section signals
`fnn-fault` if `*fnn-section-step*` is non-nil when it returns.
Not equivalent, by design: other sections may run between release and settle, so
the fence lands after commits made against the already-published, valid config.
The uncertain thing is the listener runtime, not the store, and the fence still
precedes any further client mutation after the settle. State this in the item.
Also in the settle: the model gets `(:bind-result :failed)` etc. exactly where
the drive already steps it; stdout and cut-pause errors (class unlisted) classify
as faults as they do now.

## 3. stdout: return lines for contended sections; declare the private owners

Choice: no buffer in `fnn-emit`. A hidden thread-global buffer flushed by the
generated envelope touches every section, reorders stdout against `fnn-err`
(log queue), and breaks the ordered markers below. Per group:
- listener (1): the lines are produced by the drive, which is now outside; nothing to return.
- bp-node release refusal (1): the thunk already returns `(values :receipt-refused detail)`;
  move the `fnn-out` (bp-node.lisp:202) to the caller after `fnn-quantum-bp`. It prints
  after the journal close instead of before; no test greps its position
  (`grep "release refused detail" tests` is empty).
- the 11 command sites: NOT moved, and NOT declared as exceptions (Deputy C's
  change). The owner is private to a one-shot process and the lines are ordered
  markers (`fnn-bpo-request-pause` prints a line then loops forever inside the
  section for the process-death cuts, so a deferred line would never print).
  They stay as findings: the `R2|fnn-emit|O:*` keys remain at weight 11, owned by
  LOCK-R2-OFFLINE-ONESHOT-HOLD. A checker-verified private-owner contract is that
  item's job and needs mutants (a published owner, a second thread, a global store).
Kept: per-line order within a thread, line-before-next-durable-step for commands,
the listener's `BP NODE LISTENING` before `runtime line`. Lost: for the receipt
refusal, order relative to the journal's close; for the listener, the old
guarantee that no other section ran between bind and its line (the point).

## 4. Verification

Clears (baseline keys, all 1-site reasons): `R2|fnn-emit|O:write-sequence`,
`...finish-output` (weight 13 -> 11; the key stays for the command sites),
`R2|fnn-bplc-cut|O:finish-output`, `|O:sleep`, `R2|fnn-bplc-drive|O:sb-bsd-sockets:socket-close`,
`R2|fnn-listen|O:sb-bsd-sockets:{socket-bind,socket-listen,socket-name,sockopt-reuse-address}`,
`R2|fnn-socket-shut|O:sb-bsd-sockets:socket-close`. Run
`lock_discipline_check.py --check` and `--write-baseline` for the removals only.
New raw tests (pattern tests/native_bp_node_admission_lock_raw-mock.lisp +
tests/test_native_bp_node_admission_lock.py): `native_bp_listener_off_lock_raw-mock.lisp`
(a) source: the `fnn-bpnc-execute` thunk contains no `fnn-bplc-*` or `fnn-out`; fails on
today's tree. (b) mock owner: a drive failure of each class (bind error ->
`fnn-store-indeterminate`, `fnn-fault`, an `fnn-os-error`) reaches the stop hook while
the mutex is held with the same exit code as running the same failure through the old
in-section path; (c) the mutex is free during the drive (a second section completes).
Image natives (`tests/test_bp_node_native.py`; there is no `test_native_bp_*` for the
listener): `test_live_listener_rebind_keeps_old_session_generation_and_fd`,
`test_live_listener_occupied_port_is_uncertain_and_restart_reconciles`,
`test_death_at_each_live_listener_effect_recovers_published_configuration`
(FN_BP_LISTENER_TEST_PAUSE_CUT), `test_control_listener_retires_after_one_normal_bp_session`.
Add one image case: during a PAUSE_CUT pause, a status request on the node answers.

## 5. ACL2 changes

None required. `fn-bplc-*` and `fn-fs-classify` are used as they are. Optional:
a theorem `fn-bplc-begin-only-from-stable-leaves-model-non-stable` is not needed
for soundness (it follows from `fn-bplc-turn-plan`'s :stable test).

## 6. Size and risks

~40 lines host (bp-control.lisp, bp-listener-control.lisp, bp-node.lisp), one raw test (~80 lines), baseline edits. One lane, small.
Risks: (1) closed: each drive primitive is admitted as a live section is (`fn-fs-section-admit :live` over `fnn-owner-service-stopping`, refused with the section's known refusal), pinned by a raw test where stop begins mid-drive; (2) the case-3 claim "no co-tenant in a
command's owner" is read from `fnn-bpo-call-with-owner-journal`, not proved; the lane
must confirm no worker thread waits on O in command mode. (3) the sibling item
LOCK-R2-LIVE-RECONFIGURE-IO still holds O across the publish in the same section;
this design composes with its off-lock publish phases (the plan section shrinks
further) and must not be sequenced after it as a prerequisite. (4) the re-signal
inside the settle depends on the envelope's wrap of the condition type; the raw
test (b) pins it.
