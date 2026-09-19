# Lane dump: `crash-fidelity`

Branch `lane/crash-fidelity` from `0bd0b5c`, worktree
`/Users/ember/dev/fn/build/lanes/crash-fidelity`. Written 2026-09-19 at the
usage stop. No certification is running (see In progress).

## 1. Packet as understood

1. **D4.** `fn-sf-crash` modeled a crash in `:frontier-data-durable` as old-only
   and in `:record-data-durable` as absent-only, but `tests/store_crash_child.py`
   kills the host after `os.replace` (line 30-41) / `os.link` (80-91) have
   returned and before ACL2 observes `:ok`. Make both cuts model crash points
   with a genuine choice; re-prove the crash, trace and exploration theorems;
   extend the exploration with a txid-gap record; report true state/transition
   counts distinguishing transitions from applications; prove that a completed
   barrier constrains the crash outcome rather than being asserted by it, with
   teeth.
2. **D5.** Acknowledged-history theorems quantify over ghost `successes`, and
   `fn-sn-open-observed` builds `successes = nil`, so across a restart their
   premise is unsatisfiable. Either reconstruct `successes` from the image or
   restate retention over records; the premise must be inhabited by the host's
   entry `fn-sn-open-observed`; say which theorem now carries A-DURABILITY as a
   hypothesis rather than as the constructor.
3. **D6.** Prove `fn-sn-open-observed` success implies `fn-snt-relation`,
   witness it, and restate the exact-replay theorems from that root.
4. Remove or mark `unreachable-in-composition` every dead branch
   (`:fenced-core`, `:fenced-reservation`, `:fenced-before-record`,
   `:completed`, `fn-sf-lose-success`, the fence/resolve helpers).
5. Update the four owned specs; replace the 9,038-edge sentence with true
   counts; name modeled versus physical crash points.

Gate: `make check`; full `make certify` green after the changes.

## 2. DONE (certified in this worktree)

Evidence directories (all `build/acl2/certify-*`, manifests `status: passed`
unless stated):

| Run | Books | Result |
| --- | --- | --- |
| `certify-20260919T053255Z-94181` | store-files, store-files-invariants, store-files-tests | store-files passed; invariants failed at `fn-sf-admissible-image-facts` (case explosion), fixed below |
| `certify-20260919T053440Z-95864` | store-files-invariants, store-files-tests | passed |
| `certify-20260919T053501Z-96156` | store-files-traces, store-files-traces-tests, store-files-exploration-tests | first two passed; exploration failed only on placeholder counts |
| `certify-20260919T053529Z-96624` | store-files-exploration-tests | passed |
| `certify-20260919T053546Z-96878` | store-node, store-node-invariants, store-node-tests, store-node-traces, store-node-traces-tests, store-node-resolution, store-node-resolution-tests, store-node-resolution-traces, store-node-resolution-traces-tests, store-observed, store-observed-tests, store-node-guards-tests | first nine passed (per-book `FN_CERTIFY_SUCCESS` markers in their logs); the runner was killed by a shell reset while certifying `store-observed`, so no manifest exists for this run |

### 2.1 `books/store-files.lisp` (certified)

- Phases removed: `:fenced-reservation`, `:fenced-before-record`,
  `:fenced-core` (and from `fn-sf-fencedp`, `fn-sf-record-phasep`,
  `fn-sf-completion-phasep`, `fn-sf-phase-shapep`).
- `fn-sf-refuse-reservation (s txid)`, `fn-sf-abort-completion (s sequence
  txid)`, `fn-sf-core-completion (s sequence txid)`: `result` parameter and the
  `:uncertain` / `:lost` / `:rejected` branches removed (the host never reports
  them; `Acl2Store` never sends them, `acl2_symbol` at `tools/run_store.py:195`
  would refuse the phase words; the host fences on its own side and reopens).
- `fn-sf-frontier-new-visiblep` now `'(:frontier-data-durable
  :frontier-attempted :fenced-frontier)`; `fn-sf-record-present-visiblep` now
  `'(:record-data-durable :record-attempted :fenced-record)`.
- New guard-verified predicate:

```lisp
(defun fn-sf-crash-imagep (s frontier records)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sf-statep s)
       (or (equal frontier (fn-sf-frontier s))
           (and (fn-sf-frontier-new-visiblep s)
                (equal frontier (fn-sf-frontier-candidate s))))
       (or (equal records (fn-sf-records s))
           (and (fn-sf-record-present-visiblep s)
                (equal records (append (fn-sf-records s)
                                       (list (fn-sf-record-candidate s))))))))
```

- Marked `unreachable-in-composition` with comments: `fn-sf-lose-success`,
  transient phases `:aborting` (inside `fn-sn-known-abort`) and `:completed`
  (inside `fn-sn-finish`).
- Theorem `fn-sf-lost-core-completion-fences` removed (its branch no longer
  exists); replaced by:

```lisp
(defthm fn-sf-completing-admits-only-matching-completion
  (implies (and (fn-sf-statep s)
                (equal (fn-sf-phase s) :completing))
           (and (equal (fn-sf-start-frontier s) s)
                (equal (fn-sf-prepare-record s record groups capacity) s)
                (equal (fn-sf-emit-success s sequence txid) s)
                (implies (not (equal (cons sequence txid) (fn-sf-completion s)))
                         (equal (fn-sf-core-completion s sequence txid) s)))))
```

### 2.2 `books/store-files-invariants.lisp` (certified)

Re-proved unchanged in statement: `fn-sf-crash-preserves-state`,
`fn-sf-stable-records-prefix-of-crash`,
`fn-sf-surviving-candidate-is-exact-and-dominated` (its
`fn-sf-record-present-visiblep` hypothesis now covers `:record-data-durable`).
New:

```lisp
(defthm fn-sf-unobserved-frontier-replacement-crash-is-old-or-new
  (implies (and (fn-sf-statep s)
                (equal (fn-sf-phase s) :frontier-data-durable)
                (or (equal record-choice :absent)
                    (equal record-choice :present)))
           (and (equal (fn-sf-frontier (fn-sf-crash s :old record-choice))
                       (fn-sf-frontier s))
                (equal (fn-sf-frontier (fn-sf-crash s :new record-choice))
                       (fn-sf-frontier-candidate s))
                (equal (fn-sf-records (fn-sf-crash s :old record-choice))
                       (fn-sf-records s))
                (equal (fn-sf-records (fn-sf-crash s :new record-choice))
                       (fn-sf-records s)))))

(defthm fn-sf-unobserved-record-link-crash-is-absent-or-present
  (implies (and (fn-sf-statep s)
                (equal (fn-sf-phase s) :record-data-durable)
                (or (equal frontier-choice :old)
                    (equal frontier-choice :new)))
           (and (equal (fn-sf-records (fn-sf-crash s frontier-choice :absent))
                       (fn-sf-records s))
                (equal (fn-sf-records (fn-sf-crash s frontier-choice :present))
                       (append (fn-sf-records s)
                               (list (fn-sf-record-candidate s))))
                (equal (fn-sf-frontier (fn-sf-crash s frontier-choice :absent))
                       (fn-sf-frontier s))
                (equal (fn-sf-frontier (fn-sf-crash s frontier-choice :present))
                       (fn-sf-frontier s)))))

(defthm fn-sf-crash-outside-namespace-window-keeps-image
  (implies (and (fn-sf-statep s)
                (not (fn-sf-frontier-new-visiblep s))
                (not (fn-sf-record-present-visiblep s)))
           (and (equal (fn-sf-frontier
                        (fn-sf-crash s frontier-choice record-choice))
                       (fn-sf-frontier s))
                (equal (fn-sf-records
                        (fn-sf-crash s frontier-choice record-choice))
                       (fn-sf-records s)))))

(defthm fn-sf-completed-frontier-barrier-removes-old-choice
  (implies (and (fn-sf-statep s)
                (equal (fn-sf-phase s) :frontier-attempted))
           (equal (fn-sf-frontier
                   (fn-sf-crash (fn-sf-frontier-dir-result s :ok)
                                frontier-choice record-choice))
                  (fn-sf-frontier-candidate s))))

(defthm fn-sf-completed-record-barrier-removes-absent-choice
  (implies (and (fn-sf-statep s)
                (equal (fn-sf-phase s) :record-attempted))
           (equal (fn-sf-records
                   (fn-sf-crash (fn-sf-record-dir-result s :ok)
                                frontier-choice record-choice))
                  (append (fn-sf-records s)
                          (list (fn-sf-record-candidate s))))))

(defthm fn-sf-crash-image-is-admissible
  (implies (and (fn-sf-statep s)
                (fn-sf-crash-choicep frontier-choice record-choice))
           (fn-sf-crash-imagep s
                               (fn-sf-frontier
                                (fn-sf-crash s frontier-choice record-choice))
                               (fn-sf-records
                                (fn-sf-crash s frontier-choice record-choice)))))

(defun fn-sf-image-frontier-choice (s frontier)
  (if (equal frontier (fn-sf-frontier s)) :old :new))
(defun fn-sf-image-record-choice (s records)
  (if (equal records (fn-sf-records s)) :absent :present))

(defthm fn-sf-crash-realizes-every-admissible-image
  (implies (fn-sf-crash-imagep s frontier records)
           (let ((crashed (fn-sf-crash s
                                       (fn-sf-image-frontier-choice s frontier)
                                       (fn-sf-image-record-choice s records))))
             (and (equal (fn-sf-frontier crashed) frontier)
                  (equal (fn-sf-records crashed) records)
                  (equal (fn-sf-phase crashed) :replaying)
                  (equal (fn-sf-successes crashed) (fn-sf-successes s))))))

(defthm fn-sf-admissible-image-facts
  (implies (fn-sf-crash-imagep s frontier records)
           (and (fn-sf-statep s)
                (fn-record-uint32p frontier)
                (fn-sf-record-listp records 0 0 frontier)
                (true-listp records)
                (implies (member-equal pair (fn-sf-successes s))
                         (fn-sf-record-has-pairp pair records)))))
```

plus helpers `fn-sf-image-choices-are-choices`,
`fn-sf-crash-imagep-implies-state`, `fn-sf-state-image-components-typed`.
Lesson: never enable `fn-sf-statep` with `fn-sf-phasep` enabled on a variable
state; the 17-way `member-equal` disjunction splits into hundreds of subgoals.

### 2.3 `books/store-files-traces.lisp` (certified)

Event syntax and dispatcher adjusted to the new arities (`:refuse-reservation
txid`, `:abort-completion seq txid`, `:core-completion seq txid`); footprint
lemmas renamed nothing; `:lose-success` kept in the kernel vocabulary and
marked. All trace theorems re-certified unchanged in statement.

### 2.4 `tests/acl2/store-files-tests.lisp` (certified)

Includes `std/testing/must-fail`. Witnesses for every crash point and
`must-fail` teeth, one per hypothesis, for K1-K3 above (phase dropped,
choice dropped, state dropped with malformed tuples
`*sf-bogus-data-durable*`, `*sf-bogus-attempted*`,
`*sf-bogus-record-durable*`, `*sf-bogus-record-attempted*`); admissible and
inadmissible images at each phase; the `core-durable` cut as a crash from
`:ready`.

### 2.5 `tests/acl2/store-files-traces-tests.lisp` (certified)

Second trace now dies in `:record-data-durable` (the `final-link` cut) and
recovers the present candidate.

### 2.6 `tests/acl2/store-files-exploration-tests.lisp` (certified)

Domain: groups 2, capacity 4, frontier <= 2, records <= 2; records (0,0),
(1,1) and the txid-gap (0,1); 35 events; `:lose-success` excluded. Asserted
result (computed by the test, printed to the log):

```text
SFE_BOUNDED_EXHAUSTIVE fuel=10000 max-frontier=2 max-records=2 events=35
states=240 applications=8337 transitions=1127 transition-pairs=524
transient-states=8
```

states = distinct reachable kernel states; applications = (state, event)
pairs retained including no-op applications (what the old 9,038 counted);
transitions = state-changing applications; transition-pairs = distinct
(source, destination) among transitions; transient-states = states in
`:aborting` or `:completed`. Also asserted: gap path (refuse 0, prepare gap,
publish, acknowledge (0 . 1), abort variant); crash `:new` reaches the
candidate frontier from `:frontier-data-durable`, `:frontier-attempted`,
`:fenced-frontier` and changes nothing from `:frontier-staged`/`:reserved`;
crash `:present` appends from `:record-data-durable`, `:record-attempted`,
`:fenced-record` and changes nothing from `:record-staged`, `:aborting`,
`:completing`, `:ready`; `:fault` absent; barrier counts 0-4.

### 2.7 `books/store-node.lisp`, `store-node-invariants.lisp` (certified)

`fn-sn-finish` calls `(fn-sf-core-completion files seq txid)`; comments mark
`fn-sn-file-step` (no `:core-completion` by design), `fn-sn-crash` (one
constructor of an admissible image; host never calls it), `fn-sn-fence-node`
/ `fn-sn-resolve-node` and their two theorems as unreachable-in-composition.
New:

```lisp
(defthm fn-sn-crash-files-are-kernel-crash
  (implies (and (fn-sn-statep s)
                (fn-sf-crash-choicep frontier-choice record-choice))
           (and (equal (fn-sn-files (fn-sn-crash s frontier-choice record-choice))
                       (fn-sf-crash (fn-sn-files s) frontier-choice record-choice))
                (equal (fn-sn-groups (fn-sn-crash s frontier-choice record-choice))
                       (fn-sn-groups s))
                (equal (fn-sn-capacity (fn-sn-crash s frontier-choice record-choice))
                       (fn-sn-capacity s)))))
```

### 2.8 `books/store-node-traces.lisp` (certified)

`fn-snt-crash-preserves-relation` re-certified with the extended crash points
(no hint change needed). New: `fn-snt-prepare-keeps-records`,
`fn-snt-io-records-prefix`, `fn-snt-finish-keeps-records`,
`fn-snt-crash-records-prefix`, `fn-snt-recover-keeps-records`,
`fn-snt-related-records-true-list`, `fn-snt-step-records-prefix`,
`fn-snt-mixed-trace-records-prefix`, and

```lisp
(defthm fn-snt-admissible-crash-image-is-recoverable
  (implies (and (fn-snt-relation s)
                (fn-sf-crash-imagep (fn-sn-files s) frontier records))
           (fn-sf-history-recoverablep (fn-sn-groups s) (fn-sn-capacity s)
                                       records frontier)))
```

### 2.9 `books/store-node-resolution.lisp`, `store-node-resolution-traces.lisp` (certified)

Arity updates; new `fn-snrt-refuse-keeps-records`,
`fn-snrt-known-abort-files-keep-records`, `fn-snrt-known-abort-keeps-records`,
`fn-snrt-step-records-prefix`, `fn-snrt-mixed-trace-records-prefix`.

### 2.10 Tests certified

`store-node-tests` (adds the `:record-data-durable` crash outcomes and the
`:record-staged` no-choice check), `store-node-traces-tests` (adds the
unobserved-link crash variant), `store-node-resolution-tests`,
`store-node-resolution-traces-tests` (unchanged, re-certified).

### 2.11 Specs and registries (done, `make check` passes)

`specs/store-refinement.md` (phase list, events 7/11/13/15, acknowledged-prefix
obligation restated, counts sentence replaced, `fn-sf-crash-imagep` and the
physical-assumption list), `specs/store-node.md` (marks, D5/D6 section under
"Observed physical image entry"), `specs/store-fault-matrix.md` (new section
"Process-death cuts and their model crash points" with the six-cut table),
`specs/store-exploration.md` (rewritten with the new counts and definitions),
`planning/proofs.json` (events: removed `fn-sf-lost-core-completion-fences`,
added the new keystones), `planning/requirements.json` (one implementation
note). `python3 tools/check_scaffold.py`: `Scaffold OK: 76 Markdown files, 49
requirements, 18 proof targets, 18 scenario specifications.`

## 3. IN PROGRESS: `books/store-observed.lisp` and its two test books

**Resolved 2026-09-19 (successor):** the recommended split was adopted.
`books/store-observed.lisp` includes `store-node-invariants` again (minimal-theory
guard hint kept); the D5/D6 section moved to `books/store-observed-traces.lisp`
(includes `store-observed` and `store-node-resolution-traces`), with one new
helper `fn-snt-relation-implies-observed-configuration` that the D5 keystone
now uses in place of opening `fn-sn-statep`. Tests split likewise into
`tests/acl2/store-observed-traces-tests.lisp`. All four certified
(`certify-20260919T071830Z-49794`, `certify-20260919T072017Z-51384`,
`certify-20260919T072031Z-51638`, `certify-20260919T072032Z-51648`).
PRF-007 now cites `fn-sf-crash-realizes-every-admissible-image`,
`fn-sn-open-observed-success-has-live-history-relation`,
`fn-sn-acknowledged-record-survives-observed-reopen`; `make check` is green.
The section below is kept as the record of the failure.

State: the book is fully written (D6, D5 and the re-rooted theorems, listed
below) but does NOT yet certify. It now includes
`store-node-resolution-traces` instead of `store-node-invariants`.

What happened, in order:

1. Run `certify-20260919T053546Z-96878` was killed (shell reset) while
   certifying this book; no log.
2. Run `certify-20260919T060444Z-15542` (`FN_ACL2_TIMEOUT_SECONDS=1800`) was
   also killed by a shell reset after ~10 minutes; directory contains only
   `books--store-observed.certify.lsp` and `version.log`.
3. Streamed debug session (`build/observed-debug.lsp`, log
   `build/observed-debug.log`; recipe: `(include-book
   "books/store-node-resolution-traces") (ld "books/store-observed.lisp"
   :ld-pre-eval-print t :ld-error-action :return)` fed to a detached `acl2`
   via `subprocess.Popen(start_new_session=True)`) showed that the **old**
   `(verify-guards fn-sn-observed-rebarrier)` stalled for more than nine
   minutes with the trace books in scope (its mbe guard conjecture
   `zp` versus `not posp` now sees many more rewrite rules). Fix applied and
   verified in the next session (0.00 s):

   ```lisp
   (verify-guards fn-sn-observed-rebarrier
     :hints (("Goal" :in-theory (union-theories '(zp posp)
                                                (theory 'minimal-theory)))))
   ```

4. The next streamed session then FAILED at the **old, textually unchanged**
   theorem `fn-sn-observed-one-ok-barrier`. Exact log text:

   ```text
   Form:  ( DEFTHM FN-SN-OBSERVED-ONE-OK-BARRIER ...)
   Rules: ((:DEFINITION FN-SF-BARRIERS) (:DEFINITION FN-SF-PHASE)
           (:DEFINITION FN-SN-FILES) (:DEFINITION NATP) (:DEFINITION NOT))
   Hint-events: ((:USE FN-SN-IO-PRESERVES-STATE)
                 (:USE FN-SN-STATEP-IMPLIES-FILES-STATEP))
   Warnings:  Use, Subsume, Free and Non-rec
   Time:  19.29 seconds (prove: 0.00, print: 0.09, other: 19.29)
   Prover steps counted:  334
   *** Note: No checkpoints to print. ***
   ACL2 Error [Failure] in ( DEFTHM FN-SN-OBSERVED-ONE-OK-BARRIER ...)
   ```

   The proof output shows only `Goal'` then `Goal''` and then the failure,
   with the time in "other", not "prove". In the baseline (old include of
   `store-node-invariants`) this theorem certified; the whole old book took
   72.81 s. Cause not yet identified; it is an interaction between the old
   hint (`:in-theory (e/d (fn-sn-io fn-sn-file-step fn-sf-recovery-barrier
   fn-sn-update fn-sn-make fn-sf-make) (fn-sn-statep fn-sf-statep))`) and the
   rules exported by `store-node-traces` / `store-node-resolution-traces`
   (candidates: `fn-snt-unknown-io-is-no-op`, `fn-snt-io-preserves-relation`,
   `fn-snt-typed-store-components`, the `fn-snt-*-records-*` rules I added,
   `fn-snrt-*`). "other" time with no checkpoints suggests a hint or
   forward-chaining pathology rather than a proof search.
5. A second full-output session (`build/observed-debug2.lsp` /
   `build/observed-head.lisp`) failed immediately because the head file was
   written under `build/` so its relative `(include-book
   "store-node-resolution-traces")` could not resolve. No information gained.
   No ACL2 process of this lane is running now.

**Recommended path for the successor (not started, my preference):** do not
re-prove the old observed theorems in the heavier theory. Revert
`books/store-observed.lisp` to include `store-node-invariants` again (keep the
minimal-theory guard hint; it is harmless), move the new section
("The process root establishes the live-history relation (D6)" through the
end of the file) into a NEW book `books/store-observed-traces.lisp` that
includes both `store-observed` and `store-node-resolution-traces`, add it to
`Makefile` `ACL2_BOOKS` and `tools/certify_books.py` `DEFAULT_BOOKS` right
after `books/store-observed` (before `tests/acl2/store-observed-tests`), and
make `tests/acl2/store-observed-tests.lisp` include the new book. The host
(`host/store-node-host.lisp`) keeps including `store-observed`. Alternative:
keep one book and give the six old theorems `:in-theory` hints that disable
the trace-book rules; slower to debug under the current load. Register any
new book name; no new function prefix is needed (`fn-sn-`, `fn-snrt-`).

The new theorems, verbatim (unproved by ACL2 as of this dump, hints written):

```lisp
(defthm fn-sn-open-observed-success-configuration
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (and (equal (fn-sn-groups (fn-sn-open-state
                         (fn-sn-open-observed groups capacity frontier records)))
                       groups)
                (equal (fn-sn-capacity (fn-sn-open-state
                         (fn-sn-open-observed groups capacity frontier records)))
                       capacity))))

(defthm fn-sn-open-observed-success-implies-recoverable-history
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (fn-sf-history-recoverablep groups capacity records frontier)))

;; D6 keystone
(defthm fn-sn-open-observed-success-has-live-history-relation
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (fn-snt-relation
            (fn-sn-open-state
             (fn-sn-open-observed groups capacity frontier records)))))

(defthm fn-sn-recover-of-recoverable-replaying-is-recovering
  (implies (and (fn-sn-statep st)
                (equal (fn-sf-phase (fn-sn-files st)) :replaying)
                (fn-sf-history-recoverablep (fn-sn-groups st) (fn-sn-capacity st)
                                            (fn-sf-records (fn-sn-files st))
                                            (fn-sf-frontier (fn-sn-files st))))
           (equal (fn-sf-phase (fn-sn-files (fn-sn-recover st))) :recovering)))

(defthm fn-sn-open-observed-succeeds-on-recoverable-image
  (implies (and (fn-sn-observed-configurationp groups capacity)
                (fn-sn-observed-historyp frontier records)
                (fn-sf-history-recoverablep groups capacity records frontier))
           (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))))

;; D5 keystone: A-DURABILITY (and A-WRITE-ISOLATION) as the hypothesis
;; fn-sf-crash-imagep, not as the constructor.
(defthm fn-sn-acknowledged-record-survives-observed-reopen
  (implies (and (fn-snt-relation s)
                (fn-sf-crash-imagep (fn-sn-files s) frontier records)
                (member-equal pair (fn-sf-successes (fn-sn-files s))))
           (and (fn-sn-open-okp
                 (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                      frontier records))
                (fn-sf-record-has-pairp
                 pair
                 (fn-sf-records
                  (fn-sn-files
                   (fn-sn-open-state
                    (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                         frontier records))))))))

(defthm fn-snrt-observed-open-mixed-trace-preserves-live-history-relation
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (fn-snt-relation
            (fn-snrt-run
             (fn-sn-open-state (fn-sn-open-observed groups capacity frontier records))
             events))))

(defthm fn-snrt-observed-open-ready-node-is-exact-replay
  (let ((final (fn-snrt-run
                (fn-sn-open-state (fn-sn-open-observed groups capacity frontier records))
                events)))
    (implies (and (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
                  (member-equal (fn-sf-phase (fn-sn-files final))
                                '(:ready :recovering :fenced-recovery)))
             (equal (fn-sn-node final)
                    (fn-sf-replay-node (fn-sn-groups final) (fn-sn-capacity final)
                                       (fn-sf-records (fn-sn-files final))
                                       (fn-sf-frontier (fn-sn-files final)))))))

(defthm fn-snrt-acknowledged-record-retained-across-observed-reopen
  (let ((final (fn-snrt-run
                (fn-sn-open-state
                 (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                      frontier records))
                events)))
    (implies (and (fn-snt-relation s)
                  (fn-sf-crash-imagep (fn-sn-files s) frontier records)
                  (member-equal pair (fn-sf-successes (fn-sn-files s))))
             (fn-sf-record-has-pairp pair (fn-sf-records (fn-sn-files final))))))
```

Proof plans are encoded in the hints in the file. D5 chains
`fn-snt-relation-implies-structural-state`,
`fn-snt-admissible-crash-image-is-recoverable` (certified),
`fn-sf-admissible-image-facts` (certified),
`fn-sn-open-observed-succeeds-on-recoverable-image`,
`fn-sn-open-observed-success-exact-history` (old, certified in baseline).
Expect to tune hints: the risky ones are
`fn-sn-open-observed-success-implies-recoverable-history` (opens
`fn-sn-open-observed`, `fn-sn-recover`, `fn-sf-recover` with the recognizers
disabled; relies on the phase case split) and the D5 theorem (opens
`fn-sn-statep` to get `fn-sn-observed-configurationp`; keep `fn-sf-statep`
and `fn-node-statep` disabled).

Host line inhabiting the premises: `host/store-node-host.lisp:27`
(`fn-sn-open-observed *fn-store-groups* *fn-store-capacity* frontier records`
inside `fn-store-sn-recover`), called from `tools/run_store.py:568`
(`acl2.recover(records, self.frontier)`) on every process start.

`tests/acl2/store-observed-tests.lisp` (written, not certified): D6 witness
(two-record gap image, frontier 4; refuse 4, prepare/abort txid 5, publish
and finish txid 6, uncertain link txid 7, crash `:old :present`, recover,
barriers; relation asserted at every stage and node = replay of four records
at 8), D5 witness (die in `:record-data-durable` after acknowledging
`(2 . 6)`; images `*fn-so-image-absent*` and `*fn-so-image-present*` both
admissible and both reopen with the pair present; `successes` nil after
reopen asserted honestly; `core-durable` cut), teeth (`must-fail`):
`*fn-so-reopen-rolled-back*` (image hypothesis dropped: reopen succeeds, pair
absent), `(9 . 9)` (membership dropped), `*fn-so-unrelated*` (relation
weakened to `fn-sn-statep` with an unreplayable `"fn.other"` record: reopen
refuses with `(:error :replay)`), and the refused-open tooth for D6. Also
asserts every refusal code is reachable. Depends on `fn-sn-committed-recordp`
(store-node-invariants) and `fn-snrt-run` (resolution-traces).

`tests/acl2/store-node-guards-tests.lisp`: unchanged; not re-certified since
the chain died before it (it depends on `store-observed`).

## 4. NOT STARTED

- Full gate `FN_ACL2_TIMEOUT_SECONDS=1800 make certify` after the changes
  (needs store-observed green first). Run detached:
  `setsid nohup env FN_ACL2_TIMEOUT_SECONDS=1800 make certify > build/certify-gate.log 2>&1 < /dev/null &`
  (or the harness background option); never a bare `&`.
- `HANDOFF.md` as specified by the packet: a complete draft is at
  `/private/tmp/claude-501/-Users-ember-dev-fn/b3f4abb5-8512-4271-9b78-513aa6e0845f/scratchpad/HANDOFF-draft.md`
  (scratchpad, may not survive); placeholders `__HEAD__` and `__COMMANDS__`.
  Its content is reproduced in this dump except the command tails.
- Recording the gate's evidence directory and digests in
  `specs/store-exploration.md` ("Recorded run" section points at the manifest).

## 5. Design decisions and why (do not redo)

1. **D4 crash-phase design: extend the visibility predicates, do not add
   phases.** The alternative, new phases `:frontier-replace-issued` /
   `:record-link-issued` entered by a new host observation before each syscall,
   would model the cut only after `tools/run_store.py` is changed (not owned)
   and would leave today's host cuts unmodeled until then. Extending
   `fn-sf-frontier-new-visiblep` / `fn-sf-record-present-visiblep` to the
   data-durable phases models the union of "syscall not yet issued" (old /
   absent) and "issued, unobserved" (old-or-new / absent-or-present) as a
   genuine choice, which is exactly the set of images the platform can leave,
   with no host change. Cost: in `:record-data-durable` the model cannot tell
   "link not issued" (where `fn-sn-known-abort` is legitimate) from "issued,
   unobserved"; the known-abort classification is a host claim under A-HOST
   (the `StoreError` branch before `publication_attempted = True`). This is
   stated in the specs and the handoff draft.
2. **A-DURABILITY as hypothesis:** `fn-sf-crash-imagep` is the admissible-image
   predicate; `fn-sf-crash` is proved to realize every admissible image and to
   produce only admissible ones. The reopen theorems quantify over an arbitrary
   `(frontier, records)` satisfying the predicate, so the guarantee no longer
   comes from the constructor's shape. C1-15 can wrap the predicate in an
   `encapsulate` later.
3. **D5 choice: option (b), restate over records.** Option (a) is impossible
   without an acknowledgement anchor: on disk an unacknowledged tail (present
   image after the `final-link` cut) is indistinguishable from an acknowledged
   record, so any reconstruction of `successes` from the image would either
   over-claim or be `nil`. The reopened state keeps `successes = nil`
   honestly; the theorem that carries A-DURABILITY as a hypothesis is
   `fn-sn-acknowledged-record-survives-observed-reopen` (and its trace
   extension). The `*fn-so-reopen-rolled-back*` tooth documents that the
   reopen entry cannot detect whole-store rollback: that is the freshness gap
   already in `specs/store-refinement.md`.
4. **D6 placement:** `store-observed` includes `store-node-resolution-traces`
   (Makefile order already puts resolution-traces before observed, so no
   reordering). This is what broke the old observed theorems (section 3); see
   the recommended split there.
5. **Unreachable branches: remove the dead result values and phases, mark the
   functions.** `fn-sf-lose-success`, `fn-sn-fence-node`, `fn-sn-resolve-node`
   could not be deleted because six unowned books
   (`books/bp-receiver-{invariants,context-,journal-,store-,retention-,trace-}invariants.lisp`,
   lines 151-153 and 193-194) list every `fn-sf-*`/`fn-sn-*` function in an
   `in-theory (disable ...)`, and ACL2 rejects a theory naming a non-existent
   function. Arity changes are fine for those lists (verified: they only name
   symbols). `:completed` and `:aborting` are kept as transient phases because
   they are the intermediate states of one composed host call, not dead
   branches.
6. **Exploration:** `:lose-success` excluded (dead in composition); the gap
   record is (0,1); counts distinguish applications from transitions because
   the old figure counted no-op self-loops as edges.
7. **Teeth style:** `must-fail` around a ground `thm` instantiated at a concrete
   witness with one hypothesis dropped (fast: ground evaluation), plus negated
   `assert-event`s for image admissibility. General false `thm`s were avoided
   because their failure time is unbounded.
8. **Records-prefix through composed traces** was added at the sn level
   (`fn-snt-*-records-*`, `fn-snrt-*-records-*`) rather than reusing the sf
   trace theorem, because the composed dispatchers do not go through
   `fn-sf-dispatch`.

## 6. Gate commands and last results

- Baseline `make certify` at `0bd0b5c` (`build/certify-baseline.log`, evidence
  `build/acl2/certify-20260919T033221Z-68956`): `status: failed`; only
  `books/article-properties` timed out at 600 s under ten-lane load, and its
  six dependents (`article-work-*`, `article-public-*`, `article-work-tests`)
  lacked its certificate; 106/113 roots certified, sources unchanged, runner
  unchanged. Nothing in this lane's chain includes the article books.
- Owned-root runs: see section 2 table; all owned roots except
  `store-observed`, `store-observed-tests`, `store-node-guards-tests` are green
  on the current sources.
- `python3 tools/check_scaffold.py`: passed (76 Markdown files, 49
  requirements, 18 proof targets, 18 scenarios).
- Full post-change `make certify`: not run.

## 7. Known defects and gaps

- `books/store-observed.lisp` does not certify (section 3).
- Whole-store rollback is undetectable at the reopen entry (freshness anchor
  gap, pre-existing).
- Host known-abort/refusal classifications are A-HOST claims (see 5.1).
- Physical assumptions remain physical: torn writes in a staged file that
  `fsync` reported durable, non-atomic rename/link, a directory barrier that
  did not retain the change, the APFS drive cache (`F_FULLFSYNC`, review D12,
  host lane).
- `planning/assurance-closure.md:83`, `planning/now.md:88` and
  `tests/evidence/2026-09-18-assurance.md:22` still quote 211/9,038 (shared or
  historical; left for the integrator).
- `books/bp-receiver-*.lisp` disable lists still name the three marked
  functions (fine as long as they exist).

## 8. Proposals for unowned files

- No host observation is needed for D4/D5/D6.
- To delete `fn-sf-lose-success`, `fn-sn-fence-node`, `fn-sn-resolve-node`
  outright: remove those three names from the disable lists at
  `books/bp-receiver-invariants.lisp:151-152,193`,
  `books/bp-receiver-context-invariants.lisp:151-152,193`,
  `books/bp-receiver-journal-invariants.lisp:151-152,193`,
  `books/bp-receiver-store-invariants.lisp:151-152,193`,
  `books/bp-receiver-retention-invariants.lisp:151-152,193`,
  `books/bp-receiver-trace-invariants.lisp:152-153,194`; then delete the
  definitions, their theorems, and the two lines in
  `tests/acl2/store-node-tests.lisp` and six in
  `tests/acl2/store-node-guards-tests.lisp` that name them.
- If the split into `books/store-observed-traces.lisp` is adopted: add it to
  `Makefile` `ACL2_BOOKS` and `tools/certify_books.py` `DEFAULT_BOOKS` after
  `books/store-observed`.
- `tools/run_store.py:195` `acl2_symbol`: no change; the kernel still produces
  only `:FENCED-FRONTIER`, `:FENCED-RECORD`, `:FENCED-RECOVERY` among fenced
  words.

## 9. Dirty and untracked files at this dump

Modified (all committed in the WIP commit): `books/store-files.lisp`,
`books/store-files-invariants.lisp`, `books/store-files-traces.lisp`,
`books/store-node.lisp`, `books/store-node-invariants.lisp`,
`books/store-node-traces.lisp`, `books/store-node-resolution.lisp`,
`books/store-node-resolution-traces.lisp`, `books/store-observed.lisp`,
`tests/acl2/store-files-tests.lisp`, `tests/acl2/store-files-traces-tests.lisp`,
`tests/acl2/store-files-exploration-tests.lisp`,
`tests/acl2/store-node-tests.lisp`, `tests/acl2/store-node-traces-tests.lisp`,
`tests/acl2/store-observed-tests.lisp`, `specs/store-refinement.md`,
`specs/store-node.md`, `specs/store-fault-matrix.md`,
`specs/store-exploration.md`, `planning/proofs.json`,
`planning/requirements.json`.

Untracked: `LANEDUMP-crash-fidelity.md` (this file, committed). Everything
under `build/` is ignored (certification evidence, `certify-baseline.log`,
`certify-sn-chain-1.log`, `certify-sn-chain-2.log`, `observed-debug*.lsp/.log`,
`observed-head.lisp`). Scratchpad drafts outside the repo:
`/private/tmp/claude-501/-Users-ember-dev-fn/b3f4abb5-8512-4271-9b78-513aa6e0845f/scratchpad/{drafts,HANDOFF-draft.md}`.
