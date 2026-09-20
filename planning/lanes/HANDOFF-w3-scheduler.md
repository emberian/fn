# HANDOFF — w3/scheduler (C2-06, the durable contact/retry scheduler)

Worktree `/Users/ember/dev/fn/build/lanes/w3-scheduler`, branch `w3/scheduler`,
branched from `dev` at `9321344`.

HEAD: see `git -C /Users/ember/dev/fn/build/lanes/w3-scheduler rev-parse HEAD`.
Commits: `a018394` (C2-06), the proof-style rewrite (`dad2f3c`..`b422d42`), and the
2026-09-20 proof lane (`79e5227` and after), which is what the table below reports.

## Per book: certified, or open (2026-09-20 proof lane)

Rebased onto `dev` at `c1c8ab1` (`git merge --no-edit dev`; the only conflicts
were `planning/ledger.json` and `planning/ledger.md`, resolved by taking dev's
and regenerating). Books rewritten to `docs/proof-style.md`. Every keystone
STATEMENT is unchanged.

| Artifact | Status | Evidence |
| --- | --- | --- |
| `books/scheduler.lisp` | CERTIFIED | `build/acl2/certify-20260919T235031Z-17711` |
| `books/scheduler-invariants.lisp` | CERTIFIED (`certify-book` form 3.76 s wall; no form over 1.1 s) | `build/acl2/certify-20260920T025038Z-16877` |
| `tests/acl2/scheduler-tests.lisp` | CERTIFIED (103 `assert-event`s pass; `certify-book` form 1.12 s wall) | `build/acl2/certify-20260920T025611Z-31803` |

All three roots are certified. Commit `3886f5a` is titled "Certify the rewritten
scheduler cluster"; that title is wrong and this table is the correction.

### The invariants book, failure by failure

Each failure was a fact the raw-list records used to supply by type reasoning
and an opaque record does not. In order, with the fix that closed it:

1. `fn-sched-statep-of-{pass-over,take}` — the enabled list recognizers opened
   `(fn-sched-string-listp (fn-sched-next-aged ...))` into `(stringp (car ...))`
   before the `-of-next-aged` rewrite could fire. Fix: name
   `fn-sched-string-listp` and `fn-sched-item-listp` in the hint's disable.
2. `fn-sched-statep-of-tick-step`, then `fn-sched-{step,trace}-preserves-state`
   — `fn-sched-statep` opened instead of the per-transition preservation
   lemmas applying. Fix: close `fn-sched-statep` in those three hints.
3. `fn-sched-expire-queue-preserves-queued` — `fn-sched-find` could not see
   through a marked item. Fix: `fn-sched-mark-expired-keeps-the-fields`.
4. `fn-sched-selection-is-the-promotion-head` — the head being eligible no
   longer gives `(consp (fn-sched-find head queue))`. Fix: cite
   `fn-sched-eligible-is-consp` at that instance.
5. `fn-sched-promotion-position-decreases` — three separate gaps, fixed by
   `fn-sched-member-of-append-left`,
   `fn-sched-aged-advance-consp-when-an-eligible-member-exists` and
   `fn-sched-selection-is-consp-when-the-promotion-queue-is-not-empty`.

### The proof lane (2026-09-20): what actually hung, and what was false

The runs `-94761` and `-7729` had already proved
`fn-sched-promotion-position-decreases` (0.10 s). The form that ran to the
1800 s limit was the next one, `fn-sched-promoted-work-is-selected-within-its-
position`. HEAD `b422d42` then swapped the keystone's `:use` of
`fn-sched-member-of-cdr-when-not-the-car` for a new lemma; that version fails in
0.02 s and was never run. Findings, in book order:

1. `fn-sched-step-preserves-state` / `-queued` took 359.9 s and 366.7 s: the
   `:transport` branch opens `fn-bp-step` (books/bp-workflow has no export
   theory) although the scheduler state there is `ss` itself. Closed by name:
   under 0.3 s each.
2. The keystone's `:use` list is the one that certified; the isolation lemma
   is deleted.
3. The hang: the induction needs `(< pos' (- n 1))` from `(< pos' pos)` and
   `(< pos n)`, and the keystone's `<` conjunct is a rewrite rule whose
   trigger never occurs in that goal; ACL2 pushed thirteen nested inductions.
   Accumulated persistence at 2M steps is the descent itself
   (`fn-sched-pos-is-natural` 905k frames, the run predicates' type
   prescriptions ~226k each, `nonnegative-integer-quotient` 142k), with
   `fn-sched-refused-submit-is-a-no-op`, `fn-wildmat-guard-items-p-true-listp`
   and an opened `fn-sched-selection` as the zero-useful fan. Cure:
   `fn-sched-promotion-position-decreases-linear` (`:linear`, proof
   vocabulary) and `:expand` of the three run predicates at N with their
   definitions closed.
4. **Statement change.** With the hang gone the base case is a counterexample:
   at `n = 1/2` every run predicate is `t` (`(zp (nfix 1/2))`), `(< 0 1/2)`
   holds and nothing is selected, so `fn-sched-promoted-work-is-selected-
   within-its-position` and `fn-sched-aging-bound` were false as stated, from
   `a018394` on. Both now bound the position by `(nfix n)`, the horizon the run
   predicates count. The witness is evaluated in the test book. This is a
   correction, not a weakening for a proof.
5. `fn-sched-passed-over-work-reaches-the-promotion-queue` needed
   `fn-sched-find-reaches-the-promotions` (cited at its instance) and
   `fn-sched-member-of-append-right`.
6. `fn-sched-conditional-progress-under-a-fairness`'s hint named the
   constrained `fn-assume-fairness-contact-index` in a theory (a hard error)
   and left `fn-assume-fairness-contact-index-is-finite` enabled, which
   rewrote the `:use`d `natp` fact to `t`.
7. The test book, once reachable: `*sched-decision*` and the two negative
   decision records carry their `:text` ids as octet lists (`fn-frame-textp`,
   books/frame-fields.lisp), so the two `not`-assertions now fail for the one
   named reason and not for the strings; and `*sched-promoted-wf-fenced*`
   prepared "work-small", which has an attempt in flight after the second tick,
   so `fn-bp-prepare-attempt` refused, the completion matched nothing and
   nothing was fenced. It now prepares the retryable "work-big" at the
   scheduler's next txid, and the `fn-sched-drive-okp` teeth are real.
| `host/scheduler-host.lisp` | `:program` mode, outside the proof boundary | — |
| `tools/scheduler.py`, `tests/test_scheduler.py` | PASS | 22 tests |

### What the rewrite changed

* **Opaque records.** Contact, config, item, state and result each have a
  `fn-sched-<rec>-shapep`, one `fn-sched-<field>-of-fn-sched-<rec>` per field,
  and the three forward-chaining shape facts. The `:definition` runes of the
  shape, the accessors and the constructor are withdrawn at the definition.
  The recognizers are written over the shape and the accessors, never over
  `car`/`len`. The three `fn-sched-*-fields-unfold` theorems are deleted.
* **Export theories.** `books/scheduler` ends with `fn-sched-vocabulary` and
  `fn-sched-codec-vocabulary`; `books/scheduler-invariants` with
  `fn-sched-invariants-vocabulary`. Only keystones, record lemmas and
  list-recursive vocabulary leave either book enabled.
* **Local re-enables named on the board.** `books/scheduler` opens
  `fn-clock-vocabulary` locally (board 2026-09-19 bp: clock's recognizers,
  readings and `fn-clock-expiry-decision` are withdrawn on include), and cites
  `fn-frame-decode-payload-octets` (withdrawn under
  `fn-frame-fields-vocabulary`) by `:use` instead of opening frame's grammar,
  per the time-anchor template. `books/scheduler-invariants` opens
  `fn-sched-vocabulary` and `fn-clock-vocabulary` locally.
* **Guard equalities are `:rule-classes nil`.**
  `fn-sched-decision-recordp-is-frame-values-okp` exists only to discharge the
  two FNSC guard obligations and is cited by `:use`.
* **Guards carry the invariant.** `fn-sched-next-aged`, `fn-sched-pass-over`
  and `fn-sched-take` take `(fn-sched-statep ss)`, discharged from the new
  forward-chaining `fn-sched-admissiblep-forward-statep`; no transition re-runs
  the recognizer.
* **Definitional repairs, no statement changed.** `(zp n)` became
  `(zp (nfix n))` and `(- n 1)` became `(- (nfix n) 1)` in the three run
  predicates (`zp` has `natp` for a guard, and these predicates are hypotheses
  of keystones that must not carry a `natp`); the four trace folds name
  `:measure (acl2-count events)`.
* **Teeth are concrete witnesses.** All fifteen general negated `must-fail`
  forms are gone, replaced by `assert-event` counterexamples on named reachable
  states (`*sched-teeth-forged*`, `*sched-promoted*`, `*sched-promoted-closed*`,
  `*sched-promoted-wf-fenced*`, `*sched-promoted-expired*`). Two hypotheses of
  `fn-sched-aging-bound` are recorded OPEN in the test book rather than faked:
  `(member-equal w (fn-sched-aged ss))` needs a work eligible across a run past
  the queue bound and still unselected, and `(fn-sched-aged-fitsp ss)` needs a
  promotion queue longer than the configured bound — which no transition builds,
  which is exactly the invariant `specs/scheduler.md` leaves to C3-03.

### The host passes Lisp strings to the decision codec (owner: host/scheduler-host.lisp)

`fn-frame-textp` (books/frame-fields.lisp) recognises `:text` as an octet list,
and the test book now supplies octets. The host does not:
`fn-sched-host-decision-octets` (`host/scheduler-host.lisp:82-85`) hands
`fn-sched-decision` the contact peer, a `stringp` by `fn-sched-contactp`, and the
`work-id`/`attempt-id` that `tools/scheduler.py` marshals as string literals
(`_lit`), so `fn-sched-decision-protected` answers `:bad` and `run_plan` raises
"ACL2 refused the decision record". The codec is the authority and is unchanged;
the owner of that file converts the three ids to octets at the site (the
bridge's `_octets`, or `fn-record-string-octets` in books/records.lisp) or the
contact record's peer becomes octets.

### Always-on TCP peers (specs/peering.md §3)

The outbound feed machine wants this scheduler's contact/tick model for TCP
peers, which are never out of contact. The interface already expresses that:
`fn-sched-contact` takes a window `[start, end]` in monotonic milliseconds and
`fn-sched-contact-holdsp` only tests containment, so an always-on peer is one
`(fn-sched-contact peer 0 <max fn-clock-timep>)` opened once and never closed;
every tick then finds the contact open and admissibility reduces to the retry
budget. What it would take to make that first-class rather than a wide window:
(1) a `:contact-open` variant, or a distinguished end value, that the spec names
as "always on", so a reader does not have to recognise the idiom, and one
theorem that an always-on contact makes `fn-sched-admissiblep` equivalent to the
retry-budget test alone; (2) a per-peer retry budget — today `fn-sched-retries`
is a single counter cleared by `fn-sched-open`/`fn-sched-close`, and an always-on
contact is never closed, so the budget never refills: the feed machine needs
either a refill observation or a budget indexed by peer; (3) the queue's
`peer` dimension — `fn-sched-item` carries no peer, and the decision record
takes the peer from the open contact, so one scheduler state serves one peer.
Points (2) and (3) are interface changes and belong to whoever owns
`specs/peering.md` §3; this lane did not make them.

## Verbatim keystones

### Safety — no fairness hypothesis anywhere below

```lisp
(defthm fn-sched-step-preserves-state
  (implies (fn-sched-statep ss)
           (fn-sched-statep (fn-sched-result-ss (fn-sched-step ss wf event)))))

(defthm fn-sched-trace-preserves-state
  (implies (fn-sched-statep ss)
           (fn-sched-statep (fn-sched-result-ss (fn-sched-trace ss wf events)))))

(defthm fn-sched-step-preserves-queued
  (implies (fn-sched-queuedp id (fn-sched-queue ss))
           (fn-sched-queuedp
            id (fn-sched-queue (fn-sched-result-ss (fn-sched-step ss wf event))))))

(defthm fn-sched-only-a-tick-or-a-relay-touches-the-workflow
  (implies (and (not (equal (fn-bp-nth 0 event) :tick))
                (not (equal (fn-bp-nth 0 event) :transport)))
           (equal (fn-sched-result-wf (fn-sched-step ss wf event)) wf)))

(defthm fn-sched-expiry-preserves-workflow
  (equal (fn-sched-result-wf
          (fn-sched-step ss wf (fn-sched-expiry-event id ct lt anchor obs)))
         wf))

(defthm fn-sched-contact-loss-preserves-queue-and-workflow
  (and (equal (fn-sched-result-wf (fn-sched-step ss wf (fn-sched-close-event)))
              wf)
       (equal (fn-sched-queue
               (fn-sched-result-ss (fn-sched-step ss wf (fn-sched-close-event))))
              (fn-sched-queue ss))
       (equal (fn-sched-aged
               (fn-sched-result-ss (fn-sched-step ss wf (fn-sched-close-event))))
              (fn-sched-aged ss))))
```

Every selected attempt is a durable intent. The workhorse is
`fn-bp-step-submit-requires-matching-durable-attempt-completion`
(`books/bp-workflow-invariants.lisp`); this lifts it to the scheduler's tick:

```lisp
(defthm fn-sched-selected-submit-is-a-workflow-submit
  (implies
   (member-equal e (fn-sched-result-effects
                    (fn-sched-tick-step ss wf attempt-id)))
   (let* ((sel (fn-sched-selection ss wf))
          (s1 (fn-bp-result-state
               (fn-bp-step wf (fn-bp-attempt-prepare-event
                               (fn-sched-next-tx ss) 0
                               (fn-sched-item-work-id sel) attempt-id))))
          (pending (fn-bp-state-pending s1)))
     (and (equal (fn-bp-nth 0 e) :submit)
          (fn-bp-statep s1)
          (not (fn-bp-state-fenced s1))
          (consp pending)
          (equal (fn-bp-pending-kind pending) :attempt)
          (equal (fn-bp-pending-txid pending) (fn-sched-next-tx ss))
          (equal (fn-bp-pending-generation pending) 0)
          (equal e
                 (list :submit
                       (fn-bp-work-id (fn-bp-pending-work pending))
                       (fn-bp-attempt-id
                        (fn-bp-work-attempt (fn-bp-pending-work pending)))
                       (fn-bp-attempt-generation
                        (fn-bp-work-attempt (fn-bp-pending-work pending)))
                       (fn-bp-config-local-eid (fn-bp-state-config s1))
                       (fn-bp-config-peer-eid (fn-bp-state-config s1))
                       (fn-bp-attempt-lifetime
                        (fn-bp-work-attempt (fn-bp-pending-work pending))))))))
  :rule-classes nil)
```

The theorem subject is the function the host calls. `fn-sched-tick-step` is the
composition of `fn-sched-host-selection`, the journal's durable attempt, and
`fn-sched-host-commit` (`tools/scheduler.py:run_plan`), and that equation is
itself a theorem:

```lisp
(defthm fn-sched-tick-step-is-select-drive-take
  (implies (and (fn-sched-admissiblep ss)
                (consp (fn-sched-selection ss wf))
                (fn-sched-drive-okp ss wf attempt-id))
           (and (equal (fn-sched-result-ss (fn-sched-tick-step ss wf attempt-id))
                       (fn-sched-with-decisions
                        (fn-sched-take ss wf (fn-sched-selection ss wf))
                        (fn-sched-record-decision
                         ss wf (fn-sched-selection ss wf) attempt-id)))
                (equal (fn-sched-result-wf (fn-sched-tick-step ss wf attempt-id))
                       (fn-bp-result-state
                        (fn-sched-drive-attempt
                         wf (fn-sched-next-tx ss)
                         (fn-sched-item-work-id (fn-sched-selection ss wf))
                         attempt-id))))))
```

A refused submit charges no retry and records no decision, which is what keeps
"retries bounded per contact" from being an accounting fiction:

```lisp
(defthm fn-sched-refused-submit-is-a-no-op
  (implies (and (consp (fn-sched-selection ss wf))
                (not (fn-sched-submit-for-idp
                      (fn-sched-item-work-id (fn-sched-selection ss wf))
                      (fn-bp-result-effects
                       (fn-sched-drive-attempt
                        wf (fn-sched-next-tx ss)
                        (fn-sched-item-work-id (fn-sched-selection ss wf))
                        attempt-id))))
                (fn-sched-admissiblep ss))
           (and (equal (fn-sched-result-ss (fn-sched-tick-step ss wf attempt-id)) ss)
                (equal (fn-sched-result-wf (fn-sched-tick-step ss wf attempt-id)) wf)
                (equal (fn-sched-result-effects
                        (fn-sched-tick-step ss wf attempt-id))
                       nil))))

(defthm fn-sched-retries-stay-within-the-contact-bound
  (implies (and (fn-sched-statep ss)
                (<= (fn-sched-retries ss)
                    (fn-sched-retry-bound (fn-sched-conf ss))))
           (<= (fn-sched-retries
                (fn-sched-result-ss (fn-sched-tick-step ss wf attempt-id)))
               (fn-sched-retry-bound (fn-sched-conf ss)))))
```

### The aging bound

```lisp
(defthm fn-sched-promotion-position-decreases
  (implies (and (fn-sched-admissiblep ss)
                (fn-sched-drive-okp ss wf attempt-id)
                (member-equal w (fn-sched-aged ss))
                (fn-sched-eligiblep (fn-sched-find w (fn-sched-queue ss)) wf)
                (not (fn-sched-submit-for-idp
                      w (fn-sched-result-effects
                         (fn-sched-tick-step ss wf attempt-id)))))
           (and (member-equal
                 w (fn-sched-aged
                    (fn-sched-result-ss (fn-sched-tick-step ss wf attempt-id))))
                (< (fn-sched-pos
                    w (fn-sched-aged
                       (fn-sched-result-ss
                        (fn-sched-tick-step ss wf attempt-id))))
                   (fn-sched-pos w (fn-sched-aged ss))))))

(defthm fn-sched-aging-bound
  (implies (and (fn-sched-aged-fitsp ss)
                (member-equal w (fn-sched-aged ss))
                (fn-sched-contact-runp ss wf n attempt-id)
                (fn-sched-eligible-runp ss wf n attempt-id w)
                (< (nfix (fn-sched-queue-bound (fn-sched-conf ss))) (nfix n)))
           (fn-sched-selected-withinp ss wf n attempt-id w)))
```

N is a function of configuration: `queue-bound` + 1. The stated horizon
`aging-limit` + `queue-bound` composes this with the single-tick promotion fact
`fn-sched-passed-over-work-reaches-the-promotion-queue`; the multi-tick
promotion induction is **not** done and is listed for C3-03 in
`specs/scheduler.md`.

### The starvation counterexample

The policy is written down, not described: `fn-sched-unfair-selection` /
`fn-sched-unfair-step` in `books/scheduler.lisp` are the scheduler with the
promotion queue removed and nothing else changed. The trace is exhibited in
`tests/acl2/scheduler-tests.lisp`:

```lisp
(defconst *sched-starvation-trace*
  (list (fn-sched-tick-event "attempt:0" *sched-obs*)
        (fn-sched-transport-event "work-small" "attempt:0" 0 :no-contact)
        (fn-sched-tick-event "attempt:1" *sched-obs*)
        (fn-sched-transport-event "work-small" "attempt:1" 1 :no-contact)
        (fn-sched-tick-event "attempt:2" *sched-obs*)))

(assert-event
 (not (fn-sched-unfair-submitted-in-trace *sched-ss* *sched-wf*
                                          *sched-starvation-trace* "work-big")))
(assert-event
 (fn-sched-unfair-submitted-in-trace *sched-ss* *sched-wf*
                                     *sched-starvation-trace* "work-small"))
(assert-event
 (fn-sched-submitted-in-trace *sched-ss* *sched-wf* *sched-starvation-trace*
                              "work-big"))
```

One trace, two policies: under priority-without-aging the 1000-octet article
receives no submit at all while the 10-octet one is submitted at every tick;
under the aging policy the same trace submits the large one on the third tick,
with the decision's reason recorded as `:aged` rather than `:priority`.

### Conditional progress, with A-FAIRNESS as its hypothesis

```lisp
(defthm fn-sched-conditional-progress-under-a-fairness
  (implies (and (fn-sched-aged-fitsp ss)
                (member-equal w (fn-sched-aged ss))
                (equal n (+ 1
                            (nfix (fn-sched-queue-bound (fn-sched-conf ss)))
                            (fn-assume-fairness-contact-index route schedule)))
                (fn-sched-contact-runp ss wf n attempt-id)
                (fn-sched-eligible-runp ss wf n attempt-id w))
           (fn-sched-selected-withinp ss wf n attempt-id w)))
```

`fn-assume-fairness-contact-index` is the constrained function in
`books/assumptions.lisp`; the constraint it contributes is
`fn-assume-fairness-contact-index-is-finite`, so the horizon is a natural
number of ticks. The other three hypotheses are capacity
(`fn-sched-contact-runp`: a contact is open, the retry budget is not spent, and
the durable store accepts the intent), the peer/receipt condition
(`fn-sched-eligible-runp`), and promotion. **A simulation is not the liveness
theorem** — `tests/test_scheduler.py` and the lab run one trace each; this
quantifies over all of them. No safety theorem above mentions A-FAIRNESS, per
FLR-004.

Teeth: `tests/acl2/scheduler-tests.lisp` has one `must-fail` per hypothesis of
each keystone — 13 in total, including one per hypothesis of
`fn-sched-promotion-position-decreases` and of `fn-sched-aging-bound`, and one
showing the conditional-progress conclusion fails when the horizon is the bare
fairness index rather than the index plus the configured bound.

## Python results

```
$ python3 -m unittest tests.test_scheduler
Ran 22 tests — OK
```

`tests.test_workflow_journal` and `tests.test_workflow_faults` were **not
run**: they start an ACL2 session through `tools/frame_bridge`, and the lane
was instructed to run no ACL2 while the baseline moved to the remote box. Run
them together with the three certifications:

```
python3 -m unittest tests.test_scheduler tests.test_workflow_journal \
                    tests.test_workflow_faults -v
```

`make check`: `Scaffold OK: 105 Markdown files, 50 requirements, 18 proof
targets, 18 scenario specifications. Ledger OK: cited events exist, are not
SUSPECT, and planning/ledger.md is current.` `python3 tools/ledger.py --write`
regenerated `planning/ledger.json`, `planning/ledger.md` and the
`planning/proofs.json` event arrays; it must be re-run after any book edit made
while fixing the certifications.

Smoke-tested without ACL2: `tests/bp-dtn7/fn_sender_lab.py` imports, its
`CONTACT_PLAN` (two windows `[10,20]` and `[5100,5200]`, one expiry at tick 2,
`queue-bound` 8, `aging-limit` 2, `retry-bound` 2) reads through
`tools/scheduler.plan_from`, and `MockBpa` serves the dtn7-rs inventory surface
that `tools/bpa_dtn7.BpaDtn7Client` speaks. The mock transmits no bundle and
has no peer; any report that uses it must say so.

## Proposals

1. **FNWF `:schedule` record.** `books/frame` should gain
   `(cons :schedule (list :nat :nat :text :text :text :nat (cons :enum
   '(:aged :priority)) :nat))` — `(generation tick peer work-id attempt-id
   attempt-generation reason passes)` — appended to `*fn-frame-workflow-kinds*`
   so existing kind codes stay stable, and `books/bp-workflow-records` should
   accept it as an audit record that is a no-op on workflow state. Until then
   `books/scheduler.lisp` models the shape and validates it against
   `fn-frame-values-okp`, and the host writes it as an FNSC frame under
   `<journal>/schedule/` with the same header, field encoding and A-CRYPTO
   trailer. This lane deliberately did not edit `books/frame.lisp` or
   `books/bp-workflow-records.lisp`, which other w3 lanes may hold.
2. **`fn-sched-aged-fitsp` should become a preserved invariant**, not a
   hypothesis. It needs the promotion queue's freedom from duplicates, which
   follows from the `agedp` flag but is not yet a theorem.
3. **The transport relay** (`:transport` in `fn-sched-step`) was added because
   without it no composed trace can re-arm a work whose attempt ended
   `:no-contact`, and therefore no starvation trace can be written at all. It
   decides nothing: `fn-sched-transport-relay-is-fn-bp-step` states that it is
   `fn-bp-step` with the scheduler state untouched and no effect.
4. **C3-03 inherits** the multi-tick promotion induction, delivery as opposed
   to selection (needs C2-07/C2-08 transitions), scheduler-level safety under
   clock jumps and outages, and a real BPv7 run of the contact plan against the
   pinned dtn7-rs build. `specs/scheduler.md` carries this list.
