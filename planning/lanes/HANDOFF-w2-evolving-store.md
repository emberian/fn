# Handoff: lane w2/evolving-store (packet C1-04)

Work commit: `5006536` on `w2/evolving-store` (branched from `dev` at
`4af825a`); this handoff is the commit after it. Commits are unsigned
(1Password refused the signature while the lane ran unattended).

## Certification

Baseline `make certify` of the branch point: `build/acl2/certify-20260919T100330Z-84043`
(exit 0, all roots). Each new root certified alone afterwards, in order, with
`FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py <root>`:

| Root | Status | Evidence |
| --- | --- | --- |
| `books/bp-receiver-evolving-history-invariants` (34 theorems) | certified | `build/acl2/certify-20260919T104311Z-94320` |
| `books/bp-receiver-evolving-node-invariants` (31 theorems) | certified | `build/acl2/certify-20260919T122220Z-12357` |
| `books/bp-receiver-evolving-store-invariants` (28 theorems) | certified | `build/acl2/certify-20260919T122908Z-13488` |
| `tests/acl2/bp-receiver-evolving-tests` (70 `assert-event`, 14 `must-fail`) | certified | `build/acl2/certify-20260919T123449Z-14595` |

No `skip-proofs`, `defaxiom` or trust tag. `python3 tools/ledger.py --write`
regenerated `planning/ledger.*` and the `proofs.json` event arrays from the
curated additions to `planning/proof-events.json` (PRF-001, PRF-007,
PRF-012); `make check` is green and none of the cited events is SUSPECT.
The four roots are appended to `ACL2_BOOKS` after
`tests/acl2/bp-receiver-teeth-tests`; a second full `make certify` was not
run (integrator gates remotely). All existing `books/bp-receiver-*` theorems,
including `fn-bprv-replayed-receipt-is-grounded`, are untouched.

## Keystones (verbatim)

Relation (`bp-receiver-evolving-history-invariants`):

```lisp
(defun fn-bprv-history-relationalp (history st)
  (and (fn-bprv-contexts-groundedp (fn-bpr-state-config st) (fn-bpr-state-contexts st) history)
       (fn-bprv-entries-linkedp (fn-bpr-state-config st) (fn-bpr-state-contexts st) (fn-bpr-state-receipts st))
       (fn-bprv-pending-linkedp (fn-bpr-state-config st) (fn-bpr-state-contexts st)
                                (fn-bpr-state-receipts st) (fn-bpr-state-pending st))))
(defun fn-bprv-evolving-invariantp (store st journal)
  (and (fn-bpr-statep st)
       (fn-bprv-history-relationalp (fn-bprv-history store) st)
       (fn-bprv-entries-decidedp (fn-bpr-state-receipts st) journal)))
```

`fn-bprv-context-groundedp` is `consp` of `fn-bprv-find-grounding-record`,
which searches the history for a record satisfying `fn-bprv-record-grounds`:
the conjuncts of `fn-bpr-request-acceptablep` with the Store conjunct replaced
by history membership. No phase, no node.

```lisp
(defthm fn-bprv-acceptable-implies-grounded
  (implies (fn-bpr-request-acceptablep store config record request authorized)
           (fn-bprv-context-groundedp config (fn-bpr-context-from-request record request)
                                      (fn-bprv-history store))))
(defthm fn-bprv-apply-record-preserves-evolving-invariant
  (implies (and (fn-bprv-evolving-invariantp store st journal) (member-equal r journal))
           (fn-bprv-evolving-invariantp store (cadr (fn-bprr-apply-record st store r)) journal)))
(defthm fn-bprv-successful-replay-has-evolving-invariant
  (implies (and (car (fn-bprr-replay store records))
                (fn-sf-prefixp (fn-bprv-history store) (fn-bprv-history later)))
           (fn-bprv-evolving-invariantp later (cadr (fn-bprr-replay store records)) records)))
(defthm fn-bprv-evolving-output-is-history-grounded   ; :rule-classes nil
  (implies (and (fn-bprv-evolving-invariantp store st journal) (fn-bpr-receipt-adu st request))
           (let* ((context (fn-bpr-find-context (fn-bpa-request-work-id request) (fn-bpr-state-contexts st)))
                  (entry (fn-bpr-find-receipt (fn-bpr-context-work-id context) (fn-bpr-state-receipts st)))
                  (record (fn-bprv-find-grounding-record (fn-bpr-state-config st) context (fn-bprv-history store))))
             (and (consp context) (equal request (fn-bpr-context-request context))
                  (fn-record-p record) (member-equal record (fn-bprv-history store))
                  (equal context (fn-bpr-context-from-request record request))
                  (equal (fn-bpa-request-article request) (fn-record-payload record))
                  (equal (fn-bpa-request-subject request) (fn-record-content-subject record))
                  (member-equal entry (fn-bpr-state-receipts st))
                  (fn-bprv-entry-decidedp entry journal)
                  (equal (fn-bpr-receipt-entry-receipt entry)
                         (fn-bpr-receipt-for context (fn-bpr-state-config st)
                                             (fn-bpa-receipt-id (fn-bpr-receipt-entry-receipt entry))))
                  (equal (fn-bpr-receipt-adu st request) (fn-bpa-encode (fn-bpr-receipt-entry-receipt entry)))))))
```

Node (`bp-receiver-evolving-node-invariants`), the one piece of new proof
work; the one-step lemma is `fn-bprv-apply-record-installs-record`
(hypotheses: `fn-node-statep node`, `fn-bprv-node-idlep node`,
`fn-record-p record`, `consp (fn-replay-apply-record node record)`), the
multi-step lemma `fn-bprv-apply-record-keeps-committed`, the loop lemma
`fn-bprv-replay-loop-installs-every-record`:

```lisp
(defthm fn-bprv-history-record-is-node-committed-when-idle
  (implies (and (fn-snt-relation store)
                (member-equal (fn-bprv-phase store) '(:ready :recovering :fenced-recovery))
                (member-equal record (fn-bprv-history store)))
           (fn-bpi-node-record-committedp (fn-sn-node store) record)))
(defthm fn-bprv-evolving-output-is-node-grounded-when-idle
  (implies (and (fn-bprv-evolving-invariantp store st journal) (fn-snt-relation store)
                (member-equal (fn-bprv-phase store) '(:ready :recovering :fenced-recovery))
                (fn-bpr-receipt-adu st request))
           (fn-bpi-node-record-committedp (fn-sn-node store)
             (fn-bprv-find-grounding-record (fn-bpr-state-config st)
               (fn-bpr-find-context (fn-bpa-request-work-id request) (fn-bpr-state-contexts st))
               (fn-bprv-history store)))))
(defthm fn-bprv-acceptable-at-ready-extension
  (implies (and (fn-bpr-request-acceptablep s1 config record request authorized)
                (fn-sf-prefixp (fn-bprv-history s1) (fn-bprv-history s2))
                (fn-snt-relation s2) (equal (fn-bprv-phase s2) :ready))
           (fn-bpr-request-acceptablep s2 config record request authorized)))
```

Store evolution and the live trace (`bp-receiver-evolving-store-invariants`);
`fn-bprv-system-invariantp` is `fn-snt-relation` of the Store and
`fn-bprv-evolving-invariantp`; `fn-bprv-extendsp` is `fn-sf-prefixp` of the
histories; a live state is `(store st journal)`:

```lisp
(defthm fn-bprv-store-step-preserves-evolving-invariant
  (implies (and (fn-snt-relation store) (fn-bprv-evolving-invariantp store st journal))
           (fn-bprv-evolving-invariantp (fn-snrt-step store event) st journal)))
(defthm fn-bprv-system-run-preserves-invariant
  (implies (and (fn-bprv-system-invariantp store st journal)
                (fn-bprv-system-events-journaledp events journal))
           (let ((final (fn-bprv-system-run store st events)))
             (fn-bprv-system-invariantp (car final) (cadr final) journal))))
(defthm fn-bprv-evolving-invariant-survives-observed-reopen
  (implies (and (fn-bprv-system-invariantp store st journal)
                (fn-sf-crash-imagep (fn-sn-files store) frontier records))
           (let ((opened (fn-sn-open-observed (fn-sn-groups store) (fn-sn-capacity store) frontier records)))
             (and (fn-sn-open-okp opened)
                  (fn-bprv-system-invariantp (fn-sn-open-state opened) st journal)))))
(defun fn-bpr-live-step (live event)
  (let ((store (car live)) (st (cadr live)) (journal (caddr live)))
    (case (car event)
      (:store (list (fn-snrt-step store (cadr event)) st journal))
      (:apply (let ((answer (fn-bprr-apply-record st store (cadr event))))
                (if (car answer)
                    (list store (cadr answer) (append journal (list (cadr event))))
                  (list store st journal))))
      (otherwise (list store st journal)))))
(defthm fn-bprv-apply-record-agrees-at-ready-extension
  (implies (and (car (fn-bprr-apply-record st s1 r))
                (fn-sf-prefixp (fn-bprv-history s1) (fn-bprv-history s2))
                (fn-snt-relation s2) (equal (fn-bprv-phase s2) :ready))
           (equal (fn-bprr-apply-record st s2 r) (fn-bprr-apply-record st s1 r))))
(defthm fn-bpr-live-state-is-replay-of-journal
  (let ((final (fn-bpr-live-run live events)))
    (implies (and (fn-snt-relation (car live))
                  (equal (fn-bprr-replay probe (caddr live)) (list t (cadr live)))
                  (fn-snt-relation probe) (equal (fn-bprv-phase probe) :ready)
                  (fn-bprv-extendsp (car final) probe))
             (equal (fn-bprr-replay probe (caddr final)) (list t (cadr final))))))
(defthm fn-bpr-live-receipt-regenerated-after-restart
  (let* ((final (fn-bpr-live-run live events))
         (opened (fn-sn-open-observed (fn-sn-groups (car final)) (fn-sn-capacity (car final)) frontier records))
         (probe (fn-snrt-run (fn-sn-open-state opened) recovery-events))
         (installed (fn-bpr-live-install probe (caddr final))))
    (implies (and (fn-snt-relation (car live))
                  (equal (fn-bprr-replay (car live) (caddr live)) (list t (cadr live)))
                  (fn-sf-crash-imagep (fn-sn-files (car final)) frontier records)
                  (equal (fn-bprv-phase probe) :ready))
             (and (fn-sn-open-okp opened)
                  (equal (cadr installed) (cadr final))
                  (equal (fn-bpr-receipt-adu (cadr installed) request)
                         (fn-bpr-receipt-adu (cadr final) request))))))
```

Subject and host lines: `fn-bprr-replay` is `fn-bprj-install`
(`host/bp-receipt-journal-host.lisp:12`), `fn-bprr-apply-record` is
`fn-bprj-preflight`/`fn-bprj-apply` (lines 18, 22), `fn-bpr-receipt-adu` is
`fn-bprj-receipt-adu` (line 38); the Store events are the ingress at
`tools/run_bp_receive.py:210-217`, the reopen is `host/store-node-host.lisp:27`;
the journal holds exactly the records `fn-bprj-apply` accepted because
`tools/receipt_journal.py:56-79` preflights, writes, then applies against the
same Store and state (A-HOST).

## Witness and teeth (`tests/acl2/bp-receiver-evolving-tests.lisp`)

Witness: `*bpr-store*` (real `fn-sn-initial`/`fn-sn-io`/`fn-sn-prepare`/
`fn-sn-finish` Store holding article 1); the live trace accepts the request,
runs the four reservation steps, prepares article 2 (`<receipt-2@example>`,
its own obligation identity), applies the receipt intent while
`:record-staged`, publishes, applies the committed decision while
`:completing`, finishes. `fn-bprv-system-invariantp` holds at all 13 live
states; the retired `fn-bprv-invariantp` fails at exactly the 10 non-ready
states. The final Store is `:ready` with both records node-committed; the
journal is the four records; the receipt is `*bpr-receipt-adu*`. Crash image
= the final files' frontier and records; `fn-sn-open-observed` succeeds; five
barriers reach `:ready`; `fn-bpr-live-install` reproduces the live state and
the same receipt bytes. The kernel-crash variant (`fn-sn-crash`, `fn-sn-recover`,
five barriers) keeps the invariant through `:replaying` with the empty node.

Teeth (`must-fail`, one per hypothesis, conclusion stated in full):
grounded-context without a history record; monotone without prefix;
system-step without a journaled record; L19 without idle phase (the
`:completing` Store, record in history, node not committed), without
`fn-snt-relation` (ready files with an empty node), without membership; L20
without idle phase (`:replaying`: L18 holds, node conclusion false); live
replay without a ready probe, without history extension (a ready Store that
never held the record), without base agreement (state ahead of its journal);
the live Store relation refuted at `fn-bpr-live-step-extends-history` (an
untyped Store with an improper record list is not its own prefix; the top
theorem's conclusion is not refutable without it, stated in the book); reopen
without an admissible image; plus the two inherited teeth cases.

## Deviations from `specs/bp-evolving-store.md` (recorded in its proof-status section)

Store step is `fn-snrt-step` (adds refuse/known-abort); L1/L7 carry
`fn-snt-relation` (needed by the kernel's own prefix theorems; every process
holds it from D6); L22 takes `fn-sf-crash-imagep` (D5 form) and also
concludes the open succeeds; L19 lives in the receiver's node book and carries
`fn-bprv-node-idlep` through `fn-replay-loop`; the node-level proofs name
explicit theories (`union-theories` over `minimal-theory`) because the
inherited rule set of the trace books did not terminate on them (two 1800 s
timeouts before the restructure).

## Proposals (not done here; outside the lane's ownership)

- `planning/proof-events.json` is hand-curated; the three targets now cite
  the keystones above. If the integrator prefers a separate PRF target for
  the live-trace theorem, split PRF-012.
- `books/replay-invariants.lisp` could host `fn-bprv-replay-loop-installs-every-record`
  as `fn-replay-installs-every-record` (the design's name); it depends only on
  replay, node and acceptance books.
- The two D4 crash points remain the `fn-sf-crash-imagep` hypothesis; C1-14
  owns discharging it.
- `tools/run_bp_receive.py` line 139 initialises the journal before the
  Store's recovery barriers complete only if `open_live_bp_store` returns
  early; the proofs assume `fn-bprj-install` runs against a `:ready` Store
  (the live-trace probe). Worth a host assertion.
