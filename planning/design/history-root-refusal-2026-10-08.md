# A refused history-root refresh is named (lane s-heap2; MEM-010 family)

Statements only (2026-10-08); no proof work until Deputy S's GO. The reserve figure is N-MEM10 phase 2 (92e054a48) and is not touched here.

## The defect, measured
On the C3 image (0b4d3b183) at 25k, `fnn-owner-history-root-maintain` runs at startup (host/native/owner.lisp:1650) and after each
publication (owner.lisp:7513). Both times `fnn-owner-history-root-refresh` (host/native/history-root.lisp:101) returns
`(:refused :memory-budget-exhausted)`: `fn-owner-hroot-begin` (host/history-root-host.lisp:51) asks `fn-owner-hroot-resize` for
`4096 + (fn-hroot-page-octets 1)` and the ledger refuses. The word is returned by `return-from`; maintain's `handler-case` catches only
`fnn-store-io-refusal`, and owner.lisp:1650 discards the value. The history then stays whole in `fn-hrc-sfx` with no page image and
nothing says so. Refused, uncertain and accepted must stay distinct at every boundary (AGENTS.md); this boundary silences "refused".

## What ACL2 decides (new, books/history-root-credit.lisp; the host constant moves into it)

    (defun fn-hroot-begin-ask () (+ 4096 (fn-hroot-page-octets 1)))
    (defun fn-hroot-begin-room (l generation)          ; octets the reserve still has for GENERATION
      (nfix (- (fn-mcr-hroot l) (fn-mcr-hroot-sum-with l (fn-hroot-credit-key generation) 0))))
    ; (list :funded l2) | (list :refused REASON ASK ROOM l), REASON the resize's own, L unchanged
    (defun fn-hroot-begin-verdict (l generation)
      (let ((r (fn-mcr-hroot-resize l (fn-hroot-credit-key generation) (fn-hroot-begin-ask))))
        (if (eq (car r) :ok)
            (list :funded (cadr r))
          (list :refused (cadr r) (fn-hroot-begin-ask) (fn-hroot-begin-room l generation) l))))
    ; what the host reports and the operator surfaces: a named status, never :ok-shaped
    (defun fn-hroot-refresh-status (verdict)
      (if (eq (car verdict) :funded)
          '(:history-root :building)
        (list :history-root :refused (cadr verdict) :asked (caddr verdict) :available (cadddr verdict))))

`fn-owner-hroot-begin` becomes the stateful shell over `fn-hroot-begin-verdict` (it puts the ledger and the counter only on `:funded`).
The host acts on the status: maintain writes one `fnn-err` line `HISTORY root refresh refused reason=<r> asked=<n> available=<m>` and sets
the ACL2 global `fn-owner-history-root-refusal` to the status, which the operator health report prints (read site to be located in
the proof phase; no host-side value computation). A later `:building` status clears it.

## Statements

K1 (the refusal is the resize's own, distinct, and costs nothing):

    (defthm fn-hroot-begin-verdict-refused-is-the-resizes-own
      (implies (equal (car (fn-hroot-begin-verdict l g)) :refused)
               (let ((v (fn-hroot-begin-verdict l g)))
                 (and (equal (cadr v) (cadr (fn-mcr-hroot-resize l (fn-hroot-credit-key g) (fn-hroot-begin-ask))))
                      (not (equal (car v) :funded))
                      (equal (car (cddddr v)) l)                       ; ledger unchanged
                      (equal (fn-hroot-refresh-status v)
                             (list :history-root :refused (cadr v) :asked (fn-hroot-begin-ask)
                                   :available (fn-hroot-begin-room l g)))))))

K2 (exactly when the resize refuses, never otherwise; status never reads as building):

    (defthm fn-hroot-begin-verdict-refuses-exactly-when-the-resize-does
      (equal (car (fn-hroot-begin-verdict l g))
             (if (equal (car (fn-mcr-hroot-resize l (fn-hroot-credit-key g) (fn-hroot-begin-ask))) :ok) :funded :refused)))
    (defthm fn-hroot-refresh-status-building-iff-funded
      (equal (equal (cadr (fn-hroot-refresh-status v)) :building) (equal (car v) :funded)))

The history (`img`, `nimg`, `sfx`): `fn-owner-hroot-begin` has no `fn-hist` among its STOBJS, so it cannot change them; this is not a
theorem and is not cited as one. The host-side claim, that a refused begin leaves the installed root untouched, is the existing early
`return-from` before `create-fn-hrecs$s`/`create-fn-hist$p` (history-root.lisp:108-116) and is checked by the native witness below.

## Teeth and inhabitation (ATLAS fields)
- Satisfiable (positive, whole antecedent and conclusion): a ledger `l` whose reserve has room for `(fn-hroot-begin-ask)` yields `:funded`,
  status `(:history-root :building)`, and the ledger `l2` carries the credit (`fn-mcr-hroot-credit-of` = ask); and an EXHAUSTED instance
  (`hroot` reserve smaller than the ask, e.g. the CONVERGE-2 ledger of memory-credits.lisp's
  `fn-mcr-hroot-teeth-the-old-draw-refuses-the-candidate` shape with reserve 0) yields `(:refused :history-root-reserve-exhausted ask 0 l)`
  with `ask = 4096 + (fn-hroot-page-octets 1)` computed, not asserted, and status `(:history-root :refused ... :asked ask :available 0)`.
- Hypothesis removal: the same exhausted ledger with the reserve raised to ask gives `:funded`, so K1's antecedent does the work; and K2 is
  an `equal`, so a verdict that was `:refused` on a fundable ledger (or the converse) is a counterexample.
- Premise inhabitation: `l` ranges over `fn-mcr-fundedp` ledgers, inhabited by `(fn-mca-initial small-profile ...)` (already a theorem there).
- Native witness (host, advisory until certified): the 25k census run with the hook of
  coordinator/lanedumps/s-heap2-w15-census-fixed.lisp shows exactly one `HISTORY root refresh refused` line per maintain call and the
  health report prints the status; with the pool funded (92e054a48) it prints none.

## Owed / not here
- Before 92e054a48 lands the begin draws `fn-mcr-resize` (the shared pool, reason `:memory-budget-exhausted`); the statements are over
  `fn-mcr-hroot-resize` and so are only meaningful on the tree that has it. If this lane ships first, `fn-hroot-begin-verdict` calls
  `fn-mcr-resize` and K1 names that reason; one line changes when the reserve lands.
- `host_check --load` and `interface_emit --check` must stay at 0 findings (new definterface for `fn-hroot-begin-verdict` takes `:kinds` from its book guard).
