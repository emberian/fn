; Teeth for the file-kernel publication keystones.
;
; The 2026-09-18 review §5: "Acknowledgement cannot be forged ... The
; five-barrier gate is structural through `fn-sf-phase-shapep'."  The
; file-kernel half of that is `fn-sf-success-requires-matching-completion'
; (books/store-files.lisp:614): a success record appears only for the exact
; completion the core produced, in the one phase that admits it.

(in-package "ACL2")
(include-book "../../books/store-files-invariants")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; A reachable, non-degenerate witness: the whole publication sequence, driven
; by the production transitions, to the one state in which a success may be
; emitted.  Non-degenerate because it passes through every barrier, carries a
; real record, and reaches `:completed' rather than being written down.

(defconst *sft-groups* '("fn.letters" "fn.test"))
(defconst *sft-record*
  (fn-record-make 0 0 0 "<zero@example.invalid>" '(90)
                  '("fn.letters" "fn.test")
                  "archive-zero" "content-zero" "release-zero" 2))

(defconst *sft-reserved*
  (fn-sf-frontier-dir-result
   (fn-sf-frontier-replace-result
    (fn-sf-frontier-file-result (fn-sf-start-frontier (fn-sf-initial-state)) :ok)
    :ok)
   :ok))
(defconst *sft-staged*
  (fn-sf-prepare-record *sft-reserved* *sft-record* *sft-groups* 10))
(defconst *sft-published*
  (fn-sf-record-dir-result
   (fn-sf-record-link-result (fn-sf-record-file-result *sft-staged* :ok) :ok)
   :ok))
(defconst *sft-completed* (fn-sf-core-completion *sft-published* 0 0 :matching))

(assert-event (fn-sf-statep *sft-reserved*))
(assert-event (equal (fn-sf-phase *sft-staged*) :record-staged))
(assert-event (equal (fn-sf-phase *sft-published*) :completing))
(assert-event (equal (fn-sf-phase *sft-completed*) :completed))
(assert-event (equal (fn-sf-records *sft-completed*) (list *sft-record*)))
(assert-event (null (fn-sf-successes *sft-completed*)))

; Emission is reachable exactly here, and it is the only thing that grows the
; success list.
(assert-event
 (equal (fn-sf-successes (fn-sf-emit-success *sft-completed* 0 0)) '((0 . 0))))

; Not before the phase, and not for another transaction identity.
(assert-event (equal (fn-sf-emit-success *sft-published* 0 0) *sft-published*))
(assert-event (equal (fn-sf-emit-success *sft-completed* 0 1) *sft-completed*))
(assert-event (equal (fn-sf-emit-success *sft-completed* 1 0) *sft-completed*))

; -----------------------------------------------------------------------------
; Teeth for `fn-sf-success-requires-matching-completion'
;   (implies (not (and (equal (fn-sf-phase s) :completed)
;                      (equal (cons sequence txid) (fn-sf-completion s))))
;            (equal (fn-sf-emit-success s sequence txid) s))

; The sole hypothesis dropped: the one state and identity pair that satisfies
; the conjunction is exactly where emission is not a no-op.
(assert-event (equal (fn-sf-phase *sft-completed*) :completed))
(assert-event (equal (cons 0 0) (fn-sf-completion *sft-completed*)))

(local
 (must-fail
  (defthm sft-teeth-emit-success-without-mismatch
    (equal (fn-sf-emit-success *sft-completed* 0 0) *sft-completed*))))

; -----------------------------------------------------------------------------
; Teeth for `fn-sf-stable-records-prefix-of-crash'
;   (implies (and (fn-sf-statep s)                                     ; H1
;                 (fn-sf-crash-choicep frontier-choice record-choice))  ; H2
;            (fn-sf-prefixp (fn-sf-records s)
;                           (fn-sf-records (fn-sf-crash s frontier-choice record-choice))))

; H1 dropped.  `fn-sf-crash' refuses a non-state, so the crash image is the
; forged state itself -- and `fn-sf-prefixp' is reflexive only on true lists
; (books/store-files-invariants.lisp:21-24).  A forged state whose record list
; has an improper tail is not a prefix of itself.
(defconst *sft-forged*
  (fn-sf-make :ready 1 nil (cons *sft-record* :improper-tail) nil nil nil 5))
(assert-event (not (fn-sf-statep *sft-forged*)))
(assert-event (fn-sf-crash-choicep :old :absent))
(assert-event (equal (fn-sf-crash *sft-forged* :old :absent) *sft-forged*))
(assert-event
 (not (fn-sf-prefixp (fn-sf-records *sft-forged*) (fn-sf-records *sft-forged*))))

(local
 (must-fail
  (defthm sft-teeth-crash-prefix-without-statep
    (fn-sf-prefixp (fn-sf-records *sft-forged*)
                   (fn-sf-records (fn-sf-crash *sft-forged* :old :absent))))))

; H2 has no teeth, and none is forged.  `fn-sf-crash' returns its argument
; unchanged for a choice outside `fn-sf-crash-choicep', and under H1 the record
; list of a state is a true list, so the conclusion holds for every choice
; whatever H2 says.  H2 is load-bearing for the theorems about what a crash may
; CHANGE, not for this one about what it may not DROP.  Recorded in HANDOFF.md.
(assert-event (not (fn-sf-crash-choicep :sideways :absent)))
(assert-event (equal (fn-sf-crash *sft-completed* :sideways :absent) *sft-completed*))
