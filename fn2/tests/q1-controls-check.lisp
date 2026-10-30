; Q1's shared-handler controls, judged (build/coordinator/fn2/lanes/a-dm4-q1-classification.md
; section 4). fn2/tests/q1-controls.lsp records four runs per kind into evidence/q1-controls.lisp;
; this book states what each kind's four records must say and asserts it. The Q1 case rows of a
; kind name its check (fn2-q1.lisp, :shared-handler-mutation) beside its independent contract
; (q1-contracts.lisp, :contract :independent). fn2-commit has no control until B5 (its arms are
; :unchecked); its case rows name neither, and the export lists them so.
(in-package "ACL2")
(include-book "evidence/q1-controls")
(include-book "../books/declare")

(defun fn2-q1-control-record (kind phase records)
  (declare (xargs :guard t))
  (cond ((atom records) nil)
        ((and (consp (car records)) (consp (cdar records))
              (equal (caar records) kind) (equal (cadar records) phase))
         (cddar records))
        (t (fn2-q1-control-record kind phase (cdr records)))))
; (TRACE ORACLE CONCRETE REFERENCE) per run; the four verdicts the statement requires:
; baseline and restoration pass both with the mutant idle; the shared mutant ran on both cores,
; TRACE stayed blind and the oracle failed; the concrete-only mutant ran on the concrete core
; alone and TRACE failed.
(defun fn2-q1-control-ok (kind records)
  (declare (xargs :guard t))
  (let ((b (fn2-q1-control-record kind :baseline records)) (s (fn2-q1-control-record kind :shared records))
        (c (fn2-q1-control-record kind :concrete-only records)) (r (fn2-q1-control-record kind :restored records)))
    (and (equal b '(:pass :pass 0 0)) (equal r '(:pass :pass 0 0))
         (true-listp s) (equal (take 2 s) '(:pass :fail)) (posp (nth 2 s)) (posp (nth 3 s))
         (true-listp c) (equal (car c) :fail) (posp (nth 2 c)) (equal (nth 3 c) 0))))
(defun fn2-conn-shared-handler-control () (declare (xargs :guard t)) (fn2-q1-control-ok 'fn2-conn *fn2-q1-controls*))
(defun fn2-echo-shared-handler-control () (declare (xargs :guard t)) (fn2-q1-control-ok 'fn2-echo *fn2-q1-controls*))
(defun fn2-listener-shared-handler-control () (declare (xargs :guard t)) (fn2-q1-control-ok 'fn2-listener *fn2-q1-controls*))
(defun fn2-scribe-shared-handler-control () (declare (xargs :guard t)) (fn2-q1-control-ok 'fn2-scribe *fn2-q1-controls*))
(assert-event (and (fn2-conn-shared-handler-control) (fn2-echo-shared-handler-control)
                   (fn2-listener-shared-handler-control) (fn2-scribe-shared-handler-control)))
; The judge refuses a kind without records, a shared mutant that ran on one core only, and a
; shared mutant TRACE caught.
(assert-event
 (and (not (fn2-q1-control-ok 'fn2-commit *fn2-q1-controls*))
      (not (fn2-q1-control-ok 'k '((k :baseline :pass :pass 0 0) (k :shared :pass :fail 1 0)
                                   (k :concrete-only :fail :fail 1 0) (k :restored :pass :pass 0 0))))
      (not (fn2-q1-control-ok 'k '((k :baseline :pass :pass 0 0) (k :shared :fail :fail 1 1)
                                   (k :concrete-only :fail :fail 1 0) (k :restored :pass :pass 0 0))))
      (fn2-q1-control-ok 'k '((k :baseline :pass :pass 0 0) (k :shared :pass :fail 1 1)
                              (k :concrete-only :fail :fail 1 0) (k :restored :pass :pass 0 0)))))
(value-triple (cw "Q1 CONTROLS: conn, echo, listener, scribe PASS (baseline, shared blind to TRACE and seen by the oracle, concrete-only seen by TRACE, restored); fn2-commit: none until B5~%"))
