(in-package "ACL2")
(include-book "../../books/store-recover-stream-sized")
(include-book "../../books/statement-attach")
(include-book "../../books/records-attach")

(defun fn-srss-test-snapshot-wire (sequence txid)
 (declare (xargs :guard (and (natp sequence) (natp txid) (<= sequence *fn-cbor-max-uint*) (<= txid *fn-cbor-max-uint*)) :guard-hints (("Goal" :in-theory (enable fn-cbor-valuep fn-cbor-valuep-bounded)))))
 (fn-stmt-encode-items
  (list '(:bytes 102 110 45 101) '(:uint . 0) '(:uint . 3)
        (cons :uint sequence) (cons :uint txid) '(:uint . 0) '(:uint . 1)
        '(:bytes 112) '(:bytes 42 43))))

; Actual snapshot dispatch and complete public chunk output; ordered two rows.
(assert-event
 (let ((wire (list (fn-srss-test-snapshot-wire 0 1)
                   (fn-srss-test-snapshot-wire 1 2))))
  (mv-let (rows carries) (fn-srss-decode wire)
   (and (equal rows '((0 1 0 1 (112) (42 43)) (1 2 0 1 (112) (42 43))))
        (equal rows (fn-srs-decode wire))
        (true-listp carries) (equal (len carries) 2)
        (fn-srss-carries-correspondsp rows carries)
        (equal (car carries) (fn-scs-summary (car rows)))
        (equal (cadr carries) (fn-scs-summary (cadr rows)))))))

; Refusal after a valid prefix discards both reversed accumulators.
(assert-event
 (let ((wire (list (fn-srss-test-snapshot-wire 0 1) '(255))))
  (mv-let (rows carries) (fn-srss-decode wire)
   (and (equal rows :bad) (equal rows (fn-srs-decode wire)) (null carries)))))
(assert-event
 (mv-let (rows carries) (fn-srss-decode 'malformed-tail)
  (and (equal rows :bad) (equal rows (fn-srs-decode 'malformed-tail)) (null carries))))
(assert-event
 (mv-let (rows carries) (fn-srss-decode nil)
  (and (null rows) (null carries) (equal rows (fn-srs-decode nil))
       (fn-srss-carries-correspondsp rows carries))))

; Hypothesis removal for maintained accumulator provenance: actual success,
; but a corrupted carried prefix fails correspondence after reversal.
(assert-event
 (let ((acc '((0 1 0 1 (112) (42 43)))) (carries '((0 0 0))))
  (mv-let (rows out) (fn-srss-decode-loop nil acc carries)
   (and (not (fn-srss-carries-correspondsp acc carries))
        (not (equal rows :bad))
        (not (fn-srss-carries-correspondsp rows out))))))
; Hypothesis removal for success: maintained empty accumulators, bad input,
; and :bad is not an aligned row list.
(assert-event
 (mv-let (rows carries) (fn-srss-decode-loop '(nil) nil nil)
  (and (fn-srss-carries-correspondsp nil nil) (equal rows :bad)
       (not (fn-srss-carries-correspondsp rows carries)))))
; A non-snapshot successful row retains its exact public value and NIL carry.
(assert-event
 (let ((wire (list (fn-stmt-encode-items
  '((:bytes 102 110 45 101) (:uint . 0) (:uint . 0) (:uint . 0)
    (:uint . 1) (:uint . 0) (:bytes 97) (:bytes 98) (:bytes 99) (:uint . 1))))))
  (mv-let (rows carries) (fn-srss-decode wire)
   (and (equal rows '((:retention :undertake 0 1 0 "a" "b" "c" 1)))
        (equal rows (fn-srs-decode wire)) (equal carries '(nil))
        (fn-srss-carries-correspondsp rows carries)))))
; Width lemma's sole retained seed hypothesis is necessary; provenance is
; intentionally not required for this structural statement.
(assert-event
 (let ((acc '(row)) (carries nil))
  (mv-let (rows out) (fn-srss-decode-loop nil acc carries)
   (and (not (equal (len acc) (len carries))) (true-listp out)
        (not (equal (len rows) (len out)))))))
; Improper seed tails do not need whole-list validation for aligned width.
(assert-event
 (mv-let (rows out) (fn-srss-decode-loop nil '(a . tail) '(nil . tail))
  (and (not (true-listp '(a . tail))) (not (true-listp '(nil . tail)))
       (equal (len '(a . tail)) (len '(nil . tail)))
       (true-listp out) (equal (len rows) (len out)))))
