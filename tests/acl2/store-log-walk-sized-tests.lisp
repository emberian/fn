(in-package "ACL2")
(include-book "../../books/store-log-walk-sized")
(include-book "../../books/statement-attach")
(include-book "../../books/records-attach")
(defun fn-lgbs-test-snapshot-wire (sequence txid)
 (declare (xargs :guard (and (natp sequence) (natp txid) (<= sequence *fn-cbor-max-uint*) (<= txid *fn-cbor-max-uint*)) :guard-hints (("Goal" :in-theory (enable fn-cbor-valuep fn-cbor-valuep-bounded)))))
 (fn-stmt-encode-items
  (list '(:bytes 102 110 45 101) '(:uint . 0) '(:uint . 3)
        (cons :uint sequence) (cons :uint txid) '(:uint . 0) '(:uint . 1)
        '(:bytes 112) '(:bytes 42 43))))
(defun fn-lgbs-test-legacy (txid)
 (declare (xargs :guard t :verify-guards nil))
 (fn-record-encode-impl
  (fn-record-make txid txid 1 "<t@example.invalid>" '(72 105) '("fn.test")
                  "o" "s" "e" 4 5)))
(defun fn-lgbs-test-old-result (rs next)
 (declare (xargs :guard t))
 (mv-let (rows n) (fn-lgb-decode-next rs next) (list rows n)))
; Complete positive old output and actual row carry, mixed legacy/snapshot.
(assert-event
 (let ((rs (list (fn-lgbs-test-legacy 7) (fn-lgbs-test-snapshot-wire 8 9))))
  (mv-let (rows next carries) (fn-lgb-decode-next-sized rs 1)
   (and (equal (list rows next) (fn-lgbs-test-old-result rs 1))
        (equal next 8) (equal (len rows) 2) (equal (len carries) 2)
        (null (car carries)) (fn-srss-carries-correspondsp rows carries)
        (equal (cadr carries) (fn-scs-summary (cadr rows)))))))
; Bad first record does not prevent folding a later actual txid.
(assert-event
 (let ((rs (list '(255) (fn-lgbs-test-legacy 31))))
  (mv-let (rows next carries) (fn-lgb-decode-next-sized rs 1)
   (and (equal rows :bad) (equal next 32) (null carries)
        (equal (list rows next) (fn-lgbs-test-old-result rs 1))))))
(assert-event
 (let ((rs (list (fn-lgbs-test-snapshot-wire 0 1) '(255))))
  (mv-let (rows next carries) (fn-lgb-decode-next-sized rs 9)
   (and (equal rows :bad) (equal next 9) (null carries)
        (equal (list rows next) (fn-lgbs-test-old-result rs 9))))))
(assert-event
 (mv-let (rows next carries) (fn-lgb-decode-next-sized nil 17)
  (and (null rows) (equal next 17) (null carries)
       (equal (list rows next) (fn-lgbs-test-old-result nil 17)))))
; Corrupted external list spine refuses, with complete old outputs retained.
(assert-event
 (let ((rs (cons (fn-lgbs-test-legacy 4) 'malformed-tail)))
  (mv-let (rows next carries) (fn-lgb-decode-next-sized rs 1)
   (and (equal rows :bad) (equal next 5) (null carries)
        (equal (list rows next) (fn-lgbs-test-old-result rs 1))))))
