(in-package "ACL2")
(include-book "../../books/admission-preallocation-resources")

(defun fn-apr-ct-ledger ()
 (declare (xargs :guard t))
 '((10 10 10 10 10) (1 1 1 1 1) 1 nil (0 0 0 0 0)))
(defun fn-apr-ct-current (phase status)
 (declare (xargs :guard t))
 (list (fn-apr-token 0 '(2 0 0 1 :identity)) '(1 1 1 1 1) phase nil
       (fn-apr-operation-packet nil nil nil status nil nil nil nil nil nil)))

; Source-only registered-row fixture, not an actual issued native operation.
(assert-event
 (and (equal (fn-apr-continuation-kind :precheck nil (fn-apr-ct-ledger)
                                      t 2 0 :ready nil) :admission-census-unavailable)
      (equal (fn-apr-continuation-kind :precheck (fn-apr-ct-current :reserved :carried)
               (fn-apr-ct-ledger) t 2 0 :reserved nil) :admission-yield)))
(assert-event
 (and (equal (fn-apr-continuation-kind :prepare (fn-apr-ct-current :produced :carried)
               (fn-apr-ct-ledger) t 2 0 :reserved nil) :admission-executor-unavailable)
      (equal (fn-apr-continuation-kind :record-dir (fn-apr-ct-current :produced :carried)
               (fn-apr-ct-ledger) t 2 0 :record-attempted nil) :admission-executor-unavailable)
      (equal (fn-apr-continuation-kind :commit (fn-apr-ct-current :produced :carried)
               (fn-apr-ct-ledger) t 2 1 :completing '(0 . 1)) :admission-executor-unavailable)))
(assert-event
 (and (equal (fn-apr-continuation-kind :commit (fn-apr-ct-current :produced :carried)
               (fn-apr-ct-ledger) t 2 0 :completing '(0 . 1)) :admission-phase-unavailable)
      (equal (fn-apr-continuation-kind :commit (fn-apr-ct-current :produced :carried)
               (fn-apr-ct-ledger) t 2 1 :completing '(0 . 2)) :admission-phase-unavailable)
      (equal (fn-apr-continuation-kind :prepare (fn-apr-ct-current :produced :carried)
               (fn-apr-ct-ledger) t 3 0 :reserved nil) :stale)))
(assert-event
 (and (equal (fn-apr-continuation-kind :prepare (fn-apr-ct-current :uncertain :carried)
               (fn-apr-ct-ledger) t 2 0 :reserved nil) :admission-recovery-required)
      (equal (fn-apr-continuation-kind :prepare (fn-apr-ct-current :produced :unavailable)
               (fn-apr-ct-ledger) t 2 0 :reserved nil) :canonical-size-unavailable)
      (equal (fn-apr-continuation-kind :prepare (fn-apr-ct-current :produced :carried)
               (fn-apr-ct-ledger) nil 2 0 :reserved nil) :admission-profile-unavailable)))
(assert-event
 (and (equal (fn-apr-continuation-kind :joined (fn-apr-ct-current :promoted :carried)
               (fn-apr-ct-ledger) t 2 1 :completing '(0 . 1)) :admission-join-unavailable)
      (equal (fn-apr-continuation-kind :abort (fn-apr-ct-current :produced :carried)
               (fn-apr-ct-ledger) t 2 0 :reserved nil) :admission-join-unavailable)))
