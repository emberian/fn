(in-package "ACL2")
(include-book "../../books/bp-fnbs-deletion-publication")
(include-book "bp-node-report-step-tests")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

(defun bpdp-operation ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-delete-publication-authorize
   (bprst-issued) (second (bprst-effect)) (third (bprst-effect))
   (fourth (bprst-effect)) t t))
(assert-event (fn-bpnf-delete-publication-operationp (bpdp-operation)))
(assert-event
 (equal (fn-bpnf-delete-publication-frame (bpdp-operation))
        (fn-bpnf-delete-frame (fourth (bprst-effect)))))
(assert-event
 (equal (car (fn-bpnf-delete-publication-authorize
              (bprst-issued) (second (bprst-effect))
              (third (bprst-effect)) (fourth (bprst-effect)) nil t))
        :fault))
(assert-event
 (equal (car (fn-bpnf-delete-publication-authorize
              (bprst-issued) (second (bprst-effect))
              (1+ (third (bprst-effect)))
              (fourth (bprst-effect)) t t))
        :fault))
(assert-event
 (equal (car (fn-bpnf-delete-publication-authorize
              (bprst-issued) (second (bprst-effect))
              (third (bprst-effect))
              (fn-bpn-report-delete-record 4 0 0 '(1)
                                           :lifetime-expired)
              t t))
        :fault))
(must-fail-checked
 (assert-event
  (fn-bpnf-delete-publication-operationp
   (fn-bpnf-delete-publication-authorize
    (bprst-issued) (second (bprst-effect))
    (third (bprst-effect))
    (fourth (bprst-effect)) nil t))))

; KEYSTONE teeth (PRF-1014,
; fn-bpnf-delete-publication-authorize-admits-exactly-the-issued-pending-deletion):
; the positive witness above with its complete antecedent by name, then every
; part of the conclusion; then a withheld lock and a wrong operation id (the
; antecedent affirmed otherwise) answer the authority fault exactly.
(assert-event
 (let* ((st (bprst-issued))
        (issued (fn-bpnf-issued st))
        (epoch (second (bprst-effect)))
        (op (third (bprst-effect)))
        (record (fourth (bprst-effect)))
        (answer (bpdp-operation)))
   (and (fn-bpnf-operationp issued)
        (fn-bpnf-operation-matchp issued epoch op)
        (equal (fn-bpn-nth 3 issued) :delete)
        (equal (fn-bpn-nth 0 (fn-bpn-nth 4 issued)) record)
        (equal (fn-bpn-nth 5 issued) :pending)
        (equal (fn-bpnf-epoch st) epoch)
        (equal (fn-bpnf-next-op st) (1+ op))
        (fn-bpn-report-delete-recordp record)
        (equal (fn-bpn-nth 1 record) epoch)
        (equal (fn-bpn-nth 2 record) op)
        (not (equal (fn-bpnf-delete-frame record) :bad))
        (fn-bpnf-delete-publication-operationp answer)
        (equal (nth 1 answer) epoch)
        (equal (nth 2 answer) op)
        (equal (nth 3 answer) record)
        (equal (fn-bpnf-delete-publication-name answer)
               (fn-bpnf-stored-record-name epoch op))
        (equal (fn-bpnf-delete-publication-frame answer)
               (fn-bpnf-delete-frame record))
        (equal (nth 6 answer) (fn-jpub-initial t)))))
(assert-event
 (equal (fn-bpnf-delete-publication-authorize
         (bprst-issued) (second (bprst-effect)) (third (bprst-effect))
         (fourth (bprst-effect)) nil t)
        '(:fault :delete-authority)))
(assert-event
 (let ((op (third (bprst-effect))))
   (and (not (fn-bpnf-operation-matchp (fn-bpnf-issued (bprst-issued))
                                       (second (bprst-effect)) (1+ op)))
        (equal (fn-bpnf-delete-publication-authorize
                (bprst-issued) (second (bprst-effect)) (1+ op)
                (fourth (bprst-effect)) t t)
               '(:fault :delete-authority)))))
