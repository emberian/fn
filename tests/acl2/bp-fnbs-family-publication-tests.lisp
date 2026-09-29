(in-package "ACL2")
(include-book "../../books/bp-fnbs-family-publication")
(include-book "bp-node-fragment-step-tests")
(include-book "must-fail-checked")

(defun bpnfpub-record ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpn-nth 4 (fn-bpnf-issued (bpnfs-pending))))
(defun bpnfpub-authorized ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-family-publication-authorize
   (bpnfs-pending) 3 0 (bpnfpub-record) t t))
(assert-event (equal (car (bpnfpub-authorized)) :ok))
(assert-event
 (fn-bpnf-family-publication-operationp (bpnfpub-authorized)))
(assert-event
 (equal (fn-bpnf-family-publication-name (bpnfpub-authorized))
        (fn-bpnf-stored-record-name 3 0)))
(assert-event
 (equal (fn-bpnf-family-publication-frame (bpnfpub-authorized))
        (fn-bpnf-family-v1-frame (bpnfpub-record))))
(assert-event
 (equal (fn-bpnf-family-publication-authorize
         (bpnfs-pending) 3 1 (bpnfpub-record) t t)
        '(:fault :family-authority)))
(assert-event
 (equal (fn-bpnf-family-publication-authorize
         (bpnfs-pending) 3 0 (bpnfpub-record) nil t)
        '(:fault :family-authority)))
(assert-event
 (equal (fn-bpnf-family-publication-authorize
         (bpnfs-pending) 3 0 (bpnfpub-record) t nil)
        '(:fault :family-authority)))
(assert-event
 (equal (fn-bpnf-family-publication-authorize
         (bpnfs-uncertain) 3 0 (bpnfpub-record) t t)
        '(:fault :family-authority)))
(must-fail-checked
 (assert-event
  (equal (car (fn-bpnf-family-publication-authorize
               (bpnfs-uncertain) 3 0 (bpnfpub-record) t t))
         :ok)))

; KEYSTONE teeth (PRF-1015,
; fn-bpnf-family-publication-authorize-admits-exactly-the-issued-pending-family):
; the positive witness above with its complete antecedent by name, then every
; part of the conclusion; then a withheld lock and a wrong operation id (the
; antecedent affirmed otherwise) answer the authority fault exactly.
(assert-event
 (let* ((st (bpnfs-pending))
        (issued (fn-bpnf-issued st))
        (record (bpnfpub-record))
        (answer (bpnfpub-authorized)))
   (and (fn-bpnf-operationp issued)
        (fn-bpnf-operation-matchp issued 3 0)
        (equal (fn-bpn-nth 3 issued) :family)
        (equal (fn-bpn-nth 4 issued) record)
        (equal (fn-bpn-nth 5 issued) :pending)
        (equal (fn-bpnf-epoch st) 3)
        (equal (fn-bpnf-next-op st) 1)
        (equal (fn-bpnf-next-arrival st) (1+ (fn-bpn-nth 4 record)))
        (fn-bpnf-family-record-atp record)
        (equal (fn-bpn-nth 1 record) 3)
        (equal (fn-bpn-nth 2 record) 0)
        (not (equal (fn-bpnf-family-v1-frame record) :bad))
        (fn-bpnf-family-publication-operationp answer)
        (equal (nth 1 answer) 3)
        (equal (nth 2 answer) 0)
        (equal (nth 3 answer) record)
        (equal (fn-bpnf-family-publication-name answer)
               (fn-bpnf-stored-record-name 3 0))
        (equal (fn-bpnf-family-publication-frame answer)
               (fn-bpnf-family-v1-frame record))
        (equal (nth 6 answer) (fn-jpub-initial t)))))
(assert-event
 (equal (fn-bpnf-family-publication-authorize
         (bpnfs-pending) 3 0 (bpnfpub-record) nil t)
        '(:fault :family-authority)))
(assert-event
 (and (not (fn-bpnf-operation-matchp (fn-bpnf-issued (bpnfs-pending)) 3 1))
      (equal (fn-bpnf-family-publication-authorize
              (bpnfs-pending) 3 1 (bpnfpub-record) t t)
             '(:fault :family-authority))))
