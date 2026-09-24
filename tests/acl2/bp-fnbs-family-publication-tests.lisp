(in-package "ACL2")
(include-book "../../books/bp-fnbs-family-publication")
(include-book "bp-node-fragment-step-tests")
(include-book "std/testing/must-fail" :dir :system)

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
(must-fail
 (assert-event
  (equal (car (fn-bpnf-family-publication-authorize
               (bpnfs-uncertain) 3 0 (bpnfpub-record) t t))
         :ok)))
