(in-package "ACL2")
(include-book "../../books/bp-report-observe")
(include-book "bp-report-author-tests")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

(defun bproa-committed ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpn-report-author-step
   (fn-bpnf-answer-state (bpra-proposal))
   (list :base
         (list :persist-result
               (second (car (fn-bpnf-answer-effects (bpra-proposal))))
               :durable))))
(defun bproa-job ()
  (declare (xargs :guard t :verify-guards nil))
  (car (fn-bpn-machine-state-jobs
        (fn-bpnf-base (fn-bpnf-answer-state (bproa-committed))))))
(defun bproa-subject ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpb-bundle-primary (fn-bpn-job-bundle (bproa-job))))
(defun bproa-report ()
  (declare (xargs :guard t :verify-guards nil))
  (list :report '((nil) (nil) (nil) (t)) 1
        (fn-bpp-source (bproa-subject))
        (list (fn-bpp-creation-time (bproa-subject))
              (fn-bpp-sequence (bproa-subject))) nil))
(defun bproa-incoming-bundle ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpb-make-bundle
   (fn-bpp-make-block
    *fn-bpp-flag-administrative* 2 *bpnm-local* *bpnm-peer*
    '(:dtn-none) 0 55 3600000 nil nil)
   (fn-bpn-send-blocks *bpnm-config*)
   (fn-bpb-payload-block 2 (fn-bpn-report-encode (bproa-report)))))
(defun bproa-held ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-held
   (fn-bpnf-ingress-principal *bpah-ingress*)
   (fn-bpb-bundle-id (bproa-incoming-bundle)) 2 *bpah-ingress*
   nil nil (bproa-incoming-bundle) (fn-bpb-encode (bproa-incoming-bundle))
   '(:wall) nil nil '(:dispatch-pending) nil nil 0))
(defun bproa-state ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-state-with-arrival
   (fn-bpnf-base (fn-bpnf-answer-state (bproa-committed)))
   (list (bproa-held)) nil nil nil nil nil 8 0 3))

(assert-event (fn-bpb-bundlep (bproa-incoming-bundle)))
(assert-event (fn-bpnf-heldp (bproa-held)))
(assert-event
 (equal (fn-bpn-report-job-matchp
         (fn-bpnf-base (fn-bpnf-answer-state (bproa-committed)))
         (bpro-outbox)) t))
(assert-event
 (null (fn-bpn-report-job-matchp
        (fn-bpnf-base (fn-bpnf-answer-state (bproa-committed)))
        (update-nth 3 '(1 2 3) (bpro-outbox)))))
(assert-event
 (let* ((base (fn-bpnf-base (fn-bpnf-answer-state (bproa-committed))))
        (changed (update-nth 4 10 (bproa-job)))
        (wrong (fn-bpn-state-with
                base (list changed) (fn-bpn-machine-state-contacts base)
                nil nil (fn-bpn-machine-state-next-token base))))
   (and (fn-bpn-jobp changed)
        (null (fn-bpn-report-job-matchp wrong (bpro-outbox))))))
(assert-event
 (equal (fn-bpn-report-observe-next (bproa-state) *bpnm-local* nil)
        (list :observed 2 (fn-bpn-job-key (bproa-job)) (bproa-report))))
(assert-event
 (null (fn-bpn-report-observe-next (bproa-state) *bpnm-local* 2)))
(assert-event
 (null (fn-bpn-report-observe-next (bproa-state) *bpnm-peer* nil)))
(must-fail-checked
 (assert-event
  (equal (fn-bpn-report-observe-next (bproa-state) *bpnm-peer* nil)
         (list :observed 2 (fn-bpn-job-key (bproa-job)) (bproa-report)))))

;; PRF-136: fn-bpn-report-observe-held-needs-an-administrative-header.
;; Witness: the pending request's carrier (not administrative) is no report.
;; Without the hypothesis: the held status report has an administrative
;; header and is observed, so the conclusion fails.
(assert-event
 (and (not (fn-bpnf-held-administrative-headerp *bpah-held*))
      (not (fn-bpn-report-observe-held (bproa-state) *bpah-held*
                                       *bpnm-local*))))
(assert-event
 (and (fn-bpnf-held-administrative-headerp (bproa-held))
      (fn-bpn-report-observe-held (bproa-state) (bproa-held) *bpnm-local*)))

;; KEYSTONE teeth (PRF-1047,
;; fn-bpn-report-observe-next-selects-exactly-the-least-yielding-row).
;; Reachable positive witness, the complete antecedent and conclusion: for
;; the local node with no AFTER a held row of (bproa-state) yields, the
;; answer is the answer of a yielding row, and its arrival (2) is at most
;; every yielding row's.
(assert-event
 (let* ((st (bproa-state))
        (rows (fn-bpnf-held-list st))
        (r (fn-bpn-report-observe-next st *bpnm-local* nil)))
   (and (consp rows)
        (fn-bpn-report-observe-any-yields st rows *bpnm-local* nil)
        r
        (equal (fn-bpn-nth 1 r) 2)
        (fn-bpn-report-observe-answer-of-a-yielding-row
         r st rows *bpnm-local* nil)
        (fn-bpn-report-observe-arrival-at-most-every-yield
         2 st rows *bpnm-local* nil))))
;; The nil side both ways: after arrival 2 no row yields and the answer is
;; nil; for the peer node no row yields and the answer is nil.
(assert-event
 (let* ((st (bproa-state))
        (rows (fn-bpnf-held-list st)))
   (and (not (fn-bpn-report-observe-any-yields st rows *bpnm-local* 2))
        (null (fn-bpn-report-observe-next st *bpnm-local* 2))
        (not (fn-bpn-report-observe-any-yields st rows *bpnm-peer* nil))
        (null (fn-bpn-report-observe-next st *bpnm-peer* nil)))))
;; Tooth (MUTATION witness): a selector that ignored AFTER would answer the
;; arrival-2 report after arrival 2, which no row yields.
(must-fail-checked
 (assert-event
  (let* ((st (bproa-state))
         (rows (fn-bpnf-held-list st)))
    (iff (fn-bpn-report-observe-next st *bpnm-local* nil)
         (fn-bpn-report-observe-any-yields st rows *bpnm-local* 2)))))
