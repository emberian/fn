(in-package "ACL2")
(include-book "../../books/bp-report-outbox")
(include-book "bp-node-report-step-tests")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

(defun bpro-outbox ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpn-report-outbox-next (fn-bpnf-answer-state (bprst-settled)) nil))
(assert-event (equal (car (bpro-outbox)) :report-outbox))
(assert-event (equal (second (bpro-outbox)) 0))
(assert-event (equal (third (bpro-outbox)) *bpah-peer*))
(assert-event
 (equal (fn-bpn-report-outbox-peer-matchp (bpro-outbox) *bpah-peer*) t))
(assert-event
 (null (fn-bpn-report-outbox-peer-matchp (bpro-outbox) '(:dtn-none))))
(assert-event
 (equal (fourth (bpro-outbox))
        (fn-bpn-nth 6 (fourth (bprst-effect)))))
(assert-event
 (null (fn-bpn-report-outbox-next
        (fn-bpnf-answer-state (bprst-settled)) 0)))
(assert-event (null (fn-bpn-report-outbox-view *bprst-held*)))
(defun bpro-two-tombstones ()
  (declare (xargs :guard t :verify-guards nil))
  (let* ((old (car (fn-bpnf-held-list
                    (fn-bpnf-answer-state (bprst-settled)))))
         (new (update-nth 14
                          (update-nth 3 1 (fn-bpn-nth 14 old))
                          (update-nth 3 1 old))))
    (fn-bpnf-state-with-arrival
     (fn-bpnf-base *bprst-state*) (list new old)
     nil nil nil nil nil 4 0 2)))
(assert-event
 (equal (second (fn-bpn-report-outbox-next (bpro-two-tombstones) nil)) 0))
(assert-event
 (equal (second (fn-bpn-report-outbox-next (bpro-two-tombstones) 0)) 1))
(must-fail-checked (assert-event (fn-bpn-report-outbox-view *bprst-held*)))

;; KEYSTONE teeth (PRF-1048,
;; fn-bpn-report-outbox-next-selects-exactly-the-least-yielding-row).
;; Reachable positive witness, the complete antecedent and conclusion: both
;; tombstones of (bpro-two-tombstones) (arrivals 1 then 0 in list order)
;; yield with no AFTER, the answer is a yielding row's view and its arrival
;; (0) is at most every yielding row's; after 0 only the newer yields and
;; the answer's arrival is 1; after 1 nothing yields and the answer is nil.
(assert-event
 (let* ((st (bpro-two-tombstones))
        (rows (fn-bpnf-held-list st))
        (r0 (fn-bpn-report-outbox-next st nil))
        (r1 (fn-bpn-report-outbox-next st 0)))
   (and (equal (len rows) 2)
        (fn-bpn-report-outbox-yieldsp (car rows) nil)
        (fn-bpn-report-outbox-yieldsp (cadr rows) nil)
        (fn-bpn-report-outbox-any-yields rows nil)
        (equal (fn-bpn-nth 1 r0) 0)
        (fn-bpn-report-outbox-view-of-a-yielding-row r0 rows nil)
        (fn-bpn-report-outbox-arrival-at-most-every-yield 0 rows nil)
        (not (fn-bpn-report-outbox-yieldsp (cadr rows) 0))
        (fn-bpn-report-outbox-yieldsp (car rows) 0)
        (equal (fn-bpn-nth 1 r1) 1)
        (fn-bpn-report-outbox-view-of-a-yielding-row r1 rows 0)
        (fn-bpn-report-outbox-arrival-at-most-every-yield 1 rows 0)
        (not (fn-bpn-report-outbox-any-yields rows 1))
        (null (fn-bpn-report-outbox-next st 1)))))
;; Tooth (MUTATION witness): the first row in list order (arrival 1) is a
;; yielding row's view, yet its arrival is not at most every yielding row's
;; with no AFTER; a selector answering list order would break minimality.
(assert-event
 (let* ((st (bpro-two-tombstones))
        (rows (fn-bpnf-held-list st))
        (first-view (fn-bpn-report-outbox-view (car rows))))
   (and (equal (fn-bpn-nth 1 first-view) 1)
        (fn-bpn-report-outbox-view-of-a-yielding-row first-view rows nil))))
(must-fail-checked
 (assert-event
  (let* ((st (bpro-two-tombstones))
         (rows (fn-bpnf-held-list st)))
    (fn-bpn-report-outbox-arrival-at-most-every-yield
     (fn-bpn-nth 1 (fn-bpn-report-outbox-view (car rows))) rows nil))))
