(in-package "ACL2")
(include-book "consumer-account-relation-tests")
(include-book "../../books/consumer-account-relation-stage")

(defun fn-caast-pending (s)
  (fn-cp-nth 5 (fn-cp-nth 6 s)))
(defconst *caast-event-b* (fn-caart-event *caart-a* 3 (fn-caart-row '(98) 3)))
(defconst *caast-plan-b*
  (fn-caa-row-plan (fn-cp-nth 6 *caart-a*) *caast-event-b* (fn-cp-nth 4 *caast-event-b*)))
(defconst *caast-row-b* (fn-cp-nth 1 *caast-plan-b*))
(defconst *caast-cred-b* (fn-cp-nth 2 *caast-plan-b*))
(defconst *caast-index-a* (fn-cp-nth 2 (fn-cp-nth 5 (fn-caart-prep *caart-a*))))
(defconst *caast-rows-a* (revappend (fn-cp-nth 3 (fn-caart-prep *caart-a*)) nil))

;@positive fn-caas-begin-establishes-merge-relation
(assert-event
 (let* ((s *caart-initial*) (a (fn-cp-nth 6 s))
        (op '(:authority-begin (65) 0 1 7)) (e (fn-caart-event s 1 op))
        (one (fn-caa-begin s a e op)))
   (and (natp (fn-cp-nth 2 a)) (natp (fn-cp-nth 4 op)) (<= (fn-cp-nth 4 op) 7)
        (equal (car one) :ok)
        (fn-caas-merge-relp (fn-caast-pending (fn-cp-nth 1 one))))))

;@positive fn-caas-selected-stage-preserves-complete-merge
(assert-event
 (let* ((s *caart-a*) (a (fn-cp-nth 6 s)) (p (fn-cp-nth 5 a))
        (event *caast-event-b*) (row *caast-row-b*) (credential *caast-cred-b*)
        (wm (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))
        (one (fn-caa-stage-selected s a event row credential (fn-cp-nth 3 *caast-plan-b*))))
   (and (fn-caas-merge-relp p)
        (or (not (fn-cp-nth 6 p)) (fn-caa-name-lessp (fn-cp-nth 6 p) (fn-cp-nth 1 row)))
        (fn-caar-bindingp row (list :account-binding row credential) wm)
        (fn-caas-merge-relp (fn-caast-pending (fn-cp-nth 1 one)))
        (equal (fn-cp-nth 1 one) *caart-ab*))))

; A reachable retained-account/tombstone stage obeys the same invariant.
;@positive fn-caas-selected-stage-preserves-complete-merge
(assert-event
 (let* ((s *caart-delete-a*) (a (fn-cp-nth 6 s)) (p (fn-cp-nth 5 a))
        (op '(:authority-tombstone (66) 1 (98) 3)) (event (fn-caart-event s 10 op))
        (plan (fn-caa-tombstone-plan a event op)) (row (fn-cp-nth 1 plan))
        (credential (fn-cp-nth 2 plan))
        (wm (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))
        (one (fn-caa-stage-selected s a event row credential (fn-cp-nth 3 plan))))
   (and (fn-caas-merge-relp p)
        (or (not (fn-cp-nth 6 p)) (fn-caa-name-lessp (fn-cp-nth 6 p) (fn-cp-nth 1 row)))
        (fn-caar-bindingp row (list :account-binding row credential) wm)
        (fn-caas-merge-relp (fn-caast-pending (fn-cp-nth 1 one)))
        (equal (fn-cp-nth 1 one) *caart-delete-b*)
        (null (fn-cp-nth 3 row)) (null credential))))

;@hypothesis-removal fn-caas-begin-establishes-merge-relation watermark
; Corrupted authority input, not a reachable persisted state.
(assert-event
 (let* ((s *caart-initial*) (a (update-nth 2 -1 (fn-cp-nth 6 s)))
        (op (list :authority-begin '(65) 0 -1 7)) (e (fn-caart-event s 1 op))
        (one (fn-caa-begin s a e op)))
   (and (not (natp (fn-cp-nth 2 a)))
        (natp (fn-cp-nth 4 op)) (<= (fn-cp-nth 4 op) 7)
        (equal (car one) :ok)
        (not (fn-caas-merge-relp (fn-caast-pending (fn-cp-nth 1 one)))))))

; The direct internal begin expects policy grammar established by its caller.
;@hypothesis-removal fn-caas-begin-establishes-merge-relation policy-natural
(assert-event
 (let* ((s *caart-initial*) (a (fn-cp-nth 6 s))
        (op '(:authority-begin (65) 0 1 -1)) (e (fn-caart-event s 1 op))
        (one (fn-caa-begin s a e op)))
   (and (natp (fn-cp-nth 2 a)) (not (natp (fn-cp-nth 4 op))) (<= (fn-cp-nth 4 op) 7)
        (equal (car one) :ok)
        (not (fn-caas-merge-relp (fn-caast-pending (fn-cp-nth 1 one)))))))
;@hypothesis-removal fn-caas-begin-establishes-merge-relation policy-range
(assert-event
 (let* ((s *caart-initial*) (a (fn-cp-nth 6 s))
        (op '(:authority-begin (65) 0 1 8)) (e (fn-caart-event s 1 op))
        (one (fn-caa-begin s a e op)))
   (and (natp (fn-cp-nth 2 a)) (natp (fn-cp-nth 4 op)) (not (<= (fn-cp-nth 4 op) 7))
        (equal (car one) :ok)
        (not (fn-caas-merge-relp (fn-caast-pending (fn-cp-nth 1 one)))))))
;@hypothesis-removal fn-caas-begin-establishes-merge-relation success
(assert-event
 (let* ((s *caart-begun*) (a (fn-cp-nth 6 s))
        (op '(:authority-begin (65) 0 1 7)) (e (fn-caart-event s 2 op))
        (one (fn-caa-begin s a e op)))
   (and (natp (fn-cp-nth 2 a)) (natp (fn-cp-nth 4 op)) (<= (fn-cp-nth 4 op) 7)
        (not (equal (car one) :ok))
        (not (fn-caas-merge-relp (fn-caast-pending (fn-cp-nth 1 one)))))))

;@hypothesis-removal fn-caas-selected-stage-preserves-complete-merge merge
; Corrupt maintained count: the actual stage increments it, not recounts it.
(assert-event
 (let* ((s *caart-a*) (a0 (fn-cp-nth 6 s))
        (p (update-nth 3 99 (fn-cp-nth 5 a0))) (a (update-nth 5 p a0))
        (event *caast-event-b*) (row *caast-row-b*) (credential *caast-cred-b*)
        (wm (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))
        (one (fn-caa-stage-selected s a event row credential nil)))
   (and (not (fn-caas-merge-relp p))
        (or (not (fn-cp-nth 6 p)) (fn-caa-name-lessp (fn-cp-nth 6 p) (fn-cp-nth 1 row)))
        (fn-caar-bindingp row (list :account-binding row credential) wm)
        (not (fn-caas-merge-relp (fn-caast-pending (fn-cp-nth 1 one)))))))

;@hypothesis-removal fn-caas-selected-stage-preserves-complete-merge order
; Re-inserting the same key adds a duplicate authority row but one trie key.
(assert-event
 (let* ((s *caart-a*) (a (fn-cp-nth 6 s)) (p (fn-cp-nth 5 a))
        (event *caast-event-b*) (binding (fn-cai-get-octets '(97) *caast-index-a*))
        (row (fn-cp-nth 1 binding)) (credential (fn-cp-nth 2 binding))
        (wm (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))
        (one (fn-caa-stage-selected s a event row credential nil)))
   (and (fn-caas-merge-relp p)
        (not (or (not (fn-cp-nth 6 p)) (fn-caa-name-lessp (fn-cp-nth 6 p) (fn-cp-nth 1 row))))
        (fn-caar-bindingp row (list :account-binding row credential) wm)
        (not (fn-caas-merge-relp (fn-caast-pending (fn-cp-nth 1 one)))))))

;@hypothesis-removal fn-caas-selected-stage-preserves-complete-merge binding
; Individually malformed input must be excluded by the real planner.
(assert-event
 (let* ((s *caart-a*) (a (fn-cp-nth 6 s)) (p (fn-cp-nth 5 a))
        (event *caast-event-b*) (row *caast-row-b*) (credential nil)
        (wm (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))
        (one (fn-caa-stage-selected s a event row credential nil)))
   (and (fn-caas-merge-relp p)
        (or (not (fn-cp-nth 6 p)) (fn-caa-name-lessp (fn-cp-nth 6 p) (fn-cp-nth 1 row)))
        (not (fn-caar-bindingp row (list :account-binding row credential) wm))
        (not (fn-caas-merge-relp (fn-caast-pending (fn-cp-nth 1 one)))))))
