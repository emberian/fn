; Complete literal antecedents/conclusions at the actual composed planners.
; Corruptions below are explicit state/input removals, not persisted states.
(in-package "ACL2")
(include-book "../../books/consumer-account-planner-stage-relation")
(local (include-book "consumer-account-row-relation-tests"))

;@positive fn-caps-actual-row-preserves-borrowed-complete-merge
(defthm capst-actual-new-row-complete-positive
 (let* ((s *caarrt-begun*) (a *caarrt-new-a*) (event *caarrt-new-event*) (op *caarrt-new-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-row s a event op)))
  (and (fn-caps-merge-relp p installed)
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 (fn-cp-nth 5 p)))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (equal (car (fn-caa-row-plan a event op)) :stage)
       (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed)))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@positive fn-caps-actual-row-preserves-borrowed-complete-merge
(defthm capst-actual-retained-row-complete-positive
 (let* ((s *caarrt-retain-begun*) (a *caarrt-retain-a*) (event *caarrt-retain-event*) (op *caarrt-retain-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-row s a event op)))
  (and (fn-caps-merge-relp p installed)
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 (fn-cp-nth 5 p)))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (equal (car (fn-caa-row-plan a event op)) :stage)
       (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed)))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@positive fn-caps-actual-row-preserves-borrowed-complete-merge
(defthm capst-actual-recreated-row-complete-positive
 (let* ((s *caarrt-rebirth-begun*) (a *caarrt-rebirth-a*) (event *caarrt-rebirth-event*) (op *caarrt-rebirth-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-row s a event op)))
  (and (fn-caps-merge-relp p installed)
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 (fn-cp-nth 5 p)))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (equal (car (fn-caa-row-plan a event op)) :stage)
       (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed)))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@positive fn-caps-actual-tombstone-preserves-borrowed-complete-merge
(defthm capst-actual-tombstone-complete-positive
 (let* ((s *caarrt-retain-begun*) (a *caarrt-retain-a*)
        (event *caarrt-tomb-event*) (op *caarrt-tomb-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-tombstone s a event op)))
  (and (fn-caps-merge-relp p installed)
       (equal (car (fn-caa-tombstone-plan a event op)) :stage)
       (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed)))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@positive fn-caps-begin-establishes-borrowed-merge
(defthm capst-empty-begin-complete-positive
 (let* ((s *caarrt-initial*) (a (fn-cp-nth 6 s)) (op '(:authority-begin (65) 0 1 7))
        (event (fn-caarrt-event s 1 op)) (one (fn-caa-begin s a event op)))
  (and (natp (fn-cp-nth 2 a))
       (natp (fn-cp-nth 4 op)) (<= (fn-cp-nth 4 op) 7)
       (fn-caps-old-rowsp (fn-cp-nth 4 a) (fn-cp-nth 2 a))
       (equal (car one) :ok)
       (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a))))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@positive fn-caps-begin-establishes-borrowed-merge
(defthm capst-restored-begin-complete-positive
 (let* ((s *caarrt-published*) (a (fn-cp-nth 6 s)) (op '(:authority-begin (66) 1 3 7))
        (event (fn-caarrt-event s 6 op)) (one (fn-caa-begin s a event op)))
  (and (natp (fn-cp-nth 2 a))
       (natp (fn-cp-nth 4 op)) (<= (fn-cp-nth 4 op) 7)
       (fn-caps-old-rowsp (fn-cp-nth 4 a) (fn-cp-nth 2 a))
       (equal (car one) :ok)
       (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a))))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@positive fn-caps-begin-establishes-borrowed-merge
(defthm capst-tombstones-begin-complete-positive
 (let* ((s *caarrt-tomb-published*) (a (fn-cp-nth 6 s)) (op '(:authority-begin (67) 2 8 7))
        (event (fn-caarrt-event s 11 op)) (one (fn-caa-begin s a event op)))
  (and (natp (fn-cp-nth 2 a))
       (natp (fn-cp-nth 4 op)) (<= (fn-cp-nth 4 op) 7)
       (fn-caps-old-rowsp (fn-cp-nth 4 a) (fn-cp-nth 2 a))
       (equal (car one) :ok)
       (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a))))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@hypothesis-removal fn-caps-actual-row-preserves-borrowed-complete-merge codec
(defthm capst-corrupted-row-codec-removal
 (let* ((s *caarrt-begun*) (a *caarrt-new-a*) (event *caarrt-new-event*) (op *caarrt-invalid-codec-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-row s a event op)))
  (and (fn-caps-merge-relp p installed)
       (not (fn-cac-operationp op))
       (fn-cp-authority-namespacep (fn-cp-nth 6 (fn-cp-nth 5 p)))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (equal (car (fn-caa-row-plan a event op)) :stage)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed))))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@hypothesis-removal fn-caps-actual-row-preserves-borrowed-complete-merge namespace
(defthm capst-corrupted-row-namespace-removal
 (let* ((s *caarrt-begun*) (a *caarrt-no-namespace-a*) (event *caarrt-new-event*) (op *caarrt-new-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-row s a event op)))
  (and (fn-caps-merge-relp p installed)
       (fn-cac-operationp op)
       (not (fn-cp-authority-namespacep (fn-cp-nth 6 (fn-cp-nth 5 p))))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (equal (car (fn-caa-row-plan a event op)) :stage)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed))))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@hypothesis-removal fn-caps-actual-row-preserves-borrowed-complete-merge coordinate
(defthm capst-corrupted-row-coordinate-removal
 (let* ((s *caarrt-begun*) (a *caarrt-new-a*) (event *caarrt-wide-event*) (op *caarrt-wide-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-row s a event op)))
  (and (fn-caps-merge-relp p installed)
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 (fn-cp-nth 5 p)))
       (not (fn-cp-uintp (fn-cp-nth 2 event)))
       (equal (car (fn-caa-row-plan a event op)) :stage)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed))))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@hypothesis-removal fn-caps-actual-row-preserves-borrowed-complete-merge merge
(defthm capst-corrupted-row-merge-removal
 (let* ((s *caarrt-begun*) (a (update-nth 5 (update-nth 3 99 (fn-cp-nth 5 *caarrt-new-a*)) *caarrt-new-a*)) (event *caarrt-new-event*) (op *caarrt-new-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-row s a event op)))
  (and (not (fn-caps-merge-relp p installed))
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 (fn-cp-nth 5 p)))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (equal (car (fn-caa-row-plan a event op)) :stage)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed))))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@hypothesis-removal fn-caps-actual-row-preserves-borrowed-complete-merge success
(defthm capst-corrupted-row-success-removal
 (let* ((s *caarrt-begun*) (a *caarrt-retain-a*) (event *caarrt-retain-event*) (op (update-nth 4 99 *caarrt-retain-op*))
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-row s a event op)))
  (and (fn-caps-merge-relp p installed)
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 (fn-cp-nth 5 p)))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (not (equal (car (fn-caa-row-plan a event op)) :stage))
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed))))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@hypothesis-removal fn-caps-actual-tombstone-preserves-borrowed-complete-merge merge
(defthm capst-corrupted-tombstone-merge-removal
 (let* ((s *caarrt-retain-begun*) (a *caarrt-bad-token-a*)
        (event *caarrt-tomb-event*) (op *caarrt-tomb-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-tombstone s a event op)))
  (and (not (fn-caps-merge-relp p installed))
       (equal (car (fn-caa-tombstone-plan a event op)) :stage)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed))))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@hypothesis-removal fn-caps-actual-tombstone-preserves-borrowed-complete-merge success
(defthm capst-corrupted-tombstone-success-removal
 (let* ((s *caarrt-retain-begun*) (a *caarrt-retain-a*)
        (event *caarrt-tomb-event*) (op (update-nth 3 '(98) *caarrt-tomb-op*))
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-tombstone s a event op)))
  (and (fn-caps-merge-relp p installed)
       (not (equal (car (fn-caa-tombstone-plan a event op)) :stage))
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed))))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@hypothesis-removal fn-caps-begin-establishes-borrowed-merge watermark
(defthm capst-corrupted-begin-watermark-removal
 (let* ((s *caarrt-initial*) (a (update-nth 2 -1 (fn-cp-nth 6 s))) (op '(:authority-begin (65) 0 -1 7))
        (event (fn-caarrt-event s 1 op)) (one (fn-caa-begin s a event op)))
  (and (not (natp (fn-cp-nth 2 a)))
       (natp (fn-cp-nth 4 op))
       (<= (fn-cp-nth 4 op) 7)
       (fn-caps-old-rowsp (fn-cp-nth 4 a) (fn-cp-nth 2 a))
       (equal (car one) :ok)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a)))))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@hypothesis-removal fn-caps-begin-establishes-borrowed-merge policy-natural
(defthm capst-corrupted-begin-policy-natural-removal
 (let* ((s *caarrt-initial*) (a (fn-cp-nth 6 s)) (op '(:authority-begin (65) 0 1 -1))
        (event (fn-caarrt-event s 1 op)) (one (fn-caa-begin s a event op)))
  (and (natp (fn-cp-nth 2 a))
       (not (natp (fn-cp-nth 4 op)))
       (<= (fn-cp-nth 4 op) 7)
       (fn-caps-old-rowsp (fn-cp-nth 4 a) (fn-cp-nth 2 a))
       (equal (car one) :ok)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a)))))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@hypothesis-removal fn-caps-begin-establishes-borrowed-merge policy-range
(defthm capst-corrupted-begin-policy-range-removal
 (let* ((s *caarrt-initial*) (a (fn-cp-nth 6 s)) (op '(:authority-begin (65) 0 1 8))
        (event (fn-caarrt-event s 1 op)) (one (fn-caa-begin s a event op)))
  (and (natp (fn-cp-nth 2 a))
       (natp (fn-cp-nth 4 op))
       (not (<= (fn-cp-nth 4 op) 7))
       (fn-caps-old-rowsp (fn-cp-nth 4 a) (fn-cp-nth 2 a))
       (equal (car one) :ok)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a)))))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@hypothesis-removal fn-caps-begin-establishes-borrowed-merge oldrows
(defthm capst-corrupted-begin-oldrows-removal
 (let* ((s *caarrt-initial*) (a (update-nth 4 '((:account (97) nil nil nil)) (fn-cp-nth 6 s))) (op '(:authority-begin (65) 0 1 7))
        (event (fn-caarrt-event s 1 op)) (one (fn-caa-begin s a event op)))
  (and (natp (fn-cp-nth 2 a))
       (natp (fn-cp-nth 4 op))
       (<= (fn-cp-nth 4 op) 7)
       (not (fn-caps-old-rowsp (fn-cp-nth 4 a) (fn-cp-nth 2 a)))
       (equal (car one) :ok)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a)))))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)

;@hypothesis-removal fn-caps-begin-establishes-borrowed-merge success
(defthm capst-corrupted-begin-success-removal
 (let* ((s *caarrt-begun*) (a (fn-cp-nth 6 s)) (op '(:authority-begin (65) 0 1 7))
        (event (fn-caarrt-event s 1 op)) (one (fn-caa-begin s a event op)))
  (and (natp (fn-cp-nth 2 a))
       (natp (fn-cp-nth 4 op))
       (<= (fn-cp-nth 4 op) 7)
       (fn-caps-old-rowsp (fn-cp-nth 4 a) (fn-cp-nth 2 a))
       (not (equal (car one) :ok))
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a)))))
 :hints (("Goal" :in-theory (enable fn-caps-merge-relp fn-caps-suffixp fn-caps-old-rowsp)))
 :rule-classes nil)


; Executable counterparts of the identical ground witness formulas.
;@positive fn-caps-actual-row-preserves-borrowed-complete-merge
(assert-event (let* ((s *caarrt-begun*) (a *caarrt-new-a*) (event *caarrt-new-event*) (op *caarrt-new-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-row s a event op)))
  (and (fn-caps-merge-relp p installed)
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 (fn-cp-nth 5 p)))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (equal (car (fn-caa-row-plan a event op)) :stage)
       (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed))))

;@positive fn-caps-actual-row-preserves-borrowed-complete-merge
(assert-event (let* ((s *caarrt-retain-begun*) (a *caarrt-retain-a*) (event *caarrt-retain-event*) (op *caarrt-retain-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-row s a event op)))
  (and (fn-caps-merge-relp p installed)
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 (fn-cp-nth 5 p)))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (equal (car (fn-caa-row-plan a event op)) :stage)
       (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed))))

;@positive fn-caps-actual-row-preserves-borrowed-complete-merge
(assert-event (let* ((s *caarrt-rebirth-begun*) (a *caarrt-rebirth-a*) (event *caarrt-rebirth-event*) (op *caarrt-rebirth-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-row s a event op)))
  (and (fn-caps-merge-relp p installed)
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 (fn-cp-nth 5 p)))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (equal (car (fn-caa-row-plan a event op)) :stage)
       (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed))))

;@positive fn-caps-actual-tombstone-preserves-borrowed-complete-merge
(assert-event (let* ((s *caarrt-retain-begun*) (a *caarrt-retain-a*)
        (event *caarrt-tomb-event*) (op *caarrt-tomb-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-tombstone s a event op)))
  (and (fn-caps-merge-relp p installed)
       (equal (car (fn-caa-tombstone-plan a event op)) :stage)
       (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed))))

;@positive fn-caps-begin-establishes-borrowed-merge
(assert-event (let* ((s *caarrt-initial*) (a (fn-cp-nth 6 s)) (op '(:authority-begin (65) 0 1 7))
        (event (fn-caarrt-event s 1 op)) (one (fn-caa-begin s a event op)))
  (and (natp (fn-cp-nth 2 a))
       (natp (fn-cp-nth 4 op)) (<= (fn-cp-nth 4 op) 7)
       (fn-caps-old-rowsp (fn-cp-nth 4 a) (fn-cp-nth 2 a))
       (equal (car one) :ok)
       (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a)))))

;@positive fn-caps-begin-establishes-borrowed-merge
(assert-event (let* ((s *caarrt-published*) (a (fn-cp-nth 6 s)) (op '(:authority-begin (66) 1 3 7))
        (event (fn-caarrt-event s 6 op)) (one (fn-caa-begin s a event op)))
  (and (natp (fn-cp-nth 2 a))
       (natp (fn-cp-nth 4 op)) (<= (fn-cp-nth 4 op) 7)
       (fn-caps-old-rowsp (fn-cp-nth 4 a) (fn-cp-nth 2 a))
       (equal (car one) :ok)
       (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a)))))

;@positive fn-caps-begin-establishes-borrowed-merge
(assert-event (let* ((s *caarrt-tomb-published*) (a (fn-cp-nth 6 s)) (op '(:authority-begin (67) 2 8 7))
        (event (fn-caarrt-event s 11 op)) (one (fn-caa-begin s a event op)))
  (and (natp (fn-cp-nth 2 a))
       (natp (fn-cp-nth 4 op)) (<= (fn-cp-nth 4 op) 7)
       (fn-caps-old-rowsp (fn-cp-nth 4 a) (fn-cp-nth 2 a))
       (equal (car one) :ok)
       (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a)))))

;@hypothesis-removal fn-caps-actual-row-preserves-borrowed-complete-merge codec
(assert-event (let* ((s *caarrt-begun*) (a *caarrt-new-a*) (event *caarrt-new-event*) (op *caarrt-invalid-codec-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-row s a event op)))
  (and (fn-caps-merge-relp p installed)
       (not (fn-cac-operationp op))
       (fn-cp-authority-namespacep (fn-cp-nth 6 (fn-cp-nth 5 p)))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (equal (car (fn-caa-row-plan a event op)) :stage)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed)))))

;@hypothesis-removal fn-caps-actual-row-preserves-borrowed-complete-merge namespace
(assert-event (let* ((s *caarrt-begun*) (a *caarrt-no-namespace-a*) (event *caarrt-new-event*) (op *caarrt-new-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-row s a event op)))
  (and (fn-caps-merge-relp p installed)
       (fn-cac-operationp op)
       (not (fn-cp-authority-namespacep (fn-cp-nth 6 (fn-cp-nth 5 p))))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (equal (car (fn-caa-row-plan a event op)) :stage)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed)))))

;@hypothesis-removal fn-caps-actual-row-preserves-borrowed-complete-merge coordinate
(assert-event (let* ((s *caarrt-begun*) (a *caarrt-new-a*) (event *caarrt-wide-event*) (op *caarrt-wide-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-row s a event op)))
  (and (fn-caps-merge-relp p installed)
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 (fn-cp-nth 5 p)))
       (not (fn-cp-uintp (fn-cp-nth 2 event)))
       (equal (car (fn-caa-row-plan a event op)) :stage)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed)))))

;@hypothesis-removal fn-caps-actual-row-preserves-borrowed-complete-merge merge
(assert-event (let* ((s *caarrt-begun*) (a (update-nth 5 (update-nth 3 99 (fn-cp-nth 5 *caarrt-new-a*)) *caarrt-new-a*)) (event *caarrt-new-event*) (op *caarrt-new-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-row s a event op)))
  (and (not (fn-caps-merge-relp p installed))
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 (fn-cp-nth 5 p)))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (equal (car (fn-caa-row-plan a event op)) :stage)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed)))))

;@hypothesis-removal fn-caps-actual-row-preserves-borrowed-complete-merge success
(assert-event (let* ((s *caarrt-begun*) (a *caarrt-retain-a*) (event *caarrt-retain-event*) (op (update-nth 4 99 *caarrt-retain-op*))
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-row s a event op)))
  (and (fn-caps-merge-relp p installed)
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 (fn-cp-nth 5 p)))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (not (equal (car (fn-caa-row-plan a event op)) :stage))
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed)))))

;@hypothesis-removal fn-caps-actual-tombstone-preserves-borrowed-complete-merge merge
(assert-event (let* ((s *caarrt-retain-begun*) (a *caarrt-bad-token-a*)
        (event *caarrt-tomb-event*) (op *caarrt-tomb-op*)
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-tombstone s a event op)))
  (and (not (fn-caps-merge-relp p installed))
       (equal (car (fn-caa-tombstone-plan a event op)) :stage)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed)))))

;@hypothesis-removal fn-caps-actual-tombstone-preserves-borrowed-complete-merge success
(assert-event (let* ((s *caarrt-retain-begun*) (a *caarrt-retain-a*)
        (event *caarrt-tomb-event*) (op (update-nth 3 '(98) *caarrt-tomb-op*))
        (p (fn-cp-nth 5 a)) (installed (fn-cp-nth 4 a))
        (one (fn-caa-tombstone s a event op)))
  (and (fn-caps-merge-relp p installed)
       (not (equal (car (fn-caa-tombstone-plan a event op)) :stage))
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) installed)))))

;@hypothesis-removal fn-caps-begin-establishes-borrowed-merge watermark
(assert-event (let* ((s *caarrt-initial*) (a (update-nth 2 -1 (fn-cp-nth 6 s))) (op '(:authority-begin (65) 0 -1 7))
        (event (fn-caarrt-event s 1 op)) (one (fn-caa-begin s a event op)))
  (and (not (natp (fn-cp-nth 2 a)))
       (natp (fn-cp-nth 4 op))
       (<= (fn-cp-nth 4 op) 7)
       (fn-caps-old-rowsp (fn-cp-nth 4 a) (fn-cp-nth 2 a))
       (equal (car one) :ok)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a))))))

;@hypothesis-removal fn-caps-begin-establishes-borrowed-merge policy-natural
(assert-event (let* ((s *caarrt-initial*) (a (fn-cp-nth 6 s)) (op '(:authority-begin (65) 0 1 -1))
        (event (fn-caarrt-event s 1 op)) (one (fn-caa-begin s a event op)))
  (and (natp (fn-cp-nth 2 a))
       (not (natp (fn-cp-nth 4 op)))
       (<= (fn-cp-nth 4 op) 7)
       (fn-caps-old-rowsp (fn-cp-nth 4 a) (fn-cp-nth 2 a))
       (equal (car one) :ok)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a))))))

;@hypothesis-removal fn-caps-begin-establishes-borrowed-merge policy-range
(assert-event (let* ((s *caarrt-initial*) (a (fn-cp-nth 6 s)) (op '(:authority-begin (65) 0 1 8))
        (event (fn-caarrt-event s 1 op)) (one (fn-caa-begin s a event op)))
  (and (natp (fn-cp-nth 2 a))
       (natp (fn-cp-nth 4 op))
       (not (<= (fn-cp-nth 4 op) 7))
       (fn-caps-old-rowsp (fn-cp-nth 4 a) (fn-cp-nth 2 a))
       (equal (car one) :ok)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a))))))

;@hypothesis-removal fn-caps-begin-establishes-borrowed-merge oldrows
(assert-event (let* ((s *caarrt-initial*) (a (update-nth 4 '((:account (97) nil nil nil)) (fn-cp-nth 6 s))) (op '(:authority-begin (65) 0 1 7))
        (event (fn-caarrt-event s 1 op)) (one (fn-caa-begin s a event op)))
  (and (natp (fn-cp-nth 2 a))
       (natp (fn-cp-nth 4 op))
       (<= (fn-cp-nth 4 op) 7)
       (not (fn-caps-old-rowsp (fn-cp-nth 4 a) (fn-cp-nth 2 a)))
       (equal (car one) :ok)
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a))))))

;@hypothesis-removal fn-caps-begin-establishes-borrowed-merge success
(assert-event (let* ((s *caarrt-begun*) (a (fn-cp-nth 6 s)) (op '(:authority-begin (65) 0 1 7))
        (event (fn-caarrt-event s 1 op)) (one (fn-caa-begin s a event op)))
  (and (natp (fn-cp-nth 2 a))
       (natp (fn-cp-nth 4 op))
       (<= (fn-cp-nth 4 op) 7)
       (fn-caps-old-rowsp (fn-cp-nth 4 a) (fn-cp-nth 2 a))
       (not (equal (car one) :ok))
       (not (fn-caps-merge-relp
        (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a))))))

