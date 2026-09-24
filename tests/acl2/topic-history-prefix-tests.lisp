(in-package "ACL2")
(include-book "../../books/topic-history-prefix")
(include-book "topic-history-admission-tests")
(include-book "topic-history-local-admin-tests")
(include-book "std/testing/must-fail" :dir :system)

; This is the recovery step's historical context after T10 completed the
; root event. The topic event cannot supply its own source or snapshot.
(defconst *thpx-before-install*
  (fn-th-prefix-state :ok 7 (list *tha-snapshot*)
                      (list *tha-event*) nil nil nil))
(defconst *thpx-before*
  (fn-th-prefix-step *thpx-before-install* *thla-install*))
(assert-event (equal (fn-th-at 0 *thpx-before*) :ok))
(make-event `(defconst *thpx-anchor*
               ',(fn-th-prefix-step *thpx-before*
                                    (fn-stmt-value *thla-anchor*))))
(assert-event (equal (fn-th-at 0 *thpx-anchor*) :ok))
(assert-event
 (equal (fn-th-at 0
         (fn-th-prefix-step
          (fn-th-prefix-state :ok 8 (list *tha-snapshot*)
                              (list *tha-event*) nil
                              (list :topic-admin-install 7 8 11 501
                                    *thla-id*) nil)
          (fn-stmt-value *thla-anchor*)))
        :fault))
; A historical v1 anchor still has its original ID-only replay meaning.
(assert-event
 (equal (fn-th-at 0
         (fn-th-prefix-step
          (fn-th-prefix-state :ok 8 (list *tha-snapshot*)
                              (list *tha-event*) nil
                              (list :topic-admin-install 7 8 11 501
                                    *thla-id*) nil)
          (fn-th-anchor-v1-fields (fn-stmt-value *thla-anchor*))))
        :ok))
(assert-event (equal (fn-th-at 8
                      (fn-th-find-anchor *thad-topic*
                                         (fn-th-at 4 *thpx-anchor*)))
                     2))
(assert-event
 (equal (fn-th-at 0
         (fn-th-prefix-step
          (fn-th-prefix-state :ok 8 (list *tha-snapshot*)
                              (list *tha-event*) nil
                              (list :topic-admin-install 7 8 10 501
                                    (make-list 32 :initial-element 62)) nil)
          (fn-stmt-value *thla-anchor*)))
        :fault))
(assert-event
 (equal (fn-th-at 0
         (fn-th-prefix-step
          (fn-th-prefix-state :ok 8 nil (list *tha-event*) nil
                              *thla-install* nil)
          (fn-stmt-value *thla-anchor*)))
        :fault))
(assert-event
 (equal (fn-th-at 0
         (fn-th-prefix-step
          (fn-th-prefix-state :ok 8 (list *tha-snapshot*) nil nil
                              *thla-install* nil)
          (fn-stmt-value *thla-anchor*)))
        :fault))
(assert-event
 (equal (fn-th-at 0
         (fn-th-prefix-step *thpx-before*
                            (fn-stmt-value *thla-anchor*)))
        :ok))
(must-fail
 (assert-event
  (equal (fn-th-at 0
          (fn-th-prefix-step
           (fn-th-prefix-state :ok 8 (list *tha-snapshot*) nil nil
                               *thla-install* nil)
           (fn-stmt-value *thla-anchor*)))
         :ok)))
