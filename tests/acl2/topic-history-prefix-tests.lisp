(in-package "ACL2")
(include-book "../../books/topic-history-prefix")
(include-book "topic-history-admission-tests")
(include-book "std/testing/must-fail" :dir :system)

; This is the recovery step's historical context after T10 completed the
; root event. The topic event cannot supply its own source or snapshot.
(defconst *thpx-before*
  (fn-th-prefix-state :ok 8 (list *tha-snapshot*)
                      (list *tha-event*) nil nil))
(make-event `(defconst *thpx-anchor*
               ',(fn-th-prefix-step *thpx-before* *thad-anchor-event*
                                    *tha-principal*)))
(assert-event (equal (fn-th-at 0 *thpx-anchor*) :ok))
(assert-event (equal (fn-th-at 8
                      (fn-th-find-anchor *thad-topic*
                                         (fn-th-at 4 *thpx-anchor*)))
                     2))
(assert-event
 (equal (fn-th-at 0
         (fn-th-prefix-step *thpx-before* *thad-anchor-event*
                            *tha-other-principal*))
        :fault))
(assert-event
 (equal (fn-th-at 0
         (fn-th-prefix-step
          (fn-th-prefix-state :ok 8 nil (list *tha-event*) nil nil)
          *thad-anchor-event* *tha-principal*))
        :fault))
(assert-event
 (equal (fn-th-at 0
         (fn-th-prefix-step
          (fn-th-prefix-state :ok 8 (list *tha-snapshot*) nil nil nil)
          *thad-anchor-event* *tha-principal*))
        :fault))
(assert-event
 (equal (fn-th-at 0
         (fn-th-prefix-step *thpx-before* *thad-anchor-event*
                            *tha-principal*))
        :ok))
(must-fail
 (assert-event
  (equal (fn-th-at 0
          (fn-th-prefix-step
           (fn-th-prefix-state :ok 8 (list *tha-snapshot*) nil nil nil)
           *thad-anchor-event* *tha-principal*))
         :ok)))
