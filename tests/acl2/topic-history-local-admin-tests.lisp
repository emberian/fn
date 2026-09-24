(in-package "ACL2")
(include-book "../../books/topic-history-local-admin")
(include-book "topic-history-admission-tests")
(include-book "std/testing/must-fail" :dir :system)

; A store-specific entropy observation, distinct from the UID and all T10
; principals.  The host's connected same-euid gate supplies the UID only.
(defconst *thla-id* (make-list 32 :initial-element 61))
(defconst *thla-install-result*
  (fn-th-local-admin-install 7 8 10 501 *thla-id* nil))
(assert-event (fn-stmt-okp *thla-install-result*))
(defconst *thla-install* (fn-stmt-value *thla-install-result*))
(assert-event
 (equal (fn-th-local-admin-commit *thla-install* nil)
        (fn-stmt-ok *thla-install*)))
(assert-event
 (equal (fn-th-local-admin-current-id *thla-install* 501) *thla-id*))
(assert-event
 (null (fn-th-local-admin-current-id *thla-install* 502)))
(assert-event
 (equal (fn-th-local-admin-install 9 10 10 501 *thla-id*
                                   *thla-install*)
        (fn-stmt-error :already-installed)))
(make-event `(defconst *thla-anchor*
               ',(fn-th-prepare-anchor-local
                  8 9 10 *tha-event* *tha-snapshot* 501 2
                  *thla-install* nil)))
(assert-event (fn-stmt-okp *thla-anchor*))
(assert-event (equal (fn-th-at 7 (fn-stmt-value *thla-anchor*))
                     *thla-id*))
(assert-event (equal (len (fn-stmt-value *thla-anchor*)) 9))
(assert-event (equal (fn-th-at 8 (fn-stmt-value *thla-anchor*)) 10))
(assert-event
 (equal (fn-th-commit-anchor-installed-v2
         (fn-stmt-value *thla-anchor*) *tha-event* *tha-snapshot*
         *thla-install* nil)
        (fn-th-commit-anchor
         (fn-th-anchor-v1-fields (fn-stmt-value *thla-anchor*))
         *tha-event* *tha-snapshot* *thla-id* nil)))
(assert-event
 (equal (fn-th-commit-anchor-installed-v2
         (fn-stmt-value *thla-anchor*) *tha-event* *tha-snapshot*
         (list :topic-admin-install 7 8 11 501 *thla-id*) nil)
        (fn-stmt-error :administrator-generation)))
(assert-event
 (equal (fn-th-prepare-anchor-local
         8 9 10 *tha-event* *tha-snapshot* 502 2
         *thla-install* nil)
        (fn-stmt-error :administrator)))
(must-fail
 (assert-event
  (fn-stmt-okp
   (fn-th-prepare-anchor-local
    8 9 10 *tha-event* *tha-snapshot* 502 2
    *thla-install* nil))))
