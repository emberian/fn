; Literal candidate custody witness for the actual resident source transition.
; Structural fixture only: no typed Store, private schema or allocation grant.
(in-package "ACL2")
(include-book "../../books/admission-semantic-census-lineage")
(defconst *rccap-test-committed* (fn-sl-of '(:committed)))
(defconst *rccap-test-target* (fn-sfr-snoc *rccap-test-committed* :candidate))
(defconst *rccap-test-begin*
 (fn-osrc-begin *rccap-test-target* 2 19 '(31 2)))
(defconst *rccap-test-c1* (fn-osrc-at 1 (fn-osrc-tick *rccap-test-begin* nil)))
(defconst *rccap-test-c2* (fn-osrc-at 1 (fn-osrc-tick *rccap-test-c1* nil)))
(defconst *rccap-test-c3* (fn-osrc-at 1 (fn-osrc-tick *rccap-test-c2* nil)))
(defconst *rccap-test-c4* (fn-osrc-at 1 (fn-osrc-tick *rccap-test-c3* nil)))
(defconst *rccap-test-candidate-cursor*
 (fn-osrc-at 4 (fn-osrc-tick *rccap-test-c4* nil)))
; Complete antecedent and conclusion for both maintained begin and candidate
; selection. Exact field and ordinal are checked, not guessed from token shape.
(thm
 (and (fn-sfr-canonp *rccap-test-committed*)
      (equal (fn-sfr-list *rccap-test-target*) '(:committed :candidate))
      (equal (fn-sfr-count *rccap-test-target*) 2)
      (fn-rccos-cursor-invariantp *rccap-test-begin*)
      (equal (fn-osrc-at 1 *rccap-test-candidate-cursor*)
             (fn-sfr-snoc *rccap-test-committed* :candidate))
      (fn-rccos-cursor-invariantp *rccap-test-candidate-cursor*)
      (equal (fn-osrc-at 2 *rccap-test-candidate-cursor*)
             (fn-sfr-count *rccap-test-committed*))
      (eq (car (fn-osrc-tick *rccap-test-candidate-cursor* nil)) :row)
      (eq (fn-osrc-at 0 (fn-osrc-at 2
                         (fn-osrc-tick *rccap-test-candidate-cursor* nil))) :resident)
      (equal (fn-osrc-at 1 (fn-osrc-at 2
                            (fn-osrc-tick *rccap-test-candidate-cursor* nil)))
             :candidate))
 :hints (("Goal" :in-theory (enable fn-rccos-cursor-invariantp
                                  fn-rccos-base fn-rccos-suffix))))
; Mutation witness: changing the cursor's retained candidate breaks the
; maintained capture relation even when count, epoch and nonce remain equal.
(thm
 (let* ((bad (update-nth 8 '(:substituted) *rccap-test-candidate-cursor*))
        (actual (fn-osrc-tick bad nil)))
  (and (fn-rccos-cursor-invariantp *rccap-test-candidate-cursor*)
       (equal (fn-osrc-at 1 bad) *rccap-test-target*)
       (equal (fn-osrc-at 2 bad) 1)
       (equal (fn-osrc-at 9 bad) 19)
       (equal (fn-osrc-at 10 bad) '(31 2))
       (not (fn-rccos-cursor-invariantp bad))
       (eq (car actual) :row)
       (eq (fn-osrc-at 0 (fn-osrc-at 2 actual)) :resident)
       (not (equal (fn-osrc-at 1 (fn-osrc-at 2 actual)) :candidate))))
 :hints (("Goal" :in-theory (enable fn-rccos-cursor-invariantp
                                  fn-rccos-base fn-rccos-suffix))))
