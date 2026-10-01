(in-package "ACL2")
(include-book "../../books/consumer-remote-visibility")

(defconst *crv-target* (fn-make-article "<a>" 1 '("a") '(("a" . 1)) t nil))
(defconst *crv-cause* (fn-make-article "<c>" 2 '("b") '(("b" . 1)) t nil))
(defconst *crv-row-target* '(0 0 0 "<a>" 1 ("a")))
(defconst *crv-row-cause* '(1 1 0 "<c>" 2 ("b")))
(defun fn-crv-test-view (visible withdrawn records)
 (declare (xargs :guard t))
 (list 2 2 (fn-make-state '("a" "b") nil visible 2 nil nil)
       nil nil nil records nil withdrawn nil))
(defun fn-crv-test-run (fuel result key)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (or (zp fuel) (not (eq (fn-cp-nth 0 result) :yield))) result
  (fn-crv-test-run (- fuel 1) (fn-crv-tick (fn-cp-nth 1 result) key) key)))

(assert-event
 (let* ((view (fn-crv-test-view (list *crv-target*) nil nil))
        (start (fn-crv-begin '(key) *crv-row-target* view)))
  (and (eq (car (fn-crv-test-run 1 start '(key))) :yield)
       (equal (fn-crv-test-run 8 start '(key)) (list :visible *crv-target*)))))

(assert-event
 (let* ((view (fn-crv-test-view nil (list *crv-target*) nil))
        (answer (fn-crv-test-run 8 (fn-crv-begin '(key) *crv-row-target* view) '(key))))
  (and (eq (car answer) :withdrawn) (equal (cadr answer) *crv-target*)
       (equal (fn-crv-test-run 8 (list :yield (caddr answer)) '(key)) '(:excluded :retired-or-not-visible)))))

; A visible cancel in b MUST first expose its target in a to query selection.
; The target result never contains the cause's payload/groups as its article.
(assert-event
 (let* ((view (fn-crv-test-view (list *crv-cause*) (list *crv-target*)
                 '((:withdrawal "<a>" "<c>" nil nil 0 nil))))
        (answer (fn-crv-test-run 8 (fn-crv-begin '(key) *crv-row-cause* view) '(key))))
  (and (eq (car answer) :withdrawal-target) (equal (cadr answer) *crv-target*)
       (equal (fn-crv-query-tick '(key) '(key) (fn-article-groups (cadr answer)) '((97)) '((97))) '(:query-match))
       (not (equal (cadr answer) *crv-cause*))
       (equal (fn-crv-test-run 8 (list :yield (caddr answer)) '(key)) (list :visible *crv-cause*)))))

(assert-event
 (let ((start (fn-crv-begin '(key) *crv-row-target* (fn-crv-test-view nil nil nil))))
  (and (equal (fn-crv-test-run 8 start '(key)) '(:excluded :retired-or-not-visible))
       (equal (fn-crv-tick (cadr start) '(changed)) '(:refused :remote-view-source-changed))
       (equal (fn-crv-query-tick '(key) '(key) '("b") '((97)) '((97))) '(:yield ("b") nil))
       (equal (fn-crv-query-tick '(key) '(key) '("b") nil '((97))) '(:yield nil ((97)))))))
