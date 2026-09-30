(in-package "ACL2")
(include-book "../../books/consumer-remote-history")

; Real concrete local stobj; allocation/reset below is fixture-only.
(defun fn-crpht-exec (s key rows)
 (declare (xargs :guard (true-listp rows) :verify-guards nil))
 (with-local-stobj fn-hist
  (mv-let (out fn-hist)
   (let ((fn-hist (fn-hist-load rows 0 fn-hist)))
    (mv (fn-crph-tick s key fn-hist) fn-hist))
   out)))

;@positive fn-crph-concrete-one-row-read-refines-complete-answer
; The correspondence is unconditional, so there is no hypothesis to remove.
(assert-event
 (let* ((row (fn-held-plain (fn-record-make 0 1 1 "<remote@fn.test>" '(65)
                                          '("a" "b") "o" "s" "r" 1 841000000) 0))
        (s (fn-crps-state '(key) nil nil '((97) (98)) 0 1 1 :read nil nil nil))
        (rows (list row)) (answer (fn-crpht-exec s '(key) rows)))
  (and (equal answer (fn-crph-reference s '(key) rows))
       (eq (fn-cp-nth 0 answer) :yield)
       (equal (fn-cp-nth 9 (fn-cp-nth 1 answer)) row))))

(assert-event
 (let ((s (fn-crps-state '(key) nil nil '((97)) 0 1 1 :read nil nil nil)))
  (and (equal (fn-crpht-exec s '(key) nil) (fn-crph-reference s '(key) nil))
       (equal (fn-crpht-exec s '(key) nil) '(:unavailable :history 0))
       (equal (fn-crpht-exec s '(changed) nil) '(:refused :consumer-source-changed)))))

; Already borrowed matching phases never fetch another history row.
(assert-event
 (let* ((row (fn-held-plain (fn-record-make 0 1 1 "<remote@fn.test>" '(65)
                                          '("a") "o" "s" "r" 1 841000000) 0))
        (s (fn-crps-state '(key) nil nil '((97)) 0 1 1 :match row '("a") '((97))))
        (answer (fn-crpht-exec s '(key) nil)))
  (and (equal answer (fn-crph-reference s '(key) nil))
       (eq (fn-cp-nth 0 answer) :poll) (equal (fn-cp-nth 2 answer) row))))
