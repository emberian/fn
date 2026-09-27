; Test helper (records-flip, flip-L4): a top-level test form cannot bind a
; stobj, so a call of an arena reader is lifted into a function that seals
; the test's payloads into a local arena first.
(in-package "ACL2")
(include-book "../../books/payload-arena")

;; A top-level call of an arena reader F runs over a local arena holding
;; PAYLOADS at handles 0, 1, ...: (bpr-lift F n) defines
;; (in-arena-F payloads x1 .. xn) = (F x1 .. xn fn-arena) over that arena.
(defun bpr-lift-vars (n)
  (declare (xargs :mode :program))
  (if (zp n) nil (append (bpr-lift-vars (1- n)) (list (packn (list 'x n))))))
(defmacro bpr-lift (fn nargs)
  (let ((xs (bpr-lift-vars nargs))
        (a (packn (list 'in-arena-a- fn)))
        (b (packn (list 'in-arena- fn))))
    `(progn
       (defun ,a (payloads ,@xs fn-arena)
         (declare (xargs :stobjs fn-arena :verify-guards nil))
         (let ((fn-arena (fn-arn-seal-many payloads fn-arena)))
           (mv (,fn ,@xs fn-arena) fn-arena)))
       (defun ,b (payloads ,@xs)
         (declare (xargs :verify-guards nil))
         (with-local-stobj fn-arena
           (mv-let (r fn-arena) (,a payloads ,@xs fn-arena) r))))))
