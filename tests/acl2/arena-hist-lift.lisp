; Test helper (lane history-columns-3): bpr-lift for a reader that also takes
; the history stobj fn-hist after fn-arena.  (bpr-lift-hist F n HIST) defines
; (in-arena-F payloads x1 .. xn) = (F x1 .. xn fn-arena fn-hist) over a local
; arena holding PAYLOADS and a local history stobj loaded with HIST (a term
; over x1 .. xn: the history the reader's Store holds, so R holds by
; construction).  (in-arena-F-nohist ...) runs it over an EMPTY stobj: the
; removal witness for R.
(in-package "ACL2")
(include-book "arena-lift")
(include-book "../../books/history-columns")

(defmacro bpr-lift-hist (fn nargs hist)
  (let ((xs (bpr-lift-vars nargs))
        (a (packn (list 'in-arena-a- fn)))
        (b (packn (list 'in-arena- fn)))
        (c (packn (list 'in-arena- fn '-nohist))))
    `(progn
       (defun ,a (payloads ,@xs load fn-arena)
         (declare (xargs :stobjs fn-arena :verify-guards nil))
         (let ((fn-arena (fn-arn-seal-many payloads fn-arena)))
           (with-local-stobj fn-hist
             (mv-let (r fn-hist)
               (let ((fn-hist (fn-hist-load (if load (true-list-fix ,hist) nil) 0 fn-hist)))
                 (mv (,fn ,@xs fn-arena fn-hist) fn-hist))
               (mv r fn-arena)))))
       (defun ,b (payloads ,@xs)
         (declare (xargs :verify-guards nil))
         (with-local-stobj fn-arena
           (mv-let (r fn-arena) (,a payloads ,@xs t fn-arena) r)))
       (defun ,c (payloads ,@xs)
         (declare (xargs :verify-guards nil))
         (with-local-stobj fn-arena
           (mv-let (r fn-arena) (,a payloads ,@xs nil fn-arena) r))))))
