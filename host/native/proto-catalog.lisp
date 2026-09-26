;;; host/native/proto-catalog.lisp -- the attach-stobj prototype's smoke verb
;;; (wave 5, lane consolidation-design, 2026-09-26; developer image only).
;;;
;;; `fn proto-catalog` runs the fold of books/proto-catalog-fold.lisp on the
;;; image's live `fn-pcat' (books/proto-catalog.lisp, an attachable abstract
;;; stobj) and prints what ACL2 computed and WHICH FOUNDATION the live
;;; object has.  The image includes books/proto-catalog-arena.lisp, which
;;; attaches `fn-arena' (books/payload-arena.lisp) before `fn-pcat' is
;;; introduced, so the live object is the arena's concrete stobj: five
;;; fields (buf, off, size, count, fill); the generic's own foundation has
;;; one (items).  The values are ACL2's (fn-pcat-smoke); this file only
;;; reads the live object's field count, which is a fact about the image,
;;; not a decision.

(in-package "ACL2")

(defun fnn-live-pcat ()
  (or (cdr (assoc 'fn-pcat (user-stobj-alist *the-live-state*)))
      (fnn-fault "the catalog prototype stobj is not in this image")))

(defun fnn-command-proto-catalog (args)
  (declare (ignore args))
  (let* ((live (fnn-live-pcat))
         (fields (if (simple-vector-p live) (length live) -1))
         (answer (fnn-call 'fn-pcat-smoke live))
         (result (first answer)))
    (unless (and (consp result) (= (length result) 4))
      (fnn-fault "the catalog prototype returned a malformed result"))
    (fnn-out "proto-catalog count=~d total=~d payload1=~a get02=~d foundation=~a fields=~d"
             (first result) (second result) (third result) (fourth result)
             (case fields (5 "arena") (1 "list") (t "unknown")) fields)
    +fnn-exit-ok+))

(fnn-register-developer-verb "proto-catalog" #'fnn-command-proto-catalog)
