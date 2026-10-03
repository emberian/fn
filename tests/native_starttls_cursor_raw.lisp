;;; Execute actual TLS receipt and its structural leaves from source.
;;; This is a raw transition fixture, not ACL2 guard/certification evidence.
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defmacro mbe (&key logic exec) (declare (ignore logic)) exec)
(defun nfix (x) (if (and (integerp x) (<= 0 x)) x 0))
(defun zp (x) (<= (nfix x) 0))
(defun load-transition-definitions (path names)
  (let ((seen nil))
    (with-open-file (s path)
      (loop for form = (read s nil :eof) until (eq form :eof) do
        (when (and (consp form) (eq (car form) 'defun) (member (cadr form) names))
          (eval (append (subseq form 0 3)
                        (remove-if (lambda (x) (and (consp x) (eq (car x) 'declare)))
                                   (cdddr form))))
          (push (cadr form) seen))))
    (unless (null (set-difference names seen)) (error "missing source subjects in ~a" path))))
(load-transition-definitions "books/acceptance-alloc.lisp" '(fn-ag-car fn-ag-cdr))
(load-transition-definitions "books/injection-shape.lisp" '(fn-inj-car fn-inj-cdr fn-inj-nth))
(load-transition-definitions "books/nntp-session.lisp"
 '(fn-nntp-session-openp fn-nntp-session-group fn-nntp-session-current
   fn-nntp-session-projected fn-nntp-make-session fn-nntp-set-cursor))
(load-transition-definitions "books/nntp-post.lisp"
 '(fn-post-session-base fn-post-session-awaiting fn-post-make-session
   fn-post-result-session fn-post-make-result))
(load-transition-definitions "books/peer-inbound.lisp"
 '(fn-peer-session-base fn-peer-session-peer fn-peer-session-transfer
   fn-peer-session-inflight fn-peer-session-node fn-peer-session-cfg
   fn-peer-session-refused fn-peer-make-session fn-peer-with-base))
(load-transition-definitions "books/nntp-compress.lisp" '(fn-zc-owedp fn-zc-established))
(load-transition-definitions "books/nntp-auth.lisp"
 '(fn-auth-session-base fn-auth-session-config fn-auth-session-pending
   fn-auth-session-subject fn-auth-session-tlsp fn-auth-session-handshakingp
   fn-auth-session-compress fn-auth-session-ctx fn-auth-session-failures
   fn-auth-make-session fn-auth-tls-reader-base fn-auth-tls-established))
(let* ((reader (fn-nntp-make-session t "fn.letters" 7 t))
       (peer (fn-peer-make-session (fn-post-make-session reader nil)
                                  "configured-peer" nil 0 'node 'config 'refused))
       (as (fn-auth-make-session peer 'authcfg nil nil nil t nil nil 2))
       (out (fn-post-result-session (fn-auth-tls-established as)))
       (base (fn-auth-session-base out))
       (cursor (fn-post-session-base (fn-peer-session-base base))))
  (assert (equal cursor '(t nil nil t)))
  (assert (equal (cdr base) (cdr peer)))
  (assert (fn-auth-session-tlsp out))
  (assert (not (fn-auth-session-handshakingp out)))
  ;; Same receipt when compression is owed MUST preserve the entire base.
  (let* ((compressing (fn-auth-make-session peer 'authcfg 'login 'subject t t
                                           '(:owed :deflate) 'ctx 2))
         (compressed (fn-post-result-session (fn-auth-tls-established compressing))))
    (assert (equal (fn-auth-session-base compressed) peer))
    (assert (equal (fn-auth-session-compress compressed) '(:active :deflate)))))
(format t "actual STARTTLS cursor reset / compression preservation passed~%")
