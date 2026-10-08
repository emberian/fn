;;; Enter the developer image's genuine ACL2 loop to admit the span export,
;;; then run the raw host fixture after that loop has returned to Common Lisp.
;;; No proof trust tag and no decision/dispatcher replacement is introduced.
(in-package "ACL2")
; This entry comes from the required developer image, never a test stub.
(defparameter *roots* '(fnn-command-acl2))
(dolist (name *roots*) (assert (fboundp name)))
(fnn-command-acl2 "session" nil)
(load "tests/native_extent_cache_span.lisp")
(sb-ext:exit :code 0)
