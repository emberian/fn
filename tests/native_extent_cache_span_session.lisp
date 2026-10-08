;;; Enter the developer image's genuine ACL2 loop to admit the span export,
;;; then run the raw host fixture after that loop has returned to Common Lisp.
;;; No proof trust tag and no decision/dispatcher replacement is introduced.
(in-package "ACL2")
; This entry comes from the required developer image, never a test stub.
(defparameter *roots* '(fnn-command-acl2))
(dolist (name *roots*) (assert (fboundp name)))
; Saved operator images start LD without LP's connected-directory setup.
; Restore that ordinary session state before INCLUDE-BOOK, not a proof mode.
(f-put-global 'connected-book-directory (namestring (truename ".")) *the-live-state*)
(fnn-command-acl2 "session" nil)
(if (sb-ext:posix-getenv "FN_XC2_FIXTURE")
    (load "tests/native_extent_decoded_span.lisp")
  (load "tests/native_extent_cache_span.lisp"))
(sb-ext:exit :code 0)
