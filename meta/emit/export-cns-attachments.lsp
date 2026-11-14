; From the repository root, under an allocated tools/acl2 session, after this
; exact consumer has a current record certificate. Not for a shared REPL (exits).
(in-package "ACL2")
(set-ld-error-action '(:exit 2) state)
(set-cbd "meta/emit/")
(include-book "../../books/cns-attachment-evidence" :uncertified-okp nil)
(fn2-av-export "../../build/cns-attachments.sexp" *fn2-av-cns-pairs* state)
(good-bye)
