; fn: the extraction's keyword dispatch (lane extract-writable, E2).
;
; The served command dispatch tests a command's keyword against literal
; texts, `(fn-nntp-keywordp keyword "ARTICLE")', hundreds of times per
; command in the reader's cond chains (books/nntp.lisp, served-catalog.lisp,
; nntp-auth.lisp ...).  Each test upcases the whole keyword into a fresh list
; and converts the literal text to octets again: the extracted program's two
; costliest functions (planning/evidence/extract-2-2026-09-28.md section e5).
;
; `fn-nntp-keyword-octets-equal' compares the keyword with the literal's
; octets directly, a byte at a time, upcasing each byte as it goes: no list is
; built, and a test against another keyword stops at the first differing
; byte.  The keystone below says it IS the dispatch test on the literal's
; octets, for every token and text; the extractor (tools/extract/frontend.lisp
; *xt-rewrites*) replaces a call whose text is a constant by it, the octets
; then folded to a constant, and checks that this theorem is in the world
; with exactly this statement before it does.  Nothing the image runs changes.

(in-package "ACL2")
(include-book "nntp-syntax")

(defun fn-nntp-keyword-octets-equal (token octets)
  (declare (xargs :guard t))
  (if (consp token)
      (and (consp octets)
           (equal (fn-nntp-upcase-byte (car token)) (car octets))
           (fn-nntp-keyword-octets-equal (cdr token) (cdr octets)))
    (equal octets nil)))

(local
 (defthm fn-nntp-keyword-octets-equal-is-upcase-equal
   (equal (fn-nntp-keyword-octets-equal token octets)
          (equal (fn-nntp-upcase-keyword token) octets))
   :hints (("Goal" :induct (fn-nntp-keyword-octets-equal token octets)
            :in-theory (enable fn-nntp-upcase-keyword)))))

(defthm fn-nntp-keywordp-is-octets-equal
  (equal (fn-nntp-keywordp token text)
         (fn-nntp-keyword-octets-equal token (fn-nntp-string-octets text)))
  :hints (("Goal" :in-theory (enable fn-nntp-keywordp))))
