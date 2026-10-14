; One-world tooth, part 1 (lane vertical-one-world, OW3; A25 2026-10-13).
;
; The old shape: a computed defconst whose initializer runs
; with-local-stobj fn-arena (the pre-720fac332 *hrt-rows* of
; held-rows-tests).  A compiled defconst re-evaluates its initializer when
; the FASL loads, with the creator the world selected at compile time.  This
; book is certified in the world its includes give it.
; tests/acl2/one-world-hole-attached-tests.lisp includes it after the host
; arena path: at dev (two worlds) that session is illegal to certify; after
; the one-world move (the generic exists only attached) it is legal.  Both
; books stay unchanged across the move; they are the landing's tooth.
(in-package "ACL2")
(include-book "../../books/catalog-record")

; A ground wire record: "Subject: a" CRLF CRLF "line1" CRLF.
(defconst *owh-w*
  (fn-record-make 0 1 0 "<owh@example.invalid>"
                  (append (fn-record-string-octets "Subject: a") '(13 10 13 10)
                          (fn-record-string-octets "line1") '(13 10))
                  '("fn.test") "o" "s" "e" 1 5))

; The held row of W interned on a fresh arena.
(defun fn-owh-intern (w)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (held fn-arena)
      (fn-cat-intern-list w nil 0 fn-arena)
      held)))

; The hole: this initializer runs again when the compiled file loads.
(defconst *owh-held* (fn-owh-intern *owh-w*))
(assert-event (fn-held-p *owh-held*))
(assert-event (equal (fn-record-payload *owh-held*) 0))
