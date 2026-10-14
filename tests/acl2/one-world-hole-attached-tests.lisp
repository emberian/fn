; One-world tooth, part 2 (lane vertical-one-world, OW3; A25 2026-10-13).
;
; The host arena path first (host/page-read-host includes the arena the way
; the image does), then the computed-initializer book.  At dev the arena is
; attached by books/payload-arena-attach before the generic, while
; one-world-hole-tests was compiled in the plain world, so its FASL's
; initializer hands the list foundation to the attached exports and the
; session is illegal to certify (CHK-ABSSTOBJ-INVARIANTS).  After the move
; this book certifies unchanged.
(in-package "ACL2")
(include-book "../../host/page-read-host")
(include-book "one-world-hole-tests")
(assert-event (fn-held-p *owh-held*))
