; fn: the catalog prototype with the ARENA attached (wave 5, lane
; consolidation-design, 2026-09-26).
;
; Three events, in this order, are the whole mechanism:
;   1. the implementation is introduced (`fn-arena', books/payload-arena.lisp:
;      the byte array with an offset and a size per handle);
;   2. `(attach-stobj fn-pcat fn-arena)' names it as the attachment of a
;      stobj not yet introduced;
;   3. the generic is introduced (`fn-pcat', books/proto-catalog.lisp,
;      `:attachable t'), and BECAUSE the attachment precedes it, its
;      foundation and every export's executable are the arena's, while its
;      logical side is unchanged (attach-stobj requires the two to share
;      their :logic functions, which they do by construction).
; A book certified over the generic (books/proto-catalog-fold.lisp) is then
; included unchanged: its certificate is the generic's, and its functions
; run over the arena.  The image (host/native/build.lisp) includes THIS
; book, so a developer image runs `fn-pcat' over the arena.
;
; What runs at certification time (skipped by include-book, as the demo
; does it): the fold over the live `fn-pcat', whose foundation is now the
; arena's concrete stobj, five fields; the list-backed one has one.

(in-package "ACL2")
(include-book "payload-arena")
(attach-stobj fn-pcat fn-arena)
(include-book "proto-catalog")
(include-book "proto-catalog-fold")

; The exec path on the live generic under the attachment: three seals, the
; total, a read, a clear.  The value is the logical one either way; the
; foundation is the arena's.
(defun fn-pcat-smoke (fn-pcat)
  (declare (xargs :stobjs fn-pcat))
  (let* ((fn-pcat (fn-pcat-clear fn-pcat))
         (fn-pcat (fn-pcat-seal-many '((1 2 3) (4 5) nil) fn-pcat))
         (result (list (fn-pcat-count fn-pcat)
                       (fn-pcat-total 3 fn-pcat)
                       (fn-pcat-payload 1 fn-pcat)
                       (fn-pcat-get 0 2 fn-pcat))))
    (mv result fn-pcat)))

(value-triple (fn-pcat-smoke fn-pcat) :stobjs-out '(nil fn-pcat))

(assert-event (equal (mv-let (result fn-pcat) (fn-pcat-smoke fn-pcat)
                       (mv result fn-pcat))
                     '(3 5 (4 5) 3))
              :stobjs-out '(nil fn-pcat))
