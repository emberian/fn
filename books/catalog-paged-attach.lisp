; fn: the catalog's PAGED implementation ATTACHED to the generic (stage 3 of
; planning/design-store-representation-2026-10-01.md, lane paged-catalog,
; 2026-10-01; the arena's precedent is books/payload-arena-attach.lisp).
;
; Three events, in this order, are the whole mechanism:
;   1. the implementation is introduced (`fn-cat-paged',
;      books/catalog-paged.lisp: typed columns and a byte pool for the rows,
;      the old foundation nested for the tables);
;   2. `(attach-stobj fn-cat fn-cat-paged)' names it as the attachment of a
;      stobj not yet introduced;
;   3. the generic is introduced (`fn-cat', books/catalog.lisp,
;      `:attachable t'), and BECAUSE the attachment precedes it, its
;      foundation and every export's executable are the paged ones, while
;      its logical side is unchanged (the two share their :logic functions
;      by construction).
; A book certified over the generic -- the served catalog and everything
; above it -- is then included unchanged: its certificate is the generic's,
; and its functions run over the columns.  An image that includes THIS
; book before any book that names `fn-cat' holds its rows on the columns;
; one that does not keeps the old implementation.  books/image-world-paged
; includes it (tools/extract/world.py, right after the arena's attachment);
; tools/build_native_host.sh selects that umbrella under FN_NATIVE_CATALOG=
; paged and only for an image named *-paged; the default images, and every
; published image set, keep the old implementation until the reader natives
; pass on the paged image.
;
; What runs at certification time (skipped by include-book): a clear, two
; commits of ground held rows, a withdrawal, a redecision and the reads,
; asserted equal to what the logical side says of the same program.

(in-package "ACL2")
(include-book "catalog-paged")
(attach-stobj fn-cat fn-cat-paged)
(include-book "catalog")

; Two ground held rows: a plain article in one group and a crosspost.
(defconst *cpa-w1*
  (fn-record-make 0 1 0 "<a@x>" (append (fn-record-string-octets "Subject: a") '(13 10 13 10 97 13 10))
                  '("fn.test") "o" "s" "e" 1 5))
(defconst *cpa-w2*
  (fn-record-make 1 2 0 "<b@x>" (append (fn-record-string-octets "Subject: b") '(13 10 13 10 98 13 10))
                  '("fn.test" "fn.other") "o" "s" "e" 1 6))
(defconst *cpa-h1* (fn-held-plain *cpa-w1* 0))
(defconst *cpa-h2* (fn-held-plain *cpa-w2* 1))

(defconst *cpa-ctx* (fn-hc-make (fn-stx-make-verdict :verified nil 3) nil 3))

; The program over the live generic under the attachment.
(defun fn-cpa-smoke (fn-cat)
  (declare (xargs :stobjs fn-cat))
  (let* ((fn-cat (fn-cat-clear fn-cat))
         (fn-cat (fn-cat-commit *cpa-h1* fn-cat))
         (fn-cat (fn-cat-commit *cpa-h2* fn-cat))
         (fn-cat (fn-cat-withdraw 0 1 fn-cat))
         (fn-cat (fn-cat-redecide 1 *cpa-ctx* fn-cat)))
    (mv (list (fn-cat-count fn-cat)
              (fn-cat-at 0 fn-cat)
              (fn-cat-at 1 fn-cat)
              (fn-cat-msgid-seqs "<b@x>" fn-cat)
              (fn-cat-group-number "fn.test" 2 fn-cat)
              (fn-cat-group-next "fn.other" fn-cat)
              (fn-cat-group-count "fn.test" fn-cat)
              (fn-cat-visible-at 0 1 fn-cat)
              (fn-cat-visible-at 0 3 fn-cat)
              (fn-cat-group-live-count "fn.test" fn-cat)
              (fn-cat-horizon fn-cat)
              (fn-cat-withdrawn-at 2 fn-cat))
        fn-cat)))

;; The same program over the logical side: the :logic functions the generic's
;; exports are (books/catalog-logic.lisp), on the list.
(defconst *cpa-c*
  (let* ((c (fn-cat$a-clear nil))
         (c (fn-cat$a-commit *cpa-h1* c))
         (c (fn-cat$a-commit *cpa-h2* c))
         (c (fn-cat$a-withdraw 0 1 c))
         (c (fn-cat$a-redecide 1 *cpa-ctx* c)))
    c))

(defconst *cpa-expected*
  (let ((c *cpa-c*))
    (list (fn-cat$a-count c)
          (fn-cat$a-at 0 c)
          (fn-cat$a-at 1 c)
          (fn-cat$a-msgid-seqs "<b@x>" c)
          (fn-cat$a-group-number "fn.test" 2 c)
          (fn-cat$a-group-next "fn.other" c)
          (fn-cat$a-group-count "fn.test" c)
          (fn-cat$a-visible-at 0 1 c)
          (fn-cat$a-visible-at 0 3 c)
          (fn-cat$a-group-live-count "fn.test" c)
          (fn-cat$a-horizon c)
          (fn-cat$a-withdrawn-at 2 c))))

;; Not vacuous: two rows, the second numbered 2 in fn.test, the first withdrawn.
(assert-event (and (equal (car *cpa-expected*) 2)
                   (equal (nth 4 *cpa-expected*) 1)
                   (consp (fn-held-withdrawn (nth 1 *cpa-expected*)))))

(assert-event (mv-let (result fn-cat) (fn-cpa-smoke fn-cat)
                (mv (equal result *cpa-expected*) fn-cat))
              :stobjs-out '(nil fn-cat))
