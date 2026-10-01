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
; one that does not keeps the old implementation (the SELECTABLE
; alternative: host/native/build.lisp chooses).
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
                  '("fn.test") "o" "s" "e" 1 5 (fn-ab-for-received :post-d25 '(97))))
(defconst *cpa-w2*
  (fn-record-make 1 2 0 "<b@x>" (append (fn-record-string-octets "Subject: b") '(13 10 13 10 98 13 10))
                  '("fn.test" "fn.other") "o" "s" "e" 1 6 (fn-ab-for-received :post-d25 '(98))))
(defconst *cpa-h1* (fn-held-plain *cpa-w1* 0))
(defconst *cpa-h2* (fn-held-plain *cpa-w2* 1))

; The program over the live generic under the attachment.
(defun fn-cpa-smoke (fn-cat)
  (declare (xargs :stobjs fn-cat))
  (let* ((fn-cat (fn-cat-clear fn-cat))
         (fn-cat (fn-cat-commit *cpa-h1* fn-cat))
         (fn-cat (fn-cat-commit *cpa-h2* fn-cat))
         (fn-cat (fn-cat-withdraw 0 1 fn-cat))
         (fn-cat (fn-cat-redecide 1 (fn-hc-make (fn-stx-make-verdict :verified nil 3) nil 3) fn-cat)))
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

; The same program over the logical side.
(defconst *cpa-c*
  (let* ((c nil)
         (c (append c (list (fn-cat-assign *cpa-h1* c))))
         (c (append c (list (fn-cat-assign *cpa-h2* c))))
         (c (fn-cat-mark-withdrawn 0 (len c) 1 c))
         (c (update-nth 1 (fn-held-with-context (nth 1 c)
                                                (fn-hc-make (fn-stx-make-verdict :verified nil 3) nil 3))
                        c)))
    c))

(assert-event (mv-let (result fn-cat) (fn-cpa-smoke fn-cat)
                (mv (equal result
                           (list 2 (nth 0 *cpa-c*) (nth 1 *cpa-c*) '(1) 1 2 2 t nil 1 3 '(0)))
                    fn-cat))
              :stobjs-out '(nil fn-cat))
