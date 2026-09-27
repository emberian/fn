; served-catalog-join-open-tests.lisp -- teeth for books/served-catalog-join-
; number.lisp and books/served-catalog-join-open.lisp (the row relation
; between the store's acceptance and the catalog; lane sca-join-2).
;
; The owners are tests/acl2/owner-cancel-refresh-tests.lisp's, reached
; through the real owner transitions: T alone (*ocr-t-first*), T then a
; cancel of T with the key (*ocr-after*: T hidden), T then a cancel with a
; key that opens nothing (*ocr-after-other*), and the cancel before its
; target (*ocr-c-first*, *ocr-c-then-t*).
;
;   1. REACHABLE WITNESS of fn-scj-acc-rowsp-at-idle-related-owner's
;      conclusion over each owner: the store is idle, and the catalog the host loads from its rows, under the view's index, is
;      related to its acceptance (articles = rows as articles, numbers
;      included; every watermark one past the rows' high; no row outside the
;      domain).  The same under an empty index (the relation reads no
;      withdrawal).  NOT witnessed: the antecedent's fn-ocl-relation.
;      These fixtures' stores carry no configuration history, so
;      fn-cst-relation (the replay of their records from the initial
;      configuration) is false on them (fn-cst-final-configurationp and
;      fn-cst-recoverablep are nil); a fixture whose store replays needs a
;      configuration record declaring the groups (open, planning/evidence/
;      sca-join-2026-09-27.md).
;   2. REACHABLE WITNESS of fn-scj-row-equation-of-acc-rowsp: after T then
;      C, the committed row C read as an article is the acceptance's head.
;   3. MUTATION of the numbering: the catalog's row renumbered (as a
;      numbering that ignored the rows already there would) breaks the
;      watermark conjunct and the articles conjunct; a row bound in a group
;      outside the domain breaks the domain conjunct.

(in-package "ACL2")

(include-book "owner-cancel-refresh-tests")
(include-book "../../books/served-catalog-join-open")

; fn-scj-acc-rowsp's body (a defun-nx), executed.
(defun scjo-acc-rowsp (acc c)
  (declare (xargs :mode :program))
  (list (equal (fn-state-articles acc) (fn-scj-rows-arts c))
        (fn-scj-nexts-matchp (fn-state-groups acc) (fn-state-nexts acc) c)
        (fn-scj-rows-keys-inp c (fn-state-groups acc))))

(defun scjo-rows-of (i fn-cat)
  (declare (xargs :stobjs fn-cat :mode :program))
  (if (< i (fn-cat-count fn-cat))
      (cons (fn-cat-at i fn-cat) (scjo-rows-of (+ 1 i) fn-cat))
    nil))

; The catalog the host loads (fn-sca-load-held-rows) from the owner's rows.
(defun scjo-loaded (o index)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (with-local-stobj fn-cat
        (mv-let (r fn-arena fn-cat)
          (let ((fn-cat (fn-sca-load-held-rows (fn-sf-records (fn-sn-files (fn-own-store o)))
                                               index fn-arena fn-cat)))
            (mv (scjo-rows-of 0 fn-cat) fn-arena fn-cat))
          (mv r fn-arena)))
      r)))

(defun scjo-witness (o)
  (declare (xargs :mode :program))
  (let* ((st (fn-own-store o))
         (acc (fn-node-acceptance (fn-sn-node st))))
    (list (if (fn-own-store-idlep st) t nil)
          (consp (fn-state-articles acc))
          (scjo-acc-rowsp acc (scjo-loaded o (fn-own-view-index (fn-own-view o))))
          (scjo-acc-rowsp acc (scjo-loaded o (fn-midx-build nil))))))

;; 1. Every owner: idle, related, and the loaded catalog is related.
(assert-event (equal (scjo-witness *ocr-t-first*) '(t t (t t t) (t t t))))
(assert-event (equal (scjo-witness *ocr-after*) '(t t (t t t) (t t t))))
(assert-event (equal (scjo-witness *ocr-after-other*) '(t t (t t t) (t t t))))
(assert-event (equal (scjo-witness *ocr-c-first*) '(t t (t t t) (t t t))))
(assert-event (equal (scjo-witness *ocr-c-then-t*) '(t t (t t t) (t t t))))

;; The numbers are the acceptance's, not merely consistent with each other:
;; two articles, and the second one's number in the shared group is 2.
(defconst *scjo-after-c* (scjo-loaded *ocr-after* (fn-own-view-index (fn-own-view *ocr-after*))))
(assert-event (equal (len *scjo-after-c*) 2))
(assert-event (equal (fn-article-memberships (car (fn-state-articles (fn-node-acceptance
                                                                    (fn-sn-node (fn-own-store *ocr-after*))))))
                     (fn-held-numbers (nth 1 *scjo-after-c*))))

;; 2. The row equation, over the prefix and the committed row.
(defconst *scjo-prefix* (list (nth 0 *scjo-after-c*)))
(assert-event (equal (fn-scj-row-art (fn-cat-assign (nth 1 *scjo-after-c*) *scjo-prefix*))
                     (car (fn-state-articles (fn-node-acceptance (fn-sn-node (fn-own-store *ocr-after*)))))))

;; 3. Mutations.
(defconst *scjo-acc* (fn-node-acceptance (fn-sn-node (fn-own-store *ocr-after*))))
(defconst *scjo-renumbered*
  (list (nth 0 *scjo-after-c*)
        (fn-held-with-numbers (nth 1 *scjo-after-c*)
                              (fn-cat-assign-numbers (fn-record-groups (nth 1 *scjo-after-c*)) nil))))
(assert-event (equal (scjo-acc-rowsp *scjo-acc* *scjo-renumbered*) '(nil nil t)))
(defconst *scjo-outside*
  (list (nth 0 *scjo-after-c*)
        (fn-held-with-numbers (nth 1 *scjo-after-c*)
                              (cons (cons "not.in.the.domain" 1) (fn-held-numbers (nth 1 *scjo-after-c*))))))
(assert-event (equal (nth 2 (scjo-acc-rowsp *scjo-acc* *scjo-outside*)) nil))
