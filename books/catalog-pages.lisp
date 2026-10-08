; fn: the catalog's page image follows the catalog (lane s-pck, 2026-10-07;
; owed item PCK-ADOPT).  Model level: the page image of the catalog's fn-crow
; rows (books/catalog-paged.lisp) is adopted from the rows the catalog holds,
; and a commit / a withdrawal is the dirty-page set the generated
; fn-crow-append-dirty / fn-crow-set-dirty give; no codec or dirty-set
; function is hand written here.
(in-package "ACL2")
(include-book "catalog-paged")

; The catalog's rows as the fn-crow rows of the columns (fn-cp-row-of).
(defun fn-pck-crow-rows (h)
  (declare (xargs :guard t))
  (if (consp h) (cons (fn-cp-row-of (car h)) (fn-pck-crow-rows (cdr h))) nil))

(defun fn-pck-cat-pages (h)
  (declare (xargs :guard t :verify-guards nil))
  (fn-crow-pages-of (fn-pck-crow-rows h)))

; No row is an overflow row: the columns carry every row exactly.
(defun fn-pck-carriedp (h)
  (declare (xargs :guard t))
  (if (consp h) (and (not (fn-cp-overflow-of (car h))) (fn-pck-carriedp (cdr h))) t))

(defun fn-pck-cat-commit-dirty (h row)
  (declare (xargs :guard t :verify-guards nil))
  (fn-crow-append-dirty (fn-pck-crow-rows h) (fn-cp-row-of (fn-cat-assign row h))))

(defun fn-pck-cat-withdraw-dirty (h target by)
  (declare (xargs :guard t :verify-guards nil))
  (fn-crow-set-dirty (fn-pck-crow-rows h) target
                     (fn-cp-row-of (nth target (fn-cat$a-withdraw target by h)))))

(defthm fn-pck-crow-rows-ap
  (fn-crow$ap (fn-pck-crow-rows h))
  :hints (("Goal" :in-theory (e/d (fn-crow$ap) (fn-cp-row-of adt-rec-p))
           :induct (fn-pck-crow-rows h))
          ("Subgoal *1/2" :in-theory (e/d (fn-crow$ap adt-seq-p) (fn-cp-row-of adt-rec-p))
           :use fn-cp-row-of-rec-p)))

(defthm fn-pck-crow-rows-of-append
  (equal (fn-pck-crow-rows (append a b))
         (append (fn-pck-crow-rows a) (fn-pck-crow-rows b)))
  :hints (("Goal" :in-theory (disable fn-cp-row-of))))

(defthm fn-pck-crow-rowp-of-row-of
  (fn-crow-rowp (fn-cp-row-of h))
  :hints (("Goal" :in-theory (e/d (fn-crow-rowp) (fn-cp-row-of adt-rec-p))
           :use fn-cp-row-of-rec-p)))

(defthm fn-pck-adopt-round-trip
  (equal (fn-crow-of-pages (fn-pck-cat-pages h)) (fn-pck-crow-rows h))
  :hints (("Goal" :use ((:instance fn-crow-of-pages-of-pages-of (a (fn-pck-crow-rows h))) fn-pck-crow-rows-ap)
           :in-theory (e/d (fn-pck-cat-pages) (fn-crow-of-pages-of-pages-of fn-pck-crow-rows-ap fn-pck-crow-rows)))))

(defthm fn-pck-adopt-commit-image
  (equal (pgs-apply-dirty (fn-pck-cat-pages h) (fn-pck-cat-commit-dirty h row))
         (fn-pck-cat-pages (fn-cat$a-commit row h)))
  :hints (("Goal" :use ((:instance fn-crow-pages-of-append-is-apply-dirty
                                   (a (fn-pck-crow-rows h)) (x (fn-cp-row-of (fn-cat-assign row h))))
                        fn-pck-crow-rows-ap
                        (:instance fn-pck-crow-rows-of-append (a h) (b (list (fn-cat-assign row h)))))
           :in-theory (e/d (fn-pck-cat-pages fn-pck-cat-commit-dirty fn-cat$a-commit fn-crow$a-append)
                           (fn-crow-pages-of-append-is-apply-dirty fn-pck-crow-rows-ap fn-pck-crow-rows-of-append fn-cp-row-of fn-cat-assign)))))

(defthm fn-pck-adopt-commit-bound
  (<= (len (fn-pck-cat-commit-dirty h row))
      (+ 1 (fn-crow-pool-pages-of-row (fn-cp-row-of (fn-cat-assign row h)))))
  :hints (("Goal" :in-theory (e/d (fn-pck-cat-commit-dirty) (fn-cp-row-of fn-cat-assign))
           :use ((:instance fn-crow-append-dirty-bound (a (fn-pck-crow-rows h)) (x (fn-cp-row-of (fn-cat-assign row h))))))))

(defthm fn-pck-held-accessors-of-with-withdrawn
  (and (equal (fn-held-sequence (fn-held-with-withdrawn h w)) (fn-held-sequence h))
       (equal (fn-held-txid (fn-held-with-withdrawn h w)) (fn-held-txid h))
       (equal (fn-held-generation (fn-held-with-withdrawn h w)) (fn-held-generation h))
       (equal (fn-held-msgid (fn-held-with-withdrawn h w)) (fn-held-msgid h))
       (equal (fn-held-payload (fn-held-with-withdrawn h w)) (fn-held-payload h))
       (equal (fn-held-groups (fn-held-with-withdrawn h w)) (fn-held-groups h))
       (equal (fn-held-obligation-id (fn-held-with-withdrawn h w)) (fn-held-obligation-id h))
       (equal (fn-held-content-subject (fn-held-with-withdrawn h w)) (fn-held-content-subject h))
       (equal (fn-held-release-evidence (fn-held-with-withdrawn h w)) (fn-held-release-evidence h))
       (equal (fn-held-charge (fn-held-with-withdrawn h w)) (fn-held-charge h))
       (equal (fn-held-stamp (fn-held-with-withdrawn h w)) (fn-held-stamp h))
       (equal (fn-held-facts (fn-held-with-withdrawn h w)) (fn-held-facts h))
       (equal (fn-held-context (fn-held-with-withdrawn h w)) (fn-held-context h))
       (equal (fn-held-numbers (fn-held-with-withdrawn h w)) (fn-held-numbers h))
       (equal (fn-held-withdrawn (fn-held-with-withdrawn h w)) w))
  :hints (("Goal" :in-theory (enable fn-held-with-withdrawn))))

(defthm fn-pck-row-of-withdrawn
  (implies (and (not (fn-cp-escapedp h)) (fn-cp-smallp by) (fn-cp-smallp v))
           (equal (fn-cp-row-of (fn-held-with-withdrawn h (cons v by)))
                  (update-nth 9 by (update-nth 8 v (update-nth 7 t (fn-cp-row-of h))))))
  :hints (("Goal" :in-theory (e/d (fn-cp-row-of fn-cp-tree-of fn-cp-escapedp fn-cp-msgid-octets)
                                  (fn-held-with-withdrawn fn-cp-smallp fn-cp-u64))
           :do-not-induct t)))

; Two records of a schema that agree on every octets column have the same
; word width: the other columns are one word each.
(defun fn-pck-same-octets-p (s r1 r2)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom s) t)
        ((adt-octets-kind-p (car s))
         (and (equal (car r1) (car r2))
              (fn-pck-same-octets-p (cdr s) (cdr r1) (cdr r2))))
        (t (fn-pck-same-octets-p (cdr s) (cdr r1) (cdr r2)))))

(defthm fn-pck-len-fw-of-same-octets
  (implies (fn-pck-same-octets-p s r1 r2)
           (equal (len (adt-tp-fw s r1)) (len (adt-tp-fw s r2))))
  :hints (("Goal" :induct (fn-pck-same-octets-p s r1 r2)
           :in-theory (enable adt-tp-fw fn-pck-same-octets-p))))

(defthm fn-pck-withdraw-width
  (implies (and (not (fn-cp-escapedp h)) (fn-cp-smallp by) (fn-cp-smallp v))
           (equal (len (adt-tp-rw *fn-crow-schema* (fn-cp-row-of (fn-held-with-withdrawn h (cons v by)))))
                  (len (adt-tp-rw *fn-crow-schema* (fn-cp-row-of h)))))
  :hints (("Goal" :in-theory (e/d (adt-tp-rw) (fn-held-with-withdrawn fn-cp-smallp fn-cp-u64 fn-pck-row-of-withdrawn))
           :use (fn-pck-row-of-withdrawn
                 (:instance fn-pck-len-fw-of-same-octets (s *fn-crow-schema*)
                            (r1 (fn-cp-row-of h))
                            (r2 (update-nth 9 by (update-nth 8 v (update-nth 7 t (fn-cp-row-of h)))))))
           :do-not-induct t)))

(defthm fn-pck-crow-rows-of-update-nth
  (implies (and (natp i) (< i (len h)))
           (equal (fn-pck-crow-rows (update-nth i x h))
                  (update-nth i (fn-cp-row-of x) (fn-pck-crow-rows h))))
  :hints (("Goal" :in-theory (e/d (update-nth) (fn-cp-row-of)))))

(defthm fn-pck-len-crow-rows
  (equal (len (fn-pck-crow-rows h)) (len h))
  :hints (("Goal" :in-theory (disable fn-cp-row-of))))

(defthm fn-pck-nth-crow-rows
  (implies (and (natp i) (< i (len h)))
           (equal (nth i (fn-pck-crow-rows h)) (fn-cp-row-of (nth i h))))
  :hints (("Goal" :in-theory (e/d (nth) (fn-cp-row-of)))))

(defthm fn-pck-update-nth-same
  (implies (and (natp i) (< i (len a)))
           (equal (update-nth i (nth i a) a) a))
  :hints (("Goal" :in-theory (enable update-nth nth))))

; A withdrawal rewrites one row; the case split of fn-cat-mark-withdrawn.
(defthm fn-pck-withdraw-cases
  (implies (and (natp target) (< target (len h)))
           (equal (fn-cat$a-withdraw target by h)
                  (if (null (fn-held-withdrawn (nth target h)))
                      (update-nth target (fn-held-with-withdrawn (nth target h) (cons (len h) by)) h)
                    h)))
  :hints (("Goal" :in-theory (enable fn-cat$a-withdraw fn-cat-mark-withdrawn))))

; The withdrawn row keeps its word width.
(defthm fn-pck-withdraw-row-width
  (implies (and (natp target) (< target (len h)) (natp by)
                (not (fn-cp-escapedp (nth target h)))
                (fn-cp-smallp by) (fn-cp-smallp (len h)))
           (equal (len (adt-tp-rw *fn-crow-schema*
                                  (fn-cp-row-of (nth target (fn-cat$a-withdraw target by h)))))
                  (len (adt-tp-rw *fn-crow-schema* (fn-cp-row-of (nth target h))))))
  :hints (("Goal" :in-theory (e/d (fn-pck-withdraw-cases) (fn-cp-row-of fn-held-with-withdrawn fn-cp-escapedp fn-cp-smallp adt-tp-rw))
           :use ((:instance fn-pck-withdraw-width (h (nth target h)) (v (len h)))))))

(defthm fn-pck-adopt-withdraw-image
  (implies (and (natp target) (< target (len h)) (natp by)
                (not (fn-cp-escapedp (nth target h)))
                (fn-cp-smallp by) (fn-cp-smallp (len h)))
           (equal (pgs-apply-dirty (fn-pck-cat-pages h) (fn-pck-cat-withdraw-dirty h target by))
                  (fn-pck-cat-pages (fn-cat$a-withdraw target by h))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-cat-pages fn-pck-cat-withdraw-dirty)
                           (fn-cp-row-of fn-held-with-withdrawn fn-cp-escapedp fn-cp-smallp
                            fn-pck-crow-rows fn-crow-pages-of-set-is-apply-dirty
                            fn-pck-withdraw-row-width fn-cat$a-withdraw))
           :use (fn-pck-withdraw-row-width fn-pck-withdraw-cases fn-pck-crow-rows-ap
                 (:instance fn-crow-pages-of-set-is-apply-dirty
                            (a (fn-pck-crow-rows h)) (i target)
                            (x (fn-cp-row-of (nth target (fn-cat$a-withdraw target by h)))))
                 (:instance fn-pck-crow-rows-of-update-nth (i target) (x (nth target (fn-cat$a-withdraw target by h))))))))

(defthm fn-pck-adopt-withdraw-bound
  (implies (and (natp target) (< target (len h)) (natp by)
                (not (fn-cp-escapedp (nth target h)))
                (fn-cp-smallp by) (fn-cp-smallp (len h)))
           (<= (len (fn-pck-cat-withdraw-dirty h target by))
               (+ 1 (fn-crow-pool-pages-of-row (fn-cp-row-of (nth target h))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-cat-withdraw-dirty fn-crow-pool-pages-of-row)
                           (fn-cp-row-of fn-held-with-withdrawn fn-cp-escapedp fn-cp-smallp
                            fn-pck-withdraw-row-width fn-cat$a-withdraw fn-crow-set-dirty-bound))
           :use (fn-pck-withdraw-row-width
                 (:instance fn-crow-set-dirty-bound (a (fn-pck-crow-rows h)) (i target)
                            (x (fn-cp-row-of (nth target (fn-cat$a-withdraw target by h)))))))))

; -----------------------------------------------------------------------------
; PCK-ADOPT-ESCAPED.  A withdrawal that changes the row's word width: the row
; is already escaped (its remainder tree carries the payload and the
; withdrawal) or the withdrawal newly escapes it (BY or the version is not
; below the sentinel).  The rows after the target shift, so the dirty set is
; the generated fn-crow-set-dirty-widening: the pages from the target row to
; the end of the tape.  The withdrawn row never narrows (the remainder only
; gains the withdrawn pair), but it is only a carried row while the
; remainder is encodable, so the withdrawn catalog being carried is a premise:
; a remainder past the codec's naturals is kept whole in its overflow cell,
; its columns shrink, and a page image cannot drop a page.

(defthm fn-pck-len-program-cons
  (implies (not (fn-scc-octets-valuep (cons x y)))
           (equal (len (fn-scc-program (cons x y)))
                  (+ 1 (len (fn-scc-program x)) (len (fn-scc-program y)))))
  :hints (("Goal" :in-theory (enable fn-scc-program))))

(defthm fn-pck-not-octet-list-cons
  (implies (not (fn-scc-octet-listp y)) (not (fn-scc-octets-valuep (cons x y)))))

(defthm fn-pck-not-octet-list-car
  (implies (not (fn-scc-octetp x)) (not (fn-scc-octets-valuep (cons x y)))))

(defthm fn-pck-not-octet-list-cons2
  (implies (not (fn-scc-octet-listp y)) (not (fn-scc-octet-listp (cons x y)))))

(defthm fn-pck-not-octet-list-last
  (implies (not (fn-scc-octetp e)) (not (fn-scc-octet-listp (cons e nil)))))

(defthm fn-pck-len-program-nil
  (equal (len (fn-scc-program nil)) 1)
  :hints (("Goal" :in-theory (enable fn-scc-program fn-scc-atom-octets))))

(defthm fn-pck-tree-len-mono-slot
  ; The remainder tree's program grows with its last slot.
  (implies (and (not (fn-scc-octetp e1)) (not (fn-scc-octetp e2))
                (<= (len (fn-scc-program e1)) (len (fn-scc-program e2))))
           (<= (len (fn-scc-program (list a b c d e f g e1)))
               (len (fn-scc-program (list a b c d e f g e2)))))
  :hints (("Goal" :in-theory (disable fn-scc-program fn-scc-octets-valuep fn-scc-octet-listp fn-scc-octetp))))

(defthm fn-pck-escaped-mono
  (implies (and (null (fn-held-withdrawn h)) (fn-cp-escapedp h))
           (fn-cp-escapedp (fn-held-with-withdrawn h (cons v by))))
  :hints (("Goal" :in-theory (e/d (fn-pck-held-accessors-of-with-withdrawn fn-cp-escapedp)
                                  (fn-held-with-withdrawn fn-cp-smallp)))))

(defthm fn-pck-cons-not-octetp
  (and (not (fn-scc-octetp (cons x y))) (not (fn-scc-octetp nil)))
  :hints (("Goal" :in-theory (enable fn-scc-octetp))))

(defthm fn-pck-len-program-list2
  (implies (not (fn-scc-octetp w))
           (equal (len (fn-scc-program (list p w)))
                  (+ 3 (len (fn-scc-program p)) (len (fn-scc-program w)))))
  :hints (("Goal" :in-theory (disable fn-scc-program fn-scc-octets-valuep fn-scc-octet-listp fn-scc-octetp)
           :use ((:instance fn-pck-len-program-cons (x p) (y (list w)))
                 (:instance fn-pck-len-program-cons (x w) (y nil))))))

(defthm fn-pck-len-program-pair
  (implies (natp by) (<= 1 (len (fn-scc-program (cons v by)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-scc-program fn-scc-octets-valuep fn-scc-octetp)
           :use ((:instance fn-pck-len-program-cons (x v) (y by))
                 (:instance fn-pck-not-octet-list-cons (x v) (y by))))))

(defthm fn-pck-record-payload-of-with-withdrawn
  (equal (fn-record-payload (fn-held-with-withdrawn h w)) (fn-record-payload h))
  :hints (("Goal" :in-theory (enable fn-held-with-withdrawn))))

(defthm fn-pck-slot-len-mono
  ; The escaped remainder's slot of a row not yet withdrawn, and of the same row withdrawn.
  (implies (and (null (fn-held-withdrawn h)) (natp by))
           (let ((h2 (fn-held-with-withdrawn h (cons v by))))
             (and (not (fn-scc-octetp (if (fn-cp-escapedp h) (list (fn-held-payload h) (fn-held-withdrawn h)) nil)))
                  (not (fn-scc-octetp (if (fn-cp-escapedp h2) (list (fn-held-payload h2) (fn-held-withdrawn h2)) nil)))
                  (<= (len (fn-scc-program (if (fn-cp-escapedp h) (list (fn-held-payload h) (fn-held-withdrawn h)) nil)))
                      (len (fn-scc-program (if (fn-cp-escapedp h2) (list (fn-held-payload h2) (fn-held-withdrawn h2)) nil)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-held-accessors-of-with-withdrawn fn-pck-escaped-mono fn-pck-record-payload-of-with-withdrawn)
                           (fn-cp-escapedp fn-held-with-withdrawn fn-scc-program fn-scc-octets-valuep fn-scc-octetp
                            fn-pck-len-program-cons))
           :use ((:instance fn-pck-len-program-cons (x (cons v by)) (y nil))
                 (:instance fn-pck-len-program-cons (x nil) (y nil))))))

(defthm fn-pck-tree-len-mono
  (implies (and (null (fn-held-withdrawn h)) (natp by))
           (<= (len (fn-scc-program (fn-cp-tree-of h)))
               (len (fn-scc-program (fn-cp-tree-of (fn-held-with-withdrawn h (cons v by)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cp-tree-of fn-pck-held-accessors-of-with-withdrawn)
                           (fn-held-with-withdrawn fn-scc-program fn-cp-escapedp fn-pck-slot-len-mono
                            fn-pck-tree-len-mono-slot))
           :use (fn-pck-slot-len-mono
                 (:instance fn-pck-tree-len-mono-slot
                            (a (fn-held-groups h)) (b (fn-held-obligation-id h))
                            (c (fn-held-content-subject h)) (d (fn-held-release-evidence h))
                            (e (fn-held-facts h)) (f (fn-held-context h)) (g nil)
                            (e1 (if (fn-cp-escapedp h) (list (fn-held-payload h) (fn-held-withdrawn h)) nil))
                            (e2 (let ((h2 (fn-held-with-withdrawn h (cons v by))))
                                  (if (fn-cp-escapedp h2) (list (fn-held-payload h2) (fn-held-withdrawn h2)) nil))))))))

(defun fn-pck-ind8 (x y)
  (declare (xargs :measure (nfix y)))
  (if (zp y) x (fn-pck-ind8 (nfix (- x 8)) (nfix (- y 8)))))

(defthm fn-pck-npk-mono
  (implies (and (natp x) (natp y) (<= x y)) (<= (adt-tp-npk x) (adt-tp-npk y)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-pck-ind8 x y) :in-theory (enable adt-tp-npk))))

; Two records of a schema whose octets columns do not shrink.
(defun fn-pck-octs-le-p (s r1 r2)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom s) t)
        ((adt-octets-kind-p (car s))
         (and (<= (len (car r1)) (len (car r2)))
              (fn-pck-octs-le-p (cdr s) (cdr r1) (cdr r2))))
        (t (fn-pck-octs-le-p (cdr s) (cdr r1) (cdr r2)))))

(defthm fn-pck-len-fw-mono
  (implies (fn-pck-octs-le-p s r1 r2)
           (<= (len (adt-tp-fw s r1)) (len (adt-tp-fw s r2))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-pck-octs-le-p s r1 r2)
           :in-theory (e/d (adt-tp-fw fn-pck-octs-le-p) nil))
          ("Subgoal *1/2" :use ((:instance fn-pck-npk-mono (x (len (car r1))) (y (len (car r2))))))))

(defun fn-pck-col (n r)
  (declare (xargs :guard t :verify-guards nil))
  (nth n r))
(in-theory (disable fn-pck-col))

(defthm fn-pck-octs-le-p-of-columns
  (implies (and (<= (len (fn-pck-col 6 r1)) (len (fn-pck-col 6 r2)))
                (<= (len (fn-pck-col 11 r1)) (len (fn-pck-col 11 r2)))
                (<= (len (fn-pck-col 12 r1)) (len (fn-pck-col 12 r2))))
           (fn-pck-octs-le-p *fn-crow-schema* r1 r2))
  :hints (("Goal" :in-theory (enable fn-pck-octs-le-p fn-pck-col))))

(defthm fn-pck-row-of-columns
  (and (equal (fn-pck-col 6 (fn-cp-row-of h)) (fn-cp-msgid-octets h))
       (equal (fn-pck-col 11 (fn-cp-row-of h))
              (if (fn-sccb-treep (fn-cp-tree-of h)) (fn-scc-program (fn-cp-tree-of h)) nil))
       (equal (fn-pck-col 12 (fn-cp-row-of h))
              (if (fn-sccb-treep (fn-held-numbers h)) (fn-scc-program (fn-held-numbers h)) nil)))
  :hints (("Goal" :in-theory (e/d (fn-pck-col) (fn-cp-msgid-octets fn-cp-escapedp fn-cp-smallp fn-cp-u64
                                      fn-cp-tree-of fn-sccb-treep fn-scc-program))
           :do-not-induct t)))

(defthm fn-pck-msgid-octets-of-with-withdrawn
  (equal (fn-cp-msgid-octets (fn-held-with-withdrawn h w)) (fn-cp-msgid-octets h))
  :hints (("Goal" :in-theory (e/d (fn-cp-msgid-octets fn-pck-held-accessors-of-with-withdrawn) (fn-held-with-withdrawn)))))

(defthm fn-pck-withdraw-width-mono
  ; A row not yet withdrawn does not narrow when withdrawn, whatever the version and BY, so long as
  ; both remainders are encodable (a remainder past the codec's naturals is kept whole in its cell).
  (implies (and (null (fn-held-withdrawn h)) (natp by)
                (fn-sccb-treep (fn-cp-tree-of h))
                (fn-sccb-treep (fn-cp-tree-of (fn-held-with-withdrawn h (cons v by)))))
           (<= (len (adt-tp-rw *fn-crow-schema* (fn-cp-row-of h)))
               (len (adt-tp-rw *fn-crow-schema* (fn-cp-row-of (fn-held-with-withdrawn h (cons v by)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (adt-tp-rw fn-pck-msgid-octets-of-with-withdrawn)
                           (fn-held-with-withdrawn fn-scc-program fn-cp-escapedp fn-cp-smallp fn-cp-tree-of
                            fn-pck-tree-len-mono fn-sccb-treep fn-cp-msgid-octets fn-cp-row-of
                            fn-pck-octs-le-p-of-columns fn-pck-row-of-columns fn-pck-octs-le-p adt-tp-fw))
           :use (fn-pck-tree-len-mono
                 (:instance fn-pck-row-of-columns (h h))
                 (:instance fn-pck-row-of-columns (h (fn-held-with-withdrawn h (cons v by))))
                 (:instance fn-pck-held-accessors-of-with-withdrawn (w (cons v by)))
                 (:instance fn-pck-octs-le-p-of-columns
                            (r1 (fn-cp-row-of h))
                            (r2 (fn-cp-row-of (fn-held-with-withdrawn h (cons v by)))))
                 (:instance fn-pck-len-fw-mono (s *fn-crow-schema*)
                            (r1 (fn-cp-row-of h))
                            (r2 (fn-cp-row-of (fn-held-with-withdrawn h (cons v by)))))))))

(defthm fn-pck-rowsp-nth
  (implies (and (fn-cat-rowsp h) (natp i) (< i (len h))) (fn-cat-rowp (nth i h)))
  :hints (("Goal" :in-theory (e/d (nth) (fn-cat-rowp)))))

(defthm fn-pck-carriedp-nth
  (implies (and (fn-pck-carriedp h) (natp i) (< i (len h))) (not (fn-cp-overflow-of (nth i h))))
  :hints (("Goal" :in-theory (e/d (nth) (fn-cp-overflow-of)))))

; A carried row's remainder and numbers are encodable trees.
(defthm fn-pck-carried-row-trees
  (implies (and (fn-cat-rowp x) (not (fn-cp-overflow-of x)))
           (and (fn-sccb-treep (fn-cp-tree-of x)) (fn-sccb-treep (fn-held-numbers x))))
  :hints (("Goal" :in-theory (e/d (fn-cp-overflow-of) (fn-cat-rowp fn-sccb-treep fn-cp-tree-of fn-held-numbers)))))

(defthm fn-pck-with-withdrawn-consp
  (consp (fn-held-with-withdrawn h w))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-held-with-withdrawn))))

(defthm fn-pck-carried-row-trees-consp
  (implies (and (consp x) (not (fn-cp-overflow-of x)))
           (and (fn-sccb-treep (fn-cp-tree-of x)) (fn-sccb-treep (fn-held-numbers x))))
  :hints (("Goal" :in-theory (e/d (fn-cp-overflow-of) (fn-cat-rowp fn-sccb-treep fn-cp-tree-of fn-held-numbers)))))

(defthm fn-pck-withdraw-width-ok
  ; The withdrawn row does not narrow, given that the withdrawn catalog is still carried.
  (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h) (natp target) (< target (len h)) (natp by)
                (fn-pck-carriedp (fn-cat$a-withdraw target by h)))
           (<= (len (adt-tp-rw *fn-crow-schema* (fn-cp-row-of (nth target h))))
               (len (adt-tp-rw *fn-crow-schema* (fn-cp-row-of (nth target (fn-cat$a-withdraw target by h)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-withdraw-cases)
                           (fn-cp-row-of fn-held-with-withdrawn fn-cat$a-withdraw adt-tp-rw fn-sccb-treep
                            fn-cp-tree-of fn-pck-withdraw-width-mono fn-pck-carried-row-trees-consp
                            fn-pck-carried-row-trees fn-pck-carriedp-nth fn-cp-overflow-of))
           :use ((:instance fn-pck-rowsp-nth (i target))
                 (:instance fn-pck-carriedp-nth (i target))
                 (:instance fn-pck-carriedp-nth (h (fn-cat$a-withdraw target by h)) (i target))
                 (:instance fn-pck-carried-row-trees (x (nth target h)))
                 (:instance fn-pck-carried-row-trees-consp
                            (x (fn-held-with-withdrawn (nth target h) (cons (len h) by))))
                 (:instance fn-pck-withdraw-width-mono (h (nth target h)) (v (len h)))))))

(defun fn-pck-cat-withdraw-dirty-shifted (h target by)
  ; The withdrawal's dirty set whatever the new row's width: the pages from the target row to the end.
  (declare (xargs :guard t :verify-guards nil))
  (fn-crow-set-dirty-widening (fn-pck-crow-rows h) target
                              (fn-cp-row-of (nth target (fn-cat$a-withdraw target by h)))))

(defthm fn-pck-crow-rows-of-nthcdr
  (equal (fn-pck-crow-rows (nthcdr i h)) (nthcdr i (fn-pck-crow-rows h)))
  :hints (("Goal" :in-theory (e/d (nthcdr) (fn-cp-row-of)))))

(defthm fn-pck-crow-rows-of-withdraw
  (implies (and (natp target) (< target (len h)))
           (equal (fn-pck-crow-rows (fn-cat$a-withdraw target by h))
                  (update-nth target (fn-cp-row-of (nth target (fn-cat$a-withdraw target by h)))
                              (fn-pck-crow-rows h))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-withdraw-cases) (fn-cp-row-of fn-cat$a-withdraw fn-held-with-withdrawn))
           :use ((:instance fn-pck-crow-rows-of-update-nth (i target)
                            (x (nth target (fn-cat$a-withdraw target by h)))
                            (h h))
                 (:instance fn-pck-update-nth-same (i target) (a (fn-pck-crow-rows h)))
                 (:instance fn-pck-nth-crow-rows (i target))
                 (:instance fn-pck-len-crow-rows)))))

(defthm fn-pck-adopt-withdraw-escaped
  (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h) (natp target) (< target (len h)) (natp by)
                (fn-pck-carriedp (fn-cat$a-withdraw target by h)))
           (and (equal (pgs-apply-dirty (fn-pck-cat-pages h) (fn-pck-cat-withdraw-dirty-shifted h target by))
                       (fn-pck-cat-pages (fn-cat$a-withdraw target by h)))
                (<= (len (fn-pck-cat-withdraw-dirty-shifted h target by))
                    (+ 1 (fn-crow-pool-pages-of-rows
                          (fn-pck-crow-rows (nthcdr target (fn-cat$a-withdraw target by h))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-cat-pages fn-pck-cat-withdraw-dirty-shifted)
                           (fn-cp-row-of fn-cat$a-withdraw fn-pck-crow-rows adt-tp-rw
                            fn-crow-pages-of-set-widening-is-apply-dirty fn-crow-set-dirty-widening-bound
                            fn-pck-crow-rows-of-withdraw fn-pck-crow-rows-of-nthcdr fn-pck-withdraw-width-ok
                            fn-pck-nth-crow-rows))
           :use (fn-pck-crow-rows-ap
                 (:instance fn-pck-withdraw-width-ok)
                 (:instance fn-pck-nth-crow-rows (i target))
                 (:instance fn-pck-crow-rows-of-withdraw)
                 (:instance fn-pck-crow-rows-of-nthcdr (i target) (h (fn-cat$a-withdraw target by h)))
                 (:instance fn-crow-pages-of-set-widening-is-apply-dirty
                            (a (fn-pck-crow-rows h)) (i target)
                            (x (fn-cp-row-of (nth target (fn-cat$a-withdraw target by h)))))
                 (:instance fn-crow-set-dirty-widening-bound
                            (a (fn-pck-crow-rows h)) (i target)
                            (x (fn-cp-row-of (nth target (fn-cat$a-withdraw target by h)))))))))

; The held rows the fn-crow rows decode to (fn-cp-row-held, books/catalog-paged.lisp).
(defun fn-pck-held-of-crow-rows (rows)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rows) (cons (fn-cp-row-held (car rows)) (fn-pck-held-of-crow-rows (cdr rows))) nil))

; A carried row (a catalog row the overflow test passes) decodes from its columns.
(defthm fn-pck-row-held-of-carried-row
  (implies (and (fn-cat-rowp x) (not (fn-cp-overflow-of x)))
           (equal (fn-cp-row-held (fn-cp-row-of x)) x))
  :hints (("Goal" :use fn-cp-row-held-of-row-of
           :in-theory (e/d (fn-cp-overflow-of) (fn-cp-row-of fn-cp-row-held fn-cat-rowp fn-sccb-treep fn-cp-tree-of fn-held-numbers)))))

; The columns carry every row of a carried catalog exactly.
(defthm fn-pck-held-of-crow-rows-of-crow-rows
  (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h))
           (equal (fn-pck-held-of-crow-rows (fn-pck-crow-rows h)) h))
  :hints (("Goal" :in-theory (disable fn-cp-row-of fn-cp-row-held fn-cp-overflow-of fn-cat-rowp)
           :induct (fn-pck-crow-rows h))))

(defthm fn-pck-adopt-is-the-catalog
  (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h))
           (and (equal (fn-crow-of-pages (fn-pck-cat-pages h)) (fn-pck-crow-rows h))
                ; the pages give back the CATALOG: the held rows they decode to
                (equal (fn-pck-held-of-crow-rows (fn-crow-of-pages (fn-pck-cat-pages h))) h)
                (implies (fn-held-p row)
                         (and (equal (pgs-apply-dirty (fn-pck-cat-pages h)
                                                      (fn-pck-cat-commit-dirty h row))
                                     (fn-pck-cat-pages (fn-cat$a-commit row h)))
                              (<= (len (fn-pck-cat-commit-dirty h row))
                                  (+ 1 (fn-crow-pool-pages-of-row
                                        (fn-cp-row-of (fn-cat-assign row h)))))))
                (implies (and (natp target) (< target (len h)) (natp by)
                              (not (fn-cp-escapedp (nth target h)))
                              (fn-cp-smallp by) (fn-cp-smallp (len h)))
                         (and (equal (pgs-apply-dirty (fn-pck-cat-pages h)
                                                      (fn-pck-cat-withdraw-dirty h target by))
                                     (fn-pck-cat-pages (fn-cat$a-withdraw target by h)))
                              (<= (len (fn-pck-cat-withdraw-dirty h target by))
                                  (+ 1 (fn-crow-pool-pages-of-row
                                        (fn-cp-row-of (nth target h)))))))
                ; a withdrawal that changes the row's width (an escaped row): the pages from the target on
                (implies (and (natp target) (< target (len h)) (natp by)
                              (fn-pck-carriedp (fn-cat$a-withdraw target by h)))
                         (and (equal (pgs-apply-dirty (fn-pck-cat-pages h)
                                                      (fn-pck-cat-withdraw-dirty-shifted h target by))
                                     (fn-pck-cat-pages (fn-cat$a-withdraw target by h)))
                              (<= (len (fn-pck-cat-withdraw-dirty-shifted h target by))
                                  (+ 1 (fn-crow-pool-pages-of-rows
                                        (fn-pck-crow-rows (nthcdr target (fn-cat$a-withdraw target by h))))))))))
  :hints (("Goal" :in-theory (disable fn-pck-cat-pages fn-pck-cat-commit-dirty fn-pck-cat-withdraw-dirty fn-pck-cat-withdraw-dirty-shifted
                                      fn-cat$a-commit fn-cat$a-withdraw fn-cp-row-of fn-cat-assign
                                      fn-crow-pool-pages-of-row fn-cp-escapedp fn-cp-smallp)
           :use (fn-pck-adopt-round-trip fn-pck-held-of-crow-rows-of-crow-rows
                 fn-pck-adopt-commit-image fn-pck-adopt-commit-bound
                 fn-pck-adopt-withdraw-image fn-pck-adopt-withdraw-bound fn-pck-adopt-withdraw-escaped))))
