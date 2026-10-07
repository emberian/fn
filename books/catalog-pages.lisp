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

(defthm fn-pck-adopt-is-the-catalog
  (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h))
           (and (equal (fn-crow-of-pages (fn-pck-cat-pages h)) (fn-pck-crow-rows h))
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
                                        (fn-cp-row-of (nth target h)))))))))
  :hints (("Goal" :in-theory (disable fn-pck-cat-pages fn-pck-cat-commit-dirty fn-pck-cat-withdraw-dirty
                                      fn-cat$a-commit fn-cat$a-withdraw fn-cp-row-of fn-cat-assign
                                      fn-crow-pool-pages-of-row fn-cp-escapedp fn-cp-smallp)
           :use (fn-pck-adopt-round-trip fn-pck-adopt-commit-image fn-pck-adopt-commit-bound
                 fn-pck-adopt-withdraw-image fn-pck-adopt-withdraw-bound))))
