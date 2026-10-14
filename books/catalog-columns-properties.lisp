; LB keystones; private proof cuts are scoped, frozen terms unchanged.
(in-package "ACL2")
(include-book "catalog-columns-served")
(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm fn-lbp-row-corr-served-projection
 (implies (fn-lbc-row-corr i row pm fn-lbc log)
  (equal (fn-lbc-served-row i fn-lbc) (fn-cat-served-projection row)))
 :hints (("Goal" :in-theory '(fn-lbc-row-corr)))))

(local (defun fn-lbp-rows-corr-induction (base j rows pm)
  (declare (xargs :measure (nfix j) :verify-guards nil))
  (if (and (consp rows) (not (zp j)))
      (fn-lbp-rows-corr-induction (+ 1 (nfix base)) (- j 1) (cdr rows)
                                 (max (nfix pm) (nfix (fn-record-stamp (car rows)))))
    (list base pm))))

(local (defthm fn-lbp-rows-corr-served-nth
  (implies (and (fn-lbc-rows-corr base rows pm fn-lbc log)
                (natp base) (natp j) (< j (len rows)))
           (equal (fn-lbc-served-row (+ base j) fn-lbc)
                  (fn-cat-served-projection (nth j rows))))
  :hints (("Goal" :induct (fn-lbp-rows-corr-induction base j rows pm)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbp-rows-corr-induction fn-lbc-rows-corr nth natp nfix zp max fn-lbp-row-corr-served-projection))))))

(defthm fn-lbc-served-row-is-abstract
  (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
                (natp i) (< i (len rows)))
           (equal (fn-lbc-served-row i fn-lbc)
                  (fn-cat-served-projection (nth i rows))))
  :hints (("Goal" :use ((:instance fn-lbp-rows-corr-served-nth (base 0) (j i) (pm 0)))
           :in-theory (e/d (fn-lbc-corr) (fn-lbc-p fn-cat$ap fn-lbc-rows-corr
                            fn-lbc-served-row fn-cat-served-projection)))))

(local (defthm fn-lbp-restore-control-of-homes
 (implies (true-listp control)
  (equal (fn-lbc-restore-control
          (list (len control) (take (min 3 (len control)) control) (nthcdr 4 control))
          (nth 3 control))
         control))
 :hints (("Goal" :in-theory (enable fn-lbc-restore-control take nthcdr nth len)
          :expand ((len control) (len (cdr control)) (len (cddr control))
                   (len (cdddr control)))))))

(local (defthm fn-lbp-row-reconstruction-shapes
 (implies (fn-cat-rowp row)
  (and (fn-held-shapep row) (fn-hf-shapep (fn-held-facts row))
       (true-listp (fn-hf-control (fn-held-facts row)))))
 :rule-classes nil
 :hints (("Goal" :in-theory '(fn-cat-rowp fn-hf-p)))))

(local (defthm fn-lbp-row-corr-homes
 (implies (fn-lbc-row-corr i row pm fn-lbc log)
  (equal (nth 7 (fn-lbc-home-entry i fn-lbc log)) (fn-lb-log-model-homes row)))
 :hints (("Goal" :in-theory '(fn-lbc-row-corr)))))

(local (defthm fn-lbp-true-list-fix-identity
 (implies (true-listp x) (equal (true-list-fix x) x))
 :hints (("Goal" :induct (true-list-fix x) :in-theory (enable true-list-fix true-listp)))))

(local (defthm fn-lbp-restore-control-canonical
 (implies (true-listp control)
  (equal (fn-lbc-restore-control
          (list (len control) (take (min 3 (len control)) control) (nthcdr 4 control))
          (cadddr control))
         control))
 :hints (("Goal" :use fn-lbp-restore-control-of-homes
          :in-theory (e/d (nth) (fn-lbc-restore-control len take min nthcdr
                                fn-lbp-restore-control-of-homes))))))

(local (defthm fn-lbp-at-of-row-corr
 (implies (and (fn-cat-rowp row) (fn-lbc-row-corr i row pm fn-lbc log))
          (equal (fn-lbc-at i fn-lbc log) row))
 :hints (("Goal" :use ((:instance fn-lbp-row-reconstruction-shapes)
                      (:instance fn-held-make-of-accessors (x row))
                      (:instance fn-hf-make-of-accessors (x (fn-held-facts row))))
 :in-theory (union-theories (set-difference-theories (theory 'ground-zero) '(true-listp len min nfix take nthcdr true-list-fix))
 '(fn-lbc-at fn-lbp-row-corr-served-projection fn-lbp-row-corr-homes fn-cat-served-projection fn-lb-log-model-homes fn-hf-nov
   fn-held-accessors-are-the-wire-accessors fn-cbor-ag-car fn-cbor-ag-cdr
   fn-lbp-restore-control-canonical nth fn-lbp-true-list-fix-identity
   ))))))

(local (defthm fn-lbp-rows-corr-full-nth
  (implies (and (fn-lbc-rows-corr base rows pm fn-lbc log) (fn-cat-rowsp rows)
                (natp base) (natp j) (< j (len rows)))
           (equal (fn-lbc-at (+ base j) fn-lbc log) (nth j rows)))
 :hints (("Goal" :induct (fn-lbp-rows-corr-induction base j rows pm)
 :in-theory (e/d (fn-lbc-rows-corr fn-cat-rowsp nth)
                 (fn-cat-rowp fn-lbc-row-corr fn-lbc-at fn-record-stamp))))))

(defthm fn-lbc-row-is-abstract
  (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
                (natp i) (< i (len rows)))
           (equal (fn-lbc-at i fn-lbc log) (nth i rows)))
 :hints (("Goal" :use ((:instance fn-lbp-rows-corr-full-nth (base 0) (j i) (pm 0)))
 :in-theory (e/d (fn-lbc-corr fn-cat$ap)
                 (fn-lbc-p fn-cat-rowsp fn-lbc-rows-corr fn-lbc-at)))))

(local (defthm fn-lbp-keep-from-below-start-general
 (implies (and (natp i) (natp j) (natp k) (<= j i) (<= k i))
  (equal (lb-keep-from j th stamps i) (lb-keep-from k th stamps i)))
 :rule-classes nil
 :hints (("Goal" :induct (lb-keep-from j th stamps i)
          :in-theory (enable lb-keep-from)))))

(local (defun fn-lbp-prefix-induction (stamps pm i)
 (declare (xargs :verify-guards nil))
 (if (consp stamps)
  (fn-lbp-prefix-induction (cdr stamps) (max (nfix pm) (nfix (car stamps))) (+ 1 i))
  (list pm i))))

(local (defthm fn-lbp-keep-from-normalizes
 (implies (and (syntaxp (not (equal j i))) (natp i) (natp j) (<= j i))
  (equal (lb-keep-from j th stamps i) (lb-keep-from i th stamps i)))
 :hints (("Goal" :use ((:instance fn-lbp-keep-from-below-start-general (k i)))
 :in-theory (disable lb-keep-from)))))

(local (defthm fn-lbp-first-reaching-general
 (implies (and (natp th) (natp i) (natp pm) (< pm th))
  (equal (lb-keep-from (lb-first-at-least th (lb-prefix-max stamps pm) i) th stamps i)
         (lb-keep-from i th stamps i)))
 :hints (("Goal" :induct (fn-lbp-prefix-induction stamps pm i)
          :do-not '(preprocess) :in-theory (enable lb-prefix-max lb-first-at-least lb-keep-from)))))

(defthm fn-lb-first-reaching-filter-is-full-filter
  (implies (natp th)
           (equal (lb-keep-from (lb-first-at-least th (lb-prefix-max stamps 0) 0) th stamps 0)
                  (lb-keep-from 0 th stamps 0)))
 :hints (("Goal" :cases ((equal th 0))
          :use ((:instance fn-lbp-first-reaching-general (i 0) (pm 0)))
          :in-theory (e/d (lb-first-at-least lb-prefix-max)
                         (lb-keep-from fn-lbp-first-reaching-general)))))

(local (defthm fn-lbp-append-associative
 (equal (append (append a b) c) (append a (append b c)))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(binary-append))))))

(local (defthm fn-lbp-nth-one-by-definition
 (equal (nth 1 x) (cadr x))
 :hints (("Goal" :in-theory (enable nth)))))

(local (defthm fn-lbp-retrieval-initial-starts-with-two
 (equal (car (fn-nntp-retrieval-initial kind number article)) 50)
 :hints (("Goal" :in-theory (enable fn-nntp-retrieval-initial fn-nntp-append-pieces)))))

(local (defthm fn-lbp-two-prefix-cannot-be-four
 (implies (equal (car x) 50)
  (not (equal (append x y) (cons 52 z))))
 :hints (("Goal" :cases ((consp x)) :in-theory (enable binary-append)))))

(local (defthm fn-lbp-response-of-bytes-not-unverified-refusal
 (not (equal (fn-nntp-article-response-of-bytes session article bytes number kind updatep group)
             (fn-lb-unverified-refusal refusal-session refusal-kind args)))
 :hints (("Goal" :in-theory (e/d
 (fn-nntp-article-response-of-bytes fn-lb-unverified-refusal fn-nntp-single
  fn-nntp-make-result fn-nntp-reply-effect fn-nntp-crlf)
 (fn-nntp-article-idp fn-rcl-tombstonep fn-nntp-set-cursor fn-nntp-retrieval-initial
  fn-nntp-section-of-bytes fn-nntp-framed-of-bytes fn-nntp-stuff-lines
  fn-lb-unverified-target))))))

(local (defthm fn-lbp-arbitrary-prefix-not-unverified-refusal
 (not (equal (fn-lbc-arbitrary-prefix-reply session article number kind updatep group server i fn-lbc log)
             (fn-lb-unverified-refusal session kind args)))
 :hints (("Goal" :in-theory (e/d (fn-lbc-arbitrary-prefix-reply)
  (fn-lbc-loc0 fn-lbc-loc1 fn-loc-segment fn-loc-offset fn-loc-len
   fn-lb-log-model-read-range fn-lb-log-model-unwire fn-rcompat-served-payload-of-bytes
   fn-nntp-article-response-of-bytes fn-nntp-result-session fn-nntp-response-okp-of-bytes
   fn-nntp-set-cursor fn-lb-unverified-refusal))))))

(local (defthm fn-lbp-selected-read-is-row
 (implies (fn-lbc-selected-reads-entry-p selected kind server v fn-lbc)
          (equal (car selected) :row))
 :hints (("Goal" :in-theory (enable fn-lbc-selected-reads-entry-p)))))

(local (defthm fn-lbp-resident-reply-not-unverified-refusal
 (implies (fn-lbc-selected-reads-entry-p selected kind server v fn-lbc)
  (not (equal (fn-lbc-resident-reply session selected kind server fn-lbc log)
              (fn-lb-unverified-refusal session kind args))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbp-arbitrary-prefix-not-unverified-refusal
   (article (fn-lbc-article (cadr selected) fn-lbc)) (number (nth 2 selected))
   (updatep (nth 3 selected)) (group (nth 4 selected)) (i (cadr selected))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-selected-reads-entry-p fn-lbc-resident-reply fn-lb-unverified-refusal
 fn-nntp-make-result fn-nntp-reply-effect fn-nntp-crlf
 fn-lbp-nth-one-by-definition fn-lbp-retrieval-initial-starts-with-two
 fn-lbp-two-prefix-cannot-be-four fn-lbp-append-associative fn-nntp-string-octets fn-nntp-string-octets-aux fn-nntp-string-octets-aux-loop member-equal))))))

(defthm fn-lbc-retrieval-cold-refuses-exactly-when-entry-bad
(implies (and (fn-lbc-p fn-lbc) (fn-lb-vmap-p fn-lb-vmap)
                (fn-lbc-retrieval-reads-entry-p session archive arts kind args server v fn-lbc seg entry)
                (not (fn-lb-verified-bit seg entry fn-lb-vmap)))
           (iff (equal (fn-lbc-retrieval session archive arts kind args server v log fn-lb-vmap fn-arena fn-lbc)
                       (fn-lb-unverified-refusal session kind args))
                (not (fn-arx-entry-ok (fn-lb-entry-octets seg entry log)
                                      (fn-lb-entry-protected-len seg entry log)))))
 :hints (("Goal" :in-theory (e/d (fn-lbc-retrieval fn-lbc-retrieval-reads-entry-p)
   (fn-lbc-select fn-lbc-selected-reads-entry-p fn-lb-verified-bit fn-arx-entry-ok
    fn-lb-entry-octets fn-lb-entry-protected-len fn-lbc-loc0 fn-lbc-loc1
    fn-loc-segment fn-loc-offset fn-lbc-resident-reply fn-lb-unverified-refusal
    fn-lbc-p fn-lb-vmap-p)))))

(local (defthm fn-lbr11-rows-corr-row-nth
 (implies (and (fn-lbc-rows-corr base rows pm fn-lbc log) (natp base) (natp j) (< j (len rows)))
 (fn-lbc-row-corr (+ base j) (nth j rows) (fn-lbc-value (+ base j) :prefix-max fn-lbc) fn-lbc log))
 :hints (("Goal" :induct (fn-lbp-rows-corr-induction base j rows pm)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbp-rows-corr-induction fn-lbc-rows-corr fn-lbc-row-corr nth natp nfix zp max))))))

(defthm fn-lbc-corresponding-row-at-index
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log) (natp i) (< i (len rows)))
 (fn-lbc-row-corr i (nth i rows) (fn-lbc-value i :prefix-max fn-lbc) fn-lbc log))
 :hints (("Goal" :use ((:instance fn-lbr11-rows-corr-row-nth (base 0) (j i) (pm 0)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-corr natp)))))
