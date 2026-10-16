; LB keystones; private proof cuts are scoped, frozen terms unchanged.
(in-package "ACL2")
(include-book "catalog-columns-served")
(include-book "catalog-columns-row-correspondence")
(local (include-book "arithmetic-5/top" :dir :system))



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

(local (defthm fn-lbr11-row-corr-self-prefix
 (implies (fn-lbc-row-corr i row pm fn-lbc log)
  (fn-lbc-row-corr i row (fn-lbc-value i :prefix-max fn-lbc) fn-lbc log))
 :hints (("Goal" :do-not-induct t :in-theory '(fn-lbc-row-corr)))))

(local (defthm fn-lbr11-rows-corr-row-nth
 (implies (and (fn-lbc-rows-corr base rows pm fn-lbc log) (natp base) (natp j) (< j (len rows)))
 (fn-lbc-row-corr (+ base j) (nth j rows) (fn-lbc-value (+ base j) :prefix-max fn-lbc) fn-lbc log))
 :hints (("Goal" :induct (fn-lbp-rows-corr-induction base j rows pm)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbp-rows-corr-induction fn-lbc-rows-corr fn-lbr11-row-corr-self-prefix nth natp nfix zp max))))))

(defthm fn-lbc-corresponding-row-at-index
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log) (natp i) (< i (len rows)))
 (fn-lbc-row-corr i (nth i rows) (fn-lbc-value i :prefix-max fn-lbc) fn-lbc log))
 :hints (("Goal" :use ((:instance fn-lbr11-rows-corr-row-nth (base 0) (j i) (pm 0)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-corr natp)))))
