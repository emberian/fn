; Live-number eligibility from resident columns; no row reconstruction or decode.
(in-package "ACL2")
(include-book "catalog-columns-number-correspondence")

(local (defthm fn-lbcln-escape-at-recognized-index
 (implies (and (natp start) (natp i) (<= start i)
               (< i (fn-lbc-count fn-lbc)) (fn-lbc-escape-cellsp start fn-lbc))
  (alistp (fn-lbc-escape-store-get i fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-escape-cellsp start fn-lbc)
  :in-theory (e/d (fn-lbc-escape-cellsp natp nfix)
   (fn-lbc-p fn-lbc-count fn-lbc-escape-store-get))))))
(local (defthm fn-lbcln-escape-at-zero
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lbc-escape-cellsp 0 fn-lbc))
  (alistp (fn-lbc-escape-store-get i fn-lbc)))
 :hints (("Goal" :use ((:instance fn-lbcln-escape-at-recognized-index (start 0)))
  :in-theory (theory 'ground-zero)))))

(defun fn-lbc-live-numberp (group number fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-escape-cellsp 0 fn-lbc) :verify-guards nil))
 (let ((i (fn-lbc-number-get group number fn-lbc)))
  (and (natp i) (< i (fn-lbc-count fn-lbc))
       (posp number) (<= number *fn-nntp-max-article-number*)
       (not (fn-lbc-withdrawn i fn-lbc))
       (let ((nov (fn-lbc-original-nov i fn-lbc)))
        (and (fn-hnov-p nov) (not (fn-hnov-tomb nov))))
       (fn-scat-msgid-idp (fn-lbc-msgid i fn-lbc)))))
(verify-guards fn-lbc-live-numberp
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbcln-escape-at-zero natp posp eqlablep)))))

(local (defthm fn-lbcln-reference-number-binding
 (implies (and (natp start) (fn-cat-number-seq group number rows start))
  (and (natp (fn-cat-number-seq group number rows start))
       (<= start (fn-cat-number-seq group number rows start))
       (< (fn-cat-number-seq group number rows start) (+ start (len rows)))
       (equal (fn-held-number-in group (nth (- (fn-cat-number-seq group number rows start) start) rows)) number)))
 :hints (("Goal" :induct (fn-cat-number-seq group number rows start)
  :in-theory (union-theories (theory 'ground-zero) '(fn-cat-number-seq nth len natp))))))

(defthm fn-lbc-live-numberp-is-reference
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log))
  (iff (fn-lbc-live-numberp group number fn-lbc) (fn-cat-live-numberp group number rows)))
 :hints (("Goal" :do-not-induct t
  :cases ((fn-cat-number-seq group number rows 0))
  :use ((:instance fn-lbcln-reference-number-binding (start 0)))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-live-numberp fn-cat-live-numberp fn-cat-live-rowp
     fn-cat-row-availablep fn-cat-row-facts-decidedp
     fn-lbc-number-get-is-abstract fn-lbc-corr-count-is-length
     fn-lbc-served-fields-are-abstract fn-lbc-original-nov-is-abstract natp)))))
