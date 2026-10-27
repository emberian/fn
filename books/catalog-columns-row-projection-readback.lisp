; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-composite-readback")

(local (defthm fn-lbrpr-row-withdrawn-type
 (implies (fn-cat-rowp row) (fn-held-withdrawnp (fn-held-withdrawn row)))
 :hints (("Goal" :in-theory '(fn-cat-rowp)))))

(local (defthm fn-lbrpr-withdrawn-normalization
 (implies (and (fn-held-withdrawnp w) w)
  (equal (cons (nfix (car w)) (nfix (cdr w))) w))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-held-withdrawnp nfix))))))

(defthm fn-lbc-withdrawn-of-append-row-new
 (implies (fn-cat-rowp row)
  (equal (fn-lbc-withdrawn (fn-lbc-count fn-lbc) (fn-lbc-append-row row log fn-lbc))
         (fn-held-withdrawn row)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbrpr-row-withdrawn-type))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-withdrawn fn-lbc-withdrawn-flag-of-append-row-new
     fn-lbc-withdrawal-at-of-append-row-new fn-lbc-withdrawal-by-of-append-row-new
     fn-lbrpr-withdrawn-normalization)))))

(local (defthm fn-lbrpr-row-body-start-type
 (implies (fn-cat-rowp row)
  (or (null (fn-hf-body-start (fn-held-facts row)))
      (natp (fn-hf-body-start (fn-held-facts row)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-cat-rowp fn-hf-p fn-hf-startp))))))

(local (defthm fn-lbrpr-nfix-natural
 (implies (natp x) (equal (nfix x) x))
 :hints (("Goal" :in-theory (enable nfix)))))

(defthm fn-lbc-served-row-of-append-row-new
 (implies (and (fn-cat-rowp row) (fn-lb-columns-pool-layoutp fn-lbc)
               (fn-lb-columns-directory-alignedp fn-lbc))
  (equal (fn-lbc-served-row (fn-lbc-count fn-lbc) (fn-lbc-append-row row log fn-lbc))
         (fn-cat-served-projection row)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbrpr-row-body-start-type))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-served-row fn-cat-served-projection fn-lbc-msgid-of-append-row-new
     fn-lbc-handle-of-append-row-new fn-lbc-groups-of-append-row-new
     fn-lbc-numbers-of-append-row-new fn-lbc-stamp-of-append-row-new
     fn-lbc-withdrawn-of-append-row-new fn-lbc-facts-octets-of-append-row-new
     fn-lbc-body-start-present-of-append-row-new fn-lbc-body-start-of-append-row-new
     fn-lbc-body-lines-of-append-row-new fn-lbc-original-nov-of-append-row-new
     fn-lbc-txid-of-append-row-new fn-lbc-generation-of-append-row-new
     fn-lbc-charge-of-append-row-new fn-lbc-sequence-of-append-row-new fn-lbrpr-nfix-natural
     (:executable-counterpart natp) (:executable-counterpart equal))))))
