; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-log-fresh-readback")

(local (defthm fn-lbrcla-handle-natural
 (implies (fn-cat-rowp row) (natp (fn-record-payload row)))
 :hints (("Goal" :in-theory (enable fn-cat-rowp)))))

(defthm fn-lbc-row-corr-after-fresh-log-append
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload)
    (fn-lb-log-layoutp log) (not (fn-lb-log-model-row-entry row log))
    (fn-lbc-row-log-guardp row (fn-lb-log-model-append row payload target log)) (fn-lb-log-model-segsp (fn-lb-log-model-append row payload target log))
    (fn-lb-columns-pool-layoutp fn-lbc) (fn-lb-columns-directory-alignedp fn-lbc))
  (fn-lbc-row-corr (fn-lbc-count fn-lbc) row
    (max (nfix (if (zp (fn-lbc-count fn-lbc)) 0 (fn-lbc-value (- (fn-lbc-count fn-lbc) 1) :prefix-max fn-lbc)))
         (nfix (fn-record-stamp row)))
    (fn-lbc-append-row row (fn-lb-log-model-append row payload target log) fn-lbc) (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-row-corr-of-append-row-from-log (log (fn-lb-log-model-append row payload target log)))
       (:instance fn-lb-log-fresh-append-verified-entry)
       (:instance fn-lb-log-fresh-append-stored-range)
       (:instance fn-lb-log-fresh-append-home-frame))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbrcla-handle-natural fn-lb-log-model-append-preserves-layout
   fn-lb-log-append-fresh-row-entry fn-lb-log-append-fresh-row-segment
   fn-lb-log-next-entry-homes-by-definition fn-lb-log-fresh-append-binds-payload
   fn-lb-log-model-next-range)))))
