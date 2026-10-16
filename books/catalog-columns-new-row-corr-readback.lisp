; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-home-readback")

(defthm fn-lbc-row-corr-of-append-row-from-log
 (implies (and (fn-cat-rowp row) (fn-lbc-row-log-guardp row log)
               (fn-lb-log-layoutp log) (fn-lb-log-model-segsp log)
               (fn-lb-columns-pool-layoutp fn-lbc) (fn-lb-columns-directory-alignedp fn-lbc)
               (equal (nth 7 (fn-lb-log-model-row-entry row log)) (fn-lb-log-model-homes row)) (fn-arx-entry-ok (fn-lb-entry-octets (fn-lb-log-model-row-segment row log) (nth 3 (fn-lb-log-model-row-entry row log)) log) (fn-lb-entry-protected-len (fn-lb-log-model-row-segment row log) (nth 3 (fn-lb-log-model-row-entry row log)) log)) (equal (fn-lb-log-model-read-range (fn-lb-log-model-row-segment row log) (nth 3 (fn-lb-log-model-row-entry row log)) (nth 4 (fn-lb-log-model-row-entry row log)) log) (if (fn-rcl-tombstonep (fn-lb-log-payload row log)) (fn-la-tombstone-raw (fn-lb-log-payload row log)) (fn-la-payload-wire (fn-lb-log-payload row log)))) (equal (fn-lb-log-model-read-home-frame (list (fn-lb-log-model-row-segment row log) (+ (nth 3 (fn-lb-log-model-row-entry row log)) (nth 4 (fn-lb-log-model-row-entry row log)))) log) (fn-lb-log-model-home-frame row)))
  (fn-lbc-row-corr (fn-lbc-count fn-lbc) row (max (nfix (if (zp (fn-lbc-count fn-lbc)) 0 (fn-lbc-value (- (fn-lbc-count fn-lbc) 1) :prefix-max fn-lbc))) (nfix (fn-record-stamp row))) (fn-lbc-append-row row log fn-lbc) log))
 :hints (("Goal" :do-not-induct t :cases ((fn-lb-log-model-row-entry row log))
  :use ((:instance fn-lbc-locator-of-append-row-new)
        (:instance fn-lb-log-row-entry-binds-identity)
        (:instance fn-lb-log-row-entry-has-native-directory-type))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-corr fn-lbc-home-entry-of-append-row-new fn-lbc-served-row-of-append-row-new fn-lbc-prefix-max-of-append-row-new fn-lbc-msgid-hash-word-of-append-row-new fn-lbc-ingest-verified-flag-of-append-row-new fn-lbc-reclaimed-flag-of-append-row-new fn-lbc-xref-shift-prefix-of-append-row-new fn-lbc-head-length-of-append-row-new fn-lbc-raw-head-length-of-append-row-new fn-lbc-article-ok-of-append-row-new fn-lbc-head-ok-of-append-row-new fn-lbc-body-ok-of-append-row-new fn-lbc-framed-of-append-row-new fn-lbc-render-nov-of-append-row-new fn-lb-log-payload fn-lbc-row-log-guardp (:type-prescription fn-rcl-tombstonep) (:executable-counterpart unsigned-byte-p) (:executable-counterpart nth) (:executable-counterpart equal))))))
