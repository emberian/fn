; The existing resolver supplies every old row domain needed for fresh append.
(in-package "ACL2")
(include-book "catalog-columns-append-resolver-domains")

(local (defthm fn-lbarp-payload-survives-distinct-append
 (implies (and (natp (fn-record-payload old))
  (or (not (equal (fn-record-sequence old) (fn-record-sequence row)))
      (not (equal (fn-record-payload old) (fn-record-payload row)))))
  (equal (fn-lb-log-payload old (fn-lb-log-model-append row payload target log)) (fn-lb-log-payload old log)))
 :hints (("Goal" :use fn-lb-log-row-entry-of-distinct-append
  :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-payload))))))

(defthm fn-lbc-resolved-row-corr-survives-distinct-append
 (implies (and (fn-lbc-row-corr i old pm fn-lbc-v log) (fn-lc-locator-resolves fn-lbc-v i log)
  (or (not (equal (fn-record-sequence old) (fn-record-sequence row)))
      (not (equal (fn-record-payload old) (fn-record-payload row)))))
  (fn-lbc-row-corr i old pm fn-lbc-v (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-row-corr-log-congruence-by-definition (new-log (fn-lb-log-model-append row payload target log)))
        (:instance fn-lbc-resolved-row-corr-readable-ranges)
        (:instance fn-lbc-resolved-row-corr-handle-is-natural)
        (:instance fn-lbc-row-corr-home-entry-has-shape-by-definition)
        (:instance fn-lbc-home-entry-survives-log-append)
        (:instance fn-lbarp-payload-survives-distinct-append)
        (:instance fn-lb-log-append-preserves-verified-entry
         (seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)))
         (off (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))))
        (:instance fn-lb-log-append-preserves-existing-range
         (seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)))
         (off (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)))
         (count (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))))
        (:instance fn-lb-log-append-preserves-existing-home-frame
         (position (list (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))
          (+ (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))
             (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)))))))
  :in-theory (theory 'ground-zero))))

(defthm fn-lbc-resolved-locator-survives-distinct-append
 (implies (and (fn-lbc-row-corr i old pm fn-lbc-v log) (fn-lc-locator-resolves fn-lbc-v i log)
  (or (not (equal (fn-record-sequence old) (fn-record-sequence row)))
      (not (equal (fn-record-payload old) (fn-record-payload row)))))
  (fn-lc-locator-resolves fn-lbc-v i (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-at-survives-log-append)
        (:instance fn-lbc-row-corr-home-entry-has-shape-by-definition)
        (:instance fn-lbc-at-key-is-row-corr-key-by-definition)
        (:instance fn-lbarp-payload-survives-distinct-append (old (fn-lbc-at i fn-lbc-v log)))
        (:instance fn-held-p-implies-cat-rowp (x (fn-lbc-at i fn-lbc-v log)))
        (:instance fn-cat-rowp-fields (h (fn-lbc-at i fn-lbc-v log))))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lc-locator-resolves fn-lc-bound-row fn-lc-read-range fn-lc-read-home-frame fn-lc-home-position
     fn-lb-log-append-preserves-existing-range fn-lb-log-append-preserves-existing-home-frame)))))

(local (defthm fn-lbarp-resolved-suffix-survives-distinct-append
 (implies (and (natp i) (equal (fn-lbc-count fn-lbc-v) (+ i (len rows)))
  (fn-lbc-rows-corr i rows pm fn-lbc-v log) (fn-lc-resolve-from i fn-lbc-v log)
  (fn-lb-catalog-distinct-log-keyp row rows))
  (and (fn-lbc-rows-corr i rows pm fn-lbc-v (fn-lb-log-model-append row payload target log))
       (fn-lc-resolve-from i fn-lbc-v (fn-lb-log-model-append row payload target log))))
 :hints (("Goal" :induct (fn-lbc-rows-corr i rows pm fn-lbc-v log)
  :expand ((fn-lc-resolve-from i fn-lbc-v log)
           (fn-lc-resolve-from i fn-lbc-v (fn-lb-log-model-append row payload target log)))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-rows-corr fn-lb-catalog-distinct-log-keyp fn-lc-count
     fn-lbc-resolved-row-corr-survives-distinct-append
     fn-lbc-resolved-locator-survives-distinct-append len natp nfix))))))

(defthm fn-lb-served-log-invp-of-append
 (implies (and (fn-lb-served-log-invp log fn-lb-vmap-v fn-lbc-v rows)
  (fn-lb-catalog-distinct-log-keyp row rows) (fn-cat-rowp row)
  (fn-cbor-octet-listp payload) (unsigned-byte-p 64 target))
  (fn-lb-served-log-invp (fn-lb-log-model-append row payload target log) fn-lb-vmap-v fn-lbc-v rows))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbarp-resolved-suffix-survives-distinct-append (i 0) (pm 0)))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-served-log-invp fn-lbc-corr fn-lc-locators-resolve
     fn-lb-log-append-preserves-type fn-lb-verified-invp-of-append)))))
