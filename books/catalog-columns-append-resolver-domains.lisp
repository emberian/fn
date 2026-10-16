; Resolver ownership supplies row-key domains independently of the catalog recognizer.
(in-package "ACL2")
(include-book "catalog-columns-append-invariant")

(local (defthm fn-lbard-at-key-by-definition
 (and (equal (fn-record-payload (fn-lbc-at i fn-lbc-v log)) (nth 1 (fn-lbc-served-row i fn-lbc-v)))
      (equal (fn-record-sequence (fn-lbc-at i fn-lbc-v log)) (nth 8 (fn-lbc-served-row i fn-lbc-v))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-at fn-held-make fn-record-payload fn-record-sequence fn-held-payload fn-held-sequence nth))))))
(local (defthm fn-lbard-projection-key-by-definition
 (implies (equal (fn-lbc-served-row i fn-lbc-v) (fn-cat-served-projection old))
  (and (equal (nth 1 (fn-lbc-served-row i fn-lbc-v)) (fn-record-payload old))
       (equal (nth 8 (fn-lbc-served-row i fn-lbc-v)) (fn-record-sequence old))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-served-row fn-cat-served-projection nth))))))
(defthm fn-lbc-at-key-is-row-corr-key-by-definition
 (implies (fn-lbc-row-corr i old pm fn-lbc-v log)
  (and (equal (fn-record-payload (fn-lbc-at i fn-lbc-v log)) (fn-record-payload old))
       (equal (fn-record-sequence (fn-lbc-at i fn-lbc-v log)) (fn-record-sequence old))))
 :hints (("Goal" :use (fn-lbard-at-key-by-definition fn-lbard-projection-key-by-definition)
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-row-corr)))))

(defthm fn-lbc-at-survives-log-append
 (implies (fn-lbc-home-entry i fn-lbc-v log)
  (equal (fn-lbc-at i fn-lbc-v (fn-lb-log-model-append row payload target log))
         (fn-lbc-at i fn-lbc-v log)))
 :hints (("Goal" :use fn-lbc-home-entry-survives-log-append
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-at)))))

(defthm fn-lbc-resolved-row-corr-handle-is-natural
 (implies (and (fn-lbc-row-corr i old pm fn-lbc-v log)
               (fn-lc-locator-resolves fn-lbc-v i log))
  (natp (fn-record-payload old)))
 :hints (("Goal" :use (fn-lbc-at-key-is-row-corr-key-by-definition
   (:instance fn-held-p-implies-cat-rowp (x (fn-lbc-at i fn-lbc-v log)))
   (:instance fn-cat-rowp-fields (h (fn-lbc-at i fn-lbc-v log))))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lc-locator-resolves fn-lc-bound-row fn-held-p-implies-cat-rowp fn-cat-rowp-fields)))))

(defthm fn-lbc-resolved-row-corr-readable-ranges
 (implies (and (fn-lbc-row-corr i old pm fn-lbc-v log)
               (fn-lc-locator-resolves fn-lbc-v i log))
  (let* ((seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)))
         (off (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)))
         (n (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))))
   (and (fn-arx-entry-ok (fn-lb-entry-octets seg off log) (fn-lb-entry-protected-len seg off log))
        (not (equal (fn-lb-log-model-read-range seg off n log) :bad))
        (not (equal (fn-lb-log-model-read-home-frame (list seg (+ off n)) log) :bad)))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-row-corr fn-lc-locator-resolves fn-lc-read-range fn-lc-read-home-frame fn-lc-home-position)))))

(local (defthm fn-lbard-entryp-consp
 (implies (fn-lb-log-model-entryp entry) (consp entry)) :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-entryp len))))))
(defthm fn-lbc-row-corr-home-entry-has-shape-by-definition
 (implies (fn-lbc-row-corr i old pm fn-lbc-v log) (consp (fn-lbc-home-entry i fn-lbc-v log)))
 :hints (("Goal" :use ((:instance fn-lbard-entryp-consp (entry (fn-lbc-home-entry i fn-lbc-v log))))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-row-corr)))))
