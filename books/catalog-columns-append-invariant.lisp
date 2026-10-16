; Appending a distinct accepted record preserves resident rows and their log bindings.
(in-package "ACL2")
(include-book "catalog-columns-served-preservation")
(include-book "catalog-columns-log-old-row-preservation")
(include-book "lb-log-guard-invariants")
(include-book "lb-log-payload-agreement-properties")

(local (defthm fn-lbai-old-handle-natural
 (implies (fn-cat-rowp old) (natp (fn-record-payload old)))
 :hints (("Goal" :in-theory '(fn-cat-rowp fn-record-payload fn-held-payload)))))
(local (defthm fn-lbai-next-range-not-bad
 (not (equal (if (fn-rcl-tombstonep payload) (fn-la-tombstone-raw payload) (fn-la-payload-wire payload)) :bad))
 :hints (("Goal" :cases ((equal payload :bad))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-la-tombstone-raw fn-lb-log-model-payload-wire-true-listp true-listp
     (:executable-counterpart fn-rcl-tombstonep)))))))
(local (defthm fn-lbai-home-frame-not-bad
 (implies (fn-cat-rowp old) (not (equal (fn-lb-log-model-home-frame old) :bad)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lb-log-model-home-frame-is-octets (row old)))
  :cases ((equal (fn-lb-log-model-home-frame old) :bad))
  :in-theory (union-theories (theory 'ground-zero) '((:executable-counterpart fn-cbor-octet-listp)))))))
(local (defthm fn-lbai-entryp-present
 (implies (fn-lb-log-model-entryp entry) (consp entry))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lb-log-model-entryp len))))))

(defthm fn-lbc-home-entry-survives-log-append
 (implies (fn-lbc-home-entry i fn-lbc-v log)
  (equal (fn-lbc-home-entry i fn-lbc-v (fn-lb-log-model-append row payload target log))
         (fn-lbc-home-entry i fn-lbc-v log)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lb-log-existing-home-entry-survives-append
   (seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)))
   (position (+ (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))
                (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))))))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-home-entry)))))

(local (defthm fn-lbai-row-corr-home-entry-survives
 (implies (fn-lbc-row-corr i old pm fn-lbc-v log)
  (equal (fn-lbc-home-entry i fn-lbc-v (fn-lb-log-model-append row payload target log))
         (fn-lbc-home-entry i fn-lbc-v log)))
 :hints (("Goal" :use ((:instance fn-lbc-home-entry-survives-log-append)
  (:instance fn-lbai-entryp-present (entry (fn-lbc-home-entry i fn-lbc-v log))))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-row-corr))))))

(local (defthm fn-lbai-payload-of-distinct-append
 (implies (and (fn-cat-rowp old)
  (or (not (equal (fn-record-sequence old) (fn-record-sequence row)))
      (not (equal (fn-record-payload old) (fn-record-payload row)))))
  (equal (fn-lb-log-payload old (fn-lb-log-model-append row payload target log))
         (fn-lb-log-payload old log)))
 :hints (("Goal" :use fn-lb-log-row-entry-of-distinct-append
  :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-payload fn-lbai-old-handle-natural))))))
(local (defthm fn-lbai-row-corr-readable-ranges
 (implies (and (fn-cat-rowp old) (fn-lbc-row-corr i old pm fn-lbc-v log))
  (and (fn-arx-entry-ok
    (fn-lb-entry-octets (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))
                       (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) log)
    (fn-lb-entry-protected-len (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))
                             (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) log))
   (not (equal (fn-lb-log-model-read-range
    (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))
    (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))
    (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) log) :bad))
   (not (equal (fn-lb-log-model-read-home-frame
    (list (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))
     (+ (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))
        (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)))) log) :bad))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-lbai-next-range-not-bad (payload (fn-lb-log-payload old log))))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-row-corr fn-lbai-home-frame-not-bad))))))

(defthm fn-lbc-row-corr-log-congruence-by-definition
 (implies (and
(equal (fn-lbc-home-entry i fn-lbc-v new-log) (fn-lbc-home-entry i fn-lbc-v log))
(equal (fn-lb-log-payload old new-log) (fn-lb-log-payload old log))
(iff (fn-arx-entry-ok (fn-lb-entry-octets (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) new-log) (fn-lb-entry-protected-len (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) new-log)) (fn-arx-entry-ok (fn-lb-entry-octets (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) log) (fn-lb-entry-protected-len (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) log)))
(equal (fn-lb-log-model-read-range (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) new-log) (fn-lb-log-model-read-range (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) log))
(equal (fn-lb-log-model-read-home-frame (list (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (+ (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)))) new-log) (fn-lb-log-model-read-home-frame (list (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (+ (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)))) log)))
 (equal (fn-lbc-row-corr i old pm fn-lbc-v new-log) (fn-lbc-row-corr i old pm fn-lbc-v log)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-row-corr)))))

(defthm fn-lbc-row-corr-survives-distinct-log-append
 (implies (and (fn-cat-rowp old) (fn-lbc-row-corr i old pm fn-lbc-v log)
  (or (not (equal (fn-record-sequence old) (fn-record-sequence row)))
      (not (equal (fn-record-payload old) (fn-record-payload row)))))
  (fn-lbc-row-corr i old pm fn-lbc-v (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-row-corr-log-congruence-by-definition (new-log (fn-lb-log-model-append row payload target log)))
       (:instance fn-lbai-row-corr-readable-ranges)
       (:instance fn-lbai-row-corr-home-entry-survives)
       (:instance fn-lbai-payload-of-distinct-append)
       (:instance fn-lb-log-append-preserves-verified-entry (seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))) (off (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))))
       (:instance fn-lb-log-append-preserves-existing-range (seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))) (off (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))) (count (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v))))
       (:instance fn-lb-log-append-preserves-existing-home-frame (position (list (fn-loc-segment (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (+ (fn-loc-offset (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)) (fn-loc-len (fn-lbc-loc0 i fn-lbc-v) (fn-lbc-loc1 i fn-lbc-v)))))))
 :in-theory (theory 'ground-zero))))

(defun-nx fn-lb-catalog-distinct-log-keyp (row rows)
 (if (consp rows)
  (and (or (not (equal (fn-record-sequence (car rows)) (fn-record-sequence row)))
           (not (equal (fn-record-payload (car rows)) (fn-record-payload row))))
       (fn-lb-catalog-distinct-log-keyp row (cdr rows))) t))

(defthm fn-lb-retained-agreement-survives-distinct-append
 (implies (and (fn-cat-rowsp rows) (fn-lb-retained-payloads-agreep rows log)
               (fn-lb-catalog-distinct-log-keyp row rows))
  (fn-lb-retained-payloads-agreep rows (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :induct (len rows)
 :in-theory (union-theories (theory 'ground-zero)
 '(len fn-cat-rowsp fn-lb-retained-payloads-agreep fn-lb-catalog-distinct-log-keyp
   fn-lb-log-row-copies-agree-of-distinct-append fn-lbai-payload-of-distinct-append
   fn-lbai-old-handle-natural)))))

(local (defthm fn-lbai-rows-corr-survives-distinct-log-append
 (implies (and (fn-cat-rowsp rows) (fn-lbc-rows-corr i rows pm fn-lbc-v log)
               (fn-lb-catalog-distinct-log-keyp row rows))
  (fn-lbc-rows-corr i rows pm fn-lbc-v (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :induct (fn-lbc-rows-corr i rows pm fn-lbc-v log)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-rows-corr fn-cat-rowsp fn-lb-catalog-distinct-log-keyp
     fn-lbc-row-corr-survives-distinct-log-append))))))

(defthm fn-lbc-corr-survives-distinct-log-append
 (implies (and (fn-lbc-corr fn-lbc-v rows log) (fn-cat-rowsp rows)
  (fn-lb-catalog-distinct-log-keyp row rows) (fn-cat-rowp row)
  (fn-cbor-octet-listp payload) (unsigned-byte-p 64 target))
  (fn-lbc-corr fn-lbc-v rows (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-corr fn-lbai-rows-corr-survives-distinct-log-append
     fn-lb-retained-agreement-survives-distinct-append fn-lb-log-append-preserves-type)))))

(local (defthm fn-lbai-row-resolver-survives-distinct-append
 (implies (and (fn-cat-rowp old) (fn-lbc-row-corr i old pm fn-lbc-v log)
               (fn-lc-locator-resolves fn-lbc-v i log)
  (or (not (equal (fn-record-sequence old) (fn-record-sequence row)))
      (not (equal (fn-record-payload old) (fn-record-payload row)))))
  (fn-lc-locator-resolves fn-lbc-v i (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-row-corr-survives-distinct-log-append)
        (:instance fn-lbc-at-is-corresponding-row (row old) (fn-lbc fn-lbc-v))
        (:instance fn-lbc-at-is-corresponding-row (row old) (fn-lbc fn-lbc-v)
         (log (fn-lb-log-model-append row payload target log))))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lc-locator-resolves fn-lc-bound-row fn-lc-read-range fn-lc-read-home-frame
     fn-lc-home-position fn-lbai-payload-of-distinct-append
     fn-lb-log-append-preserves-existing-range fn-lb-log-append-preserves-existing-home-frame))))))

(local (defthm fn-lbai-resolve-suffix-survives-distinct-append
 (implies (and (natp i) (equal (fn-lbc-count fn-lbc-v) (+ i (len rows)))
  (fn-cat-rowsp rows) (fn-lbc-rows-corr i rows pm fn-lbc-v log)
  (fn-lc-resolve-from i fn-lbc-v log) (fn-lb-catalog-distinct-log-keyp row rows))
  (fn-lc-resolve-from i fn-lbc-v (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :induct (fn-lbc-rows-corr i rows pm fn-lbc-v log)
  :expand ((fn-lc-resolve-from i fn-lbc-v log)
           (fn-lc-resolve-from i fn-lbc-v (fn-lb-log-model-append row payload target log)))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-rows-corr fn-cat-rowsp fn-lb-catalog-distinct-log-keyp fn-lc-count
     fn-lbai-row-resolver-survives-distinct-append len natp nfix))))))

(defthm fn-lc-locators-resolve-survives-distinct-append
 (implies (and (fn-lbc-corr fn-lbc-v rows log) (fn-cat-rowsp rows)
  (fn-lc-locators-resolve fn-lbc-v log) (fn-lb-catalog-distinct-log-keyp row rows))
  (fn-lc-locators-resolve fn-lbc-v (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :use ((:instance fn-lbai-resolve-suffix-survives-distinct-append (i 0) (pm 0)))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-corr fn-lc-locators-resolve)))))


