; LB5 stored ranges and A23 locator/payload conjuncts; owner C.
(in-package "ACL2")
(include-book "catalog-columns-properties")
(include-book "lb-log-model-properties")
(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm fn-lbp-row-corr-wire-fields-by-definition
 (implies (fn-lbc-row-corr i row pm fn-lbc log)
  (let ((payload (fn-lb-log-payload row log))
        (a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc)))
   (and (equal (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc) (fn-rcl-tombstonep payload))
    (equal (fn-lb-log-model-read-range (fn-loc-segment a b) (fn-loc-offset a b) (fn-loc-len a b) log)
           (if (fn-rcl-tombstonep payload) (fn-la-tombstone-raw payload) (fn-la-payload-wire payload)))
    (equal (fn-lbc-value i :head-length fn-lbc) (len (fn-nntp-stuffed-section :head payload)))
    (equal (fn-lbc-directory-value i :raw-head-length fn-lbc)
           (len (fn-la-payload-wire (fn-nntp-split-head (fn-nntp-split-article payload)))))
    (equal (fn-lbc-directory-value i :article-ok fn-lbc)
           (equal (car (fn-nntp-section-of-bytes payload :article)) :ok))
    (equal (fn-lbc-directory-value i :head-ok fn-lbc)
           (equal (car (fn-nntp-section-of-bytes payload :head)) :ok))
    (equal (fn-lbc-directory-value i :body-ok fn-lbc)
           (equal (car (fn-nntp-section-of-bytes payload :body)) :ok)))))

 :hints (("Goal" :in-theory '(fn-lbc-row-corr)))))

(local (defthm fn-lbp-locator-segment-natural (natp (fn-loc-segment a b)) :rule-classes :type-prescription :hints (("Goal" :in-theory (enable fn-loc-segment)))))

(local (defthm fn-lbp-locator-offset-natural (natp (fn-loc-offset a b)) :rule-classes :type-prescription :hints (("Goal" :in-theory (enable fn-loc-offset)))))

(local (defthm fn-lbp-locator-len-natural (natp (fn-loc-len a b)) :rule-classes :type-prescription :hints (("Goal" :in-theory (enable fn-loc-len)))))

(local (defthm fn-lbp-row-corr-non-tomb-range-length
 (implies (and (fn-lbc-row-corr i row pm fn-lbc log)
               (not (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc)))
  (equal (fn-loc-len (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))
         (len (fn-la-payload-wire (fn-lb-log-payload row log)))))
 :hints (("Goal" :use ((:instance fn-lb-log-model-read-range-length
  (seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
  (off (fn-loc-offset (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
  (count (fn-loc-len (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))))
 :in-theory (disable fn-lbc-row-corr fn-lbc-flag fn-lb-log-payload fn-lbc-loc0 fn-lbc-loc1
  fn-loc-segment fn-loc-offset fn-loc-len fn-lb-log-model-read-range fn-la-payload-wire fn-rcl-tombstonep)))))

(local (in-theory (disable fn-lbp-row-corr-non-tomb-range-length)))

(local (defthm fn-lbp-stored-range-tomb-of-row-corr
 (implies (and (fn-lbc-row-corr i row pm fn-lbc log)
               (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc))
  (equal (fn-lbc-stored-range i kind fn-lbc log)
         (fn-nntp-stuffed-section kind (fn-lb-log-payload row log))))
 :hints (("Goal" :in-theory (e/d (fn-lbc-stored-range fn-la-tombstone-raw)
  (fn-lbc-row-corr fn-lbc-flag fn-lb-log-payload fn-lbc-loc0 fn-lbc-loc1
   fn-loc-segment fn-loc-offset fn-loc-len fn-lb-log-model-read-range
   fn-lbc-value fn-lbc-directory-value fn-rcl-tombstonep fn-nntp-stuffed-section))))))

(local (defthm fn-lbp-stored-article-of-row-corr
 (implies (fn-lbc-row-corr i row pm fn-lbc log)
  (equal (fn-lbc-stored-range i :article fn-lbc log)
         (fn-nntp-stuffed-section :article (fn-lb-log-payload row log))))
 :hints (("Goal" :in-theory (e/d (fn-lbc-stored-range fn-la-tombstone-raw)
  (fn-lbc-row-corr fn-lbc-flag fn-lb-log-payload fn-lbc-loc0 fn-lbc-loc1
   fn-loc-segment fn-loc-offset fn-loc-len fn-lb-log-model-read-range
   fn-lbc-value fn-lbc-directory-value fn-rcl-tombstonep fn-nntp-stuffed-section
   fn-nntp-section-of-bytes fn-la-payload-wire))))))

(local (defthm fn-lbr10-stored-head-ok-of-row-corr
 (implies (and (fn-lbc-row-corr i row pm fn-lbc log)
               (not (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc))
               (fn-lbc-directory-value i :head-ok fn-lbc))
  (equal (fn-lbc-stored-range i :head fn-lbc log)
         (fn-nntp-stuffed-section :head (fn-lb-log-payload row log))))
 :hints (("Goal" :use
  ((:instance fn-lbp-row-corr-non-tomb-range-length)
   (:instance fn-lb-log-model-successful-head-body-have-split
    (kind :head) (payload (fn-lb-log-payload row log)))
   (:instance fn-lb-log-model-wire-split-length (payload (fn-lb-log-payload row log)))
   (:instance fn-lb-log-model-wire-head-take (payload (fn-lb-log-payload row log)))
   (:instance fn-lb-log-model-read-range-contained-value
    (seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
    (off (fn-loc-offset (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
    (length (fn-loc-len (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
    (inner (fn-loc-offset (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
    (count (len (fn-la-payload-wire (fn-nntp-split-head (fn-nntp-split-article (fn-lb-log-payload row log))))))))
 :in-theory (e/d (fn-lbc-stored-range nthcdr)
  (fn-lbp-row-corr-non-tomb-range-length fn-lb-log-model-successful-head-body-have-split
   fn-lb-log-model-wire-split-length fn-lb-log-model-wire-head-take
   fn-lbc-row-corr fn-lbc-flag fn-lb-log-payload fn-lbc-value fn-lbc-directory-value
   fn-lbc-loc0 fn-lbc-loc1 fn-loc-segment fn-loc-offset fn-loc-len
   fn-lb-log-model-read-range fn-nntp-stuffed-section fn-la-payload-wire
   fn-rcl-tombstonep fn-nntp-split-head fn-nntp-split-body fn-nntp-split-article
   fn-nntp-section-of-bytes))))))

(local (defthm fn-lbr10-stored-body-ok-of-row-corr
 (implies (and (fn-lbc-row-corr i row pm fn-lbc log)
               (not (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc))
               (fn-lbc-directory-value i :body-ok fn-lbc))
  (equal (fn-lbc-stored-range i :body fn-lbc log)
         (fn-nntp-stuffed-section :body (fn-lb-log-payload row log))))
 :hints (("Goal" :use
  ((:instance fn-lbp-row-corr-non-tomb-range-length)
   (:instance fn-lb-log-model-successful-head-body-have-split
    (kind :body) (payload (fn-lb-log-payload row log)))
   (:instance fn-lb-log-model-wire-split-length (payload (fn-lb-log-payload row log)))
   (:instance fn-lb-log-model-wire-body-take (payload (fn-lb-log-payload row log)))
   (:instance fn-lb-log-model-read-range-contained-value
    (seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
    (off (fn-loc-offset (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
    (length (fn-loc-len (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
    (inner (+ (fn-loc-offset (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)) (len (fn-la-payload-wire (fn-nntp-split-head (fn-nntp-split-article (fn-lb-log-payload row log))))) 2))
    (count (nfix (- (- (fn-loc-len (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)) (len (fn-la-payload-wire (fn-nntp-split-head (fn-nntp-split-article (fn-lb-log-payload row log)))))) 2)))))
 :in-theory (e/d (fn-lbc-stored-range nthcdr)
  (fn-lbp-row-corr-non-tomb-range-length fn-lb-log-model-successful-head-body-have-split
   fn-lb-log-model-wire-split-length fn-lb-log-model-wire-body-take
   fn-lbc-row-corr fn-lbc-flag fn-lb-log-payload fn-lbc-value fn-lbc-directory-value
   fn-lbc-loc0 fn-lbc-loc1 fn-loc-segment fn-loc-offset fn-loc-len
   fn-lb-log-model-read-range fn-nntp-stuffed-section fn-la-payload-wire
   fn-rcl-tombstonep fn-nntp-split-head fn-nntp-split-body fn-nntp-split-article
   fn-nntp-section-of-bytes))))))

(local (defthm fn-lbr10-stored-head-bad-of-row-corr
 (implies (and (fn-lbc-row-corr i row pm fn-lbc log)
               (not (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc))
               (not (fn-lbc-directory-value i :head-ok fn-lbc)))
  (equal (fn-lbc-stored-range i :head fn-lbc log)
         (fn-nntp-stuffed-section :head (fn-lb-log-payload row log))))
 :hints (("Goal" :in-theory (e/d (fn-lbc-stored-range)
 (fn-lbc-row-corr fn-lbc-flag fn-lbc-directory-value fn-lbc-value fn-lbc-loc0 fn-lbc-loc1
  fn-loc-segment fn-loc-offset fn-loc-len fn-lb-log-payload fn-nntp-stuffed-section
  fn-nntp-section-of-bytes fn-la-payload-wire fn-rcl-tombstonep fn-lb-log-model-read-range))))))

(local (defthm fn-lbr10-stored-body-bad-of-row-corr
 (implies (and (fn-lbc-row-corr i row pm fn-lbc log)
               (not (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc))
               (not (fn-lbc-directory-value i :body-ok fn-lbc)))
  (equal (fn-lbc-stored-range i :body fn-lbc log)
         (fn-nntp-stuffed-section :body (fn-lb-log-payload row log))))
 :hints (("Goal" :in-theory (e/d (fn-lbc-stored-range)
 (fn-lbc-row-corr fn-lbc-flag fn-lbc-directory-value fn-lbc-value fn-lbc-loc0 fn-lbc-loc1
  fn-loc-segment fn-loc-offset fn-loc-len fn-lb-log-payload fn-nntp-stuffed-section
  fn-nntp-section-of-bytes fn-la-payload-wire fn-rcl-tombstonep fn-lb-log-model-read-range))))))

(local (defthm fn-lbr10-stored-head-of-row-corr
 (implies (fn-lbc-row-corr i row pm fn-lbc log)
  (equal (fn-lbc-stored-range i :head fn-lbc log)
         (fn-nntp-stuffed-section :head (fn-lb-log-payload row log))))
 :hints (("Goal" :cases ((fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc)
   (and (not (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc)) (fn-lbc-directory-value i :head-ok fn-lbc)))
 :in-theory (disable fn-lbc-stored-range fn-lbc-row-corr fn-lbc-flag fn-lbc-directory-value
  fn-lb-log-payload fn-nntp-stuffed-section fn-nntp-section-of-bytes fn-rcl-tombstonep)))))

(local (defthm fn-lbr10-stored-body-of-row-corr
 (implies (fn-lbc-row-corr i row pm fn-lbc log)
  (equal (fn-lbc-stored-range i :body fn-lbc log)
         (fn-nntp-stuffed-section :body (fn-lb-log-payload row log))))
 :hints (("Goal" :cases ((fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc)
   (and (not (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc)) (fn-lbc-directory-value i :body-ok fn-lbc)))
 :in-theory (disable fn-lbc-stored-range fn-lbc-row-corr fn-lbc-flag fn-lbc-directory-value
  fn-lb-log-payload fn-nntp-stuffed-section fn-nntp-section-of-bytes fn-rcl-tombstonep)))))

(local (defthm fn-lbr10-stored-range-of-row-corr
 (implies (and (fn-lbc-row-corr i row pm fn-lbc log) (member-equal kind '(:article :head :body)))
  (equal (fn-lbc-stored-range i kind fn-lbc log)
         (fn-nntp-stuffed-section kind (fn-lb-log-payload row log))))
 :hints (("Goal" :cases ((equal kind :article) (equal kind :head))
 :in-theory (disable fn-lbc-stored-range fn-lbc-row-corr fn-lb-log-payload fn-nntp-stuffed-section)))))

(local (defun fn-lbr10-rows-corr-induction (base j rows pm)
 (declare (xargs :measure (nfix j) :verify-guards nil))
 (if (and (consp rows) (not (zp j)))
  (fn-lbr10-rows-corr-induction (+ 1 (nfix base)) (- j 1) (cdr rows)
    (max (nfix pm) (nfix (fn-record-stamp (car rows)))))
  (list base pm))))

(local (defthm fn-lbr10-rows-corr-stored-nth
 (implies (and (fn-lbc-rows-corr base rows pm fn-lbc log)
               (natp base) (natp j) (< j (len rows)) (member-equal kind '(:article :head :body)))
  (equal (fn-lbc-stored-range (+ base j) kind fn-lbc log)
         (fn-nntp-stuffed-section kind (fn-lb-log-payload (nth j rows) log))))
 :hints (("Goal" :induct (fn-lbr10-rows-corr-induction base j rows pm)
 :in-theory (e/d (fn-lbc-rows-corr nth)
  (fn-lbc-row-corr fn-lbc-stored-range fn-nntp-stuffed-section fn-lb-log-payload fn-record-stamp))))))

(defthm fn-lbc-stored-range-is-wire-section
  (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
                (natp i) (< i (len rows)) (member-equal kind '(:article :head :body)))
           (equal (fn-lbc-stored-range i kind fn-lbc log)
                  (fn-nntp-stuffed-section kind (fn-lb-log-payload (nth i rows) log))))
 :hints (("Goal" :use ((:instance fn-lbr10-rows-corr-stored-nth (base 0) (j i) (pm 0)))
 :in-theory (e/d (fn-lbc-corr)
  (fn-lbc-p fn-cat$ap fn-lbc-rows-corr fn-lbc-stored-range fn-nntp-stuffed-section fn-lb-log-payload)))))

(local (defthm fn-lbr10-lc-resolving-row-locator-in-log
 (implies (fn-lc-locator-resolves fn-lbc i log)
  (let* ((a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc))
         (seg (fn-lb-log-model-segment (fn-loc-segment a b) log)))
   (and seg (fn-locp a b)
    (fn-lb-log-model-range-in-entries (fn-loc-offset a b) (fn-loc-len a b) (caddr seg))
    (not (equal (fn-lb-log-model-read-range (fn-loc-segment a b) (fn-loc-offset a b)
                                          (fn-loc-len a b) log) :bad)))))
 :hints (("Goal" :in-theory (e/d (fn-lc-locator-resolves fn-lc-read-range fn-lb-log-model-read-range)
  (fn-lc-bound-row fn-held-p fn-lc-expected-range fn-lb-log-payload fn-lc-home-position
   fn-lc-read-home-frame fn-lc-expected-home-frame fn-locp fn-loc-segment fn-loc-offset fn-loc-len
   fn-lbc-loc0 fn-lbc-loc1 fn-lb-log-model-segment fn-lb-log-model-range-in-entries take nthcdr))))))

(local (defthm fn-lbr10-lc-resolve-from-gives-locators-in-log
 (implies (fn-lc-resolve-from i fn-lbc log) (fn-lb-locators-in-log-from i fn-lbc log))
 :hints (("Goal" :induct (fn-lc-resolve-from i fn-lbc log)
 :in-theory (e/d (fn-lc-resolve-from fn-lc-count fn-lb-locators-in-log-from)
 (fn-lbc-count fn-lc-locator-resolves fn-lbc-loc0 fn-lbc-loc1 fn-locp
  fn-loc-segment fn-loc-offset fn-loc-len fn-lb-log-model-segment
  fn-lb-log-model-range-in-entries fn-lb-log-model-read-range))))))

(defthm fn-lc-locators-resolve-gives-locators-in-log
 (implies (fn-lc-locators-resolve fn-lbc log) (fn-lb-locators-in-log fn-lbc log))
 :hints (("Goal" :in-theory (e/d (fn-lc-locators-resolve fn-lb-locators-in-log)
 (fn-lc-resolve-from fn-lb-locators-in-log-from)))))

(local (defthm fn-lbr10-row-corr-binds-payload
 (implies (fn-lbc-row-corr i row pm fn-lbc log)
  (let ((a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc)))
   (equal (fn-lb-log-model-read-range (fn-loc-segment a b) (fn-loc-offset a b) (fn-loc-len a b) log)
          (fn-lc-expected-range (fn-lb-log-payload row log)))))
 :hints (("Goal" :in-theory (e/d (fn-lc-expected-range)
 (fn-lbc-row-corr fn-lb-log-payload fn-lbc-loc0 fn-lbc-loc1 fn-loc-segment fn-loc-offset
  fn-loc-len fn-lb-log-model-read-range fn-rcl-tombstonep fn-la-tombstone-raw fn-la-payload-wire))))))

(local (defthm fn-lbr10-rows-corr-bind-payloads
 (implies (fn-lbc-rows-corr i rows pm fn-lbc log)
          (fn-lb-log-binds-payloads-from i rows fn-lbc log))
 :hints (("Goal" :induct (fn-lbc-rows-corr i rows pm fn-lbc log)
 :in-theory (e/d (fn-lbc-rows-corr fn-lb-log-binds-payloads-from)
 (fn-lbc-row-corr fn-lbc-loc0 fn-lbc-loc1 fn-loc-segment fn-loc-offset fn-loc-len
  fn-lb-log-model-read-range fn-lc-expected-range fn-lb-log-payload fn-record-stamp))))))

(defthm fn-lb-served-log-invp-gives-approved-conjuncts
 (implies (fn-lb-served-log-invp log fn-lb-vmap fn-lbc rows)
          (and (fn-lb-locators-in-log fn-lbc log) (fn-lb-log-binds-payloads fn-lbc rows log)))
 :hints (("Goal" :in-theory (e/d (fn-lb-served-log-invp fn-lbc-corr fn-lb-log-binds-payloads)
 (fn-lb-verified-invp fn-lc-locators-resolve fn-lb-locators-in-log fn-lbc-rows-corr
  fn-lb-log-binds-payloads-from fn-lbc-count fn-lbc-tables-corr fn-lbc-slots-corr
  fn-lbc-number-rows-covered fn-lbc-summaries-corr fn-lbc-row-group-keys fn-lbc-summary-groups)))))

(local (defthm fn-lbr10-stuffed-section-proper
 (true-listp (fn-nntp-stuffed-section kind payload))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (e/d (fn-nntp-stuffed-section)
 (fn-nntp-section-of-bytes fn-nntp-stuff-lines))))))

(local (defthm fn-lbr10-row-corr-sections-proper
 (implies (fn-lbc-row-corr i row pm fn-lbc log)
  (and (true-listp (fn-lbc-stored-range i :article fn-lbc log))
       (true-listp (fn-lbc-stored-range i :head fn-lbc log))
       (true-listp (fn-lbc-stored-range i :body fn-lbc log))))
 :hints (("Goal" :in-theory (disable fn-lbc-row-corr fn-lbc-stored-range
  fn-nntp-stuffed-section fn-lb-log-payload)))))

(local (defthm fn-lbr10-section-values-at-count-by-definition
 (fn-lbc-section-values-guardp (fn-lbc-count fn-lbc) fn-lbc log)
 :hints (("Goal" :expand ((fn-lbc-section-values-guardp (fn-lbc-count fn-lbc) fn-lbc log))
 :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbr10-rows-corr-establish-section-values
 (implies (and (fn-lbc-rows-corr i rows pm fn-lbc log) (natp i)
               (equal (fn-lbc-count fn-lbc) (+ i (len rows))))
          (fn-lbc-section-values-guardp i fn-lbc log))
 :hints (("Goal" :induct (fn-lbc-rows-corr i rows pm fn-lbc log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-rows-corr fn-lbc-section-values-guardp fn-lbr10-row-corr-sections-proper
   fn-lbr10-section-values-at-count-by-definition))))))

(defthm fn-lbc-corr-establishes-section-values-guard
 (implies (fn-lbc-corr fn-lbc rows log)
          (fn-lbc-section-values-guardp 0 fn-lbc log))
 :hints (("Goal" :use ((:instance fn-lbr10-rows-corr-establish-section-values (i 0) (pm 0)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-corr)))))
