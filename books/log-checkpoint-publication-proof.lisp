; Publication proof context: verify the LB boundary before LC adds codecs.
(in-package "ACL2")
(include-book "pagestore-keystones")
(include-book "log-checkpoint-guard-support")
(include-book "catalog-columns-guards")
(include-book "log-cleaning")
(include-book "log-checkpoint-publication")
(include-book "log-checkpoint-delta")
(include-book "defkeystone")
(include-book "log-checkpoint-publication-algebra")

; Standing rule: publication validity follows from :ok, or is not needed by request order.
(defthm fn-lc-stage-is-the-dirty
 (let ((out (fn-lc-stage old old-header header disk r mode segs outcome fn-lbc)))
    (implies (equal (mv-nth 0 out) :ok)
             (equal (fn-lc-durable-image (mv-nth 2 out) r mode)
                    (pgs-apply-dirty (fn-lc-pages old old-header)
                      (fn-lc-dirty old old-header (fn-lc-columns fn-lbc) header)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-lc-stage-value-is-the-dirty (columns (fn-lc-columns fn-lbc))))
   :in-theory (e/d (fn-lc-stage)
    (fn-lc-stage-value fn-lc-columns fn-lc-columns-value fn-lc-dirty fn-lc-pages
     fn-lc-publicationp fn-lc-durable-image fn-lc-fence-sequence pgs-commit pgs-open
     fn-lc-list-prefixp fn-lc-root-write-after-data-fsyncp
     fn-lc-accepted-stage-value-is-commit fn-lc-stage-value-is-the-dirty)))))

; Standing rule: publication validity follows from :ok, or is not needed by request order.
(defthm fn-lc-image-after-commit
 (let ((out (fn-lc-stage old old-header header disk r mode segs outcome fn-lbc)))
    (implies (equal (mv-nth 0 out) :ok)
             (equal (fn-lc-durable-image (mv-nth 2 out) r mode)
                    (fn-lc-pages (fn-lc-columns fn-lbc) header))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-lc-stage-value-image (columns (fn-lc-columns fn-lbc))))
   :in-theory (e/d (fn-lc-stage)
    (fn-lc-stage-value fn-lc-columns fn-lc-columns-value fn-lc-dirty fn-lc-pages
     fn-lc-publicationp fn-lc-durable-image fn-lc-fence-sequence pgs-commit pgs-open
     fn-lc-list-prefixp fn-lc-root-write-after-data-fsyncp
     fn-lc-accepted-stage-value-is-commit fn-lc-stage-value-image)))))

; Standing rule: publication validity follows from :ok, or is not needed by request order.
(defthm fn-lc-completed-publication-fences
 (let ((out (fn-lc-stage old old-header header disk r mode segs outcome fn-lbc)))
    (implies (equal (mv-nth 0 out) :ok)
             (equal (fn-lc-fence-sequence (mv-nth 4 out))
                    '(:data-fsync :root-write :root-fsync))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-lc-completed-stage-value-fences (columns (fn-lc-columns fn-lbc))))
   :in-theory (e/d (fn-lc-stage)
    (fn-lc-stage-value fn-lc-columns fn-lc-columns-value fn-lc-dirty fn-lc-pages
     fn-lc-publicationp fn-lc-durable-image fn-lc-fence-sequence pgs-commit pgs-open
     fn-lc-list-prefixp fn-lc-root-write-after-data-fsyncp
     fn-lc-accepted-stage-value-is-commit fn-lc-completed-stage-value-fences)))))

; Standing rule: publication validity follows from :ok, or is not needed by request order.
(defthm fn-lc-publication-fences-are-a-prefix
 (let ((out (fn-lc-stage old old-header header disk r mode segs outcome fn-lbc)))
    (and (fn-lc-list-prefixp (fn-lc-fence-sequence (mv-nth 4 out))
                                      '(:data-fsync :root-write :root-fsync))
                  (fn-lc-root-write-after-data-fsyncp (mv-nth 4 out))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-lc-stage-value-fences-prefix (columns (fn-lc-columns fn-lbc))))
   :in-theory (e/d (fn-lc-stage)
    (fn-lc-stage-value fn-lc-columns fn-lc-columns-value fn-lc-dirty fn-lc-pages
     fn-lc-publicationp fn-lc-durable-image fn-lc-fence-sequence pgs-commit pgs-open
     fn-lc-list-prefixp fn-lc-root-write-after-data-fsyncp
     fn-lc-accepted-stage-value-is-commit fn-lc-stage-value-fences-prefix)))))

; Standing rule: an accepted stage already validates its header's type.
(defthm fn-lc-stage-publishes-the-allocation-state
 (let ((out (fn-lc-stage old old-header header disk r mode segs outcome fn-lbc)))
    (implies (equal (mv-nth 0 out) :ok)
             (and (equal (fn-lc-header-next-id (fn-lc-adopted-header (mv-nth 2 out) r mode))
                         (fn-lc-header-next-id header))
                  (equal (fn-lc-header-exhaustedp (fn-lc-adopted-header (mv-nth 2 out) r mode))
                         (fn-lc-header-exhaustedp header)))))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance fn-lc-stage-value-image (columns (fn-lc-columns fn-lbc)))
   (:instance fn-lc-accepted-stage-value-headerp (columns (fn-lc-columns fn-lbc)))
   (:instance fn-lc-image-gives-header (columns (fn-lc-columns fn-lbc))
    (disk (nth 1 (fn-lc-stage-value old old-header (fn-lc-columns fn-lbc)
                                  header disk r mode outcome)))))
  :in-theory (e/d (fn-lc-stage)
   (fn-lc-stage-value fn-lc-columns fn-lc-columns-value fn-lc-pages fn-lc-headerp
    fn-lc-adopted-header fn-lc-durable-image fn-lc-header-next-id fn-lc-header-exhaustedp
    fn-lc-stage-value-image fn-lc-accepted-stage-value-headerp
    fn-lc-accepted-stage-value-is-commit fn-lc-stage-value-is-the-dirty pgs-commit
    fn-lc-image-gives-header pgs-open)))))
