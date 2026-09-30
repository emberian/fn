; Terminal old selected-row decisions, used by full range preservation.
(in-package "ACL2")
(include-book "over-byte-selected-row-relation")

(local
 (defthm fn-obts-actual-old-selected-article-bytes
  (let* ((range (nth 0 s)) (group (nth 0 range)) (number (nth 1 range))
         (v (nth 3 range)) (seq (fn-cnx-view-seq group number v fn-cat))
         (h (fn-record-payload (fn-cat-at seq fn-cat))))
   (implies (and (posp number) (<= number *fn-nntp-max-article-number*) seq
                 (fn-nntp-article-idp (fn-cat-row-article seq fn-arena fn-cat))
                 (natp h))
    (equal (fn-nntp-article-bytes
             (fn-scat-available-article group number v fn-arena fn-cat) fn-arena)
           (nth (fn-obc-selected-handle s fn-cat) fn-arena))))
  :hints (("Goal" :use
   ((:instance fn-scat-available-article-has-actual-selected-source
      (group (nth 0 (nth 0 s))) (number (nth 1 (nth 0 s))) (v (nth 3 (nth 0 s)))))
   :in-theory (e/d (fn-obc-selected-handle)
     (fn-cnx-view-seq fn-cat-at fn-record-payload fn-nntp-article-idp
      fn-cat-row-article fn-nntp-article-bytes fn-scat-available-article nth))))))

(defthm fn-obc-terminal-parser-selected-tombstone-unfolds
 (let* ((range (nth 0 s)) (group (nth 0 range)) (number (nth 1 range))
        (v (nth 3 range)) (seq (fn-cnx-view-seq group number v fn-cat))
        (h (fn-record-payload (fn-cat-at seq fn-cat)))
        (parser (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena))))
  (implies (and (equal (nth 2 s) :parse)
                (fn-obc-parser-prefix-p s fn-arena fn-cat)
                (not (equal (fn-lpc-verdict parser) :yield))
                (posp number) (<= number *fn-nntp-max-article-number*) seq
                (fn-nntp-article-idp (fn-cat-row-article seq fn-arena fn-cat))
                (natp h))
   (equal (fn-lpc-tombstonep parser)
          (fn-nntp-article-tombstonep
           (fn-scat-available-article group number v fn-arena fn-cat) fn-arena))))
 :rule-classes nil
 :hints (("Goal" :use
  (fn-obts-actual-old-selected-article-bytes
   fn-obc-final-parser-tick-is-selected-source-feed
   (:instance fn-lpv-complete-feed-tombstone-is-actual
    (bytes (nth (fn-obc-selected-handle s fn-cat) fn-arena))
    (h (fn-obc-selected-handle s fn-cat)) (pin (nth 1 s))))
  :in-theory (e/d (fn-nntp-article-tombstonep)
   (fn-lpc-tick fn-lpc-verdict fn-lpc-tombstonep fn-lpc-feed fn-lpc-begin
    fn-obc-selected-handle fn-obc-parser-prefix-p fn-cnx-view-seq fn-cat-at
    fn-record-payload fn-nntp-article-idp fn-cat-row-article fn-scat-available-article
    fn-nntp-article-bytes fn-rcl-tombstonep)))))

(local
 (defthm fn-obts-old-nov-ok-is-hnov-ok
  (equal (fn-nov-okp (fn-nov-overview article fn-arena))
         (fn-hnov-ok (fn-hnov-of (fn-nntp-article-bytes article fn-arena))))
  :hints (("Goal" :in-theory
   (e/d (fn-nov-okp fn-nov-overview fn-hnov-of fn-hnov-of-parsed
         fn-hnov-parsed-okp fn-hnov-internals)
        (fn-article-parse fn-article-result-okp fn-article-result-article
         fn-article-syntax-p fn-nntp-article-bytes fn-nov-header-content
         fn-hnov-field fn-nntp-article-length fn-nov-body-line-count
         fn-rcl-tombstonep fn-lpv-actual-parser-catalog-verdict))))))

(local
 (defthm fn-obts-parser-nov-ok-is-verdict
  (equal (fn-hnov-ok (fn-lpc-nov-value parser arena))
         (equal (fn-lpc-verdict parser) :valid))
  :hints (("Goal" :in-theory
   (e/d (fn-lpc-nov-value fn-hnov-internals)
        (fn-lpc-verdict fn-lpc-field fn-lpc-span-value fn-lpc-tombstonep
         fn-record-octets-string))))))

(defthm fn-obc-terminal-parser-selected-validity-unfolds
 (let* ((range (nth 0 s)) (group (nth 0 range)) (number (nth 1 range))
        (v (nth 3 range)) (seq (fn-cnx-view-seq group number v fn-cat))
        (h (fn-record-payload (fn-cat-at seq fn-cat)))
        (parser (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena))))
  (implies (and (equal (nth 2 s) :parse)
                (fn-obc-parser-prefix-p s fn-arena fn-cat)
                (not (equal (fn-lpc-verdict parser) :yield))
                (fn-cbor-octet-listp (nth (fn-obc-selected-handle s fn-cat) fn-arena))
                (posp number) (<= number *fn-nntp-max-article-number*) seq
                (fn-nntp-article-idp (fn-cat-row-article seq fn-arena fn-cat))
                (natp h))
   (equal (equal (fn-lpc-verdict parser) :valid)
          (fn-nov-okp (fn-nov-overview
           (fn-scat-available-article group number v fn-arena fn-cat) fn-arena)))))
 :rule-classes nil
 :hints (("Goal" :use
  (fn-obts-actual-old-selected-article-bytes
   fn-obc-final-parser-tick-has-actual-selected-nov
   (:instance fn-obts-parser-nov-ok-is-verdict
    (parser (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena))) (arena fn-arena))
   (:instance fn-obts-old-nov-ok-is-hnov-ok
    (article (fn-scat-available-article (nth 0 (nth 0 s)) (nth 1 (nth 0 s))
                                      (nth 3 (nth 0 s)) fn-arena fn-cat))))
  :in-theory (disable fn-lpc-tick fn-lpc-verdict fn-lpc-nov-value
   fn-hnov-ok fn-hnov-of fn-obc-selected-handle fn-obc-parser-prefix-p
   fn-cnx-view-seq fn-cat-at fn-record-payload fn-nntp-article-idp
   fn-cat-row-article fn-scat-available-article fn-nntp-article-bytes
   fn-nov-overview fn-nov-okp fn-cbor-octet-listp))))
