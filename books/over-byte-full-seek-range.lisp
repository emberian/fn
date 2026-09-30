; Complete old seek branch including cached, absent and unsupported rows.
; Carried cache/source correspondence is not evaluated on a served path.
(in-package "ACL2")
(include-book "over-byte-cached-row-source")
(include-book "over-range-all-step-source")
(include-book "over-reply-row-frame")
(include-book "over-byte-range-relation")
(include-book "over-byte-seek-parser-range")

(local
 (defthm fn-obfs-row-id-is-record-id
  (equal (fn-nntp-article-idp (fn-cat-row-article seq fn-arena fn-cat))
         (fn-scat-msgid-idp (fn-record-msgid (fn-cat-at seq fn-cat))))
  :hints (("Goal" :in-theory
   (e/d (fn-nntp-article-idp fn-scat-msgid-idp)
        (fn-cat-row-article fn-cat-at fn-record-msgid fn-nntp-string-octets
         fn-nntp-message-id-tokenp length))))))

(local
 (defthm fn-obfs-row-article-present
  (consp (fn-cat-row-article seq fn-arena fn-cat))
  :hints (("Goal" :in-theory (enable fn-cat-row-article fn-make-article)))))

(local
 (defthm fn-obfs-selected-article-present
  (implies (and (posp k) (<= k *fn-nntp-max-article-number*)
                (fn-cnx-view-seq group k v fn-cat)
                (fn-scat-msgid-idp (fn-record-msgid
                  (fn-cat-at (fn-cnx-view-seq group k v fn-cat) fn-cat))))
   (consp (fn-scat-available-article group k v fn-arena fn-cat)))
  :hints (("Goal" :in-theory
   (e/d (fn-scat-available-article fn-scat-number-article)
        (fn-cat-row-article fn-cnx-view-seq fn-cat-at fn-record-msgid fn-record-payload
         fn-record-groups fn-held-numbers fn-record-stamp fn-scat-msgid-idp
         fn-nntp-article-idp))))))

(local
 (defthm fn-obfs-append-associative
  (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-obfs-row-ready-residual-unfolds
  (equal (fn-obc-actual-old-residual (fn-obc-row-ready range pin pieces) fn-arena fn-cat)
   (append (if (nth 5 range) (fn-ovw-status (fn-proto-text * :overview)) nil)
           (fn-npw-remaining pieces 0 fn-arena)
           (fn-obc-old-range-reply (fn-obc-next-range range nil) fn-arena fn-cat)))
  :hints (("Goal" :in-theory
   (e/d (fn-obc-actual-old-residual fn-obc-row-ready fn-obc-make
         fn-npw-remaining fn-npw-part-bytes fn-ovw-status)
        (fn-obc-old-range-reply fn-obc-next-range fn-nsw-remaining
         fn-record-string-octets fn-record-string-octets-aux
         explode-nonnegative-integer))))))

(local
 (defthm fn-obfs-old-nov-ok-is-hnov-ok
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
 (defthm fn-obfs-nfix-successor
  (equal (nfix (+ 1 (nfix x))) (+ 1 (nfix x)))
  :hints (("Goal" :in-theory (enable nfix)))))

(local
 (defthm fn-obfs-no-facts-without-selection
  (equal (fn-nrf-facts nil fn-cat) nil)
  :hints (("Goal" :in-theory (enable fn-nrf-facts)))))

(local
 (defthm fn-obfs-facts-imply-selected-handle
  (implies (fn-nrf-facts seq fn-cat)
           (natp (fn-record-payload (fn-cat-at seq fn-cat))))
  :hints (("Goal" :in-theory (enable fn-nrf-facts)))))
(local
 (defthm fn-obfs-facts-imply-selection
  (implies (fn-nrf-facts (fn-cnx-view-seq group k v fn-cat) fn-cat)
           (fn-cnx-view-seq group k v fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-nrf-facts) (fn-cnx-view-seq fn-cat-at))))))
(local
 (defthm fn-obfs-selected-source-length
  (let* ((seq (fn-cnx-view-seq group number v fn-cat))
         (h (fn-record-payload (fn-cat-at seq fn-cat))))
   (implies (and (posp number) (<= number *fn-nntp-max-article-number*) seq
                 (fn-scat-msgid-idp (fn-record-msgid (fn-cat-at seq fn-cat))) (natp h))
    (equal (fn-arena-payload-len (nfix h) fn-arena)
           (len (fn-nntp-article-bytes
             (fn-scat-available-article group number v fn-arena fn-cat) fn-arena)))))
  :hints (("Goal" :use fn-scat-available-article-has-actual-selected-source
   :in-theory (disable fn-cnx-view-seq fn-cat-at fn-record-payload
      fn-scat-available-article fn-nntp-article-bytes fn-cat-row-article
      fn-nntp-article-idp fn-scat-msgid-idp)))))
(local
 (defthm fn-obfs-facts-tomb-is-source-tomb
  (equal (fn-hnov-tomb (fn-hf-nov (fn-held-facts-of bytes)))
         (fn-rcl-tombstonep bytes))
  :hints (("Goal" :use fn-hf-nov-of-held-facts-of
   :in-theory (e/d (fn-hnov-of fn-hnov-of-parsed fn-hnov-internals)
      (fn-hf-nov fn-held-facts-of fn-article-parse fn-hnov-field fn-rcl-tombstonep
       fn-hnov-parsed-okp fn-hf-nov-of-held-facts-of))))))

(local
 (defthm fn-obfs-cache-flags-are-old-flags
  (implies (equal facts (fn-held-facts-of (fn-nntp-article-bytes article fn-arena)))
   (and (equal (fn-hnov-ok (fn-hf-nov facts))
               (fn-nov-okp (fn-nov-overview article fn-arena)))
        (equal (fn-hnov-tomb (fn-hf-nov facts))
               (fn-nntp-article-tombstonep article fn-arena))))
  :hints (("Goal" :use
    ((:instance fn-hf-nov-of-held-facts-of
      (bytes (fn-nntp-article-bytes article fn-arena)))
     fn-obfs-old-nov-ok-is-hnov-ok
     (:instance fn-obfs-facts-tomb-is-source-tomb
      (bytes (fn-nntp-article-bytes article fn-arena))))
   :in-theory (e/d (fn-nntp-article-tombstonep)
     (fn-held-facts-of fn-hf-nov fn-hnov-ok fn-hnov-tomb fn-hnov-of
      fn-nov-okp fn-nov-overview fn-nntp-article-bytes fn-rcl-tombstonep
      fn-hf-nov-of-held-facts-of fn-obfs-old-nov-ok-is-hnov-ok
      fn-obfs-facts-tomb-is-source-tomb))))))

(defun-nx fn-obc-seek-cached-source-p (s fn-arena fn-cat)
 (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
 (let* ((range (nth 0 s)) (group (nth 0 range)) (k (nfix (nth 1 range)))
        (v (nth 3 range)) (seq (fn-cnx-view-seq group k v fn-cat))
        (row (fn-cat-at seq fn-cat)) (facts (fn-nrf-facts seq fn-cat)))
  (if (and facts (posp k) (<= k *fn-nntp-max-article-number*)
           (fn-scat-msgid-idp (fn-record-msgid row)))
      (equal facts
       (fn-held-facts-of (fn-nntp-article-bytes
        (fn-scat-available-article group k v fn-arena fn-cat) fn-arena)))
    t)))

(local
 (defthm fn-obfs-one-within-range-preserves-actual-full-old-residual
 (implies (and (equal (nth 2 s) :seek)
               (nth 0 s)
               (<= (nfix (nth 1 (nth 0 s))) (nfix (nth 2 (nth 0 s))))
               (fn-obc-seek-cached-source-p s fn-arena fn-cat))
  (let ((r (fn-obc-one s fn-arena fn-cat)))
   (equal (append (mv-nth 0 r)
                  (fn-obc-actual-old-residual (mv-nth 1 r) fn-arena fn-cat))
          (fn-obc-actual-old-residual s fn-arena fn-cat))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :expand ((fn-obc-one s fn-arena fn-cat)) :use
  ((:instance fn-ovw-lines-current-number-all-branches-unfolds
    (group (nth 0 (nth 0 s))) (k (nfix (nth 1 (nth 0 s))))
    (hi (nfix (nth 2 (nth 0 s)))) (v (nth 3 (nth 0 s))))
   (:instance fn-obfs-facts-imply-selected-handle
    (seq (fn-cnx-view-seq (nth 0 (nth 0 s)) (nfix (nth 1 (nth 0 s)))
                           (nth 3 (nth 0 s)) fn-cat)))
   (:instance fn-obfs-selected-article-present
    (group (nth 0 (nth 0 s))) (k (nfix (nth 1 (nth 0 s)))) (v (nth 3 (nth 0 s))))
   (:instance fn-obfs-selected-source-length
    (group (nth 0 (nth 0 s))) (number (nfix (nth 1 (nth 0 s)))) (v (nth 3 (nth 0 s))))
   (:instance fn-obfs-cache-flags-are-old-flags
    (article (fn-scat-available-article (nth 0 (nth 0 s)) (nfix (nth 1 (nth 0 s)))
                                       (nth 3 (nth 0 s)) fn-arena fn-cat))
    (facts (fn-nrf-facts (fn-cnx-view-seq (nth 0 (nth 0 s)) (nfix (nth 1 (nth 0 s)))
                                        (nth 3 (nth 0 s)) fn-cat) fn-cat)))
   (:instance fn-obc-cached-pieces-are-actual-old-source-row
    (article (fn-scat-available-article (nth 0 (nth 0 s)) (nfix (nth 1 (nth 0 s)))
                                       (nth 3 (nth 0 s)) fn-arena fn-cat))
    (facts (fn-nrf-facts (fn-cnx-view-seq (nth 0 (nth 0 s)) (nfix (nth 1 (nth 0 s)))
                                        (nth 3 (nth 0 s)) fn-cat) fn-cat))
    (number (nfix (nth 1 (nth 0 s)))))
   (:instance fn-ovw-reply-current-row-frame-unfolds
    (number (nfix (nth 1 (nth 0 s))))
    (over (fn-nov-overview
     (fn-scat-available-article (nth 0 (nth 0 s)) (nfix (nth 1 (nth 0 s)))
                               (nth 3 (nth 0 s)) fn-arena fn-cat) fn-arena))
    (rest (fn-ovw-lines (nth 0 (nth 0 s)) (+ 1 (nfix (nth 1 (nth 0 s))))
                       (nfix (nth 2 (nth 0 s))) (nth 3 (nth 0 s)) fn-arena fn-cat))
    (legacyp (nth 4 (nth 0 s))) (owedp (nth 5 (nth 0 s)))))
  :in-theory (e/d (fn-obc-actual-old-residual fn-obc-make fn-obc-begin
                   fn-obc-old-range-reply fn-obc-next-range fn-ovw-cursor
                   fn-obc-seek-cached-source-p fn-nntp-article-tombstonep)
   (nth nfix natp posp fn-record-string-octets
    fn-obc-one fn-lpc-tick fn-lpc-begin fn-npw-one fn-npw-remaining fn-npw-column-pieces
    fn-obc-row-ready fn-cnx-view-seq fn-cat-at fn-cat-count fn-record-payload
    fn-record-msgid fn-held-number-in fn-scat-msgid-idp fn-scat-available-article
    fn-cat-row-article fn-nov-overview fn-nov-okp fn-nov-line fn-ovw-lines fn-ovw-reply
    fn-hf-nov fn-nrf-facts fn-hnov-ok fn-hnov-tomb fn-hnov-of fn-held-facts-of
    fn-rcl-tombstonep fn-nntp-article-bytes fn-arena-payload-len)))))
)

(defthm fn-obc-one-seek-preserves-actual-full-old-residual
 (implies (and (equal (nth 2 s) :seek)
               (nth 0 s)
               (fn-obc-seek-cached-source-p s fn-arena fn-cat))
  (let ((r (fn-obc-one s fn-arena fn-cat)))
   (equal (append (mv-nth 0 r)
                  (fn-obc-actual-old-residual (mv-nth 1 r) fn-arena fn-cat))
          (fn-obc-actual-old-residual s fn-arena fn-cat))))
 :rule-classes nil
 :hints (("Goal" :use
  (fn-obfs-one-within-range-preserves-actual-full-old-residual
   fn-obc-one-exhaustion-preserves-actual-full-old-residual)
  :in-theory (disable fn-obc-one fn-obc-actual-old-residual
                       fn-obc-seek-cached-source-p))))
