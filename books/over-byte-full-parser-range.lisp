; Actual parser ONE against the COMPLETE old selected range reply.
; No executable locator or whole-state validator is added.
(in-package "ACL2")
(include-book "over-byte-terminal-selected")
(include-book "served-range-step-source")
(include-book "over-reply-row-frame")
(include-book "over-byte-range-relation")

(local
 (defthm fn-obfp-selected-sequence-in-bounds
  (implies (fn-cnx-view-seq group k v fn-cat)
   (and (natp (fn-cnx-view-seq group k v fn-cat))
        (< (fn-cnx-view-seq group k v fn-cat) (fn-cat-count fn-cat))))
  :hints (("Goal" :in-theory
   (e/d (fn-cnx-view-seq)
        (fn-cat-group-number fn-cat-visible-at fn-cat-count-is-len))))))

(local
 (defthm fn-obfp-row-id-is-record-id
  (equal (fn-nntp-article-idp (fn-cat-row-article seq fn-arena fn-cat))
         (fn-scat-msgid-idp (fn-record-msgid (fn-cat-at seq fn-cat))))
  :hints (("Goal" :in-theory
   (e/d (fn-nntp-article-idp fn-scat-msgid-idp)
        (fn-cat-row-article fn-cat-at fn-record-msgid fn-nntp-string-octets
         fn-nntp-message-id-tokenp length))))))

(local
 (defthm fn-obfp-row-article-present
  (consp (fn-cat-row-article seq fn-arena fn-cat))
  :hints (("Goal" :in-theory (enable fn-cat-row-article fn-make-article)))))

(local
 (defthm fn-obfp-selected-article-present
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
 (defthm fn-obfp-append-associative
  (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-obfp-row-ready-residual-unfolds
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
 (defthm fn-obfp-tick-returned-verdict
  (equal (mv-nth 3 (fn-lpc-tick parser 1 fn-arena))
         (fn-lpc-verdict (mv-nth 0 (fn-lpc-tick parser 1 fn-arena))))
  :hints (("Goal" :expand ((fn-lpc-tick parser 1 fn-arena)
                           (:free (p) (fn-lpc-tick p 0 fn-arena)))
   :in-theory (disable fn-lpc-tick fn-lpc-byte fn-lpc-at fn-lpc-verdict fn-arena-get)))))

(local
 (defthm fn-obfp-number-seq-shift-gen
   (implies (and (natp i) (natp j))
            (equal (fn-cat-number-seq g n c (+ i j))
                   (let ((r (fn-cat-number-seq g n c j)))
                     (and r (+ i r)))))
   :hints (("Goal" :induct (fn-cat-number-seq g n c j)))))

(local
 (defthm fn-obfp-number-seq-shift
   (implies (and (natp i) (syntaxp (not (equal i ''0))))
            (equal (fn-cat-number-seq g n c i)
                   (let ((r (fn-cat-number-seq g n c 0)))
                     (and r (+ i r)))))
   :hints (("Goal" :use ((:instance fn-obfp-number-seq-shift-gen (j 0)))
            :in-theory (disable fn-obfp-number-seq-shift-gen)))))

(local
 (defthm fn-obfp-number-seq-natp
   (implies (fn-cat-number-seq g n c 0)
            (and (natp (fn-cat-number-seq g n c 0))
                 (< (fn-cat-number-seq g n c 0) (len c))))
   :rule-classes nil))

(local
 (defthm fn-obfp-number-seq-type
   (implies (natp i)
            (or (null (fn-cat-number-seq g n c i))
                (natp (fn-cat-number-seq g n c i))))
   :rule-classes :type-prescription))

(local
 (defthm fn-obfp-nth-of-1+
   (implies (natp r)
            (equal (nth (+ 1 r) c) (nth r (cdr c))))))

(local
 (defthm fn-obfp-number-seq-binds
   (implies (fn-cat-number-seq g n c 0)
            (equal (fn-held-number-in g (nth (fn-cat-number-seq g n c 0) c)) n))
   :rule-classes nil
   :hints (("Goal" :induct (len c) :expand ((fn-cat-number-seq g n c 0))))))

(local
 (defthm fn-obfp-selected-number-binds
  (implies (fn-cnx-view-seq group k v fn-cat)
   (equal (fn-held-number-in group
             (fn-cat-at (fn-cnx-view-seq group k v fn-cat) fn-cat)) k))
  :hints (("Goal" :use ((:instance fn-obfp-number-seq-binds
                          (g group) (n k) (c fn-cat)))
   :in-theory (e/d (fn-cnx-view-seq)
    (fn-cat-group-number fn-cat-visible-at fn-held-number-in fn-cat-number-seq))))))

(defthm fn-obc-one-parse-preserves-actual-full-old-residual
 (let* ((range (nth 0 s)) (group (nth 0 range)) (k (nth 1 range))
        (v (nth 3 range)) (seq (fn-cnx-view-seq group k v fn-cat))
        (row (fn-cat-at seq fn-cat)) (h (fn-record-payload row)))
  (implies (and (equal (nth 2 s) :parse)
                (fn-obc-parser-prefix-p s fn-arena fn-cat)
                (fn-cbor-octet-listp (nth (fn-obc-selected-handle s fn-cat) fn-arena))
                (posp k) (<= k *fn-nntp-max-article-number*)
                (<= k (nfix (nth 2 range))) seq
                (fn-scat-msgid-idp (fn-record-msgid row)) (natp h))
   (let ((r (fn-obc-one s fn-arena fn-cat)))
    (equal (append (mv-nth 0 r)
                   (fn-obc-actual-old-residual (mv-nth 1 r) fn-arena fn-cat))
           (fn-obc-actual-old-residual s fn-arena fn-cat)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :use
  ((:instance fn-obfp-selected-number-binds
    (group (nth 0 (nth 0 s))) (k (nth 1 (nth 0 s))) (v (nth 3 (nth 0 s))))
   (:instance fn-obfp-selected-sequence-in-bounds
    (group (nth 0 (nth 0 s))) (k (nth 1 (nth 0 s))) (v (nth 3 (nth 0 s))))
   fn-obc-terminal-parser-selected-tombstone-unfolds
   fn-obc-terminal-parser-selected-validity-unfolds
   fn-obc-valid-final-parser-row-is-actual-old-selected-row
   (:instance fn-ovw-lines-current-number-unfolds
    (group (nth 0 (nth 0 s))) (k (nth 1 (nth 0 s)))
    (hi (nfix (nth 2 (nth 0 s)))) (v (nth 3 (nth 0 s))))
   (:instance fn-ovw-reply-current-row-frame-unfolds
    (number (nth 1 (nth 0 s)))
    (over (fn-nov-overview
      (fn-scat-available-article (nth 0 (nth 0 s)) (nth 1 (nth 0 s))
                                (nth 3 (nth 0 s)) fn-arena fn-cat) fn-arena))
    (rest (fn-ovw-lines (nth 0 (nth 0 s)) (+ 1 (nth 1 (nth 0 s)))
                        (nfix (nth 2 (nth 0 s))) (nth 3 (nth 0 s)) fn-arena fn-cat))
    (legacyp (nth 4 (nth 0 s))) (owedp (nth 5 (nth 0 s)))))
  :in-theory (e/d (fn-obc-one fn-obc-actual-old-residual fn-obc-make
                   fn-obc-begin fn-obc-old-range-reply fn-obc-next-range fn-ovw-cursor)
   (fn-lpc-tick fn-lpc-verdict fn-lpc-tombstonep fn-obc-parser-prefix-p
    fn-obc-parser-pieces fn-npw-remaining fn-obc-row-ready fn-obc-selected-handle
    fn-cnx-view-seq fn-cat-at fn-cat-count fn-record-payload fn-record-msgid
    fn-held-number-in fn-scat-msgid-idp fn-scat-available-article fn-cat-row-article
    fn-nov-overview fn-nov-okp fn-nov-line fn-ovw-lines fn-ovw-reply
    fn-cbor-octet-listp fn-npw-one fn-nntp-article-tombstonep
    fn-rcl-tombstonep fn-nntp-article-bytes fn-lpc-nov-value fn-hnov-of)))))
