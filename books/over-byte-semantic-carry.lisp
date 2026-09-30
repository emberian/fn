; Semantic selection carry for the ACTUAL old-source machine. PRF-1066.
; Global source relations here are theorem premises, never hot validators.
(in-package "ACL2")
(include-book "over-byte-full-parser-range")
(include-book "over-byte-full-seek-range")
(include-book "over-byte-invariants")

(defun-nx fn-obc-parse-selection-p (s fn-arena fn-cat)
 (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
 (if (equal (nth 2 s) :parse)
  (let* ((range (nth 0 s)) (k (nth 1 range))
         (seq (fn-cnx-view-seq (nth 0 range) k (nth 3 range) fn-cat))
         (row (fn-cat-at seq fn-cat)))
   (and (posp k) (<= k *fn-nntp-max-article-number*)
        (<= k (nfix (nth 2 range))) seq
        (fn-scat-msgid-idp (fn-record-msgid row))
        (natp (fn-record-payload row))
        (fn-cbor-octet-listp
          (nth (fn-obc-selected-handle s fn-cat) fn-arena))))
  t))

(local
 (defthm fn-obcarry-arena-nth-octets
  (implies (and (fn-arena-p fn-arena) (natp h))
           (fn-cbor-octet-listp (nth h fn-arena)))
  :hints (("Goal" :induct (nth h fn-arena)
   :in-theory (enable fn-arena-p-is-payload-listp fn-arn-payload-listp nth)))))

(local
 (defthm fn-obcarry-positive-nfix-is-original
  (implies (posp (nfix k)) (equal (nfix k) k))))

(local
 (defthm fn-obcarry-at-is-nth
  (equal (fn-lpc-at i x) (nth (nfix i) x))
  :hints (("Goal" :in-theory (enable fn-lpc-at fn-ag-car fn-ag-cdr nth)))))

(local
 (defthm fn-obcarry-nfix-natural
  (implies (natp v) (equal (nfix v) v))))

(local
 (defthm fn-obcarry-active-top-natural
  (implies (and (posp k) (<= k (nfix top))) (natp top))
  :rule-classes :forward-chaining))

(local
 (defthm fn-obcarry-active-top-order
  (implies (and (posp k) (<= k (nfix top))) (<= k top))))

(defthm fn-obc-one-preserves-parse-selection-with-seek-view
 (implies (and (fn-obc-parse-selection-p s fn-arena fn-cat)
               (fn-obc-source-ready-p s fn-arena fn-cat)
               (fn-arena-p fn-arena)
               (or (not (equal (nth 2 s) :seek))
                   (natp (nth 3 (nth 0 s)))))
  (fn-obc-parse-selection-p (mv-nth 1 (fn-obc-one s fn-arena fn-cat))
                            fn-arena fn-cat))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory
   (e/d (fn-obc-parse-selection-p fn-obc-one fn-obc-source-ready-p
         fn-obc-selected-handle fn-obc-make fn-obc-begin fn-obc-row-ready)
        (fn-lpc-tick fn-lpc-begin fn-obc-next-range fn-npw-one
         fn-obc-parser-pieces fn-npw-column-pieces fn-cnx-view-seq fn-cat-at
         fn-record-payload fn-record-msgid fn-nrf-facts fn-scat-msgid-idp
         fn-hf-nov fn-hnov-ok fn-hnov-tomb fn-arena-payload-len
         fn-npw-remaining fn-arena-p fn-cbor-octet-listp nth nfix natp posp)))))

(local
 (defthm fn-obcarry-no-facts-for-no-selection
  (equal (fn-nrf-facts nil fn-cat) nil)
  :hints (("Goal" :in-theory (enable fn-nrf-facts)))))

(local
 (defthm fn-obcarry-row-id-is-record-id
  (equal (fn-nntp-article-idp (fn-cat-row-article seq fn-arena fn-cat))
         (fn-scat-msgid-idp (fn-record-msgid (fn-cat-at seq fn-cat))))
  :hints (("Goal" :in-theory
   (e/d (fn-nntp-article-idp fn-scat-msgid-idp)
        (fn-cat-row-article fn-cat-at fn-record-msgid fn-nntp-string-octets
         fn-nntp-message-id-tokenp length))))))

(defthm fn-obc-seek-source-from-carried-columns
 (implies (fn-scol-okp fn-arena fn-cat)
          (fn-obc-seek-cached-source-p s fn-arena fn-cat))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-nrf-facts-are-row-bytes-facts
         (seq (fn-cnx-view-seq (nth 0 (nth 0 s))
               (nfix (nth 1 (nth 0 s))) (nth 3 (nth 0 s)) fn-cat))))
  :in-theory
   (e/d (fn-obc-seek-cached-source-p fn-scat-available-article
         fn-scat-number-article fn-nntp-article-bytes)
        (fn-cnx-view-seq fn-nrf-facts fn-nrf-facts-are-row-bytes-facts
         fn-cat-row-article fn-cat-at fn-record-payload fn-record-msgid
         fn-record-groups fn-held-numbers fn-record-stamp fn-scat-msgid-idp
         fn-nntp-article-idp fn-nntp-payload-bytes fn-held-facts-of
         fn-scol-okp nth nfix natp posp)))))

(defun-nx fn-obc-semantic-ready-p (s fn-arena fn-cat)
 (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
 (or (not s)
     (and (fn-obc-statep s fn-arena)
          (fn-obc-parser-prefix-p s fn-arena fn-cat)
          (fn-obc-parse-selection-p s fn-arena fn-cat))))

(defthm fn-obc-begin-carried-semantic-ready-from-cursor-and-pin
 (implies (and (fn-ovw-cursorp range) (fn-rpin-tokenp pin))
          (fn-obc-semantic-ready-p (fn-obc-begin range pin) fn-arena fn-cat))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-obc-semantic-ready-p fn-obc-statep fn-obc-begin fn-obc-make
        fn-obc-parser-prefix-p fn-obc-parse-selection-p)
       (fn-rpin-tokenp fn-lpr-prefix-p fn-lpc-ready-p
        fn-lpc-cursor-bounds-p fn-npw-piecesp fn-obc-selected-handle)))))

(local
 (defthm fn-obcarry-seek-view-from-state-shape
  (implies (and (fn-obc-statep s fn-arena) (equal (nth 2 s) :seek))
           (natp (nth 3 (nth 0 s))))
  :hints (("Goal" :in-theory
   (e/d (fn-obc-statep fn-ovw-cursorp)
        (fn-lpc-ready-p fn-lpc-cursor-bounds-p fn-npw-piecesp fn-rpin-tokenp))))))

(local
 (defthm fn-obcarry-nil-one-unfolds
  (equal (fn-obc-one nil fn-arena fn-cat) '(nil nil))
  :hints (("Goal" :in-theory (enable fn-obc-one)))))

(local
 (defthm fn-obcarry-columns-carry-arena
  (implies (fn-scol-okp fn-arena fn-cat) (fn-arena-p fn-arena))
  :hints (("Goal" :in-theory (enable fn-scol-okp)))))

(defthm fn-obc-one-preserves-carried-semantic-ready-from-columns
 (implies (and (fn-obc-semantic-ready-p s fn-arena fn-cat)
               (fn-cat-p fn-cat)
               (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
               (fn-scol-okp fn-arena fn-cat))
  (fn-obc-semantic-ready-p (mv-nth 1 (fn-obc-one s fn-arena fn-cat))
                           fn-arena fn-cat))
 :rule-classes nil
 :hints (("Goal" :cases ((not s)) :do-not-induct t
  :use (fn-obc-one-keeps-shape-under-carried-catalog-by-definition
        fn-obc-source-ready-from-carried-handles
        fn-obc-one-preserves-parser-prefix
        fn-obc-one-preserves-parse-selection-with-seek-view
        fn-obcarry-seek-view-from-state-shape)
  :in-theory
   (e/d (fn-obc-semantic-ready-p)
        (fn-obc-one fn-obc-statep fn-obc-parser-prefix-p fn-obc-parse-selection-p
         fn-obc-source-ready-p fn-cnx-view-seq fn-obcarry-seek-view-from-state-shape
         fn-cat-p fn-cat-count fn-cat-handles-inp fn-arena-p fn-scol-okp)))))

(local
 (defthm fn-obcarry-nil-residual-unfolds
  (equal (fn-obc-actual-old-residual nil fn-arena fn-cat) nil)
  :hints (("Goal" :in-theory
           (enable fn-obc-actual-old-residual fn-obc-old-range-reply)))))

(defthm fn-obc-one-carried-full-output-and-old-residual
 (implies (and (fn-obc-semantic-ready-p s fn-arena fn-cat)
               (fn-scol-okp fn-arena fn-cat))
  (let ((result (fn-obc-one s fn-arena fn-cat)))
   (equal (append (mv-nth 0 result)
                  (fn-obc-actual-old-residual (mv-nth 1 result) fn-arena fn-cat))
          (fn-obc-actual-old-residual s fn-arena fn-cat))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :cases
  ((not s) (equal (nth 2 s) :seek) (equal (nth 2 s) :parse) (equal (nth 2 s) :emit))
  :use (fn-obc-one-seek-preserves-actual-full-old-residual
        fn-obc-one-parse-preserves-actual-full-old-residual
        fn-obc-one-emit-preserves-actual-full-old-residual
        fn-obc-seek-source-from-carried-columns)
  :in-theory
   (e/d (fn-obc-semantic-ready-p fn-obc-parse-selection-p fn-obc-statep)
        (fn-obc-actual-old-residual fn-obc-old-range-reply
         fn-obc-seek-cached-source-p fn-nrf-facts fn-scat-available-article
         fn-nrf-facts-are-row-bytes-facts fn-obc-one fn-obc-parser-prefix-p fn-obc-selected-handle
         fn-lpc-ready-p fn-lpc-cursor-bounds-p fn-npw-piecesp fn-rpin-tokenp
         fn-cnx-view-seq fn-cat-at fn-record-payload fn-record-msgid
         fn-scat-msgid-idp fn-cbor-octet-listp fn-npw-remaining
         fn-ovw-lines fn-ovw-reply fn-scol-okp nth nfix natp posp)))))
