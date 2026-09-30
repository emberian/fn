; Reachable actual source prefix carried by the complete OVER machine.
; Semantic proof vocabulary only; never a served validator. PRF-1066.
(in-package "ACL2")
(include-book "over-byte-cursor")
(include-book "legacy-parser-continuation")
(include-book "over-byte-row-relation")

(defun fn-obc-selected-handle (s fn-cat)
  (declare (xargs :stobjs fn-cat :verify-guards nil))
  (let* ((range (nth 0 s))
         (seq (fn-cnx-view-seq (nth 0 range) (nfix (nth 1 range))
                               (nth 3 range) fn-cat)))
    (nfix (fn-record-payload (fn-cat-at seq fn-cat)))))

(defun fn-obc-parser-prefix-p (s fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (if (equal (nth 2 s) :parse)
      (let ((h (fn-obc-selected-handle s fn-cat)))
        (fn-lpr-prefix-p (nth 3 s) h (nth 1 s) (fn-arena-payload h fn-arena)))
    t))

(defthm fn-obc-begin-establishes-parser-prefix
  (fn-obc-parser-prefix-p (fn-obc-begin range pin) fn-arena fn-cat)
  :hints (("Goal" :in-theory (enable fn-obc-parser-prefix-p fn-obc-begin fn-obc-make))))

(local
 (defthm fn-obc-parser-start-prefix
   (implies (equal n (len bytes))
            (fn-lpr-prefix-p (fn-lpc-begin h n pin) h pin bytes))
   :hints (("Goal" :use fn-lpr-begin-establishes-prefix
            :in-theory (disable fn-lpc-begin fn-lpr-prefix-p)))))

(defthm fn-obc-one-preserves-parser-prefix
  (implies (fn-obc-parser-prefix-p s fn-arena fn-cat)
           (fn-obc-parser-prefix-p (mv-nth 1 (fn-obc-one s fn-arena fn-cat))
                                   fn-arena fn-cat))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lpr-one-tick-preserves-prefix
                            (s (nth 3 s)) (h (fn-obc-selected-handle s fn-cat))
                            (pin (nth 1 s)) (bytes (nth (fn-obc-selected-handle s fn-cat) fn-arena)))
                 (:instance fn-lpr-begin-establishes-prefix
                            (h (fn-obc-selected-handle s fn-cat)) (pin (nth 1 s))
                            (bytes (nth (fn-obc-selected-handle s fn-cat) fn-arena))))
           :in-theory
           (e/d (fn-obc-parser-prefix-p fn-obc-one fn-obc-selected-handle
                 fn-obc-make fn-obc-row-ready fn-obc-begin fn-obc-next-range)
                (fn-lpc-tick fn-npw-one fn-lpr-prefix-p fn-lpc-begin
                 fn-lpc-tombstonep fn-obc-parser-pieces fn-npw-column-pieces
                 fn-cnx-view-seq fn-nrf-facts fn-cat-at fn-record-payload
                 fn-hf-nov fn-hnov-ok fn-hnov-tomb fn-ovw-cursor
                 nth nfix fn-ovw-status fn-ovw-empty-text fn-arena-count-is-len)))))

 ; The terminal result is the parser returned INSIDE the actual ONE's parse
; branch. ONE immediately changes phase when that verdict is nonyield, so
; a retained :parse state at EOF is not used as a positive machine witness.
(defthm fn-obc-final-parser-tick-is-selected-source-feed
  (let ((parser (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena))))
    (implies (and (equal (nth 2 s) :parse)
                  (fn-obc-parser-prefix-p s fn-arena fn-cat)
                  (not (equal (fn-lpc-verdict parser) :yield)))
             (equal parser
                    (fn-lpc-feed (nth (fn-obc-selected-handle s fn-cat) fn-arena)
                      (fn-lpc-begin (fn-obc-selected-handle s fn-cat)
                        (len (nth (fn-obc-selected-handle s fn-cat) fn-arena))
                        (nth 1 s))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-lpr-one-tick-preserves-prefix
                            (s (nth 3 s)) (h (fn-obc-selected-handle s fn-cat))
                            (pin (nth 1 s)) (bytes (nth (fn-obc-selected-handle s fn-cat) fn-arena)))
                 (:instance fn-lpr-terminal-prefix-is-complete-feed
                            (s (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena)))
                            (h (fn-obc-selected-handle s fn-cat))
                            (pin (nth 1 s)) (bytes (nth (fn-obc-selected-handle s fn-cat) fn-arena))))
           :in-theory (e/d (fn-obc-parser-prefix-p)
                           (fn-lpr-prefix-p fn-lpc-verdict fn-obc-selected-handle
                            fn-lpc-begin fn-lpc-feed fn-lpc-tick)))))

(defthm fn-obc-final-parser-tick-has-actual-selected-nov
  (let ((parser (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena))))
    (implies (and (equal (nth 2 s) :parse)
                  (fn-obc-parser-prefix-p s fn-arena fn-cat)
                  (not (equal (fn-lpc-verdict parser) :yield))
                  (fn-cbor-octet-listp (nth (fn-obc-selected-handle s fn-cat) fn-arena)))
             (equal (fn-lpc-nov-value parser fn-arena)
                    (fn-hnov-of (nth (fn-obc-selected-handle s fn-cat) fn-arena)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-obc-final-parser-tick-is-selected-source-feed
                 (:instance fn-lpv-complete-feed-is-actual-catalog
                            (h (fn-obc-selected-handle s fn-cat)) (pin (nth 1 s))
                            (arena fn-arena)))
           :in-theory (disable fn-obc-parser-prefix-p fn-obc-selected-handle
                               fn-lpc-nov-value fn-hnov-of fn-lpc-verdict
                               fn-lpc-begin fn-lpc-feed fn-lpc-tick))))

(defthm fn-obc-final-parser-tick-has-actual-selected-body-lines
  (let ((parser (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena))))
    (implies (and (equal (nth 2 s) :parse)
                  (fn-obc-parser-prefix-p s fn-arena fn-cat)
                  (not (equal (fn-lpc-verdict parser) :yield)))
             (equal (fn-lpc-body-lines parser)
                    (fn-hf-body-lines-of (nth (fn-obc-selected-handle s fn-cat) fn-arena)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-obc-final-parser-tick-is-selected-source-feed
                 (:instance fn-lpc-feed-body-lines-is-body-lines-of-all-tails
                            (h (fn-obc-selected-handle s fn-cat))
                            (n (len (nth (fn-obc-selected-handle s fn-cat) fn-arena)))
                            (pin (nth 1 s))
                            (bytes (nth (fn-obc-selected-handle s fn-cat) fn-arena))))
           :in-theory (disable fn-obc-parser-prefix-p fn-obc-selected-handle
                               fn-lpc-body-lines fn-hf-body-lines-of fn-lpc-verdict
                               fn-lpc-begin fn-lpc-feed fn-lpc-tick))))

; Derive the row's representation premises from the actual consumed-source
; relation. This is logical vocabulary, never an additional served scan.
(local
 (defthm fn-obcr-prefix-has-bounds
  (implies (fn-lpr-prefix-p parser h pin bytes)
           (fn-lpc-cursor-bounds-p parser))
  :hints (("Goal" :use
           ((:instance fn-lpv-feed-preserves-bounds
                       (s (fn-lpc-begin h (len bytes) pin))
                       (bytes (take (fn-lpc-at 3 parser) bytes))))
           :in-theory (e/d (fn-lpr-prefix-p)
                          (fn-lpc-feed fn-lpc-begin fn-lpc-at
                           fn-lpc-cursor-bounds-p))))))

(local
 (defthm fn-obcr-bounded-field-has-natural-start
  (implies (and (natp k) (fn-lpc-cursor-bounds-p parser))
           (or (not (fn-lpc-field parser k))
               (natp (fn-lpc-at 1 (fn-lpc-field parser k)))))
  :hints (("Goal" :use ((:instance fn-lpc-field-retains-pinned-source
                                  (s parser)))
           :in-theory (e/d (fn-lpc-span-bound-p)
                          (fn-lpc-field fn-lpc-at fn-lpc-cursor-bounds-p
                           fn-lpc-field-retains-pinned-source))))))

(local
 (defthm fn-obcr-prefix-has-source-length
  (implies (fn-lpr-prefix-p parser h pin bytes)
           (equal (fn-lpc-at 1 parser) (len bytes)))
  :hints (("Goal" :use
           ((:instance fn-lpv-feed-keeps-source-and-position
                       (s (fn-lpc-begin h (len bytes) pin))
                       (bytes (take (fn-lpc-at 3 parser) bytes))))
           :in-theory (e/d (fn-lpr-prefix-p fn-lpc-begin fn-lpc-at)
                          (fn-lpc-feed
                           fn-lpv-feed-keeps-source-and-position))))))

(local (defthm fn-obcr-bounded-parser-row
 (implies (fn-lpc-cursor-bounds-p parser)
  (equal (fn-npw-remaining (fn-obc-parser-pieces number parser) 0 fn-arena)
   (append
    (fn-nov-line number
      (list :ok (fn-record-string-octets (fn-hnov-subject (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-from (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-date (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-msgid (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-references (fn-lpc-nov-value parser fn-arena)))
                (nfix (fn-lpc-at 1 parser)) (fn-lpc-body-lines parser)))
    '(13 10))))
 :hints (("Goal" :use
   ((:instance fn-obc-parser-pieces-denote-parser-nov-row)
    (:instance fn-obcr-bounded-field-has-natural-start (k 0))
    (:instance fn-obcr-bounded-field-has-natural-start (k 1))
    (:instance fn-obcr-bounded-field-has-natural-start (k 2))
    (:instance fn-obcr-bounded-field-has-natural-start (k 3))
    (:instance fn-obcr-bounded-field-has-natural-start (k 4))
   ) :in-theory (disable fn-obc-parser-pieces fn-npw-remaining fn-nov-line
                         fn-lpc-nov-value fn-lpc-field fn-lpc-at
                         fn-lpc-cursor-bounds-p fn-lpc-header-bounds-p
                         fn-obc-parser-pieces-denote-parser-nov-row
                         fn-obcr-bounded-field-has-natural-start)))))

; Actual terminal tick, actual selected bytes, original NOV renderer.
; Catalogue row visibility/number binding and the full range residual follow
; at a distinct boundary; no successful cache lookup substitutes for them.
(defthm fn-obc-final-parser-row-is-actual-selected-source-row
 (let* ((parser (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena)))
        (bytes (nth (fn-obc-selected-handle s fn-cat) fn-arena))
        (nov (fn-hnov-of bytes)))
  (implies (and (equal (nth 2 s) :parse)
                (fn-obc-parser-prefix-p s fn-arena fn-cat)
                (not (equal (fn-lpc-verdict parser) :yield))
                (fn-cbor-octet-listp bytes))
   (equal (fn-npw-remaining (fn-obc-parser-pieces number parser) 0 fn-arena)
    (append
     (fn-nov-line number
       (list :ok (fn-record-string-octets (fn-hnov-subject nov))
                 (fn-record-string-octets (fn-hnov-from nov))
                 (fn-record-string-octets (fn-hnov-date nov))
                 (fn-record-string-octets (fn-hnov-msgid nov))
                 (fn-record-string-octets (fn-hnov-references nov))
                 (len bytes) (fn-hf-body-lines-of bytes)))
     '(13 10)))))
 :rule-classes nil
 :hints (("Goal" :use
   ((:instance fn-lpr-one-tick-preserves-prefix
     (s (nth 3 s)) (h (fn-obc-selected-handle s fn-cat))
     (pin (nth 1 s)) (bytes (nth (fn-obc-selected-handle s fn-cat) fn-arena)))
    (:instance fn-obcr-bounded-parser-row
     (parser (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena))))
    (:instance fn-obcr-prefix-has-bounds
     (parser (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena)))
     (h (fn-obc-selected-handle s fn-cat)) (pin (nth 1 s))
     (bytes (nth (fn-obc-selected-handle s fn-cat) fn-arena)))
    (:instance fn-obcr-prefix-has-source-length
     (parser (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena)))
     (h (fn-obc-selected-handle s fn-cat)) (pin (nth 1 s))
     (bytes (nth (fn-obc-selected-handle s fn-cat) fn-arena)))
    fn-obc-final-parser-tick-has-actual-selected-nov
    fn-obc-final-parser-tick-has-actual-selected-body-lines)
   :in-theory (e/d (fn-obc-parser-prefix-p)
    (fn-lpr-prefix-p fn-lpc-tick fn-lpc-at fn-lpc-field fn-lpc-verdict
     fn-lpc-nov-value fn-obc-selected-handle fn-obc-parser-pieces
     fn-npw-remaining fn-nov-line fn-hnov-of fn-hf-body-lines-of
     fn-record-string-octets fn-lpc-body-lines fn-lpc-cursor-bounds-p
     fn-lpc-header-bounds-p fn-lpr-one-tick-preserves-prefix
     fn-obc-parser-pieces-denote-parser-nov-row
     fn-obcr-prefix-has-bounds fn-obcr-prefix-has-source-length
     fn-obcr-bounded-field-has-natural-start fn-obcr-bounded-parser-row)))))
