; Reachable actual source prefix carried by the complete OVER machine.
; Semantic proof vocabulary only; never a served validator. PRF-1066.
(in-package "ACL2")
(include-book "over-byte-cursor")
(include-book "legacy-parser-continuation")

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
