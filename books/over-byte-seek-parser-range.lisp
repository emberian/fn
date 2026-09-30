; Actual legacy seek establishes the parser carry without consuming a row.
; The genuine registered number-root controller remains a separate boundary.
(in-package "ACL2")
(include-book "over-byte-parser-relation")
(include-book "over-byte-range-relation")

(defthm fn-obc-one-seek-establishes-parser-and-full-old-residual
 (let* ((range (nth 0 s)) (k (nfix (nth 1 range)))
        (seq (fn-cnx-view-seq (nth 0 range) k (nth 3 range) fn-cat))
        (row (and seq (fn-cat-at seq fn-cat))))
  (implies (and (equal (nth 2 s) :seek)
                (<= k (nfix (nth 2 range)))
                (posp k)
                (<= k *fn-nntp-max-article-number*)
                (fn-scat-msgid-idp (fn-record-msgid row))
                (not (fn-nrf-facts seq fn-cat)))
   (let ((r (fn-obc-one s fn-arena fn-cat)))
    (and (equal (nth 2 (mv-nth 1 r)) :parse)
         (fn-obc-parser-prefix-p (mv-nth 1 r) fn-arena fn-cat)
         (equal (append (mv-nth 0 r)
                        (fn-obc-actual-old-residual (mv-nth 1 r) fn-arena fn-cat))
                (fn-obc-actual-old-residual s fn-arena fn-cat))))))
 :rule-classes nil
 :hints (("Goal"
  :use fn-obc-one-preserves-parser-prefix
  :in-theory (e/d (fn-obc-one fn-obc-actual-old-residual fn-obc-make
                   fn-obc-parser-prefix-p fn-obc-selected-handle)
                  (fn-obc-old-range-reply fn-cnx-view-seq fn-cat-at
                   fn-nrf-facts fn-lpc-begin fn-lpc-tick fn-npw-one
                   fn-lpc-feed fn-lpr-prefix-p fn-arena-payload-len)))))
