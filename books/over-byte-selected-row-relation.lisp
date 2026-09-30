; Actual numbered old getter and the actual final byte parser row.
; No second executable locator or provider authority is introduced.
(in-package "ACL2")
(include-book "over-byte-old-row-relation")
(include-book "served-selected-article")

(local
 (defthm fn-obsr-actual-old-selected-article-bytes
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

(defthm fn-obc-valid-final-parser-row-is-actual-old-selected-row
 (let* ((range (nth 0 s)) (group (nth 0 range)) (number (nth 1 range))
        (v (nth 3 range)) (seq (fn-cnx-view-seq group number v fn-cat))
        (h (fn-record-payload (fn-cat-at seq fn-cat)))
        (parser (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena))))
  (implies (and (equal (nth 2 s) :parse)
                (fn-obc-parser-prefix-p s fn-arena fn-cat)
                (equal (fn-lpc-verdict parser) :valid)
                (fn-cbor-octet-listp (nth (fn-obc-selected-handle s fn-cat) fn-arena))
                (posp number) (<= number *fn-nntp-max-article-number*) seq
                (fn-nntp-article-idp (fn-cat-row-article seq fn-arena fn-cat))
                (natp h))
   (equal (fn-npw-remaining (fn-obc-parser-pieces number parser) 0 fn-arena)
          (append (fn-nov-line number
                    (fn-nov-overview
                      (fn-scat-available-article group number v fn-arena fn-cat) fn-arena))
                  '(13 10)))))
 :rule-classes nil
 :hints (("Goal" :use
   (fn-obsr-actual-old-selected-article-bytes
    (:instance fn-obc-valid-final-parser-row-is-actual-old-article-row
      (number (nth 1 (nth 0 s)))
      (article (fn-scat-available-article (nth 0 (nth 0 s)) (nth 1 (nth 0 s))
                                         (nth 3 (nth 0 s)) fn-arena fn-cat))))
   :in-theory (disable fn-obc-selected-handle fn-obc-parser-prefix-p fn-lpc-tick
     fn-lpc-verdict fn-cnx-view-seq fn-cat-at fn-record-payload fn-cat-row-article
     fn-nntp-article-idp fn-scat-available-article fn-nntp-article-bytes
     fn-nov-overview fn-nov-line fn-npw-remaining fn-obc-parser-pieces
     fn-cbor-octet-listp))))
