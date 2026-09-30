; Semantic join of actual legacy row references to the NOV renderer.
; PRF-1066. Logical vocabulary only; no served validation or activation.
(in-package "ACL2")
(include-book "over-row-pieces")
(include-book "legacy-parser-reference")
(include-book "legacy-parser-header")
(include-book "nov-render-line")
(include-book "records-canonicality")

(local (defthm fn-obcr-nth-nfix
 (equal (nth (nfix h) xs) (nth h xs))
 :hints (("Goal" :cases ((natp h)) :in-theory (enable nth nfix)))))
(local (defthm fn-obcr-take-nfix
 (equal (take (nfix n) xs) (take n xs))
 :hints (("Goal" :cases ((natp n)) :in-theory (enable take nfix)))))

(local (defthm fn-obcr-nfix-natural
 (implies (natp x) (equal (nfix x) x))
 :hints (("Goal" :in-theory (enable nfix)))))

(defthm fn-obc-span-piece-denotes-parser-value
  (implies (or (not span) (natp (fn-lpc-at 1 span)))
           (equal (fn-npw-part-bytes (fn-obc-span-piece span) 0 fn-arena)
                  (fn-lpc-span-value span fn-arena)))
  :hints (("Goal" :use ((:instance fn-nsw-source-is-slice
                                  (h (fn-lpc-at 0 span))
                                  (at (fn-lpc-at 1 span))
                                  (left (fn-lpc-at 2 span))))
           :in-theory
           (e/d (fn-obc-span-piece fn-npw-part-bytes fn-nsw-remaining
                 fn-lpc-span-value fn-lpc-at)
                (fn-nsw-source fn-nov-scrub take nthcdr nth nfix)))))

(local (defthm fn-obcr-string-codecs-agree
 (equal (fn-record-string-octets-aux chars) (fn-nntp-string-octets-aux chars))
 :hints (("Goal" :induct (fn-record-string-octets-aux chars)
   :in-theory (enable fn-record-string-octets-aux fn-nntp-string-octets-aux)))))

(local (defthm fn-obcr-octet-piece-denotes-itself
 (implies (fn-cbor-octet-listp bytes)
  (equal (fn-npw-part-bytes bytes pos fn-arena) bytes))
 :hints (("Goal" :in-theory (enable fn-npw-part-bytes fn-cbor-octet-listp fn-cbor-octetp)))))

(local (defthm fn-obcr-digit-run-octets
 (implies (and (true-listp bytes) (fn-nntp-decimal-tokenp bytes)) (fn-cbor-octet-listp bytes))
 :hints (("Goal" :induct (fn-nntp-decimal-tokenp bytes)
 :in-theory (enable fn-nntp-decimal-tokenp fn-nntp-decimal-digitp fn-cbor-octet-listp fn-cbor-octetp)))))

(local (defthm fn-obcr-number-is-octets
 (fn-cbor-octet-listp (fn-nntp-decimal-field number))
 :hints (("Goal" :in-theory (enable fn-nntp-decimal-field fn-nntp-decimal-tokenp fn-nntp-decimal-digitp
                                  fn-cbor-octet-listp fn-cbor-octetp)))))

(local (defthm fn-obcr-nil-span-value
 (equal (fn-lpc-span-value nil arena) nil)
 :hints (("Goal" :in-theory (enable fn-lpc-span-value)))))

(local (defthm fn-obcr-append-associative
 (equal (append (append a b) c) (append a (append b c)))))

(local (defthm fn-obcr-parser-pieces-denote-raw-line
 (implies (and (or (not (fn-lpc-field parser 0)) (natp (fn-lpc-at 1 (fn-lpc-field parser 0))))
               (or (not (fn-lpc-field parser 1)) (natp (fn-lpc-at 1 (fn-lpc-field parser 1))))
               (or (not (fn-lpc-field parser 2)) (natp (fn-lpc-at 1 (fn-lpc-field parser 2))))
               (or (not (fn-lpc-field parser 3)) (natp (fn-lpc-at 1 (fn-lpc-field parser 3))))
               (or (not (fn-lpc-field parser 4)) (natp (fn-lpc-at 1 (fn-lpc-field parser 4)))))
  (equal (fn-npw-remaining (fn-obc-parser-pieces number parser) 0 fn-arena)
   (append
    (fn-nov-line number
      (list :ok (fn-lpc-span-value (fn-lpc-field parser 0) fn-arena)
                (fn-lpc-span-value (fn-lpc-field parser 1) fn-arena)
                (fn-lpc-span-value (fn-lpc-field parser 2) fn-arena)
                (fn-lpc-span-value (fn-lpc-field parser 3) fn-arena)
                (fn-lpc-span-value (fn-lpc-field parser 4) fn-arena)
                (nfix (fn-lpc-at 1 parser)) (fn-lpc-body-lines parser)))
    '(13 10))))
 :hints (("Goal" :in-theory
  (e/d (fn-obc-parser-pieces fn-npw-remaining fn-npw-part-bytes
        fn-nov-line fn-nov-subject fn-nov-from fn-nov-date fn-nov-msgid
        fn-nov-references fn-nov-bytes fn-nov-lines
        fn-nntp-append-pieces fn-nntp-decimal fn-nntp-decimal-rev)
       (fn-obc-span-piece fn-lpc-span-value fn-lpc-field fn-lpc-at
        fn-lpc-body-lines fn-nntp-decimal-field fn-record-string-octets
        explode-nonnegative-integer))))))

(local (defthm fn-obcr-scrub-is-octets
 (fn-cbor-octet-listp (fn-nov-scrub bytes))
 :hints (("Goal" :induct (fn-nov-scrub bytes)
 :in-theory (enable fn-nov-scrub fn-nov-scrub-byte fn-cbor-octet-listp fn-cbor-octetp fn-ag-car fn-ag-cdr)))))
(local (defthm fn-obcr-span-value-is-octets
 (fn-cbor-octet-listp (fn-lpc-span-value span arena))
 :hints (("Goal" :in-theory (e/d (fn-lpc-span-value) (fn-nov-scrub))))))
(local (defthm fn-obcr-span-value-string-roundtrip
 (equal (fn-record-string-octets (fn-record-octets-string (fn-lpc-span-value span arena)))
        (fn-lpc-span-value span arena))
 :hints (("Goal" :use ((:instance fn-record-string-octets-of-octets-string (octets (fn-lpc-span-value span arena))))
 :in-theory (disable fn-record-string-octets fn-record-octets-string fn-lpc-span-value)))))

(local (defthm fn-obcr-parser-nov-fields-denote-spans
 (let ((nov (fn-lpc-nov-value parser arena)))
  (and (equal (fn-record-string-octets (fn-hnov-subject nov)) (fn-lpc-span-value (fn-lpc-field parser 0) arena))
       (equal (fn-record-string-octets (fn-hnov-from nov)) (fn-lpc-span-value (fn-lpc-field parser 1) arena))
       (equal (fn-record-string-octets (fn-hnov-date nov)) (fn-lpc-span-value (fn-lpc-field parser 2) arena))
       (equal (fn-record-string-octets (fn-hnov-msgid nov)) (fn-lpc-span-value (fn-lpc-field parser 3) arena))
       (equal (fn-record-string-octets (fn-hnov-references nov)) (fn-lpc-span-value (fn-lpc-field parser 4) arena))))
 :hints (("Goal" :in-theory
  (e/d (fn-lpc-nov-value fn-hnov-internals)
       (fn-lpc-tombstonep fn-lpc-verdict fn-lpc-field fn-lpc-span-value fn-record-string-octets fn-record-octets-string))))))

(defthm fn-obc-parser-pieces-denote-parser-nov-row
 (implies (and (or (not (fn-lpc-field parser 0)) (natp (fn-lpc-at 1 (fn-lpc-field parser 0))))
               (or (not (fn-lpc-field parser 1)) (natp (fn-lpc-at 1 (fn-lpc-field parser 1))))
               (or (not (fn-lpc-field parser 2)) (natp (fn-lpc-at 1 (fn-lpc-field parser 2))))
               (or (not (fn-lpc-field parser 3)) (natp (fn-lpc-at 1 (fn-lpc-field parser 3))))
               (or (not (fn-lpc-field parser 4)) (natp (fn-lpc-at 1 (fn-lpc-field parser 4)))))
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
 :hints (("Goal" :use fn-obcr-parser-pieces-denote-raw-line
 :in-theory (disable fn-obc-parser-pieces fn-npw-remaining fn-nov-line fn-lpc-nov-value fn-lpc-field fn-lpc-at fn-lpc-span-value fn-record-string-octets))))
