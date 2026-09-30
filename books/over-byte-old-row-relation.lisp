; Exact old renderer bridge; selected-number visibility and range continuation
; remain separate obligations. No whole-state validator is served.
(in-package "ACL2")
(include-book "over-byte-parser-relation")
(include-book "nov-overview-source")

(local
 (defthm fn-obor-octet-predicates-agree
  (equal (fn-cbor-octet-listp bytes) (fn-octet-listp bytes))
  :hints (("Goal" :induct (fn-octet-listp bytes)
    :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp fn-octet-listp fn-octetp)))))

(local
 (defthm fn-obor-scrub-is-octets
  (fn-octet-listp (fn-nov-scrub bytes))
  :hints (("Goal" :induct (fn-nov-scrub bytes)
   :in-theory (enable fn-nov-scrub fn-nov-scrub-byte fn-octet-listp
                      fn-octetp fn-ag-car fn-ag-cdr)))))

(local
 (defthm fn-obor-header-string-roundtrip
  (equal (fn-record-string-octets (fn-hnov-field view name))
         (fn-nov-header-content view name))
  :hints (("Goal" :use
    ((:instance fn-record-string-octets-of-octets-string
                (octets (fn-nov-header-content view name))))
   :in-theory (e/d (fn-hnov-field fn-nov-header-content)
                  (fn-record-string-octets fn-record-octets-string fn-nov-scrub))))))

(local
 (defthm fn-obor-successful-source-is-octets
  (implies (fn-hnov-ok (fn-hnov-of bytes)) (fn-cbor-octet-listp bytes))
  :hints (("Goal" :in-theory
   (e/d (fn-hnov-of fn-hnov-of-parsed fn-hnov-parsed-okp fn-hnov-internals
         fn-article-parse fn-article-parse-under fn-article-error fn-article-result-okp)
        (fn-article-parse-lines fn-cbor-at-mostp fn-cbor-octet-listp
         fn-article-syntax-p fn-hnov-field fn-rcl-tombstonep))))))

(defthm fn-obc-source-overview-is-actual-old-overview
 (let* ((bytes (fn-nntp-article-bytes article fn-arena))
        (nov (fn-hnov-of bytes)))
  (implies (fn-hnov-ok nov)
   (equal (fn-nov-overview article fn-arena)
     (list :ok (fn-record-string-octets (fn-hnov-subject nov))
               (fn-record-string-octets (fn-hnov-from nov))
               (fn-record-string-octets (fn-hnov-date nov))
               (fn-record-string-octets (fn-hnov-msgid nov))
               (fn-record-string-octets (fn-hnov-references nov))
               (len bytes) (fn-hf-body-lines-of bytes)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
   (e/d (fn-nov-overview fn-hnov-of fn-hnov-of-parsed fn-hnov-parsed-okp
         fn-hnov-internals fn-nov-body-line-count fn-nntp-article-length
         fn-hf-body-lines-of-is-nov-body-line-count-by-definition)
        (fn-nov-header-content fn-hnov-field fn-nntp-article-bytes
         fn-hf-body-lines-of fn-nntp-split-article fn-nntp-crlf-lines
         fn-record-string-octets fn-record-octets-string fn-rcl-tombstonep)))))

(local
 (defthm fn-obor-valid-parser-has-successful-nov
  (implies (equal (fn-lpc-verdict parser) :valid)
           (fn-hnov-ok (fn-lpc-nov-value parser arena)))
  :hints (("Goal" :in-theory (e/d (fn-lpc-nov-value fn-hnov-internals)
    (fn-lpc-verdict fn-lpc-field fn-lpc-span-value fn-lpc-tombstonep
     fn-record-octets-string))))))

(defthm fn-obc-valid-final-parser-row-is-actual-old-article-row
 (let* ((parser (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena)))
        (bytes (nth (fn-obc-selected-handle s fn-cat) fn-arena)))
  (implies (and (equal (nth 2 s) :parse)
                (fn-obc-parser-prefix-p s fn-arena fn-cat)
                (equal (fn-lpc-verdict parser) :valid)
                (fn-cbor-octet-listp bytes)
                (equal (fn-nntp-article-bytes article fn-arena) bytes))
   (equal (fn-npw-remaining (fn-obc-parser-pieces number parser) 0 fn-arena)
          (append (fn-nov-line number (fn-nov-overview article fn-arena)) '(13 10)))))
 :rule-classes nil
 :hints (("Goal" :use
   (fn-obc-final-parser-row-is-actual-selected-source-row
    fn-obc-final-parser-tick-has-actual-selected-nov
    (:instance fn-obor-valid-parser-has-successful-nov
       (parser (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena))) (arena fn-arena))
    fn-obc-source-overview-is-actual-old-overview)
   :in-theory (disable fn-lpc-tick fn-lpc-verdict fn-lpc-nov-value fn-hnov-ok
    fn-hnov-of fn-obc-selected-handle fn-obc-parser-prefix-p fn-cbor-octet-listp
    fn-nntp-article-bytes fn-nov-overview fn-nov-line fn-npw-remaining
    fn-obc-parser-pieces fn-record-string-octets fn-hf-body-lines-of))))
