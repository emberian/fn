; Same selected immutable payload, cached row representation boundary.
; Source correspondence is a carried premise, never a hot validator.
(in-package "ACL2")
(include-book "over-byte-old-row-relation")
(include-book "nov-row-capture")

(local
 (defthm fn-obcr-string-octets-aux-agree
  (equal (fn-record-string-octets-aux chars) (fn-nntp-string-octets-aux chars))
  :hints (("Goal" :induct (fn-record-string-octets-aux chars)
   :in-theory (enable fn-record-string-octets-aux fn-nntp-string-octets-aux)))))
(local
 (defthm fn-obcr-body-lines-of-facts
  (equal (fn-hf-body-lines (fn-held-facts-of bytes)) (fn-hf-body-lines-of bytes))
  :hints (("Goal" :in-theory (e/d (fn-held-facts-of fn-hf-internals)
   (fn-hf-body-lines-of fn-hnov-of fn-ctl-control-of fn-hf-split-index))))))

(local
 (defthm fn-obcr-initial-number-piece
  (equal (fn-npw-part-bytes (fn-nntp-decimal-field number) 0 fn-arena)
         (fn-nntp-decimal-field number))
  :hints (("Goal" :in-theory
   (e/d (fn-npw-part-bytes fn-nntp-decimal-field fn-nntp-decimal-tokenp
         fn-nntp-decimal-digitp)
        (fn-nntp-decimal fn-nntp-decimal-value-aux fn-nsw-remaining))))))

(local
 (defthm fn-obcr-generic-cached-row
  (implies (and (fn-hnov-p (fn-hf-nov facts))
                (fn-hnov-ok (fn-hf-nov facts))
                (natp octets) (natp (fn-hf-body-lines facts)))
   (equal (fn-npw-remaining (fn-npw-column-pieces number facts octets) 0 fn-arena)
    (append
     (fn-nov-line number
      (list :ok (fn-record-string-octets (fn-hnov-subject (fn-hf-nov facts)))
                (fn-record-string-octets (fn-hnov-from (fn-hf-nov facts)))
                (fn-record-string-octets (fn-hnov-date (fn-hf-nov facts)))
                (fn-record-string-octets (fn-hnov-msgid (fn-hf-nov facts)))
                (fn-record-string-octets (fn-hnov-references (fn-hf-nov facts)))
                octets (fn-hf-body-lines facts))) '(13 10))))
  :hints (("Goal" :in-theory
   (e/d (fn-npw-column-pieces fn-npw-remaining fn-npw-part-bytes
         fn-nov-line fn-nntp-append-pieces fn-nov-subject fn-nov-from
         fn-nov-date fn-nov-msgid fn-nov-references fn-nov-bytes fn-nov-lines
         fn-nntp-decimal fn-nntp-decimal-rev fn-hnov-p fn-hnov-internals)
        (fn-hf-nov fn-hf-body-lines fn-nntp-decimal-field
         fn-record-string-octets explode-nonnegative-integer))))))

(defthm fn-obc-cached-pieces-are-actual-old-source-row
 (let* ((bytes (fn-nntp-article-bytes article fn-arena))
        (nov (fn-hnov-of bytes)))
  (implies (and (equal facts (fn-held-facts-of bytes))
                (fn-hnov-ok nov))
   (equal (fn-npw-remaining (fn-npw-column-pieces number facts (len bytes)) 0 fn-arena)
          (append (fn-nov-line number (fn-nov-overview article fn-arena)) '(13 10)))))
 :rule-classes nil
 :hints (("Goal"
  :use (fn-obc-source-overview-is-actual-old-overview
        (:instance fn-hf-nov-of-held-facts-of (bytes (fn-nntp-article-bytes article fn-arena)))
        (:instance fn-obcr-body-lines-of-facts (bytes (fn-nntp-article-bytes article fn-arena)))
        (:instance fn-hnov-p-of-hnov-of (bytes (fn-nntp-article-bytes article fn-arena)))
        (:instance fn-obcr-generic-cached-row
          (octets (len (fn-nntp-article-bytes article fn-arena)))))
  :in-theory (disable fn-npw-column-pieces fn-npw-remaining fn-nov-line
     fn-nov-overview fn-nntp-article-bytes fn-held-facts-of fn-hnov-of
     fn-obcr-generic-cached-row fn-hf-body-lines-of fn-hf-nov fn-hnov-p
     fn-record-string-octets fn-hf-nov-of-held-facts-of fn-obcr-body-lines-of-facts
     fn-hnov-p-of-hnov-of))))
