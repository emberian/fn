; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-nov-byte-store")
(include-book "records-invariants")

(local (defthm fn-lbnv-true-list-fix-identity
 (implies (true-listp xs) (equal (true-list-fix xs) xs))
 :hints (("Goal" :induct (len xs) :in-theory (enable true-list-fix true-listp)))))

(defthm fn-lbc-small-text-byte-round-trip
 (implies (fn-lbc-text-smallp text)
  (equal (fn-record-octets-string (true-list-fix (fn-record-string-octets text))) text))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-record-string-round-trip))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-text-smallp fn-record-octet-stringp fn-lbnv-true-list-fix-identity
     fn-cbor-octet-listp-implies-true-listp)))))

(local (defthm fn-lbnv-count-by-store
 (equal (fn-lbc-nov-record-count fn-lbc) (len (nth *fn-lbc-nov-store* fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-nov-record-count fn-lbc-nov-store fn-lbc-nov-count-is-len))))))

(local (defthm fn-lbnv-len-append-one
 (equal (len (append xs (list x))) (+ 1 (len xs)))
 :hints (("Goal" :induct (len xs) :in-theory (enable binary-append len)))))

(local (defthm fn-lbnv-nth-append-at-length
 (equal (nth (len xs) (append xs (list x))) x)
 :hints (("Goal" :induct (len xs) :in-theory (enable binary-append len nth)))))

(local (defthm fn-lbnv-decode-equal-small-text-bytes
  (implies (and (equal bytes (true-list-fix (fn-record-string-octets text)))
                (fn-lbc-text-smallp text))
   (equal (fn-record-octets-string bytes) text))
  :rule-classes ((:rewrite :match-free :all))
  :hints (("Goal" :do-not-induct t
   :use ((:instance fn-lbc-small-text-byte-round-trip))
   :in-theory (theory 'minimal-theory)))))

(local (defthm fn-lbnv-decode-matching-spans
 (implies (and (fn-lbc-nov-smallp nov)
               (fn-lb-nov-span-bytes-corr spans (fn-lbc-nov-texts nov) fn-lbc))
  (equal (fn-hnov-make (fn-hnov-tomb nov) (fn-hnov-ok nov)
 (fn-lbc-nov-text (nth 0 spans) (nth 1 spans) fn-lbc)
 (fn-lbc-nov-text (nth 2 spans) (nth 3 spans) fn-lbc)
 (fn-lbc-nov-text (nth 4 spans) (nth 5 spans) fn-lbc)
 (fn-lbc-nov-text (nth 6 spans) (nth 7 spans) fn-lbc)
 (fn-lbc-nov-text (nth 8 spans) (nth 9 spans) fn-lbc)) nov))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-hnov-make-of-accessors (x nov))
(:instance fn-lbnv-decode-equal-small-text-bytes (bytes (fn-lbc-overview-pool-range (nfix (nth 0 spans)) (nfix (nth 1 spans)) fn-lbc)) (text (fn-hnov-subject nov)))
(:instance fn-lbnv-decode-equal-small-text-bytes (bytes (fn-lbc-overview-pool-range (nfix (nth 2 spans)) (nfix (nth 3 spans)) fn-lbc)) (text (fn-hnov-from nov)))
(:instance fn-lbnv-decode-equal-small-text-bytes (bytes (fn-lbc-overview-pool-range (nfix (nth 4 spans)) (nfix (nth 5 spans)) fn-lbc)) (text (fn-hnov-date nov)))
(:instance fn-lbnv-decode-equal-small-text-bytes (bytes (fn-lbc-overview-pool-range (nfix (nth 6 spans)) (nfix (nth 7 spans)) fn-lbc)) (text (fn-hnov-msgid nov)))
(:instance fn-lbnv-decode-equal-small-text-bytes (bytes (fn-lbc-overview-pool-range (nfix (nth 8 spans)) (nfix (nth 9 spans)) fn-lbc)) (text (fn-hnov-references nov))))
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-hnov-p fn-lbc-nov-smallp fn-lbc-nov-texts fn-lb-nov-span-bytes-corr fn-lbc-nov-text
     fn-lbc-small-text-byte-round-trip nth)) '((:definition nfix) (:definition true-list-fix) (tau-system)))))))

(defthm fn-lbc-nov-at-of-append-nov-new
 (implies (fn-lbc-nov-pool-fitp nov (fn-lbc-overview-pool-count fn-lbc))
  (equal (fn-lbc-nov-at (fn-lbc-nov-record-count fn-lbc) (fn-lbc-append-nov nov fn-lbc)) nov))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-new-nov-spans-read-appended-bytes)
        (:instance fn-lbnv-decode-matching-spans
          (spans (fn-lbc-nov-spans (fn-lbc-nov-texts nov) (fn-lbc-overview-pool-count fn-lbc)))
          (fn-lbc (fn-lbc-append-nov nov fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-nov-at fn-lbc-nov-store-of-append-nov fn-lbc-nov-pool-fitp fn-lbnv-count-by-store fn-lbnv-len-append-one fn-lbnv-nth-append-at-length nth fn-lbc-nov-field-tomb-by-definition fn-lbc-nov-field-ok-by-definition fn-lbc-nov-field-subject-start-by-definition fn-lbc-nov-field-subject-length-by-definition fn-lbc-nov-field-from-start-by-definition fn-lbc-nov-field-from-length-by-definition fn-lbc-nov-field-date-start-by-definition fn-lbc-nov-field-date-length-by-definition fn-lbc-nov-field-msgid-start-by-definition fn-lbc-nov-field-msgid-length-by-definition fn-lbc-nov-field-references-start-by-definition fn-lbc-nov-field-references-length-by-definition)))))
