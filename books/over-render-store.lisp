; KL8 supplies KO8's row hypothesis from the store at the stored limits
; and the retained bound. Builder-C owns the parse premise, established at
; ingress by fn-o1-stored-post-within-the-widened-limits; builder-M owns the
; length premise, the retained bound established at admission. Both history
; establishments are owed by those seats.
;
; KL7c equates the configured capacity term to one header-bounded NOV line
; plus CRLF and framing. Local helpers transfer the per-record premises
; through the catalog's complete or prefix history relation.

(in-package "ACL2")
(include-book "over-render-capl")
(include-book "over-render-bound")
(include-book "filed-catalog")
(include-book "filed-stored")

(local
 (defthm fn-ovrs-len-true-list-fix
   (equal (len (true-list-fix x)) (len x))
   :hints (("Goal" :in-theory (enable true-list-fix len)))))

(local
 (defthm fn-ovrs-capl-by-definition
   (equal (fn-ovr-over-capl hdr a (len server))
          (+ 2 (fn-ovr-nov-line-header-bound hdr a server) (fn-ovr-frame-max)))
   :hints (("Goal" :in-theory
            (e/d (fn-ovr-over-capl fn-ovr-nov-line-header-bound)
                 (fn-nntp-decimal fn-ovr-frame-max))))))

(defthm fn-ovr-over-capl-is-a-line-and-the-framing
  (equal (fn-ovr-over-capl hdr a (len server))
         (+ 2 (fn-ovr-nov-line-header-bound hdr a server) (fn-ovr-frame-max))))

(defun fn-ovr-records-parse-or-reclaimedp (records limits)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (and (or (not (fn-record-p (car records)))
               (fn-rcl-tombstonep (fn-record-payload (car records)))
               (fn-article-result-okp (fn-article-parse-under (fn-record-payload (car records)) limits)))
           (fn-ovr-records-parse-or-reclaimedp (cdr records) limits))
    t))

(defun fn-ovr-records-within-octets-or-reclaimedp (records a)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (and (or (not (fn-record-p (car records)))
               (fn-rcl-tombstonep (fn-record-payload (car records)))
               (<= (len (fn-record-payload (car records))) (nfix a)))
           (fn-ovr-records-within-octets-or-reclaimedp (cdr records) a))
    t))

; After selecting article records, no non-article disjunct is needed.
(local
 (defun fn-ovrs-all-boundedp (records a limits)
   (if (consp records)
       (and (or (fn-rcl-tombstonep (fn-record-payload (car records)))
                (and (fn-article-result-okp
                      (fn-article-parse-under (fn-record-payload (car records)) limits))
                     (<= (len (fn-record-payload (car records))) (nfix a))))
            (fn-ovrs-all-boundedp (cdr records) a limits))
     t)))

(local
 (defthm fn-ovrs-filter-bounded
   (implies (and (fn-ovr-records-parse-or-reclaimedp records limits)
                 (fn-ovr-records-within-octets-or-reclaimedp records a))
            (fn-ovrs-all-boundedp (fn-sf-article-records records) a limits))
   :hints (("Goal" :induct (len records)
            :in-theory (e/d (fn-ovrs-all-boundedp fn-sf-article-records
                             fn-ovr-records-parse-or-reclaimedp
                             fn-ovr-records-within-octets-or-reclaimedp)
                            (fn-record-p fn-record-payload fn-rcl-tombstonep
                             fn-article-result-okp fn-article-parse-under))))))

(local
 (defthm fn-ovrs-prefix-bounded
   (implies (and (fn-sf-prefixp xs ys) (fn-ovrs-all-boundedp ys a limits))
            (fn-ovrs-all-boundedp xs a limits))
   :hints (("Goal" :induct (fn-sf-prefixp xs ys)
            :in-theory (e/d (fn-sf-prefixp fn-ovrs-all-boundedp)
                            (fn-record-payload fn-rcl-tombstonep
                             fn-article-result-okp fn-article-parse-under))))))

(local
 (defthm fn-ovrs-nth-bounded
   (implies (and (fn-ovrs-all-boundedp records a limits) (< (nfix k) (len records)))
            (or (fn-rcl-tombstonep (fn-record-payload (nth k records)))
                (and (fn-article-result-okp
                      (fn-article-parse-under (fn-record-payload (nth k records)) limits))
                     (<= (len (fn-record-payload (nth k records))) (nfix a)))))
   :hints (("Goal" :in-theory
            (e/d (fn-ovrs-all-boundedp nth)
                 (fn-record-payload fn-rcl-tombstonep fn-article-result-okp fn-article-parse-under))))))

(local
 (defun fn-ovrs-jk-ind (j k)
   (declare (xargs :measure (nfix k)))
   (if (zp k) (list j) (fn-ovrs-jk-ind (+ 1 j) (- k 1)))))

(local
 (defthm fn-ovrs-nth-wire-list
   (implies (and (natp j) (natp k) (< (+ j k) (fn-cat-count fn-cat)))
            (equal (nth k (fn-cat-wire-list j fn-arena fn-cat))
                   (fn-held-wire-of (fn-cat-at (+ j k) fn-cat) fn-arena)))
   :hints (("Goal" :induct (fn-ovrs-jk-ind j k)
            :in-theory (e/d (nth) (fn-held-wire-of fn-cat-at-is-nth fn-cat-count-is-len))
            :expand ((fn-cat-wire-list j fn-arena fn-cat))))))

(local
 (defthm fn-ovrs-len-wire-list
   (implies (natp j)
            (equal (len (fn-cat-wire-list j fn-arena fn-cat))
                   (nfix (- (fn-cat-count fn-cat) j))))
   :hints (("Goal" :induct (fn-cat-wire-list j fn-arena fn-cat)
            :in-theory (e/d (fn-cat-wire-list)
                            (fn-held-wire-of fn-cat-at-is-nth fn-cat-count-is-len))))))

; Both owner relation arms provide a bounded prefix of the filtered history.
(local
 (defthm fn-ovrs-owner-wire-bounded
   (let ((records (fn-cat-history-articles
                   (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) fn-arena)))
     (implies (and (fn-cat-ocl-relation oc fn-arena fn-cat)
                   (fn-ovr-records-parse-or-reclaimedp records limits)
                   (fn-ovr-records-within-octets-or-reclaimedp records a))
              (and (fn-cat-p fn-cat)
                   (fn-arena-p fn-arena)
                   (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
                   (fn-ovrs-all-boundedp (fn-cat-wire-list 0 fn-arena fn-cat) a limits))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-ovrs-filter-bounded
                             (records (fn-cat-history-articles
                                       (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                                       fn-arena)))
                  (:instance fn-ovrs-prefix-bounded
                             (xs (fn-cat-wire-list 0 fn-arena fn-cat))
                             (ys (fn-sf-article-records
                                  (fn-cat-history-articles
                                   (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                                   fn-arena)))))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(fn-cat-ocl-relation fn-cat-history-relation
                              fn-cat-history-prefix-relation))))))

(local
 (defthm fn-ovrs-wire-row-bounded
   (implies (and (fn-ovrs-all-boundedp (fn-cat-wire-list 0 fn-arena fn-cat) a limits)
                 (natp i) (< i (fn-cat-count fn-cat)))
            (or (fn-rcl-tombstonep
                 (fn-arena-payload (fn-record-payload (fn-cat-at i fn-cat)) fn-arena))
                (and (fn-article-result-okp
                      (fn-article-parse-under
                       (fn-arena-payload (fn-record-payload (fn-cat-at i fn-cat)) fn-arena) limits))
                     (<= (len (fn-arena-payload (fn-record-payload (fn-cat-at i fn-cat)) fn-arena))
                         (nfix a)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-ovrs-nth-wire-list (j 0) (k i))
                  (:instance fn-ovrs-len-wire-list (j 0))
                  (:instance fn-ovrs-nth-bounded (k i) (records (fn-cat-wire-list 0 fn-arena fn-cat))))
            :in-theory (e/d (fn-held-wire-of fn-held-wire)
                            (fn-rcl-tombstonep fn-article-result-okp fn-article-parse-under
                             fn-arena-payload fn-cat-at-is-nth fn-cat-count-is-len
                             fn-cat-wire-list fn-ovrs-nth-wire-list fn-ovrs-len-wire-list
                             fn-ovrs-nth-bounded fn-ovrs-all-boundedp))))))

(local
 (defthm fn-ovrs-served-row-bounded
   (let ((records (fn-cat-history-articles
                   (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) fn-arena)))
     (implies (and (fn-cat-ocl-relation oc fn-arena fn-cat)
                   (fn-ovr-records-parse-or-reclaimedp records limits)
                   (fn-ovr-records-within-octets-or-reclaimedp records a)
                   (natp i) (< i (fn-cat-count fn-cat)))
              (let* ((article (fn-cat-row-article i fn-arena fn-cat))
                     (payload (fn-nntp-article-bytes article fn-arena)))
                (or (fn-nntp-article-tombstonep article fn-arena)
                    (and (fn-article-result-okp (fn-article-parse-under payload limits))
                         (<= (len payload) (nfix a)))))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-ovrs-owner-wire-bounded fn-ovrs-wire-row-bounded
                  (:instance fn-cat-row-payload-natp (seq i))
                  (:instance fn-cat-handles-inp-at (n (fn-cat-count fn-cat)) (seq i)))
            :in-theory
            (e/d (fn-cat-row-article fn-nntp-article-bytes fn-nntp-payload-bytes
                                   fn-nntp-article-tombstonep)
                 (fn-cat-ocl-relation fn-cat-history-articles fn-cat-handles-inp fn-cat-handles-inp-at
                  fn-cat-row-payload-natp fn-cat-at-is-nth fn-cat-count-is-len fn-arena-payload-is-nth
                  fn-arena-count-is-len fn-arena-payload fn-arena-count fn-rcl-tombstonep
                  fn-article-result-okp fn-article-parse-under fn-ovrs-all-boundedp fn-cat-wire-list
                  fn-ovr-records-parse-or-reclaimedp fn-ovr-records-within-octets-or-reclaimedp))))))

(local
 (defthm fn-ovrs-served-rows
   (let ((records (fn-cat-history-articles
                   (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) fn-arena)))
     (implies (and (fn-cat-ocl-relation oc fn-arena fn-cat)
                   (fn-o1-records-filed-or-reclaimedp records)
                   (fn-o1-cat-positionalp fn-cat)
                   (fn-ovr-records-parse-or-reclaimedp records limits)
                   (fn-ovr-records-within-octets-or-reclaimedp records a))
              (fn-ovr-rows-within-header a limits fn-arena fn-cat)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-ovrs-served-row-bounded
                             (i (fn-ovr-rows-within-header-witness a limits fn-arena fn-cat)))
                  (:instance fn-o1-served-catalog-rows-are-reclaimed-or-within-header
                             (i (fn-ovr-rows-within-header-witness a limits fn-arena fn-cat))))
            :expand ((fn-ovr-rows-within-header a limits fn-arena fn-cat))
            :in-theory
            (union-theories (theory 'minimal-theory) nil)))))

; Keep the bridge's premises symbolic for the unchanged statement below.
(local (in-theory (union-theories (theory 'minimal-theory) '(fn-ovrs-served-rows))))

(defthm fn-ovr-served-catalog-rows-within-header
  (let ((records (fn-cat-history-articles
                  (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) fn-arena)))
    (implies (and (fn-cat-ocl-relation oc fn-arena fn-cat)
                  (fn-o1-records-filed-or-reclaimedp records)
                  (fn-o1-cat-positionalp fn-cat)
                  (fn-ovr-records-parse-or-reclaimedp records (fn-o1-stored-header-limits limits agent))
                  (fn-ovr-records-within-octets-or-reclaimedp records a))
             (fn-ovr-rows-within-header a (fn-o1-stored-header-limits limits agent) fn-arena fn-cat))))
