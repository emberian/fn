; The selected physical suffix has at most one terminal request.
(in-package "ACL2")
(include-book "log-checkpoint-tail")
(include-book "defkeystone")
(local (include-book "std/lists/append" :dir :system))
(defthm fn-lc-frame-item-is-nth
 (implies (natp n) (equal (fn-frame-item n xs) (nth n xs)))
 :hints (("Goal" :induct (fn-frame-item n xs) :in-theory (enable nth fn-frame-item))))
(defun fn-lc-split-nth-induction (n i xs)
 (declare (xargs :measure (nfix i) :guard t :verify-guards nil))
 (if (or (mbe :logic (zp i) :exec (not (posp i))) (mbe :logic (zp n) :exec (not (posp n)))) xs (fn-lc-split-nth-induction (1- (nfix n)) (1- i) (mbe :logic (cdr xs) :exec (fn-lc-rest xs)))))
(defthm fn-lc-nth-of-split-prefix
 (implies (and (natp i) (< i (nfix n)) (fn-frame-split n xs))
          (equal (nth i (car (fn-frame-split n xs))) (nth i xs)))
 :hints (("Goal" :induct (fn-lc-split-nth-induction n i xs)
  :expand ((fn-frame-split n xs))
  :in-theory (e/d (fn-frame-split nth) (fn-frame-split-exists fn-frame-split-exists-consp)))))
(defthm fn-lc-nth-of-split-suffix
 (implies (and (natp i) (fn-frame-split n xs))
          (equal (nth i (cdr (fn-frame-split n xs))) (nth (+ (nfix n) i) xs)))
 :hints (("Goal" :induct (fn-frame-split n xs) :expand ((fn-frame-split n xs))
  :in-theory (e/d (fn-frame-split nth) (fn-frame-split-exists fn-frame-split-exists-consp)))))
(defthm fn-lc-open-kind-is-header-kind
 (implies (fn-frame-result-okp (fn-frame-open slice max))
          (equal (fn-frame-result-kind (fn-frame-open slice max)) (nth 5 slice)))
 :hints (("Goal" :in-theory (enable fn-frame-open fn-frame-decode fn-frame-head-fields
  fn-frame-result-okp fn-frame-result-kind fn-frame-ok fn-frame-error nth))))
(defthm fn-lc-non-rotation-slice-is-nonempty
 (implies (and (fn-lg-entry-okp slice prev max)
               (not (equal (nth 5 slice) *fn-lg-rotation-kind*)))
          (consp (fn-lg-slice-records slice max)))
 :hints (("Goal" :in-theory
  (e/d (fn-lg-entry-okp fn-lg-slice-records fn-lg-unpack-okp fn-lg-open-bound
          fn-frame-result-okp)
       (fn-frame-open fn-frame-result-kind fn-lg-unpack fn-lg-unpack-exactp fn-lg-recordsp)))))
(local (defthm fn-lc-length-of-conditional-entry
 (equal (len (append (if move (list a) (if article (list b) c)) rest))
        (+ (if (or move article) 1 (len c)) (len rest)))
 :hints (("Goal" :cases (move article)
   :in-theory (union-theories (theory 'minimal-theory)
     '((:DEFINITION LEN)
       (:DEFINITION NOT)
       (:EXECUTABLE-COUNTERPART BINARY-+)
       (:EXECUTABLE-COUNTERPART LEN)
       (:REWRITE CDR-CONS)
       (:REWRITE COMMUTATIVITY-OF-+)
       (:REWRITE LEN-OF-APPEND)))))))
(defthm fn-lc-scan-count-with-terminal
 (<= (len (nth 2 (fn-lc-scan-bytes bytes prev unit max fuel)))
     (+ (len (nth 1 (fn-lc-scan-bytes bytes prev unit max fuel)))
        (if (equal (car (fn-lc-scan-bytes bytes prev unit max fuel)) :terminal) 1 0)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lc-scan-bytes bytes prev unit max fuel)
  :in-theory (e/d (fn-lc-scan-bytes)
    (fn-lg-entry-okp fn-lg-slice-records fn-lc-move-framep fn-lc-move-event
     fn-lg-declared-len fn-lg-pad-len fn-lc-entry-octets-bound fn-lg-trailer)))))
(defun fn-lc-scan-summaryp (scan)
 (declare (xargs :guard (true-listp scan) :verify-guards nil))
 (<= (len (mbe :logic (nth 2 scan) :exec (fn-lc-at 2 scan))) (+ (len (mbe :logic (nth 1 scan) :exec (fn-lc-at 1 scan)))
                         (if (equal (mbe :logic (car scan) :exec (fn-lc-head scan)) :terminal) 1 0))))
(defthm fn-lc-byte-scan-summary
 (fn-lc-scan-summaryp (fn-lc-scan-bytes bytes prev unit max fuel))
 :hints (("Goal" :use fn-lc-scan-count-with-terminal
  :in-theory (e/d (fn-lc-scan-summaryp) (fn-lc-scan-bytes)))))
(defthm fn-lc-merged-scan-summary
 (implies (and (fn-lc-scan-summaryp one) (equal (car one) :ok)
               (fn-lc-scan-summaryp rest))
  (fn-lc-scan-summaryp
   (list (car rest) (append (cadr one) (cadr rest))
                     (append (caddr one) (caddr rest)) (cadddr rest))))
 :hints (("Goal" :in-theory (enable fn-lc-scan-summaryp))))
(defthm fn-lc-empty-scan-summary-by-definition
 (fn-lc-scan-summaryp (list :ok nil nil prev))
 :hints (("Goal" :in-theory (enable fn-lc-scan-summaryp))))
; Match the scanner's NTH projections without opening its byte recursion.
(local
 (defthm fn-lc-merged-nth-scan-summary
  (implies (and (fn-lc-scan-summaryp one) (equal (car one) :ok)
                (fn-lc-scan-summaryp rest))
   (fn-lc-scan-summaryp
    (list (car rest) (append (nth 1 one) (nth 1 rest))
                     (append (nth 2 one) (nth 2 rest)) (nth 3 rest))))
  :hints (("Goal" :in-theory (enable fn-lc-scan-summaryp)))))
(defthm fn-lc-segment-scan-summary
 (fn-lc-scan-summaryp (fn-lc-scan-segments segs segment offset prev unit max))
 :hints (("Goal" :induct (fn-lc-scan-segments segs segment offset prev unit max)
  :in-theory (e/d (fn-lc-scan-segments)
                 (fn-lc-scan-summaryp fn-lc-scan-bytes nfix)))))
; The remaining consumers use CADR/CADDR; normalize the fixed fields locally.
(local
 (defthm fn-lc-scan-field-projections
  (and (equal (nth 1 scan) (cadr scan))
       (equal (nth 2 scan) (caddr scan))
       (equal (nth 3 scan) (cadddr scan)))
  :hints (("Goal" :in-theory (enable nth)))))
(defthm fn-lc-scan-segment-count-with-terminal
 (<= (len (nth 2 (fn-lc-scan-segments segs segment offset prev unit max)))
     (+ (len (nth 1 (fn-lc-scan-segments segs segment offset prev unit max)))
        (if (equal (car (fn-lc-scan-segments segs segment offset prev unit max)) :terminal) 1 0)))
 :rule-classes nil
 :hints (("Goal" :use fn-lc-segment-scan-summary
  :in-theory (e/d (fn-lc-scan-summaryp)
                 (fn-lc-scan-segments fn-lc-segment-scan-summary)))))

(defthm fn-lc-decode-retains-count
 (implies (not (equal (fn-lc-decode-tail-records records) :bad))
          (equal (len (fn-lc-decode-tail-records records)) (len records)))
 :hints (("Goal" :induct (fn-lc-decode-tail-records records)
   :in-theory (e/d (fn-lc-decode-tail-records)
    (fn-frame-store-decode fn-frame-protected-prefix fn-frame-digest
     fn-record-decode-exact-impl fn-record-parse-okp fn-record-parse-value
     fn-frame-result-payload fn-frame-result-okp)))))
(defun fn-lc-entries-boundedp (entries bound)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp entries) (and (<= (nfix (mbe :logic (car entries) :exec (fn-lc-head entries))) (nfix bound))
                         (fn-lc-entries-boundedp (mbe :logic (cdr entries) :exec (fn-lc-rest entries)) bound)) t))
(defthm fn-lc-scan-requests-bounded
 (fn-lc-entries-boundedp (caddr (fn-lc-scan-bytes bytes prev unit max fuel))
                        (fn-lc-entry-octets-bound max))
 :hints (("Goal" :induct (fn-lc-scan-bytes bytes prev unit max fuel)
  :in-theory (e/d (fn-lc-scan-bytes fn-lc-entries-boundedp fn-lc-entry-octets-bound
                  fn-lg-batch-entry-bound)
   (fn-lg-entry-okp fn-lg-slice-records fn-lc-move-framep fn-lc-move-event
    fn-lg-declared-len fn-lg-pad-len fn-lg-trailer)))))
(defthm fn-lc-bounded-entries-of-append
 (equal (fn-lc-entries-boundedp (append x y) bound)
        (and (fn-lc-entries-boundedp x bound) (fn-lc-entries-boundedp y bound))))
(defthm fn-lc-empty-entries-bounded-by-definition
 (fn-lc-entries-boundedp nil bound)
 :hints (("Goal" :in-theory (enable fn-lc-entries-boundedp))))
(defthm fn-lc-segment-scan-requests-bounded
 (fn-lc-entries-boundedp
  (caddr (fn-lc-scan-segments segs segment offset prev unit max))
  (fn-lc-entry-octets-bound max))
 :hints (("Goal" :induct (fn-lc-scan-segments segs segment offset prev unit max)
  :in-theory (e/d (fn-lc-scan-segments) (fn-lc-scan-bytes fn-lc-entries-boundedp fn-lc-entry-octets-bound nfix)))))
(defthm fn-lc-selected-tail-entry-bridge
 (let ((selection (fn-lc-open-selection disk r mode count segs header)))
  (implies (equal (car selection) :checkpoint)
   (and (<= (len (fn-lc-tail-entries disk r mode segs))
            (+ 1 (len (fn-lc-selection-tail selection))))
        (fn-lc-entries-boundedp (fn-lc-tail-entries disk r mode segs)
                               (fn-lc-entry-octets-bound (fn-lc-tail-max header))))))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance fn-lc-scan-segment-count-with-terminal
    (segs (fn-lc-ordered-segments segs))
    (segment (nth 0 (fn-lc-header-S header)))
    (offset (nth 1 (fn-lc-header-S header)))
    (prev (nth 4 (fn-lc-header-S header)))
    (unit (fn-lc-tail-unit header)) (max (fn-lc-tail-max header))))
 :in-theory (e/d
  (fn-lc-open-selection fn-lc-tail-entries fn-lc-tail-history fn-lc-tail-scan
   fn-lc-selection-tail fn-lc-segs-retain fn-lc-adopted-header)
  (fn-lc-scan-segments fn-lc-ordered-segments fn-lc-decode-tail-records
   fn-lc-tail-unit fn-lc-tail-max fn-lc-header-S fn-lc-headerp fn-lc-header-of-open
   pgs-open fn-lc-entries-boundedp fn-lc-entry-octets-bound)))))
