;; Route A1: log-free loaders for the LB columns.  fn-lbc-append-row-at is
;; fn-lbc-append-row (catalog-columns.lisp) with the three things the model
;; log supplied taken as arguments: the stored payload, the locator words
;; (fn-loc-make segment offset length) and the verified flag.  Same
;; body otherwise; no correspondence theorem is stated here (OWED.md).
(in-package "ACL2")
(include-book "catalog-columns")
(include-book "catalog-columns-withdraw-row")
(include-book "catalog-columns-live-number")

(defun fn-lbc-append-row-at (row payload loc0 loc1 verifiedp fn-lbc)
  (declare (xargs :stobjs fn-lbc :guard (and (fn-cat-rowp row) (fn-lbc-escape-cellsp 0 fn-lbc))
                  :verify-guards nil))
  (let* ((i (fn-lbc-count fn-lbc))
         (facts (fn-held-facts row)) (nov (fn-hf-nov facts))
         (nov-small (fn-lbc-nov-pool-fitp nov (fn-lbc-overview-pool-count fn-lbc)))
         (render-nov (fn-hnov-of payload))
         (nov-start (fn-lbc-nov-record-count fn-lbc))
         (fn-lbc (if nov-small (fn-lbc-append-nov nov fn-lbc) fn-lbc))
         (render-small (fn-lbc-nov-pool-fitp render-nov (fn-lbc-overview-pool-count fn-lbc)))
         (render-start (fn-lbc-nov-record-count fn-lbc))
         (fn-lbc (if render-small (fn-lbc-append-nov render-nov fn-lbc) fn-lbc))
         (groups-small (fn-lbc-pool-spans-fitp (fn-record-groups row) nil
                                             (fn-lbc-overview-pool-count fn-lbc)))
         (groups-start (fn-lbc-membership-record-count fn-lbc))
         (fn-lbc (if groups-small
                     (fn-lbc-append-memberships (fn-record-groups row) nil fn-lbc)
                   fn-lbc))
         (numbers-small
           (and (fn-lbc-numbers-smallp (fn-held-numbers row))
                (fn-lbc-pool-spans-fitp (fn-held-numbers row) t
                                       (fn-lbc-overview-pool-count fn-lbc))))
         (numbers-start (fn-lbc-membership-record-count fn-lbc))
         (fn-lbc (if numbers-small
                     (fn-lbc-append-memberships (fn-held-numbers row) t fn-lbc)
                   fn-lbc))
         (msgid-offset (fn-lbc-msgid-pool-count fn-lbc))
         (msgid-bytes (fn-record-string-octets (fn-record-msgid row)))
         (fn-lbc (fn-lbc-msgid-pool-append msgid-bytes fn-lbc))
         (head-length (len (fn-nntp-stuffed-section :head payload)))
         (raw-head-length
           (len (fn-la-payload-wire (fn-nntp-split-head (fn-nntp-split-article payload)))))
         (previous-max (if (zp i) 0 (fn-lbc-value (- i 1) :prefix-max fn-lbc)))
         (max-stamp (max (nfix previous-max) (nfix (fn-record-stamp row))))
         (w (fn-held-withdrawn row))
         (escape
           (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset
             (len msgid-bytes) i nov-start render-start groups-start numbers-start
             raw-head-length nov-small render-small groups-small numbers-small))
         (flags (fn-lbc-row-flags nov w escape
                  verifiedp
                  (fn-rcl-tombstonep payload))))
    (let ((loc0 loc0))
      (let* ((words
               (list (fn-lbc-u64 (fn-record-payload row)) loc0 loc1
                     (fn-lbc-u64 head-length) (fn-lbc-u64 (fn-record-stamp row))
                     (fn-lbc-u64 max-stamp) (fn-lbc-u64 (fn-record-txid row))
                     (fn-lbc-u64 (fn-record-generation row)) (fn-lbc-u64 (fn-record-charge row))
                     (fn-lbc-msgid-hash (fn-record-msgid row))
                     (fn-lbc-u64 msgid-offset) (fn-lbc-u64 (len msgid-bytes))
                     (fn-lbc-u64 (car w)) (fn-lbc-u64 (cdr w)) (fn-lbc-u64 i) flags))
             (directory
               (list (fn-lbc-u64 (fn-record-sequence row))
                     (fn-lbc-u64 (fn-hf-octets facts))
                     (fn-lbc-u64 (fn-hf-body-start facts))
                     (if (natp (fn-hf-body-start facts)) t nil)
                     (fn-lbc-u64 (fn-hf-body-lines facts))
                     (fn-lbc-u64 nov-start) (if nov-small 1 0)
                     (fn-lbc-u64 render-start) (if render-small 1 0)
                     (fn-lbc-u64 groups-start) (fn-lbc-u64 (len (fn-record-groups row)))
                     (fn-lbc-u64 numbers-start) (fn-lbc-u64 (len (fn-held-numbers row)))
                     (equal (car (fn-nntp-section-of-bytes payload :article)) :ok)
                     (equal (car (fn-nntp-section-of-bytes payload :head)) :ok)
                     (equal (car (fn-nntp-section-of-bytes payload :body)) :ok)
                     (fn-lbc-u64 raw-head-length) (fn-nntp-framed-of-bytes payload)))
             (fn-lbc
               (stobj-let ((fn-lbc-rowwords (fn-lbc-row-store fn-lbc)))
                 (fn-lbc-rowwords) (fn-lbc-rowwords-append words fn-lbc-rowwords) fn-lbc))
             (fn-lbc
               (stobj-let ((fn-lbc-directory (fn-lbc-directory-store fn-lbc)))
                 (fn-lbc-directory) (fn-lbc-directory-append directory fn-lbc-directory) fn-lbc)))
        (fn-lbc-escape-store-put i escape fn-lbc)))))

;; Incremental commit: the row, its numbers, its group summaries and its
;; msgid slot, in step (what fn-lbc-open-rebuild does in four passes).  The
;; row arrives with its numbers assigned (fn-held-numbers), as fn-cat-commit
;; has it; births are at a group's top, so a live birth is the new high and
;; the first live birth is the low.  The slot table doubles when more than
;; half full and is re-indexed whole.
(defun fn-lbc-slots-zero (i n fn-lbc)
  (declare (xargs :stobjs fn-lbc :measure (nfix (- (nfix n) (nfix i))) :verify-guards nil))
  (if (and (natp i) (natp n) (< i n))
      (let ((fn-lbc (fn-lbc-slot-put i 0 fn-lbc)))
        (fn-lbc-slots-zero (+ i 1) n fn-lbc))
    fn-lbc))

(defun fn-lbc-slots-ensure (fn-lbc)
  (declare (xargs :stobjs fn-lbc :verify-guards nil))
  (let ((cap (fn-lbc-slot-count fn-lbc)) (n (fn-lbc-count fn-lbc)))
    (if (<= (* 2 (+ n 1)) cap)
        fn-lbc
      (let* ((fn-lbc (fn-lbc-slots-zero 0 cap fn-lbc))
             (fn-lbc (fn-lbc-reserve-slots (+ 1 cap) fn-lbc)))
        (fn-lbc-index-slots 0 n fn-lbc)))))

(defun fn-lbc-commit-summaries (numbers seen row fn-lbc)
  (declare (xargs :stobjs fn-lbc :verify-guards nil))
  (if (consp numbers)
      (let* ((g (caar numbers)) (k (cdar numbers)))
        (if (member-equal g seen)
            (fn-lbc-commit-summaries (cdr numbers) seen row fn-lbc)
          (let* ((s (fn-lbc-live-summary g fn-lbc))
                 (livep (fn-cat-live-rowp g k row))
                 (next (max (nth 3 s) (+ 1 (nfix k))))
                 (vals (if livep
                           (list (+ 1 (nth 0 s))
                                 (if (zp (nth 1 s)) k (min (nth 1 s) k))
                                 (max (nth 2 s) k) next)
                         (list (nth 0 s) (nth 1 s) (nth 2 s) next)))
                 (fn-lbc (fn-lbc-summary-put g vals 1 fn-lbc)))
            (fn-lbc-commit-summaries (cdr numbers) (cons g seen) row fn-lbc))))
    fn-lbc))

(defun fn-lbc-commit-row (row payload loc0 loc1 verifiedp fn-lbc)
  (declare (xargs :stobjs fn-lbc :verify-guards nil))
  (let* ((fn-lbc (fn-lbc-slots-ensure fn-lbc))
         (i (fn-lbc-count fn-lbc))
         (fn-lbc (fn-lbc-append-row-at row payload loc0 loc1 verifiedp fn-lbc))
         (fn-lbc (fn-lbc-number-put-row (fn-held-numbers row) i fn-lbc))
         (fn-lbc (fn-lbc-commit-summaries (fn-held-numbers row) nil row fn-lbc)))
    (fn-lbc-index-slots i (+ i 1) fn-lbc)))

;; Live extrema by scan over the group's number array (no live-link columns
;; yet; O(group) only when a withdrawal takes the low or the high).
(defun fn-lbc-lv-first (group k top fn-lbc)
  (declare (xargs :stobjs fn-lbc :measure (nfix (- (+ 1 (nfix top)) (nfix k))) :verify-guards nil))
  (if (and (natp k) (natp top) (<= k top))
      (if (fn-lbc-live-numberp group k fn-lbc) k (fn-lbc-lv-first group (+ 1 k) top fn-lbc))
    0))

(defun fn-lbc-lv-last (group k fn-lbc)
  (declare (xargs :stobjs fn-lbc :measure (nfix k) :verify-guards nil))
  (if (posp k)
      (if (fn-lbc-live-numberp group k fn-lbc) k (fn-lbc-lv-last group (- k 1) fn-lbc))
    0))

;; Incremental withdraw of row I at version V by BY (a no-op on an already
;; withdrawn row, as fn-cat-mark-withdrawn).  Per group the row holds a
;; number in: if that number was live it leaves the count, and the low or
;; high is recomputed (from the group's number array) only when the number
;; was the low or the high.
(defun fn-lbc-live-groups (numbers seen fn-lbc)
  (declare (xargs :stobjs fn-lbc :verify-guards nil))
  (if (consp numbers)
      (let ((g (caar numbers)) (k (cdar numbers)))
        (if (member-equal g seen)
            (fn-lbc-live-groups (cdr numbers) seen fn-lbc)
          (cons (list g k (fn-lbc-live-numberp g k fn-lbc))
                (fn-lbc-live-groups (cdr numbers) (cons g seen) fn-lbc))))
    nil))

(defun fn-lbc-withdraw-summaries (pre fn-lbc)
  (declare (xargs :stobjs fn-lbc :verify-guards nil))
  (if (consp pre)
      (let* ((g (nth 0 (car pre))) (k (nth 1 (car pre))) (was-live (nth 2 (car pre)))
             (fn-lbc
               (if (not was-live)
                   fn-lbc
                 (let* ((s (fn-lbc-live-summary g fn-lbc))
                        (top (- (nth 3 s) 1))
                        (low (if (equal k (nth 1 s)) (fn-lbc-lv-first g 1 top fn-lbc) (nth 1 s)))
                        (high (if (equal k (nth 2 s)) (fn-lbc-lv-last g top fn-lbc) (nth 2 s))))
                   (fn-lbc-summary-put g (list (- (nth 0 s) 1) low high (nth 3 s)) 1 fn-lbc)))))
        (fn-lbc-withdraw-summaries (cdr pre) fn-lbc))
    fn-lbc))

(defun fn-lbc-withdraw-row (i version by fn-lbc)
  (declare (xargs :stobjs fn-lbc :verify-guards nil))
  (if (or (not (natp i)) (<= (fn-lbc-count fn-lbc) i) (fn-lbc-withdrawn i fn-lbc))
      fn-lbc
    (let* ((pre (fn-lbc-live-groups (fn-lbc-numbers i fn-lbc) nil fn-lbc))
           (fn-lbc (fn-lbc-set-withdrawal i version by fn-lbc)))
      (fn-lbc-withdraw-summaries pre fn-lbc))))
