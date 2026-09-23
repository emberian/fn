; Derived per-group buckets for served NNTP number/range reads.  The source
; entries and all validity decisions remain books/index and books/nntp-index.
(in-package "ACL2")
(include-book "nntp-index")

(defun fn-gidx-bucket (group buckets)
  (declare (xargs :guard t))
  (if (consp buckets)
      (if (equal group (fn-ag-car (fn-ag-car buckets)))
          (fn-ag-cdr (fn-ag-car buckets))
        (fn-gidx-bucket group (cdr buckets)))
    nil))

(defun fn-gidx-put (entry buckets)
  (declare (xargs :guard t))
  (let ((group (fn-index-entry-group entry)))
    (if (consp buckets)
        (if (equal group (fn-ag-car (fn-ag-car buckets)))
            (cons (cons group (cons entry (fn-ag-cdr (fn-ag-car buckets))))
                  (cdr buckets))
          (cons (car buckets) (fn-gidx-put entry (cdr buckets))))
      (list (cons group (list entry))))))

(defun fn-gidx-build-entries (entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (fn-gidx-put (car entries) (fn-gidx-build-entries (cdr entries)))
    nil))

(defun fn-gidx-build (articles)
  (declare (xargs :guard t))
  (fn-gidx-build-entries (fn-index-build articles)))

(defun fn-gidx-select (group entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (if (equal group (fn-index-entry-group (car entries)))
          (cons (car entries) (fn-gidx-select group (cdr entries)))
        (fn-gidx-select group (cdr entries)))
    nil))

(defthm fn-gidx-bucket-of-put
  (equal (fn-gidx-bucket group (fn-gidx-put entry buckets))
         (if (equal group (fn-index-entry-group entry))
             (cons entry (fn-gidx-bucket group buckets))
           (fn-gidx-bucket group buckets)))
  :hints (("Goal" :induct (fn-gidx-put entry buckets))))

(defthm fn-gidx-bucket-of-build-entries
  (equal (fn-gidx-bucket group (fn-gidx-build-entries entries))
         (fn-gidx-select group entries)))

; The selected bucket is the exact ordered membership projection of the
; authoritative archive.  Connection pins carry this fact from build time;
; served reads never revalidate against the entire archive.
(defthm fn-gidx-bucket-of-build
  (equal (fn-gidx-bucket group (fn-gidx-build articles))
         (fn-gidx-select group (fn-index-build articles)))
  :hints (("Goal" :in-theory (enable fn-gidx-build))))

(defun fn-gidx-range-numbers (buckets group low high)
  (declare (xargs :guard t))
  (fn-nntp-index-group-range-numbers
   (fn-gidx-bucket group buckets) group low high))

(defthm fn-gidx-select-listp
  (implies (fn-index-listp entries)
           (fn-index-listp (fn-gidx-select group entries))))

(defthm fn-gidx-built-bucket-listp
  (implies (fn-article-listp configured articles)
           (fn-index-listp
            (fn-gidx-bucket group (fn-gidx-build articles))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-index-build-listp)
                 (:instance fn-gidx-select-listp
                            (entries (fn-index-build articles))))
           :in-theory (disable fn-index-build-listp fn-gidx-select-listp))))

(defthm fn-gidx-raw-range-of-select
  (equal (fn-index-range-query-raw (fn-gidx-select group entries)
                                    group low high)
         (fn-index-range-query-raw entries group low high))
  :hints (("Goal" :induct (fn-gidx-select group entries)
           :in-theory (enable fn-index-range-query-raw
                              fn-index-entry-in-range-p))))

(defthm fn-gidx-query-range-of-select
  (implies (and (fn-index-listp entries)
                (stringp group) (natp low) (natp high))
           (equal (fn-index-query-range (fn-gidx-select group entries)
                                        group low high)
                  (fn-index-query-range entries group low high)))
  :hints (("Goal" :in-theory (enable fn-index-query-range))))

; Reuse the existing number projection and correctness theorem, rather than
; introducing another definition of NNTP local-number availability.
(defthm fn-gidx-range-of-build-is-flat-index-range
  (implies (and (fn-index-listp entries)
                (stringp group) (natp low) (natp high))
           (equal (fn-gidx-range-numbers (fn-gidx-build-entries entries)
                                         group low high)
                  (fn-nntp-index-group-range-numbers entries group low high)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-gidx-bucket-of-build-entries)
                 (:instance fn-gidx-query-range-of-select))
           :in-theory (e/d (fn-gidx-range-numbers
                            fn-nntp-index-group-range-numbers)
                           (fn-gidx-bucket-of-build-entries
                            fn-gidx-query-range-of-select)))))

(defthm fn-gidx-range-of-build-equals-archive-fold
  (implies (and (fn-article-listp configured articles)
                (stringp group) (natp low) (natp high))
           (equal (fn-gidx-range-numbers (fn-gidx-build articles)
                                          group low high)
                  (fn-nntp-group-range-numbers group low high articles)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-gidx-range-of-build-is-flat-index-range
                            (entries (fn-index-build articles)))
                 (:instance fn-nntp-index-group-range-numbers-equals-fold))
           :in-theory (disable fn-gidx-range-of-build-is-flat-index-range
                               fn-nntp-index-group-range-numbers-equals-fold))))

; Exact number of bucket headers visited by one lookup.  The range evaluator
; then visits at most the selected bucket's entries, independent of unrelated
; memberships.  No archive recognizer or article projection runs per query.
(defun fn-gidx-lookup-work (group buckets)
  (declare (xargs :guard t))
  (if (consp buckets)
      (if (equal group (fn-ag-car (fn-ag-car buckets)))
          1
        (1+ (fn-gidx-lookup-work group (cdr buckets))))
    0))

(defun fn-gidx-range-work (buckets group)
  (declare (xargs :guard t))
  (+ (fn-gidx-lookup-work group buckets)
     (len (fn-gidx-bucket group buckets))))

(defthm fn-gidx-lookup-work-at-most-bucket-count
  (<= (fn-gidx-lookup-work group buckets) (len buckets))
  :rule-classes :linear)
