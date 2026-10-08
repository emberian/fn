; The served history sync reads only the in-memory suffix. The disk prefix
; belongs to startup; an inconsistent count faults before reading any row.
(in-package "ACL2")
(include-book "history-columns-relation")

(defun fn-hist-served-base (files)
  (declare (xargs :guard t))
  (let ((field (fn-sf-records-field files)))
    (if (fn-sfr-basedp field) (fn-hrs-h-n (fn-sfr-handle field)) 0)))

(defun fn-hist-served-at (i files)
  (declare (xargs :guard (natp i)))
  (let ((field (fn-sf-records-field files)))
    (if (fn-sfr-basedp field)
        (fn-sl-nth (nfix (- i (fn-hist-served-base files))) (fn-sfr-suffix field))
      (fn-sl-nth i field))))

(defthm fn-hist-served-at-is-records-nth
  (implies (and (natp i) (<= (fn-hist-served-base files) i))
           (equal (fn-hist-served-at i files) (fn-sf-records-nth i files)))
  :hints (("Goal"
           :use ((:instance fn-sfr-nth-is-nth (f (fn-sf-records-field files))))
           :in-theory (e/d (fn-hist-served-at fn-hist-served-base
                            fn-sf-records-nth fn-sf-records fn-sfr-nth fn-hrs-h-n)
                           (fn-sfr-nth-is-nth fn-sfr-list fn-sl-nth)))))

(defun fn-hist-served-sync-aux (k n files fn-hist)
  (declare (xargs :stobjs fn-hist :guard (and (natp k) (natp n))
                  :measure (nfix (- (nfix n) (nfix k)))))
  (if (and (natp k) (natp n) (< k n))
      (let ((fn-hist (fn-hist-append (fn-hist-served-at k files) fn-hist)))
        (fn-hist-served-sync-aux (1+ k) n files fn-hist))
    fn-hist))

(defthm fn-hist-served-sync-aux-is-sync-aux
  (implies (<= (fn-hist-served-base files) (nfix k))
           (equal (fn-hist-served-sync-aux k n files fn-hist)
                  (fn-hist-sync-aux k n files fn-hist)))
  :hints (("Goal" :induct (fn-hist-served-sync-aux k n files fn-hist)
           :in-theory (e/d (fn-hist-sync-aux fn-hist-served-sync-aux)
                           (fn-hist-served-at fn-hist-served-base)))))

(defun fn-hist-served-sync (files fn-hist)
  (declare (xargs :stobjs fn-hist :guard t))
  (if (< (fn-hist-count fn-hist) (fn-hist-served-base files))
      (prog2$ (er hard? 'fn-hist-served-sync "History disk prefix not loaded.") fn-hist)
    (fn-hist-served-sync-aux (fn-hist-count fn-hist) (fn-sf-records-count files)
                             files fn-hist)))

(defthm fn-hist-served-sync-is-sync
  (implies (<= (fn-hist-served-base files) (fn-hist-count fn-hist))
           (equal (fn-hist-served-sync files fn-hist)
                  (fn-hist-sync files fn-hist)))
  :hints (("Goal" :in-theory (enable fn-hist-served-sync fn-hist-sync))))

(in-theory (disable fn-hist-served-at fn-hist-served-base
                    fn-hist-served-sync-aux fn-hist-served-sync))

(defthm fn-hist-served-base-is-within-record-count
  (<= (fn-hist-served-base files) (fn-sf-records-count files))
  :rule-classes :linear
  :hints (("Goal"
           :use ((:instance fn-sfr-count-is-len (f (fn-sf-records-field files))))
           :in-theory (e/d (fn-hist-served-base fn-sf-records-count
                            fn-sf-records fn-sfr-count fn-hrs-h-n)
                           (fn-sfr-count-is-len fn-sfr-list)))))

(defthm fn-hist-served-sync-aux-count-monotone
  (<= (fn-hist-count hist)
      (fn-hist-count (fn-hist-served-sync-aux k n files hist)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-hist-served-sync-aux k n files hist)
           :in-theory (enable fn-hist-served-sync-aux))))

(defthm fn-hist-served-sync-count-monotone
  (<= (fn-hist-count hist) (fn-hist-count (fn-hist-served-sync files hist)))
  :rule-classes :linear
  :hints (("Goal"
           :use ((:instance fn-hist-served-sync-aux-count-monotone
                            (k (fn-hist-count hist))
                            (n (fn-sf-records-count files))))
           :in-theory (e/d (fn-hist-served-sync)
                           (fn-hist-served-sync-aux-is-sync-aux
                            fn-hist-served-sync-is-sync)))))
