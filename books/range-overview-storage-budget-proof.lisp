; Each admitted source fits both its raw line workspace and the overlay
; arena, including the next row after any loaded prefix.
(in-package "ACL2")
(include-book "runs-overview-source-proof")
(include-book "runs-page-row-budget-proof")

(defun fn2-range-line-bytes (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) 0 (+ (len (nth 4 (car rows))) (fn2-range-line-bytes (cdr rows)))))

(local
 (defthm fn2-range-byte-count-of-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(defthmd fn2-range-source-storage-bounds
  (implies (fn2-run-entries-layoutp *fn2-overview-entry* rows)
           (and (<= (fn2-range-line-bytes rows) (* 1024 (len rows)))
                (<= (len (fn2-run-entries-octets *fn2-overview-entry* rows)) (* 1069 (len rows)))))
  :hints (("Goal" :induct (len rows)
           :expand ((fn2-range-line-bytes rows) (fn2-run-entries-layoutp *fn2-overview-entry* rows)
                    (fn2-run-entries-octets *fn2-overview-entry* rows))
           :in-theory (disable fn2-run-values-layoutp fn2-layout-octets binary-append nth))
          ("Subgoal *1/1" :use ((:instance fn2-run-admitted-line-fits-source (row (car rows)))
                      (:instance fn2-run-overview-admission-fits-decoder (row (car rows)) (layout *fn2-overview-entry*))))))

(defthm fn2-range-next-row-fits-both-workspaces
  (let* ((at (fn2-range-line-bytes rows)) (off (len (fn2-run-entries-octets *fn2-overview-entry* rows)))
         (next-at (+ at (len (nth 4 row)))) (end (+ off (len (fn2-layout-octets *fn2-overview-entry* row)))))
    (implies (and (< (len rows) 48) (fn2-run-entries-layoutp *fn2-overview-entry* rows)
                  (fn2-run-values-layoutp *fn2-overview-entry* row))
             (and (unsigned-byte-p 32 at) (unsigned-byte-p 32 off)
                  (unsigned-byte-p 32 next-at) (<= next-at 49152)
                  (unsigned-byte-p 32 end) (<= end 51312) (<= next-at 65536) (<= end 65536))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-source-storage-bounds fn2-run-admitted-line-fits-source
                 (:instance fn2-run-overview-admission-fits-decoder (layout *fn2-overview-entry*)))
           :in-theory (disable fn2-run-entries-layoutp fn2-run-values-layoutp fn2-range-line-bytes
                       fn2-run-entries-octets fn2-layout-octets nth len))))
