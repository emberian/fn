; Recover each overview row and its readable suffix from the contiguous
; entry bytes written before the restart directory.
(in-package "ACL2")
(include-book "range-page-scan-state-proof")
(include-book "runs-restart-lookup-proof")

(local (defthm fn2-run-entry-span-length (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn2-run-entry-bytes-of-cons
   (let* ((first (fn2-layout-octets layout row)) (rest (fn2-run-entries-octets layout rows))
          (bytes (fn2-run-entries-octets layout (cons row rows))))
     (implies (and (natp off)
                   (equal (fn2-run-read-bytes (len bytes) slot gen off pk ps pg pool) bytes))
              (and (equal (len bytes) (+ (len first) (len rest)))
                   (equal (fn2-run-read-bytes (len first) slot gen off pk ps pg pool) first)
                   (equal (fn2-run-read-bytes (len rest) slot gen (+ off (len first)) pk ps pg pool) rest))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-read-stored-segments (at off)
                             (left (fn2-layout-octets layout row)) (right (fn2-run-entries-octets layout rows))))
            :expand ((fn2-run-entries-octets layout (cons row rows)))
            :in-theory (disable fn2-run-read-bytes fn2-layout-octets fn2-run-entries-octets binary-append)))))

(local
 (defthm fn2-run-readable-tail-of-entries
   (implies (and (natp at) (natp next) (natp end) (<= at next) (<= next end)
                 (eq (fn2-layout-range-code slot gen at end nil pk ps pg pool) :ok))
            (eq (fn2-layout-range-code slot gen next end nil pk ps pg pool) :ok))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-layout-range-code)
                     (fn2-pool-readable-code fn2-pool-slot-fill fn2-pool-slot-base fn2-pool-capacity-bytes))))))

(defthmd fn2-run-entry-bytes-supply-stored-rows
  (let* ((layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*))
         (body (fn2-run-entries-octets layout rows)))
    (implies (and (fn2-run-entries-layoutp layout rows) (equal end (+ off (len body)))
                  (unsigned-byte-p 32 off) (unsigned-byte-p 32 end) (natp base)
                  (<= (+ base (len layout)) (fn2-fields-rows f))
                  (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                  (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
                  (eq (fn2-layout-range-code slot gen off end nil pk ps pg pool) :ok)
                  (equal (fn2-run-read-bytes (len body) slot gen off pk ps pg pool) body))
             (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f pool)))
  :hints (("Goal" :induct (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f pool)
           :do-not '(preprocess)
           :expand ((fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f pool))
           :in-theory (e/d ((:induction fn2-run-overview-page-rowsp) fn2-run-overview-next-offset fn2-run-overview-row-atp)
                       (fn2-run-values-layoutp fn2-layout-octets fn2-run-read-bytes fn2-layout-range-code fn2-fields-rows
                        fn2-poolp fn2-pool-wfp fn2-pool-base (:definition fn2-run-overview-page-rowsp) fn2-run-entries-octets)))
          (and (equal (access clause-id id :pool-lst) '(1)) (equal (len (access clause-id id :case-lst)) 1)
               (equal (access clause-id id :primes) 0)
               '(:use ((:instance fn2-run-entry-bytes-of-cons (layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*))
                                    (row (car rows)) (rows (cdr rows)))
                       (:instance fn2-run-readable-tail-of-entries (at off) (next (fn2-run-overview-next-offset level (car rows) off))))
                 :expand ((fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f pool)
                          (:free (layout) (fn2-run-entries-layoutp layout rows))
                          (:free (layout) (fn2-run-entries-octets layout rows)))))))
