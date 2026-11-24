; The seek starts with untouched reader fields. Decode both physical
; headers, then search the serialized body and restart directory.
(in-package "ACL2")
(include-book "range-stored-page-search-proof")
(include-book "range-stored-entry-bytes-proof")
(include-book "runs-stored-headers-proof")

(defmacro fn2-run-overview-page-offsets (level rows)
  `(fn2-run-restart-offsets-spec (fn2-run-overview-layout-at ,level) ,rows 0 *fn2-run-entries-base*))

(defmacro fn2-run-overview-directory-offset (level rows)
  `(+ *fn2-run-entries-base* (len (fn2-run-entries-octets (fn2-run-overview-layout-at ,level) ,rows))))

(defun-nx fn2-run-encoded-overview-page-p (rows level bvals cvals slot gen pk ps pg pool)
  (let* ((layout (fn2-run-overview-layout-at level)) (body (fn2-run-entries-octets layout rows))
         (dir (fn2-run-overview-directory-offset level rows)) (offsets (fn2-run-overview-page-offsets level rows))
         (size (* *fn2-run-restart-bytes* (len offsets))) (end (+ dir size)))
    (and (fn2-run-entries-layoutp layout rows)
         (fn2-run-page-headers-p bvals cvals dir (len rows) (len offsets) slot gen pk ps pg pool)
         (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (unsigned-byte-p 32 end)
         (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
         (equal (fn2-layout-range-code slot gen *fn2-run-entries-base* dir nil pk ps pg pool) :ok)
         (equal (fn2-run-read-bytes (len body) slot gen *fn2-run-entries-base* pk ps pg pool) body)
         (equal (fn2-layout-range-code slot gen dir end nil pk ps pg pool) :ok)
         (equal (fn2-run-read-bytes size slot gen dir pk ps pg pool) (fn2-run-directory-octets offsets)))))

(local
 (defthm fn2-run-encoded-page-has-headers
   (implies (fn2-run-encoded-overview-page-p rows level bvals cvals slot gen pk ps pg pool)
            (fn2-run-page-headers-p bvals cvals (fn2-run-overview-directory-offset level rows)
                (len rows) (len (fn2-run-overview-page-offsets level rows)) slot gen pk ps pg pool))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-encoded-overview-page-p))))))

(local
 (defthm fn2-run-encoded-body-with-header-counts
   (implies (and (fn2-run-encoded-overview-page-p rows level bvals cvals slot gen pk ps pg pool)
                 (natp rb) (<= (+ rb *fn2-run-reader-fields*) (fn2-fields-rows f))
                 (equal (fn2-run-directory rb f) (fn2-run-overview-directory-offset level rows))
                 (equal (fn2-run-page-entry-count rb f) (len rows))
                 (equal (fn2-run-page-restart-count rb f) (len (fn2-run-overview-page-offsets level rows))))
            (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-entry-bytes-supply-stored-rows (base (+ rb *fn2-run-reader-entry*))
                           (off *fn2-run-entries-base*) (end (fn2-run-overview-directory-offset level rows))))
            :in-theory (e/d (fn2-run-encoded-overview-page-p fn2-run-stored-overview-page-p)
                       (fn2-run-overview-page-rowsp fn2-run-page-headers-p fn2-run-entries-layoutp fn2-run-entries-octets
                        fn2-run-restart-offsets-spec fn2-run-directory-octets fn2-run-directory fn2-run-header-value
                        fn2-run-read-bytes fn2-layout-range-code fn2-poolp fn2-pool-wfp fn2-pool-base fn2-fields-rows len))))))

(defthmd fn2-run-encoded-page-prepares-search
  (let* ((read (fn2-run-read-header slot gen rb pk ps pg f pool)) (rf (mv-nth 1 read)))
    (implies (and (fn2-run-encoded-overview-page-p rows level bvals cvals slot gen pk ps pg pool)
                  (fn2-fieldsp f) (fn2-run-readerp rb f) (natp qbase) (< (1+ qbase) rb))
             (and (equal (car read) :ok) (fn2-fieldsp rf) (fn2-run-readerp rb rf)
                  (equal (fn2-run-page-restart-count rb rf) (len (fn2-run-overview-page-offsets level rows)))
                  (equal (fn2-overview-range-key-at qbase rf) (fn2-overview-range-key-at qbase f))
                  (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg rf pool))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-encoded-page-has-headers
                 (:instance fn2-run-reads-stored-page-headers (watch qbase)
                            (dir (fn2-run-overview-directory-offset level rows)) (count (len rows))
                            (nr (len (fn2-run-overview-page-offsets level rows))))
                 (:instance fn2-run-reads-stored-page-headers (watch (1+ qbase))
                            (dir (fn2-run-overview-directory-offset level rows)) (count (len rows))
                            (nr (len (fn2-run-overview-page-offsets level rows))))
                 (:instance fn2-run-encoded-body-with-header-counts
                            (f (mv-nth 1 (fn2-run-read-header slot gen rb pk ps pg f pool)))))
           :in-theory (e/d (fn2-overview-range-key-at fn2-run-readerp)
                   (fn2-run-encoded-overview-page-p fn2-run-stored-overview-page-p fn2-run-page-headers-p fn2-run-read-header fn2-run-entries-layoutp fn2-run-entries-octets
                    fn2-run-restart-offsets-spec fn2-run-directory-octets fn2-run-overview-page-rowsp
                    fn2-run-directory fn2-run-header-value fn2-run-read-bytes fn2-layout-range-code
                    fn2-poolp fn2-pool-wfp fn2-pool-base fn2-fieldsp fn2-fields-wfp fn2-fields-rows fn2-fields-value len nth)))))

(defthmd fn2-run-searches-encoded-overview-page
  (let* ((query (fn2-overview-range-key-at qbase f)) (read (fn2-run-read-header slot gen rb pk ps pg f pool))
         (rf (mv-nth 1 read)) (nr (fn2-run-page-restart-count rb rf))
         (seek (fn2-run-seek 3 level fuel 0 nr 0 0 qbase rb slot gen pk ps pg qk qs qg rf pool)))
    (implies (and (fn2-run-encoded-overview-page-p rows level bvals cvals slot gen pk ps pg pool)
                  (consp rows) (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                  (fn2-fieldsp f) (fn2-run-readerp rb f) (natp qbase) (< (1+ qbase) rb)
                  (natp fuel) (< (+ (integer-length (len (fn2-run-overview-page-offsets level rows)))
                                   *fn2-run-restart-interval* 1) fuel))
             (and (equal (car read) :ok)
                  (equal (list (car seek) (mv-nth 3 seek)) (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query 0))
                  (equal (mv-nth 4 seek) (fn2-run-overview-lower-bound-offset level rows query *fn2-run-entries-base*))
                  (equal (fn2-overview-range-key-at qbase (mv-nth 5 seek)) query))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-encoded-page-prepares-search
                 (:instance fn2-run-stored-overview-page-lower-bound (f (mv-nth 1 (fn2-run-read-header slot gen rb pk ps pg f pool)))))
           :in-theory (e/d (fn2-run-readerp)
                    (fn2-run-encoded-overview-page-p fn2-run-stored-overview-page-p fn2-run-sorted-spec
                     fn2-run-read-header fn2-run-seek fn2-run-header-value fn2-run-directory fn2-overview-range-key-at
                     fn2-run-lower-bound-spec fn2-run-overview-lower-bound-offset fn2-run-restart-offsets-spec
                     fn2-fieldsp fn2-fields-wfp fn2-fields-rows len integer-length)))))
