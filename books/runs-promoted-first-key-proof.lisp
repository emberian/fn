; The child's first physical row supplies the two key fields promoted to
; its parent, at leaf and index levels alike.
(in-package "ACL2")
(include-book "range-encoded-page-search-proof")
(include-book "runs-child-reference-values-proof")

(local
 (defthm fn2-run-first-physical-row
   (implies (and (consp rows) (fn2-run-overview-page-rowsp level rows ib slot gen off end pk ps pg f pool))
            (fn2-run-overview-row-atp level (car rows) ib slot gen off end pk ps pg f pool))
   :rule-classes nil
   :hints (("Goal" :expand (fn2-run-overview-page-rowsp level rows ib slot gen off end pk ps pg f pool)
            :in-theory (union-theories (theory 'minimal-theory) '(atom))))))

(local
 (defthm fn2-run-encoded-page-first-row
   (implies (and (consp rows) (fn2-run-encoded-overview-page-p rows level bvals cvals slot gen pk ps pg pool)
                 (natp ib) (<= (+ ib (len (fn2-run-overview-layout-at level))) (fn2-fields-rows f)))
            (fn2-run-overview-row-atp level (car rows) ib slot gen *fn2-run-entries-base*
                       (fn2-run-overview-directory-offset level rows) pk ps pg f pool))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-entry-bytes-supply-stored-rows (base ib) (off *fn2-run-entries-base*)
                              (end (fn2-run-overview-directory-offset level rows)))
                         (:instance fn2-run-first-physical-row (off *fn2-run-entries-base*) (end (fn2-run-overview-directory-offset level rows))))
            :in-theory (e/d (fn2-run-encoded-overview-page-p)
                        (fn2-run-overview-row-atp fn2-run-page-headers-p fn2-run-overview-page-rowsp fn2-run-read-bytes fn2-run-entries-layoutp
                         fn2-run-entries-octets fn2-run-restart-offsets-spec fn2-run-directory-octets fn2-fields-rows fn2-poolp fn2-pool-wfp
                         fn2-layout-range-code fn2-pool-base len))))))

(defthmd fn2-run-encoded-child-supplies-first-key
  (let* ((end (fn2-run-overview-directory-offset level rows))
         (read (fn2-run-layout-decode 3 level ib slot gen *fn2-run-entries-base* end pk ps pg f pool)))
    (implies (and (consp rows) (fn2-run-encoded-overview-page-p rows level bvals cvals slot gen pk ps pg pool)
                  (natp ib) (<= (+ ib (len (fn2-run-overview-layout-at level))) (fn2-fields-rows f)))
             (and (equal (car read) :ok)
                  (equal (fn2-overview-range-key-at ib (mv-nth 2 read))
                         (list (nth 0 (car rows)) (nth 1 (car rows)))))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-encoded-page-first-row
                 (:instance fn2-run-overview-page-row-id (j 0) (base ib) (row (car rows)) (off *fn2-run-entries-base*)
                            (end (fn2-run-overview-directory-offset level rows)))
                 (:instance fn2-run-overview-page-row-id (j 1) (base ib) (row (car rows)) (off *fn2-run-entries-base*)
                            (end (fn2-run-overview-directory-offset level rows)))
                 (:instance fn2-run-overview-page-row-boundary (base ib) (row (car rows)) (off *fn2-run-entries-base*)
                            (end (fn2-run-overview-directory-offset level rows))))
           :in-theory (e/d (fn2-run-overview-row-atp fn2-overview-range-key-at)
                          (fn2-run-encoded-overview-page-p fn2-run-page-headers-p fn2-run-entries-layoutp fn2-run-values-layoutp fn2-layout-octets
                           fn2-run-entries-octets fn2-run-directory-octets fn2-run-overview-page-rowsp fn2-run-overview-next-offset
                           fn2-run-restart-offsets-spec fn2-run-layout-decode fn2-run-read-bytes fn2-fields-value
                           fn2-pool-base fn2-poolp fn2-pool-wfp fn2-layout-range-code fn2-fields-rows len nth)))))

(defmacro fn2-run-promotion-input (level w ib end hrow hslot hgen writers f pool ds)
  `(let ((read (fn2-run-layout-decode 3 ,level ,ib (fn2-run-writers-slot ,w ,writers)
                       (fn2-run-writers-gen ,w ,writers) *fn2-run-entries-base* ,end 9 0 1 ,f ,pool)))
     (fn2-run-child-ref ,w ,level (+ ,ib 2) (+ ,ib 2 *fn2-format-ref-num-fields*) ,hrow ,hslot ,hgen
                        9 0 1 ,writers (mv-nth 2 read) ,pool ,ds)))

(defthmd fn2-run-encoded-child-supplies-promotion-input
  (let* ((end (fn2-run-writers-cursor w writers)) (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
         (read (fn2-run-layout-decode 3 level ib slot gen *fn2-run-entries-base* end 9 0 1 f pool))
         (ref (fn2-run-promotion-input level w ib end hrow hslot hgen writers f pool ds)) (head (car rows)))
    (implies (and (consp rows) (fn2-run-encoded-overview-page-p rows level bvals cvals slot gen 9 0 1 pool)
                  (equal end (fn2-run-overview-directory-offset level rows))
                  (fn2-fieldsp f) (fn2-fields-wfp f)
                  (fn2-run-child-reference-room-p w level ib hrow hslot hgen writers f pool ds))
             (and (equal (car read) :ok) (equal (car ref) :ok)
                  (equal (fn2-run-unload-values *fn2-overview-index* ib (mv-nth 1 ref) (mv-nth 2 ref))
                         (fn2-run-overview-child-row (list (nth 0 head) (nth 1 head)) w hrow writers ds)))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-encoded-child-supplies-first-key (pk 9) (ps 0) (pg 1)
                            (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers)))
                 (:instance fn2-run-child-reference-records-sealed-writer
                      (f (mv-nth 2 (fn2-run-layout-decode 3 level ib (fn2-run-writers-slot w writers) (fn2-run-writers-gen w writers)
                                         *fn2-run-entries-base* (fn2-run-writers-cursor w writers) 9 0 1 f pool)))))
           :in-theory (e/d (fn2-run-child-reference-room-p)
                         (fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-rows fn2-run-writers-slot fn2-run-writers-gen
                          fn2-run-writers-cursor fn2-page-parent-octets fn2-digest-list fn2-run-load-bytes fn2-pool-base
                          fn2-layout-range-code fn2-digest-rowp fn2-fieldsp fn2-fields-wfp fn2-fields-rows fn2-run-child-ref
                          fn2-run-unload-values fn2-run-overview-child-row fn2-run-encoded-overview-page-p
                          fn2-run-layout-decode fn2-overview-range-key-at fn2-run-entries-octets len nth unsigned-byte-p)))))
