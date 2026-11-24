; A run heading write turns the closed entry and restart regions into a
; page that the physical lower-bound reader accepts.
(in-package "ACL2")
(include-book "runs-writer-stored-headers-proof")
(include-book "runs-restart-directory-count-proof")
(include-book "range-encoded-page-search-proof")

(local
 (defthm fn2-run-two-header-writes-preserve-body
   (let* ((bp (mv-nth 1 (fn2-run-load-bytes outer slot gen 0 pk ps pg pool)))
          (after (mv-nth 1 (fn2-run-load-bytes inner slot gen *fn2-run-header-area* pk ps pg bp))))
     (implies (and (fn2-run-filled-page-p slot gen pk ps pg pool)
                   (fn-b3-octet-listp outer) (<= (len outer) *fn2-run-header-area*)
                   (fn-b3-octet-listp inner) (<= (+ *fn2-run-header-area* (len inner)) *fn2-run-entries-base*)
                   (natp at) (natp n) (<= *fn2-run-entries-base* at) (<= (+ at n) *fn2-run-page-size*))
              (equal (fn2-run-read-bytes n slot gen at pk ps pg after)
                     (fn2-run-read-bytes n slot gen at pk ps pg pool))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-overwrite-filled-page (bytes outer) (off 0) (i 0))
                         (:instance fn2-run-header-overwrite-retains-span (bytes outer) (off 0))
                         (:instance fn2-run-header-overwrite-retains-span (bytes inner) (off *fn2-run-header-area*)
                           (pool (mv-nth 1 (fn2-run-load-bytes outer slot gen 0 pk ps pg pool)))))
            :in-theory (disable fn2-run-read-bytes fn2-run-load-bytes fn2-layout-range-code fn-b3-octet-listp fn2-pool-base)))))

(local (in-theory (disable fn2-run-head fn2-run-heading-page-p fn2-layout-octets fn2-run-load-bytes fn2-run-read-bytes
       fn2-layout-range-code fn-b3-octet-listp fn2-pool-base fn2-poolp fn2-pool-wfp fn2-run-stored-header-p
       fn2-run-writers-level fn2-run-writers-schema fn2-run-writers-schema-version fn2-run-writers-ordinal
       fn2-run-writers-run fn2-run-writers-history fn2-run-writers-incarnation fn2-run-writers-epoch
       fn2-run-writers-unit fn2-run-writers-counter fn2-run-writers-page-kind fn2-run-payload-length
       fn2-run-writers-entries fn2-run-writers-restarts fn2-run-writers-slot fn2-run-writers-gen
       fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-set-phase
       fn2-run-header-values-valid-p fn2-run-header-scalars-p fn2-run-values-layoutp)))

(defthmd fn2-run-heading-keeps-page-span
  (let ((slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
        (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
        (after (mv-nth 3 (fn2-run-head w writers restarts f pool))))
    (implies (and (fn2-run-heading-page-p w writers f pool)
                  (natp at) (natp n) (<= *fn2-run-entries-base* at) (<= (+ at n) *fn2-run-page-size*))
             (equal (fn2-run-read-bytes n slot gen at pk ps pg after)
                    (fn2-run-read-bytes n slot gen at pk ps pg pool))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-heading-writes-readable-headers fn2-run-heading-values-are-valid
                 (:instance fn2-run-typed-header-has-canonical-encoding (layout *fn2-format-page-header*) (vals (fn2-run-outer-header-values w writers)))
                 (:instance fn2-run-typed-header-has-canonical-encoding (layout *fn2-run-page-header*) (vals (fn2-run-inner-header-values w writers)))
                 (:instance fn2-run-two-header-writes-preserve-body
                      (outer (fn2-layout-octets *fn2-format-page-header* (fn2-run-outer-header-values w writers)))
                      (inner (fn2-layout-octets *fn2-run-page-header* (fn2-run-inner-header-values w writers)))
                      (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
                      (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))))
           :in-theory (e/d (fn2-run-heading-page-p) (fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-rows
                        fn2-run-writers-phase fn2-run-writers-fields fn2-fields-rows unsigned-byte-p)))))

(defun-nx fn2-run-closed-overview-contents-p (rows w writers pool)
  (let* ((level (fn2-run-writers-level w writers)) (layout (fn2-run-overview-layout-at level))
         (body (fn2-run-entries-octets layout rows)) (dir (+ *fn2-run-entries-base* (len body)))
         (offsets (fn2-run-overview-page-offsets level rows)) (size (* *fn2-run-restart-bytes* (len offsets)))
         (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
         (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers)))
    (and (fn2-run-entries-layoutp layout rows) (equal (fn2-run-writers-entries w writers) (len rows))
         (equal (fn2-run-writers-restarts w writers) (len offsets)) (equal (fn2-run-writers-cursor w writers) dir)
         (<= (+ dir size) *fn2-run-page-size*)
         (equal (fn2-run-read-bytes (len body) slot gen *fn2-run-entries-base* pk ps pg pool) body)
         (equal (fn2-run-read-bytes size slot gen dir pk ps pg pool) (fn2-run-directory-octets offsets)))))

(local
 (defthm fn2-run-headed-page-metadata
   (let* ((level (fn2-run-writers-level w writers)) (dir (fn2-run-overview-directory-offset level rows))
          (count (len rows)) (nr (len (fn2-run-overview-page-offsets level rows)))
          (bvals (fn2-run-outer-header-values w writers)) (cvals (fn2-run-inner-header-values w writers)))
     (implies (fn2-run-closed-overview-contents-p rows w writers pool)
              (and (equal (nth *fn2-format-page-header-field-magic* bvals) *fn2-format-page-magic*)
                   (equal (nth *fn2-format-page-header-field-header-length* bvals) *fn2-run-header-area*)
                   (equal (nth *fn2-format-page-header-field-payload-length* bvals)
                          (- (+ dir (* *fn2-run-restart-bytes* nr)) *fn2-run-header-area*))
                   (equal (nth *fn2-run-page-header-field-entries* cvals) count)
                   (equal (nth *fn2-run-page-header-field-restarts* cvals) nr)
                   (equal (nth *fn2-run-page-header-field-restart-interval* cvals) *fn2-run-restart-interval*)
                   (equal nr (ceiling count *fn2-run-restart-interval*)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-directory-count-matches-entries
                              (layout (fn2-run-overview-layout-at (fn2-run-writers-level w writers))) (entries rows) (off *fn2-run-entries-base*)))
            :in-theory (e/d (fn2-run-payload-length)
                          (fn2-run-writers-cursor fn2-run-entries-layoutp fn2-run-entries-octets
                           fn2-run-restart-offsets-spec fn2-run-directory-octets ceiling ceiling-to-floor len))))))

(local
 (defthm fn2-run-heading-address-widths
   (implies (fn2-run-heading-page-p w writers f pool)
            (and (unsigned-byte-p 32 (fn2-run-writers-slot w writers)) (unsigned-byte-p 60 (fn2-run-writers-gen w writers))))
   :hints (("Goal" :in-theory (e/d (fn2-run-heading-page-p) (fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-rows
                      fn2-run-writers-phase fn2-run-writers-fields fn2-fields-rows))))))

(local
 (defthm fn2-run-heading-decodable
   (let* ((slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
          (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
          (write (fn2-run-head w writers restarts f pool)) (after (mv-nth 3 write)))
     (implies (fn2-run-heading-page-p w writers f pool)
              (and (equal (car write) :ok) (fn2-run-filled-page-p slot gen pk ps pg after) (fn2-poolp after) (fn2-pool-wfp after)
                   (fn2-run-stored-header-p *fn2-format-page-header* (fn2-run-outer-header-values w writers)
                                            slot gen 0 *fn2-run-header-area* pk ps pg after)
                   (fn2-run-stored-header-p *fn2-run-page-header* (fn2-run-inner-header-values w writers)
                                            slot gen *fn2-run-header-area* *fn2-run-entries-base* pk ps pg after))))
   :rule-classes nil
   :hints (("Goal" :use fn2-run-heading-writes-readable-headers :in-theory (theory 'minimal-theory)))))

(defthmd fn2-run-writer-produces-encoded-overview-page
  (let* ((level (fn2-run-writers-level w writers)) (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
         (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
         (write (fn2-run-head w writers restarts f pool)) (after (mv-nth 3 write)))
    (implies (and (fn2-run-heading-page-p w writers f pool) (fn2-run-closed-overview-contents-p rows w writers pool))
             (and (equal (car write) :ok)
                  (fn2-run-encoded-overview-page-p rows level (fn2-run-outer-header-values w writers) (fn2-run-inner-header-values w writers)
                                                   slot gen pk ps pg after))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-heading-decodable fn2-run-heading-address-widths fn2-run-headed-page-metadata
                 (:instance fn2-run-heading-keeps-page-span (at *fn2-run-entries-base*)
                      (n (len (fn2-run-entries-octets (fn2-run-overview-layout-at (fn2-run-writers-level w writers)) rows))))
                 (:instance fn2-run-heading-keeps-page-span (at (fn2-run-overview-directory-offset (fn2-run-writers-level w writers) rows))
                      (n (* *fn2-run-restart-bytes* (len (fn2-run-overview-page-offsets (fn2-run-writers-level w writers) rows)))))
                 (:instance fn2-run-filled-page-allows-subrange (start *fn2-run-entries-base*) (writep nil)
                      (end (fn2-run-overview-directory-offset (fn2-run-writers-level w writers) rows))
                      (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
                      (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
                      (pool (mv-nth 3 (fn2-run-head w writers restarts f pool))))
                 (:instance fn2-run-filled-page-allows-subrange (start (fn2-run-overview-directory-offset (fn2-run-writers-level w writers) rows)) (writep nil)
                      (end (+ (fn2-run-overview-directory-offset (fn2-run-writers-level w writers) rows)
                              (* *fn2-run-restart-bytes* (len (fn2-run-overview-page-offsets (fn2-run-writers-level w writers) rows)))))
                      (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
                      (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
                      (pool (mv-nth 3 (fn2-run-head w writers restarts f pool)))))
           :in-theory (e/d (fn2-run-closed-overview-contents-p fn2-run-encoded-overview-page-p fn2-run-page-headers-p)
                         (fn2-run-heading-address-widths fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-rows fn2-run-writers-fields fn2-run-writers-phase fn2-fields-rows
                          fn2-run-writers-cursor fn2-run-entries-layoutp fn2-run-entries-octets
                          fn2-run-restart-offsets-spec fn2-run-directory-octets ceiling ceiling-to-floor len)))))
