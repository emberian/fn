; Heading a padded run page establishes both readable wire headers and
; preserves the entry and restart regions following them.
(in-package "ACL2")
(include-book "runs-written-header-proof")

(defun-nx fn2-run-heading-page-p (w writers f pool)
  (and (fn2-run-writersp writers) (fn2-run-writers-wfp writers) (natp w) (< w (fn2-run-writers-rows writers))
       (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-heading*)
       (<= (+ (fn2-run-writers-fields w writers) *fn2-run-c-header-fields*) (fn2-fields-rows f))
       (< (fn2-run-writers-page-kind w writers) (len (caddr *fn2-format-page-kind*)))
       (unsigned-byte-p 60 (fn2-run-payload-length w writers))
       (fn2-poolp pool) (fn2-pool-wfp pool)
       (fn2-run-filled-page-p (fn2-run-writers-slot w writers) (fn2-run-writers-gen w writers)
             (fn2-run-writers-okind w writers) (fn2-run-writers-oslot w writers) (fn2-run-writers-ogen w writers) pool)))

(local (in-theory (disable fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-rows fn2-run-writers-phase
         fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen
         fn2-run-writers-fields fn2-run-writers-history fn2-run-writers-incarnation fn2-run-writers-unit
         fn2-run-writers-epoch fn2-run-writers-counter fn2-run-writers-page-kind fn2-run-writers-schema
         fn2-run-writers-schema-version fn2-run-writers-run fn2-run-writers-level fn2-run-writers-ordinal
         fn2-run-writers-entries fn2-run-writers-restarts fn2-run-writers-set-phase fn2-fields-rows
         fn2-run-payload-length fn2-run-writable-header-p fn2-run-stored-header-p fn2-poolp fn2-pool-wfp
         fn2-pool-base fn2-layout-range-code fn2-run-load-bytes fn2-run-read-bytes fn2-layout-octets
         fn2-run-head fn2-run-head-b unsigned-byte-p fn2-run-header-values-valid-p fn-b3-octet-listp)))

(defthmd fn2-run-heading-values-are-valid
   (implies (fn2-run-heading-page-p w writers f pool)
            (and (fn2-run-header-values-valid-p *fn2-format-page-header* (fn2-run-outer-header-values w writers))
                 (fn2-run-header-values-valid-p *fn2-run-page-header* (fn2-run-inner-header-values w writers))))
   :hints (("Goal" :do-not '(preprocess) :in-theory (enable fn2-run-header-values-valid-p fn2-run-header-field-valid-p unsigned-byte-p))))

(local
 (defthm fn2-run-heading-writes-readable-outer
   (let* ((slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
          (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
          (base (fn2-run-writers-fields w writers)) (outer (fn2-run-head-b w base writers f pool)) (bp (mv-nth 2 outer))
          (vals (fn2-run-outer-header-values w writers)))
     (implies (fn2-run-heading-page-p w writers f pool)
              (and (equal (car outer) :ok) (fn2-run-filled-page-p slot gen pk ps pg bp)
                   (fn2-poolp bp) (fn2-pool-wfp bp)
                   (fn2-run-stored-header-p *fn2-format-page-header* vals slot gen 0 *fn2-run-header-area* pk ps pg bp)
                   (equal bp (mv-nth 1 (fn2-run-load-bytes (fn2-layout-octets *fn2-format-page-header* vals)
                                                         slot gen 0 pk ps pg pool))))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-heading-values-are-valid
                  (:instance fn2-run-writer-stores-outer-header (base (fn2-run-writers-fields w writers)))
                  (:instance fn2-run-filled-page-stores-typed-header (layout *fn2-format-page-header*)
                       (vals (fn2-run-outer-header-values w writers)) (off 0) (cap *fn2-run-header-area*)
                       (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
                       (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))))
            :in-theory (e/d (unsigned-byte-p) (fn2-run-heading-values-are-valid))))))

(defthmd fn2-run-heading-writes-readable-headers
  (let* ((slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
         (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
         (write (fn2-run-head w writers restarts f pool)) (after (mv-nth 3 write)))
    (implies (fn2-run-heading-page-p w writers f pool)
             (and (equal (car write) :ok)
                  (equal (mv-nth 1 write) (fn2-run-writers-set-phase w *fn2-run-writer-phase-sealing* writers))
                  (fn2-run-filled-page-p slot gen pk ps pg after)
                  (fn2-poolp after) (fn2-pool-wfp after)
                  (equal after
                         (mv-nth 1 (fn2-run-load-bytes (fn2-layout-octets *fn2-run-page-header* (fn2-run-inner-header-values w writers))
                                      slot gen *fn2-run-header-area* pk ps pg
                                      (mv-nth 1 (fn2-run-load-bytes (fn2-layout-octets *fn2-format-page-header* (fn2-run-outer-header-values w writers))
                                                    slot gen 0 pk ps pg pool)))))
                  (fn2-run-stored-header-p *fn2-format-page-header* (fn2-run-outer-header-values w writers)
                                           slot gen 0 *fn2-run-header-area* pk ps pg after)
                  (fn2-run-stored-header-p *fn2-run-page-header* (fn2-run-inner-header-values w writers)
                                           slot gen *fn2-run-header-area* *fn2-run-entries-base* pk ps pg after))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-heading-values-are-valid fn2-run-heading-writes-readable-outer
                 fn2-run-writer-stores-inner-header
                 (:instance fn2-run-typed-header-has-canonical-encoding (layout *fn2-run-page-header*) (vals (fn2-run-inner-header-values w writers)))
                 (:instance fn2-run-filled-page-stores-typed-header (layout *fn2-run-page-header*)
                      (vals (fn2-run-inner-header-values w writers)) (off *fn2-run-header-area*) (cap *fn2-run-entries-base*)
                      (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
                      (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
                      (pool (mv-nth 2 (fn2-run-head-b w (fn2-run-writers-fields w writers) writers f pool))))
                 (:instance fn2-run-later-write-preserves-stored-header (layout *fn2-format-page-header*)
                      (vals (fn2-run-outer-header-values w writers)) (off 0) (cap *fn2-run-header-area*) (at *fn2-run-header-area*)
                      (bytes (fn2-layout-octets *fn2-run-page-header* (fn2-run-inner-header-values w writers)))
                      (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
                      (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
                      (pool (mv-nth 2 (fn2-run-head-b w (fn2-run-writers-fields w writers) writers f pool)))))
           :in-theory (e/d (unsigned-byte-p) (fn2-run-heading-values-are-valid fn2-run-header-scalars-p fn2-run-values-layoutp)))))
