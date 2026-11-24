; The two header encoders receive their values from the current writer row.
(in-package "ACL2")
(include-book "runs-format-page-header-encode-proof")
(include-book "runs-data-header-encode-proof")

(defmacro fn2-run-outer-header-values (w writer)
  `(list *fn2-format-page-magic* *fn2-format-version* (fn2-run-writers-page-kind ,w ,writer)
         (fn2-run-writers-history ,w ,writer) (fn2-run-writers-incarnation ,w ,writer)
         (fn2-run-writers-unit ,w ,writer) (fn2-run-writers-epoch ,w ,writer)
         (fn2-run-writers-counter ,w ,writer) *fn2-run-header-area* (fn2-run-payload-length ,w ,writer)))

(defmacro fn2-run-inner-header-values (w writer)
  `(list (fn2-run-writers-schema ,w ,writer) (fn2-run-writers-schema-version ,w ,writer)
         (fn2-run-writers-run ,w ,writer) (fn2-run-writers-level ,w ,writer) (fn2-run-writers-ordinal ,w ,writer)
         (fn2-run-writers-entries ,w ,writer) (fn2-run-writers-restarts ,w ,writer) *fn2-run-restart-interval*))

(defun-nx fn2-run-writable-header-p (layout values slot gen off cap pk ps pg pool)
  (let ((bytes (fn2-layout-octets layout values)))
    (and (natp off) (natp (fn2-pool-base slot pool)) (fn-b3-octet-listp bytes)
         (<= (+ off (len bytes)) cap)
         (equal (fn2-layout-range-code slot gen off cap t pk ps pg pool) :ok))))

(local (defthm fn2-run-proper-header-bytes
  (implies (fn-b3-octet-listp xs) (equal (true-list-fix xs) xs))))

(local
 (defthm fn2-run-writable-header-can-load
   (let ((bytes (fn2-layout-octets layout vals)))
     (implies (fn2-run-writable-header-p layout vals slot gen off cap pk ps pg pool)
              (and (equal (car (fn2-run-load-bytes bytes slot gen off pk ps pg pool)) :ok)
                   (equal (fn2-layout-range-code slot gen off (+ off (len bytes)) t pk ps pg pool) :ok))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-load-bytes-roundtrip (bytes (fn2-layout-octets layout vals))))
            :in-theory (e/d (fn2-run-writable-header-p fn2-layout-range-code)
                      (fn2-layout-octets fn2-run-load-bytes fn2-run-read-bytes fn2-pool-slot-base fn2-pool-base
                       fn2-pool-slot-fill fn2-pool-slot-cap fn2-pool-capacity-bytes fn2-pool-workspace-code
                       fn2-pool-readable-code fn-b3-octet-listp))))))

(local
 (defthm fn2-run-header-value-write
   (implies (and (natp i) (natp j))
            (equal (fn2-fields-value i (fn2-fields-set-value j v f))
                   (if (equal i j) v (fn2-fields-value i f))))
   :hints (("Goal" :in-theory (e/d (fn2-fields-value fn2-fields-set-value update-fn2-fields-value$ai nth-update-nth)
                                    (nth update-nth))))))

(defthmd fn2-run-writer-stores-outer-header
  (let* ((slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
         (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
         (vals (fn2-run-outer-header-values w writers)) (bytes (fn2-layout-octets *fn2-format-page-header* vals))
         (write (fn2-run-head-b w base writers f pool)))
    (implies (and (fn2-run-writersp writers) (fn2-run-writers-wfp writers) (natp w) (< w (fn2-run-writers-rows writers))
                  (natp base) (<= (+ base *fn2-run-c-header-fields*) (fn2-fields-rows f))
                  (< (fn2-run-writers-page-kind w writers) (len (caddr *fn2-format-page-kind*)))
                  (unsigned-byte-p 60 (fn2-run-payload-length w writers))
                  (fn2-run-writable-header-p *fn2-format-page-header* vals slot gen 0 *fn2-run-header-area* pk ps pg pool))
             (and (equal (car write) :ok)
                  (equal (mv-nth 2 write) (mv-nth 1 (fn2-run-load-bytes bytes slot gen 0 pk ps pg pool))))))
  :hints (("Goal" :do-not '(preprocess) :do-not-induct t
           :use ((:instance fn2-run-writable-header-can-load (layout *fn2-format-page-header*)
                        (vals (fn2-run-outer-header-values w writers))
                        (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
                        (off 0) (cap *fn2-run-header-area*) (pk (fn2-run-writers-okind w writers))
                        (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))))
           :in-theory (e/d (fn2-run-head-b fn2-format-page-header-writes-scalar-header)
                     (fn2-run-writable-header-p fn2-format-page-header-encode fn2-run-payload-length fn2-fields-value
                      fn2-fields-set-value fn2-fields-rows fn2-run-load-bytes fn2-layout-range-code fn2-layout-octets
                      fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen
                      fn2-run-writers-history fn2-run-writers-incarnation fn2-run-writers-unit fn2-run-writers-epoch
                      fn2-run-writers-counter fn2-run-writers-page-kind fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-rows)))))

(defthmd fn2-run-writer-stores-inner-header
  (let* ((slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
         (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
         (base (fn2-run-writers-fields w writers)) (outer (fn2-run-head-b w base writers f pool)) (bp (mv-nth 2 outer))
         (vals (fn2-run-inner-header-values w writers)) (bytes (fn2-layout-octets *fn2-run-page-header* vals))
         (write (fn2-run-head w writers restarts f pool)))
    (implies (and (fn2-run-writersp writers) (fn2-run-writers-wfp writers) (natp w) (< w (fn2-run-writers-rows writers))
                  (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-heading*) (equal (car outer) :ok)
                  (fn2-run-writable-header-p *fn2-run-page-header* vals slot gen *fn2-run-header-area* *fn2-run-entries-base* pk ps pg bp))
             (and (equal (car write) :ok)
                  (equal (mv-nth 1 write) (fn2-run-writers-set-phase w *fn2-run-writer-phase-sealing* writers))
                  (equal (mv-nth 3 write) (mv-nth 1 (fn2-run-load-bytes bytes slot gen *fn2-run-header-area* pk ps pg bp))))))
  :hints (("Goal" :do-not '(preprocess) :do-not-induct t
           :use ((:instance fn2-run-writable-header-can-load (layout *fn2-run-page-header*)
                        (vals (fn2-run-inner-header-values w writers))
                        (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
                        (off *fn2-run-header-area*) (cap *fn2-run-entries-base*) (pk (fn2-run-writers-okind w writers))
                        (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
                        (pool (mv-nth 2 (fn2-run-head-b w (fn2-run-writers-fields w writers) writers f pool)))))
           :in-theory (e/d (fn2-run-head fn2-run-page-header-writes-scalar-header)
                     (fn2-run-writable-header-p fn2-run-page-header-encode fn2-run-head-b fn2-fields-value fn2-fields-set-value
                      fn2-run-load-bytes fn2-layout-range-code fn2-layout-octets fn2-run-writers-fields fn2-run-writers-phase
                      fn2-run-writers-set-phase fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind
                      fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-schema fn2-run-writers-schema-version
                      fn2-run-writers-run fn2-run-writers-level fn2-run-writers-ordinal fn2-run-writers-entries
                      fn2-run-writers-restarts fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-rows)))))
