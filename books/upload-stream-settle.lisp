; One retained provisional entry per drain turn; no reconstructed Ref or list.
; The controller owns current-unreferenced and root settlement after :end.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "upload-stream")
(fn2-book-layer :d)

(defmacro fn2-upload-stream-settle-op-events ()
 '(progn
   (local
    (defthm fn2-ussn-pool-code-ok-slot-bound
      (and (implies (equal (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool) :ok)
                    (< slot (fn2-pool-rows fn2-pool)))
           (implies (equal (fn2-pool-readable-code slot gen okind oslot ogen fn2-pool) :ok)
                    (< slot (fn2-pool-rows fn2-pool))))
      :rule-classes (:rewrite
                     (:linear :corollary
                      (implies (equal (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool) :ok)
                               (< slot (fn2-pool-rows fn2-pool))))
                     (:linear :corollary
                      (implies (equal (fn2-pool-readable-code slot gen okind oslot ogen fn2-pool) :ok)
                               (< slot (fn2-pool-rows fn2-pool)))))
      :hints (("Goal" :in-theory (e/d (fn2-pool-workspace-code fn2-pool-readable-code fn2-pool-handle-code)
                                      (fn2-pool-rows))))))
   (local
    (defthm fn2-ussn-pool-query-ref-count-numberp
      (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                    (natp i) (< i (fn2-pool-rows fn2-pool)))
               (and (integerp (fn2-pool-query-ref-count i fn2-pool))
                    (rationalp (fn2-pool-query-ref-count i fn2-pool))
                    (acl2-numberp (fn2-pool-query-ref-count i fn2-pool))))
      :hints (("Goal" :in-theory (disable fn2-pool-query-ref-count fn2-poolp fn2-pool-wfp fn2-pool-rows)))))
   (local
    (defthm fn2-ussn-am-get-entry-unit-rationalp
      (implies (natp (mv-nth 4 (fn2-am-get-entry base ls lg at end okind oslot ogen fn2-fields fn2-pool)))
               (and (integerp (mv-nth 4 (fn2-am-get-entry base ls lg at end okind oslot ogen fn2-fields fn2-pool)))
                    (rationalp (mv-nth 4 (fn2-am-get-entry base ls lg at end okind oslot ogen fn2-fields fn2-pool)))
                    (acl2-numberp (mv-nth 4 (fn2-am-get-entry base ls lg at end okind oslot ogen fn2-fields fn2-pool)))))))
   (defun fn2-upload-stream-settle-next (id gen fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                    :guard-hints (("Goal" :do-not '(preprocess)
                                          :in-theory (disable fn2-pool-workspace-code fn2-pool-readable-code
                                                              fn2-pool-query-ref-count
                                                              fn2-layout-range-code floor mod min nfix)))))
    (b* (((unless (and (eq (fn2-upload-snapshot-read-code id fn2-core) :ok)
                       (posp gen) (unsigned-byte-p 60 gen)
                       (equal (fn2-machine-generation id fn2-core) gen)
                       (equal (fn2-upload-row-phase id fn2-core) *fn2-upload-state-stream-drain*)
                       (equal (fn2-upload-row-pending id fn2-core) 0)))
          (mv :fault fn2-core))
         (ls (fn2-upload-row-lslot id fn2-core))
         (lg (fn2-upload-row-lgen id fn2-core))
         (c0 (fn2-upload-row-c0-slot id fn2-core))
         (g0 (fn2-upload-row-c0-gen id fn2-core))
         (c1 (fn2-upload-row-c1-slot id fn2-core))
         (g1 (fn2-upload-row-c1-gen id fn2-core))
         (ready
          (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (ready)
           (and (eq (fn2-pool-workspace-code ls lg *fn2-upload-kind* id gen fn2-pool) :ok)
                (eq (fn2-pool-readable-code c0 g0 *fn2-upload-kind* id gen fn2-pool) :ok)
                (eq (fn2-pool-readable-code c1 g1 *fn2-upload-kind* id gen fn2-pool) :ok)
                (= (fn2-pool-query-ref-count c0 fn2-pool) 0)
                (= (fn2-pool-query-ref-count c1 fn2-pool) 0)
                (= (fn2-pool-query-ref-count ls fn2-pool) 0)) ready))
         ((unless ready) (mv :fault fn2-core))
         (cursor (fn2-upload-row-stream-repack id fn2-core))
         (limit (fn2-upload-row-stream-provisional id fn2-core))
         ((unless (and (unsigned-byte-p 32 cursor) (unsigned-byte-p 32 limit)
                       (<= cursor limit))) (mv :fault fn2-core))
         (relative (fn2-am-entry-at cursor))
         ((when (>= relative limit)) (mv :end fn2-core))
         (at (+ *fn2-upload-page-provisional* relative))
         (end (min (+ at *fn2-am-entry-max*) (+ *fn2-upload-page-provisional* limit)))
         (base (* 128 (fn2-upload-hasher id fn2-core)))
         ((mv code next ?logical ?length unit epoch allocation fn2-core)
          (stobj-let ((fn2-fields (fn2-core-fields fn2-core))
                      (fn2-pool (fn2-core-pool fn2-core)))
           (code next logical length unit epoch allocation fn2-fields)
           (if (and (natp base) (<= (+ base *fn2-am-entry-fields*) (fn2-fields-rows fn2-fields))
                    (unsigned-byte-p 32 at) (unsigned-byte-p 32 end)
                    (eq (fn2-layout-range-code ls lg at end nil *fn2-upload-kind* id gen fn2-pool) :ok))
            (fn2-am-get-entry base ls lg at end *fn2-upload-kind* id gen fn2-fields fn2-pool)
            (mv :fault 0 0 0 0 0 0 fn2-fields))
           (mv code next logical length unit epoch allocation fn2-core)))
         ((unless (and (eq code :ok) (unsigned-byte-p 32 next)
                       (< at next) (<= next end) (natp unit)
                       (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 allocation)))
          (mv :fault fn2-core))
         ((mv settled fn2-core)
          (if (equal (mod unit *fn2-storage-extent-units*) 0)
              (fn2-upload-payload-settle (floor unit *fn2-storage-extent-units*) epoch allocation fn2-core)
            (mv :ok fn2-core)))
         ((unless (eq settled :ok)) (mv :fault fn2-core))
         (fn2-core (fn2-upload-put-core id (stream-repack (- next *fn2-upload-page-provisional*)))))
     (mv :ok fn2-core)))
   (fn2-core-preserves fn2-upload-stream-settle-next (id gen fn2-core) :position 1 :rows nil
    :hints (("Goal" :do-not '(preprocess)
                    :in-theory (disable fn2-pool-workspace-code fn2-pool-readable-code
                                        fn2-pool-query-ref-count
                                        fn2-layout-range-code floor mod min nfix unsigned-byte-p))))
   (defcost fn2-upload-stream-settle-next
    :answers (:ok :end :fault) :faults (:fault) :bytes *fn2-upload-entry-bytes*
    :tables (fn2-core-fields fn2-core-extents fn2-upload-table fn2-core-machines)
    :own-writes (stream-repack)
    :doc "Decode at most one retained provisional entry and settle its physical extent leader; preserve root/current/first handles.")))
