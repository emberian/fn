; Appending an overview row writes its wire bytes and records its physical restart offset.
(in-package "ACL2")
(include-book "runs-overview-write-read-proof")

(local
 (defthm fn2-run-page-note-restart-position
 (let* ((count (fn2-run-writers-restarts w writers)) (idx (fn2-run-writers-entries w writers))
        (off (fn2-run-writers-cursor w writers)) (startp (equal (mod idx *fn2-run-restart-interval*) 0))
        (row (+ (* w *fn2-run-restart-capacity*) count))
        (note (fn2-run-note-restart w writers restarts)) (after (mv-nth 1 note)))
  (implies (and (natp w) (natp count) (< count *fn2-run-restart-capacity*)
                (<= (* (1+ w) *fn2-run-restart-capacity*) (fn2-run-restarts-rows restarts)))
           (and (equal (car note) :ok)
                (equal (fn2-run-writers-entries w after) idx)
                (equal (fn2-run-writers-restarts w after) (if startp (1+ count) count))
                (implies startp (equal (fn2-run-restarts-offset row (mv-nth 2 note)) off)))))
 :hints (("Goal" :in-theory (e/d (fn2-run-note-restart fn2-run-writers-entries fn2-run-writers-restarts
                                  fn2-run-writers-set-restarts update-fn2-run-writers-restarts$ai
                                  fn2-run-restarts-offset fn2-run-restarts-set-offset
                                  update-fn2-run-restarts-offset$ai nth-update-nth)
                              (fn2-run-restarts-rows fn2-run-writers-cursor nfix mod nth update-nth))))))

(local
 (defthm fn2-run-page-commit-position
 (let* ((idx (1+ (fn2-run-writers-entries w writers)))
        (res (fn2-run-add-commit w :ok end writers)) (after (mv-nth 1 res)))
   (implies (and (natp w) (unsigned-byte-p 32 end) (unsigned-byte-p 32 idx))
            (and (equal (car res) :ok)
                 (equal (fn2-run-writers-cursor w after) end) (equal (fn2-run-writers-entries w after) idx)
                 (equal (fn2-run-writers-restarts w after) (fn2-run-writers-restarts w writers)))))
 :hints (("Goal" :in-theory (e/d (fn2-run-add-commit fn2-run-writers-cursor fn2-run-writers-entries
                             fn2-run-writers-restarts fn2-run-writers-set-prev fn2-run-writers-set-cursor
                             fn2-run-writers-set-entries update-fn2-run-writers-prev$ai
                             update-fn2-run-writers-cursor$ai update-fn2-run-writers-entries$ai nth-update-nth)
                            (nth update-nth unsigned-byte-p))))))

(local
 (defthm fn2-run-ready-writer-bounds
 (implies (eq (fn2-run-add-ready w sid base writers restarts f pool) :ok)
          (and (equal (fn2-run-add-check w sid base writers restarts f) :ok)
               (natp w) (natp base) (< w (fn2-run-writers-rows writers))
               (<= (* (+ 1 w) *fn2-run-restart-capacity*) (fn2-run-restarts-rows restarts))
               (<= (+ (nfix (fn2-run-writers-fields w writers)) *fn2-run-prev-fields* *fn2-run-entry-rows*)
                   (fn2-fields-rows f))
               (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-open*)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn2-run-add-ready fn2-run-add-check)
                (fn2-run-roomp fn2-run-layout-fields fn2-run-layout-size fn2-run-layout-compare
                 fn2-run-writers-phase fn2-run-writers-fields fn2-fields-rows fn2-run-restarts-rows
                 fn2-run-writers-rows fn2-run-writers-schema fn2-run-writers-level fn2-run-writers-prev nfix))))))

(local
 (defthm fn2-run-ready-writer-previous-row-space
 (let ((prev (+ (nfix (fn2-run-writers-fields w writers)) *fn2-run-prev-fields*)))
  (implies (equal (fn2-run-add-ready w sid base writers restarts f pool) :ok)
           (and (natp prev) (<= (+ prev (len *fn2-overview-entry*)) (fn2-fields-rows f))
                (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-open*))))
 :rule-classes nil
 :hints (("Goal" :use fn2-run-ready-writer-bounds
          :in-theory (disable fn2-run-add-ready fn2-run-writers-fields fn2-fields-rows
                              fn2-run-add-check fn2-run-writers-phase nfix)))))

(defthm fn2-run-append-stores-encoded-row
 (let* ((lv (fn2-run-writers-level w writers)) (dst (fn2-run-writers-slot w writers))
        (dg (fn2-run-writers-gen w writers)) (off (fn2-run-writers-cursor w writers))
        (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers))
        (pg (fn2-run-writers-ogen w writers))
        (idx (fn2-run-writers-entries w writers)) (nr (fn2-run-writers-restarts w writers))
        (restartp (equal (mod idx *fn2-run-restart-interval*) 0))
        (prev (+ (nfix (fn2-run-writers-fields w writers)) *fn2-run-prev-fields*))
        (enc (fn2-run-layout-encode sid lv base dst dg off pk ps pg f pool))
        (end (mv-nth 1 enc))
        (read (fn2-run-layout-decode sid lv prev dst dg off end pk ps pg f (mv-nth 2 enc)))
        (add (fn2-run-add w sid base writers restarts f pool)) (after (mv-nth 1 add)))
  (implies (and (eq (fn2-run-add-ready w sid base writers restarts f pool) :ok)
                (natp nr) (< nr *fn2-run-restart-capacity*) (unsigned-byte-p 32 (1+ idx))
                (eq (car enc) :ok) (unsigned-byte-p 32 end) (eq (car read) :ok))
           (and (equal (car add) :ok) (equal (mv-nth 4 add) (mv-nth 2 enc))
                (equal (mv-nth 3 add) (mv-nth 2 read))
                (equal (fn2-run-writers-cursor w after) end)
                (equal (fn2-run-writers-entries w after) (1+ idx))
                (equal (fn2-run-writers-restarts w after) (if restartp (1+ nr) nr))
                (implies restartp
                         (equal (fn2-run-restarts-offset (+ (* w *fn2-run-restart-capacity*) nr) (mv-nth 2 add))
                                off)))))
 :rule-classes nil
 :hints (("Goal" :use (fn2-run-ready-writer-bounds fn2-run-page-note-restart-position)
          :in-theory (e/d (fn2-run-add fn2-run-add-write)
             (fn2-run-add-ready fn2-run-add-check fn2-run-layout-encode fn2-run-layout-decode
              fn2-run-note-restart fn2-run-add-commit fn2-fields-rows fn2-run-writers-rows fn2-run-restarts-rows
              fn2-run-writers-level fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-cursor
              fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-fields
              fn2-run-writers-entries fn2-run-writers-restarts fn2-run-restarts-offset mod nfix unsigned-byte-p)))))

(local
 (defthm fn2-run-open-build-adds-row
 (let* ((w (fn2-run-builds-wbase b builds)) (sid (fn2-run-builds-schema b builds))
        (entry-count (1+ (fn2-run-builds-entries b builds)))
        (add (fn2-run-add w sid base writers restarts f pool))
        (build (fn2-run-build-add b base builds writers restarts f pool)))
  (implies (and (natp b) (equal (fn2-run-builds-phase b builds) *fn2-run-build-phase-adding*)
                (posp (fn2-run-builds-height b builds))
                (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-open*)
                (eq (car add) :ok) (unsigned-byte-p 60 entry-count))
           (and (equal (car build) :ok)
                (equal (fn2-run-builds-entries b (mv-nth 1 build)) entry-count)
                (equal (mv-nth 2 build) (mv-nth 1 add)) (equal (mv-nth 3 build) (mv-nth 2 add))
                (equal (mv-nth 4 build) (mv-nth 3 add)) (equal (mv-nth 5 build) (mv-nth 4 add)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn2-run-build-add fn2-run-builds-entries fn2-run-builds-set-entries
                                  update-fn2-run-builds-entries$ai nth-update-nth)
                             (fn2-run-add fn2-run-builds-height fn2-run-builds-phase fn2-run-builds-schema
                              fn2-run-builds-wbase fn2-run-writers-phase unsigned-byte-p nth update-nth))))))

(defthm fn2-run-builder-appends-overview-source-row
 (let* ((w (fn2-run-builds-wbase 0 builds)) (base *fn2-run-run-entry*)
        (dst (fn2-run-writers-slot w writers)) (dg (fn2-run-writers-gen w writers))
        (off (fn2-run-writers-cursor w writers)) (line (nth 4 row)) (n (len line))
        (bytes (fn2-layout-octets *fn2-overview-entry* row)) (size (len bytes)) (end (+ off size))
        (source (+ at (fn2-pool-base src pool))) (target (+ off (fn2-pool-base dst pool)))
        (idx (fn2-run-writers-entries w writers)) (nr (fn2-run-writers-restarts w writers))
        (restartp (equal (mod idx *fn2-run-restart-interval*) 0))
        (total (1+ (fn2-run-builds-entries 0 builds)))
        (load (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool))
        (sf (mv-nth 2 load)) (sp (mv-nth 3 load))
        (build (fn2-run-build-add 0 base builds writers restarts sf sp))
        (after (mv-nth 2 build)))
  (implies (and (fn2-run-values-layoutp *fn2-overview-entry* row)
                (equal (fn2-run-builds-schema 0 builds) 3)
                (equal (fn2-run-builds-phase 0 builds) *fn2-run-build-phase-adding*)
                (posp (fn2-run-builds-height 0 builds))
                (equal (fn2-run-writers-level w writers) 0)
                (equal (fn2-run-writers-okind w writers) 9) (equal (fn2-run-writers-oslot w writers) 0)
                (equal (fn2-run-writers-ogen w writers) 1)
                (eq (fn2-run-add-ready w 3 base writers restarts sf sp) :ok)
                (natp nr) (< nr *fn2-run-restart-capacity*) (unsigned-byte-p 32 (1+ idx))
                (unsigned-byte-p 60 total) (fn2-poolp pool) (fn2-pool-wfp pool)
                (natp src) (natp dst) (not (equal src dst))
                (natp (fn2-pool-base src pool)) (natp (fn2-pool-base dst pool))
                (unsigned-byte-p 32 off) (unsigned-byte-p 32 at) (unsigned-byte-p 32 end)
                (or (<= (+ source n) target) (<= (+ target size) source))
                (equal (fn2-layout-range-code src sg at (+ at n) t 9 0 1 pool) :ok)
                (equal (fn2-layout-range-code dst dg off end t 9 0 1 pool) :ok))
           (and (equal (car load) :ok) (equal (car build) :ok)
                (fn2-poolp (mv-nth 5 build)) (fn2-pool-wfp (mv-nth 5 build))
                (natp (fn2-pool-base dst (mv-nth 5 build)))
                (equal (fn2-layout-range-code dst dg off end nil 9 0 1 (mv-nth 5 build)) :ok)
                (equal (fn2-run-builds-entries 0 (mv-nth 1 build)) total)
                (equal (fn2-run-writers-entries w after) (1+ idx))
                (equal (fn2-run-writers-cursor w after) end)
                (equal (fn2-run-writers-restarts w after) (if restartp (1+ nr) nr))
                (implies restartp
                         (equal (fn2-run-restarts-offset (+ (* w *fn2-run-restart-capacity*) nr) (mv-nth 3 build)) off))
                (equal (fn2-run-read-bytes size dst dg off 9 0 1 (mv-nth 5 build)) bytes))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess) :use
          ((:instance fn2-run-adapter-source-wire-readback
             (base *fn2-run-run-entry*) (dst (fn2-run-writers-slot (fn2-run-builds-wbase 0 builds) writers))
             (dg (fn2-run-writers-gen (fn2-run-builds-wbase 0 builds) writers)) (off (fn2-run-writers-cursor (fn2-run-builds-wbase 0 builds) writers))
             (rb (+ (nfix (fn2-run-writers-fields (fn2-run-builds-wbase 0 builds) writers)) *fn2-run-prev-fields*))
             (rf (mv-nth 2 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg at 9 0 1 f pool))))
           (:instance fn2-run-ready-writer-previous-row-space (sid 3) (base *fn2-run-run-entry*) (w (fn2-run-builds-wbase 0 builds))
             (f (mv-nth 2 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg at 9 0 1 f pool))) (pool (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg at 9 0 1 f pool))))
           (:instance fn2-run-append-stores-encoded-row (sid 3) (base *fn2-run-run-entry*) (w (fn2-run-builds-wbase 0 builds))
             (f (mv-nth 2 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg at 9 0 1 f pool))) (pool (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg at 9 0 1 f pool))))
           (:instance fn2-run-open-build-adds-row (b 0) (base *fn2-run-run-entry*)
             (f (mv-nth 2 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg at 9 0 1 f pool))) (pool (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg at 9 0 1 f pool)))))
          :in-theory (union-theories (theory 'minimal-theory)
                     '(eq not (:e len) (:e natp) (:e equal) commutativity-of-+)))))
