; One admitted row extends a contiguous overlay prefix using the actual
; source load and insertion. All workspace premises describe the state
; before the load.
(in-package "ACL2")
(include-book "range-overlay-loaded-row-proof")
(include-book "range-overlay-source-workspace-proof")
(include-book "range-overview-storage-budget-proof")

(defun-nx fn2-ov-load-workspaces-p (rows src sg ov ix f pool)
  (let* ((at (fn2-range-line-bytes rows)) (dst (fn2-overlays-slot 0 ov))
         (dg (fn2-overlays-gen 0 ov)) (off (fn2-overlays-fill 0 ov)))
    (and (fn2-ov-contiguous-arena-p rows 0 ov ix pool)
         (fn2-ov-overview-reader-p 0 *fn2-run-adapter-reader* *fn2-run-adapter-entry* ov ix f)
         (equal (fn2-overlays-phase 0 ov) *fn2-overlay-phase-active*)
         (natp (fn2-overlays-ibase 0 ov)) (<= 48 (fn2-overlays-icap 0 ov)) (equal (fn2-overlays-cap 0 ov) 65536)
         (unsigned-byte-p 32 src) (unsigned-byte-p 60 sg) (not (equal src dst))
         (natp (fn2-pool-base src pool)) (<= (+ (fn2-pool-base dst pool) 65536) (fn2-pool-base src pool))
         (equal (fn2-layout-range-code src sg at 65536 t 9 0 1 pool) :ok)
         (equal (fn2-layout-range-code dst dg off 65536 t 9 0 1 pool) :ok))))

(local
 (defthm fn2-ov-writable-row-window
   (implies (and (unsigned-byte-p 32 end) (<= at end) (<= end 65536)
                 (equal (fn2-layout-range-code slot gen at 65536 t 9 0 1 pool) :ok))
            (equal (fn2-layout-range-code slot gen at end t 9 0 1 pool) :ok))
   :hints (("Goal" :in-theory (e/d (fn2-layout-range-code)
                        (fn2-pool-workspace-code fn2-pool-slot-fill fn2-pool-slot-cap fn2-pool-slot-base
                         fn2-pool-capacity-bytes unsigned-byte-p))))))

(local
 (defthm fn2-ov-word-index-natural (implies (unsigned-byte-p 32 x) (natp x))))

(local
 (defthmd fn2-ov-next-row-has-writable-space
   (let* ((at (fn2-range-line-bytes rows)) (off (fn2-overlays-fill 0 ov)) (dst (fn2-overlays-slot 0 ov))
          (end (+ off (len (fn2-layout-octets *fn2-overview-entry* row)))))
     (implies (and (fn2-ov-load-workspaces-p rows src sg ov ix f pool)
                   (fn2-run-entries-layoutp *fn2-overview-entry* rows) (fn2-run-values-layoutp *fn2-overview-entry* row)
                   (< (len rows) 48))
              (and (unsigned-byte-p 32 at) (natp at) (unsigned-byte-p 32 end) (<= end (fn2-overlays-cap 0 ov))
                   (natp src) (natp dst)
                   (<= (+ (fn2-pool-base dst pool) off) (+ (fn2-pool-base src pool) at))
                   (<= (+ (+ off (fn2-pool-base dst pool)) (len (fn2-layout-octets *fn2-overview-entry* row)))
                       (+ at (fn2-pool-base src pool)))
                   (equal (fn2-layout-range-code src sg at (+ at (len (nth 4 row))) t 9 0 1 pool) :ok)
                   (equal (fn2-layout-range-code dst (fn2-overlays-gen 0 ov) off end t 9 0 1 pool) :ok))))
   :hints (("Goal" :use fn2-range-next-row-fits-both-workspaces
            :in-theory (e/d (fn2-ov-load-workspaces-p fn2-ov-contiguous-arena-p)
                        (fn2-ov-overview-reader-p fn2-layout-range-code fn2-range-line-bytes fn2-layout-octets
                         fn2-run-read-bytes fn2-run-entries-octets fn2-run-entries-layoutp fn2-run-values-layoutp fn2-ov-prefix-offsets-p
                         fn2-overlays-ibase fn2-overlays-icap fn2-overlays-cap fn2-overlays-slot fn2-overlays-gen fn2-overlays-fill
                         fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen fn2-overlays-phase fn2-overlays-count
                         fn2-poolp fn2-pool-wfp fn2-pool-base len nth unsigned-byte-p))))))

(local
 (defthmd fn2-ov-workspace-addresses
   (implies (fn2-ov-load-workspaces-p rows src sg ov ix f pool)
            (and (fn2-poolp pool) (fn2-pool-wfp pool) (unsigned-byte-p 32 src) (unsigned-byte-p 60 sg)
                 (natp (fn2-pool-base src pool)) (not (equal src (fn2-overlays-slot 0 ov)))
                 (natp (fn2-pool-base (fn2-overlays-slot 0 ov) pool)) (unsigned-byte-p 32 (fn2-overlays-fill 0 ov))
                 (equal (fn2-overlays-count 0 ov) (len rows)) (<= 48 (fn2-overlays-icap 0 ov)) (natp (fn2-overlays-ibase 0 ov))
                 (equal (fn2-overlays-phase 0 ov) *fn2-overlay-phase-active*) (equal (fn2-overlays-okind 0 ov) 9)
                 (equal (fn2-overlays-oslot 0 ov) 0) (equal (fn2-overlays-ogen 0 ov) 1)
                 (fn2-ov-contiguous-arena-p rows 0 ov ix pool)
                 (fn2-ov-overview-reader-p 0 *fn2-run-adapter-reader* *fn2-run-adapter-entry* ov ix f)
                 (<= (+ 5 *fn2-run-adapter-reader*) (fn2-fields-rows f))))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn2-ov-load-workspaces-p fn2-ov-contiguous-arena-p fn2-ov-overview-reader-p
                      (:e binary-+) (:e <) (:e equal) (:e natp) (:e not)))))))

(local
 (defthmd fn2-ov-prefix-ready-after-load
   (let* ((at (fn2-range-line-bytes rows))
          (load (fn2-run-load-values *fn2-overview-entry* row *fn2-run-adapter-entry* src sg at 9 0 1 f pool)))
     (implies (and (fn2-ov-load-workspaces-p rows src sg ov ix f pool)
                   (fn2-run-entries-layoutp *fn2-overview-entry* rows) (fn2-run-values-layoutp *fn2-overview-entry* row)
                   (< (len rows) 48))
              (and (fn2-ov-indexed-rows-p (len rows) rows 0 *fn2-run-adapter-reader* ov ix (mv-nth 2 load) (mv-nth 3 load))
                   (fn2-ov-overview-reader-p 0 *fn2-run-adapter-reader* *fn2-run-adapter-entry* ov ix (mv-nth 2 load)))))
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-ov-workspace-addresses fn2-ov-next-row-has-writable-space
                 (:instance fn2-ov-load-keeps-indexed-prefix (eb *fn2-run-adapter-reader*) (at (fn2-range-line-bytes rows)))
                 (:instance fn2-ov-load-preserves-reader (at (fn2-range-line-bytes rows))))
            :in-theory (union-theories (theory 'minimal-theory) '((:e natp) (:e binary-+) (:e equal) (:e not)))))))

(defthm fn2-ov-inserts-next-prefix-row
  (let* ((at (fn2-range-line-bytes rows)) (off (fn2-overlays-fill 0 ov)) (b (fn2-overlays-ibase 0 ov))
         (dst (fn2-overlays-slot 0 ov)) (dg (fn2-overlays-gen 0 ov)) (n (len rows))
         (line (nth 4 row)) (bytes (fn2-layout-octets *fn2-overview-entry* row)) (end (+ off (len bytes)))
         (load (fn2-run-load-values *fn2-overview-entry* row *fn2-run-adapter-entry* src sg at 9 0 1 f pool))
         (ins (fn2-ov-insert 0 *fn2-run-adapter-entry* *fn2-run-adapter-reader* ov ix (mv-nth 2 load) (mv-nth 3 load)))
         (after (mv-nth 1 ins)) (index (mv-nth 2 ins)) (p (mv-nth 4 ins)))
    (implies (and (fn2-ov-load-workspaces-p rows src sg ov ix f pool)
                  (fn2-run-entries-layoutp *fn2-overview-entry* rows) (fn2-run-values-layoutp *fn2-overview-entry* row)
                  (fn2-run-sorted-spec *fn2-overview-range-key* (append rows (list row))) (< n 48) (natp j))
             (and (equal (car load) :ok) (equal (mv-nth 1 load) (+ at (len line)))
                  (equal (car ins) :ok) (equal (fn2-overlays-count 0 after) (1+ n)) (equal (fn2-overlays-fill 0 after) end)
                  (equal (fn2-overlay-index-off (+ b j) index) (if (equal j n) off (fn2-overlay-index-off (+ b j) ix)))
                  (equal p (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1
                                         (mv-nth 1 (fn2-run-load-bytes line src sg at 9 0 1 pool)))))
                  (equal (fn2-layout-range-code dst dg off end nil 9 0 1 p) :ok)
                  (equal (fn2-run-read-bytes (len bytes) dst dg off 9 0 1 p) bytes))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-ov-next-row-has-writable-space fn2-ov-workspace-addresses fn2-ov-prefix-ready-after-load
                 (:instance fn2-ov-loaded-input-is-stored-at-fill (at (fn2-range-line-bytes rows))))
           :in-theory (theory 'minimal-theory))))
