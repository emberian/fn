(in-package "ACL2")
(include-book "ribbon-false-neg-finish-proof")
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

; A byte count accounts for completed chunks, completed blocks, and the
; pending block. Both the byte path and the full-chunk path use this count.
(defun fn2-ribbon-hash-cursor-p (bytes fn2-b3)
  (declare (xargs :stobjs fn2-b3 :verify-guards nil))
  (let ((ctr (fn2-b3-counter 0 fn2-b3)) (blocks (fn2-b3-blocks 0 fn2-b3)) (pos (fn2-b3-pos 0 fn2-b3)))
    (and (natp ctr) (natp blocks) (< blocks 16) (natp pos) (<= pos 64)
         (equal bytes (+ (* 1024 ctr) (* 64 blocks) pos))
         (equal (fn2-b3-verify-phase 0 fn2-b3) 0)
         (equal (fn2-b3-flags 0 fn2-b3) 0) (equal (fn2-b3-origin 0 fn2-b3) 0)
         (natp (fn2-b3-depth 0 fn2-b3)) (<= (fn2-b3-depth 0 fn2-b3) 54))))

(local
 (defconst *fn2-ribbon-b3-controls* '(fn2-b3-counter fn2-b3-blocks fn2-b3-pos fn2-b3-verify-phase fn2-b3-flags fn2-b3-origin fn2-b3-depth)))

(local
 (defun fn2-ribbon-control-frames (columns call changed value)
   (if (atom columns) nil
     (cons `(equal (,(car columns) 0 ,call)
                   ,(if (eq (car columns) changed) value `(,(car columns) 0 fn2-b3)))
           (fn2-ribbon-control-frames (cdr columns) call changed value)))))

(local
 (defmacro fn2-ribbon-control-frame (name call changed value &rest hints)
   `(defthm ,name
      (and ,@(fn2-ribbon-control-frames (if (eq changed :ignore-depth) (remove-eq 'fn2-b3-depth *fn2-ribbon-b3-controls*) *fn2-ribbon-b3-controls*) call changed value))
      :hints (("Goal" ,@hints)))))

(local (in-theory (disable fn2-ribbon-hash-cursor-p fn2-b3-counter fn2-b3-blocks fn2-b3-pos fn2-b3-verify-phase fn2-b3-flags fn2-b3-origin fn2-b3-depth fn2-b3-words-length
       fn2-b3-set-counter fn2-b3-set-blocks fn2-b3-set-pos fn2-b3-set-verify-phase fn2-b3-set-flags fn2-b3-set-origin fn2-b3-set-depth nth update-nth fn2-digest-copy fn2-digest-slot fn2-pool-datai)))

(local
 (defmacro fn2-ribbon-scalar-frames (column setter updater)
   `(fn2-ribbon-control-frame ,(fn2-columns-sym setter "-RIBBON-FRAME")
        (,setter 0 v fn2-b3) ,column v
        :in-theory (enable ,setter ,updater ,@*fn2-ribbon-b3-controls*))))

(local (progn
 (fn2-ribbon-scalar-frames fn2-b3-counter fn2-b3-set-counter update-fn2-b3-counter$ai)
 (fn2-ribbon-scalar-frames fn2-b3-blocks fn2-b3-set-blocks update-fn2-b3-blocks$ai)
 (fn2-ribbon-scalar-frames fn2-b3-pos fn2-b3-set-pos update-fn2-b3-pos$ai)
 (fn2-ribbon-scalar-frames fn2-b3-verify-phase fn2-b3-set-verify-phase update-fn2-b3-verify-phase$ai)
 (fn2-ribbon-scalar-frames fn2-b3-flags fn2-b3-set-flags update-fn2-b3-flags$ai)
 (fn2-ribbon-scalar-frames fn2-b3-origin fn2-b3-set-origin update-fn2-b3-origin$ai)
 (fn2-ribbon-scalar-frames fn2-b3-depth fn2-b3-set-depth update-fn2-b3-depth$ai)))

(local
 (fn2-ribbon-control-frame fn2-ribbon-store-keeps-controls (fn2-b3-store 0 i v fn2-b3) nil nil
   :in-theory (enable fn2-b3-store update-fn2-b3-wordsi fn2-b3-counter fn2-b3-blocks fn2-b3-pos fn2-b3-verify-phase fn2-b3-flags fn2-b3-origin fn2-b3-depth)))

(local
 (fn2-ribbon-control-frame fn2-ribbon-push-keeps-counters (mv-nth 1 (fn2-b3-push 0 n depth src fn2-digests fn2-b3)) :ignore-depth nil
   :induct (fn2-b3-push 0 n depth src fn2-digests fn2-b3) :in-theory (enable fn2-b3-push)))

(local
 (defthm fn2-ribbon-pushed-depth-bounds
   (let ((d (fn2-b3-depth 0 (mv-nth 1 (fn2-b3-push 0 n depth src fn2-digests fn2-b3)))))
     (and (natp d) (<= d (+ 1 (nfix depth)))))
   :hints (("Goal" :induct (fn2-b3-push 0 n depth src fn2-digests fn2-b3) :in-theory (e/d (fn2-b3-push) (mod floor))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-normalized-push-fits-stack
   (implies (and (natp depth) (< depth 54))
      (let ((d (fn2-b3-depth 0 (mv-nth 1 (fn2-b3-push 0 n depth src fn2-digests fn2-b3))))) (and (natp d) (<= d 54))))
   :hints (("Goal" :use fn2-ribbon-pushed-depth-bounds :in-theory (enable nfix)))))

(defthm fn2-ribbon-hash-init-cursor
   (fn2-ribbon-hash-cursor-p 0 (mv-nth 1 (fn2-b3-init 0 0 key fn2-digests fn2-b3)))
   :hints (("Goal" :in-theory (enable fn2-ribbon-hash-cursor-p fn2-b3-init))))

(local
 (defthm fn2-ribbon-hash-byte-advances-cursor
   (implies (and (fn2-ribbon-hash-cursor-p bytes fn2-b3) (<= bytes 70000))
            (fn2-ribbon-hash-cursor-p (+ 1 bytes) (mv-nth 1 (fn2-b3-byte 0 byte fn2-digests fn2-b3))))
   :hints (("Goal" :cases ((equal (fn2-b3-pos 0 fn2-b3) 64) (equal (fn2-b3-blocks 0 fn2-b3) 15))
            :in-theory (e/d (fn2-ribbon-hash-cursor-p fn2-b3-byte fn2-b3-flush)
                     (fn2-b3-push fn2-b3-store fn2-b3-word fn2-b3-output fn2-digest-copy fn-b3-word))))))

(local
 (defthm fn2-ribbon-fragment-cursor-relative
   (implies (and (natp off) (integerp delta) (natp n) (<= (+ delta off n) 70000)
                 (fn2-ribbon-hash-cursor-p (+ delta off) fn2-b3))
            (fn2-ribbon-hash-cursor-p (+ delta off n) (mv-nth 1 (fn2-b3-fragment-into 0 off n fn2-digests fn2-b3 fn2-pool))))
   :hints (("Goal" :induct (fn2-b3-fragment-into 0 off n fn2-digests fn2-b3 fn2-pool) :expand ((fn2-b3-fragment-into 0 off n fn2-digests fn2-b3 fn2-pool))
            :in-theory (e/d ((:induction fn2-b3-fragment-into)) ((:definition fn2-b3-fragment-into) fn2-b3-byte)))
           ("Subgoal *1/1" :in-theory (enable fn2-b3-fragment-into))
           ("Subgoal *1/2" :use ((:instance fn2-ribbon-hash-byte-advances-cursor (bytes (+ delta off)) (byte (fn2-pool-datai off fn2-pool))))))
   :rule-classes nil))

(local
 (fn2-ribbon-control-frame fn2-ribbon-message-keeps-controls
     (fn2-b3-pool-message 0 off i fn2-b3 fn2-pool) nil nil
     :induct (fn2-b3-pool-message 0 off i fn2-b3 fn2-pool)
     :in-theory (enable fn2-b3-pool-message)))

(local
 (defthm fn2-ribbon-span-advances-cursor
   (implies (and (fn2-ribbon-hash-cursor-p bytes fn2-b3) (<= bytes 70000) (or (and (equal (fn2-b3-pos 0 fn2-b3) 0) (equal (fn2-b3-blocks 0 fn2-b3) 0)) (and (equal (fn2-b3-pos 0 fn2-b3) 64) (equal (fn2-b3-blocks 0 fn2-b3) 15))))
       (fn2-ribbon-hash-cursor-p (+ 1024 bytes) (mv-nth 1 (fn2-b3-span 0 abs (fn2-b3-next-counter 0 fn2-b3) lastp fn2-digests fn2-b3 fn2-pool))))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (e/d (fn2-b3-span fn2-b3-bulk fn2-b3-chunk-output-into fn2-ribbon-hash-cursor-p fn2-b3-next-counter fn2-b3-flush)
                 (fn2-b3-pool-message fn-b3-pool-blocks fn2-b3-push fn2-b3-output fn2-b3-subtree-cv-into fn2-digest-copy))))))

(local
 (defthm fn2-ribbon-page-hash-read-in-range
   (implies (and (fn2-ribbon-arena-p 0 1 9 0 1 65536 65536 fn2-pool) (natp off) (< off 65536))
            (equal (mv-nth 0 (fn2-b3-read 0 1 off 9 0 1 fn2-pool)) :ok))
   :hints (("Goal" :in-theory (e/d (fn2-b3-read fn2-pool-read fn2-ribbon-arena-p fn2-pool-workspace-code fn2-pool-readable-code)
                          (fn2-pool-handle-code fn2-pool-ownerp fn2-pool-base fn2-pool-fill fn2-pool-data-length))))))

(local
 (defthm fn2-ribbon-hash-cursor-has-room
   (implies (and (fn2-ribbon-hash-cursor-p bytes fn2-b3) (<= bytes 70000))
         (fn2-b3-roomp 0 fn2-b3))
   :hints (("Goal" :in-theory (enable fn2-ribbon-hash-cursor-p fn2-b3-roomp)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-bulk-entry-conditions
   (implies (fn2-b3-can-span 0 0 1 off left consumed 9 0 1 fn2-b3 fn2-pool) (and (<= 1024 left) (or (and (equal (fn2-b3-pos 0 fn2-b3) 0) (equal (fn2-b3-blocks 0 fn2-b3) 0)) (and (equal (fn2-b3-pos 0 fn2-b3) 64) (equal (fn2-b3-blocks 0 fn2-b3) 15)))))
   :hints (("Goal" :in-theory (e/d (fn2-b3-can-span) (fn2-b3-next-counter fn2-layout-range-code))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-feed-completes-in-page
   (let ((r (fn2-b3-feed 0 0 1 off left consumed 9 0 1 fn2-digests fn2-b3 fn2-pool)))
     (implies (and (fn2-ribbon-arena-p 0 1 9 0 1 65536 65536 fn2-pool) (natp left) (natp off) (natp consumed) (integerp delta)
                   (<= (+ consumed left) 4096) (<= (+ off left) 65536) (<= (+ delta consumed left) 70000)
                   (fn2-ribbon-hash-cursor-p (+ delta consumed) fn2-b3))
              (and (equal (mv-nth 0 r) :ok) (equal (mv-nth 1 r) (+ consumed left))
                   (fn2-ribbon-hash-cursor-p (+ delta consumed left) (mv-nth 3 r)))))
   :hints (("Goal" :induct (fn2-b3-feed 0 0 1 off left consumed 9 0 1 fn2-digests fn2-b3 fn2-pool) :expand ((fn2-b3-feed 0 0 1 off left consumed 9 0 1 fn2-digests fn2-b3 fn2-pool))
            :do-not '(preprocess) :in-theory (e/d ((:i fn2-b3-feed))
               ((:d fn2-b3-feed) fn2-ribbon-arena-p fn2-b3-roomp fn2-b3-can-span fn2-b3-read fn2-b3-next-counter fn2-b3-span fn2-b3-byte
                fn2-pool-slot-base fn2-pool-data-length fn2-b3-can-span-bounds)))
           ("Subgoal *1/1" :in-theory (enable fn2-b3-feed))
           ("Subgoal *1/2" :use ((:instance fn2-ribbon-hash-cursor-has-room (bytes (+ delta consumed)))))
           ("Subgoal *1/3" :use (fn2-ribbon-bulk-entry-conditions
                (:instance fn2-ribbon-span-advances-cursor (bytes (+ delta consumed)) (abs (+ (nfix (fn2-pool-slot-base 0 fn2-pool)) off))
                           (lastp (< left 2048)))))
           ("Subgoal *1/5" :use ((:instance fn2-ribbon-hash-byte-advances-cursor (bytes (+ delta consumed))
                                 (byte (mv-nth 1 (fn2-b3-read 0 1 off 9 0 1 fn2-pool)))))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-fragment-advances-cursor
   (implies (and (natp bytes) (natp off) (natp n) (<= (+ bytes n) 70000) (fn2-ribbon-hash-cursor-p bytes fn2-b3))
            (fn2-ribbon-hash-cursor-p (+ bytes n) (mv-nth 1 (fn2-b3-fragment-into 0 off n fn2-digests fn2-b3 fn2-pool))))
   :hints (("Goal" :use ((:instance fn2-ribbon-fragment-cursor-relative (delta (- bytes off)))))) :rule-classes nil))

(defthm fn2-ribbon-hash-update-consumes-page-range
   (let ((r (fn2-b3-update 0 0 1 off len 9 0 1 fn2-digests fn2-b3 fn2-pool)))
     (implies (and (fn2-ribbon-arena-p 0 1 9 0 1 65536 65536 fn2-pool) (natp off) (natp len) (<= len 4096) (<= (+ off len) 65536)
                   (natp bytes) (<= (+ bytes len) 70000) (fn2-ribbon-hash-cursor-p bytes fn2-b3))
              (and (equal (mv-nth 0 r) :ok) (equal (mv-nth 1 r) len)
                   (fn2-ribbon-hash-cursor-p (+ bytes len) (mv-nth 3 r)))))
   :hints (("Goal" :do-not '(preprocess) :cases ((posp (fn2-b3-fragment-count 0 0 1 off len 9 0 1 fn2-b3 fn2-pool)))
            :use ((:instance fn2-ribbon-fragment-advances-cursor (off (+ (nfix (fn2-pool-slot-base 0 fn2-pool)) off)) (n (fn2-b3-fragment-count 0 0 1 off len 9 0 1 fn2-b3 fn2-pool)))
                  (:instance fn2-ribbon-feed-completes-in-page (off (+ off (fn2-b3-fragment-count 0 0 1 off len 9 0 1 fn2-b3 fn2-pool))) (left (- len (fn2-b3-fragment-count 0 0 1 off len 9 0 1 fn2-b3 fn2-pool)))
                      (consumed (fn2-b3-fragment-count 0 0 1 off len 9 0 1 fn2-b3 fn2-pool)) (delta bytes) (fn2-digests (mv-nth 0 (fn2-b3-fragment-into 0 (+ (nfix (fn2-pool-slot-base 0 fn2-pool)) off) (fn2-b3-fragment-count 0 0 1 off len 9 0 1 fn2-b3 fn2-pool) fn2-digests fn2-b3 fn2-pool))) (fn2-b3 (mv-nth 1 (fn2-b3-fragment-into 0 (+ (nfix (fn2-pool-slot-base 0 fn2-pool)) off) (fn2-b3-fragment-count 0 0 1 off len 9 0 1 fn2-b3 fn2-pool) fn2-digests fn2-b3 fn2-pool))))
                  (:instance fn2-ribbon-feed-completes-in-page (left len) (consumed 0) (delta bytes)))
            :in-theory (e/d (fn2-b3-update) (fn2-b3-feed fn2-b3-fragment-into fn2-b3-fragment-count fn2-ribbon-arena-p
                              fn2-pool-slot-base fn2-ribbon-hash-cursor-p))))
   :rule-classes nil)

(local
 (defthm fn2-ribbon-aligned-count-positive
   (implies (and (posp n) (natp pos)) (posp (fn2-fc-aligned-count n pos morep)))
   :hints (("Goal" :use ((:instance mod-bounds-2 (x (+ pos n)) (y 1024)))
            :in-theory (enable fn2-fc-aligned-count)))))

(local
 (defthm fn2-ribbon-aligned-count-lower-bound
    (implies (and (posp n) (natp used)) (< 0 (fn2-fc-aligned-count n used morep)))
    :hints (("Goal" :use ((:instance fn2-ribbon-aligned-count-positive (pos used))) :in-theory (disable fn2-ribbon-aligned-count-positive)))
    :rule-classes :linear))

(local
 (defthm fn2-ribbon-page-span-progress-bounds
   (let ((k (fn2-fc-span-size fuel pos pad 65536 used)))
     (implies (and (posp fuel) (natp pos) (< pos 65536) (natp pad) (natp used))
              (and (posp k) (<= (+ pos k) 65536) (<= k 4096)
                   (implies (< pos pad) (<= (+ pos k) pad)))))
   :hints (("Goal" :in-theory (e/d (fn2-fc-span-size) (fn2-fc-aligned-count))))
   :rule-classes nil))

(defun fn2-ribbon-hash-input-p (pad fn2-pool)
   (declare (xargs :stobjs fn2-pool :verify-guards nil))
   (and (natp pad) (<= pad 65536) (fn2-ribbon-arena-p 0 1 9 0 1 65536 65536 fn2-pool)
        (fn2-ribbon-zero-region-p (- 65536 pad) pad 0 1 fn2-pool)))

(local
 (defthm fn2-ribbon-hash-span-addresses
   (implies (fn2-ribbon-arena-p 0 1 9 0 1 65536 65536 fn2-pool)
     (and (< 0 (fn2-pool-rows fn2-pool))
          (natp (fn2-pool-base 0 fn2-pool))
          (equal (nfix (fn2-pool-slot-base 0 fn2-pool)) (fn2-pool-base 0 fn2-pool))
          (<= (+ (fn2-pool-base 0 fn2-pool) 65536) (fn2-pool-data-length fn2-pool))))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-arena-p fn2-pool-workspace-code fn2-pool-handle-code fn2-pool-slot-base)
                         (fn2-pool-base fn2-pool-rows fn2-pool-data-length)))) :rule-classes nil))

(local
 (defthm fn2-ribbon-hash-pending-count-natural
   (implies (fn2-ribbon-hash-cursor-p bytes fn2-b3) (natp (+ (* 64 (fn2-b3-blocks 0 fn2-b3)) (fn2-b3-pos 0 fn2-b3))))
   :hints (("Goal" :in-theory (enable fn2-ribbon-hash-cursor-p))) :rule-classes nil))

(local
 (defthm fn2-ribbon-admitted-page-span
   (let* ((pos (fn2-fc-pos 0 fn2-fc)) (pad (fn2-fc-pad 0 fn2-fc)) (k (fn2-fc-span-size fuel (fn2-fc-pos 0 fn2-fc) (fn2-fc-pad 0 fn2-fc) 65536 (+ (* 64 (fn2-b3-blocks 0 fn2-b3)) (fn2-b3-pos 0 fn2-b3)))) (update (fn2-b3-update 0 0 1 (fn2-fc-pos 0 fn2-fc) (fn2-fc-span-size fuel (fn2-fc-pos 0 fn2-fc) (fn2-fc-pad 0 fn2-fc) 65536 (+ (* 64 (fn2-b3-blocks 0 fn2-b3)) (fn2-b3-pos 0 fn2-b3))) 9 0 1 fn2-digests fn2-b3 fn2-pool)) (span (fn2-fc-page-span fuel 0 0 1 0 65536 0 9 0 1 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
     (implies (and (posp fuel) (natp pos) (< pos 65536) (equal (fn2-fc-pad-end 0 fn2-fc) 65536)
                   (fn2-ribbon-hash-input-p pad fn2-pool) (fn2-ribbon-hash-cursor-p (+ 20 pos) fn2-b3))
       (and (posp k) (<= (+ pos k) 65536)
            (equal span (list :yield k (fn2-fc-set-pos 0 (+ pos k) fn2-fc) (mv-nth 3 update) (mv-nth 2 update)))
            (fn2-ribbon-hash-cursor-p (+ 20 pos k) (mv-nth 3 update)))))
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-ribbon-hash-span-addresses
                  (:instance fn2-ribbon-hash-pending-count-natural (bytes (+ 20 (fn2-fc-pos 0 fn2-fc))))
                  (:instance fn2-ribbon-page-span-progress-bounds (pos (fn2-fc-pos 0 fn2-fc)) (pad (fn2-fc-pad 0 fn2-fc)) (used (+ (* 64 (fn2-b3-blocks 0 fn2-b3)) (fn2-b3-pos 0 fn2-b3))))
                  (:instance fn2-ribbon-checker-accepts-padding-span (pad (fn2-fc-pad 0 fn2-fc)) (pos (fn2-fc-pos 0 fn2-fc)) (span (fn2-fc-span-size fuel (fn2-fc-pos 0 fn2-fc) (fn2-fc-pad 0 fn2-fc) 65536 (+ (* 64 (fn2-b3-blocks 0 fn2-b3)) (fn2-b3-pos 0 fn2-b3)))) (slot 0) (gen 1))
                  (:instance fn2-ribbon-hash-update-consumes-page-range (off (fn2-fc-pos 0 fn2-fc)) (len (fn2-fc-span-size fuel (fn2-fc-pos 0 fn2-fc) (fn2-fc-pad 0 fn2-fc) 65536 (+ (* 64 (fn2-b3-blocks 0 fn2-b3)) (fn2-b3-pos 0 fn2-b3)))) (bytes (+ 20 (fn2-fc-pos 0 fn2-fc)))))
            :in-theory (e/d (fn2-fc-page-span fn2-ribbon-hash-input-p) (fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-phase fn2-fc-zero fn2-fc-set-pos fn2-fc-set-phase fn2-fc-span-size fn2-fc-zero-prefix fn2-pool-base fn2-pool-data-length fn2-pool-rows fn2-pool-slot-base fn2-ribbon-arena-p fn2-ribbon-zero-region-p fn2-layout-range-code fn2-b3-update fn2-ribbon-hash-cursor-p nfix))))
   :rule-classes nil))

(defun fn2-ribbon-hash-workspace-p (fn2-b3 fn2-digests)
   (declare (xargs :stobjs (fn2-b3 fn2-digests) :verify-guards nil))
   (and (fn2-b3p fn2-b3) (fn2-digestsp fn2-digests) (fn2-b3-ready 0 fn2-b3 fn2-digests)
        (fn2-digest-rowp 136 fn2-digests)))

(local
 (defthm fn2-ribbon-update-keeps-workspace
   (implies (and (fn2-ribbon-hash-workspace-p fn2-b3 fn2-digests) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                 (unsigned-byte-p 32 off) (unsigned-byte-p 32 len))
     (fn2-ribbon-hash-workspace-p (mv-nth 3 (fn2-b3-update 0 0 1 off len 9 0 1 fn2-digests fn2-b3 fn2-pool)) (mv-nth 2 (fn2-b3-update 0 0 1 off len 9 0 1 fn2-digests fn2-b3 fn2-pool))))
   :hints (("Goal" :use ((:instance fn2-b3-update-shape (row 0) (slot 0) (gen 1) (okind 9) (oslot 0) (ogen 1)))
            :in-theory (e/d (fn2-ribbon-hash-workspace-p fn2-b3-ready fn2-digest-rowp fn2-digest-workspacep fn2-b3-words-length) (fn2-b3p fn2-digestsp fn2-b3-wfp fn2-digests-wfp fn2-b3-rows fn2-digests-rows fn2-poolp fn2-pool-wfp nth unsigned-byte-p fn2-b3-update-shape fn2-b3-update))))))

(local
 (defthm fn2-ribbon-byte-keeps-workspace
   (implies (and (fn2-ribbon-hash-workspace-p fn2-b3 fn2-digests) (unsigned-byte-p 8 byte))
      (fn2-ribbon-hash-workspace-p (mv-nth 1 (fn2-b3-byte 0 byte fn2-digests fn2-b3)) (mv-nth 0 (fn2-b3-byte 0 byte fn2-digests fn2-b3))))
   :hints (("Goal" :use ((:instance fn2-b3-byte-shape (row 0)))
            :in-theory (e/d (mv-nth fn2-ribbon-hash-workspace-p fn2-b3-ready fn2-digest-rowp fn2-digest-workspacep fn2-b3-words-length) (fn2-b3p fn2-digestsp fn2-b3-wfp fn2-digests-wfp fn2-b3-rows fn2-digests-rows fn2-poolp fn2-pool-wfp nth fn2-b3-byte fn2-b3-byte-shape))))))

(local
 (defthm fn2-ribbon-page-init-keeps-workspace
   (implies (and (fn2-ribbon-hash-workspace-p fn2-b3 fn2-digests) t)
      (fn2-ribbon-hash-workspace-p (mv-nth 1 (fn2-b3-init 0 0 1 fn2-digests fn2-b3)) (mv-nth 0 (fn2-b3-init 0 0 1 fn2-digests fn2-b3))))
   :hints (("Goal" :use ((:instance fn2-b3-init-shape (row 0) (mode 0) (key 1)))
            :in-theory (e/d (mv-nth fn2-ribbon-hash-workspace-p fn2-b3-ready fn2-digest-rowp fn2-digest-workspacep fn2-b3-words-length) (fn2-b3p fn2-digestsp fn2-b3-wfp fn2-digests-wfp fn2-b3-rows fn2-digests-rows fn2-poolp fn2-pool-wfp nth fn2-b3-init fn2-b3-init-shape))))))

(local
 (defthm fn2-ribbon-finalize-keeps-workspace
   (implies (and (fn2-ribbon-hash-workspace-p fn2-b3 fn2-digests) t)
      (fn2-ribbon-hash-workspace-p fn2-b3 (fn2-b3-finalize 125 0 fn2-digests fn2-b3)))
   :hints (("Goal" :use ((:instance fn2-b3-finalize-shape (row 0) (dst 125)))
            :in-theory (e/d (fn2-ribbon-hash-workspace-p fn2-b3-ready fn2-digest-rowp fn2-digest-workspacep fn2-b3-words-length) (fn2-b3p fn2-digestsp fn2-b3-wfp fn2-digests-wfp fn2-b3-rows fn2-digests-rows fn2-poolp fn2-pool-wfp nth fn2-b3-finalize fn2-b3-finalize-shape))))))

(local
 (defthm fn2-ribbon-hashing-observes-fc-updates
   (let ((p (fn2-fc-set-pos 0 v fn2-fc)) (s (fn2-fc-set-phase 0 v fn2-fc)))
     (and (equal (fn2-fc-phase 0 p) (fn2-fc-phase 0 fn2-fc))
          (equal (fn2-fc-phase 0 s) v)
          (equal (fn2-fc-pos 0 p) v)
          (equal (fn2-fc-pos 0 s) (fn2-fc-pos 0 fn2-fc))
          (equal (fn2-fc-pad 0 p) (fn2-fc-pad 0 fn2-fc))
          (equal (fn2-fc-pad 0 s) (fn2-fc-pad 0 fn2-fc))
          (equal (fn2-fc-pad-end 0 p) (fn2-fc-pad-end 0 fn2-fc))
          (equal (fn2-fc-pad-end 0 s) (fn2-fc-pad-end 0 fn2-fc))
          (equal (fn2-fc-rows p) (fn2-fc-rows fn2-fc))
          (equal (fn2-fc-rows s) (fn2-fc-rows fn2-fc))))
   :hints (("Goal" :in-theory (enable fn2-fc-phase fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-rows fn2-fc-set-pos update-fn2-fc-pos$ai fn2-fc-set-phase update-fn2-fc-phase$ai)))))

(defun fn2-ribbon-hash-remaining (fn2-fc)
  (declare (xargs :stobjs fn2-fc :verify-guards nil))
  (let ((end (if (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-prefix*) 65557 65536)))
    (- end (fn2-fc-pos 0 fn2-fc))))

(defun fn2-ribbon-hash-state-p (pad fn2-fc fn2-b3 fn2-digests)
   (declare (xargs :stobjs (fn2-fc fn2-b3 fn2-digests) :verify-guards nil))
   (let ((pos (fn2-fc-pos 0 fn2-fc)) (phase (fn2-fc-phase 0 fn2-fc)))
     (and (fn2-ribbon-hash-workspace-p fn2-b3 fn2-digests)
          (< 0 (fn2-fc-rows fn2-fc)) (equal (fn2-fc-pad 0 fn2-fc) pad)
          (equal (fn2-fc-pad-end 0 fn2-fc) 65536) (natp pos)
          (if (equal phase *fn2-fc-phase-prefix*)
              (and (<= pos 20) (fn2-ribbon-hash-cursor-p pos fn2-b3))
            (and (equal phase *fn2-fc-phase-hash*) (<= pos 65536)
                 (fn2-ribbon-hash-cursor-p (+ 20 pos) fn2-b3))))))

(defthm fn2-ribbon-hash-remaining-bounds
   (implies (fn2-ribbon-hash-state-p pad fn2-fc fn2-b3 fn2-digests) (and (natp (fn2-ribbon-hash-remaining fn2-fc))
                (<= (fn2-ribbon-hash-remaining fn2-fc) 65557)))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-hash-state-p fn2-ribbon-hash-remaining)
                  (fn2-fc-phase fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-rows fn2-ribbon-hash-workspace-p fn2-ribbon-hash-cursor-p))))
   :rule-classes nil)

(local
 (defthm fn2-ribbon-prefix-advances-one
   (let* ((r (fn2-fc-advance fuel 0 :page sealp 0 1 0 65536 0 9 0 1 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) (after (mv-nth 2 r)))
     (implies (and (fn2-ribbon-hash-state-p pad fn2-fc fn2-b3 fn2-digests) (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-prefix*))
          (and (equal (mv-nth 0 r) :more) (equal (mv-nth 1 r) 1)
               (equal (mv-nth 4 r) fn2-pool)
               (fn2-ribbon-hash-state-p pad after (mv-nth 3 r) (mv-nth 5 r))
               (equal (fn2-ribbon-hash-remaining after) (1- (fn2-ribbon-hash-remaining fn2-fc)))
               (< 0 (fn2-ribbon-hash-remaining after)))))
   :hints (("Goal" :do-not '(preprocess) :use ((:instance fn2-ribbon-hash-byte-advances-cursor (bytes (fn2-fc-pos 0 fn2-fc)) (byte (fn2-fc-prefix-byte 0 :page (fn2-fc-pos 0 fn2-fc) fn2-fc-context))))
            :in-theory (e/d (fn2-fc-advance fn2-fc-byte fn2-ribbon-hash-state-p fn2-ribbon-hash-remaining)
                  (fn2-fc-phase fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-rows fn2-ribbon-hash-workspace-p fn2-ribbon-hash-cursor-p fn2-fc-set-pos fn2-fc-set-phase fn2-b3-byte
                    fn2-b3-finalize fn2-fc-page-span fn2-fc-prefix-byte unsigned-byte-p))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-hash-advances-a-span
   (let* ((r (fn2-fc-advance fuel 0 :page sealp 0 1 0 65536 0 9 0 1 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) (after (mv-nth 2 r)))
     (implies (and (and (fn2-ribbon-hash-input-p pad fn2-pool) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-ribbon-hash-state-p pad fn2-fc fn2-b3 fn2-digests)) (posp fuel) (< 0 (fn2-ribbon-hash-remaining fn2-fc))
                   (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-hash*))
          (and (equal (mv-nth 0 r) :yield) (equal (mv-nth 4 r) fn2-pool)
               (fn2-ribbon-hash-state-p pad after (mv-nth 3 r) (mv-nth 5 r))
               (< (fn2-ribbon-hash-remaining after) (fn2-ribbon-hash-remaining fn2-fc)))))
   :hints (("Goal" :do-not '(preprocess) :use (fn2-ribbon-admitted-page-span
                   (:instance fn2-ribbon-update-keeps-workspace (off (fn2-fc-pos 0 fn2-fc)) (len (fn2-fc-span-size fuel (fn2-fc-pos 0 fn2-fc) (fn2-fc-pad 0 fn2-fc) 65536 (+ (* 64 (fn2-b3-blocks 0 fn2-b3)) (fn2-b3-pos 0 fn2-b3))))))
            :in-theory (e/d (fn2-fc-advance fn2-ribbon-hash-state-p fn2-ribbon-hash-remaining unsigned-byte-p)
                   (fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-phase fn2-fc-zero fn2-fc-set-pos fn2-fc-set-phase fn2-fc-span-size fn2-fc-zero-prefix fn2-pool-base fn2-pool-data-length fn2-pool-rows fn2-pool-slot-base fn2-ribbon-arena-p fn2-ribbon-zero-region-p fn2-layout-range-code fn2-b3-update fn2-ribbon-hash-cursor-p fn2-ribbon-hash-input-p fn2-poolp fn2-pool-wfp fn2-ribbon-hash-workspace-p
                         fn2-fc-page-span fn2-fc-rows fn2-fc-byte fn2-ribbon-update-keeps-workspace))))
   :rule-classes nil))

(local
 (defun-nx fn2-ribbon-prefix-induct (fuel sealp fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
   (declare (xargs :measure (nfix fuel)))
   (if (or (zp fuel) (not (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-prefix*))) t
     (let ((r (fn2-fc-advance fuel 0 :page sealp 0 1 0 65536 0 9 0 1 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
       (fn2-ribbon-prefix-induct (1- fuel) sealp (mv-nth 2 r) fn2-fc-context (mv-nth 3 r) fn2-fields fn2-pool (mv-nth 5 r))))))

(local
 (defthm fn2-ribbon-hash-phase-alternatives
   (implies (fn2-ribbon-hash-state-p pad fn2-fc fn2-b3 fn2-digests) (or (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-prefix*)
       (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-hash*)))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-hash-state-p) (fn2-fc-phase fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-rows fn2-ribbon-hash-workspace-p))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-hash-run-makes-progress
   (let* ((r (fn2-fc-run-bytes fuel 0 :page sealp 0 1 0 65536 0 9 0 1 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) (before (fn2-ribbon-hash-remaining fn2-fc)) (after (fn2-ribbon-hash-remaining (mv-nth 1 r))))
     (implies (and (and (fn2-ribbon-hash-input-p pad fn2-pool) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-ribbon-hash-state-p pad fn2-fc fn2-b3 fn2-digests)) (natp fuel) (< 0 before))
       (and (equal (mv-nth 0 r) :more) (equal (mv-nth 3 r) fn2-pool)
            (fn2-ribbon-hash-state-p pad (mv-nth 1 r) (mv-nth 2 r) (mv-nth 4 r))
            (<= after before) (implies (posp fuel) (< after before)))))
   :hints (("Goal" :induct (fn2-ribbon-prefix-induct fuel sealp fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests) :expand ((fn2-fc-run-bytes fuel 0 :page sealp 0 1 0 65536 0 9 0 1 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
            :do-not '(preprocess) :in-theory (union-theories '((:i fn2-ribbon-prefix-induct) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)
                    posp natp zp-open (:compound-recognizer zp-compound-recognizer) |(+ c (+ d x))| (:t fn2-fc-advance) (:t fn2-fc-run-bytes) |(+ y x)| (:e unary--))
                   (theory 'minimal-theory)))
           ("Subgoal *1/1" :use (fn2-ribbon-hash-phase-alternatives fn2-ribbon-hash-advances-a-span))
           ("Subgoal *1/2" :use fn2-ribbon-prefix-advances-one))
   :rule-classes nil))

(defthm fn2-ribbon-page-hash-step-progress
   (let* ((r (fn2-format-run :page sealp 0 0 1 0 65536 0 9 0 1 4096 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) (after (mv-nth 1 r)))
     (implies (and (and (fn2-ribbon-hash-input-p pad fn2-pool) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-ribbon-hash-state-p pad fn2-fc fn2-b3 fn2-digests)) (< 0 (fn2-ribbon-hash-remaining fn2-fc)))
       (and (equal (mv-nth 0 r) :more) (equal (mv-nth 3 r) fn2-fields) (equal (mv-nth 4 r) fn2-pool)
            (fn2-ribbon-hash-state-p pad after (mv-nth 2 r) (mv-nth 5 r))
            (< (fn2-ribbon-hash-remaining after) (fn2-ribbon-hash-remaining fn2-fc)))))
   :hints (("Goal" :use (fn2-ribbon-hash-phase-alternatives (:instance fn2-ribbon-hash-run-makes-progress (fuel 4096)))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-format-run fn2-fc-step (:t fn2-fc-run-bytes) (:e member-equal) (:e posp)
                   mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory))))
   :rule-classes nil)

(local
 (defthm fn2-ribbon-hash-end-position
   (implies (and (fn2-ribbon-hash-state-p pad fn2-fc fn2-b3 fn2-digests) (equal (fn2-ribbon-hash-remaining fn2-fc) 0))
      (and (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-hash*) (equal (fn2-fc-pos 0 fn2-fc) 65536)))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-hash-state-p fn2-ribbon-hash-remaining)
                (fn2-fc-phase fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-rows fn2-ribbon-hash-workspace-p)))) :rule-classes nil))

(local
 (defthm fn2-ribbon-hash-end-finalizes
   (implies (and (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-hash*) (equal (fn2-fc-pos 0 fn2-fc) 65536))
      (equal (fn2-fc-advance fuel 0 :page sealp 0 1 0 65536 0 9 0 1 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests) (list :more 1 (fn2-fc-set-pos 0 0 (fn2-fc-set-phase 0 *fn2-fc-phase-digest* fn2-fc)) fn2-b3 fn2-pool (fn2-b3-finalize 125 0 fn2-digests fn2-b3))))
   :hints (("Goal" :in-theory (e/d (fn2-fc-advance fn2-fc-page-span fn2-fc-byte)
                    (fn2-fc-phase fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-rows fn2-fc-set-phase fn2-fc-set-pos fn2-b3-finalize fn2-b3-update fn2-b3-byte fn2-fc-prefix-byte))))))

(local
 (defthm fn2-ribbon-sealer-records-final-digest
   (implies (and (posp fuel) (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-digest*)
                 (equal (fn2-fc-context-hash 0 fn2-fc-context) 136))
      (equal (fn2-fc-run-bytes fuel 0 :page t 0 1 0 65536 0 9 0 1 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests) (list :ok fn2-fc fn2-b3 fn2-pool (fn2-digest-copy 136 125 fn2-digests))))
   :hints (("Goal" :expand ((fn2-fc-run-bytes fuel 0 :page t 0 1 0 65536 0 9 0 1 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) :in-theory (e/d (fn2-fc-advance fn2-fc-byte)
         (fn2-fc-context-hash fn2-fc-phase fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-rows fn2-fc-run-bytes fn2-digest-copy))))))

(defthm fn2-ribbon-page-hash-completes-seal
   (implies (and (fn2-ribbon-hash-state-p pad fn2-fc fn2-b3 fn2-digests) (equal (fn2-ribbon-hash-remaining fn2-fc) 0)
                 (equal (fn2-fc-context-hash 0 fn2-fc-context) 136))
     (equal (fn2-format-run :page t 0 0 1 0 65536 0 9 0 1 4096 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
            (list :ok (fn2-fc-reset 0 (fn2-fc-set-pos 0 0 (fn2-fc-set-phase 0 *fn2-fc-phase-digest* fn2-fc))) fn2-b3 fn2-fields fn2-pool (fn2-digest-copy 136 125 (fn2-b3-finalize 125 0 fn2-digests fn2-b3)))))
   :hints (("Goal" :use fn2-ribbon-hash-end-position
           :expand ((fn2-fc-run-bytes 4096 0 :page t 0 1 0 65536 0 9 0 1 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
           :in-theory (union-theories '(fn2-format-run fn2-fc-step fn2-ribbon-hash-end-finalizes fn2-ribbon-sealer-records-final-digest
               fn2-ribbon-hashing-observes-fc-updates (:e member-equal) (:e posp) (:e unary--) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory))))
   :rule-classes nil)

(local (defthm fn2-b3-read-copy
  (implies (and (natp i) (natp dst))
           (equal (fn2-digest-list i (fn2-digest-copy dst src fn2-digests))
                  (fn2-digest-list (if (equal i dst) src i) fn2-digests)))
  :hints (("Goal" :cases ((equal i dst))
                  :in-theory (enable fn2-digest-copy fn2-digest-list)))))

(local (defthm fn2-b3-read-parent-cv
  (implies (and (natp i) (natp dst))
    (equal (fn2-digest-list i (fn2-b3-parent-cv dst left right key flags fn2-digests))
           (if (equal i dst)
               (fn-b3-compress (fn2-digest-list key fn2-digests)
                 (append (fn2-digest-list left fn2-digests)
                         (fn2-digest-list right fn2-digests))
                 0 64 (logior flags 4))
             (fn2-digest-list i fn2-digests))))
  :hints (("Goal" :cases ((equal i dst))
                  :in-theory (enable fn2-b3-parent-cv fn2-digest-list fn-b3-compress)))))

(local (defthm fn2-b3-read-parent-root
  (implies (and (natp i) (natp dst))
    (equal (fn2-digest-list i (fn2-b3-parent-root dst left right key flags fn2-digests))
           (if (equal i dst)
               (fn-b3-compress (fn2-digest-list key fn2-digests)
                 (append (fn2-digest-list left fn2-digests)
                         (fn2-digest-list right fn2-digests))
                 0 64 (logior flags 12))
             (fn2-digest-list i fn2-digests))))
  :hints (("Goal" :cases ((equal i dst))
                  :in-theory (enable fn2-b3-parent-root fn2-digest-list fn-b3-compress)))))

(local (in-theory (disable fn2-digest-list fn-b3-compress fn2-b3-flags
                           fn2-b3-depth logior)))

(defun fn2-b3-frontier-list (depth fn2-digests)
  (declare (xargs :stobjs fn2-digests :verify-guards nil))
  (if (zp depth) nil
    (cons (fn2-digest-list (+ *fn2-b3-frontier* (1- depth)) fn2-digests)
          (fn2-b3-frontier-list (1- depth) fn2-digests))))

(local (defun fn2-b3-join (key left right flags root)
  (fn-b3-compress key (append left right) 0 64 (logior flags (if root 12 4)))))

(local (defun fn2-b3-fold-list (stack cv key flags root)
  (if (atom stack) cv
    (fn2-b3-fold-list (cdr stack)
                      (fn2-b3-join key (car stack) cv flags
                                   (and root (atom (cdr stack))))
                      key flags root))))

(local (defthm fn2-b3-read-parent
  (implies (and (natp i) (natp dst))
    (equal (fn2-digest-list i (fn2-b3-parent dst 0 level right root fn2-digests fn2-b3))
           (if (equal i dst)
               (fn2-b3-join (fn2-digest-list *fn2-b3-key* fn2-digests)
                            (fn2-digest-list (+ *fn2-b3-frontier* level) fn2-digests)
                            (fn2-digest-list right fn2-digests)
                            (fn2-b3-flags 0 fn2-b3) root)
             (fn2-digest-list i fn2-digests))))
  :hints (("Goal" :in-theory (enable fn2-b3-parent fn2-b3-join)))))

(local (in-theory (disable fn2-b3-join)))

(local (defthm fn2-b3-parent-preserves-lower-frontier
  (implies (and (natp dst) (<= (+ *fn2-b3-frontier* (nfix depth)) dst))
    (equal (fn2-b3-frontier-list depth (fn2-b3-parent dst 0 level right root fn2-digests fn2-b3))
           (fn2-b3-frontier-list depth fn2-digests)))
  :hints (("Goal" :induct (fn2-b3-frontier-list depth fn2-digests)))))

(local (defthm fn2-b3-frontier-list-consp
  (equal (consp (fn2-b3-frontier-list depth fn2-digests)) (posp depth))))

(local (defthm fn2-b3-fold-refines-list
  (implies (and (natp depth) (natp dst) (<= (+ *fn2-b3-frontier* depth) dst))
    (equal (fn2-digest-list dst (fn2-b3-fold dst 0 depth root fn2-digests fn2-b3))
           (fn2-b3-fold-list (fn2-b3-frontier-list depth fn2-digests)
                             (fn2-digest-list dst fn2-digests)
                             (fn2-digest-list *fn2-b3-key* fn2-digests)
                             (fn2-b3-flags 0 fn2-b3) root)))
  :hints (("Goal" :induct (fn2-b3-fold dst 0 depth root fn2-digests fn2-b3)
                  :expand ((:free (depth root) (fn2-b3-fold dst 0 depth root fn2-digests fn2-b3)))
                  :in-theory (enable (:induction fn2-b3-fold)))
          ("Subgoal *1/2" :cases ((equal depth 1))))))

(local (defun fn2-b3-push-list (stack cv n key flags)
  (if (and (consp stack) (equal (mod (nfix n) 2) 0))
      (fn2-b3-push-list (cdr stack) (fn2-b3-join key (car stack) cv flags nil)
                        (floor n 2) key flags)
    (cons cv stack))))

(local (defthm fn2-b3-copy-preserves-lower-frontier
  (implies (and (natp dst) (<= (+ *fn2-b3-frontier* (nfix depth)) dst))
    (equal (fn2-b3-frontier-list depth (fn2-digest-copy dst src fn2-digests))
           (fn2-b3-frontier-list depth fn2-digests)))
  :hints (("Goal" :induct (fn2-b3-frontier-list depth fn2-digests)))))

(local (defthm fn2-b3-read-set-depth
  (and (equal (fn2-b3-depth 0 (fn2-b3-set-depth 0 d fn2-b3)) d)
       (equal (fn2-b3-flags 0 (fn2-b3-set-depth 0 d fn2-b3))
              (fn2-b3-flags 0 fn2-b3)))
  :hints (("Goal" :in-theory (enable fn2-b3-depth fn2-b3-flags)))))

(local (defthm fn2-b3-push-refines-list
  (implies (and (natp depth) (natp src) (< (+ *fn2-b3-frontier* depth) src))
    (mv-let (next-digests next-b3) (fn2-b3-push 0 n depth src fn2-digests fn2-b3)
      (and
       (equal (fn2-b3-frontier-list (fn2-b3-depth 0 next-b3) next-digests)
              (fn2-b3-push-list (fn2-b3-frontier-list depth fn2-digests)
                                (fn2-digest-list src fn2-digests)
                                n (fn2-digest-list *fn2-b3-key* fn2-digests)
                                (fn2-b3-flags 0 fn2-b3)))
       (equal (fn2-digest-list *fn2-b3-key* next-digests)
              (fn2-digest-list *fn2-b3-key* fn2-digests))
       (equal (fn2-b3-flags 0 next-b3) (fn2-b3-flags 0 fn2-b3)))))
  :hints (("Goal" :induct (fn2-b3-push 0 n depth src fn2-digests fn2-b3)
                  :expand ((:free (v) (fn2-b3-push 0 v 0 src fn2-digests fn2-b3)) (:free (v) (fn2-b3-push 0 v depth src fn2-digests fn2-b3))
                           (:free (cv key flags) (fn2-b3-push-list (fn2-b3-frontier-list depth fn2-digests) cv n key flags)))
                  :do-not '(preprocess generalize fertilize) :in-theory (e/d ((:induction fn2-b3-push)) (floor mod))))))

(local (defun fn2-b3-buffer-words (fn2-b3)
  (declare (xargs :stobjs fn2-b3 :verify-guards nil))
  (list
    (fn2-b3-block-word 0 0 fn2-b3) (fn2-b3-block-word 0 1 fn2-b3)
    (fn2-b3-block-word 0 2 fn2-b3) (fn2-b3-block-word 0 3 fn2-b3)
    (fn2-b3-block-word 0 4 fn2-b3) (fn2-b3-block-word 0 5 fn2-b3)
    (fn2-b3-block-word 0 6 fn2-b3) (fn2-b3-block-word 0 7 fn2-b3)
    (fn2-b3-block-word 0 8 fn2-b3) (fn2-b3-block-word 0 9 fn2-b3)
    (fn2-b3-block-word 0 10 fn2-b3) (fn2-b3-block-word 0 11 fn2-b3)
    (fn2-b3-block-word 0 12 fn2-b3) (fn2-b3-block-word 0 13 fn2-b3)
    (fn2-b3-block-word 0 14 fn2-b3) (fn2-b3-block-word 0 15 fn2-b3)
    )))

(local (defun fn2-b3-buffer-output (end fn2-digests fn2-b3)
  (declare (xargs :stobjs (fn2-digests fn2-b3) :verify-guards nil))
  (fn-b3-output (fn2-digest-list *fn2-b3-cv* fn2-digests)
                (fn2-b3-buffer-words fn2-b3)
                (fn2-b3-counter 0 fn2-b3) (fn2-b3-pos 0 fn2-b3)
                (logior (if (equal (fn2-b3-blocks 0 fn2-b3) 0) 1 0)
                        (if end 2 0)))))

(local (defun fn2-b3-output-words (out root)
  (if root
      (fn-b3-compress (fn-b3-nthx 0 out) (fn-b3-nthx 1 out) 0
                      (fn-b3-nthx 3 out) (logior (ifix (fn-b3-nthx 4 out)) 8))
    (fn-b3-output-cv out))))

(local (defthm fn2-b3-nth-cons
  (equal (nth n (cons a b)) (if (zp n) a (nth (1- n) b))) :hints (("Goal" :expand ((nth n (cons a b)))))))

(local (defthm fn2-b3-read-output
  (implies (and (natp i) (natp dst) (equal (fn2-b3-flags 0 fn2-b3) 0))
    (equal (fn2-digest-list i (fn2-b3-output dst 0 end root fn2-digests fn2-b3))
           (if (equal i dst)
               (fn2-b3-output-words (fn2-b3-buffer-output end fn2-digests fn2-b3) root)
             (fn2-digest-list i fn2-digests))))
  :hints (("Goal" :cases ((equal i dst))
                  :in-theory (e/d (fn2-b3-output fn-b3-output-cv fn-b3-compress fn2-digest-list)
                                  (nth fn2-b3-counter fn2-b3-pos fn2-b3-blocks fn2-b3-block-word))))))

(local (in-theory (disable fn2-b3-output-words fn2-b3-buffer-output)))

(local (defthm fn2-b3-output-preserves-lower-frontier
  (implies (and (natp dst) (<= (+ *fn2-b3-frontier* (nfix depth)) dst)
                (equal (fn2-b3-flags 0 fn2-b3) 0))
    (equal (fn2-b3-frontier-list depth (fn2-b3-output dst 0 end root fn2-digests fn2-b3))
           (fn2-b3-frontier-list depth fn2-digests)))
  :hints (("Goal" :induct (fn2-b3-frontier-list depth fn2-digests)))))

(local (defthm fn2-b3-finish-refines-list
  (let ((depth (fn2-b3-depth 0 fn2-b3)))
    (implies (and (natp depth) (<= depth 54) (equal (fn2-b3-flags 0 fn2-b3) 0))
      (equal (fn2-digest-list 125 (fn2-b3-finish 125 0 root fn2-digests fn2-b3))
             (fn2-b3-fold-list (fn2-b3-frontier-list depth fn2-digests)
               (fn2-b3-output-words (fn2-b3-buffer-output t fn2-digests fn2-b3)
                                    (and root (equal depth 0)))
               (fn2-digest-list *fn2-b3-key* fn2-digests) 0 root))))
  :hints (("Goal" :in-theory (enable fn2-b3-finish)))))

(defun-nx fn2-ribbon-live-words-p (n pos a b)
   (if (zp n) t (and (or (<= pos (* 4 (1- n))) (equal (fn2-b3-word 0 (1- n) a) (fn2-b3-word 0 (1- n) b))) (fn2-ribbon-live-words-p (1- n) pos a b))))

(local (defthm fn2-ribbon-live-word-agrees
 (implies (and (fn2-ribbon-live-words-p n pos a b) (natp i) (natp n) (< i n) (< (* 4 i) pos)) (equal (fn2-b3-word 0 i a) (fn2-b3-word 0 i b)))
 :hints (("Goal" :induct (fn2-ribbon-live-words-p n pos a b) :in-theory (enable fn2-ribbon-live-words-p)))
 :rule-classes nil))

(local (defthm fn2-ribbon-block-word-agrees
 (implies (and (equal pos (fn2-b3-pos 0 a)) (equal pos (fn2-b3-pos 0 b)) (fn2-ribbon-live-words-p 16 pos a b) (natp i) (< i 16)) (equal (fn2-b3-block-word 0 i a) (fn2-b3-block-word 0 i b)))
 :hints (("Goal" :use ((:instance fn2-ribbon-live-word-agrees (n 16))) :in-theory (e/d (fn2-b3-block-word) (fn2-ribbon-live-words-p fn2-b3-word fn2-b3-pos mod expt)))) :rule-classes nil))

(local (defthm fn2-ribbon-buffer-words-agree
 (implies (and (equal (fn2-b3-pos 0 a) (fn2-b3-pos 0 b)) (fn2-ribbon-live-words-p 16 (fn2-b3-pos 0 a) a b)) (equal (fn2-b3-buffer-words a) (fn2-b3-buffer-words b)))
 :hints (("Goal" :use ((:instance fn2-ribbon-block-word-agrees (pos (fn2-b3-pos 0 a)) (i 0)) (:instance fn2-ribbon-block-word-agrees (pos (fn2-b3-pos 0 a)) (i 1)) (:instance fn2-ribbon-block-word-agrees (pos (fn2-b3-pos 0 a)) (i 2)) (:instance fn2-ribbon-block-word-agrees (pos (fn2-b3-pos 0 a)) (i 3)) (:instance fn2-ribbon-block-word-agrees (pos (fn2-b3-pos 0 a)) (i 4)) (:instance fn2-ribbon-block-word-agrees (pos (fn2-b3-pos 0 a)) (i 5)) (:instance fn2-ribbon-block-word-agrees (pos (fn2-b3-pos 0 a)) (i 6)) (:instance fn2-ribbon-block-word-agrees (pos (fn2-b3-pos 0 a)) (i 7)) (:instance fn2-ribbon-block-word-agrees (pos (fn2-b3-pos 0 a)) (i 8)) (:instance fn2-ribbon-block-word-agrees (pos (fn2-b3-pos 0 a)) (i 9)) (:instance fn2-ribbon-block-word-agrees (pos (fn2-b3-pos 0 a)) (i 10)) (:instance fn2-ribbon-block-word-agrees (pos (fn2-b3-pos 0 a)) (i 11)) (:instance fn2-ribbon-block-word-agrees (pos (fn2-b3-pos 0 a)) (i 12)) (:instance fn2-ribbon-block-word-agrees (pos (fn2-b3-pos 0 a)) (i 13)) (:instance fn2-ribbon-block-word-agrees (pos (fn2-b3-pos 0 a)) (i 14)) (:instance fn2-ribbon-block-word-agrees (pos (fn2-b3-pos 0 a)) (i 15))) :in-theory (union-theories '(fn2-b3-buffer-words (:e natp) (:e <)) (theory 'minimal-theory)))) :rule-classes nil))

(defun-nx fn2-ribbon-b3-agree (a da b db)
 (let ((pos (fn2-b3-pos 0 a)) (depth (fn2-b3-depth 0 a)))
  (and (natp pos) (<= pos 64) (natp depth) (<= depth 54) (equal (fn2-b3-flags 0 a) 0)
    (equal (fn2-b3-counter 0 a) (fn2-b3-counter 0 b))
    (equal (fn2-b3-blocks 0 a) (fn2-b3-blocks 0 b))
    (equal (fn2-b3-pos 0 a) (fn2-b3-pos 0 b))
    (equal (fn2-b3-verify-phase 0 a) (fn2-b3-verify-phase 0 b))
    (equal (fn2-b3-flags 0 a) (fn2-b3-flags 0 b))
    (equal (fn2-b3-origin 0 a) (fn2-b3-origin 0 b))
    (equal (fn2-b3-depth 0 a) (fn2-b3-depth 0 b))
    (equal (fn2-digest-list 0 da) (fn2-digest-list 0 db)) (equal (fn2-digest-list 1 da) (fn2-digest-list 1 db))
    (equal (fn2-b3-frontier-list depth da) (fn2-b3-frontier-list depth db)) (fn2-ribbon-live-words-p 16 pos a b))))

(defthm fn2-ribbon-finalized-results-agree
 (implies (fn2-ribbon-b3-agree a da b db) (equal (fn2-digest-list 125 (fn2-b3-finalize 125 0 da a)) (fn2-digest-list 125 (fn2-b3-finalize 125 0 db b))))
 :hints (("Goal" :use (fn2-ribbon-buffer-words-agree) :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-b3-agree fn2-b3-finalize fn2-b3-finish-refines-list fn2-b3-buffer-output) (theory 'minimal-theory)))) :rule-classes nil)

(local (defthm fn2-ribbon-no-words-at-zero (fn2-ribbon-live-words-p n 0 a b) :hints (("Goal" :induct (fn2-ribbon-live-words-p n 0 a b)))))

(local
 (defthm fn2-b3-read-iv
  (equal (fn2-digest-list 1 (fn2-digest-iv 1 fn2-digests)) *fn-b3-iv*)
  :hints (("Goal" :in-theory (enable fn2-digest-iv fn2-digest-list)))))

(defthm fn2-ribbon-initialized-hashers-agree
 (let ((x (fn2-b3-init 0 0 1 da a)) (y (fn2-b3-init 0 0 1 db b))) (fn2-ribbon-b3-agree (mv-nth 1 x) (mv-nth 0 x) (mv-nth 1 y) (mv-nth 0 y)))
 :hints (("Goal" :in-theory (e/d (fn2-ribbon-b3-agree fn2-b3-init) (fn2-ribbon-live-words-p fn2-b3-frontier-list)) :expand ((:free (d) (fn2-b3-frontier-list 0 d))))) :rule-classes nil)

(local
 (defthm fn2-b3-copy-cv-preserves-frontier
 (equal (fn2-b3-frontier-list d (fn2-digest-copy 0 src fn2-digests)) (fn2-b3-frontier-list d fn2-digests))
 :hints (("Goal" :induct (fn2-b3-frontier-list d fn2-digests) :in-theory (enable fn2-b3-frontier-list)))))

(local (defun fn2-ribbon-depth-after-push (n d)
 (declare (xargs :measure (nfix d)))
 (if (and (posp d) (equal (mod (nfix n) 2) 0)) (fn2-ribbon-depth-after-push (floor n 2) (1- d)) (+ 1 (nfix d)))))

(local (defthm fn2-ribbon-depth-of-push
 (equal (fn2-b3-depth 0 (mv-nth 1 (fn2-b3-push 0 n depth src fn2-digests fn2-b3))) (fn2-ribbon-depth-after-push n depth))
 :hints (("Goal" :induct (fn2-b3-push 0 n depth src fn2-digests fn2-b3) :in-theory (e/d (fn2-b3-push) (mod floor))))))

(local (defthm fn2-ribbon-buffer-outputs-agree
 (implies (fn2-ribbon-b3-agree a da b db) (equal (fn2-b3-buffer-output end da a) (fn2-b3-buffer-output end db b)))
 :hints (("Goal" :use fn2-ribbon-buffer-words-agree :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-b3-agree fn2-b3-buffer-output) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-depth-after-push-bound (<= (fn2-ribbon-depth-after-push n d) (+ 1 (nfix d))) :rule-classes :linear :hints (("Goal" :induct (fn2-ribbon-depth-after-push n d) :in-theory (e/d (nfix) (mod floor))))))

(local (defthm fn2-ribbon-frontier-at-zero (equal (fn2-b3-frontier-list 0 d) nil) :hints (("Goal" :expand ((fn2-b3-frontier-list 0 d))))))

(local (defthm fn2-ribbon-frontier-of-push
 (implies (and (natp depth) (< depth 54)) (equal (fn2-b3-frontier-list (fn2-ribbon-depth-after-push n depth) (mv-nth 0 (fn2-b3-push 0 n depth 56 fn2-digests fn2-b3)))
  (fn2-b3-push-list (fn2-b3-frontier-list depth fn2-digests) (fn2-digest-list 56 fn2-digests) n (fn2-digest-list 1 fn2-digests) (fn2-b3-flags 0 fn2-b3))))
 :hints (("Goal" :use ((:instance fn2-b3-push-refines-list (src 56))) :in-theory (union-theories '(fn2-ribbon-depth-of-push natp (:e natp) (:e binary-+) (:e <)) (theory 'minimal-theory))))))

(local (defthm fn2-ribbon-flushed-hashers-agree
 (implies (fn2-ribbon-b3-agree a da b db) (fn2-ribbon-b3-agree (mv-nth 1 (fn2-b3-flush 0 da a)) (mv-nth 0 (fn2-b3-flush 0 da a)) (mv-nth 1 (fn2-b3-flush 0 db b)) (mv-nth 0 (fn2-b3-flush 0 db b))))
 :hints (("Goal" :use ((:instance fn2-ribbon-buffer-outputs-agree (end (equal (fn2-b3-blocks 0 a) 15))))
 :do-not '(preprocess) :in-theory (e/d (fn2-b3-flush fn2-ribbon-b3-agree)
 (fn2-ribbon-live-words-p fn2-b3-frontier-list fn2-b3-push-list fn2-ribbon-depth-after-push fn2-b3-output fn2-b3-push fn2-b3-buffer-output fn2-b3-output-words mod floor)))) :rule-classes nil))

(local
 (defthm fn2-b3-word-store
  (implies (and (natp i) (natp j))
    (equal (fn2-b3-word 0 i (fn2-b3-store 0 j v fn2-b3))
           (if (equal i j) (fn-b3-word v) (fn2-b3-word 0 i fn2-b3))))
  :hints (("Goal" :cases ((equal i j)) :in-theory (enable fn2-b3-word fn2-b3-store update-fn2-b3-wordsi)))))

(local
 (defthm fn2-b3-word-set-pos
  (equal (fn2-b3-word 0 i (fn2-b3-set-pos 0 pos fn2-b3)) (fn2-b3-word 0 i fn2-b3))
  :hints (("Goal" :in-theory (enable fn2-b3-word fn2-b3-set-pos update-fn2-b3-pos$ai)))))

(local (defthm fn2-ribbon-store-extends-live-prefix
 (implies (and (natp pos) (fn2-ribbon-live-words-p n pos a b))
    (fn2-ribbon-live-words-p n (+ 1 pos)
     (fn2-b3-set-pos 0 (+ 1 pos) (fn2-b3-store 0 (floor pos 4) v a))
     (fn2-b3-set-pos 0 (+ 1 pos) (fn2-b3-store 0 (floor pos 4) v b))))
 :hints (("Goal" :induct (fn2-ribbon-live-words-p n pos a b) :in-theory (e/d (fn2-ribbon-live-words-p) (fn2-b3-word fn2-b3-store fn2-b3-set-pos floor fn-b3-word))))))

(local (defun-nx fn2-ribbon-packed-word (pos byte a)
 (let* ((shift (* 8 (mod pos 4))) (word (if (equal shift 0) 0 (fn2-b3-word 0 (floor pos 4) a))))
  (fn-b3-word (+ word (ash byte shift))))))

(local (defthm fn2-ribbon-packed-words-agree
 (implies (and (natp pos) (< pos 64) (fn2-ribbon-live-words-p 16 pos a b)) (equal (fn2-ribbon-packed-word pos byte a) (fn2-ribbon-packed-word pos byte b)))
 :hints (("Goal" :use ((:instance fn2-ribbon-live-word-agrees (n 16) (i (floor pos 4))))
  :in-theory (e/d (fn2-ribbon-packed-word mod) (fn2-ribbon-live-words-p fn2-b3-word floor ash fn-b3-word)))) :rule-classes nil))

(local (defun-nx fn2-ribbon-put-packed-byte (pos byte a)
 (fn2-b3-set-pos 0 (1+ pos) (fn2-b3-store 0 (floor pos 4) (fn2-ribbon-packed-word pos byte a) a))))

(local (defthm fn2-ribbon-put-packed-bytes-agree
 (implies (and (fn2-ribbon-b3-agree a da b db) (equal pos (fn2-b3-pos 0 a)) (< pos 64))
  (fn2-ribbon-b3-agree (fn2-ribbon-put-packed-byte pos byte a) da (fn2-ribbon-put-packed-byte pos byte b) db))
 :hints (("Goal" :use (fn2-ribbon-packed-words-agree) :do-not '(preprocess) :in-theory (e/d (fn2-ribbon-put-packed-byte fn2-ribbon-b3-agree) (fn2-ribbon-packed-word fn2-ribbon-live-words-p fn2-b3-frontier-list fn2-b3-store floor)))) :rule-classes nil))

(local (defthm fn2-ribbon-byte-is-packed-write
 (let* ((pos (fn2-b3-pos 0 a)) (flush (fn2-b3-flush 0 da a)))
 (implies (and (natp pos) (<= pos 64)) (equal (fn2-b3-byte 0 byte da a)
  (if (equal pos 64) (list (mv-nth 0 flush) (fn2-ribbon-put-packed-byte 0 byte (mv-nth 1 flush)))
     (list da (fn2-ribbon-put-packed-byte pos byte a))))))
 :hints (("Goal" :cases ((equal (fn2-b3-pos 0 a) 64)) :in-theory (e/d (fn2-b3-byte fn2-ribbon-put-packed-byte fn2-ribbon-packed-word) (fn2-b3-flush fn2-b3-store fn2-b3-word fn2-b3-pos mod floor ash fn-b3-word))))))

(local (defthm fn2-ribbon-flush-resets-pos (equal (fn2-b3-pos 0 (mv-nth 1 (fn2-b3-flush 0 d a))) 0) :hints (("Goal" :in-theory (enable fn2-b3-flush)))))

(local (defthm fn2-ribbon-replay-cursor-fields
 (implies (fn2-ribbon-b3-agree a da b db) (and (natp (fn2-b3-pos 0 a)) (<= (fn2-b3-pos 0 a) 64) (equal (fn2-b3-pos 0 a) (fn2-b3-pos 0 b))
(equal (fn2-b3-blocks 0 a) (fn2-b3-blocks 0 b))
(equal (fn2-b3-counter 0 a) (fn2-b3-counter 0 b))
(equal (fn2-b3-origin 0 a) (fn2-b3-origin 0 b))
(equal (fn2-b3-depth 0 a) (fn2-b3-depth 0 b))
(equal (fn2-b3-verify-phase 0 a) (fn2-b3-verify-phase 0 b))
(equal (fn2-b3-flags 0 a) (fn2-b3-flags 0 b))))
 :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-b3-agree) (theory 'minimal-theory)))) :rule-classes nil))

(defthm fn2-ribbon-identical-bytes-preserve-hash-agreement
 (let ((x (fn2-b3-byte 0 byte da a)) (y (fn2-b3-byte 0 byte db b))) (implies (fn2-ribbon-b3-agree a da b db) (fn2-ribbon-b3-agree (mv-nth 1 x) (mv-nth 0 x) (mv-nth 1 y) (mv-nth 0 y))))
 :hints (("Goal" :use (fn2-ribbon-replay-cursor-fields fn2-ribbon-flushed-hashers-agree (:instance fn2-ribbon-put-packed-bytes-agree (pos (fn2-b3-pos 0 a))) (:instance fn2-ribbon-put-packed-bytes-agree (pos 0) (a (mv-nth 1 (fn2-b3-flush 0 da a))) (da (mv-nth 0 (fn2-b3-flush 0 da a))) (b (mv-nth 1 (fn2-b3-flush 0 db b))) (db (mv-nth 0 (fn2-b3-flush 0 db b))))) :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-byte-is-packed-write fn2-ribbon-flush-resets-pos (:t fn2-b3-flush) natp mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil)

(local
 (defthm fn2-b3-word-idempotent
  (equal (fn-b3-word (fn-b3-word x)) (fn-b3-word x))
  :hints (("Goal" :in-theory (enable fn-b3-word)))))

(local
 (defthm fn2-b3-pool-message-reads
 (implies (and (natp i) (<= i 16) (natp k) (< k 16))
  (equal (fn2-b3-word 0 k (fn2-b3-pool-message 0 off i fn2-b3 fn2-pool))
         (if (< k i) (fn2-b3-word 0 k fn2-b3)
           (fn-b3-word (fn-b3-pool-word (+ off (* 4 k)) fn2-pool)))))
 :hints (("Goal" :induct (fn2-b3-pool-message 0 off i fn2-b3 fn2-pool)
          :in-theory (enable fn2-b3-pool-message)))))

(local
 (defthm fn2-b3-pool-message-columns
 (let ((next (fn2-b3-pool-message 0 off i fn2-b3 fn2-pool)))
  (and (equal (fn2-b3-origin 0 next) (fn2-b3-origin 0 fn2-b3))
       (equal (fn2-b3-flags 0 next) (fn2-b3-flags 0 fn2-b3))
       (equal (fn2-b3-depth 0 next) (fn2-b3-depth 0 fn2-b3))
       (equal (fn2-b3-verify-phase 0 next) (fn2-b3-verify-phase 0 fn2-b3))))
 :hints (("Goal" :induct (fn2-b3-pool-message 0 off i fn2-b3 fn2-pool)
          :in-theory (enable fn2-b3-pool-message)))))

(local
 (defthm fn2-b3-word-set-columns
 (and (equal (fn2-b3-word 0 i (fn2-b3-set-blocks 0 n fn2-b3)) (fn2-b3-word 0 i fn2-b3))
      (equal (fn2-b3-word 0 i (fn2-b3-set-counter 0 n fn2-b3)) (fn2-b3-word 0 i fn2-b3)))
 :hints (("Goal" :in-theory (enable fn2-b3-word fn2-b3-set-blocks fn2-b3-set-counter update-fn2-b3-blocks$ai update-fn2-b3-counter$ai)))))

(local
 (defthm fn2-b3-chunk-output-buffer
 (equal (mv-nth 1 (fn2-b3-chunk-output-into 0 off ctr fn2-digests fn2-b3 fn2-pool))
        (fn2-b3-set-pos 0 64 (fn2-b3-set-blocks 0 15 (fn2-b3-set-counter 0 ctr
         (fn2-b3-pool-message 0 (+ 960 off) 0 fn2-b3 fn2-pool)))))
 :hints (("Goal" :in-theory (enable fn2-b3-chunk-output-into)))))

(local (defthm fn2-ribbon-loaded-chunk-digest-table
 (let ((v (fn-b3-pool-blocks off ctr 15 0 (nth 0 *fn2-b3-iv*) (nth 1 *fn2-b3-iv*) (nth 2 *fn2-b3-iv*) (nth 3 *fn2-b3-iv*) (nth 4 *fn2-b3-iv*) (nth 5 *fn2-b3-iv*) (nth 6 *fn2-b3-iv*) (nth 7 *fn2-b3-iv*) fn2-pool)))
 (equal (mv-nth 0 (fn2-b3-chunk-output-into 0 off ctr ds a fn2-pool)) (fn2-digest-load 0 (list (mv-nth 0 v) (mv-nth 1 v) (mv-nth 2 v) (mv-nth 3 v) (mv-nth 4 v) (mv-nth 5 v) (mv-nth 6 v) (mv-nth 7 v)) ds)))
 :hints (("Goal" :in-theory (e/d (fn2-b3-chunk-output-into fn2-digest-load) (fn-b3-pool-blocks fn2-b3-pool-message))))))

(local (defthm fn2-ribbon-read-loaded-row
 (implies (and (natp i) (natp dst)) (equal (fn2-digest-list i (fn2-digest-load dst ws ds)) (if (equal i dst) (list (nth 0 ws) (nth 1 ws) (nth 2 ws) (nth 3 ws) (nth 4 ws) (nth 5 ws) (nth 6 ws) (nth 7 ws)) (fn2-digest-list i ds))))
 :hints (("Goal" :cases ((equal i dst)) :in-theory (enable fn2-digest-list fn2-digest-load)))) )

(local (defthm fn2-ribbon-load-keeps-unwritten-frontier
 (implies (and (natp dst) (or (< dst 2) (<= (+ 2 (nfix depth)) dst))) (equal (fn2-b3-frontier-list depth (fn2-digest-load dst ws d)) (fn2-b3-frontier-list depth d)))
 :hints (("Goal" :induct (fn2-b3-frontier-list depth d) :in-theory (disable fn2-digest-load)))))

(local (defthm fn2-ribbon-chunk-buffer-agreement
 (fn2-ribbon-live-words-p 16 64 (mv-nth 1 (fn2-b3-chunk-output-into 0 off ctr da a fn2-pool)) (mv-nth 1 (fn2-b3-chunk-output-into 0 off ctr db b fn2-pool)))
 :hints (("Goal" :expand ((:free (x y) (fn2-ribbon-live-words-p 0 64 x y)) (:free (x y) (fn2-ribbon-live-words-p 1 64 x y)) (:free (x y) (fn2-ribbon-live-words-p 2 64 x y)) (:free (x y) (fn2-ribbon-live-words-p 3 64 x y)) (:free (x y) (fn2-ribbon-live-words-p 4 64 x y)) (:free (x y) (fn2-ribbon-live-words-p 5 64 x y)) (:free (x y) (fn2-ribbon-live-words-p 6 64 x y)) (:free (x y) (fn2-ribbon-live-words-p 7 64 x y)) (:free (x y) (fn2-ribbon-live-words-p 8 64 x y)) (:free (x y) (fn2-ribbon-live-words-p 9 64 x y)) (:free (x y) (fn2-ribbon-live-words-p 10 64 x y)) (:free (x y) (fn2-ribbon-live-words-p 11 64 x y)) (:free (x y) (fn2-ribbon-live-words-p 12 64 x y)) (:free (x y) (fn2-ribbon-live-words-p 13 64 x y)) (:free (x y) (fn2-ribbon-live-words-p 14 64 x y)) (:free (x y) (fn2-ribbon-live-words-p 15 64 x y)) (:free (x y) (fn2-ribbon-live-words-p 16 64 x y))) :in-theory (enable fn2-ribbon-live-words-p)))))

(local (defthm fn2-ribbon-full-chunk-agrees
 (implies (fn2-ribbon-b3-agree a da b db) (fn2-ribbon-b3-agree (mv-nth 1 (fn2-b3-chunk-output-into 0 off ctr da a fn2-pool)) (mv-nth 0 (fn2-b3-chunk-output-into 0 off ctr da a fn2-pool)) (mv-nth 1 (fn2-b3-chunk-output-into 0 off ctr db b fn2-pool)) (mv-nth 0 (fn2-b3-chunk-output-into 0 off ctr db b fn2-pool))))
 :hints (("Goal" :use fn2-ribbon-chunk-buffer-agreement :in-theory (e/d (fn2-ribbon-b3-agree) (fn2-digest-load fn2-ribbon-live-words-p fn2-b3-frontier-list fn-b3-pool-blocks fn2-b3-pool-message)))) :rule-classes nil))

(local (defthm fn2-ribbon-bulk-hashers-agree
 (implies (fn2-ribbon-b3-agree a da b db) (fn2-ribbon-b3-agree (mv-nth 1 (fn2-b3-bulk 0 off 1024 ctr lastp da a fn2-pool)) (mv-nth 0 (fn2-b3-bulk 0 off 1024 ctr lastp da a fn2-pool)) (mv-nth 1 (fn2-b3-bulk 0 off 1024 ctr lastp db b fn2-pool)) (mv-nth 0 (fn2-b3-bulk 0 off 1024 ctr lastp db b fn2-pool))))
 :hints (("Goal" :use fn2-ribbon-full-chunk-agrees :do-not '(preprocess) :in-theory (e/d (fn2-b3-bulk fn2-ribbon-b3-agree) (fn2-ribbon-live-words-p fn2-b3-frontier-list fn2-b3-push-list fn2-ribbon-depth-after-push fn2-b3-chunk-output-into fn2-b3-output fn2-b3-push fn2-digest-load fn-b3-pool-tree fn-b3-pool-blocks mod floor)))) :rule-classes nil))

(local (defthm fn2-ribbon-span-hashers-agree
 (implies (fn2-ribbon-b3-agree a da b db) (fn2-ribbon-b3-agree (mv-nth 1 (fn2-b3-span 0 off ctr lastp da a fn2-pool)) (mv-nth 0 (fn2-b3-span 0 off ctr lastp da a fn2-pool)) (mv-nth 1 (fn2-b3-span 0 off ctr lastp db b fn2-pool)) (mv-nth 0 (fn2-b3-span 0 off ctr lastp db b fn2-pool))))
 :hints (("Goal" :use (fn2-ribbon-replay-cursor-fields fn2-ribbon-flushed-hashers-agree fn2-ribbon-bulk-hashers-agree (:instance fn2-ribbon-bulk-hashers-agree (a (mv-nth 1 (fn2-b3-flush 0 da a))) (da (mv-nth 0 (fn2-b3-flush 0 da a))) (b (mv-nth 1 (fn2-b3-flush 0 db b))) (db (mv-nth 0 (fn2-b3-flush 0 db b))))) :do-not '(preprocess) :in-theory (union-theories '(fn2-b3-span (:t fn2-b3-flush) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-agree-on-feed-controls
 (implies (fn2-ribbon-b3-agree a da b db)
 (and (equal (fn2-b3-next-counter 0 a) (fn2-b3-next-counter 0 b))
(equal (fn2-b3-roomp 0 a) (fn2-b3-roomp 0 b))
(equal (fn2-b3-can-span 0 slot gen off left consumed okind oslot ogen a fn2-pool) (fn2-b3-can-span 0 slot gen off left consumed okind oslot ogen b fn2-pool))
(equal (fn2-b3-fragment-count 0 slot gen off left okind oslot ogen a fn2-pool) (fn2-b3-fragment-count 0 slot gen off left okind oslot ogen b fn2-pool))))
 :hints (("Goal" :use fn2-ribbon-replay-cursor-fields :do-not '(preprocess) :in-theory (union-theories '(fn2-b3-next-counter fn2-b3-roomp fn2-b3-can-span fn2-b3-fragment-count) (theory 'minimal-theory)))) :rule-classes nil))

(local (defun-nx fn2-ribbon-replay-feed-induct (left off consumed a da b db fn2-pool)
 (declare (xargs :measure (nfix left) :hints (("Goal" :in-theory (enable fn2-b3-can-span)))))
 (cond ((or (zp left) (not (fn2-b3-roomp 0 a)) (>= off 4294967295) (>= consumed 4096)) t)
       ((fn2-b3-can-span 0 0 1 off left consumed 9 0 1 a fn2-pool) (fn2-ribbon-replay-feed-induct (- left 1024) (+ off 1024) (+ consumed 1024) (mv-nth 1 (fn2-b3-span 0 (+ (nfix (fn2-pool-slot-base 0 fn2-pool)) off) (fn2-b3-next-counter 0 a) (< left 2048) da a fn2-pool)) (mv-nth 0 (fn2-b3-span 0 (+ (nfix (fn2-pool-slot-base 0 fn2-pool)) off) (fn2-b3-next-counter 0 a) (< left 2048) da a fn2-pool)) (mv-nth 1 (fn2-b3-span 0 (+ (nfix (fn2-pool-slot-base 0 fn2-pool)) off) (fn2-b3-next-counter 0 a) (< left 2048) db b fn2-pool)) (mv-nth 0 (fn2-b3-span 0 (+ (nfix (fn2-pool-slot-base 0 fn2-pool)) off) (fn2-b3-next-counter 0 a) (< left 2048) db b fn2-pool)) fn2-pool))
       ((equal (mv-nth 0 (fn2-b3-read 0 1 off 9 0 1 fn2-pool)) :ok) (fn2-ribbon-replay-feed-induct (1- left) (+ off 1) (+ consumed 1) (mv-nth 1 (fn2-b3-byte 0 (mv-nth 1 (fn2-b3-read 0 1 off 9 0 1 fn2-pool)) da a)) (mv-nth 0 (fn2-b3-byte 0 (mv-nth 1 (fn2-b3-read 0 1 off 9 0 1 fn2-pool)) da a)) (mv-nth 1 (fn2-b3-byte 0 (mv-nth 1 (fn2-b3-read 0 1 off 9 0 1 fn2-pool)) db b)) (mv-nth 0 (fn2-b3-byte 0 (mv-nth 1 (fn2-b3-read 0 1 off 9 0 1 fn2-pool)) db b)) fn2-pool))
       (t t))))

(local (defthm fn2-ribbon-feeds-agree
 (let ((x (fn2-b3-feed 0 0 1 off left consumed 9 0 1 da a fn2-pool)) (y (fn2-b3-feed 0 0 1 off left consumed 9 0 1 db b fn2-pool))) (implies (fn2-ribbon-b3-agree a da b db) (and (equal (mv-nth 0 x) (mv-nth 0 y)) (equal (mv-nth 1 x) (mv-nth 1 y)) (fn2-ribbon-b3-agree (mv-nth 3 x) (mv-nth 2 x) (mv-nth 3 y) (mv-nth 2 y)))))
 :hints (("Goal" :induct (fn2-ribbon-replay-feed-induct left off consumed a da b db fn2-pool) :expand ((fn2-b3-feed 0 0 1 off left consumed 9 0 1 da a fn2-pool) (fn2-b3-feed 0 0 1 off left consumed 9 0 1 db b fn2-pool)) :do-not '(preprocess) :in-theory (union-theories '((:i fn2-ribbon-replay-feed-induct) (:t fn2-b3-read) (:t fn2-b3-span) (:t fn2-b3-byte) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))
 ("Subgoal *1/1" :use (:instance fn2-ribbon-agree-on-feed-controls (slot 0) (gen 1) (okind 9) (oslot 0) (ogen 1)))
 ("Subgoal *1/2" :use ((:instance fn2-ribbon-agree-on-feed-controls (slot 0) (gen 1) (okind 9) (oslot 0) (ogen 1)) (:instance fn2-ribbon-span-hashers-agree (off (+ (nfix (fn2-pool-slot-base 0 fn2-pool)) off)) (ctr (fn2-b3-next-counter 0 a)) (lastp (< left 2048)))))
 ("Subgoal *1/3" :use ((:instance fn2-ribbon-agree-on-feed-controls (slot 0) (gen 1) (okind 9) (oslot 0) (ogen 1)) (:instance fn2-ribbon-identical-bytes-preserve-hash-agreement (byte (mv-nth 1 (fn2-b3-read 0 1 off 9 0 1 fn2-pool))))))
 ("Subgoal *1/4" :use (:instance fn2-ribbon-agree-on-feed-controls (slot 0) (gen 1) (okind 9) (oslot 0) (ogen 1)))) :rule-classes nil))

(local (defun-nx fn2-ribbon-replay-fragment-induct (off n a da b db fn2-pool)
 (declare (xargs :measure (nfix n)))
 (if (zp n) t (fn2-ribbon-replay-fragment-induct (+ 1 off) (1- n) (mv-nth 1 (fn2-b3-byte 0 (fn2-pool-datai off fn2-pool) da a)) (mv-nth 0 (fn2-b3-byte 0 (fn2-pool-datai off fn2-pool) da a)) (mv-nth 1 (fn2-b3-byte 0 (fn2-pool-datai off fn2-pool) db b)) (mv-nth 0 (fn2-b3-byte 0 (fn2-pool-datai off fn2-pool) db b)) fn2-pool))))

(local (defthm fn2-ribbon-fragments-agree
 (implies (fn2-ribbon-b3-agree a da b db) (fn2-ribbon-b3-agree (mv-nth 1 (fn2-b3-fragment-into 0 off n da a fn2-pool)) (mv-nth 0 (fn2-b3-fragment-into 0 off n da a fn2-pool)) (mv-nth 1 (fn2-b3-fragment-into 0 off n db b fn2-pool)) (mv-nth 0 (fn2-b3-fragment-into 0 off n db b fn2-pool))))
 :hints (("Goal" :induct (fn2-ribbon-replay-fragment-induct off n a da b db fn2-pool)
  :expand ((fn2-b3-fragment-into 0 off n da a fn2-pool) (fn2-b3-fragment-into 0 off n db b fn2-pool)) :do-not '(preprocess)
  :in-theory (union-theories '((:i fn2-ribbon-replay-fragment-induct) (:t fn2-b3-byte) |(+ y x)| mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))
  ("Subgoal *1/2" :use (:instance fn2-ribbon-identical-bytes-preserve-hash-agreement (byte (fn2-pool-datai off fn2-pool))))) :rule-classes nil))

(defthm fn2-ribbon-identical-page-updates-preserve-hash-agreement
 (let ((x (fn2-b3-update 0 0 1 off len 9 0 1 da a fn2-pool)) (y (fn2-b3-update 0 0 1 off len 9 0 1 db b fn2-pool))) (implies (fn2-ribbon-b3-agree a da b db) (and (equal (mv-nth 0 x) (mv-nth 0 y)) (equal (mv-nth 1 x) (mv-nth 1 y)) (fn2-ribbon-b3-agree (mv-nth 3 x) (mv-nth 2 x) (mv-nth 3 y) (mv-nth 2 y)))))
 :hints (("Goal" :use ((:instance fn2-ribbon-agree-on-feed-controls (slot 0) (gen 1) (okind 9) (oslot 0) (ogen 1) (left len))
 (:instance fn2-ribbon-fragments-agree (off (+ (nfix (fn2-pool-slot-base 0 fn2-pool)) off)) (n (fn2-b3-fragment-count 0 0 1 off len 9 0 1 a fn2-pool))) (:instance fn2-ribbon-feeds-agree (consumed (fn2-b3-fragment-count 0 0 1 off len 9 0 1 a fn2-pool)) (off (+ off (fn2-b3-fragment-count 0 0 1 off len 9 0 1 a fn2-pool))) (left (- (min len 4096) (fn2-b3-fragment-count 0 0 1 off len 9 0 1 a fn2-pool)))) (:instance fn2-ribbon-feeds-agree (consumed (fn2-b3-fragment-count 0 0 1 off len 9 0 1 a fn2-pool)) (off (+ off (fn2-b3-fragment-count 0 0 1 off len 9 0 1 a fn2-pool))) (left (- (min len 4096) (fn2-b3-fragment-count 0 0 1 off len 9 0 1 a fn2-pool))) (a (mv-nth 1 (fn2-b3-fragment-into 0 (+ (nfix (fn2-pool-slot-base 0 fn2-pool)) off) (fn2-b3-fragment-count 0 0 1 off len 9 0 1 a fn2-pool) da a fn2-pool))) (da (mv-nth 0 (fn2-b3-fragment-into 0 (+ (nfix (fn2-pool-slot-base 0 fn2-pool)) off) (fn2-b3-fragment-count 0 0 1 off len 9 0 1 a fn2-pool) da a fn2-pool))) (b (mv-nth 1 (fn2-b3-fragment-into 0 (+ (nfix (fn2-pool-slot-base 0 fn2-pool)) off) (fn2-b3-fragment-count 0 0 1 off len 9 0 1 a fn2-pool) db b fn2-pool))) (db (mv-nth 0 (fn2-b3-fragment-into 0 (+ (nfix (fn2-pool-slot-base 0 fn2-pool)) off) (fn2-b3-fragment-count 0 0 1 off len 9 0 1 a fn2-pool) db b fn2-pool)))))
 :do-not '(preprocess) :in-theory (union-theories '(fn2-b3-update (:t fn2-b3-fragment-into) (:t fn2-b3-feed) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil)

(local (defthm fn2-ribbon-output-preserves-parent-digest
 (implies (and (natp dst) (not (equal dst 136))) (equal (fn2-digest-list 136 (fn2-b3-output dst 0 end root fn2-digests fn2-b3)) (fn2-digest-list 136 fn2-digests)))
 :hints (("Goal" :in-theory (e/d (fn2-b3-output fn2-digest-list) (fn-b3-compress-core fn2-b3-block-word fn-b3-word nth))))))

(local (defthm fn2-ribbon-push-preserves-parent-digest
 (implies (< (nfix depth) 54) (equal (fn2-digest-list 136 (mv-nth 0 (fn2-b3-push 0 n depth 56 fn2-digests fn2-b3))) (fn2-digest-list 136 fn2-digests)))
 :hints (("Goal" :induct (fn2-b3-push 0 n depth 56 fn2-digests fn2-b3) :in-theory (e/d (fn2-b3-push nfix) (mod floor fn2-b3-parent fn2-digest-copy))))))

(local (defthm fn2-ribbon-flush-preserves-parent-digest
 (equal (fn2-digest-list 136 (mv-nth 0 (fn2-b3-flush 0 fn2-digests fn2-b3))) (fn2-digest-list 136 fn2-digests))
 :hints (("Goal" :in-theory (e/d (fn2-b3-flush nfix) (fn2-b3-push fn2-b3-output fn2-digest-copy mod floor))))))

(defthm fn2-ribbon-byte-preserves-parent-digest
 (equal (fn2-digest-list 136 (mv-nth 0 (fn2-b3-byte 0 byte fn2-digests fn2-b3))) (fn2-digest-list 136 fn2-digests))
 :hints (("Goal" :in-theory (e/d (fn2-b3-byte) (fn2-ribbon-byte-is-packed-write fn2-b3-flush fn2-b3-word ash floor mod fn-b3-word)))))

(defthm fn2-ribbon-init-preserves-parent-digest
 (equal (fn2-digest-list 136 (mv-nth 0 (fn2-b3-init 0 0 1 fn2-digests fn2-b3))) (fn2-digest-list 136 fn2-digests))
 :hints (("Goal" :in-theory (enable fn2-b3-init fn2-digest-iv fn2-digest-list fn2-digest-copy))))

(local (defthm fn2-ribbon-bulk-preserves-parent-digest
 (equal (fn2-digest-list 136 (mv-nth 0 (fn2-b3-bulk 0 off 1024 ctr lastp fn2-digests fn2-b3 fn2-pool))) (fn2-digest-list 136 fn2-digests))
 :hints (("Goal" :in-theory (e/d (fn2-b3-bulk nfix) (fn2-digest-load fn-b3-pool-tree fn-b3-pool-blocks fn2-b3-push floor mod))))))

(local (defthm fn2-ribbon-span-preserves-parent-digest
 (equal (fn2-digest-list 136 (mv-nth 0 (fn2-b3-span 0 off ctr lastp fn2-digests fn2-b3 fn2-pool))) (fn2-digest-list 136 fn2-digests))
 :hints (("Goal" :in-theory (enable fn2-b3-span)))))

(local (defthm fn2-ribbon-fragment-preserves-parent-digest
 (equal (fn2-digest-list 136 (mv-nth 0 (fn2-b3-fragment-into 0 off n fn2-digests fn2-b3 fn2-pool))) (fn2-digest-list 136 fn2-digests))
 :hints (("Goal" :induct (fn2-b3-fragment-into 0 off n fn2-digests fn2-b3 fn2-pool) :in-theory (e/d (fn2-b3-fragment-into) (fn2-b3-byte fn2-ribbon-byte-is-packed-write))))))

(local (defthm fn2-ribbon-feed-preserves-parent-digest
 (equal (fn2-digest-list 136 (mv-nth 2 (fn2-b3-feed 0 0 1 off left consumed 9 0 1 fn2-digests fn2-b3 fn2-pool))) (fn2-digest-list 136 fn2-digests))
 :hints (("Goal" :induct (fn2-b3-feed 0 0 1 off left consumed 9 0 1 fn2-digests fn2-b3 fn2-pool) :expand ((fn2-b3-feed 0 0 1 off left consumed 9 0 1 fn2-digests fn2-b3 fn2-pool)) :in-theory (e/d ((:i fn2-b3-feed)) (fn2-b3-byte fn2-ribbon-byte-is-packed-write fn2-b3-span fn2-b3-can-span fn2-b3-roomp fn2-b3-read))))))

(defthm fn2-ribbon-page-update-preserves-parent-digest
 (equal (fn2-digest-list 136 (mv-nth 2 (fn2-b3-update 0 0 1 off len 9 0 1 fn2-digests fn2-b3 fn2-pool))) (fn2-digest-list 136 fn2-digests))
 :hints (("Goal" :in-theory (e/d (fn2-b3-update) (fn2-b3-feed fn2-b3-fragment-into fn2-b3-fragment-count)))))

(local (defthm fn2-ribbon-result-fold-preserves-parent-digest
 (equal (fn2-digest-list 136 (fn2-b3-fold 125 0 depth root fn2-digests fn2-b3)) (fn2-digest-list 136 fn2-digests))
 :hints (("Goal" :induct (fn2-b3-fold 125 0 depth root fn2-digests fn2-b3) :in-theory (enable fn2-b3-fold)))))

(defthm fn2-ribbon-finalize-preserves-parent-digest
 (equal (fn2-digest-list 136 (fn2-b3-finalize 125 0 fn2-digests fn2-b3)) (fn2-digest-list 136 fn2-digests))
 :hints (("Goal" :in-theory (enable fn2-b3-finalize fn2-b3-finish))))

(defun-nx fn2-ribbon-page-hash-agree (fa a da fb b db)
  (and (equal (fn2-fc-phase 0 fa) (fn2-fc-phase 0 fb))
       (equal (fn2-fc-pos 0 fa) (fn2-fc-pos 0 fb))
       (fn2-ribbon-b3-agree a da b db)))

(defthm fn2-ribbon-agreement-implies-equal-remaining
 (implies (fn2-ribbon-page-hash-agree fa a da fb b db) (equal (fn2-ribbon-hash-remaining fa) (fn2-ribbon-hash-remaining fb)))
 :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-page-hash-agree fn2-ribbon-hash-remaining) (theory 'minimal-theory)))) :rule-classes nil)

(local (defthm fn2-ribbon-page-domain-byte
 (implies (< pos 20) (equal (fn2-fc-prefix-byte 0 :page pos ctx) (char-code (char (fn2-fc-domain :page) pos))))
 :hints (("Goal" :in-theory (e/d (fn2-fc-prefix-byte) (char char-code))))))

(local (defthm fn2-ribbon-domain-steps-agree
 (let ((x (fn2-fc-advance fuel 0 :page t 0 1 0 65536 0 9 0 1 fa ca a va fn2-pool da)) (y (fn2-fc-advance fuel 0 :page nil 0 1 0 65536 0 9 0 1 fb cb b vb fn2-pool db)))
  (implies (and (fn2-ribbon-page-hash-agree fa a da fb b db) (equal (fn2-fc-phase 0 fa) *fn2-fc-phase-prefix*)) (and (fn2-ribbon-page-hash-agree (mv-nth 2 x) (mv-nth 3 x) (mv-nth 5 x) (mv-nth 2 y) (mv-nth 3 y) (mv-nth 5 y)) (equal (fn2-digest-list 136 (mv-nth 5 y)) (fn2-digest-list 136 db)))))
 :hints (("Goal" :use ((:instance fn2-ribbon-byte-preserves-parent-digest (fn2-digests db) (fn2-b3 b) (byte (fn2-fc-prefix-byte 0 :page (fn2-fc-pos 0 fa) ca))) (:instance fn2-ribbon-identical-bytes-preserve-hash-agreement (byte (fn2-fc-prefix-byte 0 :page (fn2-fc-pos 0 fa) ca))))
  :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-page-hash-agree fn2-fc-advance fn2-fc-byte fn2-ribbon-page-domain-byte fn2-ribbon-hashing-observes-fc-updates fn2-ribbon-byte-preserves-parent-digest (:t fn2-b3-byte) (:e member-equal) (:e length) (:e fn2-fc-domain) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-hash-advance-explicit
 (let* ((pos (fn2-fc-pos 0 fn2-fc)) (k (fn2-fc-span-size fuel (fn2-fc-pos 0 fn2-fc) pad 65536 (+ (* 64 (fn2-b3-blocks 0 fn2-b3)) (fn2-b3-pos 0 fn2-b3)))) (u (fn2-b3-update 0 0 1 pos k 9 0 1 fn2-digests fn2-b3 fn2-pool)))
 (implies (and (fn2-ribbon-hash-state-p pad fn2-fc fn2-b3 fn2-digests) (fn2-ribbon-hash-input-p pad fn2-pool) (posp fuel) (< 0 (fn2-ribbon-hash-remaining fn2-fc)) (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-hash*))
 (equal (fn2-fc-advance fuel 0 :page sealp 0 1 0 65536 0 9 0 1 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests) (list :yield k (fn2-fc-set-pos 0 (+ pos k) fn2-fc) (mv-nth 3 u) fn2-pool (mv-nth 2 u)))))
 :hints (("Goal" :use fn2-ribbon-admitted-page-span :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-hash-state-p fn2-ribbon-hash-remaining fn2-fc-advance (:e member-equal) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-hash-steps-agree
 (let ((x (fn2-fc-advance fuel 0 :page t 0 1 0 65536 0 9 0 1 fa ca a va fn2-pool da)) (y (fn2-fc-advance fuel 0 :page nil 0 1 0 65536 0 9 0 1 fb cb b vb fn2-pool db))) (implies (and (fn2-ribbon-page-hash-agree fa a da fb b db) (fn2-ribbon-hash-state-p pad fa a da) (fn2-ribbon-hash-state-p pad fb b db) (fn2-ribbon-hash-input-p pad fn2-pool) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (posp fuel) (< 0 (fn2-ribbon-hash-remaining fa)) (equal (fn2-fc-phase 0 fa) *fn2-fc-phase-hash*)) (and (fn2-ribbon-page-hash-agree (mv-nth 2 x) (mv-nth 3 x) (mv-nth 5 x) (mv-nth 2 y) (mv-nth 3 y) (mv-nth 5 y)) (equal (fn2-digest-list 136 (mv-nth 5 y)) (fn2-digest-list 136 db)))))
 :hints (("Goal" :use ((:instance fn2-ribbon-hash-advance-explicit (sealp t) (fn2-fc fa) (fn2-b3 a) (fn2-fields va) (fn2-fc-context ca) (fn2-digests da)) (:instance fn2-ribbon-hash-advance-explicit (sealp nil) (fn2-fc fb) (fn2-b3 b) (fn2-fields vb) (fn2-fc-context cb) (fn2-digests db)) fn2-ribbon-agreement-implies-equal-remaining fn2-ribbon-replay-cursor-fields (:instance fn2-ribbon-identical-page-updates-preserve-hash-agreement (off (fn2-fc-pos 0 fa)) (len (fn2-fc-span-size fuel (fn2-fc-pos 0 fa) pad 65536 (+ (* 64 (fn2-b3-blocks 0 a)) (fn2-b3-pos 0 a))))) (:instance fn2-ribbon-page-update-preserves-parent-digest (fn2-digests db) (fn2-b3 b) (off (fn2-fc-pos 0 fa)) (len (fn2-fc-span-size fuel (fn2-fc-pos 0 fa) pad 65536 (+ (* 64 (fn2-b3-blocks 0 a)) (fn2-b3-pos 0 a))))))
 :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-page-hash-agree  fn2-ribbon-hashing-observes-fc-updates (:t fn2-b3-update) (:e member-equal) natp posp mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-paired-prefix-advances
 (let ((x (fn2-fc-advance fuel 0 :page t 0 1 0 65536 0 9 0 1 fa ca a va fn2-pool da)) (y (fn2-fc-advance fuel 0 :page nil 0 1 0 65536 0 9 0 1 fb cb b vb fn2-pool db))) (implies (and (and (fn2-ribbon-page-hash-agree fa a da fb b db) (fn2-ribbon-hash-state-p pad fa a da) (fn2-ribbon-hash-state-p pad fb b db) (fn2-ribbon-hash-input-p pad fn2-pool) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (< 0 (fn2-ribbon-hash-remaining fa))) (equal (fn2-fc-phase 0 fa) *fn2-fc-phase-prefix*))
 (and (and (fn2-ribbon-page-hash-agree (mv-nth 2 x) (mv-nth 3 x) (mv-nth 5 x) (mv-nth 2 y) (mv-nth 3 y) (mv-nth 5 y)) (equal (fn2-digest-list 136 (mv-nth 5 y)) (fn2-digest-list 136 db))) (equal (mv-nth 0 x) :more) (equal (mv-nth 1 x) 1) (equal (mv-nth 4 x) fn2-pool) (fn2-ribbon-hash-state-p pad (mv-nth 2 x) (mv-nth 3 x) (mv-nth 5 x)) (equal (mv-nth 0 y) :more) (equal (mv-nth 1 y) 1) (equal (mv-nth 4 y) fn2-pool) (fn2-ribbon-hash-state-p pad (mv-nth 2 y) (mv-nth 3 y) (mv-nth 5 y)) (< 0 (fn2-ribbon-hash-remaining (mv-nth 2 x))))))
 :hints (("Goal" :use (fn2-ribbon-domain-steps-agree (:instance fn2-ribbon-prefix-advances-one (sealp t) (fn2-fc fa) (fn2-fc-context ca) (fn2-b3 a) (fn2-fields va) (fn2-digests da)) (:instance fn2-ribbon-prefix-advances-one (sealp nil) (fn2-fc fb) (fn2-fc-context cb) (fn2-b3 b) (fn2-fields vb) (fn2-digests db))) :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-page-hash-agree) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-paired-spans-yield
 (let ((x (fn2-fc-advance fuel 0 :page t 0 1 0 65536 0 9 0 1 fa ca a va fn2-pool da)) (y (fn2-fc-advance fuel 0 :page nil 0 1 0 65536 0 9 0 1 fb cb b vb fn2-pool db))) (implies (and (and (fn2-ribbon-page-hash-agree fa a da fb b db) (fn2-ribbon-hash-state-p pad fa a da) (fn2-ribbon-hash-state-p pad fb b db) (fn2-ribbon-hash-input-p pad fn2-pool) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (< 0 (fn2-ribbon-hash-remaining fa))) (posp fuel) (not (equal (fn2-fc-phase 0 fa) *fn2-fc-phase-prefix*)))
 (and (and (fn2-ribbon-page-hash-agree (mv-nth 2 x) (mv-nth 3 x) (mv-nth 5 x) (mv-nth 2 y) (mv-nth 3 y) (mv-nth 5 y)) (equal (fn2-digest-list 136 (mv-nth 5 y)) (fn2-digest-list 136 db))) (equal (mv-nth 0 x) :yield) (equal (mv-nth 0 y) :yield))))
 :hints (("Goal" :use (fn2-ribbon-hash-steps-agree fn2-ribbon-agreement-implies-equal-remaining (:instance fn2-ribbon-hash-phase-alternatives (fn2-fc fa) (fn2-b3 a) (fn2-digests da)) (:instance fn2-ribbon-hash-advances-a-span (sealp t) (fn2-fc fa) (fn2-fc-context ca) (fn2-b3 a) (fn2-fields va) (fn2-digests da)) (:instance fn2-ribbon-hash-phase-alternatives (fn2-fc fb) (fn2-b3 b) (fn2-digests db)) (:instance fn2-ribbon-hash-advances-a-span (sealp nil) (fn2-fc fb) (fn2-fc-context cb) (fn2-b3 b) (fn2-fields vb) (fn2-digests db))) :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-page-hash-agree) (theory 'minimal-theory)))) :rule-classes nil))

(local (defun-nx fn2-ribbon-paired-prefix-induct (fuel fa ca a va da fb cb b vb db fn2-pool)
 (declare (xargs :measure (nfix fuel)))
 (if (or (zp fuel) (not (equal (fn2-fc-phase 0 fa) *fn2-fc-phase-prefix*))) t
 (let ((x (fn2-fc-advance fuel 0 :page t 0 1 0 65536 0 9 0 1 fa ca a va fn2-pool da)) (y (fn2-fc-advance fuel 0 :page nil 0 1 0 65536 0 9 0 1 fb cb b vb fn2-pool db))) (fn2-ribbon-paired-prefix-induct (1- fuel) (mv-nth 2 x) ca (mv-nth 3 x) va (mv-nth 5 x) (mv-nth 2 y) cb (mv-nth 3 y) vb (mv-nth 5 y) fn2-pool)))))

(local (defthm fn2-ribbon-checked-hash-run-replays-sealing
 (let ((x (fn2-fc-run-bytes fuel 0 :page t 0 1 0 65536 0 9 0 1 fa ca a va fn2-pool da)) (y (fn2-fc-run-bytes fuel 0 :page nil 0 1 0 65536 0 9 0 1 fb cb b vb fn2-pool db)))
  (implies (and (and (fn2-ribbon-page-hash-agree fa a da fb b db) (fn2-ribbon-hash-state-p pad fa a da) (fn2-ribbon-hash-state-p pad fb b db) (fn2-ribbon-hash-input-p pad fn2-pool) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (< 0 (fn2-ribbon-hash-remaining fa))) (natp fuel)) (and (fn2-ribbon-page-hash-agree (mv-nth 1 x) (mv-nth 2 x) (mv-nth 4 x) (mv-nth 1 y) (mv-nth 2 y) (mv-nth 4 y)) (equal (fn2-digest-list 136 (mv-nth 4 y)) (fn2-digest-list 136 db)))))
 :hints (("Goal" :induct (fn2-ribbon-paired-prefix-induct fuel fa ca a va da fb cb b vb db fn2-pool)
 :expand ((fn2-fc-run-bytes fuel 0 :page t 0 1 0 65536 0 9 0 1 fa ca a va fn2-pool da) (fn2-fc-run-bytes fuel 0 :page nil 0 1 0 65536 0 9 0 1 fb cb b vb fn2-pool db))
 :do-not '(preprocess) :in-theory (union-theories '((:i fn2-ribbon-paired-prefix-induct) (:t fn2-fc-advance) (:t fn2-fc-run-bytes) zp-open (:compound-recognizer zp-compound-recognizer) posp natp |(+ c (+ d x))| |(+ y x)| (:e unary--) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))
 ("Subgoal *1/1" :use fn2-ribbon-paired-spans-yield)
 ("Subgoal *1/2" :use fn2-ribbon-paired-prefix-advances)) :rule-classes nil))

(defthm fn2-ribbon-check-step-replays-sealing
 (let ((x (fn2-format-run :page t 0 0 1 0 65536 0 9 0 1 4096 fa ca a va fn2-pool da)) (y (fn2-format-run :page nil 0 0 1 0 65536 0 9 0 1 4096 fb cb b vb fn2-pool db)))
 (implies (and (fn2-ribbon-page-hash-agree fa a da fb b db) (fn2-ribbon-hash-state-p pad fa a da) (fn2-ribbon-hash-state-p pad fb b db) (fn2-ribbon-hash-input-p pad fn2-pool) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (< 0 (fn2-ribbon-hash-remaining fa))) (and (fn2-ribbon-page-hash-agree (mv-nth 1 x) (mv-nth 2 x) (mv-nth 5 x) (mv-nth 1 y) (mv-nth 2 y) (mv-nth 5 y)) (equal (fn2-digest-list 136 (mv-nth 5 y)) (fn2-digest-list 136 db)))))
 :hints (("Goal" :use ((:instance fn2-ribbon-checked-hash-run-replays-sealing (fuel 4096)) (:instance fn2-ribbon-hash-phase-alternatives (fn2-fc fa) (fn2-b3 a) (fn2-digests da)) (:instance fn2-ribbon-hash-run-makes-progress (fuel 4096) (sealp t) (fn2-fc fa) (fn2-fc-context ca) (fn2-b3 a) (fn2-fields va) (fn2-digests da)) (:instance fn2-ribbon-hash-phase-alternatives (fn2-fc fb) (fn2-b3 b) (fn2-digests db)) (:instance fn2-ribbon-hash-run-makes-progress (fuel 4096) (sealp nil) (fn2-fc fb) (fn2-fc-context cb) (fn2-b3 b) (fn2-fields vb) (fn2-digests db)) fn2-ribbon-agreement-implies-equal-remaining) :do-not '(preprocess) :in-theory (union-theories '(fn2-format-run fn2-fc-step (:t fn2-fc-run-bytes) (:e member-equal) (:e posp) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil)

(defthm fn2-ribbon-seal-saves-result-in-parent
 (equal (fn2-digest-list 136 (fn2-digest-copy 136 125 d)) (fn2-digest-list 125 d))
 :hints (("Goal" :in-theory (enable fn2-b3-read-copy))))

(defthm fn2-ribbon-equal-rows-pass-digest-comparison
 (implies (equal (fn2-digest-list 125 d) (fn2-digest-list 136 d)) (fn2-digest-equal 125 136 d))
 :hints (("Goal" :in-theory (enable fn2-digest-list fn2-digest-equal))) :rule-classes nil)
