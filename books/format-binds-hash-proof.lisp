; The checker hashes the covered stream: the invariant through byte, span, run, step and drive.
; One link of the format-binds proof chain; events are exported so the next link sees the same world.
(in-package "ACL2")
(include-book "format-binds-trailer-proof")


(defmacro fc-byte-step ()
  '(fn2-fc-byte 0 kind nil 0 1 0 len base 1 0 1 fc ctx b3 fields pool ds))

(defthm fc-byte-keeps-hashing-prefix
  (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-prefix*)
           (fc-inv-claim (fc-byte-step) 1 2 4))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
     :use ((:instance fc-g-byte (b (fn2-fc-prefix-byte 0 kind (fn2-fc-pos 0 fc) ctx))
              (xs (append (fc-prefix-from (+ 1 (fn2-fc-pos 0 fc)) (fc-plen kind) kind ctx)
                          (fc-body-from 0 len bytes)))
              (ans (fc-answer kind len bytes ctx))))
     :expand ((:free (n kind) (fc-prefix-from (fn2-fc-pos 0 fc) n kind ctx)))
     :in-theory (e/d (fc-byte-in-prefix fc-inv fc-phase-pos-updates fc-zero-updates fc-pad-end-updates
                      fc-prefix-from-end fc-append-nil-left fc-append-cons
                      (:executable-counterpart natp) natp)
                     (mv-nth)))))

(defthm fc-byte-keeps-hashing-hash
  (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-hash*)
           (fc-inv-claim (fc-byte-step) 1 2 4))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
     :use ((:instance fc-g-byte
              (b (if (<= (- len 32) (fn2-fc-pos 0 fc)) 0 (fn-b3-octet (nth (fn2-fc-pos 0 fc) bytes))))
              (xs (fc-body-from (+ 1 (fn2-fc-pos 0 fc)) len bytes))
              (ans (fc-answer kind len bytes ctx)))
           (:instance fc-g-finish (dst 125) (ans (fc-answer kind len bytes ctx)))
           (:instance fc-pool-holds-necc (k (fn2-fc-pos 0 fc))))
     :expand ((:free (len) (fc-body-from (fn2-fc-pos 0 fc) len bytes)))
     :in-theory (e/d (fc-byte-in-hash fc-inv fc-phase-pos-updates fc-zero-updates fc-pad-end-updates
                      fn2-b3-finalize fc-zero-plus-len fc-body-from-end
                      (:executable-counterpart natp) natp)
                     (mv-nth)))))
(defthm fc-byte-keeps-hashing-digest
  (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-digest*)
           (fc-inv-claim (fc-byte-step) 1 2 4))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
     :use ((:instance fc-byte-in-digest (slot 0) (gen 1) (off 0) (okind 1) (oslot 0) (ogen 1)))
     :in-theory (e/d (fc-inv) (mv-nth fc-byte-in-digest)))))
(defthm fc-byte-keeps-hashing
  (fc-inv-claim (fc-byte-step) 1 2 4)
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
     :use (fc-byte-keeps-hashing-prefix fc-byte-keeps-hashing-hash fc-byte-keeps-hashing-digest
           (:instance fc-byte-in-other (sealp nil) (slot 0) (gen 1) (off 0) (okind 1) (oslot 0) (ogen 1)))
     :in-theory (theory 'minimal-theory))))

(defun fc-body-from-drop-induct (k pos)
  (declare (xargs :hints (("Goal" :in-theory (current-theory 'fc-u32-reconstruct)))))
  (if (zp k) pos (fc-body-from-drop-induct (1- k) (1+ pos))))
(defthm fc-body-from-shape
  (and (fn-b3-octet-listp (fc-body-from pos len bytes))
       (true-listp (fc-body-from pos len bytes))
       (equal (len (fc-body-from pos len bytes))
              (if (and (natp pos) (natp len)) (nfix (- len pos)) 0)))
  :hints (("Goal" :induct (fc-body-from pos len bytes)
           :in-theory (union-theories (current-theory 'fc-u32-reconstruct)
                                      '(fc-body-from fn-b3-octet-listp)))))

(defthm fc-body-from-drop
  (implies (and (natp k) (natp pos) (natp len))
           (equal (fn-b3-nthcdrx k (fc-body-from pos len bytes))
                  (fc-body-from (+ pos k) len bytes)))
  :hints (("Goal" :induct (fc-body-from-drop-induct k pos)
           :expand ((fc-body-from pos len bytes) (:free (x) (fn-b3-nthcdrx k x)))
           :in-theory (union-theories (current-theory 'fc-u32-reconstruct)
                                      '(fc-body-from-end fc-body-from-drop-induct)))))
(defthm fc-window-covers
  (implies (and (fn2-b3-windowp 4096 pool) (fc-pool-holds bytes pool) (natp pos) (natp n) (natp len)
                (<= (+ pos n) (- len 32)) (<= len 4096))
           (fn2-b3-covers (fn-b3-firstn n (fc-body-from pos len bytes)) pos pool))
  :hints (("Goal" :induct (fc-body-from-drop-induct n pos)
           :expand ((fc-body-from pos len bytes)
                    (:free (x) (fn-b3-firstn n x)) (:free (x) (fn-b3-firstn 0 x)) (fn2-b3-covers nil pos pool)
                    (:free (a x) (fn2-b3-covers (cons a x) pos pool)))
           :in-theory (union-theories (current-theory 'fc-u32-reconstruct)
                                      '(fc-body-from-drop-induct fn2-b3-covers)))
          ("Subgoal *1/2" :use ((:instance fn2-b3-window-read (used 4096) (off pos) (fn2-pool pool))
                                (:instance fc-pool-holds-necc (k pos))))))
(defthm fc-rejoin-after-partial
  (implies (and (natp k) (natp n) (<= k n) (true-listp x))
           (equal (append (fn-b3-nthcdrx k (fn-b3-firstn n x)) (fn-b3-nthcdrx n x))
                  (fn-b3-nthcdrx k x)))
  :hints (("Goal" :use ((:instance fn2-b3-cut-rejoin (n (- n k)) (xs (fn-b3-nthcdrx k x)))
                        (:instance fn2-b3-drop-twice (a k) (b (- n k)) (xs x))
                        (:instance fn2-b3-drop-of-first (a k) (b n) (xs x)))
           :in-theory (union-theories (current-theory 'fc-u32-reconstruct) '(fn2-b3-drop-true-list)))))
(defthm fc-update-body
  (implies (and (fn2-b3-windowp 4096 pool) (fc-pool-holds bytes pool)
                (natp pos) (natp n) (<= (+ pos n) 4064)
                (fc-g (fc-body-from pos 4096 bytes) ans ds b3))
   (let ((r (fn2-b3-update 0 0 1 pos n 1 0 1 ds b3 pool)))
     (and (natp (mv-nth 1 r))
          (fc-g (fc-body-from (+ pos (mv-nth 1 r)) 4096 bytes) ans (mv-nth 2 r) (mv-nth 3 r)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fc-g-update (bytes (fn-b3-firstn n (fc-body-from pos 4096 bytes)))
                    (rest (fn-b3-nthcdrx n (fc-body-from pos 4096 bytes))) (off pos))
                 (:instance fc-window-covers (len 4096))
                 (:instance fc-rejoin-after-partial (x (fc-body-from pos 4096 bytes))
                    (k (mv-nth 1 (fn2-b3-update 0 0 1 pos n 1 0 1 ds b3 pool))))
                 (:instance fn2-b3-cut-rejoin (xs (fc-body-from pos 4096 bytes))))
           :in-theory (union-theories (set-difference-theories (current-theory 'fc-u32-reconstruct)
                                         '(fc-rejoin-after-partial fn2-b3-cut-rejoin mv-nth fn2-b3-drop-of-first))
                         '(fc-body-from-shape fc-body-from-drop min)))))

(defthm fc-less-irreflexive (equal (< x x) nil))
(defthm fc-span-size-end-bound
  (implies (and (natp pos) (natp end) (< pos end))
           (<= (+ pos (fn2-fc-span-size fuel pos pad end used)) end))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn2-fc-aligned-count-bounds
                           (n (min (min (nfix fuel) 4096)
                                   (min (nfix (- end pos)) (if (< pos pad) (nfix (- pad pos)) 4096))))
                           (pos (nfix used))
                           (morep (< (min (min (nfix fuel) 4096)
                                          (min (nfix (- end pos)) (if (< pos pad) (nfix (- pad pos)) 4096)))
                                     (- end pos)))))
           :in-theory (union-theories (theory 'minimal-theory) '(fn2-fc-span-size min nfix natp fc-less-irreflexive)))))
(defthm fc-update-count-integer
  (and (integerp (mv-nth 1 (fn2-b3-update row slot gen off len okind oslot ogen ds b3 pool)))
       (<= 0 (mv-nth 1 (fn2-b3-update row slot gen off len okind oslot ogen ds b3 pool))))
  :hints (("Goal" :in-theory (union-theories (current-theory 'fc-u32-reconstruct) '(fn2-b3-update)))))
(defthm fc-update-count-sum
  (implies (and (integerp p) (<= 0 p))
           (and (integerp (+ p (mv-nth 1 (fn2-b3-update row slot gen off len okind oslot ogen ds b3 pool))))
                (<= 0 (+ p (mv-nth 1 (fn2-b3-update row slot gen off len okind oslot ogen ds b3 pool))))))
  :hints (("Goal" :use fc-update-count-integer
           :in-theory (theory 'minimal-theory))))
(defthm fc-span-keeps-hashing
  (let ((step (fn2-fc-page-span fuel 0 0 1 0 end base 1 0 1 fc ctx b3 fields pool ds)))
    (implies (and (fn2-b3-windowp 4096 pool) (fc-pool-holds bytes pool)
                  (natp (fn2-fc-pos 0 fc)) (natp end) (<= end 4064)
                  (fc-g (fc-body-from (fn2-fc-pos 0 fc) 4096 bytes) ans ds b3))
             (and (natp (fn2-fc-pos 0 (mv-nth 2 step)))
                  (fc-g (fc-body-from (fn2-fc-pos 0 (mv-nth 2 step)) 4096 bytes) ans
                        (mv-nth 4 step) (mv-nth 3 step)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (fn2-fc-page-span fc-phase-pos-updates fc-zero-plus-len fc-update-body
                            fc-span-size-end-bound fn2-fc-span-size-natural fn2-fc-zero-prefix-natural
                            fn2-fc-zero-prefix-bound fc-update-count-integer fc-update-count-sum natp (:executable-counterpart natp))
                           (mv-nth)))))

(defmacro fc-frame-span ()
  '(fn2-fc-page-span fuel 0 0 1 0 (min len (fn2-fc-pad-end 0 fc)) base 1 0 1 fc ctx b3 fields pool ds))
(defthm fc-span-keeps-pad-end
  (equal (fn2-fc-pad-end 0 (mv-nth 2 (fn2-fc-page-span fuel 0 slot gen off end base okind oslot ogen
                                                        fc ctx b3 fields pool ds)))
         (fn2-fc-pad-end 0 fc))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (fn2-fc-page-span fc-pad-end-updates) (mv-nth fn2-fc-pad-end)))))
(defthm fc-frame-span-keeps-inv
  (implies (and (eq kind :frame) (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-hash*)
                (implies (equal len 4096) (fn2-b3-windowp 4096 pool)) (fc-pool-holds bytes pool)
                (fc-inv kind len bytes ctx fc ds b3))
           (fc-inv kind len bytes ctx (mv-nth 2 (fc-frame-span)) (mv-nth 4 (fc-frame-span))
                   (mv-nth 3 (fc-frame-span))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fc-span-keeps-hashing (end 4063) (ans (fc-answer kind len bytes ctx))))
           :in-theory (e/d (fc-inv fc-span-keeps-cursor-layout fc-span-keeps-pad-end min
                            (:executable-counterpart natp) natp)
                           (mv-nth)))))
(defmacro fc-advance-step ()
  '(fn2-fc-advance fuel 0 kind nil 0 1 0 len base 1 0 1 fc ctx b3 fields pool ds))
(in-theory (disable fc-byte-in-prefix fc-byte-in-hash fc-byte-in-digest fc-byte-in-other))
(defthm fc-advance-keeps-hashing
  (fc-inv-claim (fc-advance-step) 2 3 5)
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
     :cases ((eq kind :frame))
     :in-theory (e/d (fn2-fc-advance fc-span-keeps-cursor-layout member-equal
                      (:executable-counterpart member-equal))
                     (mv-nth fc-inv)))
    ("Subgoal 2" :use (fc-byte-keeps-hashing))
    ("Subgoal 1" :use (fc-byte-keeps-hashing fc-frame-span-keeps-inv
           (:instance fc-byte-keeps-hashing
             (fc (mv-nth 2 (fc-frame-span))) (b3 (mv-nth 3 (fc-frame-span))) (ds (mv-nth 4 (fc-frame-span))))))))
(defmacro fc-run-step ()
  '(fn2-fc-run-bytes fuel 0 kind nil 0 1 0 len base 1 0 1 fc ctx b3 fields pool ds))
(defthm fc-run-keeps-hashing
  (fc-inv-claim (fc-run-step) 1 2 4)
  :rule-classes nil
  :hints (("Goal" :induct (fc-run-step) :expand (fc-run-step)
                  :in-theory (e/d ((:induction fn2-fc-run-bytes)) (mv-nth fc-inv)))
          ("Subgoal *1/3" :use fc-advance-keeps-hashing)
          ("Subgoal *1/2" :use fc-advance-keeps-hashing)))
(defthm fc-decoded-starts-hashing
  (let ((step (fn2-fc-decoded 0 kind 0 len base next fc ctx b3 fields pool ds)))
    (implies (and (not (eq kind :page)) (natp len)
                  (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-decode*)
                  (fc-inv kind len bytes ctx fc ds b3))
             (and (not (eq (car step) :ok))
                  (not (eq (car step) :yield))
                  (implies (eq (car step) :more)
                           (fc-inv kind len bytes ctx (mv-nth 1 step) ds b3)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-fc-decoded fc-inv fc-stream fc-phase-pos-updates
                                   fc-zero-updates fc-pad-end-updates fc-identity-never-more
                                   (:executable-counterpart natp) natp)
                                  (mv-nth fn2-fc-phase fn2-fc-zero fn2-fc-pad-end)))))
(defthm fc-prefix-byte-octet
  (and (integerp (fn2-fc-prefix-byte row kind pos ctx))
       (<= 0 (fn2-fc-prefix-byte row kind pos ctx))
       (<= (fn2-fc-prefix-byte row kind pos ctx) 255))
  :rule-classes ((:rewrite :corollary (integerp (fn2-fc-prefix-byte row kind pos ctx)))
                 (:linear :corollary (and (<= 0 (fn2-fc-prefix-byte row kind pos ctx))
                                          (<= (fn2-fc-prefix-byte row kind pos ctx) 255))))
  :hints (("Goal" :use ((:instance fn2-fc-prefix-byte-type (fn2-fc-context ctx)))
           :in-theory (union-theories (theory 'minimal-theory) '(unsigned-byte-p integer-range-p (:executable-counterpart expt))))))
(defthm fc-prefix-from-shape
  (and (fn-b3-octet-listp (fc-prefix-from pos n kind ctx))
       (equal (len (fc-prefix-from pos n kind ctx))
              (if (and (natp pos) (natp n)) (nfix (- n pos)) 0)))
  :hints (("Goal" :induct (fc-prefix-from pos n kind ctx)
           :in-theory (union-theories (current-theory 'fc-u32-reconstruct)
                                      '(fc-prefix-from fn-b3-octet-listp fc-prefix-byte-octet)))))
(defthm fc-stream-shape
  (implies (natp len)
           (and (fn-b3-octet-listp (fc-stream kind len bytes ctx))
                (<= (len (fc-stream kind len bytes ctx)) (+ 60 len))))
  :hints (("Goal" :use ((:instance fn2-fc-domain-bound))
           :in-theory (union-theories (current-theory 'fc-u32-reconstruct)
                         '(fc-stream fc-plen fc-prefix-from-shape fc-body-from-shape)))))
(defmacro fc-step-step ()
  '(fn2-fc-step 0 kind nil 0 1 0 len base 1 0 1 budget fc ctx b3 fields pool ds))
(in-theory (disable fc-stream-shape fc-prefix-from-shape fc-body-from-shape fc-prefix-byte-octet))
(defthm fc-inv-in-decode
  (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-decode*)
           (iff (fc-inv kind len bytes ctx fc ds b3)
                (fc-g (fc-stream kind len bytes ctx) (fc-answer kind len bytes ctx) ds b3)))
  :hints (("Goal" :in-theory (enable fc-inv))))
(defthm fc-step-keeps-hashing-idle
  (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-idle*)
           (fc-inv-claim (fc-step-step) 1 2 5))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
     :use ((:instance fc-g-init (xs (fc-stream kind len bytes ctx)))
           fc-stream-shape)
     :in-theory (e/d (fn2-fc-step fc-inv-in-decode fc-answer fc-b3-init-key fc-phase-pos-updates
                      (:executable-counterpart fn2-digest-slot) (:executable-counterpart expt)
                      fc-zero-plus-len natp)
                     (mv-nth fc-inv)))))
(defthm fc-step-keeps-hashing-decode
  (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-decode*)
           (fc-inv-claim (fc-step-step) 1 2 5))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
     :use ((:instance fc-decoded-starts-hashing
             (next (mv-nth 1 (fn2-fc-decode-step kind base 0 1 0 (+ 0 len) 1 0 1 budget fields pool)))
             (fields (mv-nth 2 (fn2-fc-decode-step kind base 0 1 0 (+ 0 len) 1 0 1 budget fields pool)))))
     :in-theory (e/d (fn2-fc-step) (mv-nth fc-inv)))))
(defthm fc-step-keeps-hashing-run
  (implies (and (not (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-idle*))
                (not (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-decode*)))
           (fc-inv-claim (fc-step-step) 1 2 5))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
     :use ((:instance fc-run-keeps-hashing (fuel budget)))
     :in-theory (e/d (fn2-fc-step) (mv-nth fc-inv)))))
(defthm fc-step-keeps-hashing
  (fc-inv-claim (fc-step-step) 1 2 5)
  :rule-classes nil
  :hints (("Goal" :use (fc-step-keeps-hashing-idle fc-step-keeps-hashing-decode fc-step-keeps-hashing-run)
           :in-theory (theory 'minimal-theory))))
(defthm fc-reset-inv
  (fc-inv kind len bytes ctx (fn2-fc-reset 0 fc) ds b3)
  :hints (("Goal" :in-theory (enable fc-inv fn2-fc-reset fc-phase-pos-updates))))
(defmacro fc-format-step ()
  '(fn2-format-run kind nil 0 0 1 0 len base 1 0 1 budget fc ctx b3 fields pool ds))
(defthm fc-format-keeps-hashing
  (fc-inv-claim (fc-format-step) 1 2 5)
  :rule-classes nil
  :hints (("Goal" :use fc-step-keeps-hashing
                  :in-theory (e/d (fn2-format-run fc-reset-inv) (mv-nth fc-inv)))))
(defmacro fc-drive-step ()
  '(fn2-format-drive fuel 0 kind nil 0 1 0 len base 1 0 1 budget fc ctx b3 fields pool ds))
(defthm fc-drive-hashes-stream
  (let ((step (fc-drive-step)))
    (implies (and (not (eq kind :page)) (natp len) (fc-pool-holds bytes pool)
                  (implies (and (eq kind :frame) (equal len 4096)) (fn2-b3-windowp 4096 pool))
                  (fc-inv kind len bytes ctx fc ds b3) (eq (car step) :ok))
             (equal (fn2-digest-list 125 (mv-nth 5 step)) (fc-answer kind len bytes ctx))))
  :rule-classes nil
  :hints (("Goal" :induct (fc-drive-step) :expand (fc-drive-step)
                  :in-theory (e/d ((:induction fn2-format-drive)) (mv-nth fc-inv)))
          ("Subgoal *1/3" :use fc-format-keeps-hashing)
          ("Subgoal *1/2" :use fc-format-keeps-hashing)))
(defthm fc-spec-load-shape
  (implies (and (fn2-poolp pool) (fn2-pool-wfp pool))
           (and (fn2-poolp (fn2-fc-spec-load bytes i pool))
                (fn2-pool-wfp (fn2-fc-spec-load bytes i pool))))
  :hints (("Goal" :induct (fn2-fc-spec-load bytes i pool)
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-fc-spec-load (:induction fn2-fc-spec-load)
                          fn2-pool-write-preserves-type fn2-pool-write-preserves-wfp)))))
(defthm fc-image-pool-shape
  (implies (< (len bytes) 4294967296)
           (and (fn2-poolp (fc-image-pool bytes)) (fn2-pool-wfp (fc-image-pool bytes))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                        '(fc-image-pool fc-spec-load-shape fc-image-pool-profile fc-created-pool-type
                          fn2-pool-init-type fn2-pool-init-wfp
                          fn2-pool-reserve-preserves-type fn2-pool-reserve-preserves-wfp
                          (:executable-counterpart unsigned-byte-p) (:executable-counterpart <)
                          (:executable-counterpart not))))))
(defthm fc-accepted-pool-holds
  (implies (fn2-fc-acceptedp kind bytes ctx)
           (fc-pool-holds bytes (fc-image-pool bytes)))
  :rule-classes nil
  :hints (("Goal" :use (fc-accepted-length-bound fc-image-pool-shape
                        (:instance fc-accepted-pool-reads-input
                           (i (fc-pool-holds-witness bytes (fc-image-pool bytes))))
                        (:instance fn2-b3-read-byte (slot 0) (gen 1) (okind 1) (oslot 0) (ogen 1)
                           (off (fc-pool-holds-witness bytes (fc-image-pool bytes)))
                           (fn2-pool (fc-image-pool bytes))))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fc-pool-holds fn-b3-octet fn-b3-byte-of-octet unsigned-byte-p integer-range-p
                          (:executable-counterpart expt))))))
(defthm fc-window-write
  (implies (and (fn2-b3-windowp used pool) (<= used 4096))
           (let ((next (mv-nth 1 (fn2-pool-write 0 1 i b 1 0 1 pool))))
             (and (fn2-b3-windowp (fn2-pool-fill 0 next) next)
                  (<= (fn2-pool-fill 0 next) 4096))))
  :hints (("Goal" :in-theory (union-theories (current-theory 'fn2-b3-initial-window)
                     '(fn2-b3-windowp fn2-pool-write fn2-pool-workspace-code fn2-pool-handle-code
                       fn2-pool-readable-code fn2-pool-ownerp fn2-pool-datai update-fn2-pool-datai
                       fn2-pool-data-length)))))
(defun-nx fc-load-induct (bytes i used pool)
  (declare (xargs :hints (("Goal" :in-theory (current-theory 'fc-u32-reconstruct)))))
  (if (atom bytes) (list i used pool)
    (let ((w (fn2-pool-write 0 1 i (car bytes) 1 0 1 pool)))
      (if (eq (mv-nth 0 w) :ok)
          (fc-load-induct (cdr bytes) (+ 1 (nfix i)) (fn2-pool-fill 0 (mv-nth 1 w)) (mv-nth 1 w))
        nil))))
(defthm fc-window-load
  (implies (and (fn2-b3-windowp used pool) (<= used 4096))
           (let ((next (fn2-fc-spec-load bytes i pool)))
             (and (fn2-b3-windowp (fn2-pool-fill 0 next) next)
                  (<= (fn2-pool-fill 0 next) 4096))))
  :hints (("Goal" :induct (fc-load-induct bytes i used pool)
           :expand ((fn2-fc-spec-load bytes i pool))
           :in-theory (union-theories (theory 'minimal-theory)
                        '((:induction fc-load-induct) fn2-b3-windowp)))
          ("Subgoal *1/3" :use ((:instance fc-window-write (b (car bytes)))))
          ("Subgoal *1/2" :use ((:instance fc-window-write (b (car bytes)))))
          ("Subgoal *1/1" :use ((:instance fc-window-write (b (car bytes)))))))
(defthm fc-accepted-window
  (implies (and (fn2-fc-acceptedp kind bytes ctx) (not (eq kind :page)) (equal (len bytes) 4096))
           (fn2-b3-windowp 4096 (fc-image-pool bytes)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fc-image-drive-verifies-trailer (k 31))
                        (:instance fc-window-load (used 0) (i 0)
                           (pool (mv-nth 3 (fn2-pool-reserve 0 1 0 1
                                    (fn2-pool-init '((1 . 4096)) 1 100 (create-fn2-pool))))))
                        fn2-b3-initial-window fc-image-pool-shape
                        (:instance fn2-pool-fill-natp (i 0) (fn2-pool (fc-image-pool bytes))))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fc-image-pool fc-digest-match fn2-b3-read fn2-pool-read fn2-b3-windowp natp
                          (:executable-counterpart max) (:executable-counterpart cons)
                          (:executable-counterpart binary-+) (:executable-counterpart unary--)
                          (:executable-counterpart natp) (:executable-counterpart <)
                          (:executable-counterpart not) car-cons cdr-cons fc-mv-zero)))))
(defthm fc-initial-inv
  (fc-inv kind len bytes ctx (fn2-fc-init 1 (create-fn2-fc)) ds b3)
  :hints (("Goal" :in-theory (enable fc-inv fc-image-initially-idle))))
(defthm fc-accepted-digest
  (implies (and (fn2-fc-acceptedp kind bytes ctx) (not (eq kind :page)))
           (equal (fn2-digest-list 125 (mv-nth 5 (fc-image-drive kind bytes ctx)))
                  (fc-answer kind (len bytes) bytes (fc-image-context ctx))))
  :rule-classes nil
  :hints (("Goal" :use (fc-accepted-drive-ok fc-accepted-pool-holds fc-accepted-window
             (:instance fc-drive-hashes-stream
               (fuel (fn2-format-fuel (len bytes))) (len (len bytes)) (base 0) (budget 4096)
               (fc (fn2-fc-init 1 (create-fn2-fc))) (ctx (fc-image-context ctx))
               (b3 (fn2-b3-table-init 1 (create-fn2-b3)))
               (fields (fn2-fields-init *fn2-format-sealed-batch-num-fields* (create-fn2-fields)))
               (pool (fc-image-pool bytes))
               (ds (fc-expected-digests ctx (fn2-digests-init 144 (create-fn2-digests))))))
           :in-theory (union-theories (theory 'minimal-theory)
              '(fc-image-drive fc-initial-inv fc-length-natural)))))
