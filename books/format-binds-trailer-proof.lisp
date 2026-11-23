; The accepted image: trailer verification, pool contents, and the hashing invariant's setup.
; One link of the format-binds proof chain; events are exported so the next link sees the same world.
(in-package "ACL2")
(include-book "format-binds-b3-proof")


(defthm fc-expected-digests-overwrite
  (equal (fc-expected-digests b (fc-expected-digests a ds))
         (fc-expected-digests b ds))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                  (append '(update-nth-array nth-update-nth update-nth-of-update-nth-same
                            update-nth-of-update-nth-diff (:executable-counterpart nfix))
                          (theory 'fc-expected-digest-layout))))))
(defthm fc-adapter-digests
  (equal (mv-nth 1 (fn2-fc-spec-context ctx 0 carrier ds)) (fc-expected-digests ctx ds))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                   '(fn2-fc-spec-context fc-mv-second fc-expected-digests)))))
(defthm fc-adapter-context
  (equal (car (fn2-fc-spec-context ctx 0 (fn2-fc-context-init 1 (create-fn2-fc-context))
                                   (fn2-digests-init 144 (create-fn2-digests))))
         (fc-image-context ctx))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fc-image-context)))))

(defthm fc-u32-bytes-unique
  (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y)
                (equal (fn2-fc-word-byte x 0) (fn2-fc-word-byte y 0))
                (equal (fn2-fc-word-byte x 1) (fn2-fc-word-byte y 1))
                (equal (fn2-fc-word-byte x 2) (fn2-fc-word-byte y 2))
                (equal (fn2-fc-word-byte x 3) (fn2-fc-word-byte y 3)))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :use (fc-u32-reconstruct (:instance fc-u32-reconstruct (x y)))
                  :in-theory (theory 'minimal-theory))))

; During digest verification all positions below the cursor have matched.
; State the invariant for an arbitrary index to avoid rescanning the prefix.
(defmacro fc-check-input (i)
  `(fn2-b3-read slot gen (+ off (- len 32) ,i) okind oslot ogen pool))
(defun-nx fc-digest-match (k slot gen off len okind oslot ogen pool ds)
  (let ((input (fc-check-input k)))
    (and (eq (car input) :ok)
         (equal (mv-nth 1 input) (fn2-fc-digest-byte 0 k nil ds)))))
(defun-nx fc-digest-progress (k slot gen off len okind oslot ogen fc pool ds)
  (let ((phase (fn2-fc-phase 0 fc)) (pos (fn2-fc-pos 0 fc)))
    (and (implies (or (equal phase *fn2-fc-phase-prefix*)
                      (equal phase *fn2-fc-phase-hash*)
                      (equal phase *fn2-fc-phase-digest*))
                  (equal (fn2-fc-zero 0 fc) (- len 32)))
         (implies (equal phase *fn2-fc-phase-digest*)
                  (and (natp pos)
                       (or (<= pos k)
                           (fc-digest-match k slot gen off len okind oslot ogen pool ds)))))))
(defthm fc-zero-updates
  (and (equal (fn2-fc-zero 0 (fn2-fc-set-phase 0 v fc)) (fn2-fc-zero 0 fc))
       (equal (fn2-fc-zero 0 (fn2-fc-set-pos 0 v fc)) (fn2-fc-zero 0 fc))
       (equal (fn2-fc-zero 0 (fn2-fc-set-zero 0 v fc)) v)
       (equal (fn2-fc-zero 0 (fn2-fc-set-pad 0 v fc)) (fn2-fc-zero 0 fc))
       (equal (fn2-fc-zero 0 (fn2-fc-set-pad-end 0 v fc)) (fn2-fc-zero 0 fc)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             '(fn2-fc-zero fn2-fc-zero$ai fn2-fc-set-phase fn2-fc-set-pos
               fn2-fc-set-zero fn2-fc-set-pad fn2-fc-set-pad-end
               update-fn2-fc-phase$ai update-fn2-fc-pos$ai update-fn2-fc-zero$ai
               update-fn2-fc-pad$ai update-fn2-fc-pad-end$ai
               update-nth-array nth-update-nth (:executable-counterpart nfix))))))
(defmacro fc-progress-at (cursor data digests)
  `(fc-digest-progress k slot gen off len okind oslot ogen ,cursor ,data ,digests))
(defmacro fc-match-at (data digests)
  `(fc-digest-match k slot gen off len okind oslot ogen ,data ,digests))
(defmacro fc-digest-step-claim (call fc-index pool-index ds-index)
  `(let ((step ,call))
     (implies (and (not (eq kind :page)) (natp k) (< k 32)
                   (fc-progress-at fc pool ds))
              (and (implies (eq (car step) :ok)
                            (fc-match-at (mv-nth ,pool-index step) (mv-nth ,ds-index step)))
                   (implies (or (eq (car step) :more) (eq (car step) :yield))
                            (fc-progress-at (mv-nth ,fc-index step)
                                            (mv-nth ,pool-index step) (mv-nth ,ds-index step)))))))
(defthm fc-byte-verifies-trailer
  (fc-digest-step-claim
    (fn2-fc-byte 0 kind nil slot gen off len base okind oslot ogen fc ctx b3 fields pool ds) 1 3 4)
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
          :in-theory (e/d (fn2-fc-byte fc-digest-progress fc-digest-match fc-phase-pos-updates
                           fc-zero-updates fn2-fc-digest-byte fc-pending-after-increment
                           (:executable-counterpart natp) natp)
                          (mv-nth)))))

(defthm fc-span-keeps-cursor-layout
  (let ((step (fn2-fc-page-span fuel 0 slot gen off end base okind oslot ogen
                                fc ctx b3 fields pool ds)))
    (and (not (eq (car step) :ok))
         (equal (fn2-fc-zero 0 (mv-nth 2 step)) (fn2-fc-zero 0 fc))
         (equal (fn2-fc-phase 0 (mv-nth 2 step)) (fn2-fc-phase 0 fc))))
  :hints (("Goal" :do-not '(preprocess)
                  :in-theory (e/d (fn2-fc-page-span fc-zero-updates fc-phase-pos-updates)
                                  (mv-nth fn2-fc-zero fn2-fc-phase)))))
(defthm fc-hashing-progress
  (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-hash*)
           (equal (fc-progress-at fc pool ds)
                  (equal (fn2-fc-zero 0 fc) (- len 32))))
  :hints (("Goal" :in-theory (enable fc-digest-progress))))
(defmacro fc-advance-trailer ()
  '(fn2-fc-advance fuel 0 kind nil slot gen off len base okind oslot ogen
                   fc ctx b3 fields pool ds))
(defthm fc-advance-verifies-trailer
  (fc-digest-step-claim (fc-advance-trailer) 2 4 5)
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
     :use (fc-byte-verifies-trailer
           (:instance fc-byte-verifies-trailer
             (fc (mv-nth 2 (fn2-fc-page-span fuel 0 slot gen off
                   (if (eq kind :frame) (min len (fn2-fc-pad-end 0 fc)) len)
                   base okind oslot ogen fc ctx b3 fields pool ds)))
             (b3 (mv-nth 3 (fn2-fc-page-span fuel 0 slot gen off
                   (if (eq kind :frame) (min len (fn2-fc-pad-end 0 fc)) len)
                   base okind oslot ogen fc ctx b3 fields pool ds)))
             (ds (mv-nth 4 (fn2-fc-page-span fuel 0 slot gen off
                   (if (eq kind :frame) (min len (fn2-fc-pad-end 0 fc)) len)
                   base okind oslot ogen fc ctx b3 fields pool ds)))))
     :in-theory (e/d (fn2-fc-advance fc-span-keeps-cursor-layout fc-hashing-progress)
                     (mv-nth fc-digest-match fc-digest-progress)))))
(defmacro fc-run-trailer ()
  '(fn2-fc-run-bytes fuel 0 kind nil slot gen off len base okind oslot ogen
                     fc ctx b3 fields pool ds))
(defthm fc-run-verifies-trailer
  (fc-digest-step-claim (fc-run-trailer) 1 3 4)
  :rule-classes nil
  :hints (("Goal" :induct (fc-run-trailer) :expand (fc-run-trailer)
                  :in-theory (e/d ((:induction fn2-fc-run-bytes))
                                  (mv-nth fc-digest-progress fc-digest-match)))
          ("Subgoal *1/3" :use fc-advance-verifies-trailer)
          ("Subgoal *1/2" :use fc-advance-verifies-trailer)))
(defthm fc-identity-never-more
  (not (equal (fn2-fc-identity row kind base len ctx fields) :more))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn2-fc-identity)))))
(defthm fc-decoded-starts-trailer
  (let ((step (fn2-fc-decoded 0 kind off len base next fc ctx b3 fields pool ds)))
    (implies (not (eq kind :page))
             (and (not (eq (car step) :ok))
                  (implies (eq (car step) :more)
                           (fc-progress-at (mv-nth 1 step) pool ds)))))
  :hints (("Goal" :in-theory (e/d (fn2-fc-decoded fc-digest-progress fc-phase-pos-updates
                                   fc-zero-updates fc-identity-never-more)
                                  (mv-nth fn2-fc-phase fn2-fc-zero)))))
(defthm fc-start-progress
  (fc-progress-at (fn2-fc-set-phase 0 *fn2-fc-phase-decode* fc) pool ds)
  :hints (("Goal" :in-theory (enable fc-phase-pos-updates fc-digest-progress))))
(defthm fc-decoded-never-yields
  (not (equal (car (fn2-fc-decoded 0 kind off len base next fc ctx b3 fields pool ds)) :yield))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                            '(fn2-fc-decoded fn2-fc-identity car-cons)))))
(defmacro fc-step-trailer ()
  '(fn2-fc-step 0 kind nil slot gen off len base okind oslot ogen budget
                fc ctx b3 fields pool ds))
(defthm fc-step-verifies-trailer
  (fc-digest-step-claim (fc-step-trailer) 1 4 5)
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :use ((:instance fc-run-verifies-trailer (fuel budget))
                       (:instance fc-decoded-starts-trailer
                        (next (mv-nth 1 (fn2-fc-decode-step kind base slot gen off (+ off len)
                                                    okind oslot ogen budget fields pool)))
                        (fields (mv-nth 2 (fn2-fc-decode-step kind base slot gen off (+ off len)
                                                    okind oslot ogen budget fields pool)))))
                  :in-theory (e/d (fn2-fc-step fc-start-progress fc-decoded-never-yields)
                                  (mv-nth fc-digest-progress fc-digest-match)))))
(defmacro fc-format-trailer ()
  '(fn2-format-run kind nil 0 slot gen off len base okind oslot ogen budget
                   fc ctx b3 fields pool ds))
(defthm fc-reset-progress
  (fc-progress-at (fn2-fc-reset 0 fc) pool ds)
  :hints (("Goal" :in-theory (enable fn2-fc-reset fc-phase-pos-updates fc-digest-progress))))
(defthm fc-format-verifies-trailer
  (fc-digest-step-claim (fc-format-trailer) 1 4 5)
  :rule-classes nil
  :hints (("Goal" :use fc-step-verifies-trailer
                  :in-theory (e/d (fn2-format-run fc-reset-progress)
                                  (mv-nth fc-digest-progress fc-digest-match)))))
(defmacro fc-drive-trailer ()
  '(fn2-format-drive fuel 0 kind nil slot gen off len base okind oslot ogen budget
                     fc ctx b3 fields pool ds))
(defthm fc-drive-verifies-trailer
  (let ((step (fc-drive-trailer)))
    (implies (and (not (eq kind :page)) (natp k) (< k 32)
                  (fc-progress-at fc pool ds) (eq (car step) :ok))
             (fc-match-at (mv-nth 4 step) (mv-nth 5 step))))
  :rule-classes nil
  :hints (("Goal" :induct (fc-drive-trailer) :expand (fc-drive-trailer)
                  :in-theory (e/d ((:induction fn2-format-drive))
                                  (mv-nth fc-digest-progress fc-digest-match)))
          ("Subgoal *1/3" :use fc-format-verifies-trailer)
          ("Subgoal *1/2" :use fc-format-verifies-trailer)))

(defmacro fc-reservation (bytes)
  `(fn2-pool-reserve 0 1 0 1
      (fn2-pool-init (list (cons 1 (max 1 (len ,bytes)))) 1 100 (create-fn2-pool))))
(defun-nx fc-image-pool (bytes)
  (fn2-fc-spec-load bytes 0 (mv-nth 3 (fc-reservation bytes))))
(defun-nx fc-image-drive (kind bytes ctx)
  (fn2-format-drive (fn2-format-fuel (len bytes)) 0 kind nil 0 1 0 (len bytes) 0 1 0 1 4096
    (fn2-fc-init 1 (create-fn2-fc)) (fc-image-context ctx)
    (fn2-b3-table-init 1 (create-fn2-b3))
    (fn2-fields-init *fn2-format-sealed-batch-num-fields* (create-fn2-fields))
    (fc-image-pool bytes) (fc-expected-digests ctx (fn2-digests-init 144 (create-fn2-digests)))))
(defthm fc-accepted-drive-ok
  (implies (fn2-fc-acceptedp kind bytes ctx) (equal (car (fc-image-drive kind bytes ctx)) :ok))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
        '(fn2-fc-acceptedp fn2-fc-image fn2-fc-image-run fc-image-drive fc-image-pool
          fc-adapter-context fc-adapter-digests fc-mv-zero fc-mv-cons
          (:executable-counterpart zp) car-cons)))))
(defmacro fc-read-only (name call index &optional recursive)
  `(defthm ,name
     (equal (mv-nth ,index ,call) pool)
     :hints (("Goal" ,@(and recursive (list :induct call :expand call))
              :in-theory (e/d (,(if recursive (list :induction (car call)) (car call))) (mv-nth))))))
(fc-read-only fc-byte-keeps-pool
  (fn2-fc-byte 0 kind nil slot gen off len base okind oslot ogen fc ctx b3 fields pool ds) 3)
(fc-read-only fc-advance-keeps-pool
  (fn2-fc-advance fuel 0 kind nil slot gen off len base okind oslot ogen fc ctx b3 fields pool ds) 4)
(fc-read-only fc-run-keeps-pool
  (fn2-fc-run-bytes fuel 0 kind nil slot gen off len base okind oslot ogen fc ctx b3 fields pool ds) 3 t)
(fc-read-only fc-step-keeps-pool
  (fn2-fc-step 0 kind nil slot gen off len base okind oslot ogen budget fc ctx b3 fields pool ds) 4)
(fc-read-only fc-format-keeps-pool
  (fn2-format-run kind nil 0 slot gen off len base okind oslot ogen budget fc ctx b3 fields pool ds) 4)
(fc-read-only fc-drive-keeps-pool
  (fn2-format-drive fuel 0 kind nil slot gen off len base okind oslot ogen budget fc ctx b3 fields pool ds) 4 t)
(defthm fc-initial-progress
  (fc-progress-at (fn2-fc-init 1 (create-fn2-fc)) pool ds)
  :hints (("Goal" :in-theory (enable fc-digest-progress fc-image-initially-idle))))
(defthm fc-image-drive-verifies-trailer
  (implies (and (not (eq kind :page)) (natp k) (< k 32) (fn2-fc-acceptedp kind bytes ctx))
           (fc-digest-match k 0 1 0 (len bytes) 1 0 1 (fc-image-pool bytes)
                            (mv-nth 5 (fc-image-drive kind bytes ctx))))
  :rule-classes nil
  :hints (("Goal" :use (fc-accepted-drive-ok (:instance fc-drive-verifies-trailer
             (fuel (fn2-format-fuel (len bytes))) (slot 0) (gen 1) (off 0) (len (len bytes))
             (base 0) (okind 1) (oslot 0) (ogen 1) (budget 4096)
             (fc (fn2-fc-init 1 (create-fn2-fc))) (ctx (fc-image-context ctx))
             (b3 (fn2-b3-table-init 1 (create-fn2-b3)))
             (fields (fn2-fields-init *fn2-format-sealed-batch-num-fields* (create-fn2-fields)))
             (pool (fc-image-pool bytes))
             (ds (fc-expected-digests ctx (fn2-digests-init 144 (create-fn2-digests))))))
            :in-theory (union-theories (theory 'minimal-theory)
               '(fc-image-drive fc-drive-keeps-pool fc-initial-progress (:executable-counterpart natp))))))

; The fixture loader appends until its first refusal. A successful read below
; the resulting fill therefore refers to an input byte that was written.
(defmacro fc-put-input ()
  '(fn2-pool-write 0 1 i byte 1 0 1 pool))
(defthm fc-write-input-effects
  (let ((next (mv-nth 1 (fc-put-input))))
    (implies (and (equal (car (fc-put-input)) :ok) (equal (fn2-pool-fill 0 pool) i))
      (and (equal (fn2-pool-fill 0 next) (1+ i))
           (equal (fn2-pool-base 0 next) (fn2-pool-base 0 pool))
           (equal (fn2-pool-datai p next)
                  (if (equal (nfix p) (nfix (+ (fn2-pool-base 0 pool) i)))
                      byte (fn2-pool-datai p pool))))))
  :hints (("Goal" :in-theory (union-theories (theory 'fc-hash-rules)
            '(fn2-pool-write fn2-pool-set-fill update-fn2-pool-fill$ai update-fn2-pool-datai
              fn2-pool-fill fn2-pool-fill$ai fn2-pool-base fn2-pool-base$ai fn2-pool-datai
              update-nth-array nth-update-nth max natp (:executable-counterpart nfix))))))
(defun-nx fc-input-octet (k pool)
  (fn2-pool-datai (+ (fn2-pool-base 0 pool) k) pool))
(defthm fc-write-input-octet
  (implies (and (equal (car (fc-put-input)) :ok)
                (natp (fn2-pool-base 0 pool)) (equal (fn2-pool-fill 0 pool) i)
                (natp k) (natp i))
           (equal (fc-input-octet k (mv-nth 1 (fc-put-input)))
                  (if (equal k i) byte (fc-input-octet k pool))))
  :hints (("Goal" :in-theory (e/d (fc-input-octet fc-write-input-effects natp nfix) (mv-nth)))))
(defthm fc-nth-from-input-offset
  (implies (and (consp bytes) (natp k) (natp i) (<= i k))
           (equal (nth (- k i) bytes)
                  (if (equal i k) (car bytes) (nth (- k (1+ i)) (cdr bytes)))))
  :hints (("Goal" :expand (nth (- k i) bytes)
                  :in-theory (union-theories (current-theory 'fc-u32-reconstruct) '(nth)))))
(defthm fc-refused-write-keeps-pool
  (implies (not (eq (car (fc-put-input)) :ok))
           (equal (mv-nth 1 (fc-put-input)) pool))
  :hints (("Goal" :in-theory (e/d (fn2-pool-write) (mv-nth)))))
(defthm fc-loaded-input-byte
  (let ((loaded (fn2-fc-spec-load bytes i pool)))
   (implies (and (natp i) (natp k) (natp (fn2-pool-base 0 pool))
                 (equal (fn2-pool-fill 0 pool) i)
                 (< k (fn2-pool-fill 0 loaded)))
            (equal (fc-input-octet k loaded)
                   (if (< k i) (fc-input-octet k pool) (nth (- k i) bytes)))))
  :hints (("Goal" :induct (fn2-fc-spec-load bytes i pool)
                  :expand (:free (i) (fn2-fc-spec-load bytes i pool))
                  :in-theory (e/d (fn2-fc-spec-load fc-refused-write-keeps-pool fc-nth-from-input-offset fc-write-input-effects fc-write-input-octet
                                   natp nfix zp)
                                  (fc-input-octet mv-nth fn2-pool-fill fn2-pool-base)))
          ("Subgoal *1/2" :use ((:instance fc-write-input-effects (byte (car bytes)))
                                (:instance fc-write-input-octet (byte (car bytes)))))))

(defthm fc-initial-drive-length-bound
  (implies (and (natp len) (<= 4294967296 len))
           (not (equal (car (fn2-format-drive fuel 0 kind nil 0 1 0 len 0 1 0 1 4096
                                            fc ctx b3 fields pool ds)) :ok)))
  :hints (("Goal" :expand (fn2-format-drive fuel 0 kind nil 0 1 0 len 0 1 0 1 4096
                                            fc ctx b3 fields pool ds)
                  :in-theory (e/d (fn2-format-run fn2-fc-step fc-zero-plus-len)
                                  (mv-nth)))))
(defthm fc-accepted-length-bound
  (implies (fn2-fc-acceptedp kind bytes ctx) (< (len bytes) 4294967296))
  :rule-classes nil
  :hints (("Goal" :use fc-accepted-drive-ok
                  :in-theory (enable fc-image-drive fc-initial-drive-length-bound fc-length-natural))))
(defthm fc-image-pool-profile
  (implies (< (len bytes) 4294967296)
           (fn2-pool-profilep (list (cons 1 (max 1 (len bytes))))))
  :hints (("Goal" :in-theory (current-theory 'fc-u32-reconstruct))))
(defthm fc-reserved-slot-initial
  (let ((r (fn2-pool-reserve 0 1 0 1 pool)))
    (implies (and (equal (car r) :ok) (equal (mv-nth 1 r) 0))
             (and (equal (fn2-pool-fill 0 (mv-nth 3 r)) 0)
                  (< 0 (fn2-pool-rows pool))
                  (equal (fn2-pool-base 0 (mv-nth 3 r)) (fn2-pool-base 0 pool)))))
  :hints (("Goal" :do-not '(preprocess)
    :in-theory (union-theories (theory 'fc-hash-rules)
      '(fn2-pool-reserve fn2-pool-reserve-body fn2-pool-fill fn2-pool-fill$ai
        fn2-pool-base fn2-pool-base$ai fn2-pool-set-state fn2-pool-set-owner-kind
        fn2-pool-set-owner-slot fn2-pool-set-owner-gen fn2-pool-set-out-count
        fn2-pool-set-query-ref-count fn2-pool-set-fill
        update-fn2-pool-state$ai update-fn2-pool-owner-kind$ai
        update-fn2-pool-owner-slot$ai update-fn2-pool-owner-gen$ai update-fn2-pool-out-count$ai
        update-fn2-pool-query-ref-count$ai update-fn2-pool-fill$ai
        update-fn2-pool-class-headsi update-fn2-pool-class-countsi
        update-nth-array nth-update-nth)))))
(defthm fc-accepted-reservation
  (implies (fn2-fc-acceptedp kind bytes ctx)
           (and (equal (car (fc-reservation bytes)) :ok)
                (equal (mv-nth 1 (fc-reservation bytes)) 0)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
       '(fn2-fc-acceptedp fn2-fc-image fn2-fc-image-run fc-mv-cons fc-mv-zero
         car-cons (:executable-counterpart zp))))))
(defthm fc-created-pool-type
  (fn2-poolp (create-fn2-pool))
  :hints (("Goal" :in-theory (current-theory 'fc-u32-reconstruct))))
(defthm fc-accepted-load-start
  (implies (fn2-fc-acceptedp kind bytes ctx)
           (and (natp (fn2-pool-base 0 (mv-nth 3 (fc-reservation bytes))))
                (equal (fn2-pool-fill 0 (mv-nth 3 (fc-reservation bytes))) 0)))
  :rule-classes nil
  :hints (("Goal" :use (fc-accepted-length-bound fc-accepted-reservation
             (:instance fc-reserved-slot-initial
              (pool (fn2-pool-init (list (cons 1 (max 1 (len bytes)))) 1 100 (create-fn2-pool))))
             (:instance fn2-pool-base-natp (i 0)
              (fn2-pool (fn2-pool-init (list (cons 1 (max 1 (len bytes)))) 1 100 (create-fn2-pool)))))
           :in-theory (union-theories (theory 'minimal-theory)
             '(fc-image-pool-profile fn2-pool-init-type fn2-pool-init-wfp
               fc-created-pool-type (:executable-counterpart <) (:executable-counterpart not)
               (:executable-counterpart unsigned-byte-p) (:executable-counterpart natp))))))
(defthm fc-accepted-pool-reads-input
  (let ((read (fn2-b3-read 0 1 i 1 0 1 (fc-image-pool bytes))))
    (implies (and (fn2-fc-acceptedp kind bytes ctx) (eq (car read) :ok))
             (equal (mv-nth 1 read) (nth i bytes))))
  :rule-classes nil
  :hints (("Goal" :use (fc-accepted-load-start
              (:instance fc-loaded-input-byte (k i) (i 0)
                         (pool (mv-nth 3 (fc-reservation bytes)))))
                  :in-theory (e/d (fc-image-pool fc-input-octet fn2-b3-read fn2-pool-read natp commutativity-of-+ fc-zero-plus-len)
                                  (mv-nth fn2-pool-datai fn2-pool-base fn2-pool-fill)))))

(defthm fc-accepted-result-byte
  (implies (and (fn2-fc-acceptedp kind bytes ctx) (not (eq kind :page)) (natp k) (< k 32))
           (equal (fn2-fc-digest-byte 0 k nil (mv-nth 5 (fc-image-drive kind bytes ctx)))
                  (nth (+ 0 (- (len bytes) 32) k) bytes)))
  :rule-classes nil
  :hints (("Goal" :use (fc-image-drive-verifies-trailer
                         (:instance fc-accepted-pool-reads-input (i (+ 0 (- (len bytes) 32) k))))
                  :in-theory (union-theories (theory 'minimal-theory) '(fc-digest-match)))))
(defthm fc-accepted-trailer-length
  (implies (and (fn2-fc-acceptedp kind bytes ctx) (not (eq kind :page)))
           (<= 32 (len bytes)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fc-image-drive-verifies-trailer (k 0)))
                  :in-theory (e/d (fc-digest-match fn2-b3-read fn2-pool-read natp
                                   (:executable-counterpart natp))
                                  (mv-nth fc-image-drive fc-image-pool)))))
(defun-nx fc-result-octets (k n ds)
  (declare (xargs :measure (nfix n)
                  :hints (("Goal" :in-theory (current-theory 'fc-u32-reconstruct)))))
  (if (zp n) nil
    (cons (fn2-fc-digest-byte 0 k nil ds) (fc-result-octets (1+ k) (1- n) ds))))
(defthm fc-take-at-index
  (implies (and (posp n) (natp i))
           (equal (take n (nthcdr i bytes))
                  (cons (nth i bytes) (take (1- n) (nthcdr (1+ i) bytes)))))
  :rule-classes nil
  :hints (("Goal" :induct (nthcdr i bytes)
                  :in-theory (current-theory 'fc-u32-reconstruct))))
(defthm fc-result-octets-are-trailer
  (implies (and (fn2-fc-acceptedp kind bytes ctx) (not (eq kind :page))
                (natp n) (natp k) (equal (+ k n) 32))
           (equal (fc-result-octets k n (mv-nth 5 (fc-image-drive kind bytes ctx)))
                  (take n (nthcdr (+ (- (len bytes) 32) k) bytes))))
  :rule-classes nil
  :hints (("Goal" :induct (fc-result-octets k n ds)
                  :in-theory (union-theories (theory 'minimal-theory)
                     '(fc-result-octets (:induction fc-result-octets) take zp natp
                       car-cons cdr-cons (:executable-counterpart zp))))
          ("Subgoal *1/2" :use (fc-accepted-result-byte fc-accepted-trailer-length
                      (:instance fc-take-at-index (i (+ (- (len bytes) 32) k))))
                  :in-theory (union-theories '(fc-result-octets) (set-difference-theories (current-theory 'fc-u32-reconstruct) '(fn2-fc-acceptedp mv-nth take nthcdr nth))))))

(defthm fc-frame-header-allocation
  (implies (and (fn2-fc-acceptedp :frame bytes a) (fn2-fc-acceptedp :frame bytes b))
           (and (equal (fn2-fc-expected-extent-writer-epoch a) (fn2-fc-expected-extent-writer-epoch b))
                (equal (fn2-fc-expected-allocation a) (fn2-fc-expected-allocation b))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fc-accepted-binds-header (context a) (kind :frame))
                        (:instance fc-accepted-binds-header (context b) (kind :frame)))
                  :in-theory (union-theories (theory 'minimal-theory) '(fn2-fc-identity fc-image-context-scalars)))))
(defthm fc-seal-header-predecessor-commit
  (implies (and (fn2-fc-acceptedp :seal bytes a) (fn2-fc-acceptedp :seal bytes b))
           (equal (fn2-fc-expected-previous-commit a) (fn2-fc-expected-previous-commit b)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fc-accepted-binds-header (context a) (kind :seal))
                        (:instance fc-accepted-binds-header (context b) (kind :seal)))
                  :in-theory (union-theories (theory 'minimal-theory) '(fn2-fc-identity fc-image-context-scalars)))))
(defthm fc-seal-covered-binds-padded-body
  (implies (and (fn2-fc-expectedp ca) (fn2-fc-expectedp cb)
                (equal (fn2-fc-covered :seal a ca) (fn2-fc-covered :seal b cb)))
           (equal (append (take (nfix (- (len a) 32)) a) (make-list 32 :initial-element 0))
                  (append (take (nfix (- (len b) 32)) b) (make-list 32 :initial-element 0))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn2-fc-covered fn2-fc-expectedp fc-append-associative
                fc-cancel-common-prefix fc-eight-byte-fields-injective)))))
(defthm fc-prefix-length
  (equal (len (append (take n x) suffix)) (+ (nfix n) (len suffix)))
  :hints (("Goal" :in-theory (current-theory 'fc-u32-reconstruct))))
(defthm fc-cancel-fixed-tail
  (equal (take n (append (take n x) suffix)) (take n x))
  :hints (("Goal" :induct (take n x) :in-theory (current-theory 'fc-u32-reconstruct))))
(defthm fc-rejoin-at
  (implies (and (natp n) (<= n (len x))) (equal (append (take n x) (nthcdr n x)) x))
  :hints (("Goal" :induct (take n x) :in-theory (current-theory 'fc-u32-reconstruct))))
(defthm fc-rejoin-identical-images
  (implies (and (natp i) (natp j) (<= i (len a)) (<= j (len b))
                (equal (append (take i a) suffix) (append (take j b) suffix))
                (equal (nthcdr i a) (nthcdr j b)))
           (equal a b))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fc-prefix-length (n i) (x a))
                        (:instance fc-prefix-length (n j) (x b))
                        (:instance fc-cancel-fixed-tail (n i) (x a))
                        (:instance fc-cancel-fixed-tail (n j) (x b))
                        (:instance fc-rejoin-at (n i) (x a))
                        (:instance fc-rejoin-at (n j) (x b)))
                  :in-theory (union-theories (theory 'minimal-theory) '(nfix natp)))))
(defthm fc-seal-covered-and-trailer-bind-image
  (implies (and (fn2-fc-expectedp ca) (fn2-fc-expectedp cb)
                (equal (fn2-fc-covered :seal a ca) (fn2-fc-covered :seal b cb))
                (equal (nthcdr (nfix (- (len a) 32)) a) (nthcdr (nfix (- (len b) 32)) b)))
           (equal a b))
  :rule-classes nil
  :hints (("Goal" :use (fc-seal-covered-binds-padded-body
                   (:instance fc-rejoin-identical-images (i (nfix (- (len a) 32)))
                       (j (nfix (- (len b) 32))) (suffix (make-list 32 :initial-element 0))))
                  :in-theory (union-theories (theory 'minimal-theory)
                    '(fc-length-natural natp nfix (:type-prescription len))))))

; ---- the checker hashes the covered stream ----
(defun fc-plen (kind)
  (+ (length (fn2-fc-domain kind)) (case kind (:frame 24) (:seal 40) (otherwise 0))))
(defun-nx fc-prefix-from (pos n kind ctx)
  (declare (xargs :measure (nfix (- n pos))
                  :hints (("Goal" :in-theory (current-theory 'fc-u32-reconstruct)))))
  (if (and (natp pos) (natp n) (< pos n))
      (cons (fn2-fc-prefix-byte 0 kind pos ctx) (fc-prefix-from (1+ pos) n kind ctx))
    nil))
(defun fc-body-from (pos len bytes)
  (declare (xargs :measure (nfix (- len pos))
                  :hints (("Goal" :in-theory (current-theory 'fc-u32-reconstruct)))))
  (if (and (natp pos) (natp len) (< pos len))
      (cons (if (<= (- len 32) pos) 0 (fn-b3-octet (nth pos bytes)))
            (fc-body-from (1+ pos) len bytes))
    nil))
(defun-nx fc-stream (kind len bytes ctx)
  (append (fc-prefix-from 0 (fc-plen kind) kind ctx) (fc-body-from 0 len bytes)))
(defun-nx fc-answer (kind len bytes ctx)
  (fn2-b3-output-words (fn-b3-node *fn-b3-iv* (fc-stream kind len bytes ctx) 0 0) t))
(defun-sk fc-pool-holds (bytes pool)
  (forall k (implies (equal (car (fn2-b3-read 0 1 k 1 0 1 pool)) :ok)
                     (equal (mv-nth 1 (fn2-b3-read 0 1 k 1 0 1 pool))
                            (fn-b3-octet (nth k bytes))))))
(defun-nx fc-inv (kind len bytes ctx fc ds b3)
  (let ((phase (fn2-fc-phase 0 fc)) (pos (fn2-fc-pos 0 fc))
        (ans (fc-answer kind len bytes ctx)))
    (and (implies (equal phase *fn2-fc-phase-decode*)
                  (fc-g (fc-stream kind len bytes ctx) ans ds b3))
         (implies (or (equal phase *fn2-fc-phase-prefix*) (equal phase *fn2-fc-phase-hash*))
                  (and (natp pos) (equal (fn2-fc-zero 0 fc) (- len 32))
                       (implies (eq kind :frame)
                                (and (equal len 4096) (equal (fn2-fc-pad-end 0 fc) 4063)))))
         (implies (equal phase *fn2-fc-phase-prefix*)
                  (fc-g (append (fc-prefix-from pos (fc-plen kind) kind ctx)
                                (fc-body-from 0 len bytes)) ans ds b3))
         (implies (equal phase *fn2-fc-phase-hash*)
                  (fc-g (fc-body-from pos len bytes) ans ds b3))
         (implies (equal phase *fn2-fc-phase-digest*)
                  (equal (fn2-digest-list 125 ds) ans)))))
(in-theory (disable fc-prefix-from fc-body-from fc-stream fc-answer fc-pool-holds fc-pool-holds-necc fc-inv fc-plen))
(defthm fc-pad-end-updates
  (and (equal (fn2-fc-pad-end 0 (fn2-fc-set-phase 0 v fc)) (fn2-fc-pad-end 0 fc))
       (equal (fn2-fc-pad-end 0 (fn2-fc-set-pos 0 v fc)) (fn2-fc-pad-end 0 fc))
       (equal (fn2-fc-pad-end 0 (fn2-fc-set-pad-end 0 v fc)) v))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             '(fn2-fc-pad-end fn2-fc-pad-end$ai fn2-fc-set-phase fn2-fc-set-pos fn2-fc-set-pad-end
               update-fn2-fc-phase$ai update-fn2-fc-pos$ai update-fn2-fc-pad-end$ai
               update-nth-array nth-update-nth (:executable-counterpart nfix))))))
(defmacro fc-inv-claim (call fc-index b3-index ds-index &rest hyps)
  `(let ((step ,call))
     (implies (and (not (eq kind :page)) (natp len) (fc-pool-holds bytes pool)
                   (implies (and (eq kind :frame) (equal len 4096)) (fn2-b3-windowp 4096 pool))
                   ,@hyps
                   (fc-inv kind len bytes ctx fc ds b3))
              (and (implies (eq (car step) :ok)
                            (equal (fn2-digest-list 125 (mv-nth ,ds-index step))
                                   (fc-answer kind len bytes ctx)))
                   (implies (or (eq (car step) :more) (eq (car step) :yield))
                            (fc-inv kind len bytes ctx (mv-nth ,fc-index step)
                                    (mv-nth ,ds-index step) (mv-nth ,b3-index step)))))))
(defthm fc-prefix-from-end
  (implies (<= n pos) (equal (fc-prefix-from pos n kind ctx) nil))
  :hints (("Goal" :expand ((fc-prefix-from pos n kind ctx)))))
(defthm fc-body-from-end
  (implies (<= len pos) (equal (fc-body-from pos len bytes) nil))
  :hints (("Goal" :expand ((fc-body-from pos len bytes)))))
(defthm fc-append-nil-left (equal (append nil x) x)
  :hints (("Goal" :in-theory (enable append))))
(defthm fc-append-cons (equal (append (cons a x) y) (cons a (append x y)))
  :hints (("Goal" :in-theory (enable append))))

(in-theory (disable fc-pending-after-increment))
(defthm fc-byte-in-prefix
  (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-prefix*)
   (equal (fn2-fc-byte 0 kind sealp slot gen off len base okind oslot ogen fc ctx b3 fields pool ds)
          (if (>= (fn2-fc-pos 0 fc) (fc-plen kind))
              (mv :more (fn2-fc-set-phase 0 *fn2-fc-phase-hash* (fn2-fc-set-pos 0 0 fc)) b3 pool ds)
            (mv :more (fn2-fc-set-pos 0 (+ 1 (fn2-fc-pos 0 fc)) fc)
                (mv-nth 1 (fn2-b3-byte 0 (fn2-fc-prefix-byte 0 kind (fn2-fc-pos 0 fc) ctx) ds b3))
                pool
                (mv-nth 0 (fn2-b3-byte 0 (fn2-fc-prefix-byte 0 kind (fn2-fc-pos 0 fc) ctx) ds b3))))))
  :hints (("Goal" :in-theory (e/d (fn2-fc-byte fc-plen) (mv-nth)))))

(defthm fc-byte-in-hash
  (implies (and (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-hash*) (not (eq kind :page)))
   (equal (fn2-fc-byte 0 kind nil slot gen off len base okind oslot ogen fc ctx b3 fields pool ds)
    (let ((pos (fn2-fc-pos 0 fc)) (zero (fn2-fc-zero 0 fc)))
     (if (>= pos len)
         (mv :more (fn2-fc-set-pos 0 0 (fn2-fc-set-phase 0 *fn2-fc-phase-digest* fc)) b3 pool
             (fn2-b3-finalize 125 0 ds b3))
       (let ((rd (fn2-b3-read slot gen (+ off pos) okind oslot ogen pool)))
         (if (not (eq (car rd) :ok)) (mv (car rd) fc b3 pool ds)
           (let ((code (fn2-fc-check-byte 0 kind off pos (mv-nth 1 rd) fc ctx ds)))
             (if (not (eq code :ok)) (mv code fc b3 pool ds)
               (let ((r (fn2-b3-byte 0 (if (and (<= zero pos) (< pos (+ zero 32))) 0 (mv-nth 1 rd)) ds b3)))
                 (mv :more (fn2-fc-set-pos 0 (+ 1 pos) fc) (mv-nth 1 r) pool (mv-nth 0 r)))))))))))
  :hints (("Goal" :in-theory (e/d (fn2-fc-byte) (mv-nth)))))
(defthm fc-byte-in-digest
  (implies (and (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-digest*) (not (eq kind :page)))
   (let ((r (fn2-fc-byte 0 kind nil slot gen off len base okind oslot ogen fc ctx b3 fields pool ds)))
     (and (equal (mv-nth 4 r) ds) (equal (mv-nth 2 r) b3)
          (equal (fn2-fc-phase 0 (mv-nth 1 r)) *fn2-fc-phase-digest*))))
  :hints (("Goal" :in-theory (e/d (fn2-fc-byte fc-phase-pos-updates) (mv-nth)))))
(defthm fc-byte-in-other
  (implies (and (not (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-prefix*))
                (not (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-hash*))
                (not (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-digest*)))
   (equal (car (fn2-fc-byte 0 kind sealp slot gen off len base okind oslot ogen fc ctx b3 fields pool ds))
          :state))
  :hints (("Goal" :in-theory (e/d (fn2-fc-byte) (mv-nth)))))
