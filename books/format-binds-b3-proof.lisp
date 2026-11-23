; Streaming BLAKE3 equals fn-blake3; decoded header binding; expected-digest overlay.
; One link of the format-binds proof chain; events are exported so the next link sees the same world.
(in-package "ACL2")
(include-book "format-binds-base-proof")

(defun fn2-b3-match (buf xs root answer fn2-digests fn2-b3)
 (declare (xargs :stobjs (fn2-digests fn2-b3) :verify-guards nil))
 (let ((cv (fn2-digest-list 0 fn2-digests)) (depth (fn2-b3-depth 0 fn2-b3))
       (org (fn2-b3-origin 0 fn2-b3)) (ctr (fn2-b3-counter 0 fn2-b3))
       (j (fn2-b3-blocks 0 fn2-b3)) (pos (fn2-b3-pos 0 fn2-b3)))
  (and (equal (fn2-b3-flags 0 fn2-b3) 0) (equal (fn2-b3-verify-phase 0 fn2-b3) 0)
       (equal (fn2-digest-list 1 fn2-digests) *fn-b3-iv*)
       (natp org) (natp ctr) (<= org ctr) (natp j) (< j 16)
       (equal pos (len buf)) (<= pos 64)
       (equal depth (fn2-b3-bits (- ctr org)))
       (equal (fn-b3-cv8 cv) cv)
       (implies (equal j 0) (equal cv *fn-b3-iv*))
       (fn-b3-octet-listp buf) (fn-b3-octet-listp xs)
       (< (+ (* 1024 ctr) (* 64 j) pos (len xs)) (expt 2 64))
       (if (equal pos 64) (equal (fn2-b3-buffer-words fn2-b3) (fn-b3-words 16 buf))
         (fn2-b3-packedp buf 0 fn2-b3))
       (equal answer (fn2-b3-resume (append buf xs) cv j ctr org
                      (fn2-b3-frontier-list depth fn2-digests) root)))))
(defun fn2-b3-good (past xs root answer fn2-digests fn2-b3)
 (declare (xargs :stobjs (fn2-digests fn2-b3) :verify-guards nil))
 (and (true-listp past) (<= (fn2-b3-pos 0 fn2-b3) (len past))
      (fn2-b3-match (fn2-b3-suffix (fn2-b3-pos 0 fn2-b3) past) xs root answer fn2-digests fn2-b3)))
(defthm fn2-b3-copy-cv-preserves-frontier
 (equal (fn2-b3-frontier-list d (fn2-digest-copy 0 src fn2-digests)) (fn2-b3-frontier-list d fn2-digests))
 :hints (("Goal" :induct (fn2-b3-frontier-list d fn2-digests) :in-theory (enable fn2-b3-frontier-list))))
(defthm fn2-b3-half-below
 (implies (and (natp n) (posp p) (< n (1- (* 2 p))))
  (and (< (floor n 2) p)
       (or (< (floor n 2) (1- p)) (equal (mod n 2) 0))))
 :rule-classes nil :hints (("Goal" :in-theory (enable mod))))
(defthm fn2-b3-bits-strict
 (implies (and (natp k) (natp n) (< n (1- (expt 2 k)))) (< (fn2-b3-bits n) k))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-b3-bit-induct n k) :do-not '(generalize eliminate-destructors)
                 )
         ("Subgoal *1/2" :use (fn2-b3-double-prev-expt
                 (:instance fn2-b3-half-below (p (expt 2 (1- k))))
                 (:instance fn2-b3-bits-bound (n (floor n 2)) (k (1- k))))
          :expand ((fn2-b3-bits n)) :do-not-induct t)))
(defconst *fn2-b3-proof-columns*
 '(fn2-b3-pos fn2-b3-blocks fn2-b3-counter fn2-b3-origin fn2-b3-depth fn2-b3-flags fn2-b3-verify-phase))
(defun fn2-b3-column-equations (columns changed value next)
 (if (endp columns) nil
  (cons `(equal (,(car columns) 0 ,next)
                ,(if (eq (car columns) changed) value `(,(car columns) 0 fn2-b3)))
        (fn2-b3-column-equations (cdr columns) changed value next))))
(defmacro fn2-b3-prove-column-reads (name op args changed value)
 `(defthm ,name
   (and ,@(fn2-b3-column-equations *fn2-b3-proof-columns* changed value (cons op args)))
   :hints (("Goal" :in-theory (enable ,op update-fn2-b3-pos$ai update-fn2-b3-blocks$ai update-fn2-b3-counter$ai update-fn2-b3-depth$ai update-fn2-b3-origin$ai ,@*fn2-b3-proof-columns*)))))
(fn2-b3-prove-column-reads fn2-b3-store-columns fn2-b3-store (0 i w fn2-b3) nil nil)
(fn2-b3-prove-column-reads fn2-b3-pos-columns fn2-b3-set-pos (0 v fn2-b3) fn2-b3-pos v)
(fn2-b3-prove-column-reads fn2-b3-blocks-columns fn2-b3-set-blocks (0 v fn2-b3) fn2-b3-blocks v)
(fn2-b3-prove-column-reads fn2-b3-counter-columns fn2-b3-set-counter (0 v fn2-b3) fn2-b3-counter v)
(fn2-b3-prove-column-reads fn2-b3-depth-columns fn2-b3-set-depth (0 v fn2-b3) fn2-b3-depth v)
(fn2-b3-prove-column-reads fn2-b3-origin-columns fn2-b3-set-origin (0 v fn2-b3) fn2-b3-origin v)
(in-theory (disable fn2-b3-set-pos fn2-b3-set-blocks fn2-b3-set-counter fn2-b3-set-depth fn2-b3-set-origin))
(defthm fn2-b3-push-other-columns
 (let ((next (mv-nth 1 (fn2-b3-push 0 n d src fn2-digests fn2-b3))))
   (and (equal (fn2-b3-origin 0 next) (fn2-b3-origin 0 fn2-b3))
        (equal (fn2-b3-verify-phase 0 next) (fn2-b3-verify-phase 0 fn2-b3))))
 :hints (("Goal" :induct (fn2-b3-push 0 n d src fn2-digests fn2-b3)
          :expand ((:free (n) (fn2-b3-push 0 n d src fn2-digests fn2-b3)))
          :in-theory (e/d ((:induction fn2-b3-push)) (floor mod)))))
(defthm fn2-b3-buffer-cv
 (implies (and (equal (fn-b3-cv8 (fn2-digest-list 0 fn2-digests)) (fn2-digest-list 0 fn2-digests))
               (equal (fn2-b3-buffer-words fn2-b3) (fn-b3-words 16 buf))
               (equal (fn2-b3-pos 0 fn2-b3) (len buf)) (<= (len buf) 64))
  (equal (fn2-b3-buffer-output t fn2-digests fn2-b3)
         (fn-b3-chunk (fn2-digest-list 0 fn2-digests) buf (fn2-b3-counter 0 fn2-b3) 0
                      (equal (fn2-b3-blocks 0 fn2-b3) 0))))
 :hints (("Goal" :in-theory (enable fn2-b3-buffer-output fn2-b3-chunk-last))))
(defthm fn2-b3-buffer-middle
 (implies (and (equal (fn2-b3-buffer-words fn2-b3) (fn-b3-words 16 buf)) (equal (fn2-b3-pos 0 fn2-b3) 64))
  (equal (fn2-b3-output-words (fn2-b3-buffer-output nil fn2-digests fn2-b3) nil)
         (fn-b3-compress (fn2-digest-list 0 fn2-digests) (fn-b3-words 16 buf) (fn2-b3-counter 0 fn2-b3)
                         64 (if (equal (fn2-b3-blocks 0 fn2-b3) 0) 1 0))))
 :hints (("Goal" :in-theory (enable fn2-b3-buffer-output fn2-b3-output-words fn-b3-output-cv fn-b3-output))))

(defthm fn2-b3-append-assoc
 (equal (append (append a b) c) (append a (append b c))))
(defun fn2-b3-append-buffer-byte (buf b fn2-b3)
 (declare (xargs :stobjs fn2-b3 :verify-guards nil))
 (let ((fn2-b3 (fn2-b3-store 0 (floor (len buf) 4) (fn2-b3-append-word buf 0 b fn2-b3) fn2-b3)))
   (fn2-b3-set-pos 0 (1+ (len buf)) fn2-b3)))
(defmacro fn2-b3-composite-columns (name op args changed value)
 `(defthm ,name (and ,@(fn2-b3-column-equations *fn2-b3-proof-columns* changed value (cons op args)))
    :hints (("Goal" :in-theory (enable ,op)))))
(fn2-b3-composite-columns fn2-b3-append-buffer-byte-columns fn2-b3-append-buffer-byte (buf b fn2-b3) fn2-b3-pos (1+ (len buf)))
(defthm fn2-b3-append-buffer-byte-packed
 (implies (and (fn2-b3-packedp buf 0 fn2-b3) (fn-b3-octet-listp buf) (unsigned-byte-p 8 b))
   (fn2-b3-packedp (append buf (list b)) 0 (fn2-b3-append-buffer-byte buf b fn2-b3)))
 :hints (("Goal" :use ((:instance fn2-b3-packed-append (base 0)))
          :in-theory (disable fn2-b3-packed-append))))
(defthm fn2-b3-byte-when-room
 (implies (and (equal (fn2-b3-pos 0 fn2-b3) (len buf)) (< (len buf) 64))
  (equal (fn2-b3-byte 0 b fn2-digests fn2-b3) (mv fn2-digests (fn2-b3-append-buffer-byte buf b fn2-b3))))
 :rule-classes nil :hints (("Goal" :in-theory (enable fn2-b3-byte fn2-b3-append-word))))
(in-theory (disable fn2-b3-append-buffer-byte))
(defthm fn2-b3-match-put
 (implies (and (fn2-b3-match buf (cons b xs) root answer fn2-digests fn2-b3) (< (len buf) 64))
   (fn2-b3-match (append buf (list b)) xs root answer fn2-digests (fn2-b3-append-buffer-byte buf b fn2-b3)))
 :hints (("Goal" :use ((:instance fn2-b3-packed-words (xs (append buf (list b))) (fn2-b3 (fn2-b3-append-buffer-byte buf b fn2-b3))))
          :in-theory (disable fn2-b3-packed-words fn2-b3-suffix)
          :do-not-induct t)))

(defthm fn2-b3-packed-empty (fn2-b3-packedp nil base fn2-b3) :hints (("Goal" :expand ((fn2-b3-packedp nil base fn2-b3)))))
(defthm fn2-b3-output-middle-raw
 (equal (fn-b3-output-cv (fn2-b3-buffer-output nil fn2-digests fn2-b3))
        (fn-b3-compress (fn2-digest-list 0 fn2-digests) (fn2-b3-buffer-words fn2-b3)
          (fn2-b3-counter 0 fn2-b3) (fn2-b3-pos 0 fn2-b3) (if (equal (fn2-b3-blocks 0 fn2-b3) 0) 1 0)))
 :hints (("Goal" :in-theory (enable fn2-b3-buffer-output fn-b3-output fn-b3-output-cv))))
(defthm fn2-b3-match-flush
 (implies (and (fn2-b3-match buf xs root answer fn2-digests fn2-b3)
               (equal (len buf) 64) (consp xs))
  (mv-let (dg b3) (fn2-b3-flush 0 fn2-digests fn2-b3)
    (fn2-b3-match nil xs root answer dg b3)))
 :hints (("Goal" :cases ((equal (fn2-b3-blocks 0 fn2-b3) 15))
                 :do-not-induct t :in-theory (enable fn2-b3-flush))
         ("Subgoal 2" :use ((:instance fn2-b3-bits-bound (k 54) (n (- (fn2-b3-counter 0 fn2-b3) (fn2-b3-origin 0 fn2-b3)))) (:instance fn2-b3-resume-full-block (rest xs)
           (cv (fn2-digest-list 0 fn2-digests)) (j (fn2-b3-blocks 0 fn2-b3))
           (ctr (fn2-b3-counter 0 fn2-b3)) (org (fn2-b3-origin 0 fn2-b3))
           (stack (fn2-b3-frontier-list (fn2-b3-depth 0 fn2-b3) fn2-digests)))))
         ("Subgoal 1" :use ((:instance fn2-b3-resume-full-chunk (rest xs)
           (cv (fn2-digest-list 0 fn2-digests)) (ctr (fn2-b3-counter 0 fn2-b3)) (org (fn2-b3-origin 0 fn2-b3))
           (stack (fn2-b3-frontier-list (fn2-b3-depth 0 fn2-b3) fn2-digests)))
           (:instance fn2-b3-bits-strict (k 54) (n (- (fn2-b3-counter 0 fn2-b3) (fn2-b3-origin 0 fn2-b3))))
           (:instance fn2-b3-push-refines-list (n (+ 1 (- (fn2-b3-counter 0 fn2-b3) (fn2-b3-origin 0 fn2-b3))))
            (depth (fn2-b3-depth 0 fn2-b3)) (src 56) (fn2-digests (fn2-b3-output 56 0 t nil fn2-digests fn2-b3)))))))
(defthm fn2-b3-match-pos
 (implies (fn2-b3-match buf xs root answer fn2-digests fn2-b3)
  (and (equal (fn2-b3-pos 0 fn2-b3) (len buf)) (<= (len buf) 64)))
 :rule-classes nil)
(defthm fn2-b3-flush-pos
 (equal (fn2-b3-pos 0 (mv-nth 1 (fn2-b3-flush 0 fn2-digests fn2-b3))) 0)
 :hints (("Goal" :in-theory (enable fn2-b3-flush))))
(defthm fn2-b3-suffix-one
 (implies (and (natp n) (<= n (len past)) (true-listp past))
  (equal (fn2-b3-suffix (1+ n) (append past (list b))) (append (fn2-b3-suffix n past) (list b))))
 :hints (("Goal" :use ((:instance fn2-b3-suffix-append (more (list b))))
          :in-theory (disable fn2-b3-suffix fn2-b3-suffix-append))))
(defthm fn2-b3-len-suffix
 (implies (and (natp n) (<= n (len past))) (equal (len (fn2-b3-suffix n past)) n)))
(in-theory (disable fn2-b3-suffix fn2-b3-match))
(defthm fn2-b3-good-flush
 (implies (and (fn2-b3-good past xs root answer fn2-digests fn2-b3)
               (equal (fn2-b3-pos 0 fn2-b3) 64) (consp xs))
  (mv-let (dg b3) (fn2-b3-flush 0 fn2-digests fn2-b3)
    (fn2-b3-good past xs root answer dg b3)))
 :hints (("Goal" :use ((:instance fn2-b3-match-flush (buf (fn2-b3-suffix 64 past)))))))
(defthm fn2-b3-good-put
 (let ((buf (fn2-b3-suffix (fn2-b3-pos 0 fn2-b3) past)))
  (implies (and (fn2-b3-good past (cons b xs) root answer fn2-digests fn2-b3)
                (< (fn2-b3-pos 0 fn2-b3) 64))
    (fn2-b3-good (append past (list b)) xs root answer fn2-digests (fn2-b3-append-buffer-byte buf b fn2-b3))))
 :hints (("Goal" :use ((:instance fn2-b3-match-pos (xs (cons b xs)) (buf (fn2-b3-suffix (fn2-b3-pos 0 fn2-b3) past)))
                       (:instance fn2-b3-match-put (buf (fn2-b3-suffix (fn2-b3-pos 0 fn2-b3) past)))))
         ))
(defthm fn2-b3-good-pos
 (implies (fn2-b3-good past xs root answer fn2-digests fn2-b3)
  (and (natp (fn2-b3-pos 0 fn2-b3)) (<= (fn2-b3-pos 0 fn2-b3) 64)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-b3-match-pos (buf (fn2-b3-suffix (fn2-b3-pos 0 fn2-b3) past)))))))
(defthm fn2-b3-byte-from-full
 (implies (equal (fn2-b3-pos 0 fn2-b3) 64)
  (equal (fn2-b3-byte 0 b fn2-digests fn2-b3)
         (mv-let (dg b3) (fn2-b3-flush 0 fn2-digests fn2-b3)
           (mv dg (fn2-b3-append-buffer-byte nil b b3)))))
 :hints (("Goal" :in-theory (enable fn2-b3-byte fn2-b3-append-buffer-byte fn2-b3-append-word))))
(defthm fn2-b3-good-byte
 (implies (fn2-b3-good past (cons b xs) root answer fn2-digests fn2-b3)
  (mv-let (dg b3) (fn2-b3-byte 0 b fn2-digests fn2-b3)
    (fn2-b3-good (append past (list b)) xs root answer dg b3)))
 :hints (("Goal" :cases ((equal (fn2-b3-pos 0 fn2-b3) 64)) :in-theory (disable fn2-b3-good))
         ("Subgoal 2" :use ((:instance fn2-b3-good-pos (xs (cons b xs)))
                        (:instance fn2-b3-byte-when-room (buf (fn2-b3-suffix (fn2-b3-pos 0 fn2-b3) past)))
                        (:instance fn2-b3-match-pos (xs (cons b xs)) (buf (fn2-b3-suffix (fn2-b3-pos 0 fn2-b3) past))))
                  :expand ((fn2-b3-good past (cons b xs) root answer fn2-digests fn2-b3)))
         ("Subgoal 1" :use ((:instance fn2-b3-good-flush (xs (cons b xs)))
                 (:instance fn2-b3-good-put
                  (fn2-digests (mv-nth 0 (fn2-b3-flush 0 fn2-digests fn2-b3)))
                  (fn2-b3 (mv-nth 1 (fn2-b3-flush 0 fn2-digests fn2-b3)))))
          :expand ((fn2-b3-good past (cons b xs) root answer fn2-digests fn2-b3)))))
(defthm fn2-b3-pool-blocks-list
 (let ((v (fn-b3-pool-blocks off ctr n j a b c d e f g h fn2-pool)))
  (and (true-listp v) (equal (len v) 8) (equal (fn-b3-cv8 v) v)))
 :hints (("Goal" :induct (fn-b3-pool-blocks off ctr n j a b c d e f g h fn2-pool)
                 :in-theory (enable fn-b3-pool-blocks fn-b3-cv8))))
(defthm fn2-b3-pool-run-shape
 (let ((v (fn2-b3-pool-run off ctr n j cv fn2-pool)))
  (and (true-listp v) (equal (len v) 8) (equal (fn-b3-cv8 v) v)))
 :hints (("Goal" :in-theory (enable fn2-b3-pool-run))))
(defthm fn2-b3-pool-message-reads
 (implies (and (natp i) (<= i 16) (natp k) (< k 16))
  (equal (fn2-b3-word 0 k (fn2-b3-pool-message 0 off i fn2-b3 fn2-pool))
         (if (< k i) (fn2-b3-word 0 k fn2-b3)
           (fn-b3-word (fn-b3-pool-word (+ off (* 4 k)) fn2-pool)))))
 :hints (("Goal" :induct (fn2-b3-pool-message 0 off i fn2-b3 fn2-pool)
          :in-theory (enable fn2-b3-pool-message))))
(defthm fn2-b3-pool-message-columns
 (let ((next (fn2-b3-pool-message 0 off i fn2-b3 fn2-pool)))
  (and (equal (fn2-b3-origin 0 next) (fn2-b3-origin 0 fn2-b3))
       (equal (fn2-b3-flags 0 next) (fn2-b3-flags 0 fn2-b3))
       (equal (fn2-b3-depth 0 next) (fn2-b3-depth 0 fn2-b3))
       (equal (fn2-b3-verify-phase 0 next) (fn2-b3-verify-phase 0 fn2-b3))))
 :hints (("Goal" :induct (fn2-b3-pool-message 0 off i fn2-b3 fn2-pool)
          :in-theory (enable fn2-b3-pool-message))))
(defthm fn2-b3-word-set-columns
 (and (equal (fn2-b3-word 0 i (fn2-b3-set-blocks 0 n fn2-b3)) (fn2-b3-word 0 i fn2-b3))
      (equal (fn2-b3-word 0 i (fn2-b3-set-counter 0 n fn2-b3)) (fn2-b3-word 0 i fn2-b3)))
 :hints (("Goal" :in-theory (enable fn2-b3-word fn2-b3-set-blocks fn2-b3-set-counter update-fn2-b3-blocks$ai update-fn2-b3-counter$ai))))
(defthm fn2-b3-chunk-output-rows
 (let ((next (mv-nth 0 (fn2-b3-chunk-output-into 0 off ctr fn2-digests fn2-b3 fn2-pool))))
   (equal next (fn2-digest-load 0 (fn2-b3-pool-run off ctr 15 0 *fn-b3-iv* fn2-pool) fn2-digests)))
 :hints (("Goal" :in-theory (e/d (fn2-b3-chunk-output-into fn2-digest-load fn2-b3-pool-run fn2-b3-mv-nth-is-nth)
                                  (nth mv-nth)))))
(defthm fn2-b3-chunk-output-buffer
 (equal (mv-nth 1 (fn2-b3-chunk-output-into 0 off ctr fn2-digests fn2-b3 fn2-pool))
        (fn2-b3-set-pos 0 64 (fn2-b3-set-blocks 0 15 (fn2-b3-set-counter 0 ctr
         (fn2-b3-pool-message 0 (+ 960 off) 0 fn2-b3 fn2-pool)))))
 :hints (("Goal" :in-theory (enable fn2-b3-chunk-output-into))))
(defthm fn2-b3-load-cv-preserves-frontier
 (implies (and (true-listp ws) (equal (len ws) 8))
  (equal (fn2-b3-frontier-list d (fn2-digest-load 0 ws fn2-digests)) (fn2-b3-frontier-list d fn2-digests)))
 :hints (("Goal" :induct (fn2-b3-frontier-list d fn2-digests) :in-theory (enable fn2-b3-frontier-list))))

(defthm fn2-b3-message-final-words
 (implies (and (natp off) (fn2-b3-covers xs off fn2-pool) (fn-b3-octet-listp xs) (equal (len xs) 64))
  (equal (fn2-b3-buffer-words
   (fn2-b3-set-pos 0 64 (fn2-b3-set-blocks 0 15 (fn2-b3-set-counter 0 ctr
      (fn2-b3-pool-message 0 off 0 fn2-b3 fn2-pool)))))
   (fn-b3-words 16 xs)))
 :rule-classes nil
 :hints ((and t `(:use ((:instance fn2-b3-word-sequence-correct (i 0) (k 16))
                        ,@(fn2-b3-pool-word-instances 16))
                 :in-theory (e/d (fn2-b3-buffer-words fn2-b3-block-word) (fn2-b3-word-sequence-correct))))))
(defthm fn2-b3-resume-deferred
 (implies (and (true-listp chunk) (equal (len chunk) 1024)
               (true-listp buf) (equal (len buf) 64) (true-listp rest)
               (equal (fn-b3-chunk cv buf ctr 0 nil) (fn-b3-chunk *fn-b3-iv* chunk ctr 0 t)))
  (equal (fn2-b3-resume (append buf rest) cv 15 ctr org stack root)
         (fn2-b3-resume (append chunk rest) *fn-b3-iv* 0 ctr org stack root)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :expand ((fn-b3-firstn 0 rest)) :cases ((consp rest)) :in-theory (enable fn2-b3-resume))))
(defthm fn2-b3-match-last-span
 (implies (and (fn2-b3-match nil (append chunk xs) root answer fn2-digests fn2-b3)
               (equal (fn2-b3-blocks 0 fn2-b3) 0) (equal ctr (fn2-b3-counter 0 fn2-b3))
               (natp off) (fn2-b3-covers chunk off fn2-pool) (fn-b3-octet-listp chunk)
               (fn-b3-octet-listp xs) (equal (len chunk) 1024))
  (mv-let (dg b3) (fn2-b3-chunk-output-into 0 off ctr fn2-digests fn2-b3 fn2-pool)
   (fn2-b3-match (fn-b3-nthcdrx 960 chunk) xs root answer dg b3)))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn2-b3-message-final-words (off (+ 960 off)) (xs (fn-b3-nthcdrx 960 chunk)))
                (:instance fn2-b3-covers-drop (n 960) (xs chunk))
                (:instance fn2-b3-full-pool-chunk (j 0) (cv *fn-b3-iv*) (xs chunk))
                (:instance fn2-b3-resume-deferred (rest xs) (buf (fn-b3-nthcdrx 960 chunk))
                 (cv (fn2-b3-pool-run off ctr 15 0 *fn-b3-iv* fn2-pool))
                 (org (fn2-b3-origin 0 fn2-b3)) (stack (fn2-b3-frontier-list (fn2-b3-depth 0 fn2-b3) fn2-digests))))
          :in-theory (enable fn2-b3-match fn2-b3-chunk-last))))

(defthm fn2-b3-resume-pushed-chunk
 (implies (and (true-listp chunk) (equal (len chunk) 1024) (consp xs)
               (natp ctr) (natp org) (<= org ctr))
  (equal (fn2-b3-resume (append chunk xs) *fn-b3-iv* 0 ctr org stack root)
   (fn2-b3-resume xs *fn-b3-iv* 0 (1+ ctr) org
    (fn2-b3-push-list stack (fn-b3-output-cv (fn-b3-chunk *fn-b3-iv* chunk ctr 0 t))
      (+ 1 (- ctr org)) *fn-b3-iv* 0) root)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-b3-resume-start (ctr (1+ ctr))
       (stack (fn2-b3-push-list stack (fn-b3-output-cv (fn-b3-chunk *fn-b3-iv* chunk ctr 0 t))
      (+ 1 (- ctr org)) *fn-b3-iv* 0))))
        :expand ((fn-b3-firstn 0 xs)) :in-theory (enable fn2-b3-resume))))
(defthm fn2-b3-match-bulk-push
 (implies (and (fn2-b3-match nil (append chunk xs) root answer fn2-digests fn2-b3)
               (equal (fn2-b3-blocks 0 fn2-b3) 0) (equal ctr (fn2-b3-counter 0 fn2-b3))
               (natp off) (fn2-b3-covers chunk off fn2-pool) (fn-b3-octet-listp chunk)
               (fn-b3-octet-listp xs) (consp xs) (equal (len chunk) 1024))
  (mv-let (dg b3) (fn2-b3-bulk 0 off 1024 ctr nil fn2-digests fn2-b3 fn2-pool)
   (fn2-b3-match nil xs root answer dg b3)))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn2-b3-resume-pushed-chunk
                 (org (fn2-b3-origin 0 fn2-b3)) (stack (fn2-b3-frontier-list (fn2-b3-depth 0 fn2-b3) fn2-digests)))
                (:instance fn2-b3-subtree-chunk-effect (xs chunk) (dst 56))
                (:instance fn2-b3-bits-strict (k 54) (n (- ctr (fn2-b3-origin 0 fn2-b3))))
                (:instance fn2-b3-push-refines-list (src 56) (depth (fn2-b3-depth 0 fn2-b3))
                  (n (+ 1 (- ctr (fn2-b3-origin 0 fn2-b3))))
                  (fn2-digests (fn2-digest-load 56 (fn-b3-output-cv (fn-b3-chunk *fn-b3-iv* chunk ctr 0 t)) fn2-digests))))
          :in-theory (e/d (fn2-b3-match fn2-b3-bulk)
                     (fn2-b3-subtree-chunk-effect fn2-b3-subtree-cv-into-by-definition)))))
(defthm fn2-b3-good-bulk
 (implies (and (fn2-b3-good past (append chunk xs) root answer fn2-digests fn2-b3)
               (equal (fn2-b3-pos 0 fn2-b3) 0) (equal (fn2-b3-blocks 0 fn2-b3) 0)
               (equal ctr (fn2-b3-counter 0 fn2-b3))
               (natp off) (fn2-b3-covers chunk off fn2-pool) (fn-b3-octet-listp chunk)
               (fn-b3-octet-listp xs) (or lastp (consp xs)) (equal (len chunk) 1024))
  (mv-let (dg b3) (fn2-b3-bulk 0 off 1024 ctr lastp fn2-digests fn2-b3 fn2-pool)
   (fn2-b3-good (append past chunk) xs root answer dg b3)))
 :hints (("Goal" :cases (lastp) :do-not-induct t)
         ("Subgoal 1" :use (fn2-b3-match-last-span) :in-theory (enable fn2-b3-bulk fn2-b3-suffix))
         ("Subgoal 2" :use (fn2-b3-match-bulk-push)
          :in-theory (enable fn2-b3-bulk fn2-b3-suffix))))

(defthm fn2-b3-consp-by-length
 (iff (consp xs) (< 0 (len xs))) :rule-classes nil)
(defthm fn2-b3-good-counter-bounded
 (implies (fn2-b3-good past xs root answer fn2-digests fn2-b3)
          (unsigned-byte-p 54 (fn2-b3-counter 0 fn2-b3)))
 :rule-classes nil :hints (("Goal" :in-theory (enable fn2-b3-good fn2-b3-match))))
(in-theory (disable fn2-b3-good fn2-b3-byte-from-full))
(defthm fn2-b3-good-room
 (implies (and (fn2-b3-good past xs root answer fn2-digests fn2-b3) (consp xs))
  (fn2-b3-roomp 0 fn2-b3))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-b3-bits-bound (k 54)
                       (n (- (fn2-b3-counter 0 fn2-b3) (fn2-b3-origin 0 fn2-b3)))))
          :in-theory (enable fn2-b3-good fn2-b3-match fn2-b3-roomp))))
(defthm fn2-b3-good-counter
 (implies (fn2-b3-good past xs root answer fn2-digests fn2-b3)
          (natp (fn2-b3-counter 0 fn2-b3)))
 :rule-classes nil :hints (("Goal" :in-theory (enable fn2-b3-good fn2-b3-match))))
(defthm fn2-b3-flush-boundary
 (implies (and (equal (fn2-b3-blocks 0 fn2-b3) 15) (unsigned-byte-p 54 (fn2-b3-counter 0 fn2-b3)))
  (let ((b3 (mv-nth 1 (fn2-b3-flush 0 fn2-digests fn2-b3))))
    (and (equal (fn2-b3-blocks 0 b3) 0) (equal (fn2-b3-counter 0 b3) (1+ (fn2-b3-counter 0 fn2-b3))))))
 :hints (("Goal" :in-theory (enable fn2-b3-flush))))
(defthm fn2-b3-window-base
 (implies (fn2-b3-windowp used fn2-pool) (equal (fn2-pool-slot-base 0 fn2-pool) 0))
 :hints (("Goal" :in-theory (enable fn2-pool-slot-base fn2-b3-windowp))))
(defthm fn2-b3-span-shape-at-entry
 (implies (fn2-b3-can-span 0 0 1 off left consumed 1 0 1 fn2-b3 fn2-pool)
  (or (and (equal (fn2-b3-pos 0 fn2-b3) 64) (equal (fn2-b3-blocks 0 fn2-b3) 15))
      (and (equal (fn2-b3-pos 0 fn2-b3) 0) (equal (fn2-b3-blocks 0 fn2-b3) 0))))
 :rule-classes nil :hints (("Goal" :in-theory (enable fn2-b3-can-span))))
(defthm fn2-b3-good-span
 (implies (and (fn2-b3-good past (append chunk xs) root answer fn2-digests fn2-b3)
               (fn2-b3-can-span 0 0 1 off left consumed 1 0 1 fn2-b3 fn2-pool)
               (natp off) (fn2-b3-covers chunk off fn2-pool) (fn-b3-octet-listp chunk)
               (fn-b3-octet-listp xs) (or lastp (consp xs)) (equal (len chunk) 1024))
  (mv-let (dg b3) (fn2-b3-span 0 off (fn2-b3-next-counter 0 fn2-b3) lastp fn2-digests fn2-b3 fn2-pool)
   (fn2-b3-good (append past chunk) xs root answer dg b3)))
 :hints (("Goal" :use ((:instance fn2-b3-good-bulk (ctr (fn2-b3-counter 0 fn2-b3))) fn2-b3-span-shape-at-entry (:instance fn2-b3-consp-by-length (xs (append chunk xs))) (:instance fn2-b3-good-counter-bounded (xs (append chunk xs)))
                       (:instance fn2-b3-good-counter (xs (append chunk xs)))
                       (:instance fn2-b3-good-flush (xs (append chunk xs)))
                       (:instance fn2-b3-good-bulk (ctr (1+ (fn2-b3-counter 0 fn2-b3)))
                          (fn2-digests (mv-nth 0 (fn2-b3-flush 0 fn2-digests fn2-b3)))
                          (fn2-b3 (mv-nth 1 (fn2-b3-flush 0 fn2-digests fn2-b3)))))
          :do-not-induct t
          :in-theory (enable fn2-b3-span fn2-b3-next-counter))))

(defthm fn2-b3-cut-rejoin
 (implies (true-listp xs) (equal (append (fn-b3-firstn n xs) (fn-b3-nthcdrx n xs)) xs))
 :hints (("Goal" :induct (fn-b3-nthcdrx n xs) :in-theory (fn2-b3-list-theory fn-b3-firstn fn-b3-nthcdrx))))
(defthm fn2-b3-cut-rejoin-rest
 (implies (true-listp xs)
  (equal (append (fn-b3-firstn n xs) (append (fn-b3-nthcdrx n xs) rest)) (append xs rest)))
 :hints (("Goal" :use ((:instance fn2-b3-append-assoc (a (fn-b3-firstn n xs)) (b (fn-b3-nthcdrx n xs)) (c rest)))
          :in-theory (disable fn2-b3-append-assoc))))
(defthm fn2-b3-first-covers
 (implies (fn2-b3-covers xs off fn2-pool) (fn2-b3-covers (fn-b3-firstn n xs) off fn2-pool))
 :hints (("Goal" :induct (fn2-b3-drop-induct n off xs) :in-theory (fn2-b3-list-theory fn2-b3-drop-induct fn2-b3-covers fn-b3-firstn))))
(defthm fn2-b3-first-octets
 (implies (fn-b3-octet-listp xs) (fn-b3-octet-listp (fn-b3-firstn n xs)))
 :hints (("Goal" :induct (fn-b3-firstn n xs) :in-theory (fn2-b3-list-theory fn-b3-firstn fn-b3-octet-listp))))
(defthm fn2-b3-covers-head
 (implies (and (consp xs) (fn2-b3-covers xs off fn2-pool))
  (and (equal (fn2-pool-datai off fn2-pool) (car xs)) (fn2-b3-covers (cdr xs) (1+ off) fn2-pool)))
 :hints (("Goal" :expand ((fn2-b3-covers xs off fn2-pool)))))
(defun fn2-b3-frag-induct (bytes past off fn2-digests fn2-b3 fn2-pool)
 (declare (xargs :stobjs (fn2-digests fn2-b3 fn2-pool) :verify-guards nil))
 (if (atom bytes) (mv (list past off) fn2-digests fn2-b3)
  (mv-let (fn2-digests fn2-b3) (fn2-b3-byte 0 (fn2-pool-datai off fn2-pool) fn2-digests fn2-b3)
   (fn2-b3-frag-induct (cdr bytes) (append past (list (car bytes))) (1+ off) fn2-digests fn2-b3 fn2-pool))))
(defthm fn2-b3-good-past-list
 (implies (fn2-b3-good past xs root answer fn2-digests fn2-b3) (true-listp past))
 :rule-classes :forward-chaining :hints (("Goal" :in-theory (enable fn2-b3-good))))
(defthm fn2-b3-good-fragment
 (implies (and (fn2-b3-good past (append bytes rest) root answer fn2-digests fn2-b3)
               (fn2-b3-covers bytes off fn2-pool) (fn-b3-octet-listp bytes))
  (mv-let (dg b3) (fn2-b3-fragment-into 0 off (len bytes) fn2-digests fn2-b3 fn2-pool)
    (fn2-b3-good (append past bytes) rest root answer dg b3)))
 :hints (("Goal" :induct (fn2-b3-frag-induct bytes past off fn2-digests fn2-b3 fn2-pool)
          :expand ((:free (n) (fn2-b3-fragment-into 0 off n fn2-digests fn2-b3 fn2-pool))
                   (append bytes rest)))
         ("Subgoal *1/2" :use ((:instance fn2-b3-good-byte (b (car bytes)) (xs (append (cdr bytes) rest)))))))

(in-theory (disable fn2-b3-roomp fn2-b3-read fn2-pool-slot-base))
(defun fn2-b3-feed-induct (bytes past off fn2-digests fn2-b3 fn2-pool)
 (declare (xargs :stobjs (fn2-digests fn2-b3 fn2-pool) :verify-guards nil :measure (len bytes)))
 (cond ((atom bytes) (mv (list past off) fn2-digests fn2-b3))
       ((and (<= 1024 (len bytes))
          (fn2-b3-can-span 0 0 1 off (len bytes) off 1 0 1 fn2-b3 fn2-pool))
        (mv-let (fn2-digests fn2-b3)
         (fn2-b3-span 0 off (fn2-b3-next-counter 0 fn2-b3) (< (len bytes) 2048) fn2-digests fn2-b3 fn2-pool)
         (fn2-b3-feed-induct (fn-b3-nthcdrx 1024 bytes) (append past (fn-b3-firstn 1024 bytes))
                            (+ 1024 off) fn2-digests fn2-b3 fn2-pool)))
       (t (mv-let (fn2-digests fn2-b3) (fn2-b3-byte 0 (car bytes) fn2-digests fn2-b3)
            (fn2-b3-feed-induct (cdr bytes) (append past (list (car bytes))) (1+ off)
              fn2-digests fn2-b3 fn2-pool)))))
(defthm fn2-b3-feed-span-step
 (implies (and (fn2-b3-good past (append bytes rest) root answer fn2-digests fn2-b3)
               (fn2-b3-covers bytes off fn2-pool) (fn-b3-octet-listp bytes) (fn-b3-octet-listp rest) (natp off)
               (<= 1024 (len bytes)) (fn2-b3-can-span 0 0 1 off (len bytes) off 1 0 1 fn2-b3 fn2-pool))
  (mv-let (dg b3) (fn2-b3-span 0 off (fn2-b3-next-counter 0 fn2-b3) (< (len bytes) 2048) fn2-digests fn2-b3 fn2-pool)
   (fn2-b3-good (append past (fn-b3-firstn 1024 bytes)) (append (fn-b3-nthcdrx 1024 bytes) rest) root answer dg b3)))
 :hints (("Goal" :use ((:instance fn2-b3-good-span (chunk (fn-b3-firstn 1024 bytes))
                (xs (append (fn-b3-nthcdrx 1024 bytes) rest)) (left (len bytes)) (consumed off)
                (lastp (< (len bytes) 2048)))
            (:instance fn2-b3-consp-by-length (xs (append (fn-b3-nthcdrx 1024 bytes) rest))))
          :do-not-induct t)))
(defthm fn2-b3-good-feed
 (implies (and (fn2-b3-good past (append bytes rest) root answer fn2-digests fn2-b3)
               (fn2-b3-covers bytes off fn2-pool) (fn-b3-octet-listp bytes) (fn-b3-octet-listp rest)
               (natp off) (<= (+ off (len bytes)) 4096) (fn2-b3-windowp (+ off (len bytes)) fn2-pool))
  (mv-let (code count dg b3) (fn2-b3-feed 0 0 1 off (len bytes) off 1 0 1 fn2-digests fn2-b3 fn2-pool)
   (and (equal code :ok) (equal count (+ off (len bytes)))
        (fn2-b3-good (append past bytes) rest root answer dg b3))))
 :hints (("Goal" :induct (fn2-b3-feed-induct bytes past off fn2-digests fn2-b3 fn2-pool)
             :expand ((:free (left) (fn2-b3-feed 0 0 1 off left off 1 0 1 fn2-digests fn2-b3 fn2-pool)))
             :do-not '(generalize eliminate-destructors))
         ("Subgoal *1/3" :use ((:instance fn2-b3-good-byte (b (car bytes)) (xs (append (cdr bytes) rest)))
                         (:instance fn2-b3-good-room (xs (append bytes rest)))
                         (:instance fn2-b3-window-read (used (+ off (len bytes))))
                         (:instance fn2-b3-can-span-bounds (row 0) (slot 0) (gen 1) (left (len bytes))
                            (consumed off) (okind 1) (oslot 0) (ogen 1)))
          :expand ((append bytes rest) (:free (left) (fn2-b3-feed 0 0 1 off left off 1 0 1 fn2-digests fn2-b3 fn2-pool))))
         ("Subgoal *1/2" :use (fn2-b3-feed-span-step
                         (:instance fn2-b3-good-room (xs (append bytes rest)))
                         (:instance fn2-b3-consp-by-length (xs (append bytes rest)))
                         (:instance fn2-b3-window-base (used (+ off (len bytes))))))))
(defthm fn2-b3-admitted-window-length
 (implies (<= n 4096) (equal (min n 4096) n)))
(defthm fn2-b3-fragment-zero
 (equal (fn2-b3-fragment-into 0 off 0 fn2-digests fn2-b3 fn2-pool) (mv fn2-digests fn2-b3))
 :hints (("Goal" :expand ((fn2-b3-fragment-into 0 off 0 fn2-digests fn2-b3 fn2-pool)))))
(defthm fn2-b3-update-at-cut
 (implies (and (fn2-b3-good past (append bytes rest) root answer fn2-digests fn2-b3)
               (fn2-b3-covers bytes 0 fn2-pool) (fn-b3-octet-listp bytes) (fn-b3-octet-listp rest)
               (natp n) (<= n (len bytes)) (<= (len bytes) 4096) (fn2-b3-windowp (len bytes) fn2-pool))
  (mv-let (dg b3) (fn2-b3-fragment-into 0 0 n fn2-digests fn2-b3 fn2-pool)
   (mv-let (code count dg b3) (fn2-b3-feed 0 0 1 n (- (len bytes) n) n 1 0 1 dg b3 fn2-pool)
    (and (equal code :ok) (equal count (len bytes)) (fn2-b3-good (append past bytes) rest root answer dg b3)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-b3-good-fragment (bytes (fn-b3-firstn n bytes)) (off 0)
                         (rest (append (fn-b3-nthcdrx n bytes) rest)))
                       (:instance fn2-b3-good-feed (off n) (bytes (fn-b3-nthcdrx n bytes))
                        (past (append past (fn-b3-firstn n bytes)))
                        (fn2-digests (mv-nth 0 (fn2-b3-fragment-into 0 0 n fn2-digests fn2-b3 fn2-pool)))
                        (fn2-b3 (mv-nth 1 (fn2-b3-fragment-into 0 0 n fn2-digests fn2-b3 fn2-pool))))
                       (:instance fn2-b3-covers-drop (xs bytes) (off 0)))
          :do-not-induct t :in-theory (disable fn2-b3-good-fragment fn2-b3-good-feed))))
(in-theory (disable min))
(defthm fn2-b3-good-update
 (implies (and (fn2-b3-good past (append bytes rest) root answer fn2-digests fn2-b3)
               (fn2-b3-covers bytes 0 fn2-pool) (fn-b3-octet-listp bytes) (fn-b3-octet-listp rest)
               (<= (len bytes) 4096) (fn2-b3-windowp (len bytes) fn2-pool))
  (mv-let (code count dg b3) (fn2-b3-update 0 0 1 0 (len bytes) 1 0 1 fn2-digests fn2-b3 fn2-pool)
    (and (equal code :ok) (equal count (len bytes)) (fn2-b3-good (append past bytes) rest root answer dg b3))))
 :hints (("Goal" :cases ((equal (fn2-b3-fragment-count 0 0 1 0 (len bytes) 1 0 1 fn2-b3 fn2-pool) 0)))
         ("Subgoal 2" :use ((:instance fn2-b3-update-at-cut (n (fn2-b3-fragment-count 0 0 1 0 (len bytes) 1 0 1 fn2-b3 fn2-pool))))
          :in-theory (enable fn2-b3-update) :do-not-induct t)
         ("Subgoal 1" :use ((:instance fn2-b3-update-at-cut (n 0))) :in-theory (enable fn2-b3-update) :do-not-induct t)))
(defthm fn2-b3-loaded-update
 (implies (and (fn2-b3-good past (append bytes rest) root answer fn2-digests fn2-b3)
               (fn-b3-octet-listp bytes) (fn-b3-octet-listp rest) (<= (len bytes) 4096)
               (fn2-b3-windowp 0 fn2-pool))
  (let ((pool (fn2-b3-spec-load bytes 0 fn2-pool)))
   (mv-let (code count dg b3) (fn2-b3-update 0 0 1 0 (len bytes) 1 0 1 fn2-digests fn2-b3 pool)
    (declare (ignore code count))
    (fn2-b3-good (append past bytes) rest root answer dg b3))))
 :hints (("Goal" :use ((:instance fn2-b3-window-loaded (xs bytes) (off 0)) (:instance fn2-b3-loaded-covers (xs bytes)) (:instance fn2-b3-good-update (fn2-pool (fn2-b3-spec-load bytes 0 fn2-pool))))
          :in-theory (disable fn2-b3-good-update fn2-b3-spec-load))))

(defun fn2-b3-splits-window-induct (splits past used fn2-digests fn2-b3 fn2-pool)
 (declare (xargs :stobjs (fn2-digests fn2-b3 fn2-pool) :verify-guards nil))
 (if (atom splits) (mv (list past used) fn2-digests fn2-b3 fn2-pool)
  (b* (((mv & fn2-pool) (fn2-pool-reset 0 1 1 0 1 fn2-pool))
       (fn2-pool (fn2-b3-spec-load (car splits) 0 fn2-pool))
       ((mv & & fn2-digests fn2-b3) (fn2-b3-update 0 0 1 0 (len (car splits)) 1 0 1 fn2-digests fn2-b3 fn2-pool)))
    (fn2-b3-splits-window-induct (cdr splits) (append past (car splits)) (len (car splits)) fn2-digests fn2-b3 fn2-pool))))
; A split may end in the middle of a word, a block, or a chunk.
(defthm fn2-b3-good-splits
 (implies (and (fn2-b3-good past (fn2-b3-flatten splits) root answer fn2-digests fn2-b3)
               (fn2-b3-windowp used fn2-pool) (fn2-b3-splitsp splits))
  (mv-let (dg b3 pool) (fn2-b3-spec-splits splits fn2-digests fn2-b3 fn2-pool)
   (declare (ignore pool)) (fn2-b3-good (append past (fn2-b3-flatten splits)) nil root answer dg b3)))
 :hints (("Goal" :induct (fn2-b3-splits-window-induct splits past used fn2-digests fn2-b3 fn2-pool)
          :expand ((fn2-b3-spec-splits nil fn2-digests fn2-b3 fn2-pool) (fn2-b3-spec-splits splits fn2-digests fn2-b3 fn2-pool)
                   (fn2-b3-splitsp splits) (fn2-b3-flatten splits))
          :in-theory (disable fn2-b3-spec-load fn2-b3-spec-splits)
          :do-not '(generalize eliminate-destructors))
         ("Subgoal *1/2" :use ((:instance fn2-b3-loaded-update (bytes (car splits)) (rest (fn2-b3-flatten (cdr splits)))
                 (fn2-pool (mv-nth 1 (fn2-pool-reset 0 1 1 0 1 fn2-pool))))
                (:instance fn2-b3-window-loaded (xs (car splits)) (off 0)
                 (fn2-pool (mv-nth 1 (fn2-pool-reset 0 1 1 0 1 fn2-pool))))))))

(defthm fn2-b3-resume-end
 (implies (and (true-listp buf) (<= (len buf) 64) (natp j) (< j 16))
  (equal (fn2-b3-resume buf cv j ctr org stack root)
         (fn2-b3-seal stack (fn-b3-chunk cv buf ctr 0 (equal j 0)) root)))
 :hints (("Goal" :in-theory (enable fn2-b3-resume) :do-not-induct t)))
(defthm fn2-b3-seal-frontier
 (let ((stack (fn2-b3-frontier-list depth fn2-digests)))
  (implies (and (natp depth) (booleanp root))
    (equal (fn2-b3-fold-list stack (fn2-b3-output-words out (and root (equal depth 0))) *fn-b3-iv* 0 root)
           (fn2-b3-seal stack out root))))
 :hints (("Goal" :cases ((zp depth) root)
          :expand ((fn2-b3-frontier-list 0 fn2-digests)
                   (:free (cv r) (fn2-b3-fold-list nil cv *fn-b3-iv* 0 r)))
          :in-theory (enable fn2-b3-seal))))
(defthm fn2-b3-match-end-facts
 (let ((depth (fn2-b3-depth 0 fn2-b3)))
  (implies (fn2-b3-match buf nil root answer fn2-digests fn2-b3)
   (and (natp depth) (<= depth 54) (equal (fn2-b3-flags 0 fn2-b3) 0)
        (equal (fn2-digest-list 1 fn2-digests) *fn-b3-iv*)
        (equal answer (fn2-b3-seal (fn2-b3-frontier-list depth fn2-digests)
                       (fn2-b3-buffer-output t fn2-digests fn2-b3) root)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-b3-packed-words (xs buf)) fn2-b3-buffer-cv
                       (:instance fn2-b3-bits-bound (k 54) (n (- (fn2-b3-counter 0 fn2-b3) (fn2-b3-origin 0 fn2-b3)))))
          :in-theory (fn2-b3-list-theory fn2-b3-match fn2-b3-resume-end fn2-b3-octets-true-list fn2-b3-bits-natp append-to-nil fn2-b3-len-append) :do-not-induct t)))
(defthm fn2-b3-match-finish
 (implies (and (natp dst) (<= 57 dst) (booleanp root) (fn2-b3-match buf nil root answer fn2-digests fn2-b3))
   (equal (fn2-digest-list dst (fn2-b3-finish dst 0 root fn2-digests fn2-b3)) answer))
 :rule-classes nil
 :hints (("Goal" :use (fn2-b3-match-end-facts fn2-b3-finish-refines-list
                      (:instance fn2-b3-seal-frontier (depth (fn2-b3-depth 0 fn2-b3))
                           (out (fn2-b3-buffer-output t fn2-digests fn2-b3))))
          :in-theory (theory 'minimal-theory))))
(defthm fn2-b3-good-finish
 (implies (and (natp dst) (<= 57 dst) (booleanp root) (fn2-b3-good past nil root answer fn2-digests fn2-b3))
   (equal (fn2-digest-list dst (fn2-b3-finish dst 0 root fn2-digests fn2-b3)) answer))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-b3-match-finish (buf (fn2-b3-suffix (fn2-b3-pos 0 fn2-b3) past))))
          :in-theory (enable fn2-b3-good))))
(in-theory (enable update-fn2-b3-verify-phase$ai update-fn2-b3-flags$ai))
(fn2-b3-prove-column-reads fn2-b3-phase-columns fn2-b3-set-verify-phase (0 v fn2-b3) fn2-b3-verify-phase v)
(fn2-b3-prove-column-reads fn2-b3-flags-columns fn2-b3-set-flags (0 v fn2-b3) fn2-b3-flags v)
(in-theory (disable fn2-b3-set-flags fn2-b3-set-verify-phase))
(defthm fn2-b3-init-zero-fields
 (let ((b3 (mv-nth 1 (fn2-b3-init 0 0 136 fn2-digests fn2-b3))))
  (and (equal (fn2-b3-pos 0 b3) 0) (equal (fn2-b3-blocks 0 b3) 0)
       (equal (fn2-b3-verify-phase 0 b3) 0)))
 :hints (("Goal" :in-theory (enable fn2-b3-init))))
(defthm fn2-b3-good-init
 (implies (and (natp ctr) (fn-b3-octet-listp xs) (< (+ (* 1024 ctr) (len xs)) (expt 2 64)))
  (mv-let (dg b3) (fn2-b3-init 0 0 136 fn2-digests fn2-b3)
   (fn2-b3-good nil xs root (fn2-b3-output-words (fn-b3-node *fn-b3-iv* xs ctr 0) root)
                dg (fn2-b3-start-subtree 0 ctr b3))))
 :hints (("Goal" :do-not-induct t :use (fn2-b3-init-observations (:instance fn2-b3-scan-is-node (k 0) (counter ctr))
                       (:instance fn2-b3-resume-start (org ctr) (stack nil)))
          :expand ((:free (dg) (fn2-b3-frontier-list 0 dg)) (fn2-b3-bits 0))
          :in-theory (enable fn2-b3-good fn2-b3-match fn2-b3-start-subtree))))
(defthm fn2-b3-initial-window
 (fn2-b3-windowp 0 (mv-nth 3 (fn2-pool-reserve 0 1 0 1
           (fn2-pool-init '((1 . 4096)) 1 100 (create-fn2-pool)))))
 :hints (("Goal" :expand ((create-fn2-pool)) :in-theory (executable-counterpart-theory :here))))

; ---- hashing invariant with the buffered past quantified away ----
(defthm fc-b3-init-key
  (implies (syntaxp (not (equal key ''136)))
           (equal (fn2-b3-init 0 0 key ds b3) (fn2-b3-init 0 0 136 ds b3)))
  :hints (("Goal" :in-theory (enable fn2-b3-init))))
(defthm fc-b3-init-counters
  (let ((b3 (mv-nth 1 (fn2-b3-init 0 0 136 ds b3))))
    (and (equal (fn2-b3-counter 0 b3) 0) (equal (fn2-b3-origin 0 b3) 0)))
  :hints (("Goal" :in-theory (enable fn2-b3-init))))
(defthm fc-b3-good-init
  (implies (and (fn-b3-octet-listp xs) (< (len xs) (expt 2 64)))
   (mv-let (dg b3) (fn2-b3-init 0 0 136 fn2-digests fn2-b3)
    (fn2-b3-good nil xs root (fn2-b3-output-words (fn-b3-node *fn-b3-iv* xs 0 0) root) dg b3)))
  :hints (("Goal" :do-not-induct t
           :use (fn2-b3-init-observations (:instance fn2-b3-scan-is-node (k 0) (counter 0))
                 (:instance fn2-b3-resume-start (org 0) (ctr 0) (stack nil)))
           :expand ((:free (dg) (fn2-b3-frontier-list 0 dg)) (fn2-b3-bits 0))
           :in-theory (enable fn2-b3-good fn2-b3-match))))

(defun-sk fc-g (xs ans ds b3)
  (exists past (fn2-b3-good past xs t ans ds b3)))
(in-theory (disable fc-g fc-g-suff))
(defthm fc-g-init
  (implies (and (fn-b3-octet-listp xs) (< (len xs) (expt 2 64)))
   (mv-let (dg b3) (fn2-b3-init 0 0 136 ds b3)
    (fc-g xs (fn2-b3-output-words (fn-b3-node *fn-b3-iv* xs 0 0) t) dg b3)))
  :hints (("Goal" :use ((:instance fc-b3-good-init (root t) (fn2-digests ds) (fn2-b3 b3))
                        (:instance fc-g-suff (past nil)
                          (ans (fn2-b3-output-words (fn-b3-node *fn-b3-iv* xs 0 0) t))
                          (ds (mv-nth 0 (fn2-b3-init 0 0 136 ds b3)))
                          (b3 (mv-nth 1 (fn2-b3-init 0 0 136 ds b3)))))
           :in-theory (disable fc-b3-good-init))))
(defthm fc-g-byte
  (implies (fc-g (cons b xs) ans ds b3)
   (mv-let (dg b3) (fn2-b3-byte 0 b ds b3) (fc-g xs ans dg b3)))
  :hints (("Goal" :use ((:instance fn2-b3-good-byte (past (fc-g-witness (cons b xs) ans ds b3))
                           (root t) (answer ans) (fn2-digests ds) (fn2-b3 b3))
                        (:instance fc-g-suff (past (append (fc-g-witness (cons b xs) ans ds b3) (list b)))
                          (ds (mv-nth 0 (fn2-b3-byte 0 b ds b3)))
                          (b3 (mv-nth 1 (fn2-b3-byte 0 b ds b3)))))
           :expand ((fc-g (cons b xs) ans ds b3))
           :in-theory (disable fn2-b3-good-byte))))
(defthm fc-g-room
  (implies (and (fc-g xs ans ds b3) (consp xs)) (fn2-b3-roomp 0 b3))
  :hints (("Goal" :use ((:instance fn2-b3-good-room (past (fc-g-witness xs ans ds b3))
                           (root t) (answer ans) (fn2-digests ds) (fn2-b3 b3)))
           :expand ((fc-g xs ans ds b3)))))
(defthm fc-g-fragment
  (implies (and (fc-g (append bytes rest) ans ds b3)
                (fn2-b3-covers bytes off pool) (fn-b3-octet-listp bytes))
   (mv-let (dg b3) (fn2-b3-fragment-into 0 off (len bytes) ds b3 pool)
     (fc-g rest ans dg b3)))
  :hints (("Goal" :use ((:instance fn2-b3-good-fragment (past (fc-g-witness (append bytes rest) ans ds b3))
                           (root t) (answer ans) (fn2-digests ds) (fn2-b3 b3) (fn2-pool pool))
                        (:instance fc-g-suff (xs rest)
                          (past (append (fc-g-witness (append bytes rest) ans ds b3) bytes))
                          (ds (mv-nth 0 (fn2-b3-fragment-into 0 off (len bytes) ds b3 pool)))
                          (b3 (mv-nth 1 (fn2-b3-fragment-into 0 off (len bytes) ds b3 pool)))))
           :expand ((fc-g (append bytes rest) ans ds b3))
           :in-theory (disable fn2-b3-good-fragment))))
(defthm fc-g-span
  (implies (and (fc-g (append bytes rest) ans ds b3)
                (fn2-b3-covers bytes off pool) (fn-b3-octet-listp bytes) (fn-b3-octet-listp rest) (natp off)
                (<= 1024 (len bytes)) (fn2-b3-can-span 0 0 1 off (len bytes) consumed 1 0 1 b3 pool))
   (mv-let (dg b3) (fn2-b3-span 0 off (fn2-b3-next-counter 0 b3) (< (len bytes) 2048) ds b3 pool)
    (fc-g (append (fn-b3-nthcdrx 1024 bytes) rest) ans dg b3)))
  :hints (("Goal" :use ((:instance fn2-b3-good-span (chunk (fn-b3-firstn 1024 bytes))
                 (past (fc-g-witness (append bytes rest) ans ds b3)) (root t) (answer ans)
                 (fn2-digests ds) (fn2-b3 b3) (fn2-pool pool)
                 (xs (append (fn-b3-nthcdrx 1024 bytes) rest)) (left (len bytes))
                 (lastp (< (len bytes) 2048)))
             (:instance fn2-b3-consp-by-length (xs (append (fn-b3-nthcdrx 1024 bytes) rest)))
             (:instance fc-g-suff (xs (append (fn-b3-nthcdrx 1024 bytes) rest))
                (past (append (fc-g-witness (append bytes rest) ans ds b3) (fn-b3-firstn 1024 bytes)))
                (ds (mv-nth 0 (fn2-b3-span 0 off (fn2-b3-next-counter 0 b3) (< (len bytes) 2048) ds b3 pool)))
                (b3 (mv-nth 1 (fn2-b3-span 0 off (fn2-b3-next-counter 0 b3) (< (len bytes) 2048) ds b3 pool)))))
           :expand ((fc-g (append bytes rest) ans ds b3))
           :do-not-induct t :in-theory (e/d (min) (fn2-b3-good-span)))))
(defthm fc-g-finish
  (implies (and (natp dst) (<= 57 dst) (fc-g nil ans ds b3))
   (equal (fn2-digest-list dst (fn2-b3-finish dst 0 t ds b3)) ans))
  :hints (("Goal" :use ((:instance fn2-b3-good-finish (past (fc-g-witness nil ans ds b3))
                           (root t) (answer ans) (fn2-digests ds) (fn2-b3 b3)))
           :expand ((fc-g nil ans ds b3)))))
(defun-nx fc-feed-induct (bytes off consumed ds b3 pool)
  (declare (xargs :measure (len bytes)))
  (cond ((atom bytes) (list off consumed ds b3))
        ((or (not (fn2-b3-roomp 0 b3)) (>= off 4294967295) (>= consumed 4096)) nil)
        ((and (<= 1024 (len bytes))
              (fn2-b3-can-span 0 0 1 off (len bytes) consumed 1 0 1 b3 pool))
         (let ((r (fn2-b3-span 0 off (fn2-b3-next-counter 0 b3) (< (len bytes) 2048) ds b3 pool)))
           (fc-feed-induct (fn-b3-nthcdrx 1024 bytes) (+ off 1024) (+ consumed 1024)
                           (mv-nth 0 r) (mv-nth 1 r) pool)))
        (t (let ((r (fn2-b3-byte 0 (car bytes) ds b3)))
             (fc-feed-induct (cdr bytes) (1+ off) (1+ consumed) (mv-nth 0 r) (mv-nth 1 r) pool)))))
(defthm fc-drop-cdr
  (implies (and (natp k) (consp xs))
           (equal (fn-b3-nthcdrx k (cdr xs)) (fn-b3-nthcdrx (+ 1 k) xs)))
  :hints (("Goal" :expand ((fn-b3-nthcdrx (+ 1 k) xs)))))

(defthm fc-g-feed
  (implies (and (fc-g (append bytes rest) ans ds b3)
                (fn2-b3-covers bytes off pool) (fn-b3-octet-listp bytes) (fn-b3-octet-listp rest)
                (natp off) (natp consumed) (<= (+ off (len bytes)) 4096) (fn2-b3-windowp 4096 pool))
   (let* ((r (fn2-b3-feed 0 0 1 off (len bytes) consumed 1 0 1 ds b3 pool))
          (k (- (mv-nth 1 r) consumed)))
     (and (natp k) (<= k (len bytes))
          (fc-g (append (fn-b3-nthcdrx k bytes) rest) ans (mv-nth 2 r) (mv-nth 3 r)))))
  :rule-classes nil
  :hints (("Goal" :induct (fc-feed-induct bytes off consumed ds b3 pool)
              :expand ((:free (left) (fn2-b3-feed 0 0 1 off left consumed 1 0 1 ds b3 pool)))
              :do-not '(generalize eliminate-destructors))
          ("Subgoal *1/4" :use ((:instance fc-g-byte (b (car bytes)) (xs (append (cdr bytes) rest)))
                          (:instance fn2-b3-window-read (used 4096) (fn2-pool pool))
                          (:instance fn2-b3-covers-head (xs bytes) (fn2-pool pool))
                          (:instance fn2-b3-can-span-bounds (row 0) (slot 0) (gen 1) (left (len bytes))
                             (okind 1) (oslot 0) (ogen 1) (fn2-b3 b3) (fn2-pool pool)))
           :expand ((append bytes rest) (:free (left) (fn2-b3-feed 0 0 1 off left consumed 1 0 1 ds b3 pool))))
          ("Subgoal *1/3" :use (fc-g-span
                          (:instance fn2-b3-covers-drop (xs bytes) (n 1024) (fn2-pool pool))
                          (:instance fn2-b3-window-base (used 4096) (fn2-pool pool)))
           :expand ((:free (left) (fn2-b3-feed 0 0 1 off left consumed 1 0 1 ds b3 pool))))))

(in-theory (disable fc-drop-cdr))
(defthm fc-g-update
  (implies (and (fc-g (append bytes rest) ans ds b3)
                (fn2-b3-covers bytes off pool) (fn-b3-octet-listp bytes) (fn-b3-octet-listp rest)
                (natp off) (<= (+ off (len bytes)) 4096) (fn2-b3-windowp 4096 pool))
   (let* ((r (fn2-b3-update 0 0 1 off (len bytes) 1 0 1 ds b3 pool)) (k (mv-nth 1 r)))
     (and (natp k) (<= k (len bytes))
          (fc-g (append (fn-b3-nthcdrx k bytes) rest) ans (mv-nth 2 r) (mv-nth 3 r)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use ((:instance fc-g-fragment (bytes (fn-b3-firstn (fn2-b3-fragment-count 0 0 1 off (len bytes) 1 0 1 b3 pool) bytes))
             (rest (append (fn-b3-nthcdrx (fn2-b3-fragment-count 0 0 1 off (len bytes) 1 0 1 b3 pool) bytes) rest)))
          (:instance fc-g-feed (bytes (fn-b3-nthcdrx (fn2-b3-fragment-count 0 0 1 off (len bytes) 1 0 1 b3 pool) bytes))
             (off (+ off (fn2-b3-fragment-count 0 0 1 off (len bytes) 1 0 1 b3 pool)))
             (consumed (fn2-b3-fragment-count 0 0 1 off (len bytes) 1 0 1 b3 pool))
             (ds (mv-nth 0 (fn2-b3-fragment-into 0 off (fn2-b3-fragment-count 0 0 1 off (len bytes) 1 0 1 b3 pool) ds b3 pool)))
             (b3 (mv-nth 1 (fn2-b3-fragment-into 0 off (fn2-b3-fragment-count 0 0 1 off (len bytes) 1 0 1 b3 pool) ds b3 pool))))
          (:instance fc-g-feed (off off) (consumed 0))
          (:instance fn2-b3-covers-drop (xs bytes) (n (fn2-b3-fragment-count 0 0 1 off (len bytes) 1 0 1 b3 pool)) (fn2-pool pool))
          (:instance fn2-b3-window-base (used 4096) (fn2-pool pool)))
    :in-theory (e/d (fn2-b3-update min) (fc-g-fragment)))))

; ---- format checker helpers ----

(include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)
(defun fc-le-induct (width x y)
  (if (zp width) (list x y)
    (fc-le-induct (1- width) (floor x 256) (floor y 256))))
(defun fc-le-fits (width x)
  (if (zp width) (equal x 0)
    (fc-le-fits (1- width) (floor x 256))))
(defthm fc-equal-by-byte-and-quotient
  (implies (and (natp x) (natp y)
                (equal (mod x 256) (mod y 256))
                (equal (floor x 256) (floor y 256)))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable mod))))
(defthm fc-le-prefix-injective
  (implies (and (natp width) (natp x) (natp y)
                (fc-le-fits width x) (fc-le-fits width y))
           (equal (equal (append (fn2-layout-le width x) a)
                         (append (fn2-layout-le width y) b))
                  (and (equal x y) (equal a b))))
  :hints (("Goal" :induct (fc-le-induct width x y)
                  :in-theory (enable fc-le-fits fn2-layout-le nfix))
          ("Subgoal *1/2" :use fc-equal-by-byte-and-quotient)))
(defthm fc-le-fits-at-fixed-width
  (implies (syntaxp (quotep width))
           (equal (fc-le-fits width x)
                  (if (zp width) (equal x 0)
                    (fc-le-fits (1- width) (floor x 256)))))
  :hints (("Goal" :expand (fc-le-fits width x))))
(defthm fc-u60-fits-eight
  (implies (unsigned-byte-p 60 x) (fc-le-fits 8 x))
  :hints (("Goal" :in-theory (enable fc-le-fits))))

(defthm fc-append-associative
  (equal (append (append a b) c) (append a (append b c))))
(defthm fc-cancel-common-prefix
  (equal (equal (append p a) (append p b)) (equal a b)))
(defthm fc-eight-byte-fields-injective
  (implies (and (unsigned-byte-p 60 x) (unsigned-byte-p 60 y))
           (equal (equal (append (fn2-layout-le 8 x) a)
                         (append (fn2-layout-le 8 y) b))
                  (and (equal x y) (equal a b))))
  :hints (("Goal" :use ((:instance fc-le-prefix-injective (width 8)))
                  :in-theory (disable fc-le-prefix-injective
                                      fc-le-fits-at-fixed-width fn2-layout-le))))
(defthm fc-frame-covered-binds-identity
  (implies (and (fn2-fc-expectedp a) (fn2-fc-expectedp b)
                (equal (fn2-fc-covered :frame bytes a)
                       (fn2-fc-covered :frame bytes b)))
           (equal (fn2-fc-frame-identity a) (fn2-fc-frame-identity b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn2-fc-covered fn2-fc-expectedp fn2-fc-frame-identity
                      fc-append-associative fc-cancel-common-prefix
                      fc-eight-byte-fields-injective)))))
(defthm fc-seal-covered-binds-identity
  (implies (and (fn2-fc-expectedp ca) (fn2-fc-expectedp cb)
                (equal (fn2-fc-covered :seal a ca)
                       (fn2-fc-covered :seal b cb)))
           (equal (fn2-fc-seal-identity ca) (fn2-fc-seal-identity cb)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn2-fc-covered fn2-fc-expectedp fn2-fc-seal-identity
                      fc-append-associative fc-cancel-common-prefix
                      fc-eight-byte-fields-injective)))))

(include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)
(defthm fc-u32-reconstruct
  (implies (unsigned-byte-p 32 x)
    (equal (+ (fn2-fc-word-byte x 0) (* 256 (fn2-fc-word-byte x 1))
              (* 65536 (fn2-fc-word-byte x 2)) (* 16777216 (fn2-fc-word-byte x 3)))
           x))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-fc-word-byte ash mod)) ("Goal''" :in-theory (enable floor))))

; Decode depends on the image and the budget only. This projection follows
; the same resumptions as the driver until the header decoder finishes.
(defun-nx fc-decoded-fields (fuel kind len fields pool)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel) fields
    (let ((step (fn2-fc-decode-step kind 0 0 1 0 len 1 0 1 4096 fields pool)))
      (if (eq (car step) :more)
          (fc-decoded-fields (1- fuel) kind len (mv-nth 2 step) pool)
        (mv-nth 2 step)))))
(defthm fc-decoded-more-requires-identity
  (implies (not (equal (fn2-fc-identity row kind base len ctx fields) :ok))
           (and (not (equal (car (fn2-fc-decoded row kind off len base next fc ctx b3 fields pool digs)) :more))
                (not (equal (car (fn2-fc-decoded row kind off len base next fc ctx b3 fields pool digs)) :ok))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                       '(fn2-fc-identity fn2-fc-decoded car-cons)))))
(defthm fc-mv-nth-zero (equal (mv-nth 0 x) (car x)))
(defthm fc-zero-plus-len (implies (natp x) (equal (+ 0 x) x)))
(defthm fc-drive-from-decode-binds-header
  (implies (and (natp len) (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-decode*)
                (equal (car (fn2-format-drive fuel 0 kind nil 0 1 0 len 0 1 0 1 4096
                                              fc ctx b3 fields pool digs)) :ok))
           (equal (fn2-fc-identity 0 kind 0 len ctx
                                   (fc-decoded-fields fuel kind len fields pool)) :ok))
  :rule-classes nil
  :hints (("Goal" :induct (fc-decoded-fields fuel kind len fields pool)
                  :in-theory (union-theories (theory 'minimal-theory)
                               '(fc-decoded-fields fn2-format-run fn2-fc-step
                                 car-cons cdr-cons mv-nth fc-mv-nth-zero fc-zero-plus-len fc-decoded-more-requires-identity)))
          ("Subgoal *1/3" :expand (:free (fc ctx b3 fields pool digs)
                             (fn2-format-drive fuel 0 kind nil 0 1 0 len 0 1 0 1 4096
                                               fc ctx b3 fields pool digs)))
          ("Subgoal *1/2" :expand (:free (fc ctx b3 fields pool digs)
                             (fn2-format-drive fuel 0 kind nil 0 1 0 len 0 1 0 1 4096
                                               fc ctx b3 fields pool digs)))
          ("Subgoal *1/1" :expand (:free (fc ctx b3 fields pool digs)
                             (fn2-format-drive fuel 0 kind nil 0 1 0 len 0 1 0 1 4096
                                               fc ctx b3 fields pool digs)))))
(defthm fc-phase-after-decode-start
  (equal (fn2-fc-phase 0 (fn2-fc-set-phase 0 *fn2-fc-phase-decode* fc))
         *fn2-fc-phase-decode*)
  :hints (("Goal" :in-theory (enable fn2-fc-phase fn2-fc-set-phase update-fn2-fc-phase$ai update-nth))))
(defthm fc-read-range-never-yields
  (not (equal (fn2-layout-range-code slot gen off end nil okind oslot ogen pool) :more))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                      '(fn2-layout-range-code fn2-pool-readable-code fn2-pool-handle-code)))))
(defthm fc-drive-from-idle-binds-header
  (implies (and (natp len) (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-idle*)
                (equal (car (fn2-format-drive fuel 0 kind nil 0 1 0 len 0 1 0 1 4096
                                              fc ctx b3 fields pool digs)) :ok))
           (equal (fn2-fc-identity 0 kind 0 len ctx
                     (fc-decoded-fields (1- fuel) kind len
                                        (fn2-fc-start kind 0 fields) pool)) :ok))
  :rule-classes nil
  :hints (("Goal" :expand (fn2-format-drive fuel 0 kind nil 0 1 0 len 0 1 0 1 4096
                                           fc ctx b3 fields pool digs)
                  :in-theory (union-theories (theory 'minimal-theory)
                               '(fn2-format-run fn2-fc-step car-cons cdr-cons
                                 mv-nth fc-mv-nth-zero fc-read-range-never-yields fc-phase-after-decode-start))
                  :use ((:instance fc-drive-from-decode-binds-header
                          (fuel (1- fuel)) (fields (fn2-fc-start kind 0 fields))
                          (fc (fn2-fc-set-phase 0 *fn2-fc-phase-decode* fc))
                          (b3 (mv-nth 1 (fn2-b3-init 0 0 (fn2-digest-slot 0 *fn2-b3-key*) digs b3)))
                          (digs (car (fn2-b3-init 0 0 (fn2-digest-slot 0 *fn2-b3-key*) digs b3))))))))
(defthm fc-header-mismatch-refuses
  (implies (and (natp len) (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-idle*)
                (not (equal (fn2-fc-identity 0 kind 0 len ctx
                               (fc-decoded-fields (1- fuel) kind len
                                                  (fn2-fc-start kind 0 fields) pool)) :ok)))
           (not (equal (car (fn2-format-drive fuel 0 kind nil 0 1 0 len 0 1 0 1 4096
                                              fc ctx b3 fields pool digs)) :ok)))
  :hints (("Goal" :use fc-drive-from-idle-binds-header
                  :in-theory (theory 'minimal-theory))))
(defun-nx fc-image-header (kind bytes)
  (let* ((len (len bytes))
         (pool (fn2-pool-init (list (cons 1 (max 1 len))) 1 100 (create-fn2-pool)))
         (pool (mv-nth 3 (fn2-pool-reserve 0 1 0 1 pool)))
         (pool (fn2-fc-spec-load bytes 0 pool))
         (fields (fn2-fields-init *fn2-format-sealed-batch-num-fields* (create-fn2-fields))))
    (fc-decoded-fields (1- (fn2-format-fuel len)) kind len (fn2-fc-start kind 0 fields) pool)))
(defun-nx fc-image-context (context)
  (car (fn2-fc-spec-context context 0
           (fn2-fc-context-init 1 (create-fn2-fc-context))
           (fn2-digests-init 144 (create-fn2-digests)))))
(defthm fc-image-initially-idle
  (equal (fn2-fc-phase 0 (fn2-fc-init 1 (create-fn2-fc))) *fn2-fc-phase-idle*))
(defthm fc-length-natural (natp (len bytes)))
(defthm fc-accepted-binds-header
  (implies (fn2-fc-acceptedp kind bytes context)
           (equal (fn2-fc-identity 0 kind 0 (len bytes) (fc-image-context context)
                                   (fc-image-header kind bytes)) :ok))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn2-fc-acceptedp fn2-fc-image fn2-fc-image-run
                      fc-image-context fc-image-header fc-mv-nth-zero car-cons cdr-cons
                      fc-header-mismatch-refuses fc-image-initially-idle fc-length-natural)))))

(defthm fc-image-context-scalars
  (and
    (equal (fn2-fc-context-location 0 (fc-image-context ctx)) (fn2-fc-expected-location ctx))
    (equal (fn2-fc-context-allocation 0 (fc-image-context ctx)) (fn2-fc-expected-allocation ctx))
    (equal (fn2-fc-context-history 0 (fc-image-context ctx)) (fn2-fc-expected-history ctx))
    (equal (fn2-fc-context-incarnation 0 (fc-image-context ctx)) (fn2-fc-expected-incarnation ctx))
    (equal (fn2-fc-context-writer-epoch 0 (fc-image-context ctx)) (fn2-fc-expected-writer-epoch ctx))
    (equal (fn2-fc-context-commit 0 (fc-image-context ctx)) (fn2-fc-expected-commit ctx))
    (equal (fn2-fc-context-page-kind 0 (fc-image-context ctx)) (fn2-fc-expected-page-kind ctx))
    (equal (fn2-fc-context-encoded-length 0 (fc-image-context ctx)) (fn2-fc-expected-encoded-length ctx))
    (equal (fn2-fc-context-extent-writer-epoch 0 (fc-image-context ctx)) (fn2-fc-expected-extent-writer-epoch ctx))
    (equal (fn2-fc-context-previous-commit 0 (fc-image-context ctx)) (fn2-fc-expected-previous-commit ctx))
    (equal (fn2-fc-context-extent 0 (fc-image-context ctx)) (fn2-fc-expected-extent ctx))
    (equal (fn2-fc-context-hash 0 (fc-image-context ctx)) (fn2-digest-slot 0 *fn2-fc-hash*)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
    '(fc-image-context fn2-fc-spec-context fc-mv-nth-zero car-cons nth-update-nth update-nth-array
      nfix (:executable-counterpart nfix)
      fn2-fc-context-location fn2-fc-context-allocation fn2-fc-context-history fn2-fc-context-incarnation fn2-fc-context-writer-epoch fn2-fc-context-commit fn2-fc-context-page-kind fn2-fc-context-encoded-length fn2-fc-context-extent-writer-epoch fn2-fc-context-previous-commit fn2-fc-context-extent fn2-fc-context-hash fn2-fc-context-geometry fn2-fc-context-previous-seal fn2-fc-context-set-location fn2-fc-context-set-allocation fn2-fc-context-set-history fn2-fc-context-set-incarnation fn2-fc-context-set-writer-epoch fn2-fc-context-set-commit fn2-fc-context-set-page-kind fn2-fc-context-set-encoded-length fn2-fc-context-set-extent-writer-epoch fn2-fc-context-set-previous-commit fn2-fc-context-set-extent fn2-fc-context-set-hash fn2-fc-context-set-geometry fn2-fc-context-set-previous-seal update-fn2-fc-context-location$ai update-fn2-fc-context-allocation$ai update-fn2-fc-context-history$ai update-fn2-fc-context-incarnation$ai update-fn2-fc-context-writer-epoch$ai update-fn2-fc-context-commit$ai update-fn2-fc-context-page-kind$ai update-fn2-fc-context-encoded-length$ai update-fn2-fc-context-extent-writer-epoch$ai update-fn2-fc-context-previous-commit$ai update-fn2-fc-context-extent$ai update-fn2-fc-context-hash$ai update-fn2-fc-context-geometry$ai update-fn2-fc-context-previous-seal$ai fn2-fc-context-location$ai fn2-fc-context-allocation$ai fn2-fc-context-history$ai fn2-fc-context-incarnation$ai fn2-fc-context-writer-epoch$ai fn2-fc-context-commit$ai fn2-fc-context-page-kind$ai fn2-fc-context-encoded-length$ai fn2-fc-context-extent-writer-epoch$ai fn2-fc-context-previous-commit$ai fn2-fc-context-extent$ai fn2-fc-context-hash$ai fn2-fc-context-geometry$ai fn2-fc-context-previous-seal$ai)))))

(include-book "std/lists/update-nth" :dir :system)
(defun-nx fc-expected-digests (ctx ds)
  (mv-nth 1 (fn2-fc-spec-context ctx 0 nil ds)))
(defthm fc-mv-second (equal (mv-nth 1 (cons a (cons b rest))) b))
(defthm fc-update-array-commutes
  (implies (and (natp c1) (natp c2) (or (not (equal c1 c2))
               (not (equal (nfix r1) (nfix r2)))))
           (equal (update-nth-array c1 r1 v1 (update-nth-array c2 r2 v2 ds))
                  (update-nth-array c2 r2 v2 (update-nth-array c1 r1 v1 ds))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (update-nth-array nth-update-nth nfix) (nth update-nth)))))
(defun-nx fc-workspace-write (c r v ds) (update-nth-array c r v ds))
(defthm fc-workspace-write-commutes
  (implies (and (natp c) (natp col) (natp row) (< (nfix r) *fn2-fc-hash*) (<= *fn2-fc-hash* row))
           (equal (fc-workspace-write c r v (update-nth-array col row w ds))
                  (update-nth-array col row w (fc-workspace-write c r v ds))))
  :hints (("Goal" :use ((:instance fc-update-array-commutes
                            (c1 c) (r1 r) (v1 v) (c2 col) (r2 row) (v2 w)))
                  :in-theory (enable nfix fc-workspace-write))))
(deftheory fc-expected-digest-layout
  '(fc-expected-digests fn2-fc-spec-context fc-mv-second
    (:executable-counterpart fn2-digest-slot) (:executable-counterpart natp)
    (:executable-counterpart <)
    fn2-digests-set-w0 fn2-digests-set-w1 fn2-digests-set-w2 fn2-digests-set-w3 fn2-digests-set-w4 fn2-digests-set-w5 fn2-digests-set-w6 fn2-digests-set-w7
    update-fn2-digests-w0$ai update-fn2-digests-w1$ai update-fn2-digests-w2$ai update-fn2-digests-w3$ai update-fn2-digests-w4$ai update-fn2-digests-w5$ai update-fn2-digests-w6$ai update-fn2-digests-w7$ai))
(defthm fc-workspace-write-expected-digests
  (implies (and (natp c) (< (nfix r) *fn2-fc-hash*))
           (equal (fc-workspace-write c r v (fc-expected-digests ctx ds))
                  (fc-expected-digests ctx (fc-workspace-write c r v ds))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                (cons 'fc-workspace-write-commutes (theory 'fc-expected-digest-layout))))))
(defthm fc-read-expected-digests
  (implies (and (natp c) (< (nfix r) *fn2-fc-hash*))
           (equal (nth r (nth c (fc-expected-digests ctx ds))) (nth r (nth c ds))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                (append '(nfix natp nth-update-nth update-nth-array (:executable-counterpart nfix))
                        (theory 'fc-expected-digest-layout))))))
(defmacro fc-digest-column (getter setter raw-get raw-set column)
  `(progn
     (defthm ,(fn2-columns-sym getter "-FC-WORKSPACE")
       (implies (< (nfix r) *fn2-fc-hash*)
                (equal (,getter r (fc-expected-digests ctx ds)) (,getter r ds)))
       :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                       '(,getter ,raw-get (:executable-counterpart natp) fc-read-expected-digests)))))
     (defthm ,(fn2-columns-sym setter "-FC-WORKSPACE")
       (implies (< (nfix r) *fn2-fc-hash*)
                (equal (,setter r v (fc-expected-digests ctx ds))
                       (fc-expected-digests ctx (,setter r v ds))))
       :hints (("Goal" :use ((:instance fc-workspace-write-expected-digests (c ,column)))
                :in-theory (union-theories (theory 'minimal-theory)
                                  '(,setter ,raw-set fc-workspace-write (:executable-counterpart natp))))))))
(fc-digest-column fn2-digests-w0 fn2-digests-set-w0 fn2-digests-w0$ai update-fn2-digests-w0$ai *fn2-digests-w0$ai*)
(fc-digest-column fn2-digests-w1 fn2-digests-set-w1 fn2-digests-w1$ai update-fn2-digests-w1$ai *fn2-digests-w1$ai*)
(fc-digest-column fn2-digests-w2 fn2-digests-set-w2 fn2-digests-w2$ai update-fn2-digests-w2$ai *fn2-digests-w2$ai*)
(fc-digest-column fn2-digests-w3 fn2-digests-set-w3 fn2-digests-w3$ai update-fn2-digests-w3$ai *fn2-digests-w3$ai*)
(fc-digest-column fn2-digests-w4 fn2-digests-set-w4 fn2-digests-w4$ai update-fn2-digests-w4$ai *fn2-digests-w4$ai*)
(fc-digest-column fn2-digests-w5 fn2-digests-set-w5 fn2-digests-w5$ai update-fn2-digests-w5$ai *fn2-digests-w5$ai*)
(fc-digest-column fn2-digests-w6 fn2-digests-set-w6 fn2-digests-w6$ai update-fn2-digests-w6$ai *fn2-digests-w6$ai*)
(fc-digest-column fn2-digests-w7 fn2-digests-set-w7 fn2-digests-w7$ai update-fn2-digests-w7$ai *fn2-digests-w7$ai*)
(defthm fc-mv-cons
  (equal (mv-nth i (cons a b)) (if (zp i) a (mv-nth (1- i) b))))
(defun fc-result (i term single)
  (if single term (if (zp i) (list 'car term) (list 'mv-nth i term))))
(defun fc-overlay-claims (outs i call over single)
  (declare (xargs :verify-guards nil))
  (if (atom outs) nil
    (cons (list 'equal (fc-result i over single)
                (if (eq (car outs) 'fn2-digests)
                    (list 'fc-expected-digests 'ctx (fc-result i call single))
                  (fc-result i call single)))
          (fc-overlay-claims (cdr outs) (1+ i) call over single))))
(defun fc-overlay-event (fn hyps world)
  (declare (xargs :verify-guards nil))
  (let* ((args (getpropc fn 'formals nil world))
         (outs (getpropc fn 'stobjs-out nil world))
         (rec (getpropc fn 'recursivep nil world))
         (call (subst 0 'row (cons fn args)))
         (over (subst '(fc-expected-digests ctx fn2-digests) 'fn2-digests call)))
    `(defthm ,(fn2-columns-sym fn "-FC-WORKSPACE")
       (implies (and ,@hyps)
                (and ,@(fc-overlay-claims outs 0 call over (equal (len outs) 1))))
       :hints (("Goal" :do-not '(preprocess) ,@(and rec (list :induct call :expand (list call over)))
                      :in-theory (e/d (,fn min ,@(and rec (list 'posp))) (mv-nth)))))))
(defmacro fc-overlay-op (fn &rest hyps)
  `(make-event (value (fc-overlay-event ',fn ',hyps (w state)))))
(defthm fc-mv-zero (equal (mv-nth 0 x) (car x)))
(defthm fc-nfix-small (implies (< x 120) (< (nfix x) 126))
  :hints (("Goal" :in-theory (enable nfix))))
(defthm fc-nfix-bound
  (implies (and (posp k) (< x k)) (< (nfix x) k))
  :hints (("Goal" :in-theory (enable nfix))))
(defthm fc-nfix-depth-decrease
  (implies (and (posp depth) (< (nfix depth) 54))
           (and (< (nfix (1- depth)) 54) (< (1- depth) 54)))
  :hints (("Goal" :in-theory (enable nfix))))
(defthm fc-nfix-nonpositive
  (implies (<= x 0) (equal (nfix x) 0)) :hints (("Goal" :in-theory (enable nfix))))
(defthm fc-nfix-noninteger
  (implies (not (integerp x)) (equal (nfix x) 0)) :hints (("Goal" :in-theory (enable nfix))))
(deftheory fc-hash-rules
  (union-theories (theory 'minimal-theory)
    '(fc-mv-cons fc-mv-zero car-cons cdr-cons
      (:executable-counterpart zp) (:executable-counterpart nfix)
      (:executable-counterpart fn2-digest-slot) fc-nfix-nonpositive fc-nfix-noninteger fc-nfix-small fc-nfix-bound fc-nfix-depth-decrease (:executable-counterpart posp)
      fn2-digests-w0-fc-workspace fn2-digests-set-w0-fc-workspace
      fn2-digests-w1-fc-workspace fn2-digests-set-w1-fc-workspace
      fn2-digests-w2-fc-workspace fn2-digests-set-w2-fc-workspace
      fn2-digests-w3-fc-workspace fn2-digests-set-w3-fc-workspace
      fn2-digests-w4-fc-workspace fn2-digests-set-w4-fc-workspace
      fn2-digests-w5-fc-workspace fn2-digests-set-w5-fc-workspace
      fn2-digests-w6-fc-workspace fn2-digests-set-w6-fc-workspace
      fn2-digests-w7-fc-workspace fn2-digests-set-w7-fc-workspace)))
(in-theory (theory 'fc-hash-rules))
(fc-overlay-op fn2-digest-copy (< (nfix dst) 126) (< (nfix src) 126))
(fc-overlay-op fn2-digest-iv (< (nfix dst) 126))
(fc-overlay-op fn2-b3-init (< (nfix key) 126))
(fc-overlay-op fn2-b3-parent-cv (< (nfix dst) 126) (< (nfix left) 126)
                                        (< (nfix right) 126) (< (nfix key) 126))
(fc-overlay-op fn2-b3-parent-root (< (nfix dst) 126) (< (nfix left) 126)
                                          (< (nfix right) 126) (< (nfix key) 126))
(fc-overlay-op fn2-b3-parent (< (nfix dst) 126) (< (nfix right) 126) (< level 54))
(fc-overlay-op fn2-b3-output (< (nfix dst) 126))
(fc-overlay-op fn2-b3-push (< (nfix src) 126) (< (nfix depth) 54))
(fc-overlay-op fn2-b3-flush)
(fc-overlay-op fn2-b3-byte)
(fc-overlay-op fn2-b3-subtree-cv-into (< (nfix dst) 126))
(fc-overlay-op fn2-b3-chunk-output-into)
(fc-overlay-op fn2-b3-bulk)
(fc-overlay-op fn2-b3-span)
(fc-overlay-op fn2-b3-feed)
(fc-overlay-op fn2-b3-fragment-into)
(fc-overlay-op fn2-b3-update)
(fc-overlay-op fn2-b3-fold (< (nfix dst) 126) (<= depth 54))
(fc-overlay-op fn2-b3-finish (< (nfix dst) 126))
(fc-overlay-op fn2-b3-finalize (< (nfix dst) 126))

(in-theory (current-theory :here))
(defun-nx fc-linked-digests (a b da db)
  (and (equal (fc-expected-digests a da) da)
       (equal (fc-expected-digests b da) db)))
(defun fc-same-outputs (indices a-call b-call)
  (declare (xargs :verify-guards nil))
  (if (atom indices) nil
    (cons (list 'equal (fc-result (car indices) b-call nil)
                       (fc-result (car indices) a-call nil))
          (fc-same-outputs (cdr indices) a-call b-call))))
(defmacro fc-linked-op (fn din dout &rest hyps)
  (let* ((single (eq dout :single))
         (a-call (subst 'da 'fn2-digests din))
         (b-call (subst 'db 'fn2-digests din))
         (dpos (if single 0 dout))
         (other (case fn (fn2-b3-update '(0 1 3))
                          ((fn2-b3-byte fn2-b3-init) '(1))))
         (proof (fn2-columns-sym fn "-FC-WORKSPACE")))
    `(defthm ,(fn2-columns-sym fn "-FC-LINKED")
       (implies (and (fc-linked-digests a b da db) ,@hyps)
                (and (fc-linked-digests a b ,(fc-result dpos a-call single)
                                            ,(fc-result dpos b-call single))
                     ,@(fc-same-outputs other a-call b-call)))
       :hints (("Goal" :use ((:instance ,proof (ctx a) (fn2-digests da) ,@(case fn ((fn2-b3-byte fn2-b3-init fn2-b3-update fn2-b3-finalize) '((fn2-b3 b3)))) ,@(case fn (fn2-b3-update '((fn2-pool pool))) (fn2-b3-init '((mode 0) (key 1))) (fn2-b3-finalize '((dst 125)))))
                             (:instance ,proof (ctx b) (fn2-digests da) ,@(case fn ((fn2-b3-byte fn2-b3-init fn2-b3-update fn2-b3-finalize) '((fn2-b3 b3)))) ,@(case fn (fn2-b3-update '((fn2-pool pool))) (fn2-b3-init '((mode 0) (key 1))) (fn2-b3-finalize '((dst 125))))))
                       :in-theory (union-theories (theory 'minimal-theory) '(fc-linked-digests (:executable-counterpart nfix) (:executable-counterpart <))))))))
(fc-linked-op fn2-b3-byte (fn2-b3-byte 0 byte fn2-digests b3) 0)
(fc-linked-op fn2-b3-finalize (fn2-b3-finalize 125 0 fn2-digests b3) :single)
(fc-linked-op fn2-b3-init (fn2-b3-init 0 0 1 fn2-digests b3) 0)
(fc-linked-op fn2-b3-update (fn2-b3-update 0 slot gen off len okind oslot ogen fn2-digests b3 pool) 2)
(defthm fc-phase-pos-updates
  (and (equal (fn2-fc-phase 0 (fn2-fc-set-phase 0 phase fc)) phase)
       (equal (fn2-fc-phase 0 (fn2-fc-set-pos 0 pos fc)) (fn2-fc-phase 0 fc))
       (equal (fn2-fc-pos 0 (fn2-fc-set-pos 0 pos fc)) pos)
       (equal (fn2-fc-pos 0 (fn2-fc-set-phase 0 phase fc)) (fn2-fc-pos 0 fc)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                     '(fn2-fc-phase fn2-fc-pos fn2-fc-set-pos fn2-fc-set-phase
                       fn2-fc-pos$ai fn2-fc-phase$ai update-fn2-fc-phase$ai
                       update-fn2-fc-pos$ai update-nth-array nth-update-nth
                       (:executable-counterpart nfix))))))
(defthm fc-pending-after-increment
  (implies (and (natp pos) (natp k) (<= pos k) (not (equal pos k)))
           (and (natp (+ 1 pos)) (<= (+ 1 pos) k)))
  :hints (("Goal" :in-theory (enable natp))))
