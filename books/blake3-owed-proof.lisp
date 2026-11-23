; Relate the table-backed hasher to the list BLAKE3 specification.
(in-package "ACL2")
(include-book "blake3")
(include-book "owed-discharge")

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

(local (defun fn2-b3-frontier-list (depth fn2-digests)
  (declare (xargs :stobjs fn2-digests :verify-guards nil))
  (if (zp depth) nil
    (cons (fn2-digest-list (+ *fn2-b3-frontier* (1- depth)) fn2-digests)
          (fn2-b3-frontier-list (1- depth) fn2-digests)))))

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
                  :expand ((:free (d) (fn2-b3-push 0 n d src fn2-digests fn2-b3))
                           (:free (cv key flags) (fn2-b3-push-list (fn2-b3-frontier-list depth fn2-digests) cv n key flags)))
                  :in-theory (e/d ((:induction fn2-b3-push)) (floor mod))))))

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
  (equal (nth n (cons a b)) (if (zp n) a (nth (1- n) b)))))

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
      (equal (fn2-digest-list 136 (fn2-b3-finish 136 0 root fn2-digests fn2-b3))
             (fn2-b3-fold-list (fn2-b3-frontier-list depth fn2-digests)
               (fn2-b3-output-words (fn2-b3-buffer-output t fn2-digests fn2-b3)
                                    (and root (equal depth 0)))
               (fn2-digest-list *fn2-b3-key* fn2-digests) 0 root))))
  :hints (("Goal" :in-theory (enable fn2-b3-finish)))))

(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

; Keep structural inductions independent of the table and layout rewrite rules.
(local (deftheory fn2-b3-list-arithmetic
  (union-theories (current-theory 'ground-zero)
    (set-difference-theories (current-theory :here)
                             (current-theory 'fn2-b3-finish-refines-list)))))
(local (defmacro fn2-b3-list-theory (&rest rules)
  `(union-theories (theory 'fn2-b3-list-arithmetic) ',rules)))

(local (defthm fn2-b3-decode-encoded-word
  (implies (unsigned-byte-p 32 w)
    (equal (fn-b3-le-word (mod w 256)
                          (mod (floor w 256) 256)
                          (mod (floor w 65536) 256)
                          (mod (floor w 16777216) 256))
           w))
  :hints (("Goal" :in-theory (enable fn-b3-le-word fn-b3-octet fn-b3-byte mod)))))

(local (defthm fn2-b3-digest-words-roundtrip
  (implies (fn-b3-word-listp words)
    (equal (fn-b3-words (len words) (fn-b3-words-octets words)) words))
  :hints (("Goal" :induct (len words) :in-theory (enable fn-b3-words fn-b3-words-octets
                                                          fn-b3-word)))))

; Pair adjacent subtree outputs until a single interval covers the message.
(local (defun fn2-b3-left-level-induct (k p)
  (if (zp k) p (fn2-b3-left-level-induct (1- k) (* 2 p)))))

(local (defthm fn2-b3-pow2-lower-bound
  (implies (posp k) (<= 2 (expt 2 k)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn2-b3-left-level-induct k 1)
                  :expand ((expt 2 k))))))

(local (defthm fn2-b3-left-at-level
  (implies (and (natp k) (posp p) (natp size)
                (< (* 1024 p (expt 2 k)) size)
                (<= size (* 2048 p (expt 2 k))))
           (equal (fn-b3-left-chunks p size) (* p (expt 2 k))))
  :hints (("Goal" :induct (fn2-b3-left-level-induct k p)
                  :nonlinearp t :expand ((fn-b3-left-chunks p size))))))

(local (in-theory (disable fn2-b3-left-at-level fn-b3-node fn-b3-left-chunks
                           fn-b3-chunk fn-b3-output)))

(local (defun fn2-b3-prefix-induct (a b xs)
  (if (or (zp a) (atom xs)) (list b xs)
    (fn2-b3-prefix-induct (1- a) (1- b) (cdr xs)))))

(local (defthm fn2-b3-first-of-first
  (implies (and (natp a) (natp b) (<= a b))
           (equal (fn-b3-firstn a (fn-b3-firstn b xs)) (fn-b3-firstn a xs)))
  :hints (("Goal" :induct (fn2-b3-prefix-induct a b xs)))))

(local (defthm fn2-b3-drop-of-first
  (implies (and (natp a) (natp b) (<= a b))
           (equal (fn-b3-nthcdrx a (fn-b3-firstn b xs))
                  (fn-b3-firstn (- b a) (fn-b3-nthcdrx a xs))))
  :hints (("Goal" :induct (fn2-b3-prefix-induct a b xs)))))

(local (defthm fn2-b3-drop-twice
  (implies (and (natp a) (natp b))
           (equal (fn-b3-nthcdrx b (fn-b3-nthcdrx a xs))
                  (fn-b3-nthcdrx (+ a b) xs)))
  :hints (("Goal" :induct (fn-b3-nthcdrx a xs)))))

(local (defthm fn2-b3-first-whole
  (implies (and (true-listp xs) (natp n) (<= (len xs) n))
           (equal (fn-b3-firstn n xs) xs))
  :hints (("Goal" :induct (fn-b3-firstn n xs)))))

(local (defun fn2-b3-node-at (chunks xs counter)
  (fn-b3-node *fn-b3-iv* (fn-b3-firstn (* 1024 chunks) xs) counter 0)))

(local (defun fn2-b3-pair-output (left right)
  (fn-b3-output *fn-b3-iv* (append (fn-b3-output-cv left) (fn-b3-output-cv right)) 0 64 4)))

(local (defthm fn2-b3-node-at-cut
  (implies (and (< 1024 (len xs)) (natp counter)
                (equal (fn-b3-left-chunks 1 (len xs)) chunks))
           (equal (fn-b3-node *fn-b3-iv* xs counter 0)
                  (fn2-b3-pair-output
                   (fn-b3-node *fn-b3-iv* (fn-b3-firstn (* 1024 chunks) xs) counter 0)
                   (fn-b3-node *fn-b3-iv* (fn-b3-nthcdrx (* 1024 chunks) xs)
                               (+ counter chunks) 0))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-b3-node *fn-b3-iv* xs counter 0))))))

(local (defthm fn2-b3-node-at-double-cut
  (implies (and (posp chunks) (natp counter)
                (equal (fn-b3-left-chunks 1 (min (* 2048 chunks) (len xs))) chunks)
                (< (* 1024 chunks) (len xs)))
           (equal (fn2-b3-node-at (* 2 chunks) xs counter)
                  (fn2-b3-pair-output
                    (fn2-b3-node-at chunks xs counter)
                    (fn2-b3-node-at chunks (fn-b3-nthcdrx (* 1024 chunks) xs)
                                    (+ counter chunks)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-b3-node-at-cut (xs (fn-b3-firstn (* 2048 chunks) xs))))
                  :do-not-induct t
                  :in-theory (e/d (fn2-b3-node-at) (|(* x (expt x n))| fn2-b3-pair-output fn-b3-firstn fn-b3-nthcdrx))))))

(local (defthm fn2-b3-node-at-double
  (implies (and (natp k) (equal chunks (expt 2 k)) (natp counter)
                (< (* 1024 chunks) (len xs)))
           (equal (fn2-b3-node-at (* 2 chunks) xs counter)
                  (fn2-b3-pair-output
                    (fn2-b3-node-at chunks xs counter)
                    (fn2-b3-node-at chunks (fn-b3-nthcdrx (* 1024 chunks) xs)
                                    (+ counter chunks)))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-b3-node-at-double-cut
                         (:instance fn2-b3-left-at-level (p 1) (size (min (* 2048 chunks) (len xs)))))
                  :in-theory (disable fn2-b3-node-at fn2-b3-pair-output)))))

(local (defthm fn2-b3-pair-output-words
  (equal (fn2-b3-output-words (fn2-b3-pair-output left right) root)
         (fn2-b3-join *fn-b3-iv* (fn-b3-output-cv left) (fn-b3-output-cv right) 0 root))
  :hints (("Goal" :in-theory (enable fn2-b3-pair-output fn2-b3-output-words
                                     fn-b3-output-cv fn-b3-output fn2-b3-join)))))

(local (defthm fn2-b3-output-words-cv
  (equal (fn2-b3-output-words out nil) (fn-b3-output-cv out))
  :hints (("Goal" :in-theory (enable fn2-b3-output-words)))))

(local (defthm fn2-b3-cv-of-pair
  (equal (fn-b3-output-cv (fn2-b3-pair-output left right))
         (fn2-b3-join *fn-b3-iv* (fn-b3-output-cv left) (fn-b3-output-cv right) 0 nil))
  :hints (("Goal" :use ((:instance fn2-b3-pair-output-words (root nil)))
                  :in-theory (disable fn2-b3-pair-output fn2-b3-pair-output-words)))))

(local (defun fn2-b3-units (k) (expt 2 (nfix k))))
(local (defthm fn2-b3-units-next
  (implies (natp k) (equal (fn2-b3-units (+ 1 k)) (* 2 (fn2-b3-units k))))))
(local (defthm fn2-b3-units-positive
  (and (integerp (fn2-b3-units k)) (< 0 (fn2-b3-units k)))
  :rule-classes :type-prescription))
(local (defthm fn2-b3-units-double-node
  (implies (and (natp k) (natp counter) (< (* 1024 (fn2-b3-units k)) (len xs)))
           (equal (fn2-b3-node-at (* 2 (fn2-b3-units k)) xs counter)
                  (fn2-b3-pair-output
                   (fn2-b3-node-at (fn2-b3-units k) xs counter)
                   (fn2-b3-node-at (fn2-b3-units k)
                                   (fn-b3-nthcdrx (* 1024 (fn2-b3-units k)) xs)
                                   (+ counter (fn2-b3-units k))))))
  :hints (("Goal" :use ((:instance fn2-b3-node-at-double (chunks (fn2-b3-units k))))
                  :in-theory (disable fn2-b3-node-at fn2-b3-pair-output)))))

(local (in-theory (disable fn2-b3-units fn2-b3-node-at fn2-b3-pair-output
                           fn-b3-firstn fn-b3-nthcdrx fn2-b3-push-list fn2-b3-fold-list)))

(local (defun fn2-b3-seal (stack out root)
  (if (atom stack) (fn2-b3-output-words out root)
    (fn2-b3-fold-list stack (fn-b3-output-cv out) *fn-b3-iv* 0 root))))

(local (defthm fn2-b3-seal-pair
  (equal (fn2-b3-seal (cons (fn-b3-output-cv left) stack) right root)
         (fn2-b3-seal stack (fn2-b3-pair-output left right) root))
  :hints (("Goal" :expand ((:free (cv key flags r) (fn2-b3-fold-list (cons (fn-b3-output-cv left) stack) cv key flags r))
                           (:free (cv key flags r) (fn2-b3-fold-list stack cv key flags r)))
                  :in-theory (enable fn2-b3-join) :cases ((consp stack))))))
(local (in-theory (disable fn2-b3-seal)))

(local (defun fn2-b3-scan (chunks xs n counter stack root)
  (declare (xargs :measure (len xs)))
  (let* ((w (* 1024 (if (posp chunks) chunks 1)))
         (out (fn2-b3-node-at chunks xs counter)))
    (if (<= (len xs) w) (fn2-b3-seal stack out root)
      (fn2-b3-scan chunks (fn-b3-nthcdrx w xs) (+ 1 (nfix n)) (+ (nfix counter) (if (posp chunks) chunks 1))
                   (fn2-b3-push-list stack (fn-b3-output-cv out) n *fn-b3-iv* 0)
                   root)))))

(local (defthm fn2-b3-push-pair-left
  (implies (natp i)
           (equal (fn2-b3-push-list stack cv (+ 1 (* 2 i)) key flags)
                  (cons cv stack)))
  :hints (("Goal" :expand ((fn2-b3-push-list stack cv (+ 1 (* 2 i)) key flags))))))

(local (defthm fn2-b3-push-pair-right
  (implies (natp i)
           (equal (fn2-b3-push-list (cons left stack) cv (+ 2 (* 2 i)) key flags)
                  (fn2-b3-push-list stack (fn2-b3-join key left cv flags nil)
                                    (+ 1 i) key flags)))
  :hints (("Goal" :expand ((fn2-b3-push-list (cons left stack) cv (+ 2 (* 2 i)) key flags))))))

(local (defthm fn2-b3-drop-true-list
  (implies (true-listp xs) (true-listp (fn-b3-nthcdrx n xs)))
  :hints (("Goal" :induct (fn-b3-nthcdrx n xs)
                  :in-theory (fn2-b3-list-theory fn-b3-nthcdrx)))))

(local (defthm fn2-b3-short-node
  (implies (and (posp chunks) (true-listp xs) (<= (len xs) (* 1024 chunks)))
           (equal (fn2-b3-node-at chunks xs counter) (fn-b3-node *fn-b3-iv* xs counter 0)))
  :hints (("Goal" :in-theory (enable fn2-b3-node-at)))))

(local (defun fn2-b3-pairs-induct (k xs i counter stack)
  (declare (xargs :measure (len xs)))
  (let ((units (fn2-b3-units k)))
    (if (<= (len xs) (* 2048 units)) (list i counter stack)
      (fn2-b3-pairs-induct k (fn-b3-nthcdrx (* 2048 units) xs) (+ 1 i)
                           (+ counter (* 2 units))
                           (fn2-b3-push-list stack (fn-b3-output-cv (fn2-b3-node-at (* 2 units) xs counter))
                                             (+ 1 i) *fn-b3-iv* 0))))))

(local (in-theory (disable fn2-b3-scan)))

(local (defthm fn2-b3-scan-coarsen
  (implies (and (natp k) (true-listp xs) (natp counter) (natp i))
    (let ((u (fn2-b3-units k)))
      (equal (fn2-b3-scan u xs (+ 1 (* 2 i)) counter stack root)
             (fn2-b3-scan (* 2 u) xs (+ 1 i) counter stack root))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-b3-pairs-induct k xs i counter stack)
           :expand ((:free (u n st) (fn2-b3-scan u xs n counter st root))
                    (:free (n ctr st)
                           (fn2-b3-scan (fn2-b3-units k)
                                        (fn-b3-nthcdrx (* 1024 (fn2-b3-units k)) xs)
                                        n ctr st root)))
           :in-theory (disable fn2-b3-short-node))
          ("Subgoal *1/1" :cases ((<= (len xs) (* 1024 (fn2-b3-units k))))
                          :use ((:instance fn2-b3-short-node (chunks (fn2-b3-units k)))
                                (:instance fn2-b3-short-node (chunks (* 2 (fn2-b3-units k)))))
                          :in-theory (disable fn2-b3-short-node)))))
(local (defun fn2-b3-double-until-covered (k xs)
  (declare (xargs :measure (nfix (- (len xs) (* 1024 (fn2-b3-units k)))) ))
  (if (or (not (natp k)) (<= (len xs) (* 1024 (fn2-b3-units k)))) k
    (fn2-b3-double-until-covered (1+ k) xs))))

(local (defthm fn2-b3-scan-is-node
  (implies (and (natp k) (true-listp xs) (natp counter))
    (equal (fn2-b3-scan (fn2-b3-units k) xs 1 counter nil root)
           (fn2-b3-output-words (fn-b3-node *fn-b3-iv* xs counter 0) root)))
  :hints (("Goal" :induct (fn2-b3-double-until-covered k xs))
          ("Subgoal *1/2" :use ((:instance fn2-b3-scan-coarsen (i 0) (stack nil))))
          ("Subgoal *1/1" :expand ((fn2-b3-scan (fn2-b3-units k) xs 1 counter nil root))
                          :in-theory (enable fn2-b3-seal)))))

(local (defthm fn2-b3-decode-root
  (equal (fn-b3-words 8 (fn-b3-output-root out)) (fn2-b3-output-words out t))
  :hints (("Goal" :in-theory (enable fn-b3-output-root fn2-b3-output-words)
                  :use ((:instance fn2-b3-digest-words-roundtrip
                                   (words (fn2-b3-output-words out t))))))))

(local (defthm fn2-b3-octets-true-list
  (implies (fn-b3-octet-listp xs) (true-listp xs)) :rule-classes :forward-chaining))

(local (defthm fn2-b3-scan-is-blake3
  (implies (and (natp k) (fn-b3-octet-listp xs))
    (equal (fn2-b3-scan (fn2-b3-units k) xs 1 0 nil t)
           (fn-b3-words 8 (fn-blake3 xs))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-b3-hash)))))
; The frontier contains one chaining value per set bit of the completed count.
(local (defun fn2-b3-bits (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) 0 (+ (mod n 2) (fn2-b3-bits (floor n 2))))))

(local (defthm fn2-b3-bits-natp (natp (fn2-b3-bits n)) :rule-classes :type-prescription))
(local (defthm fn2-b3-bits-even
  (implies (natp i) (equal (fn2-b3-bits (* 2 i)) (fn2-b3-bits i)))
  :hints (("Goal" :expand ((fn2-b3-bits (* 2 i)))))))
(local (defthm fn2-b3-bits-odd
  (implies (natp i) (equal (fn2-b3-bits (+ 1 (* 2 i))) (1+ (fn2-b3-bits i))))
  :hints (("Goal" :expand ((fn2-b3-bits (+ 1 (* 2 i))))))))

(local (defthm fn2-b3-previous-bits
  (implies (posp n)
    (and (implies (equal (mod n 2) 0)
                  (equal (fn2-b3-bits (1- n)) (1+ (fn2-b3-bits (1- (floor n 2))))))
         (implies (not (equal (mod n 2) 0))
                  (equal (fn2-b3-bits (1- n)) (fn2-b3-bits (floor n 2))))))
  :hints (("Goal" :use ((:instance fn2-b3-bits-odd (i (1- (floor n 2))))
                         (:instance fn2-b3-bits-even (i (floor n 2))))
                  :in-theory (disable fn2-b3-bits fn2-b3-bits-even fn2-b3-bits-odd)))))

(local (defthm fn2-b3-frontier-length
  (equal (len (fn2-b3-frontier-list depth fn2-digests)) (nfix depth))))
(local (defthm fn2-b3-frontier-length-after-carry
  (implies (and (posp n) (equal (len stack) (fn2-b3-bits (1- n))))
           (equal (len (fn2-b3-push-list stack cv n key flags)) (fn2-b3-bits n)))
  :hints (("Goal" :induct (fn2-b3-push-list stack cv n key flags)
                  :expand ((fn2-b3-bits n) (fn2-b3-push-list stack cv n key flags))
                  :in-theory (e/d ((:induction fn2-b3-push-list)) (fn2-b3-bits))))))

(local (defun fn2-b3-bit-induct (n k)
  (if (zp k) n (fn2-b3-bit-induct (floor n 2) (1- k)))))

(local (defthm fn2-b3-double-prev-expt
  (implies (posp k) (equal (expt 2 k) (* 2 (expt 2 (1- k)))))
  :hints (("Goal" :expand ((expt 2 k))))
  :rule-classes :linear))

(local (defthm fn2-b3-bits-bound
  (implies (and (natp k) (natp n) (< n (expt 2 k)))
           (<= (fn2-b3-bits n) k))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-b3-bit-induct n k)
                  :expand ((fn2-b3-bits n))))))

(local (in-theory (disable fn2-b3-double-prev-expt)))

(local (defthm fn2-b3-pushed-depth-natp
  (natp (fn2-b3-depth 0 (mv-nth 1 (fn2-b3-push 0 n d src fn2-digests fn2-b3))))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn2-b3-push 0 n d src fn2-digests fn2-b3)
                  :in-theory (e/d (fn2-b3-push) (fn2-b3-depth fn2-b3-bits floor mod))))))

(local (defthm fn2-b3-pushed-depth
  (implies (and (posp n) (natp d) (natp src) (< (+ *fn2-b3-frontier* d) src)
                (equal d (fn2-b3-bits (1- n))))
    (equal (fn2-b3-depth 0 (mv-nth 1 (fn2-b3-push 0 n d src fn2-digests fn2-b3)))
           (fn2-b3-bits n)))
  :hints (("Goal" :use
           ((:instance fn2-b3-push-refines-list (depth d))
            (:instance fn2-b3-frontier-length-after-carry
                       (stack (fn2-b3-frontier-list d fn2-digests))
                       (cv (fn2-digest-list src fn2-digests))
                       (key (fn2-digest-list *fn2-b3-key* fn2-digests))
                       (flags (fn2-b3-flags 0 fn2-b3)))
            (:instance fn2-b3-frontier-length (depth d))
            (:instance fn2-b3-frontier-length
                       (depth (fn2-b3-depth 0 (mv-nth 1 (fn2-b3-push 0 n d src fn2-digests fn2-b3))))
                       (fn2-digests (mv-nth 0 (fn2-b3-push 0 n d src fn2-digests fn2-b3)))))
           :in-theory (disable fn2-b3-frontier-length-after-carry fn2-b3-push-refines-list fn2-b3-frontier-length fn2-b3-frontier-list fn2-b3-bits fn2-b3-previous-bits)))))

(local (defthm fn2-b3-take-length
  (implies (and (true-listp xs) (equal (len xs) n)) (equal (take n xs) xs))
  :hints (("Goal" :induct (len xs) :in-theory (fn2-b3-list-theory)))))

(local (defthm fn2-b3-eight-words
  (implies (and (true-listp ws) (equal (len ws) 8))
           (equal (list (nth 0 ws) (nth 1 ws) (nth 2 ws) (nth 3 ws)
                        (nth 4 ws) (nth 5 ws) (nth 6 ws) (nth 7 ws)) ws))
  :hints (("Goal" :use ((:instance fn2-b3-take-length (xs ws) (n 8)))
                  :in-theory (fn2-b3-list-theory)))))

(local (defthm fn2-b3-read-load
  (implies (and (natp i) (natp dst) (true-listp ws) (equal (len ws) 8))
           (equal (fn2-digest-list i (fn2-digest-load dst ws fn2-digests))
                  (if (equal i dst) ws (fn2-digest-list i fn2-digests))))
  :hints (("Goal" :cases ((equal i dst)) :in-theory (enable fn2-digest-list fn2-digest-load)))))

(local (defthm fn2-b3-load-preserves-frontier
  (implies (and (natp dst) (<= (+ *fn2-b3-frontier* (nfix d)) dst)
                (true-listp ws) (equal (len ws) 8))
           (equal (fn2-b3-frontier-list d (fn2-digest-load dst ws fn2-digests))
                  (fn2-b3-frontier-list d fn2-digests)))
  :hints (("Goal" :induct (fn2-b3-frontier-list d fn2-digests) :in-theory (disable fn2-digest-load)))))
(local (in-theory (disable fn2-b3-bits fn2-b3-previous-bits fn2-digest-load
                           fn2-b3-frontier-list fn2-b3-split-digest fn2-b3-subtree-inputsp)))
(local (defthm fn2-b3-bits-positive
  (implies (posp n) (< 0 (fn2-b3-bits n)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :induct (fn2-b3-bits n) :in-theory (enable fn2-b3-bits)))))

(local (defun fn2-b3-block-bytes (blocks)
  (if (atom blocks) nil
    (append (fn2-b3-flatten (car blocks)) (fn2-b3-block-bytes (cdr blocks))))))

(local (defthm fn2-b3-flatten-append
  (equal (fn2-b3-flatten (append a b)) (append (fn2-b3-flatten a) (fn2-b3-flatten b)))))
(local (defthm fn2-b3-block-bytes-flatten
  (equal (fn2-b3-flatten (fn2-b3-flatten blocks)) (fn2-b3-block-bytes blocks))))

(local (defthm fn2-b3-octets-append
  (implies (and (fn-b3-octet-listp xs) (fn-b3-octet-listp ys))
           (fn-b3-octet-listp (append xs ys)))))
(local (defthm fn2-b3-splits-octets
  (implies (fn2-b3-splitsp splits) (fn-b3-octet-listp (fn2-b3-flatten splits)))))
(local (defthm fn2-b3-block-octets
  (implies (fn2-b3-subtree-inputsp blocks counters counter)
           (fn-b3-octet-listp (fn2-b3-block-bytes blocks)))
  :hints (("Goal" :induct (fn2-b3-subtree-inputsp blocks counters counter)
                  :in-theory (enable fn2-b3-subtree-inputsp)))))

(local (defthm fn2-b3-len-append
  (equal (len (append xs ys)) (+ (len xs) (len ys)))))

(local (defthm fn2-b3-block-nonempty
  (implies (and (consp blocks) (fn2-b3-subtree-inputsp blocks counters counter))
           (< 0 (len (fn2-b3-block-bytes blocks))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :expand ((fn2-b3-subtree-inputsp blocks counters counter)
                           (fn2-b3-block-bytes blocks))))))

(local (defthm fn2-b3-cut-append
  (implies (and (true-listp a) (equal n (len a)))
           (and (equal (fn-b3-firstn n (append a b)) a)
                (equal (fn-b3-nthcdrx n (append a b)) b)))
  :hints (("Goal" :induct (len a) :in-theory (fn2-b3-list-theory fn-b3-firstn fn-b3-nthcdrx)))))

(local (defun fn2-b3-block-cvsp (blocks counters)
  (if (atom blocks) t
    (and (equal (fn2-b3-split-digest (car blocks) (car counters) nil)
                (fn-b3-output-cv
                 (fn-b3-node *fn-b3-iv* (fn2-b3-flatten (car blocks)) (car counters) 0)))
         (fn2-b3-block-cvsp (cdr blocks) (cdr counters))))))

(local (defthm fn2-b3-node-at-block
  (implies (and (consp blocks) (fn2-b3-subtree-inputsp blocks counters ctr))
    (equal (fn2-b3-node-at 64 (fn2-b3-block-bytes blocks) ctr)
           (fn-b3-node *fn-b3-iv* (fn2-b3-flatten (car blocks)) ctr 0)))
  :hints (("Goal" :expand ((fn2-b3-subtree-inputsp blocks counters ctr)
                           (fn2-b3-block-bytes blocks))
                  :in-theory (enable fn2-b3-node-at)))))

(local (defthm fn2-b3-after-block
  (implies (and (consp blocks) (consp (cdr blocks)) (fn2-b3-subtree-inputsp blocks counters ctr))
           (equal (fn-b3-nthcdrx 65536 (fn2-b3-block-bytes blocks))
                  (fn2-b3-block-bytes (cdr blocks))))
  :hints (("Goal" :expand ((fn2-b3-subtree-inputsp blocks counters ctr)
                           (fn2-b3-block-bytes blocks))))))


(local (defthm fn2-b3-block-input-facts
  (implies (and (consp blocks) (natp ctr) (fn2-b3-subtree-inputsp blocks counters ctr))
    (and (equal (car counters) ctr)
         (fn2-b3-subtree-inputsp (cdr blocks) (cdr counters) (+ 64 ctr))
         (if (consp (cdr blocks))
             (equal (len (fn2-b3-block-bytes blocks)) (+ 65536 (len (fn2-b3-block-bytes (cdr blocks)))))
           (<= (len (fn2-b3-block-bytes blocks)) 65536))))
  :hints (("Goal" :expand ((fn2-b3-subtree-inputsp blocks counters ctr)
                           (fn2-b3-block-bytes blocks))))))

(local (in-theory (disable fn2-b3-block-bytes fn2-b3-block-cvsp fn2-b3-compose-loop)))

(local (defthm fn2-b3-scan-block-step
  (implies (and (posp n) (natp ctr) (consp blocks)
                (fn2-b3-subtree-inputsp blocks counters ctr) (fn2-b3-block-cvsp blocks counters)
                (or (consp stack) (consp (cdr blocks))))
    (let ((cv (fn2-b3-split-digest (car blocks) (car counters) nil)))
      (equal (fn2-b3-scan 64 (fn2-b3-block-bytes blocks) n ctr stack t)
             (if (consp (cdr blocks))
                 (fn2-b3-scan 64 (fn2-b3-block-bytes (cdr blocks)) (+ 1 n) (+ 64 ctr)
                              (fn2-b3-push-list stack cv n *fn-b3-iv* 0) t)
               (fn2-b3-fold-list stack cv *fn-b3-iv* 0 t)))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn2-b3-scan 64 (fn2-b3-block-bytes blocks) n ctr stack t)
                           (fn2-b3-block-cvsp blocks counters))
                  :use (fn2-b3-block-input-facts
                        (:instance fn2-b3-block-nonempty (blocks (cdr blocks))
                                   (counters (cdr counters)) (counter (+ 64 ctr))))
                  :in-theory (enable fn2-b3-seal)))))

(local (defthm fn2-b3-split-shape-from-cvs
  (implies (and (consp blocks) (fn2-b3-block-cvsp blocks counters))
           (and (true-listp (fn2-b3-split-digest (car blocks) (car counters) nil))
                (equal (len (fn2-b3-split-digest (car blocks) (car counters) nil)) 8)
                (fn2-b3-block-cvsp (cdr blocks) (cdr counters))))
  :hints (("Goal" :expand ((fn2-b3-block-cvsp blocks counters))))))

(local (defthm fn2-b3-compose-refines-scan
  (let ((depth (fn2-b3-depth 0 fn2-b3))
        (ctr (* 64 (1- n))))
    (implies (and (consp blocks) (posp n) (or (< 1 n) (consp (cdr blocks)))
                  (< (+ (* 65536 (1- n)) (len (fn2-b3-block-bytes blocks))) (expt 2 64))
                  (fn2-b3-subtree-inputsp blocks counters ctr)
                  (fn2-b3-block-cvsp blocks counters)
                  (equal depth (fn2-b3-bits (1- n)))
                  (equal (fn2-b3-flags 0 fn2-b3) 0)
                  (equal (fn2-digest-list *fn2-b3-key* fn2-digests) *fn-b3-iv*))
      (equal (mv-nth 0 (fn2-b3-compose-loop blocks counters n fn2-digests fn2-b3))
             (fn2-b3-scan 64 (fn2-b3-block-bytes blocks) n ctr
                          (fn2-b3-frontier-list depth fn2-digests) t))))
  :hints (("Goal" :induct (fn2-b3-compose-loop blocks counters n fn2-digests fn2-b3)
                  :in-theory (e/d ((:induction fn2-b3-compose-loop)) (fn2-b3-block-input-facts))
                  :expand ((fn2-b3-compose-loop blocks counters n fn2-digests fn2-b3)))
          ("Subgoal *1/3" :use
           ((:instance fn2-b3-block-input-facts (ctr (* 64 (1- n))))
            (:instance fn2-b3-push-refines-list
              (depth (fn2-b3-depth 0 fn2-b3)) (src 136)
              (fn2-digests (fn2-digest-load 136 (fn2-b3-split-digest (car blocks) (car counters) nil) fn2-digests)))
            (:instance fn2-b3-bits-bound (k 48) (n (1- n)))
            (:instance fn2-b3-scan-block-step (ctr (* 64 (1- n)))
                       (stack (fn2-b3-frontier-list (fn2-b3-depth 0 fn2-b3) fn2-digests)))))
          ("Subgoal *1/2" :use
           ((:instance fn2-b3-bits-bound (k 48) (n (1- n)))
            (:instance fn2-b3-scan-block-step (ctr (* 64 (1- n)))
                       (stack (fn2-b3-frontier-list (fn2-b3-depth 0 fn2-b3) fn2-digests))))))))
(local (defthm fn2-b3-compose-start
  (implies (and (fn2-b3-subtree-hyps blocks counters)
                (fn2-b3-block-cvsp blocks counters)
                (equal (fn2-b3-depth 0 fn2-b3) 0) (equal (fn2-b3-flags 0 fn2-b3) 0)
                (equal (fn2-digest-list 1 fn2-digests) *fn-b3-iv*))
           (equal (mv-nth 0 (fn2-b3-compose-loop blocks counters 1 fn2-digests fn2-b3))
                  (fn-b3-words 8 (fn-blake3 (fn2-b3-block-bytes blocks)))))
  :hints (("Goal" :use ((:instance fn2-b3-compose-refines-scan (n 1))
                        (:instance fn2-b3-scan-is-blake3 (k 6) (xs (fn2-b3-block-bytes blocks)))
                        (:instance fn2-b3-block-octets (counter 0)))
                  :expand ((fn2-b3-frontier-list 0 fn2-digests)) :in-theory (disable fn2-b3-compose-refines-scan fn2-b3-block-octets)))))

(local (defthm fn2-b3-read-iv
  (equal (fn2-digest-list 1 (fn2-digest-iv 1 fn2-digests)) *fn-b3-iv*)
  :hints (("Goal" :in-theory (enable fn2-digest-iv fn2-digest-list)))))

(local (defthm fn2-b3-init-observations
  (mv-let (dg b3) (fn2-b3-init 0 0 136 fn2-digests fn2-b3)
    (and (equal (fn2-b3-depth 0 b3) 0) (equal (fn2-b3-flags 0 b3) 0)
         (equal (fn2-digest-list 1 dg) *fn-b3-iv*)
         (equal (fn2-digest-list 0 dg) *fn-b3-iv*)))
  :hints (("Goal" :in-theory (enable fn2-b3-init fn2-b3-depth fn2-b3-flags)))))

(local (defthm fn2-b3-compose-correct-from-cvs
  (implies (and (fn2-b3-subtree-hyps blocks counters) (fn2-b3-block-cvsp blocks counters))
           (fn2-b3-subtree-resultp blocks counters))
  :hints (("Goal" :use ((:instance fn2-b3-compose-start
                    (fn2-digests (mv-nth 0 (fn2-b3-init 0 0 136
                      (fn2-digests-init 144 (create-fn2-digests)) (fn2-b3-table-init 1 (create-fn2-b3)))))
                    (fn2-b3 (mv-nth 1 (fn2-b3-init 0 0 136
                      (fn2-digests-init 144 (create-fn2-digests)) (fn2-b3-table-init 1 (create-fn2-b3))))))
                    (:instance fn2-b3-init-observations (fn2-digests (fn2-digests-init 144 (create-fn2-digests)))
                                                (fn2-b3 (fn2-b3-table-init 1 (create-fn2-b3)))))
                  :in-theory (e/d (fn2-b3-compose-sources fn2-b3-subtree-resultp)
                                  (fn2-b3-subtree-hyps fn2-b3-compose-start fn2-b3-init-observations))))))
; Slot zero is the checked 4096-byte workspace used by the split adapter.
(local (defun fn2-b3-windowp (used fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (and (equal (fn2-pool-workspace-code 0 1 1 0 1 fn2-pool) :ok)
       (equal (fn2-pool-readable-code 0 1 1 0 1 fn2-pool) :ok)
       (equal (fn2-pool-rows fn2-pool) 1)
       (equal (fn2-pool-base 0 fn2-pool) 0)
       (equal (fn2-pool-cap 0 fn2-pool) 4096)
       (equal (fn2-pool-data-length fn2-pool) 4096)
       (equal (fn2-pool-fill 0 fn2-pool) used))))

(local (defthm fn2-b3-window-update-len
  (implies (and (natp i) (< i (len xs)))
           (equal (len (update-nth i v xs)) (len xs)))))

(local (defthm fn2-b3-window-write
  (implies (and (fn2-b3-windowp off fn2-pool) (natp off) (< off 4096)
                (unsigned-byte-p 8 b))
    (mv-let (code pool) (fn2-pool-write 0 1 off b 1 0 1 fn2-pool)
      (and (equal code :ok) (fn2-b3-windowp (1+ off) pool)
           (implies (natp i)
                    (equal (fn2-pool-datai i pool) (if (equal i off) b (fn2-pool-datai i fn2-pool)))))))
  :hints (("Goal" :in-theory (enable fn2-pool-write fn2-pool-workspace-code fn2-pool-handle-code
                                     fn2-pool-readable-code fn2-pool-ownerp
                                     fn2-pool-datai update-fn2-pool-datai fn2-pool-data-length)))))

(local (defthm fn2-b3-window-reset
  (implies (fn2-b3-windowp used fn2-pool)
           (fn2-b3-windowp 0 (mv-nth 1 (fn2-pool-reset 0 1 1 0 1 fn2-pool))))
  :hints (("Goal" :in-theory (enable fn2-pool-reset fn2-pool-workspace-code fn2-pool-handle-code
                                     fn2-pool-readable-code fn2-pool-ownerp fn2-pool-data-length)))))

(local (in-theory (disable fn2-b3-windowp fn2-pool-write fn2-pool-datai fn2-pool-reset)))

(local (defthm fn2-b3-window-loaded
  (implies (and (fn2-b3-windowp off fn2-pool) (natp off) (<= (+ off (len xs)) 4096)
                (fn-b3-octet-listp xs))
           (fn2-b3-windowp (+ off (len xs)) (fn2-b3-spec-load xs off fn2-pool)))
  :hints (("Goal" :induct (fn2-b3-spec-load xs off fn2-pool)))))

(local (defthm fn2-b3-window-loaded-byte
  (implies (and (fn2-b3-windowp off fn2-pool) (natp off) (<= (+ off (len xs)) 4096)
                (fn-b3-octet-listp xs) (natp i))
           (equal (fn2-pool-datai i (fn2-b3-spec-load xs off fn2-pool))
                  (if (and (<= off i) (< i (+ off (len xs))))
                      (nth (- i off) xs)
                    (fn2-pool-datai i fn2-pool))))
  :hints (("Goal" :induct (fn2-b3-spec-load xs off fn2-pool)
                  :expand ((nth (+ i (- off)) xs))))))

(local (defthm fn2-b3-window-read
  (implies (and (fn2-b3-windowp used fn2-pool) (natp used) (<= used 4096) (natp off) (< off used))
           (equal (fn2-b3-read 0 1 off 1 0 1 fn2-pool) (mv :ok (fn2-pool-datai off fn2-pool))))
  :hints (("Goal" :in-theory (e/d (fn2-b3-read fn2-pool-read fn2-b3-windowp)
                                  (fn2-pool-base fn2-pool-rows fn2-pool-fill fn2-pool-readable-code
                                   fn2-pool-workspace-code fn2-pool-data-length))))))

(local (defun fn2-b3-covers (xs off fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (if (atom xs) t
    (and (equal (fn2-pool-datai off fn2-pool) (car xs))
         (fn2-b3-covers (cdr xs) (1+ off) fn2-pool)))))

(local (defthm fn2-b3-nth-of-drop
  (implies (and (natp i) (natp off) (< (+ off i) (len xs)))
           (equal (nth i (fn-b3-nthcdrx off xs)) (nth (+ off i) xs)))
  :hints (("Goal" :induct (fn-b3-nthcdrx off xs) :in-theory (enable fn-b3-nthcdrx)))))

(local (defthm fn2-b3-car-of-drop
  (implies (and (natp off) (< off (len xs)))
           (equal (car (fn-b3-nthcdrx off xs)) (nth off xs)))
  :hints (("Goal" :induct (fn-b3-nthcdrx off xs) :in-theory (enable fn-b3-nthcdrx)))))
(local (defthm fn2-b3-cdr-of-drop
  (implies (and (natp off) (< off (len xs)))
           (equal (cdr (fn-b3-nthcdrx off xs)) (fn-b3-nthcdrx (1+ off) xs)))
  :hints (("Goal" :induct (fn-b3-nthcdrx off xs) :in-theory (enable fn-b3-nthcdrx)))))

(local (defun fn2-b3-to-end (off xs)
  (declare (xargs :measure (nfix (- (len xs) (nfix off)))))
  (if (or (not (natp off)) (<= (len xs) off)) off (fn2-b3-to-end (1+ off) xs))))

(local (defthm fn2-b3-consp-drop
  (implies (natp off) (equal (consp (fn-b3-nthcdrx off xs)) (< off (len xs))))
  :hints (("Goal" :induct (fn-b3-nthcdrx off xs) :in-theory (enable fn-b3-nthcdrx)))))

(local (defthm fn2-b3-loaded-covers-tail
  (implies (and (fn2-b3-windowp 0 fn2-pool) (natp off)
                (fn-b3-octet-listp xs) (<= (len xs) 4096))
           (fn2-b3-covers (fn-b3-nthcdrx off xs) off (fn2-b3-spec-load xs 0 fn2-pool)))
  :hints (("Goal" :induct (fn2-b3-to-end off xs)
                  :expand ((:free (pool) (fn2-b3-covers (fn-b3-nthcdrx off xs) off pool)))
                  :in-theory (disable fn2-b3-spec-load)))))

(local (defthm fn2-b3-loaded-covers
  (implies (and (fn2-b3-windowp 0 fn2-pool)
                (fn-b3-octet-listp xs) (<= (len xs) 4096))
           (fn2-b3-covers xs 0 (fn2-b3-spec-load xs 0 fn2-pool)))
  :hints (("Goal" :use ((:instance fn2-b3-loaded-covers-tail (off 0)))
                  :expand ((fn-b3-nthcdrx 0 xs))
                  :in-theory (disable fn2-b3-loaded-covers-tail fn2-b3-spec-load)))))

(local (defun fn2-b3-drop-induct (n off xs)
  (if (or (zp n) (atom xs)) off
    (fn2-b3-drop-induct (1- n) (1+ off) (cdr xs)))))
(local (defthm fn2-b3-covers-drop
  (implies (and (fn2-b3-covers xs off fn2-pool) (natp off) (natp n) (<= n (len xs)))
           (fn2-b3-covers (fn-b3-nthcdrx n xs) (+ n off) fn2-pool))
  :hints (("Goal" :induct (fn2-b3-drop-induct n off xs)
                  :in-theory (enable fn-b3-nthcdrx)))))
(local (defthm fn2-b3-covered-byte
  (implies (and (fn2-b3-covers xs off fn2-pool) (natp i) (natp off) (< i (len xs)))
           (equal (fn2-pool-datai (+ i off) fn2-pool) (fn-b3-nthx i xs)))
  :hints (("Goal" :induct (fn2-b3-drop-induct i off xs)))))

(local (defthm fn2-b3-nthx-octet
  (implies (fn-b3-octet-listp xs) (unsigned-byte-p 8 (fn-b3-nthx n xs)))))

(local (defthm fn2-b3-word-of-byte
  (implies (unsigned-byte-p 8 b)
           (and (equal (fn-b3-word b) b) (equal (fn-b3-octet b) b)))
  :hints (("Goal" :in-theory (enable fn-b3-word fn-b3-octet)))))

(local (defun fn2-b3-msg-word (i xs)
  (let ((b (* 4 i)))
    (fn-b3-le-word (fn-b3-nthx b xs) (fn-b3-nthx (+ 1 b) xs)
                   (fn-b3-nthx (+ 2 b) xs) (fn-b3-nthx (+ 3 b) xs)))))

(local (defthm fn2-b3-pool-word-at
  (implies (and (fn2-b3-covers xs off fn2-pool) (fn-b3-octet-listp xs)
                (natp off) (natp i) (<= (+ 4 (* 4 i)) (len xs)))
    (equal (fn-b3-pool-word (+ off (* 4 i)) fn2-pool) (fn2-b3-msg-word i xs)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-b3-covered-byte (i (* 4 i)))
                         (:instance fn2-b3-covered-byte (i (+ 1 (* 4 i))))
                         (:instance fn2-b3-covered-byte (i (+ 2 (* 4 i))))
                         (:instance fn2-b3-covered-byte (i (+ 3 (* 4 i)))))
                  :in-theory (e/d (fn-b3-pool-word fn-b3-le-word)
                                  (fn-b3-nthx fn2-b3-covers fn2-b3-covered-byte))))))

(local (defthm fn2-b3-nthx-drop
  (implies (and (natp i) (natp n))
           (equal (fn-b3-nthx i (fn-b3-nthcdrx n xs)) (fn-b3-nthx (+ n i) xs)))
  :hints (("Goal" :induct (fn-b3-nthcdrx n xs) :in-theory (enable fn-b3-nthcdrx)))))

(local (defthm fn2-b3-msg-word-next
  (implies (posp i)
           (equal (fn2-b3-msg-word (1- i) (fn-b3-nthcdrx 4 xs)) (fn2-b3-msg-word i xs)))))

(local (defun fn2-b3-words-induct (k i xs)
  (if (or (zp k) (zp i)) xs
    (fn2-b3-words-induct (1- k) (1- i) (fn-b3-nthcdrx 4 xs)))))

(local (defthm fn2-b3-word-at
  (implies (and (natp k) (natp i) (< i k))
           (equal (fn-b3-nthx i (fn-b3-words k xs)) (fn2-b3-msg-word i xs)))
  :hints (("Goal" :induct (fn2-b3-words-induct k i xs)
                  :expand ((fn-b3-words k xs))
                  :in-theory (enable fn-b3-nthx)))))

(local (in-theory (disable fn2-b3-msg-word fn2-b3-covers fn-b3-nthx)))

(local (defun fn2-b3-pool-run (off ctr n j cv fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (fn-b3-pool-blocks off ctr n j
    (fn-b3-nthx 0 cv) (fn-b3-nthx 1 cv) (fn-b3-nthx 2 cv) (fn-b3-nthx 3 cv)
    (fn-b3-nthx 4 cv) (fn-b3-nthx 5 cv) (fn-b3-nthx 6 cv) (fn-b3-nthx 7 cv) fn2-pool)))

(local (defthm fn2-b3-nthx-cons
  (equal (fn-b3-nthx n (cons a b)) (if (zp n) a (fn-b3-nthx (1- n) b)))
  :hints (("Goal" :expand ((fn-b3-nthx n (cons a b)))))))

(local (defun fn2-b3-pool-word-instances (count)
  (if (zp count) nil
    (cons `(:instance fn2-b3-pool-word-at (i ,(1- count)))
          (fn2-b3-pool-word-instances (1- count))))))

(local (defthm fn2-b3-pool-run-step
  (implies (and (posp n) (natp off) (<= 64 (len xs))
                (fn2-b3-covers xs off fn2-pool) (fn-b3-octet-listp xs))
    (equal (fn2-b3-pool-run off ctr n j cv fn2-pool)
           (fn2-b3-pool-run (+ 64 off) ctr (1- n) (+ 1 j)
             (fn-b3-compress cv (fn-b3-words 16 xs) ctr 64
               (logior (if (equal j 0) 1 0) (if (equal j 15) 2 0)))
             fn2-pool)))
  :rule-classes nil
  :hints ((and t
               `(:use ,(fn2-b3-pool-word-instances 16)
                  :expand ((:free (a b c d e f g h)
                                  (fn-b3-pool-blocks off ctr n j a b c d e f g h fn2-pool)))
                  :in-theory (e/d (fn2-b3-pool-run fn-b3-compress)
                                  (fn-b3-words mv-nth)))))))

(local (defthm fn2-b3-pool-run-zero
  (equal (fn2-b3-pool-run off ctr 0 j cv fn2-pool) (fn-b3-cv8 cv))
  :hints (("Goal" :in-theory (enable fn2-b3-pool-run fn-b3-pool-blocks)))))

(local (defthm fn2-b3-octets-drop
  (implies (fn-b3-octet-listp xs) (fn-b3-octet-listp (fn-b3-nthcdrx n xs)))
  :hints (("Goal" :induct (fn-b3-nthcdrx n xs) :in-theory (enable fn-b3-nthcdrx)))))

(local (defthm fn2-b3-cv8-compress
  (equal (fn-b3-cv8 (fn-b3-compress cv words ctr n flags)) (fn-b3-compress cv words ctr n flags))
  :hints (("Goal" :in-theory (enable fn-b3-cv8 fn-b3-compress)))))

(local (defthm fn2-b3-compress-cv8
  (equal (fn-b3-compress (fn-b3-cv8 cv) words ctr n flags) (fn-b3-compress cv words ctr n flags))
  :hints (("Goal" :in-theory (enable fn-b3-cv8 fn-b3-compress)))))

(local (in-theory (disable fn-b3-cv8 fn2-b3-pool-run fn-b3-words)))

(local (defun fn2-b3-chunk-induct (j xs off ctr cv)
  (declare (xargs :measure (nfix (- 15 (nfix j)))))
  (if (or (not (natp j)) (<= 15 j)) (list xs off ctr cv)
    (fn2-b3-chunk-induct (1+ j) (fn-b3-nthcdrx 64 xs) (+ 64 off) ctr
                         (fn-b3-compress cv (fn-b3-words 16 xs) ctr 64 (if (equal j 0) 1 0))))))

(local (defthm fn2-b3-chunk-more
  (implies (< 64 (len xs))
    (equal (fn-b3-chunk cv xs ctr 0 first)
           (fn-b3-chunk (fn-b3-compress cv (fn-b3-words 16 xs) ctr 64 (if first 1 0))
                        (fn-b3-nthcdrx 64 xs) ctr 0 nil)))
  :hints (("Goal" :expand ((fn-b3-chunk cv xs ctr 0 first))))))

(local (defthm fn2-b3-chunk-last
  (implies (<= (len xs) 64)
    (equal (fn-b3-chunk cv xs ctr 0 first)
           (fn-b3-output (fn-b3-cv8 cv) (fn-b3-words 16 xs) ctr (len xs) (if first 3 2))))
  :hints (("Goal" :expand ((fn-b3-chunk cv xs ctr 0 first))))))

(local (defthm fn2-b3-full-pool-chunk
  (implies (and (natp j) (<= j 15) (natp off)
                (fn2-b3-covers xs off fn2-pool) (fn-b3-octet-listp xs)
                (equal (len xs) (* 64 (- 16 j))))
    (let ((out (fn-b3-chunk cv xs ctr 0 (equal j 0))))
      (and (equal (fn2-b3-pool-run off ctr (- 16 j) j cv fn2-pool) (fn-b3-output-cv out))
           (equal (fn-b3-output (fn2-b3-pool-run off ctr (- 15 j) j cv fn2-pool)
                                (fn-b3-words 16 (fn-b3-nthcdrx (* 64 (- 15 j)) xs)) ctr 64 2)
                  out))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-b3-chunk-induct j xs off ctr cv)
                   :do-not '(generalize eliminate-destructors))
          ("Subgoal *1/2" :use ((:instance fn2-b3-pool-run-step (n (- 15 j)))
                                (:instance fn2-b3-pool-run-step (n (- 16 j)))
                                (:instance fn2-b3-covers-drop (n 64))))
          ("Subgoal *1/1" :use ((:instance fn2-b3-pool-run-step (n 1) (j 15)))
                           :expand ((fn-b3-nthcdrx 0 xs))
                           :in-theory (enable fn-b3-output-cv fn-b3-output)))))
(local (defthm fn2-b3-pool-tree-one
  (implies (and (natp off) (fn2-b3-covers xs off fn2-pool) (fn-b3-octet-listp xs)
                (equal (len xs) 1024))
    (equal (fn-b3-pool-tree off 1 ctr fn2-pool)
           (fn-b3-output-cv (fn-b3-chunk *fn-b3-iv* xs ctr 0 t))))
  :hints (("Goal" :use ((:instance fn2-b3-full-pool-chunk (j 0) (cv *fn-b3-iv*)))
                  :expand ((fn-b3-pool-tree off 1 ctr fn2-pool))
                  :in-theory (enable fn2-b3-pool-run)))))

(local (defthm fn2-b3-mv-nth-is-nth
  (implies (natp n) (equal (mv-nth n xs) (nth n xs)))))

(local (defthm fn2-b3-subtree-chunk-effect
  (implies (and (natp off) (fn2-b3-covers xs off fn2-pool) (fn-b3-octet-listp xs)
                (equal (len xs) 1024))
    (equal (fn2-b3-subtree-cv-into dst off 1024 ctr fn2-digests fn2-pool)
           (fn2-digest-load dst (fn-b3-output-cv (fn-b3-chunk *fn-b3-iv* xs ctr 0 t)) fn2-digests)))
  :hints (("Goal" :use ((:instance fn2-b3-pool-tree-one)
                        (:instance fn2-b3-subtree-cv-into-by-definition (len 1024) (counter ctr)))
                  :in-theory (disable fn2-b3-subtree-cv-into-by-definition
                                      fn-b3-compress fn2-b3-pool-tree-one fn2-b3-chunk-more
                                      fn2-b3-chunk-last mv-nth nth)))))

(local (in-theory (disable fn2-b3-mv-nth-is-nth fn2-b3-chunk-more fn2-b3-chunk-last)))
; Packed words may be stale beyond the pending block. Within the last
; occupied word, the high bytes are zero, as required by the append operation.
(local (defun fn2-b3-packedp (buf base fn2-b3)
  (declare (xargs :stobjs fn2-b3 :verify-guards nil :measure (len buf)))
  (if (atom buf) t
    (and (equal (fn2-b3-word 0 base fn2-b3) (fn2-b3-msg-word 0 buf))
         (fn2-b3-packedp (fn-b3-nthcdrx 4 buf) (+ 1 base) fn2-b3)))))

(local (defthm fn2-b3-word-store
  (implies (and (natp i) (natp j))
    (equal (fn2-b3-word 0 i (fn2-b3-store 0 j v fn2-b3))
           (if (equal i j) (fn-b3-word v) (fn2-b3-word 0 i fn2-b3))))
  :hints (("Goal" :cases ((equal i j)) :in-theory (enable fn2-b3-word fn2-b3-store)))))

(local (defthm fn2-b3-word-set-pos
  (equal (fn2-b3-word 0 i (fn2-b3-set-pos 0 pos fn2-b3)) (fn2-b3-word 0 i fn2-b3))
  :hints (("Goal" :in-theory (enable fn2-b3-word)))))

(local (defthm fn2-b3-packed-set-pos
  (equal (fn2-b3-packedp buf base (fn2-b3-set-pos 0 pos fn2-b3)) (fn2-b3-packedp buf base fn2-b3))
  :hints (("Goal" :induct (fn2-b3-packedp buf base fn2-b3)))))

(local (defthm fn2-b3-octet-append-last
  (implies (and (fn-b3-octet-listp buf) (unsigned-byte-p 8 b))
           (fn-b3-octet-listp (append buf (list b))))))

(local (defthm fn2-b3-drop-append
  (implies (and (natp n) (<= n (len xs)))
           (equal (fn-b3-nthcdrx n (append xs ys)) (append (fn-b3-nthcdrx n xs) ys)))
  :hints (("Goal" :induct (fn-b3-nthcdrx n xs) :in-theory (fn2-b3-list-theory fn-b3-nthcdrx)))))

(local (defthm fn2-b3-nthx-append-before
  (implies (and (natp i) (< i (len xs)))
           (equal (fn-b3-nthx i (append xs ys)) (fn-b3-nthx i xs)))
  :hints (("Goal" :induct (fn-b3-nthx i xs) :in-theory (fn2-b3-list-theory fn-b3-nthx)))))

(local (defthm fn2-b3-full-first-word
  (implies (<= 4 (len buf))
           (equal (fn2-b3-msg-word 0 (append buf xs)) (fn2-b3-msg-word 0 buf)))
  :hints (("Goal" :in-theory (enable fn2-b3-msg-word)))))

(local (defthm fn2-b3-word-idempotent
  (equal (fn-b3-word (fn-b3-word x)) (fn-b3-word x))
  :hints (("Goal" :in-theory (enable fn-b3-word)))))

(local (defthm fn2-b3-append-literal-0
  (implies (and  (unsigned-byte-p 8 b))
           (equal (fn-b3-word (+ (fn2-b3-msg-word 0 nil) (ash b 0)))
                  (fn2-b3-msg-word 0 (append nil (list b)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-b3-msg-word fn-b3-nthx fn-b3-le-word fn-b3-word fn-b3-octet)))))
(local (defthm fn2-b3-append-literal-1
  (implies (and (unsigned-byte-p 8 x0) (unsigned-byte-p 8 b))
           (equal (fn-b3-word (+ (fn2-b3-msg-word 0 (list x0)) (ash b 8)))
                  (fn2-b3-msg-word 0 (append (list x0) (list b)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-b3-msg-word fn-b3-nthx fn-b3-le-word fn-b3-word fn-b3-octet)))))
(local (defthm fn2-b3-append-literal-2
  (implies (and (unsigned-byte-p 8 x0) (unsigned-byte-p 8 x1) (unsigned-byte-p 8 b))
           (equal (fn-b3-word (+ (fn2-b3-msg-word 0 (list x0 x1)) (ash b 16)))
                  (fn2-b3-msg-word 0 (append (list x0 x1) (list b)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-b3-msg-word fn-b3-nthx fn-b3-le-word fn-b3-word fn-b3-octet)))))
(local (defthm fn2-b3-append-literal-3
  (implies (and (unsigned-byte-p 8 x0) (unsigned-byte-p 8 x1) (unsigned-byte-p 8 x2) (unsigned-byte-p 8 b))
           (equal (fn-b3-word (+ (fn2-b3-msg-word 0 (list x0 x1 x2)) (ash b 24)))
                  (fn2-b3-msg-word 0 (append (list x0 x1 x2) (list b)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-b3-msg-word fn-b3-nthx fn-b3-le-word fn-b3-word fn-b3-octet)))))
(local (defthm fn2-b3-short-shapes
  (implies (and (fn-b3-octet-listp buf) (< (len buf) 4))
    (or (equal buf nil)
        (and (equal buf (list (car buf))) (unsigned-byte-p 8 (car buf)))
        (and (equal buf (list (car buf) (cadr buf))) (unsigned-byte-p 8 (car buf)) (unsigned-byte-p 8 (cadr buf)))
        (and (equal buf (list (car buf) (cadr buf) (caddr buf)))
             (unsigned-byte-p 8 (car buf)) (unsigned-byte-p 8 (cadr buf)) (unsigned-byte-p 8 (caddr buf)))))
  :rule-classes nil :hints (("Goal" :induct (len buf)))))
(local (defthm fn2-b3-append-short-word
  (implies (and (fn-b3-octet-listp buf) (< (len buf) 4) (unsigned-byte-p 8 b))
    (equal (fn-b3-word (+ (fn2-b3-msg-word 0 buf) (ash b (* 8 (len buf)))))
           (fn2-b3-msg-word 0 (append buf (list b)))))
  :hints (("Goal" :use (fn2-b3-short-shapes
    (:instance fn2-b3-append-literal-0 )
    (:instance fn2-b3-append-literal-1 (x0 (car buf)))
    (:instance fn2-b3-append-literal-2 (x0 (car buf)) (x1 (cadr buf)))
    (:instance fn2-b3-append-literal-3 (x0 (car buf)) (x1 (cadr buf)) (x2 (caddr buf)))
    ) :in-theory (theory 'minimal-theory))
    (and stable-under-simplificationp '(:in-theory (enable len))))))
(local (defun fn2-b3-append-word (buf base b fn2-b3)
  (declare (xargs :stobjs fn2-b3 :verify-guards nil))
  (let* ((idx (+ base (floor (len buf) 4))) (shift (* 8 (mod (len buf) 4))))
    (fn-b3-word (+ (if (equal shift 0) 0 (fn2-b3-word 0 idx fn2-b3)) (ash b shift))))))

(local (defthm fn2-b3-append-word-drop
  (implies (and (natp base) (<= 4 (len buf)))
    (equal (fn2-b3-append-word (fn-b3-nthcdrx 4 buf) (+ 1 base) b fn2-b3)
           (fn2-b3-append-word buf base b fn2-b3)))))

(local (defthm fn2-b3-word-of-msg
 (equal (fn-b3-word (fn2-b3-msg-word i xs)) (fn2-b3-msg-word i xs))
 :hints (("Goal" :use ((:instance fn-b3-le-word-type (b0 (fn-b3-nthx (* 4 i) xs)) (b1 (fn-b3-nthx (+ 1 (* 4 i)) xs)) (b2 (fn-b3-nthx (+ 2 (* 4 i)) xs)) (b3 (fn-b3-nthx (+ 3 (* 4 i)) xs))))
 :in-theory (e/d (fn2-b3-msg-word fn-b3-word) (fn-b3-le-word-type))))))
(local (defthm fn2-b3-zero-length-atom
  (implies (consp buf) (< 0 (len buf))) :rule-classes :linear))
(local (defthm fn2-b3-drop-end
  (implies (and (true-listp xs) (<= (len xs) (nfix n)))
           (equal (fn-b3-nthcdrx n xs) nil))
  :hints (("Goal" :induct (fn-b3-nthcdrx n xs) :in-theory (fn2-b3-list-theory fn-b3-nthcdrx)))))
(local (defthm fn2-b3-msg-single
  (implies (unsigned-byte-p 8 b) (equal (fn2-b3-msg-word 0 (list b)) b))
  :hints (("Goal" :in-theory (enable fn2-b3-msg-word fn-b3-nthx fn-b3-le-word fn-b3-octet)))))
(local (defthm fn2-b3-packed-append
  (implies (and (fn2-b3-packedp buf base fn2-b3) (natp base)
                (fn-b3-octet-listp buf) (unsigned-byte-p 8 b))
    (fn2-b3-packedp (append buf (list b)) base
      (fn2-b3-store 0 (+ base (floor (len buf) 4)) (fn2-b3-append-word buf base b fn2-b3) fn2-b3)))
  :hints (("Goal" :induct (fn2-b3-packedp buf base fn2-b3)
                  :expand ((:free (p) (fn2-b3-packedp (append buf (list b)) base p)))
                  :in-theory (disable fn2-b3-append-word ash))
          ("Subgoal *1/2" :cases ((<= 4 (len buf))))
          ("Subgoal *1/2.2" :in-theory (e/d (fn2-b3-append-word) (ash)))
          ("Subgoal *1/1" :in-theory (enable fn2-b3-append-word)))))
(local (defun fn2-b3-packed-index (i xs base fn2-b3)
  (declare (xargs :stobjs fn2-b3 :verify-guards nil))
  (if (zp i) (cons xs (fn2-b3-word 0 base fn2-b3))
    (fn2-b3-packed-index (1- i) (fn-b3-nthcdrx 4 xs) (1+ base) fn2-b3))))


(local (defthm fn2-b3-nthx-padding
 (implies (and (natp i) (<= (len xs) i)) (equal (fn-b3-nthx i xs) 0))
 :hints (("Goal" :induct (fn-b3-nthx i xs) :in-theory (enable fn-b3-nthx)))))
(local (defthm fn2-b3-msg-padding
 (implies (and (natp i) (<= (len xs) (* 4 i))) (equal (fn2-b3-msg-word i xs) 0))
 :hints (("Goal" :in-theory (enable fn2-b3-msg-word)))))
(local (defthm fn2-b3-short-msg-bound
 (implies (and (fn-b3-octet-listp xs) (< (len xs) 4))
   (and (natp (fn2-b3-msg-word 0 xs))
        (< (fn2-b3-msg-word 0 xs) (expt 256 (len xs)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-b3-short-shapes (buf xs)))
          :in-theory (disable fn2-b3-msg-word fn-b3-octet-listp len))
         (and stable-under-simplificationp
              '(:in-theory (enable fn2-b3-msg-word fn-b3-nthx fn-b3-le-word fn-b3-octet len))))))
(local (defthm fn2-b3-partial-word-mask
  (implies (and (fn-b3-octet-listp xs) (< (len xs) 4))
    (equal (mod (fn2-b3-msg-word 0 xs) (expt 256 (len xs))) (fn2-b3-msg-word 0 xs)))
  :hints (("Goal" :use fn2-b3-short-msg-bound))))
(local (defun fn2-b3-mask (w left)
  (cond ((<= left 0) 0) ((<= 4 left) w) (t (mod w (expt 256 left))))))
(local (defthm fn2-b3-packed-mask-at
  (implies (and (fn2-b3-packedp xs base fn2-b3) (fn-b3-octet-listp xs) (natp base) (natp i))
    (equal (fn2-b3-mask (fn2-b3-word 0 (+ base i) fn2-b3) (- (len xs) (* 4 i)))
           (fn2-b3-msg-word i xs)))
  :hints (("Goal" :induct (fn2-b3-packed-index i xs base fn2-b3)
                  :expand ((fn2-b3-packedp xs base fn2-b3))
                  :in-theory (disable fn2-b3-mask))
          ("Subgoal *1/2" :cases ((< (len xs) 4)) :in-theory (enable fn2-b3-mask))
          ("Subgoal *1/1" :use fn2-b3-short-msg-bound :in-theory (enable fn2-b3-mask)))))

(local (defthm fn2-b3-packed-block-word
 (implies (and (fn2-b3-packedp xs 0 fn2-b3) (fn-b3-octet-listp xs) (natp i)
               (equal (fn2-b3-pos 0 fn2-b3) (len xs)))
  (equal (fn2-b3-block-word 0 i fn2-b3) (fn2-b3-msg-word i xs)))
 :hints (("Goal" :use ((:instance fn2-b3-packed-mask-at (base 0)))
          :in-theory (e/d (fn2-b3-block-word) (fn2-b3-packed-mask-at fn2-b3-pos))))))
(local (defun fn2-b3-word-sequence (k i xs)
 (if (zp k) nil (cons (fn2-b3-msg-word i xs) (fn2-b3-word-sequence (1- k) (1+ i) xs)))))
(local (defthm fn2-b3-word-sequence-correct
 (implies (and (natp i) (natp k))
  (equal (fn2-b3-word-sequence k i xs) (fn-b3-words k (fn-b3-nthcdrx (* 4 i) xs))))
 :hints (("Goal" :induct (fn2-b3-word-sequence k i xs)
          :expand ((:free (ys) (fn-b3-words k ys)) (:free (ys) (fn-b3-words 0 ys)))
          :in-theory (fn2-b3-list-theory fn2-b3-word-sequence fn2-b3-msg-word fn2-b3-nthx-drop fn2-b3-drop-twice)))))
(local (defthm fn2-b3-packed-words
 (implies (and (fn2-b3-packedp xs 0 fn2-b3) (fn-b3-octet-listp xs)
               (equal (fn2-b3-pos 0 fn2-b3) (len xs)))
   (equal (fn2-b3-buffer-words fn2-b3) (fn-b3-words 16 xs)))
 :hints (("Goal" :use ((:instance fn2-b3-word-sequence-correct (k 16) (i 0)))
          :expand ((fn-b3-nthcdrx 0 xs))
          :in-theory (disable fn2-b3-word-sequence-correct fn2-b3-pos)))))
(local (defthm fn2-b3-drop-zero (equal (fn-b3-nthcdrx 0 xs) xs) :hints (("Goal" :expand ((fn-b3-nthcdrx 0 xs))))))
(local (in-theory (disable fn2-b3-block-input-facts)))
(local (defthm fn2-b3-drop-past-append
 (implies (and (natp n) (<= (len xs) n))
  (equal (fn-b3-nthcdrx n (append xs ys)) (fn-b3-nthcdrx (- n (len xs)) ys)))
 :hints (("Goal" :induct (fn-b3-nthcdrx n xs) :in-theory (fn2-b3-list-theory fn-b3-nthcdrx)))))
(local (defthm fn2-b3-first-past-append
 (implies (and (natp n) (<= (len xs) n))
  (equal (fn-b3-firstn n (append xs ys)) (append xs (fn-b3-firstn (- n (len xs)) ys))))
 :hints (("Goal" :induct (fn-b3-firstn n xs) :in-theory (fn2-b3-list-theory fn-b3-firstn)))))
(local (defthm fn2-b3-word-prefix-same
 (implies (and (natp i) (<= (+ 4 (* 4 i)) (len xs)))
  (equal (fn2-b3-msg-word i (append xs ys)) (fn2-b3-msg-word i xs)))
 :hints (("Goal" :in-theory (enable fn2-b3-msg-word)))))
(local (defthm fn2-b3-words-prefix-same
 (implies (and (natp k) (<= (* 4 k) (len xs)))
  (equal (fn-b3-words k (append xs ys)) (fn-b3-words k xs)))
 :hints (("Goal" :induct (fn-b3-words k xs)
          :in-theory (enable fn-b3-words)))))
(local (defun fn2-b3-resume (xs cv j ctr org stack root)
 (let* ((room (* 64 (- 16 j)))
        (out (fn-b3-chunk cv (fn-b3-firstn room xs) ctr 0 (equal j 0))))
   (if (<= (len xs) room) (fn2-b3-seal stack out root)
     (fn2-b3-scan 1 (fn-b3-nthcdrx room xs) (+ 2 (- ctr org)) (1+ ctr)
      (fn2-b3-push-list stack (fn-b3-output-cv out) (+ 1 (- ctr org)) *fn-b3-iv* 0) root)))))
(local (defthm fn2-b3-resume-start
 (implies (and (natp ctr) (natp org) (<= org ctr))
  (equal (fn2-b3-resume xs *fn-b3-iv* 0 ctr org stack root)
         (fn2-b3-scan 1 xs (+ 1 (- ctr org)) ctr stack root)))
 :hints (("Goal" :expand ((fn2-b3-scan 1 xs (+ 1 (- ctr org)) ctr stack root)
                          (fn-b3-node *fn-b3-iv* (fn-b3-firstn 1024 xs) ctr 0))
          :in-theory (enable fn2-b3-node-at)))))
(local (defthm fn2-b3-resume-full-block
 (implies (and (natp j) (< j 15) (true-listp buf) (equal (len buf) 64) (consp rest))
  (equal (fn2-b3-resume (append buf rest) cv j ctr org stack root)
         (fn2-b3-resume rest (fn-b3-compress cv (fn-b3-words 16 buf) ctr 64 (if (equal j 0) 1 0))
                        (1+ j) ctr org stack root)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory (e/d (fn2-b3-chunk-more) (fn2-b3-resume-start))))))
(local (defthm fn2-b3-resume-full-chunk
 (implies (and (true-listp buf) (equal (len buf) 64) (consp rest) (natp ctr) (natp org) (<= org ctr))
  (equal (fn2-b3-resume (append buf rest) cv 15 ctr org stack root)
         (fn2-b3-resume rest *fn-b3-iv* 0 (1+ ctr) org
          (fn2-b3-push-list stack (fn-b3-output-cv (fn-b3-chunk cv buf ctr 0 nil))
                    (+ 1 (- ctr org)) *fn-b3-iv* 0) root)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-b3-resume-start (xs rest) (ctr (1+ ctr))
   (stack (fn2-b3-push-list stack (fn-b3-output-cv (fn-b3-chunk cv buf ctr 0 nil))
                    (+ 1 (- ctr org)) *fn-b3-iv* 0))))
          :expand ((fn-b3-nthcdrx 0 rest) (fn-b3-firstn 0 rest))
          :in-theory (disable fn2-b3-resume-start)))))
(local (in-theory (disable fn2-b3-resume fn2-b3-resume-start fn2-b3-packedp fn2-b3-buffer-words
 fn2-b3-pos fn2-b3-counter fn2-b3-blocks fn2-b3-origin fn2-b3-depth fn2-b3-flags fn2-b3-verify-phase
 fn2-b3-append-word)))
(local (defun fn2-b3-suffix (n past) (fn-b3-nthcdrx (- (len past) n) past)))
(local (defthm fn2-b3-suffix-zero (implies (true-listp past) (equal (fn2-b3-suffix 0 past) nil))))
(local (defthm fn2-b3-suffix-append
 (implies (and (natp n) (<= n (len past)) (true-listp past))
  (equal (fn2-b3-suffix (+ n (len more)) (append past more))
         (append (fn2-b3-suffix n past) more)))
 :hints (("Goal" :in-theory (disable fn2-b3-drop-past-append)))))
(local (defthm fn2-b3-suffix-after-span
 (implies (and (natp n) (<= n (len more)))
  (equal (fn2-b3-suffix n (append past more)) (fn2-b3-suffix n more)))))
(local (defun fn2-b3-match (buf xs root answer fn2-digests fn2-b3)
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
                      (fn2-b3-frontier-list depth fn2-digests) root))))))
(local (defun fn2-b3-good (past xs root answer fn2-digests fn2-b3)
 (declare (xargs :stobjs (fn2-digests fn2-b3) :verify-guards nil))
 (and (true-listp past) (<= (fn2-b3-pos 0 fn2-b3) (len past))
      (fn2-b3-match (fn2-b3-suffix (fn2-b3-pos 0 fn2-b3) past) xs root answer fn2-digests fn2-b3))))
(local (defthm fn2-b3-copy-cv-preserves-frontier
 (equal (fn2-b3-frontier-list d (fn2-digest-copy 0 src fn2-digests)) (fn2-b3-frontier-list d fn2-digests))
 :hints (("Goal" :induct (fn2-b3-frontier-list d fn2-digests) :in-theory (enable fn2-b3-frontier-list)))))
(local (defthm fn2-b3-half-below
 (implies (and (natp n) (posp p) (< n (1- (* 2 p))))
  (and (< (floor n 2) p)
       (or (< (floor n 2) (1- p)) (equal (mod n 2) 0))))
 :rule-classes nil :hints (("Goal" :in-theory (enable mod)))))
(local (defthm fn2-b3-bits-strict
 (implies (and (natp k) (natp n) (< n (1- (expt 2 k)))) (< (fn2-b3-bits n) k))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-b3-bit-induct n k) :do-not '(generalize eliminate-destructors)
                 )
         ("Subgoal *1/2" :use (fn2-b3-double-prev-expt
                 (:instance fn2-b3-half-below (p (expt 2 (1- k))))
                 (:instance fn2-b3-bits-bound (n (floor n 2)) (k (1- k))))
          :expand ((fn2-b3-bits n)) :do-not-induct t))))
(local (defconst *fn2-b3-proof-columns*
 '(fn2-b3-pos fn2-b3-blocks fn2-b3-counter fn2-b3-origin fn2-b3-depth fn2-b3-flags fn2-b3-verify-phase)))
(local (defun fn2-b3-column-equations (columns changed value next)
 (if (endp columns) nil
  (cons `(equal (,(car columns) 0 ,next)
                ,(if (eq (car columns) changed) value `(,(car columns) 0 fn2-b3)))
        (fn2-b3-column-equations (cdr columns) changed value next)))))
(local (defmacro fn2-b3-prove-column-reads (name op args changed value)
 `(defthm ,name
   (and ,@(fn2-b3-column-equations *fn2-b3-proof-columns* changed value (cons op args)))
   :hints (("Goal" :in-theory (enable ,op update-fn2-b3-pos$ai update-fn2-b3-blocks$ai update-fn2-b3-counter$ai update-fn2-b3-depth$ai update-fn2-b3-origin$ai ,@*fn2-b3-proof-columns*))))))
(local (fn2-b3-prove-column-reads fn2-b3-store-columns fn2-b3-store (0 i w fn2-b3) nil nil))
(local (fn2-b3-prove-column-reads fn2-b3-pos-columns fn2-b3-set-pos (0 v fn2-b3) fn2-b3-pos v))
(local (fn2-b3-prove-column-reads fn2-b3-blocks-columns fn2-b3-set-blocks (0 v fn2-b3) fn2-b3-blocks v))
(local (fn2-b3-prove-column-reads fn2-b3-counter-columns fn2-b3-set-counter (0 v fn2-b3) fn2-b3-counter v))
(local (fn2-b3-prove-column-reads fn2-b3-depth-columns fn2-b3-set-depth (0 v fn2-b3) fn2-b3-depth v))
(local (fn2-b3-prove-column-reads fn2-b3-origin-columns fn2-b3-set-origin (0 v fn2-b3) fn2-b3-origin v))
(local (in-theory (disable fn2-b3-set-pos fn2-b3-set-blocks fn2-b3-set-counter fn2-b3-set-depth fn2-b3-set-origin)))
(local (defthm fn2-b3-push-other-columns
 (let ((next (mv-nth 1 (fn2-b3-push 0 n d src fn2-digests fn2-b3))))
   (and (equal (fn2-b3-origin 0 next) (fn2-b3-origin 0 fn2-b3))
        (equal (fn2-b3-verify-phase 0 next) (fn2-b3-verify-phase 0 fn2-b3))))
 :hints (("Goal" :induct (fn2-b3-push 0 n d src fn2-digests fn2-b3)
          :expand ((:free (n) (fn2-b3-push 0 n d src fn2-digests fn2-b3)))
          :in-theory (e/d ((:induction fn2-b3-push)) (floor mod))))))
(local (defthm fn2-b3-buffer-cv
 (implies (and (equal (fn-b3-cv8 (fn2-digest-list 0 fn2-digests)) (fn2-digest-list 0 fn2-digests))
               (equal (fn2-b3-buffer-words fn2-b3) (fn-b3-words 16 buf))
               (equal (fn2-b3-pos 0 fn2-b3) (len buf)) (<= (len buf) 64))
  (equal (fn2-b3-buffer-output t fn2-digests fn2-b3)
         (fn-b3-chunk (fn2-digest-list 0 fn2-digests) buf (fn2-b3-counter 0 fn2-b3) 0
                      (equal (fn2-b3-blocks 0 fn2-b3) 0))))
 :hints (("Goal" :in-theory (enable fn2-b3-buffer-output fn2-b3-chunk-last)))))
(local (defthm fn2-b3-buffer-middle
 (implies (and (equal (fn2-b3-buffer-words fn2-b3) (fn-b3-words 16 buf)) (equal (fn2-b3-pos 0 fn2-b3) 64))
  (equal (fn2-b3-output-words (fn2-b3-buffer-output nil fn2-digests fn2-b3) nil)
         (fn-b3-compress (fn2-digest-list 0 fn2-digests) (fn-b3-words 16 buf) (fn2-b3-counter 0 fn2-b3)
                         64 (if (equal (fn2-b3-blocks 0 fn2-b3) 0) 1 0))))
 :hints (("Goal" :in-theory (enable fn2-b3-buffer-output fn2-b3-output-words fn-b3-output-cv fn-b3-output)))))

(local (defthm fn2-b3-append-assoc
 (equal (append (append a b) c) (append a (append b c)))))
(local (defun fn2-b3-append-buffer-byte (buf b fn2-b3)
 (declare (xargs :stobjs fn2-b3 :verify-guards nil))
 (let ((fn2-b3 (fn2-b3-store 0 (floor (len buf) 4) (fn2-b3-append-word buf 0 b fn2-b3) fn2-b3)))
   (fn2-b3-set-pos 0 (1+ (len buf)) fn2-b3))))
(local (defmacro fn2-b3-composite-columns (name op args changed value)
 `(defthm ,name (and ,@(fn2-b3-column-equations *fn2-b3-proof-columns* changed value (cons op args)))
    :hints (("Goal" :in-theory (enable ,op))))))
(local (fn2-b3-composite-columns fn2-b3-append-buffer-byte-columns fn2-b3-append-buffer-byte (buf b fn2-b3) fn2-b3-pos (1+ (len buf))))
(local (defthm fn2-b3-append-buffer-byte-packed
 (implies (and (fn2-b3-packedp buf 0 fn2-b3) (fn-b3-octet-listp buf) (unsigned-byte-p 8 b))
   (fn2-b3-packedp (append buf (list b)) 0 (fn2-b3-append-buffer-byte buf b fn2-b3)))
 :hints (("Goal" :use ((:instance fn2-b3-packed-append (base 0)))
          :in-theory (disable fn2-b3-packed-append)))))
(local (defthm fn2-b3-byte-when-room
 (implies (and (equal (fn2-b3-pos 0 fn2-b3) (len buf)) (< (len buf) 64))
  (equal (fn2-b3-byte 0 b fn2-digests fn2-b3) (mv fn2-digests (fn2-b3-append-buffer-byte buf b fn2-b3))))
 :rule-classes nil :hints (("Goal" :in-theory (enable fn2-b3-byte fn2-b3-append-word)))))
(local (in-theory (disable fn2-b3-append-buffer-byte)))
(local (defthm fn2-b3-match-put
 (implies (and (fn2-b3-match buf (cons b xs) root answer fn2-digests fn2-b3) (< (len buf) 64))
   (fn2-b3-match (append buf (list b)) xs root answer fn2-digests (fn2-b3-append-buffer-byte buf b fn2-b3)))
 :hints (("Goal" :use ((:instance fn2-b3-packed-words (xs (append buf (list b))) (fn2-b3 (fn2-b3-append-buffer-byte buf b fn2-b3))))
          :in-theory (disable fn2-b3-packed-words fn2-b3-suffix)
          :do-not-induct t))))

(local (defthm fn2-b3-packed-empty (fn2-b3-packedp nil base fn2-b3) :hints (("Goal" :expand ((fn2-b3-packedp nil base fn2-b3))))))
(local (defthm fn2-b3-output-middle-raw
 (equal (fn-b3-output-cv (fn2-b3-buffer-output nil fn2-digests fn2-b3))
        (fn-b3-compress (fn2-digest-list 0 fn2-digests) (fn2-b3-buffer-words fn2-b3)
          (fn2-b3-counter 0 fn2-b3) (fn2-b3-pos 0 fn2-b3) (if (equal (fn2-b3-blocks 0 fn2-b3) 0) 1 0)))
 :hints (("Goal" :in-theory (enable fn2-b3-buffer-output fn-b3-output fn-b3-output-cv)))))
(local (defthm fn2-b3-match-flush
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
            (depth (fn2-b3-depth 0 fn2-b3)) (src 56) (fn2-digests (fn2-b3-output 56 0 t nil fn2-digests fn2-b3))))))))
(local (defthm fn2-b3-match-pos
 (implies (fn2-b3-match buf xs root answer fn2-digests fn2-b3)
  (and (equal (fn2-b3-pos 0 fn2-b3) (len buf)) (<= (len buf) 64)))
 :rule-classes nil))
(local (defthm fn2-b3-flush-pos
 (equal (fn2-b3-pos 0 (mv-nth 1 (fn2-b3-flush 0 fn2-digests fn2-b3))) 0)
 :hints (("Goal" :in-theory (enable fn2-b3-flush)))))
(local (defthm fn2-b3-suffix-one
 (implies (and (natp n) (<= n (len past)) (true-listp past))
  (equal (fn2-b3-suffix (1+ n) (append past (list b))) (append (fn2-b3-suffix n past) (list b))))
 :hints (("Goal" :use ((:instance fn2-b3-suffix-append (more (list b))))
          :in-theory (disable fn2-b3-suffix fn2-b3-suffix-append)))))
(local (defthm fn2-b3-len-suffix
 (implies (and (natp n) (<= n (len past))) (equal (len (fn2-b3-suffix n past)) n))))
(local (in-theory (disable fn2-b3-suffix fn2-b3-match)))
(local (defthm fn2-b3-good-flush
 (implies (and (fn2-b3-good past xs root answer fn2-digests fn2-b3)
               (equal (fn2-b3-pos 0 fn2-b3) 64) (consp xs))
  (mv-let (dg b3) (fn2-b3-flush 0 fn2-digests fn2-b3)
    (fn2-b3-good past xs root answer dg b3)))
 :hints (("Goal" :use ((:instance fn2-b3-match-flush (buf (fn2-b3-suffix 64 past))))))))
(local (defthm fn2-b3-good-put
 (let ((buf (fn2-b3-suffix (fn2-b3-pos 0 fn2-b3) past)))
  (implies (and (fn2-b3-good past (cons b xs) root answer fn2-digests fn2-b3)
                (< (fn2-b3-pos 0 fn2-b3) 64))
    (fn2-b3-good (append past (list b)) xs root answer fn2-digests (fn2-b3-append-buffer-byte buf b fn2-b3))))
 :hints (("Goal" :use ((:instance fn2-b3-match-pos (xs (cons b xs)) (buf (fn2-b3-suffix (fn2-b3-pos 0 fn2-b3) past)))
                       (:instance fn2-b3-match-put (buf (fn2-b3-suffix (fn2-b3-pos 0 fn2-b3) past)))))
         )))
(local (defthm fn2-b3-good-pos
 (implies (fn2-b3-good past xs root answer fn2-digests fn2-b3)
  (and (natp (fn2-b3-pos 0 fn2-b3)) (<= (fn2-b3-pos 0 fn2-b3) 64)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-b3-match-pos (buf (fn2-b3-suffix (fn2-b3-pos 0 fn2-b3) past))))))))
(local (defthm fn2-b3-byte-from-full
 (implies (equal (fn2-b3-pos 0 fn2-b3) 64)
  (equal (fn2-b3-byte 0 b fn2-digests fn2-b3)
         (mv-let (dg b3) (fn2-b3-flush 0 fn2-digests fn2-b3)
           (mv dg (fn2-b3-append-buffer-byte nil b b3)))))
 :hints (("Goal" :in-theory (enable fn2-b3-byte fn2-b3-append-buffer-byte fn2-b3-append-word)))))
(local (defthm fn2-b3-good-byte
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
          :expand ((fn2-b3-good past (cons b xs) root answer fn2-digests fn2-b3))))))
(local (defthm fn2-b3-pool-blocks-list
 (let ((v (fn-b3-pool-blocks off ctr n j a b c d e f g h fn2-pool)))
  (and (true-listp v) (equal (len v) 8) (equal (fn-b3-cv8 v) v)))
 :hints (("Goal" :induct (fn-b3-pool-blocks off ctr n j a b c d e f g h fn2-pool)
                 :in-theory (enable fn-b3-pool-blocks fn-b3-cv8)))))
(local (defthm fn2-b3-pool-run-shape
 (let ((v (fn2-b3-pool-run off ctr n j cv fn2-pool)))
  (and (true-listp v) (equal (len v) 8) (equal (fn-b3-cv8 v) v)))
 :hints (("Goal" :in-theory (enable fn2-b3-pool-run)))))
(local (defthm fn2-b3-pool-message-reads
 (implies (and (natp i) (<= i 16) (natp k) (< k 16))
  (equal (fn2-b3-word 0 k (fn2-b3-pool-message 0 off i fn2-b3 fn2-pool))
         (if (< k i) (fn2-b3-word 0 k fn2-b3)
           (fn-b3-word (fn-b3-pool-word (+ off (* 4 k)) fn2-pool)))))
 :hints (("Goal" :induct (fn2-b3-pool-message 0 off i fn2-b3 fn2-pool)
          :in-theory (enable fn2-b3-pool-message)))))
(local (defthm fn2-b3-pool-message-columns
 (let ((next (fn2-b3-pool-message 0 off i fn2-b3 fn2-pool)))
  (and (equal (fn2-b3-origin 0 next) (fn2-b3-origin 0 fn2-b3))
       (equal (fn2-b3-flags 0 next) (fn2-b3-flags 0 fn2-b3))
       (equal (fn2-b3-depth 0 next) (fn2-b3-depth 0 fn2-b3))
       (equal (fn2-b3-verify-phase 0 next) (fn2-b3-verify-phase 0 fn2-b3))))
 :hints (("Goal" :induct (fn2-b3-pool-message 0 off i fn2-b3 fn2-pool)
          :in-theory (enable fn2-b3-pool-message)))))
(local (defthm fn2-b3-word-set-columns
 (and (equal (fn2-b3-word 0 i (fn2-b3-set-blocks 0 n fn2-b3)) (fn2-b3-word 0 i fn2-b3))
      (equal (fn2-b3-word 0 i (fn2-b3-set-counter 0 n fn2-b3)) (fn2-b3-word 0 i fn2-b3)))
 :hints (("Goal" :in-theory (enable fn2-b3-word fn2-b3-set-blocks fn2-b3-set-counter update-fn2-b3-blocks$ai update-fn2-b3-counter$ai)))))
(local (defthm fn2-b3-chunk-output-rows
 (let ((next (mv-nth 0 (fn2-b3-chunk-output-into 0 off ctr fn2-digests fn2-b3 fn2-pool))))
   (equal next (fn2-digest-load 0 (fn2-b3-pool-run off ctr 15 0 *fn-b3-iv* fn2-pool) fn2-digests)))
 :hints (("Goal" :in-theory (e/d (fn2-b3-chunk-output-into fn2-digest-load fn2-b3-pool-run fn2-b3-mv-nth-is-nth)
                                  (nth mv-nth))))))
(local (defthm fn2-b3-chunk-output-buffer
 (equal (mv-nth 1 (fn2-b3-chunk-output-into 0 off ctr fn2-digests fn2-b3 fn2-pool))
        (fn2-b3-set-pos 0 64 (fn2-b3-set-blocks 0 15 (fn2-b3-set-counter 0 ctr
         (fn2-b3-pool-message 0 (+ 960 off) 0 fn2-b3 fn2-pool)))))
 :hints (("Goal" :in-theory (enable fn2-b3-chunk-output-into)))))
(local (defthm fn2-b3-load-cv-preserves-frontier
 (implies (and (true-listp ws) (equal (len ws) 8))
  (equal (fn2-b3-frontier-list d (fn2-digest-load 0 ws fn2-digests)) (fn2-b3-frontier-list d fn2-digests)))
 :hints (("Goal" :induct (fn2-b3-frontier-list d fn2-digests) :in-theory (enable fn2-b3-frontier-list)))))

(local (defthm fn2-b3-message-final-words
 (implies (and (natp off) (fn2-b3-covers xs off fn2-pool) (fn-b3-octet-listp xs) (equal (len xs) 64))
  (equal (fn2-b3-buffer-words
   (fn2-b3-set-pos 0 64 (fn2-b3-set-blocks 0 15 (fn2-b3-set-counter 0 ctr
      (fn2-b3-pool-message 0 off 0 fn2-b3 fn2-pool)))))
   (fn-b3-words 16 xs)))
 :rule-classes nil
 :hints ((and t `(:use ((:instance fn2-b3-word-sequence-correct (i 0) (k 16))
                        ,@(fn2-b3-pool-word-instances 16))
                 :in-theory (e/d (fn2-b3-buffer-words fn2-b3-block-word) (fn2-b3-word-sequence-correct)))))))
(local (defthm fn2-b3-resume-deferred
 (implies (and (true-listp chunk) (equal (len chunk) 1024)
               (true-listp buf) (equal (len buf) 64) (true-listp rest)
               (equal (fn-b3-chunk cv buf ctr 0 nil) (fn-b3-chunk *fn-b3-iv* chunk ctr 0 t)))
  (equal (fn2-b3-resume (append buf rest) cv 15 ctr org stack root)
         (fn2-b3-resume (append chunk rest) *fn-b3-iv* 0 ctr org stack root)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :expand ((fn-b3-firstn 0 rest)) :cases ((consp rest)) :in-theory (enable fn2-b3-resume)))))
(local (defthm fn2-b3-match-last-span
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
          :in-theory (enable fn2-b3-match fn2-b3-chunk-last)))))

(local (defthm fn2-b3-resume-pushed-chunk
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
        :expand ((fn-b3-firstn 0 xs)) :in-theory (enable fn2-b3-resume)))))
(local (defthm fn2-b3-match-bulk-push
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
                     (fn2-b3-subtree-chunk-effect fn2-b3-subtree-cv-into-by-definition))))))
(local (defthm fn2-b3-good-bulk
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
          :in-theory (enable fn2-b3-bulk fn2-b3-suffix)))))

(local (defthm fn2-b3-consp-by-length
 (iff (consp xs) (< 0 (len xs))) :rule-classes nil))
(local (defthm fn2-b3-good-counter-bounded
 (implies (fn2-b3-good past xs root answer fn2-digests fn2-b3)
          (unsigned-byte-p 54 (fn2-b3-counter 0 fn2-b3)))
 :rule-classes nil :hints (("Goal" :in-theory (enable fn2-b3-good fn2-b3-match)))))
(local (in-theory (disable fn2-b3-good fn2-b3-byte-from-full)))
(local (defthm fn2-b3-good-room
 (implies (and (fn2-b3-good past xs root answer fn2-digests fn2-b3) (consp xs))
  (fn2-b3-roomp 0 fn2-b3))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-b3-bits-bound (k 54)
                       (n (- (fn2-b3-counter 0 fn2-b3) (fn2-b3-origin 0 fn2-b3)))))
          :in-theory (enable fn2-b3-good fn2-b3-match fn2-b3-roomp)))))
(local (defthm fn2-b3-good-counter
 (implies (fn2-b3-good past xs root answer fn2-digests fn2-b3)
          (natp (fn2-b3-counter 0 fn2-b3)))
 :rule-classes nil :hints (("Goal" :in-theory (enable fn2-b3-good fn2-b3-match)))))
(local (defthm fn2-b3-flush-boundary
 (implies (and (equal (fn2-b3-blocks 0 fn2-b3) 15) (unsigned-byte-p 54 (fn2-b3-counter 0 fn2-b3)))
  (let ((b3 (mv-nth 1 (fn2-b3-flush 0 fn2-digests fn2-b3))))
    (and (equal (fn2-b3-blocks 0 b3) 0) (equal (fn2-b3-counter 0 b3) (1+ (fn2-b3-counter 0 fn2-b3))))))
 :hints (("Goal" :in-theory (enable fn2-b3-flush)))))
(local (defthm fn2-b3-window-base
 (implies (fn2-b3-windowp used fn2-pool) (equal (fn2-pool-slot-base 0 fn2-pool) 0))
 :hints (("Goal" :in-theory (enable fn2-pool-slot-base fn2-b3-windowp)))))
(local (defthm fn2-b3-span-shape-at-entry
 (implies (fn2-b3-can-span 0 0 1 off left consumed 1 0 1 fn2-b3 fn2-pool)
  (or (and (equal (fn2-b3-pos 0 fn2-b3) 64) (equal (fn2-b3-blocks 0 fn2-b3) 15))
      (and (equal (fn2-b3-pos 0 fn2-b3) 0) (equal (fn2-b3-blocks 0 fn2-b3) 0))))
 :rule-classes nil :hints (("Goal" :in-theory (enable fn2-b3-can-span)))))
(local (defthm fn2-b3-good-span
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
          :in-theory (enable fn2-b3-span fn2-b3-next-counter)))))

(local (defthm fn2-b3-cut-rejoin
 (implies (true-listp xs) (equal (append (fn-b3-firstn n xs) (fn-b3-nthcdrx n xs)) xs))
 :hints (("Goal" :induct (fn-b3-nthcdrx n xs) :in-theory (fn2-b3-list-theory fn-b3-firstn fn-b3-nthcdrx)))))
(local (defthm fn2-b3-cut-rejoin-rest
 (implies (true-listp xs)
  (equal (append (fn-b3-firstn n xs) (append (fn-b3-nthcdrx n xs) rest)) (append xs rest)))
 :hints (("Goal" :use ((:instance fn2-b3-append-assoc (a (fn-b3-firstn n xs)) (b (fn-b3-nthcdrx n xs)) (c rest)))
          :in-theory (disable fn2-b3-append-assoc)))))
(local (defthm fn2-b3-first-covers
 (implies (fn2-b3-covers xs off fn2-pool) (fn2-b3-covers (fn-b3-firstn n xs) off fn2-pool))
 :hints (("Goal" :induct (fn2-b3-drop-induct n off xs) :in-theory (fn2-b3-list-theory fn2-b3-drop-induct fn2-b3-covers fn-b3-firstn)))))
(local (defthm fn2-b3-first-octets
 (implies (fn-b3-octet-listp xs) (fn-b3-octet-listp (fn-b3-firstn n xs)))
 :hints (("Goal" :induct (fn-b3-firstn n xs) :in-theory (fn2-b3-list-theory fn-b3-firstn fn-b3-octet-listp)))))
(local (defthm fn2-b3-covers-head
 (implies (and (consp xs) (fn2-b3-covers xs off fn2-pool))
  (and (equal (fn2-pool-datai off fn2-pool) (car xs)) (fn2-b3-covers (cdr xs) (1+ off) fn2-pool)))
 :hints (("Goal" :expand ((fn2-b3-covers xs off fn2-pool))))))
(local (defun fn2-b3-frag-induct (bytes past off fn2-digests fn2-b3 fn2-pool)
 (declare (xargs :stobjs (fn2-digests fn2-b3 fn2-pool) :verify-guards nil))
 (if (atom bytes) (mv (list past off) fn2-digests fn2-b3)
  (mv-let (fn2-digests fn2-b3) (fn2-b3-byte 0 (fn2-pool-datai off fn2-pool) fn2-digests fn2-b3)
   (fn2-b3-frag-induct (cdr bytes) (append past (list (car bytes))) (1+ off) fn2-digests fn2-b3 fn2-pool)))))
(local (defthm fn2-b3-good-past-list
 (implies (fn2-b3-good past xs root answer fn2-digests fn2-b3) (true-listp past))
 :rule-classes :forward-chaining :hints (("Goal" :in-theory (enable fn2-b3-good)))))
(local (defthm fn2-b3-good-fragment
 (implies (and (fn2-b3-good past (append bytes rest) root answer fn2-digests fn2-b3)
               (fn2-b3-covers bytes off fn2-pool) (fn-b3-octet-listp bytes))
  (mv-let (dg b3) (fn2-b3-fragment-into 0 off (len bytes) fn2-digests fn2-b3 fn2-pool)
    (fn2-b3-good (append past bytes) rest root answer dg b3)))
 :hints (("Goal" :induct (fn2-b3-frag-induct bytes past off fn2-digests fn2-b3 fn2-pool)
          :expand ((:free (n) (fn2-b3-fragment-into 0 off n fn2-digests fn2-b3 fn2-pool))
                   (append bytes rest)))
         ("Subgoal *1/2" :use ((:instance fn2-b3-good-byte (b (car bytes)) (xs (append (cdr bytes) rest))))))))

(local (in-theory (disable fn2-b3-roomp fn2-b3-read fn2-pool-slot-base)))
(local (defun fn2-b3-feed-induct (bytes past off fn2-digests fn2-b3 fn2-pool)
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
              fn2-digests fn2-b3 fn2-pool))))))
(local (defthm fn2-b3-feed-span-step
 (implies (and (fn2-b3-good past (append bytes rest) root answer fn2-digests fn2-b3)
               (fn2-b3-covers bytes off fn2-pool) (fn-b3-octet-listp bytes) (fn-b3-octet-listp rest) (natp off)
               (<= 1024 (len bytes)) (fn2-b3-can-span 0 0 1 off (len bytes) off 1 0 1 fn2-b3 fn2-pool))
  (mv-let (dg b3) (fn2-b3-span 0 off (fn2-b3-next-counter 0 fn2-b3) (< (len bytes) 2048) fn2-digests fn2-b3 fn2-pool)
   (fn2-b3-good (append past (fn-b3-firstn 1024 bytes)) (append (fn-b3-nthcdrx 1024 bytes) rest) root answer dg b3)))
 :hints (("Goal" :use ((:instance fn2-b3-good-span (chunk (fn-b3-firstn 1024 bytes))
                (xs (append (fn-b3-nthcdrx 1024 bytes) rest)) (left (len bytes)) (consumed off)
                (lastp (< (len bytes) 2048)))
            (:instance fn2-b3-consp-by-length (xs (append (fn-b3-nthcdrx 1024 bytes) rest))))
          :do-not-induct t))))
(local (defthm fn2-b3-good-feed
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
                         (:instance fn2-b3-window-base (used (+ off (len bytes)))))))))
(local (defthm fn2-b3-admitted-window-length
 (implies (<= n 4096) (equal (min n 4096) n))))
(local (defthm fn2-b3-fragment-zero
 (equal (fn2-b3-fragment-into 0 off 0 fn2-digests fn2-b3 fn2-pool) (mv fn2-digests fn2-b3))
 :hints (("Goal" :expand ((fn2-b3-fragment-into 0 off 0 fn2-digests fn2-b3 fn2-pool))))))
(local (defthm fn2-b3-update-at-cut
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
          :do-not-induct t :in-theory (disable fn2-b3-good-fragment fn2-b3-good-feed)))))
(local (in-theory (disable min)))
(local (defthm fn2-b3-good-update
 (implies (and (fn2-b3-good past (append bytes rest) root answer fn2-digests fn2-b3)
               (fn2-b3-covers bytes 0 fn2-pool) (fn-b3-octet-listp bytes) (fn-b3-octet-listp rest)
               (<= (len bytes) 4096) (fn2-b3-windowp (len bytes) fn2-pool))
  (mv-let (code count dg b3) (fn2-b3-update 0 0 1 0 (len bytes) 1 0 1 fn2-digests fn2-b3 fn2-pool)
    (and (equal code :ok) (equal count (len bytes)) (fn2-b3-good (append past bytes) rest root answer dg b3))))
 :hints (("Goal" :cases ((equal (fn2-b3-fragment-count 0 0 1 0 (len bytes) 1 0 1 fn2-b3 fn2-pool) 0)))
         ("Subgoal 2" :use ((:instance fn2-b3-update-at-cut (n (fn2-b3-fragment-count 0 0 1 0 (len bytes) 1 0 1 fn2-b3 fn2-pool))))
          :in-theory (enable fn2-b3-update) :do-not-induct t)
         ("Subgoal 1" :use ((:instance fn2-b3-update-at-cut (n 0))) :in-theory (enable fn2-b3-update) :do-not-induct t))))
(local (defthm fn2-b3-loaded-update
 (implies (and (fn2-b3-good past (append bytes rest) root answer fn2-digests fn2-b3)
               (fn-b3-octet-listp bytes) (fn-b3-octet-listp rest) (<= (len bytes) 4096)
               (fn2-b3-windowp 0 fn2-pool))
  (let ((pool (fn2-b3-spec-load bytes 0 fn2-pool)))
   (mv-let (code count dg b3) (fn2-b3-update 0 0 1 0 (len bytes) 1 0 1 fn2-digests fn2-b3 pool)
    (declare (ignore code count))
    (fn2-b3-good (append past bytes) rest root answer dg b3))))
 :hints (("Goal" :use ((:instance fn2-b3-window-loaded (xs bytes) (off 0)) (:instance fn2-b3-loaded-covers (xs bytes)) (:instance fn2-b3-good-update (fn2-pool (fn2-b3-spec-load bytes 0 fn2-pool))))
          :in-theory (disable fn2-b3-good-update fn2-b3-spec-load)))))

(local (defun fn2-b3-splits-window-induct (splits past used fn2-digests fn2-b3 fn2-pool)
 (declare (xargs :stobjs (fn2-digests fn2-b3 fn2-pool) :verify-guards nil))
 (if (atom splits) (mv (list past used) fn2-digests fn2-b3 fn2-pool)
  (b* (((mv & fn2-pool) (fn2-pool-reset 0 1 1 0 1 fn2-pool))
       (fn2-pool (fn2-b3-spec-load (car splits) 0 fn2-pool))
       ((mv & & fn2-digests fn2-b3) (fn2-b3-update 0 0 1 0 (len (car splits)) 1 0 1 fn2-digests fn2-b3 fn2-pool)))
    (fn2-b3-splits-window-induct (cdr splits) (append past (car splits)) (len (car splits)) fn2-digests fn2-b3 fn2-pool)))))
; A split may end in the middle of a word, a block, or a chunk.
(local (defthm fn2-b3-good-splits
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
                 (fn2-pool (mv-nth 1 (fn2-pool-reset 0 1 1 0 1 fn2-pool)))))))))

(local (defthm fn2-b3-resume-end
 (implies (and (true-listp buf) (<= (len buf) 64) (natp j) (< j 16))
  (equal (fn2-b3-resume buf cv j ctr org stack root)
         (fn2-b3-seal stack (fn-b3-chunk cv buf ctr 0 (equal j 0)) root)))
 :hints (("Goal" :in-theory (enable fn2-b3-resume) :do-not-induct t))))
(local (defthm fn2-b3-seal-frontier
 (let ((stack (fn2-b3-frontier-list depth fn2-digests)))
  (implies (and (natp depth) (booleanp root))
    (equal (fn2-b3-fold-list stack (fn2-b3-output-words out (and root (equal depth 0))) *fn-b3-iv* 0 root)
           (fn2-b3-seal stack out root))))
 :hints (("Goal" :cases ((zp depth) root)
          :expand ((fn2-b3-frontier-list 0 fn2-digests)
                   (:free (cv r) (fn2-b3-fold-list nil cv *fn-b3-iv* 0 r)))
          :in-theory (enable fn2-b3-seal)))))
(local (defthm fn2-b3-match-end-facts
 (let ((depth (fn2-b3-depth 0 fn2-b3)))
  (implies (fn2-b3-match buf nil root answer fn2-digests fn2-b3)
   (and (natp depth) (<= depth 54) (equal (fn2-b3-flags 0 fn2-b3) 0)
        (equal (fn2-digest-list 1 fn2-digests) *fn-b3-iv*)
        (equal answer (fn2-b3-seal (fn2-b3-frontier-list depth fn2-digests)
                       (fn2-b3-buffer-output t fn2-digests fn2-b3) root)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-b3-packed-words (xs buf)) fn2-b3-buffer-cv
                       (:instance fn2-b3-bits-bound (k 54) (n (- (fn2-b3-counter 0 fn2-b3) (fn2-b3-origin 0 fn2-b3)))))
          :in-theory (fn2-b3-list-theory fn2-b3-match fn2-b3-resume-end fn2-b3-octets-true-list fn2-b3-bits-natp append-to-nil fn2-b3-len-append) :do-not-induct t))))
(local (defthm fn2-b3-match-finish
 (implies (and (booleanp root) (fn2-b3-match buf nil root answer fn2-digests fn2-b3))
   (equal (fn2-digest-list 136 (fn2-b3-finish 136 0 root fn2-digests fn2-b3)) answer))
 :rule-classes nil
 :hints (("Goal" :use (fn2-b3-match-end-facts fn2-b3-finish-refines-list
                      (:instance fn2-b3-seal-frontier (depth (fn2-b3-depth 0 fn2-b3))
                           (out (fn2-b3-buffer-output t fn2-digests fn2-b3))))
          :in-theory (theory 'minimal-theory)))))
(local (defthm fn2-b3-good-finish
 (implies (and (booleanp root) (fn2-b3-good past nil root answer fn2-digests fn2-b3))
   (equal (fn2-digest-list 136 (fn2-b3-finish 136 0 root fn2-digests fn2-b3)) answer))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-b3-match-finish (buf (fn2-b3-suffix (fn2-b3-pos 0 fn2-b3) past))))
          :in-theory (enable fn2-b3-good)))))
(local (in-theory (enable update-fn2-b3-verify-phase$ai update-fn2-b3-flags$ai)))
(local (fn2-b3-prove-column-reads fn2-b3-phase-columns fn2-b3-set-verify-phase (0 v fn2-b3) fn2-b3-verify-phase v))
(local (fn2-b3-prove-column-reads fn2-b3-flags-columns fn2-b3-set-flags (0 v fn2-b3) fn2-b3-flags v))
(local (in-theory (disable fn2-b3-set-flags fn2-b3-set-verify-phase)))
(local (defthm fn2-b3-init-zero-fields
 (let ((b3 (mv-nth 1 (fn2-b3-init 0 0 136 fn2-digests fn2-b3))))
  (and (equal (fn2-b3-pos 0 b3) 0) (equal (fn2-b3-blocks 0 b3) 0)
       (equal (fn2-b3-verify-phase 0 b3) 0)))
 :hints (("Goal" :in-theory (enable fn2-b3-init)))))
(local (defthm fn2-b3-good-init
 (implies (and (natp ctr) (fn-b3-octet-listp xs) (< (+ (* 1024 ctr) (len xs)) (expt 2 64)))
  (mv-let (dg b3) (fn2-b3-init 0 0 136 fn2-digests fn2-b3)
   (fn2-b3-good nil xs root (fn2-b3-output-words (fn-b3-node *fn-b3-iv* xs ctr 0) root)
                dg (fn2-b3-start-subtree 0 ctr b3))))
 :hints (("Goal" :do-not-induct t :use (fn2-b3-init-observations (:instance fn2-b3-scan-is-node (k 0) (counter ctr))
                       (:instance fn2-b3-resume-start (org ctr) (stack nil)))
          :expand ((:free (dg) (fn2-b3-frontier-list 0 dg)) (fn2-b3-bits 0))
          :in-theory (enable fn2-b3-good fn2-b3-match fn2-b3-start-subtree)))))
(local (defthm fn2-b3-initial-window
 (fn2-b3-windowp 0 (mv-nth 3 (fn2-pool-reserve 0 1 0 1
           (fn2-pool-init '((1 . 4096)) 1 100 (create-fn2-pool)))))
 :hints (("Goal" :expand ((create-fn2-pool)) :in-theory (executable-counterpart-theory :here)))))

(local (defthm fn2-b3-finish-splits
 (implies (and (booleanp root) (fn2-b3-splitsp splits) (fn2-b3-windowp 0 fn2-pool)
               (fn2-b3-good nil (fn2-b3-flatten splits) root answer fn2-digests fn2-b3))
  (mv-let (dg b3 pool) (fn2-b3-spec-splits splits fn2-digests fn2-b3 fn2-pool)
    (declare (ignore pool)) (equal (fn2-digest-list 136 (fn2-b3-finish 136 0 root dg b3)) answer)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-b3-good-splits (past nil) (used 0))
              (:instance fn2-b3-good-finish (past (fn2-b3-flatten splits))
               (fn2-digests (mv-nth 0 (fn2-b3-spec-splits splits fn2-digests fn2-b3 fn2-pool)))
               (fn2-b3 (mv-nth 1 (fn2-b3-spec-splits splits fn2-digests fn2-b3 fn2-pool)))))
          :in-theory (disable fn2-b3-spec-splits fn2-b3-good-splits)))))
(local (defthm fn2-b3-split-digest-correct
 (implies (and (booleanp root) (natp ctr) (fn2-b3-splitsp splits)
               (< (+ (* 1024 ctr) (len (fn2-b3-flatten splits))) (expt 2 64)))
  (equal (fn2-b3-split-digest splits ctr root)
         (fn2-b3-output-words (fn-b3-node *fn-b3-iv* (fn2-b3-flatten splits) ctr 0) root)))
 :rule-classes nil
 :hints ((let* ((dg '(fn2-digests-init 144 (create-fn2-digests)))
                (b3 '(fn2-b3-table-init 1 (create-fn2-b3)))
                (init `(fn2-b3-init 0 0 136 ,dg ,b3))
                (pool '(mv-nth 3 (fn2-pool-reserve 0 1 0 1 (fn2-pool-init '((1 . 4096)) 1 100 (create-fn2-pool))))))
          `(:use ((:instance fn2-b3-good-init (xs (fn2-b3-flatten splits)) (fn2-digests ,dg) (fn2-b3 ,b3))
                  (:instance fn2-b3-finish-splits (fn2-pool ,pool)
                   (fn2-digests (mv-nth 0 ,init)) (fn2-b3 (fn2-b3-start-subtree 0 ctr (mv-nth 1 ,init)))
                   (answer (fn2-b3-output-words (fn-b3-node *fn-b3-iv* (fn2-b3-flatten splits) ctr 0) root))))
            :expand ((fn2-b3-split-digest splits ctr root))
            :in-theory (disable fn2-b3-spec-splits fn2-b3-good-init fn2-pool-reserve fn2-pool-init)
            :do-not-induct t)))))

(local (defun fn2-b3-block-induct (blocks counters ctr)
 (if (or (atom blocks) (atom (cdr blocks))) (list counters ctr)
   (fn2-b3-block-induct (cdr blocks) (cdr counters) (+ 64 ctr)))))
(local (defthm fn2-b3-block-cvsp-atom
 (implies (not (consp blocks)) (fn2-b3-block-cvsp blocks counters))
 :hints (("Goal" :expand ((fn2-b3-block-cvsp blocks counters))))))
(local (defthm fn2-b3-subtree-inputs-have-cvs
 (implies (and (natp ctr) (fn2-b3-subtree-inputsp blocks counters ctr)
               (< (+ (* 1024 ctr) (len (fn2-b3-block-bytes blocks))) (expt 2 64)))
          (fn2-b3-block-cvsp blocks counters))
 :hints (("Goal" :induct (fn2-b3-block-induct blocks counters ctr)
          :expand ((fn2-b3-block-cvsp blocks counters) (:free (c) (fn2-b3-subtree-inputsp blocks counters c))
                   (fn2-b3-block-bytes blocks)))
         ("Subgoal *1/2" :use ((:instance fn2-b3-split-digest-correct (splits (car blocks)) (root nil))))
         ("Subgoal *1/1" :use ((:instance fn2-b3-split-digest-correct (splits (car blocks)) (root nil)))))))
(local (defthm fn2-b3-subtree-hyps-have-cvs
 (implies (fn2-b3-subtree-hyps blocks counters) (fn2-b3-block-cvsp blocks counters))
 :hints (("Goal" :use ((:instance fn2-b3-subtree-inputs-have-cvs (ctr 0)))
          :in-theory (e/d (fn2-b3-subtree-hyps) (fn2-b3-flatten fn2-b3-subtree-inputs-have-cvs))))))
(defthm fn2-b3-subtree-composition-proved
 (implies (fn2-b3-subtree-hyps blocks counters) (fn2-b3-subtree-resultp blocks counters))
 :rule-classes nil
 :hints (("Goal" :use (fn2-b3-subtree-hyps-have-cvs fn2-b3-compose-correct-from-cvs)
          :in-theory (theory 'minimal-theory))))
(fn2-owed-discharge fn2-b3-subtree-composition fn2-b3-subtree-composition-proved)

(defthm fn2-b3-incremental-is-blake3-proved
  (implies (fn2-b3-incremental-hyps splits)
           (fn2-b3-incremental-resultp splits))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-b3-split-digest-correct (ctr 0) (root t)))
                  :in-theory (enable fn2-b3-incremental-hyps fn2-b3-incremental-resultp
                                     fn-blake3 fn-b3-hash))))

(fn2-owed-discharge fn2-b3-incremental-is-blake3 fn2-b3-incremental-is-blake3-proved)
