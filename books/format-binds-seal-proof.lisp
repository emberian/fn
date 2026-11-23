; Discharges fn2-format-frame-binds-location; exports fc-accepted-covered-hash and fc-same-trailer-same-digest.
; One link of the format-binds proof chain; events are exported so the next link sees the same world.
(in-package "ACL2")
(include-book "format-binds-hash-proof")

(defthm fc-le8-is-word-bytes
  (implies (natp v)
           (equal (fn2-layout-le 8 v)
                  (list (fn2-fc-word-byte v 0) (fn2-fc-word-byte v 1) (fn2-fc-word-byte v 2)
                        (fn2-fc-word-byte v 3) (fn2-fc-word-byte v 4) (fn2-fc-word-byte v 5)
                        (fn2-fc-word-byte v 6) (fn2-fc-word-byte v 7))))
  :hints (("Goal" :in-theory (union-theories (current-theory 'fc-u32-reconstruct)
                                '(fn2-fc-word-byte ash fc-le-fits-at-fixed-width))
           :expand ((:free (n v) (fn2-layout-le n v))))))
(defthm fc-prefix-from-unroll
  (implies (and (syntaxp (quotep pos)) (syntaxp (quotep n)))
           (equal (fc-prefix-from pos n kind ctx)
                  (if (and (natp pos) (natp n) (< pos n))
                      (cons (fn2-fc-prefix-byte 0 kind pos ctx) (fc-prefix-from (1+ pos) n kind ctx))
                    nil)))
  :hints (("Goal" :expand ((fc-prefix-from pos n kind ctx)))))
(defthm fc-word-byte-wrap
  (implies (and (syntaxp (quotep i)) (natp i) (<= 8 i))
           (equal (fn2-fc-word-byte v i) (fn2-fc-word-byte v (- i 8))))
  :hints (("Goal" :in-theory (union-theories (current-theory 'fc-u32-reconstruct) '(fn2-fc-word-byte)))))
(deftheory fc-prefix-theory
  (union-theories (theory 'minimal-theory)
    '(fc-prefix-from-unroll fc-word-byte-wrap fc-le8-is-word-bytes fn2-fc-prefix-byte
      binary-append car-cons cdr-cons natp
      (:executable-counterpart fn2-fc-domain) (:executable-counterpart length)
      (:executable-counterpart char) (:executable-counterpart char-code)
      (:executable-counterpart <) (:executable-counterpart natp) (:executable-counterpart binary-+)
      (:executable-counterpart unary--) (:executable-counterpart fn2-fc-string-bytes)
      (:executable-counterpart eq) (:executable-counterpart equal) (:executable-counterpart not)
      (:executable-counterpart consp) (:executable-counterpart car) (:executable-counterpart cdr)
      (:executable-counterpart binary-append))))
(defthm fc-frame-prefix
  (implies (and (natp (fn2-fc-context-location 0 c)) (natp (fn2-fc-context-extent-writer-epoch 0 c))
                (natp (fn2-fc-context-allocation 0 c)))
   (equal (fc-prefix-from 0 44 :frame c)
          (append (fn2-fc-string-bytes (fn2-fc-domain :frame) 0)
                  (append (fn2-layout-le 8 (fn2-fc-context-location 0 c))
                          (append (fn2-layout-le 8 (fn2-fc-context-extent-writer-epoch 0 c))
                                  (fn2-layout-le 8 (fn2-fc-context-allocation 0 c)))))))
  :hints (("Goal" :in-theory (theory 'fc-prefix-theory))))
(defthm fc-seal-prefix
  (implies (and (natp (fn2-fc-context-history 0 c)) (natp (fn2-fc-context-incarnation 0 c))
                (natp (fn2-fc-context-extent 0 c)) (natp (fn2-fc-context-extent-writer-epoch 0 c))
                (natp (fn2-fc-context-allocation 0 c)))
   (equal (fc-prefix-from 0 59 :seal c)
          (append (fn2-fc-string-bytes (fn2-fc-domain :seal) 0)
                  (append (fn2-layout-le 8 (fn2-fc-context-history 0 c))
                          (append (fn2-layout-le 8 (fn2-fc-context-incarnation 0 c))
                                  (append (fn2-layout-le 8 (fn2-fc-context-extent 0 c))
                                          (append (fn2-layout-le 8 (fn2-fc-context-extent-writer-epoch 0 c))
                                                  (fn2-layout-le 8 (fn2-fc-context-allocation 0 c)))))))))
  :hints (("Goal" :in-theory (theory 'fc-prefix-theory))))
(defun fc-zeros (n) (if (zp n) nil (cons 0 (fc-zeros (1- n)))))
(defthm fc-body-tail-zeros
  (implies (and (natp pos) (natp len) (<= (- len 32) pos) (<= pos len))
           (equal (fc-body-from pos len bytes) (fc-zeros (- len pos))))
  :hints (("Goal" :induct (fc-body-from pos len bytes)
           :in-theory (union-theories (current-theory 'fc-u32-reconstruct)
                         '(fc-body-from fc-zeros (:induction fc-body-from))))))
(defthm fc-nthcdr-step
  (implies (natp i)
           (and (equal (car (nthcdr i x)) (nth i x))
                (equal (cdr (nthcdr i x)) (nthcdr (+ 1 i) x))))
  :hints (("Goal" :induct (nthcdr i x)
           :in-theory (union-theories (current-theory 'fc-u32-reconstruct) '(nthcdr nth)))))
(defthm fc-fixed-take-step
  (implies (natp pos)
           (equal (fn-b3-fix-octets-walk (take n (nthcdr pos bytes)))
                  (if (zp n) nil
                    (cons (fn-b3-octet (nth pos bytes))
                          (fn-b3-fix-octets-walk (take (1- n) (nthcdr (1+ pos) bytes)))))))
  :rule-classes nil
  :hints (("Goal" :expand ((take n (nthcdr pos bytes)))
           :in-theory (union-theories (current-theory 'fc-u32-reconstruct)
                         '(fc-nthcdr-step fn-b3-fix-octets-walk)))))
(defthm fc-body-is-fixed-take
  (implies (and (natp pos) (natp n) (natp len) (equal (+ pos n) (- len 32)))
           (equal (fc-body-from pos len bytes)
                  (append (fn-b3-fix-octets-walk (take n (nthcdr pos bytes)))
                          (fc-zeros 32))))
  :rule-classes nil
  :hints (("Goal" :induct (fc-body-from-drop-induct n pos)
           :expand ((fc-body-from pos len bytes))
           :in-theory (union-theories
                        (set-difference-theories (current-theory 'fc-u32-reconstruct)
                           '((:definition take) (:definition nthcdr) (:definition nth)
                             (:definition fn-b3-fix-octets-walk)))
                        '((:induction fc-body-from-drop-induct) fc-body-from-drop-induct
                          (:executable-counterpart fc-zeros))))
          ("Subgoal *1/2" :use ((:instance fc-fixed-take-step)))
          ("Subgoal *1/1" :use ((:instance fc-fixed-take-step) (:instance fc-body-tail-zeros)))))
(defthm fc-fix-append
  (equal (fn-b3-fix-octets-walk (append a b))
         (append (fn-b3-fix-octets-walk a) (fn-b3-fix-octets-walk b)))
  :hints (("Goal" :induct (append a b)
           :in-theory (union-theories (theory 'minimal-theory)
                         '(binary-append fn-b3-fix-octets-walk car-cons cdr-cons
                           (:induction binary-append))))))
(defthm fc-fix-le
  (equal (fn-b3-fix-octets-walk (fn2-layout-le n v)) (fn2-layout-le n v))
  :hints (("Goal" :induct (fn2-layout-le n v)
           :in-theory (union-theories (current-theory 'fc-u32-reconstruct)
                         '(fn2-layout-le fn-b3-fix-octets-walk fn-b3-octet fn-b3-byte)))))
(defthm fc-stream-is-covered
  (implies (and (or (eq kind :frame) (eq kind :seal)) (fn2-fc-expectedp ctx) (<= 32 (len bytes)))
           (equal (fc-stream kind (len bytes) bytes (fc-image-context ctx))
                  (fn-b3-fix-octets (fn2-fc-covered kind bytes ctx))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fc-body-is-fixed-take (pos 0) (n (- (len bytes) 32)) (len (len bytes)))
                        (:instance fc-frame-prefix (c (fc-image-context ctx)))
                        (:instance fc-seal-prefix (c (fc-image-context ctx))))
           :in-theory (union-theories (theory 'minimal-theory)
              '(fc-stream fn2-fc-covered fn-b3-fix-octets fc-fix-append fc-fix-le fn2-fc-expectedp fc-append-associative
                fc-image-context-scalars fc-length-natural natp nfix nthcdr (:type-prescription len)
                unsigned-byte-p integer-range-p
                (:executable-counterpart fc-plen) (:executable-counterpart fc-zeros)
                (:executable-counterpart make-list-ac) (:executable-counterpart fn-b3-fix-octets-walk)
                (:executable-counterpart fn2-fc-domain) (:executable-counterpart fn2-fc-string-bytes)
                (:executable-counterpart zp) (:executable-counterpart eq)
                (:executable-counterpart equal) (:executable-counterpart natp)
                (:executable-counterpart expt) (:executable-counterpart <))))))
(defthm fc-blake3-is-answer-octets
  (equal (fn-blake3 m)
         (fn-b3-words-octets
           (fn2-b3-output-words (fn-b3-node *fn-b3-iv* (fn-b3-fix-octets m) 0 0) t)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-blake3 fn-b3-hash fn-b3-output-root fn2-b3-output-words
                (:executable-counterpart binary-logior) (:executable-counterpart ifix))))))
(defthm fc-answer-words
  (fn-b3-word-listp (fc-answer kind len bytes ctx))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fc-answer fn2-b3-output-words fn-b3-compress-shape)))))
(defthm fc-result-octets-unroll
  (implies (syntaxp (quotep n))
           (equal (fc-result-octets k n ds)
                  (if (zp n) nil
                    (cons (fn2-fc-digest-byte 0 k nil ds) (fc-result-octets (1+ k) (1- n) ds)))))
  :hints (("Goal" :expand ((fc-result-octets k n ds))
           :in-theory (union-theories (theory 'minimal-theory) '(fc-result-octets)))))
(defmacro fc-result-word (i)
  (let ((name (packn-pos (list 'fc-result-word- i) 'fc-result-octets))
        (w (packn-pos (list 'fn2-digests-w i) 'fn2-digests-w0)))
    `(defthm ,name
       (implies (and (fn-b3-word-listp (fn2-digest-list 125 da))
                     (fn-b3-word-listp (fn2-digest-list 125 db))
                     (equal (fc-result-octets 0 32 da) (fc-result-octets 0 32 db)))
                (equal (,w 125 da) (,w 125 db)))
       :rule-classes nil
       :hints (("Goal"
         :use ((:instance fc-u32-bytes-unique (x (,w 125 da)) (y (,w 125 db))))
         :in-theory (union-theories (theory 'minimal-theory)
            '(fc-result-octets-unroll fn2-fc-digest-byte fn2-digest-word fn2-digest-list fn-b3-word-listp
              car-cons cdr-cons cons-equal
              (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--)
              (:executable-counterpart floor) (:executable-counterpart mod)
              (:executable-counterpart fn2-digest-slot) (:executable-counterpart equal)
              (:executable-counterpart eql) (:executable-counterpart consp))))))))
(fc-result-word 0)
(fc-result-word 1)
(fc-result-word 2)
(fc-result-word 3)
(fc-result-word 4)
(fc-result-word 5)
(fc-result-word 6)
(fc-result-word 7)
(defthm fc-result-octets-fix-words
  (implies (and (fn-b3-word-listp (fn2-digest-list 125 da))
                (fn-b3-word-listp (fn2-digest-list 125 db))
                (equal (fc-result-octets 0 32 da) (fc-result-octets 0 32 db)))
           (equal (fn2-digest-list 125 da) (fn2-digest-list 125 db)))
  :rule-classes nil
  :hints (("Goal"
    :use (fc-result-word-0 fc-result-word-1 fc-result-word-2 fc-result-word-3
          fc-result-word-4 fc-result-word-5 fc-result-word-6 fc-result-word-7)
    :in-theory (union-theories (theory 'minimal-theory) '(fn2-digest-list)))))
(defmacro fc-image-digest (kind bytes ctx)
  `(fn2-digest-list 125 (mv-nth 5 (fc-image-drive ,kind ,bytes ,ctx))))
(defthm fc-accepted-covered-hash
  (implies (and (fn2-fc-acceptedp kind bytes ctx) (or (eq kind :frame) (eq kind :seal))
                (fn2-fc-expectedp ctx))
           (and (equal (fn-blake3 (fn2-fc-covered kind bytes ctx))
                       (fn-b3-words-octets (fc-image-digest kind bytes ctx)))
                (fn-b3-word-listp (fc-image-digest kind bytes ctx))))
  :rule-classes nil
  :hints (("Goal" :use (fc-accepted-digest fc-stream-is-covered fc-accepted-trailer-length
                        (:instance fc-blake3-is-answer-octets (m (fn2-fc-covered kind bytes ctx)))
                        (:instance fc-answer-words (len (len bytes)) (ctx (fc-image-context ctx))))
           :in-theory (union-theories (theory 'minimal-theory) '(fc-answer)))))
(defthm fc-same-trailer-same-digest
  (implies (and (fn2-fc-acceptedp kind a ca) (fn2-fc-acceptedp kind b cb) (not (eq kind :page))
                (fn-b3-word-listp (fc-image-digest kind a ca))
                (fn-b3-word-listp (fc-image-digest kind b cb))
                (equal (nthcdr (nfix (- (len a) 32)) a) (nthcdr (nfix (- (len b) 32)) b)))
           (equal (fc-image-digest kind a ca) (fc-image-digest kind b cb)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fc-result-octets-are-trailer (bytes a) (ctx ca) (k 0) (n 32))
                        (:instance fc-result-octets-are-trailer (bytes b) (ctx cb) (k 0) (n 32))
                        (:instance fc-accepted-trailer-length (bytes a) (ctx ca))
                        (:instance fc-accepted-trailer-length (bytes b) (ctx cb))
                        (:instance fc-result-octets-fix-words
                           (da (mv-nth 5 (fc-image-drive kind a ca)))
                           (db (mv-nth 5 (fc-image-drive kind b cb)))))
           :in-theory (union-theories (theory 'minimal-theory)
                         '(nfix natp (:executable-counterpart natp) (:executable-counterpart binary-+)
                           (:executable-counterpart equal) (:type-prescription len)
                           commutativity-of-+ fc-zero-plus-len)))))
(defthm fn2-format-frame-binds-location-proved
  (fn2-format-frame-binds-location$owed bytes a b)
  :rule-classes nil
  :hints (("Goal" :use ((:instance fc-accepted-covered-hash (kind :frame) (ctx a))
                        (:instance fc-accepted-covered-hash (kind :frame) (ctx b))
                        (:instance fc-same-trailer-same-digest (kind :frame) (a bytes) (b bytes) (ca a) (cb b))
                        fc-frame-covered-binds-identity)
           :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-format-frame-binds-location$owed fn2-fc-collision-free-pairp)))))
(fn2-owed-discharge fn2-format-frame-binds-location fn2-format-frame-binds-location-proved)
