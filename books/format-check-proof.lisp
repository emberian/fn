; Format checker binding proofs.
(in-package "ACL2")
(include-book "format-check")
(include-book "owed-discharge")

(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
(local (defun fc-le-induct (width x y)
  (if (zp width) (list x y)
    (fc-le-induct (1- width) (floor x 256) (floor y 256)))))
(local (defun fc-le-fits (width x)
  (if (zp width) (equal x 0)
    (fc-le-fits (1- width) (floor x 256)))))
(local (defthm fc-equal-by-byte-and-quotient
  (implies (and (natp x) (natp y)
                (equal (mod x 256) (mod y 256))
                (equal (floor x 256) (floor y 256)))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable mod)))))
(local (defthm fc-le-prefix-injective
  (implies (and (natp width) (natp x) (natp y)
                (fc-le-fits width x) (fc-le-fits width y))
           (equal (equal (append (fn2-layout-le width x) a)
                         (append (fn2-layout-le width y) b))
                  (and (equal x y) (equal a b))))
  :hints (("Goal" :induct (fc-le-induct width x y)
                  :in-theory (enable fc-le-fits fn2-layout-le nfix))
          ("Subgoal *1/2" :use fc-equal-by-byte-and-quotient))))
(local (defthm fc-le-fits-at-fixed-width
  (implies (syntaxp (quotep width))
           (equal (fc-le-fits width x)
                  (if (zp width) (equal x 0)
                    (fc-le-fits (1- width) (floor x 256)))))
  :hints (("Goal" :expand (fc-le-fits width x)))))
(local (defthm fc-u60-fits-eight
  (implies (unsigned-byte-p 60 x) (fc-le-fits 8 x))
  :hints (("Goal" :in-theory (enable fc-le-fits)))))

(local (defthm fc-append-associative
  (equal (append (append a b) c) (append a (append b c)))))
(local (defthm fc-cancel-common-prefix
  (equal (equal (append p a) (append p b)) (equal a b))))
(local (defthm fc-eight-byte-fields-injective
  (implies (and (unsigned-byte-p 60 x) (unsigned-byte-p 60 y))
           (equal (equal (append (fn2-layout-le 8 x) a)
                         (append (fn2-layout-le 8 y) b))
                  (and (equal x y) (equal a b))))
  :hints (("Goal" :use ((:instance fc-le-prefix-injective (width 8)))
                  :in-theory (disable fc-le-prefix-injective
                                      fc-le-fits-at-fixed-width fn2-layout-le)))))
(local (defthm fc-frame-covered-binds-identity
  (implies (and (fn2-fc-expectedp a) (fn2-fc-expectedp b)
                (equal (fn2-fc-covered :frame bytes a)
                       (fn2-fc-covered :frame bytes b)))
           (equal (fn2-fc-frame-identity a) (fn2-fc-frame-identity b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn2-fc-covered fn2-fc-expectedp fn2-fc-frame-identity
                      fc-append-associative fc-cancel-common-prefix
                      fc-eight-byte-fields-injective))))))
(local (defthm fc-seal-covered-binds-identity
  (implies (and (fn2-fc-expectedp ca) (fn2-fc-expectedp cb)
                (equal (fn2-fc-covered :seal a ca)
                       (fn2-fc-covered :seal b cb)))
           (equal (fn2-fc-seal-identity ca) (fn2-fc-seal-identity cb)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn2-fc-covered fn2-fc-expectedp fn2-fc-seal-identity
                      fc-append-associative fc-cancel-common-prefix
                      fc-eight-byte-fields-injective))))))

(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
(local (defthm fc-u32-reconstruct
  (implies (unsigned-byte-p 32 x)
    (equal (+ (fn2-fc-word-byte x 0) (* 256 (fn2-fc-word-byte x 1))
              (* 65536 (fn2-fc-word-byte x 2)) (* 16777216 (fn2-fc-word-byte x 3)))
           x))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-fc-word-byte ash mod)) ("Goal''" :in-theory (enable floor)))))

; Decode depends on the image and the budget only. This projection follows
; the same resumptions as the driver until the header decoder finishes.
(local (defun-nx fc-decoded-fields (fuel kind len fields pool)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel) fields
    (let ((step (fn2-fc-decode-step kind 0 0 1 0 len 1 0 1 4096 fields pool)))
      (if (eq (car step) :more)
          (fc-decoded-fields (1- fuel) kind len (mv-nth 2 step) pool)
        (mv-nth 2 step))))))
(local (defthm fc-decoded-more-requires-identity
  (implies (not (equal (fn2-fc-identity row kind base len ctx fields) :ok))
           (and (not (equal (car (fn2-fc-decoded row kind off len base next fc ctx b3 fields pool digs)) :more))
                (not (equal (car (fn2-fc-decoded row kind off len base next fc ctx b3 fields pool digs)) :ok))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                       '(fn2-fc-identity fn2-fc-decoded car-cons))))))
(local (defthm fc-mv-nth-zero (equal (mv-nth 0 x) (car x))))
(local (defthm fc-zero-plus-len (implies (natp x) (equal (+ 0 x) x))))
(local (defthm fc-drive-from-decode-binds-header
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
                                               fc ctx b3 fields pool digs))))))
(local (defthm fc-phase-after-decode-start
  (equal (fn2-fc-phase 0 (fn2-fc-set-phase 0 *fn2-fc-phase-decode* fc))
         *fn2-fc-phase-decode*)
  :hints (("Goal" :in-theory (enable fn2-fc-phase fn2-fc-set-phase update-fn2-fc-phase$ai update-nth)))))
(local (defthm fc-read-range-never-yields
  (not (equal (fn2-layout-range-code slot gen off end nil okind oslot ogen pool) :more))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                      '(fn2-layout-range-code fn2-pool-readable-code fn2-pool-handle-code))))))
(local (defthm fc-drive-from-idle-binds-header
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
                          (digs (car (fn2-b3-init 0 0 (fn2-digest-slot 0 *fn2-b3-key*) digs b3)))))))))
(local (defthm fc-header-mismatch-refuses
  (implies (and (natp len) (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-idle*)
                (not (equal (fn2-fc-identity 0 kind 0 len ctx
                               (fc-decoded-fields (1- fuel) kind len
                                                  (fn2-fc-start kind 0 fields) pool)) :ok)))
           (not (equal (car (fn2-format-drive fuel 0 kind nil 0 1 0 len 0 1 0 1 4096
                                              fc ctx b3 fields pool digs)) :ok)))
  :hints (("Goal" :use fc-drive-from-idle-binds-header
                  :in-theory (theory 'minimal-theory)))))
(local (defun-nx fc-image-header (kind bytes)
  (let* ((len (len bytes))
         (pool (fn2-pool-init (list (cons 1 (max 1 len))) 1 100 (create-fn2-pool)))
         (pool (mv-nth 3 (fn2-pool-reserve 0 1 0 1 pool)))
         (pool (fn2-fc-spec-load bytes 0 pool))
         (fields (fn2-fields-init *fn2-format-sealed-batch-num-fields* (create-fn2-fields))))
    (fc-decoded-fields (1- (fn2-format-fuel len)) kind len (fn2-fc-start kind 0 fields) pool))))
(local (defun-nx fc-image-context (context)
  (car (fn2-fc-spec-context context 0
           (fn2-fc-context-init 1 (create-fn2-fc-context))
           (fn2-digests-init 144 (create-fn2-digests))))))
(local (defthm fc-image-initially-idle
  (equal (fn2-fc-phase 0 (fn2-fc-init 1 (create-fn2-fc))) *fn2-fc-phase-idle*)))
(local (defthm fc-length-natural (natp (len bytes))))
(local (defthm fc-accepted-binds-header
  (implies (fn2-fc-acceptedp kind bytes context)
           (equal (fn2-fc-identity 0 kind 0 (len bytes) (fc-image-context context)
                                   (fc-image-header kind bytes)) :ok))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn2-fc-acceptedp fn2-fc-image fn2-fc-image-run
                      fc-image-context fc-image-header fc-mv-nth-zero car-cons cdr-cons
                      fc-header-mismatch-refuses fc-image-initially-idle fc-length-natural))))))

(local (defthm fc-image-context-scalars
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
      fn2-fc-context-location fn2-fc-context-allocation fn2-fc-context-history fn2-fc-context-incarnation fn2-fc-context-writer-epoch fn2-fc-context-commit fn2-fc-context-page-kind fn2-fc-context-encoded-length fn2-fc-context-extent-writer-epoch fn2-fc-context-previous-commit fn2-fc-context-extent fn2-fc-context-hash fn2-fc-context-geometry fn2-fc-context-previous-seal fn2-fc-context-set-location fn2-fc-context-set-allocation fn2-fc-context-set-history fn2-fc-context-set-incarnation fn2-fc-context-set-writer-epoch fn2-fc-context-set-commit fn2-fc-context-set-page-kind fn2-fc-context-set-encoded-length fn2-fc-context-set-extent-writer-epoch fn2-fc-context-set-previous-commit fn2-fc-context-set-extent fn2-fc-context-set-hash fn2-fc-context-set-geometry fn2-fc-context-set-previous-seal update-fn2-fc-context-location$ai update-fn2-fc-context-allocation$ai update-fn2-fc-context-history$ai update-fn2-fc-context-incarnation$ai update-fn2-fc-context-writer-epoch$ai update-fn2-fc-context-commit$ai update-fn2-fc-context-page-kind$ai update-fn2-fc-context-encoded-length$ai update-fn2-fc-context-extent-writer-epoch$ai update-fn2-fc-context-previous-commit$ai update-fn2-fc-context-extent$ai update-fn2-fc-context-hash$ai update-fn2-fc-context-geometry$ai update-fn2-fc-context-previous-seal$ai fn2-fc-context-location$ai fn2-fc-context-allocation$ai fn2-fc-context-history$ai fn2-fc-context-incarnation$ai fn2-fc-context-writer-epoch$ai fn2-fc-context-commit$ai fn2-fc-context-page-kind$ai fn2-fc-context-encoded-length$ai fn2-fc-context-extent-writer-epoch$ai fn2-fc-context-previous-commit$ai fn2-fc-context-extent$ai fn2-fc-context-hash$ai fn2-fc-context-geometry$ai fn2-fc-context-previous-seal$ai))))))
(local (defthm fc-accepted-page-header-unique
  (implies (and (fn2-fc-acceptedp :page bytes a) (fn2-fc-acceptedp :page bytes b))
           (and (equal (fn2-fc-expected-location a) (fn2-fc-expected-location b))
                (equal (fn2-fc-expected-allocation a) (fn2-fc-expected-allocation b))
                (equal (fn2-fc-expected-writer-epoch a) (fn2-fc-expected-writer-epoch b))
                (equal (fn2-fc-expected-page-kind a) (fn2-fc-expected-page-kind b))
                (equal (fn2-fc-expected-encoded-length a) (fn2-fc-expected-encoded-length b))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fc-accepted-binds-header (kind :page) (context a))
                        (:instance fc-accepted-binds-header (kind :page) (context b)))
                  :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn2-fc-identity fc-image-context-scalars))))))

(local (include-book "std/lists/update-nth" :dir :system))
(local (defun-nx fc-expected-digests (ctx ds)
  (mv-nth 1 (fn2-fc-spec-context ctx 0 nil ds))))
(local (defthm fc-mv-second (equal (mv-nth 1 (cons a (cons b rest))) b)))
(local (defthm fc-update-array-commutes
  (implies (and (natp c1) (natp c2) (or (not (equal c1 c2))
               (not (equal (nfix r1) (nfix r2)))))
           (equal (update-nth-array c1 r1 v1 (update-nth-array c2 r2 v2 ds))
                  (update-nth-array c2 r2 v2 (update-nth-array c1 r1 v1 ds))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (update-nth-array nth-update-nth nfix) (nth update-nth))))))
(local (defun-nx fc-workspace-write (c r v ds) (update-nth-array c r v ds)))
(local (defthm fc-workspace-write-commutes
  (implies (and (natp c) (natp col) (natp row) (< (nfix r) *fn2-fc-hash*) (<= *fn2-fc-hash* row))
           (equal (fc-workspace-write c r v (update-nth-array col row w ds))
                  (update-nth-array col row w (fc-workspace-write c r v ds))))
  :hints (("Goal" :use ((:instance fc-update-array-commutes
                            (c1 c) (r1 r) (v1 v) (c2 col) (r2 row) (v2 w)))
                  :in-theory (enable nfix fc-workspace-write)))))
(local (deftheory fc-expected-digest-layout
  '(fc-expected-digests fn2-fc-spec-context fc-mv-second
    (:executable-counterpart fn2-digest-slot) (:executable-counterpart natp)
    (:executable-counterpart <)
    fn2-digests-set-w0 fn2-digests-set-w1 fn2-digests-set-w2 fn2-digests-set-w3 fn2-digests-set-w4 fn2-digests-set-w5 fn2-digests-set-w6 fn2-digests-set-w7
    update-fn2-digests-w0$ai update-fn2-digests-w1$ai update-fn2-digests-w2$ai update-fn2-digests-w3$ai update-fn2-digests-w4$ai update-fn2-digests-w5$ai update-fn2-digests-w6$ai update-fn2-digests-w7$ai)))
(local (defthm fc-workspace-write-expected-digests
  (implies (and (natp c) (< (nfix r) *fn2-fc-hash*))
           (equal (fc-workspace-write c r v (fc-expected-digests ctx ds))
                  (fc-expected-digests ctx (fc-workspace-write c r v ds))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                (cons 'fc-workspace-write-commutes (theory 'fc-expected-digest-layout)))))))
(local (defthm fc-read-expected-digests
  (implies (and (natp c) (< (nfix r) *fn2-fc-hash*))
           (equal (nth r (nth c (fc-expected-digests ctx ds))) (nth r (nth c ds))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                (append '(nfix natp nth-update-nth update-nth-array (:executable-counterpart nfix))
                        (theory 'fc-expected-digest-layout)))))))
(local (defmacro fc-digest-column (getter setter raw-get raw-set column)
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
                                  '(,setter ,raw-set fc-workspace-write (:executable-counterpart natp)))))))))
(local (fc-digest-column fn2-digests-w0 fn2-digests-set-w0 fn2-digests-w0$ai update-fn2-digests-w0$ai *fn2-digests-w0$ai*))
(local (fc-digest-column fn2-digests-w1 fn2-digests-set-w1 fn2-digests-w1$ai update-fn2-digests-w1$ai *fn2-digests-w1$ai*))
(local (fc-digest-column fn2-digests-w2 fn2-digests-set-w2 fn2-digests-w2$ai update-fn2-digests-w2$ai *fn2-digests-w2$ai*))
(local (fc-digest-column fn2-digests-w3 fn2-digests-set-w3 fn2-digests-w3$ai update-fn2-digests-w3$ai *fn2-digests-w3$ai*))
(local (fc-digest-column fn2-digests-w4 fn2-digests-set-w4 fn2-digests-w4$ai update-fn2-digests-w4$ai *fn2-digests-w4$ai*))
(local (fc-digest-column fn2-digests-w5 fn2-digests-set-w5 fn2-digests-w5$ai update-fn2-digests-w5$ai *fn2-digests-w5$ai*))
(local (fc-digest-column fn2-digests-w6 fn2-digests-set-w6 fn2-digests-w6$ai update-fn2-digests-w6$ai *fn2-digests-w6$ai*))
(local (fc-digest-column fn2-digests-w7 fn2-digests-set-w7 fn2-digests-w7$ai update-fn2-digests-w7$ai *fn2-digests-w7$ai*))
(local (defthm fc-mv-cons
  (equal (mv-nth i (cons a b)) (if (zp i) a (mv-nth (1- i) b)))))
(local (defun fc-result (i term single)
  (if single term (if (zp i) (list 'car term) (list 'mv-nth i term)))))
(local (defun fc-overlay-claims (outs i call over single)
  (declare (xargs :verify-guards nil))
  (if (atom outs) nil
    (cons (list 'equal (fc-result i over single)
                (if (eq (car outs) 'fn2-digests)
                    (list 'fc-expected-digests 'ctx (fc-result i call single))
                  (fc-result i call single)))
          (fc-overlay-claims (cdr outs) (1+ i) call over single)))))
(local (defun fc-overlay-event (fn hyps world)
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
                      :in-theory (e/d (,fn min ,@(and rec (list 'posp))) (mv-nth))))))))
(local (defmacro fc-overlay-op (fn &rest hyps)
  `(make-event (value (fc-overlay-event ',fn ',hyps (w state))))))
(local (defthm fc-mv-zero (equal (mv-nth 0 x) (car x))))
(local (defthm fc-nfix-small (implies (< x 120) (< (nfix x) 126))
  :hints (("Goal" :in-theory (enable nfix)))))
(local (defthm fc-nfix-bound
  (implies (and (posp k) (< x k)) (< (nfix x) k))
  :hints (("Goal" :in-theory (enable nfix)))))
(local (defthm fc-nfix-depth-decrease
  (implies (and (posp depth) (< (nfix depth) 54))
           (and (< (nfix (1- depth)) 54) (< (1- depth) 54)))
  :hints (("Goal" :in-theory (enable nfix)))))
(local (defthm fc-nfix-nonpositive
  (implies (<= x 0) (equal (nfix x) 0)) :hints (("Goal" :in-theory (enable nfix)))))
(local (defthm fc-nfix-noninteger
  (implies (not (integerp x)) (equal (nfix x) 0)) :hints (("Goal" :in-theory (enable nfix)))))
(local (deftheory fc-hash-rules
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
      fn2-digests-w7-fc-workspace fn2-digests-set-w7-fc-workspace))))
(local (in-theory (theory 'fc-hash-rules)))
(local (fc-overlay-op fn2-digest-copy (< (nfix dst) 126) (< (nfix src) 126)))
(local (fc-overlay-op fn2-digest-iv (< (nfix dst) 126)))
(local (fc-overlay-op fn2-b3-init (< (nfix key) 126)))
(local (fc-overlay-op fn2-b3-parent-cv (< (nfix dst) 126) (< (nfix left) 126)
                                        (< (nfix right) 126) (< (nfix key) 126)))
(local (fc-overlay-op fn2-b3-parent-root (< (nfix dst) 126) (< (nfix left) 126)
                                          (< (nfix right) 126) (< (nfix key) 126)))
(local (fc-overlay-op fn2-b3-parent (< (nfix dst) 126) (< (nfix right) 126) (< level 54)))
(local (fc-overlay-op fn2-b3-output (< (nfix dst) 126)))
(local (fc-overlay-op fn2-b3-push (< (nfix src) 126) (< (nfix depth) 54)))
(local (fc-overlay-op fn2-b3-flush))
(local (fc-overlay-op fn2-b3-byte))
(local (fc-overlay-op fn2-b3-subtree-cv-into (< (nfix dst) 126)))
(local (fc-overlay-op fn2-b3-chunk-output-into))
(local (fc-overlay-op fn2-b3-bulk))
(local (fc-overlay-op fn2-b3-span))
(local (fc-overlay-op fn2-b3-feed))
(local (fc-overlay-op fn2-b3-fragment-into))
(local (fc-overlay-op fn2-b3-update))
(local (fc-overlay-op fn2-b3-fold (< (nfix dst) 126) (<= depth 54)))
(local (fc-overlay-op fn2-b3-finish (< (nfix dst) 126)))
(local (fc-overlay-op fn2-b3-finalize (< (nfix dst) 126)))

(local (in-theory (current-theory :here)))
(local (defun-nx fc-linked-digests (a b da db)
  (and (equal (fc-expected-digests a da) da)
       (equal (fc-expected-digests b da) db))))
(local (defun fc-same-outputs (indices a-call b-call)
  (declare (xargs :verify-guards nil))
  (if (atom indices) nil
    (cons (list 'equal (fc-result (car indices) b-call nil)
                       (fc-result (car indices) a-call nil))
          (fc-same-outputs (cdr indices) a-call b-call)))))
(local (defmacro fc-linked-op (fn din dout &rest hyps)
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
                       :in-theory (union-theories (theory 'minimal-theory) '(fc-linked-digests (:executable-counterpart nfix) (:executable-counterpart <)))))))))
(local (fc-linked-op fn2-b3-byte (fn2-b3-byte 0 byte fn2-digests b3) 0))
(local (fc-linked-op fn2-b3-finalize (fn2-b3-finalize 125 0 fn2-digests b3) :single))
(local (fc-linked-op fn2-b3-init (fn2-b3-init 0 0 1 fn2-digests b3) 0))
(local (fc-linked-op fn2-b3-update (fn2-b3-update 0 slot gen off len okind oslot ogen fn2-digests b3 pool) 2))

(local (defun fc-hash-word (i ctx)
  (declare (xargs :verify-guards nil))
  (case i
    (0 (fn2-fc-expected-hash-0 ctx))    (1 (fn2-fc-expected-hash-1 ctx))    (2 (fn2-fc-expected-hash-2 ctx))    (3 (fn2-fc-expected-hash-3 ctx))    (4 (fn2-fc-expected-hash-4 ctx))    (5 (fn2-fc-expected-hash-5 ctx))    (6 (fn2-fc-expected-hash-6 ctx))    (otherwise (fn2-fc-expected-hash-7 ctx)))))
(local (defun fc-hash-byte (k ctx)
  (declare (xargs :verify-guards nil))
  (fn2-fc-word-byte (fc-hash-word (floor k 4) ctx) (mod k 4))))
(local (defthm fc-expected-word-installed
  (equal (fn2-digest-word 126 i (fc-expected-digests ctx ds)) (fc-hash-word i ctx))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             (append '(fc-hash-word fn2-digest-word nth-update-nth update-nth-array
                       (:executable-counterpart nfix) fn2-digests-w0 fn2-digests-w1 fn2-digests-w2 fn2-digests-w3 fn2-digests-w4 fn2-digests-w5 fn2-digests-w6 fn2-digests-w7 fn2-digests-w0$ai fn2-digests-w1$ai fn2-digests-w2$ai fn2-digests-w3$ai fn2-digests-w4$ai fn2-digests-w5$ai fn2-digests-w6$ai fn2-digests-w7$ai)
                     (theory 'fc-expected-digest-layout)))))))
(local (defthm fc-result-byte-independent
  (equal (fn2-fc-digest-byte 0 k fc (fc-expected-digests ctx ds))
         (fn2-fc-digest-byte 0 k fc ds))
  :hints (("Goal" :in-theory (enable fn2-fc-digest-byte fn2-digest-word)))))
(local (defthm fc-linked-result-byte
  (implies (fc-linked-digests a b da db)
           (equal (fn2-fc-digest-byte 0 k fc db) (fn2-fc-digest-byte 0 k fc da)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fc-linked-digests fc-result-byte-independent))))))
(local (defthm fc-linked-expected-bytes
  (implies (fc-linked-digests a b da db)
           (and (equal (fn2-fc-word-byte (fn2-fc-context-hash-word 0 (floor k 4)
                                               (fc-image-context a) da) (mod k 4))
                       (fc-hash-byte k a))
                (equal (fn2-fc-word-byte (fn2-fc-context-hash-word 0 (floor k 4)
                                               (fc-image-context b) db) (mod k 4))
                       (fc-hash-byte k b))))
  :hints (("Goal" :use ((:instance fc-expected-word-installed (ctx a) (ds da) (i (floor k 4)))
                        (:instance fc-expected-word-installed (ctx b) (ds da) (i (floor k 4))))
                  :in-theory (union-theories (theory 'minimal-theory)
                            '(fc-hash-byte fc-linked-digests fn2-fc-context-hash-word
                              fc-image-context-scalars (:executable-counterpart fn2-digest-slot)))))))

(local (defun-nx fc-byte-pending (k fc)
  (or (not (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-digest*))
      (and (natp (fn2-fc-pos 0 fc)) (<= (fn2-fc-pos 0 fc) k)))))
(local (defun fc-live (code) (or (eq code :more) (eq code :yield) (eq code :ok))))
(local (defthm fc-phase-pos-updates
  (and (equal (fn2-fc-phase 0 (fn2-fc-set-phase 0 phase fc)) phase)
       (equal (fn2-fc-phase 0 (fn2-fc-set-pos 0 pos fc)) (fn2-fc-phase 0 fc))
       (equal (fn2-fc-pos 0 (fn2-fc-set-pos 0 pos fc)) pos)
       (equal (fn2-fc-pos 0 (fn2-fc-set-phase 0 phase fc)) (fn2-fc-pos 0 fc)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                     '(fn2-fc-phase fn2-fc-pos fn2-fc-set-pos fn2-fc-set-phase
                       fn2-fc-pos$ai fn2-fc-phase$ai update-fn2-fc-phase$ai
                       update-fn2-fc-pos$ai update-nth-array nth-update-nth
                       (:executable-counterpart nfix)))))))
(local (defthm fc-page-prefix-is-domain
  (implies (< pos (+ (length (fn2-fc-domain :page)) 0))
           (equal (fn2-fc-prefix-byte 0 :page pos ctx)
                  (char-code (char (fn2-fc-domain :page) pos))))
  :hints (("Goal" :in-theory (enable fn2-fc-prefix-byte length fn2-fc-domain)))))
(local (defthm fc-page-check-byte-independent
  (equal (fn2-fc-check-byte 0 :page off pos byte fc ctx ds)
         (if (and (<= (fn2-fc-pad 0 fc) pos) (< pos (fn2-fc-pad-end 0 fc))
                  (not (equal byte 0))) :nonzero-padding :ok))
  :hints (("Goal" :in-theory (enable fn2-fc-check-byte)))))
(local (defthm fc-pending-after-increment
  (implies (and (natp pos) (natp k) (<= pos k) (not (equal pos k)))
           (and (natp (+ 1 pos)) (<= (+ 1 pos) k)))
  :hints (("Goal" :in-theory (enable natp)))))
(local (defmacro fc-pair-hyps ()
  '(and (natp k) (< k 32) (not (equal (fc-hash-byte k a) (fc-hash-byte k b)))
        (fc-byte-pending k fc) (fc-linked-digests a b da db))))
(local (defun fc-pair-goal (call sig)
  (declare (xargs :verify-guards nil))
  (let* ((al (sublis '((ctx . (fc-image-context a)) (ds . da)) call))
         (bl (sublis '((ctx . (fc-image-context b)) (ds . db)) call))
         (fc-idx (position-eq 'fc sig))
         (ds-idx (position-eq 'ds sig))
         (same (remove ds-idx (take (len sig) '(0 1 2 3 4 5 6)))))
    `(implies (and (fc-pair-hyps) (fc-live (car ,al)) (fc-live (car ,bl)))
              (and (not (equal (car ,al) :ok))
                   ,@(fc-same-outputs same al bl)
                   (fc-byte-pending k ,(fc-result fc-idx al nil))
                   (fc-linked-digests a b ,(fc-result ds-idx al nil) ,(fc-result ds-idx bl nil)))))))
(local (defmacro fc-pair-thm (name call sig &rest hints)
  `(defthm ,name ,(fc-pair-goal call sig) :rule-classes nil :hints ,hints)))
(local (fc-pair-thm fc-page-byte-pair
  (fn2-fc-byte 0 :page nil slot gen off len base okind oslot ogen fc ctx b3 fields pool ds)
  (code fc b3 pool ds)
  ("Goal" :do-not '(preprocess)
          :in-theory (e/d (fn2-fc-byte fc-live fc-byte-pending
                            (:executable-counterpart natp) natp
                            fc-phase-pos-updates fc-page-prefix-is-domain
                            fc-pending-after-increment fc-linked-result-byte fc-linked-expected-bytes
                            fn2-b3-finalize-fc-linked fn2-b3-byte-fc-linked fc-page-check-byte-independent)
                          (mv-nth fc-hash-word fc-hash-byte fc-linked-digests
                           fn2-fc-phase fn2-fc-pos fc-image-context)))))

(local (defmacro fc-span-call (ctx ds)
  `(fn2-fc-page-span fuel 0 slot gen off len base okind oslot ogen
                     fc ,ctx b3 fields pool ,ds)))
(local (defthm fc-page-span-pair
  (implies (fc-linked-digests a b da db)
    (let ((x (fc-span-call (fc-image-context a) da))
          (y (fc-span-call (fc-image-context b) db)))
      (and (not (equal (car x) :ok))
           (equal (car y) (car x))
           (equal (mv-nth 1 y) (mv-nth 1 x))
           (equal (mv-nth 2 y) (mv-nth 2 x))
           (equal (mv-nth 3 y) (mv-nth 3 x))
           (equal (fn2-fc-phase 0 (mv-nth 2 x)) (fn2-fc-phase 0 fc))
           (fc-linked-digests a b (mv-nth 4 x) (mv-nth 4 y)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
                  :in-theory (e/d (fn2-fc-page-span fc-phase-pos-updates fn2-b3-update-fc-linked)
                                  (mv-nth fc-linked-digests fc-image-context fn2-fc-phase fc-byte-pending))))))
(local (defthm fc-span-pending
  (implies (and (fc-linked-digests a b da db)
                (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-hash*))
           (fc-byte-pending k (mv-nth 2 (fc-span-call (fc-image-context a) da))))
  :hints (("Goal" :use fc-page-span-pair :in-theory (enable fc-byte-pending)))))
(local (fc-pair-thm fc-page-advance-pair
  (fn2-fc-advance fuel 0 :page nil slot gen off len base okind oslot ogen fc ctx b3 fields pool ds)
  (code used fc b3 pool ds)
  ("Goal" :do-not '(preprocess)
          :use (fc-page-byte-pair fc-page-span-pair
                (:instance fc-page-byte-pair
                  (fc (mv-nth 2 (fc-span-call (fc-image-context a) da)))
                  (b3 (mv-nth 3 (fc-span-call (fc-image-context a) da)))
                  (da (mv-nth 4 (fc-span-call (fc-image-context a) da)))
                  (db (mv-nth 4 (fc-span-call (fc-image-context b) db)))))
          :in-theory (e/d (fn2-fc-advance (:executable-counterpart fc-live) fc-span-pending (:executable-counterpart member-equal))
                          (mv-nth fc-live fc-byte-pending fc-linked-digests fc-image-context fc-hash-byte)))))
(local (defmacro fc-advance-call (fuel ctx ds)
  `(fn2-fc-advance ,fuel 0 :page nil slot gen off len base okind oslot ogen fc
                   (fc-image-context ,ctx) b3 fields pool ,ds)))
(local (defmacro fc-bytes-call (fuel ctx ds)
  `(fn2-fc-run-bytes ,fuel 0 :page nil slot gen off len base okind oslot ogen fc
                     (fc-image-context ,ctx) b3 fields pool ,ds)))
(local (defun-nx fc-page-run-induct (fuel slot gen off len base okind oslot ogen
                                      fc a b b3 fields pool da db)
  (declare (xargs :measure (nfix fuel) :hints (("Goal" :in-theory (union-theories (current-theory 'fn2-fc-acceptedp) '(nfix posp zp))))))
  (if (zp fuel) nil
    (let* ((x (fc-advance-call fuel a da)) (y (fc-advance-call fuel b db))
           (used (mv-nth 1 x)))
      (if (and (equal (car x) :more) (posp used) (<= used fuel))
          (fc-page-run-induct (- fuel used) slot gen off len base okind oslot ogen
                              (mv-nth 2 x) a b (mv-nth 3 x) fields (mv-nth 4 x)
                              (mv-nth 5 x) (mv-nth 5 y))
        nil)))))
(local (defthm fc-run-live-enters-live
  (implies (and (not (zp fuel)) (fc-live (car (fc-bytes-call fuel a da))))
           (fc-live (car (fc-advance-call fuel a da))))
  :hints (("Goal" :expand (fc-bytes-call fuel a da)
                  :in-theory (e/d (fc-live) (mv-nth fc-image-context))))))
(local (fc-pair-thm fc-page-run-pair
  (fn2-fc-run-bytes fuel 0 :page nil slot gen off len base okind oslot ogen fc ctx b3 fields pool ds)
  (code fc b3 pool ds)
  ("Goal" :induct (fc-page-run-induct fuel slot gen off len base okind oslot ogen
                                      fc a b b3 fields pool da db)
          :expand ((fc-bytes-call fuel a da) (fc-bytes-call fuel b db))
          :in-theory (e/d ((:executable-counterpart fc-live))
                          (mv-nth fc-image-context fc-byte-pending fc-live fc-linked-digests fc-hash-byte)))
  ("Subgoal *1/3" :use (fc-page-advance-pair fc-run-live-enters-live
                       (:instance fc-run-live-enters-live (a b) (da db))))
  ("Subgoal *1/2" :use (fc-page-advance-pair fc-run-live-enters-live
                       (:instance fc-run-live-enters-live (a b) (da db))))))

(local (defthm fc-page-identity-live
  (equal (fc-live (fn2-fc-identity 0 :page base len ctx fields))
         (equal (fn2-fc-identity 0 :page base len ctx fields) :ok))
  :hints (("Goal" :in-theory (e/d (fn2-fc-identity fc-live) (mv-nth))))))
(local (defthm fc-page-decoded-pair
  (let ((x (fn2-fc-decoded 0 :page off len base next fc ca b3 fields pool da))
        (y (fn2-fc-decoded 0 :page off len base next fc cb b3 fields pool db)))
    (implies (and (fc-live (car x)) (fc-live (car y)))
             (and (equal (car x) :more) (equal (car y) :more)
                  (equal (mv-nth 1 y) (mv-nth 1 x))
                  (fc-byte-pending k (mv-nth 1 x)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-fc-decoded fc-byte-pending fc-page-identity-live
                                   (:executable-counterpart fc-live)
                                   fc-phase-pos-updates)
                                  (mv-nth fc-live fn2-fc-identity))))))
(local (defthm fc-start-pending
  (fc-byte-pending k (fn2-fc-set-phase 0 *fn2-fc-phase-decode* fc))
  :hints (("Goal" :in-theory (enable fc-byte-pending fc-phase-pos-updates)))))
(local (defthm fc-page-step-pair
  (let ((x (fn2-fc-step 0 :page nil slot gen off len base okind oslot ogen budget
                        fc (fc-image-context a) b3 fields pool da))
        (y (fn2-fc-step 0 :page nil slot gen off len base okind oslot ogen budget
                        fc (fc-image-context b) b3 fields pool db)))
    (implies (and (fc-pair-hyps) (fc-live (car x)) (fc-live (car y)))
             (and (not (equal (car x) :ok)) (equal (car y) (car x))
                  (equal (mv-nth 1 y) (mv-nth 1 x))
                  (equal (mv-nth 2 y) (mv-nth 2 x))
                  (equal (mv-nth 3 y) (mv-nth 3 x))
                  (equal (mv-nth 4 y) (mv-nth 4 x))
                  (fc-byte-pending k (mv-nth 1 x))
                  (fc-linked-digests a b (mv-nth 5 x) (mv-nth 5 y)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
          :use ((:instance fc-page-run-pair (fuel budget))
                (:instance fc-page-decoded-pair (ca (fc-image-context a)) (cb (fc-image-context b))
                 (next (mv-nth 1 (fn2-fc-decode-step :page base slot gen off (+ off len)
                                                     okind oslot ogen budget fields pool)))
                 (fields (mv-nth 2 (fn2-fc-decode-step :page base slot gen off (+ off len)
                                                       okind oslot ogen budget fields pool)))))
          :in-theory (e/d (fn2-fc-step (:executable-counterpart member-equal)
                           (:executable-counterpart fc-live) fc-start-pending fc-phase-pos-updates
                           fn2-b3-init-fc-linked)
                          (mv-nth fc-byte-pending fc-hash-byte fc-live fc-linked-digests fc-image-context))))))
(local (defthm fc-reset-pending
  (fc-byte-pending k (fn2-fc-reset 0 fc))
  :hints (("Goal" :in-theory (enable fn2-fc-reset fc-byte-pending fc-phase-pos-updates)))))
(local (fc-pair-thm fc-page-format-run-pair
  (fn2-format-run :page nil 0 slot gen off len base okind oslot ogen budget fc ctx b3 fields pool ds)
  (code fc b3 fields pool ds)
  ("Goal" :use fc-page-step-pair :in-theory (e/d (fn2-format-run fc-reset-pending)
                (mv-nth fc-hash-byte fc-live fc-linked-digests fc-byte-pending fc-image-context)))))
(local (defmacro fc-run-call (context digests)
  `(fn2-format-run :page nil 0 slot gen off len base okind oslot ogen budget
                   fc (fc-image-context ,context) b3 fields pool ,digests)))
(local (defmacro fc-drive-call (context digests)
  `(fn2-format-drive fuel 0 :page nil slot gen off len base okind oslot ogen budget
                     fc (fc-image-context ,context) b3 fields pool ,digests)))
(local (defun-nx fc-drive-induct (fuel slot gen off len base okind oslot ogen budget
                                  fc a b b3 fields pool da db)
  (declare (xargs :measure (nfix fuel)
                  :hints (("Goal" :in-theory (union-theories (current-theory 'fn2-fc-acceptedp)
                                                            '(nfix zp))))))
  (if (zp fuel) nil
    (let ((x (fc-run-call a da)) (y (fc-run-call b db)))
      (if (eq (car x) :more)
          (fc-drive-induct (1- fuel) slot gen off len base okind oslot ogen budget
                           (mv-nth 1 x) a b (mv-nth 2 x) (mv-nth 3 x) (mv-nth 4 x)
                           (mv-nth 5 x) (mv-nth 5 y))
        nil)))))
(local (defthm fc-drive-ok-enters-live
  (implies (equal (car (fc-drive-call a da)) :ok) (fc-live (car (fc-run-call a da))))
  :hints (("Goal" :expand (fc-drive-call a da)
                  :in-theory (e/d (fc-live) (mv-nth fc-image-context))))))
(local (defthm fc-drive-rejects-hash-disagreement
  (implies (and (fc-pair-hyps) (equal (car (fc-drive-call a da)) :ok))
           (not (equal (car (fc-drive-call b db)) :ok)))
  :rule-classes nil
  :hints (("Goal" :induct (fc-drive-induct fuel slot gen off len base okind oslot ogen budget
                                           fc a b b3 fields pool da db)
                  :expand ((fc-drive-call a da) (fc-drive-call b db))
                  :in-theory (e/d ((:executable-counterpart fc-live))
                                  (mv-nth fc-hash-byte fc-live fc-linked-digests
                                          fc-byte-pending fc-image-context)))
          ("Subgoal *1/3" :use (fc-page-format-run-pair fc-drive-ok-enters-live
                              (:instance fc-drive-ok-enters-live (a b) (da db))))
          ("Subgoal *1/2" :use (fc-page-format-run-pair fc-drive-ok-enters-live
                              (:instance fc-drive-ok-enters-live (a b) (da db)))))))

(local (defthm fc-expected-digests-overwrite
  (equal (fc-expected-digests b (fc-expected-digests a ds))
         (fc-expected-digests b ds))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                  (append '(update-nth-array nth-update-nth update-nth-of-update-nth-same
                            update-nth-of-update-nth-diff (:executable-counterpart nfix))
                          (theory 'fc-expected-digest-layout)))))))
(local (defthm fc-fresh-digests-linked
  (fc-linked-digests a b (fc-expected-digests a ds) (fc-expected-digests b ds))
  :hints (("Goal" :in-theory (enable fc-linked-digests fc-expected-digests-overwrite)))))
(local (defthm fc-adapter-digests
  (equal (mv-nth 1 (fn2-fc-spec-context ctx 0 carrier ds)) (fc-expected-digests ctx ds))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                   '(fn2-fc-spec-context fc-mv-second fc-expected-digests))))))
(local (defthm fc-adapter-context
  (equal (car (fn2-fc-spec-context ctx 0 (fn2-fc-context-init 1 (create-fn2-fc-context))
                                   (fn2-digests-init 144 (create-fn2-digests))))
         (fc-image-context ctx))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fc-image-context))))))
(local (defthm fc-fresh-pending
  (fc-byte-pending k (fn2-fc-init 1 (create-fn2-fc)))
  :hints (("Goal" :in-theory (enable fc-byte-pending fc-image-initially-idle)))))
(local (defthm fc-accepted-page-hash-byte-unique
  (implies (and (fn2-fc-acceptedp :page bytes a) (fn2-fc-acceptedp :page bytes b)
                (natp k) (< k 32))
           (equal (fc-hash-byte k a) (fc-hash-byte k b)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fc-drive-rejects-hash-disagreement
                 (fuel (fn2-format-fuel (len bytes))) (slot 0) (gen 1) (off 0)
                 (len (len bytes)) (base 0) (okind 1) (oslot 0) (ogen 1) (budget 4096)
                 (fc (fn2-fc-init 1 (create-fn2-fc)))
                 (b3 (fn2-b3-table-init 1 (create-fn2-b3)))
                 (fields (fn2-fields-init *fn2-format-sealed-batch-num-fields* (create-fn2-fields)))
                 (pool (fn2-fc-spec-load bytes 0
                      (mv-nth 3 (fn2-pool-reserve 0 1 0 1
                         (fn2-pool-init (list (cons 1 (max 1 (len bytes)))) 1 100 (create-fn2-pool))))))
                 (da (fc-expected-digests a (fn2-digests-init 144 (create-fn2-digests))))
                 (db (fc-expected-digests b (fn2-digests-init 144 (create-fn2-digests)))) ))
          :in-theory (union-theories (theory 'minimal-theory)
                     '(fn2-fc-acceptedp fn2-fc-image fn2-fc-image-run
                       fc-mv-zero fc-mv-cons car-cons (:executable-counterpart zp)
                       fc-fresh-pending fc-fresh-digests-linked fc-adapter-context fc-adapter-digests))))))

(local (defthm fc-u32-bytes-unique
  (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y)
                (equal (fn2-fc-word-byte x 0) (fn2-fc-word-byte y 0))
                (equal (fn2-fc-word-byte x 1) (fn2-fc-word-byte y 1))
                (equal (fn2-fc-word-byte x 2) (fn2-fc-word-byte y 2))
                (equal (fn2-fc-word-byte x 3) (fn2-fc-word-byte y 3)))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :use (fc-u32-reconstruct (:instance fc-u32-reconstruct (x y)))
                  :in-theory (theory 'minimal-theory)))))
(local (defmacro fc-accepted-word (i)
  (let ((name (packn-pos (list 'fc-accepted-hash-word- i) 'fc-hash-word)))
    `(defthm ,name
       (implies (and (fn2-fc-expectedp a) (fn2-fc-expectedp b)
                     (fn2-fc-acceptedp :page bytes a) (fn2-fc-acceptedp :page bytes b))
                (equal (fc-hash-word ,i a) (fc-hash-word ,i b)))
       :rule-classes nil
       :hints (("Goal" :use ((:instance fc-u32-bytes-unique
                                (x (fc-hash-word ,i a)) (y (fc-hash-word ,i b)))
                             (:instance fc-accepted-page-hash-byte-unique (k ,(* 4 i)))
                             (:instance fc-accepted-page-hash-byte-unique (k ,(+ 1 (* 4 i))))
                             (:instance fc-accepted-page-hash-byte-unique (k ,(+ 2 (* 4 i))))
                             (:instance fc-accepted-page-hash-byte-unique (k ,(+ 3 (* 4 i)))))
                       :in-theory (union-theories (theory 'minimal-theory)
                                  '(fn2-fc-expectedp fc-hash-byte fc-hash-word
                                    (:executable-counterpart floor) (:executable-counterpart mod)
                                    (:executable-counterpart natp)))))))))
(local (fc-accepted-word 0))
(local (fc-accepted-word 1))
(local (fc-accepted-word 2))
(local (fc-accepted-word 3))
(local (fc-accepted-word 4))
(local (fc-accepted-word 5))
(local (fc-accepted-word 6))
(local (fc-accepted-word 7))

(defthm fn2-format-page-binds-parent-proved
  (fn2-format-page-binds-parent$owed bytes a b)
  :rule-classes nil
  :hints (("Goal" :use (fc-accepted-page-header-unique
                        fc-accepted-hash-word-0 fc-accepted-hash-word-1
                        fc-accepted-hash-word-2 fc-accepted-hash-word-3
                        fc-accepted-hash-word-4 fc-accepted-hash-word-5
                        fc-accepted-hash-word-6 fc-accepted-hash-word-7)
                  :in-theory (union-theories (theory 'minimal-theory)
                             '(fn2-format-page-binds-parent$owed fn2-fc-parent-identity fc-hash-word)))))
(fn2-owed-discharge fn2-format-page-binds-parent fn2-format-page-binds-parent-proved)

; During digest verification all positions below the cursor have matched.
; State the invariant for an arbitrary index to avoid rescanning the prefix.
(local (defmacro fc-check-input (i)
  `(fn2-b3-read slot gen (+ off (- len 32) ,i) okind oslot ogen pool)))
(local (defun-nx fc-digest-match (k slot gen off len okind oslot ogen pool ds)
  (let ((input (fc-check-input k)))
    (and (eq (car input) :ok)
         (equal (mv-nth 1 input) (fn2-fc-digest-byte 0 k nil ds))))))
(local (defun-nx fc-digest-progress (k slot gen off len okind oslot ogen fc pool ds)
  (let ((phase (fn2-fc-phase 0 fc)) (pos (fn2-fc-pos 0 fc)))
    (and (implies (or (equal phase *fn2-fc-phase-prefix*)
                      (equal phase *fn2-fc-phase-hash*)
                      (equal phase *fn2-fc-phase-digest*))
                  (equal (fn2-fc-zero 0 fc) (- len 32)))
         (implies (equal phase *fn2-fc-phase-digest*)
                  (and (natp pos)
                       (or (<= pos k)
                           (fc-digest-match k slot gen off len okind oslot ogen pool ds))))))))
(local (defthm fc-zero-updates
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
               update-nth-array nth-update-nth (:executable-counterpart nfix)))))))
(local (defmacro fc-progress-at (cursor data digests)
  `(fc-digest-progress k slot gen off len okind oslot ogen ,cursor ,data ,digests)))
(local (defmacro fc-match-at (data digests)
  `(fc-digest-match k slot gen off len okind oslot ogen ,data ,digests)))
(local (defmacro fc-digest-step-claim (call fc-index pool-index ds-index)
  `(let ((step ,call))
     (implies (and (not (eq kind :page)) (natp k) (< k 32)
                   (fc-progress-at fc pool ds))
              (and (implies (eq (car step) :ok)
                            (fc-match-at (mv-nth ,pool-index step) (mv-nth ,ds-index step)))
                   (implies (or (eq (car step) :more) (eq (car step) :yield))
                            (fc-progress-at (mv-nth ,fc-index step)
                                            (mv-nth ,pool-index step) (mv-nth ,ds-index step))))))))
(local (defthm fc-byte-verifies-trailer
  (fc-digest-step-claim
    (fn2-fc-byte 0 kind nil slot gen off len base okind oslot ogen fc ctx b3 fields pool ds) 1 3 4)
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
          :in-theory (e/d (fn2-fc-byte fc-digest-progress fc-digest-match fc-phase-pos-updates
                           fc-zero-updates fn2-fc-digest-byte fc-pending-after-increment
                           (:executable-counterpart natp) natp)
                          (mv-nth))))))

(local (defthm fc-span-keeps-cursor-layout
  (let ((step (fn2-fc-page-span fuel 0 slot gen off end base okind oslot ogen
                                fc ctx b3 fields pool ds)))
    (and (not (eq (car step) :ok))
         (equal (fn2-fc-zero 0 (mv-nth 2 step)) (fn2-fc-zero 0 fc))
         (equal (fn2-fc-phase 0 (mv-nth 2 step)) (fn2-fc-phase 0 fc))))
  :hints (("Goal" :do-not '(preprocess)
                  :in-theory (e/d (fn2-fc-page-span fc-zero-updates fc-phase-pos-updates)
                                  (mv-nth fn2-fc-zero fn2-fc-phase))))))
(local (defthm fc-hashing-progress
  (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-hash*)
           (equal (fc-progress-at fc pool ds)
                  (equal (fn2-fc-zero 0 fc) (- len 32))))
  :hints (("Goal" :in-theory (enable fc-digest-progress)))))
(local (defmacro fc-advance-trailer ()
  '(fn2-fc-advance fuel 0 kind nil slot gen off len base okind oslot ogen
                   fc ctx b3 fields pool ds)))
(local (defthm fc-advance-verifies-trailer
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
                     (mv-nth fc-digest-match fc-digest-progress))))))
(local (defmacro fc-run-trailer ()
  '(fn2-fc-run-bytes fuel 0 kind nil slot gen off len base okind oslot ogen
                     fc ctx b3 fields pool ds)))
(local (defthm fc-run-verifies-trailer
  (fc-digest-step-claim (fc-run-trailer) 1 3 4)
  :rule-classes nil
  :hints (("Goal" :induct (fc-run-trailer) :expand (fc-run-trailer)
                  :in-theory (e/d ((:induction fn2-fc-run-bytes))
                                  (mv-nth fc-digest-progress fc-digest-match)))
          ("Subgoal *1/3" :use fc-advance-verifies-trailer)
          ("Subgoal *1/2" :use fc-advance-verifies-trailer))))
(local (defthm fc-identity-never-more
  (not (equal (fn2-fc-identity row kind base len ctx fields) :more))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn2-fc-identity))))))
(local (defthm fc-decoded-starts-trailer
  (let ((step (fn2-fc-decoded 0 kind off len base next fc ctx b3 fields pool ds)))
    (implies (not (eq kind :page))
             (and (not (eq (car step) :ok))
                  (implies (eq (car step) :more)
                           (fc-progress-at (mv-nth 1 step) pool ds)))))
  :hints (("Goal" :in-theory (e/d (fn2-fc-decoded fc-digest-progress fc-phase-pos-updates
                                   fc-zero-updates fc-identity-never-more)
                                  (mv-nth fn2-fc-phase fn2-fc-zero))))))
(local (defthm fc-start-progress
  (fc-progress-at (fn2-fc-set-phase 0 *fn2-fc-phase-decode* fc) pool ds)
  :hints (("Goal" :in-theory (enable fc-phase-pos-updates fc-digest-progress)))))
(local (defthm fc-decoded-never-yields
  (not (equal (car (fn2-fc-decoded 0 kind off len base next fc ctx b3 fields pool ds)) :yield))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                            '(fn2-fc-decoded fn2-fc-identity car-cons))))))
(local (defmacro fc-step-trailer ()
  '(fn2-fc-step 0 kind nil slot gen off len base okind oslot ogen budget
                fc ctx b3 fields pool ds)))
(local (defthm fc-step-verifies-trailer
  (fc-digest-step-claim (fc-step-trailer) 1 4 5)
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :use ((:instance fc-run-verifies-trailer (fuel budget))
                       (:instance fc-decoded-starts-trailer
                        (next (mv-nth 1 (fn2-fc-decode-step kind base slot gen off (+ off len)
                                                    okind oslot ogen budget fields pool)))
                        (fields (mv-nth 2 (fn2-fc-decode-step kind base slot gen off (+ off len)
                                                    okind oslot ogen budget fields pool)))))
                  :in-theory (e/d (fn2-fc-step fc-start-progress fc-decoded-never-yields)
                                  (mv-nth fc-digest-progress fc-digest-match))))))
(local (defmacro fc-format-trailer ()
  '(fn2-format-run kind nil 0 slot gen off len base okind oslot ogen budget
                   fc ctx b3 fields pool ds)))
(local (defthm fc-reset-progress
  (fc-progress-at (fn2-fc-reset 0 fc) pool ds)
  :hints (("Goal" :in-theory (enable fn2-fc-reset fc-phase-pos-updates fc-digest-progress)))))
(local (defthm fc-format-verifies-trailer
  (fc-digest-step-claim (fc-format-trailer) 1 4 5)
  :rule-classes nil
  :hints (("Goal" :use fc-step-verifies-trailer
                  :in-theory (e/d (fn2-format-run fc-reset-progress)
                                  (mv-nth fc-digest-progress fc-digest-match))))))
(local (defmacro fc-drive-trailer ()
  '(fn2-format-drive fuel 0 kind nil slot gen off len base okind oslot ogen budget
                     fc ctx b3 fields pool ds)))
(local (defthm fc-drive-verifies-trailer
  (let ((step (fc-drive-trailer)))
    (implies (and (not (eq kind :page)) (natp k) (< k 32)
                  (fc-progress-at fc pool ds) (eq (car step) :ok))
             (fc-match-at (mv-nth 4 step) (mv-nth 5 step))))
  :rule-classes nil
  :hints (("Goal" :induct (fc-drive-trailer) :expand (fc-drive-trailer)
                  :in-theory (e/d ((:induction fn2-format-drive))
                                  (mv-nth fc-digest-progress fc-digest-match)))
          ("Subgoal *1/3" :use fc-format-verifies-trailer)
          ("Subgoal *1/2" :use fc-format-verifies-trailer))))

(local (defmacro fc-reservation (bytes)
  `(fn2-pool-reserve 0 1 0 1
      (fn2-pool-init (list (cons 1 (max 1 (len ,bytes)))) 1 100 (create-fn2-pool)))))
(local (defun-nx fc-image-pool (bytes)
  (fn2-fc-spec-load bytes 0 (mv-nth 3 (fc-reservation bytes)))))
(local (defun-nx fc-image-drive (kind bytes ctx)
  (fn2-format-drive (fn2-format-fuel (len bytes)) 0 kind nil 0 1 0 (len bytes) 0 1 0 1 4096
    (fn2-fc-init 1 (create-fn2-fc)) (fc-image-context ctx)
    (fn2-b3-table-init 1 (create-fn2-b3))
    (fn2-fields-init *fn2-format-sealed-batch-num-fields* (create-fn2-fields))
    (fc-image-pool bytes) (fc-expected-digests ctx (fn2-digests-init 144 (create-fn2-digests))))))
(local (defthm fc-accepted-drive-ok
  (implies (fn2-fc-acceptedp kind bytes ctx) (equal (car (fc-image-drive kind bytes ctx)) :ok))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
        '(fn2-fc-acceptedp fn2-fc-image fn2-fc-image-run fc-image-drive fc-image-pool
          fc-adapter-context fc-adapter-digests fc-mv-zero fc-mv-cons
          (:executable-counterpart zp) car-cons))))))
(local (defmacro fc-read-only (name call index &optional recursive)
  `(defthm ,name
     (equal (mv-nth ,index ,call) pool)
     :hints (("Goal" ,@(and recursive (list :induct call :expand call))
              :in-theory (e/d (,(if recursive (list :induction (car call)) (car call))) (mv-nth)))))))
(local (fc-read-only fc-byte-keeps-pool
  (fn2-fc-byte 0 kind nil slot gen off len base okind oslot ogen fc ctx b3 fields pool ds) 3))
(local (fc-read-only fc-advance-keeps-pool
  (fn2-fc-advance fuel 0 kind nil slot gen off len base okind oslot ogen fc ctx b3 fields pool ds) 4))
(local (fc-read-only fc-run-keeps-pool
  (fn2-fc-run-bytes fuel 0 kind nil slot gen off len base okind oslot ogen fc ctx b3 fields pool ds) 3 t))
(local (fc-read-only fc-step-keeps-pool
  (fn2-fc-step 0 kind nil slot gen off len base okind oslot ogen budget fc ctx b3 fields pool ds) 4))
(local (fc-read-only fc-format-keeps-pool
  (fn2-format-run kind nil 0 slot gen off len base okind oslot ogen budget fc ctx b3 fields pool ds) 4))
(local (fc-read-only fc-drive-keeps-pool
  (fn2-format-drive fuel 0 kind nil slot gen off len base okind oslot ogen budget fc ctx b3 fields pool ds) 4 t))
(local (defthm fc-initial-progress
  (fc-progress-at (fn2-fc-init 1 (create-fn2-fc)) pool ds)
  :hints (("Goal" :in-theory (enable fc-digest-progress fc-image-initially-idle)))))
(local (defthm fc-image-drive-verifies-trailer
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
               '(fc-image-drive fc-drive-keeps-pool fc-initial-progress (:executable-counterpart natp)))))))

; The fixture loader appends until its first refusal. A successful read below
; the resulting fill therefore refers to an input byte that was written.
(local (defmacro fc-put-input ()
  '(fn2-pool-write 0 1 i byte 1 0 1 pool)))
(local (defthm fc-write-input-effects
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
              update-nth-array nth-update-nth max natp (:executable-counterpart nfix)))))))
(local (defun-nx fc-input-octet (k pool)
  (fn2-pool-datai (+ (fn2-pool-base 0 pool) k) pool)))
(local (defthm fc-write-input-octet
  (implies (and (equal (car (fc-put-input)) :ok)
                (natp (fn2-pool-base 0 pool)) (equal (fn2-pool-fill 0 pool) i)
                (natp k) (natp i))
           (equal (fc-input-octet k (mv-nth 1 (fc-put-input)))
                  (if (equal k i) byte (fc-input-octet k pool))))
  :hints (("Goal" :in-theory (e/d (fc-input-octet fc-write-input-effects natp nfix) (mv-nth))))))
(local (defthm fc-nth-from-input-offset
  (implies (and (consp bytes) (natp k) (natp i) (<= i k))
           (equal (nth (- k i) bytes)
                  (if (equal i k) (car bytes) (nth (- k (1+ i)) (cdr bytes)))))
  :hints (("Goal" :expand (nth (- k i) bytes)
                  :in-theory (union-theories (current-theory 'fc-u32-reconstruct) '(nth))))))
(local (defthm fc-refused-write-keeps-pool
  (implies (not (eq (car (fc-put-input)) :ok))
           (equal (mv-nth 1 (fc-put-input)) pool))
  :hints (("Goal" :in-theory (e/d (fn2-pool-write) (mv-nth))))))
(local (defthm fc-loaded-input-byte
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
                                (:instance fc-write-input-octet (byte (car bytes))))))))

(local (defthm fc-initial-drive-length-bound
  (implies (and (natp len) (<= 4294967296 len))
           (not (equal (car (fn2-format-drive fuel 0 kind nil 0 1 0 len 0 1 0 1 4096
                                            fc ctx b3 fields pool ds)) :ok)))
  :hints (("Goal" :expand (fn2-format-drive fuel 0 kind nil 0 1 0 len 0 1 0 1 4096
                                            fc ctx b3 fields pool ds)
                  :in-theory (e/d (fn2-format-run fn2-fc-step fc-zero-plus-len)
                                  (mv-nth))))))
(local (defthm fc-accepted-length-bound
  (implies (fn2-fc-acceptedp kind bytes ctx) (< (len bytes) 4294967296))
  :rule-classes nil
  :hints (("Goal" :use fc-accepted-drive-ok
                  :in-theory (enable fc-image-drive fc-initial-drive-length-bound fc-length-natural)))))
(local (defthm fc-image-pool-profile
  (implies (< (len bytes) 4294967296)
           (fn2-pool-profilep (list (cons 1 (max 1 (len bytes))))))
  :hints (("Goal" :in-theory (current-theory 'fc-u32-reconstruct)))))
(local (defthm fc-reserved-slot-initial
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
        update-nth-array nth-update-nth))))))
(local (defthm fc-accepted-reservation
  (implies (fn2-fc-acceptedp kind bytes ctx)
           (and (equal (car (fc-reservation bytes)) :ok)
                (equal (mv-nth 1 (fc-reservation bytes)) 0)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
       '(fn2-fc-acceptedp fn2-fc-image fn2-fc-image-run fc-mv-cons fc-mv-zero
         car-cons (:executable-counterpart zp)))))))
(local (defthm fc-created-pool-type
  (fn2-poolp (create-fn2-pool))
  :hints (("Goal" :in-theory (current-theory 'fc-u32-reconstruct)))))
(local (defthm fc-accepted-load-start
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
               (:executable-counterpart unsigned-byte-p) (:executable-counterpart natp)))))))
(local (defthm fc-accepted-pool-reads-input
  (let ((read (fn2-b3-read 0 1 i 1 0 1 (fc-image-pool bytes))))
    (implies (and (fn2-fc-acceptedp kind bytes ctx) (eq (car read) :ok))
             (equal (mv-nth 1 read) (nth i bytes))))
  :rule-classes nil
  :hints (("Goal" :use (fc-accepted-load-start
              (:instance fc-loaded-input-byte (k i) (i 0)
                         (pool (mv-nth 3 (fc-reservation bytes)))))
                  :in-theory (e/d (fc-image-pool fc-input-octet fn2-b3-read fn2-pool-read natp commutativity-of-+ fc-zero-plus-len)
                                  (mv-nth fn2-pool-datai fn2-pool-base fn2-pool-fill))))))

(local (defthm fc-accepted-result-byte
  (implies (and (fn2-fc-acceptedp kind bytes ctx) (not (eq kind :page)) (natp k) (< k 32))
           (equal (fn2-fc-digest-byte 0 k nil (mv-nth 5 (fc-image-drive kind bytes ctx)))
                  (nth (+ 0 (- (len bytes) 32) k) bytes)))
  :rule-classes nil
  :hints (("Goal" :use (fc-image-drive-verifies-trailer
                         (:instance fc-accepted-pool-reads-input (i (+ 0 (- (len bytes) 32) k))))
                  :in-theory (union-theories (theory 'minimal-theory) '(fc-digest-match))))))
(local (defthm fc-accepted-trailer-length
  (implies (and (fn2-fc-acceptedp kind bytes ctx) (not (eq kind :page)))
           (<= 32 (len bytes)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fc-image-drive-verifies-trailer (k 0)))
                  :in-theory (e/d (fc-digest-match fn2-b3-read fn2-pool-read natp
                                   (:executable-counterpart natp))
                                  (mv-nth fc-image-drive fc-image-pool))))))
(local (defun-nx fc-result-octets (k n ds)
  (declare (xargs :measure (nfix n)
                  :hints (("Goal" :in-theory (current-theory 'fc-u32-reconstruct)))))
  (if (zp n) nil
    (cons (fn2-fc-digest-byte 0 k nil ds) (fc-result-octets (1+ k) (1- n) ds)))))
(local (defthm fc-take-at-index
  (implies (and (posp n) (natp i))
           (equal (take n (nthcdr i bytes))
                  (cons (nth i bytes) (take (1- n) (nthcdr (1+ i) bytes)))))
  :rule-classes nil
  :hints (("Goal" :induct (nthcdr i bytes)
                  :in-theory (current-theory 'fc-u32-reconstruct)))))
(local (defthm fc-result-octets-are-trailer
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
                  :in-theory (union-theories '(fc-result-octets) (set-difference-theories (current-theory 'fc-u32-reconstruct) '(fn2-fc-acceptedp mv-nth take nthcdr nth)))))))

(local (defthm fc-frame-header-allocation
  (implies (and (fn2-fc-acceptedp :frame bytes a) (fn2-fc-acceptedp :frame bytes b))
           (and (equal (fn2-fc-expected-extent-writer-epoch a) (fn2-fc-expected-extent-writer-epoch b))
                (equal (fn2-fc-expected-allocation a) (fn2-fc-expected-allocation b))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fc-accepted-binds-header (context a) (kind :frame))
                        (:instance fc-accepted-binds-header (context b) (kind :frame)))
                  :in-theory (union-theories (theory 'minimal-theory) '(fn2-fc-identity fc-image-context-scalars))))))
(local (defthm fc-seal-header-predecessor-commit
  (implies (and (fn2-fc-acceptedp :seal bytes a) (fn2-fc-acceptedp :seal bytes b))
           (equal (fn2-fc-expected-previous-commit a) (fn2-fc-expected-previous-commit b)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fc-accepted-binds-header (context a) (kind :seal))
                        (:instance fc-accepted-binds-header (context b) (kind :seal)))
                  :in-theory (union-theories (theory 'minimal-theory) '(fn2-fc-identity fc-image-context-scalars))))))
(local (defthm fc-seal-covered-binds-padded-body
  (implies (and (fn2-fc-expectedp ca) (fn2-fc-expectedp cb)
                (equal (fn2-fc-covered :seal a ca) (fn2-fc-covered :seal b cb)))
           (equal (append (take (nfix (- (len a) 32)) a) (make-list 32 :initial-element 0))
                  (append (take (nfix (- (len b) 32)) b) (make-list 32 :initial-element 0))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn2-fc-covered fn2-fc-expectedp fc-append-associative
                fc-cancel-common-prefix fc-eight-byte-fields-injective))))))
(local (defthm fc-prefix-length
  (equal (len (append (take n x) suffix)) (+ (nfix n) (len suffix)))
  :hints (("Goal" :in-theory (current-theory 'fc-u32-reconstruct)))))
(local (defthm fc-cancel-fixed-tail
  (equal (take n (append (take n x) suffix)) (take n x))
  :hints (("Goal" :induct (take n x) :in-theory (current-theory 'fc-u32-reconstruct)))))
(local (defthm fc-rejoin-at
  (implies (and (natp n) (<= n (len x))) (equal (append (take n x) (nthcdr n x)) x))
  :hints (("Goal" :induct (take n x) :in-theory (current-theory 'fc-u32-reconstruct)))))
(local (defthm fc-rejoin-identical-images
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
                  :in-theory (union-theories (theory 'minimal-theory) '(nfix natp))))))
(local (defthm fc-seal-covered-and-trailer-bind-image
  (implies (and (fn2-fc-expectedp ca) (fn2-fc-expectedp cb)
                (equal (fn2-fc-covered :seal a ca) (fn2-fc-covered :seal b cb))
                (equal (nthcdr (nfix (- (len a) 32)) a) (nthcdr (nfix (- (len b) 32)) b)))
           (equal a b))
  :rule-classes nil
  :hints (("Goal" :use (fc-seal-covered-binds-padded-body
                   (:instance fc-rejoin-identical-images (i (nfix (- (len a) 32)))
                       (j (nfix (- (len b) 32))) (suffix (make-list 32 :initial-element 0))))
                  :in-theory (union-theories (theory 'minimal-theory)
                    '(fc-length-natural natp nfix (:type-prescription len)))))))
