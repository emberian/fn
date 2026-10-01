; Actual basic-loop output-window boundary. Source proof only; no runtime
; activation, native funding or complete controller/dictionary/digest claim.
(in-package "ACL2")
(include-book "decoded-window-budget-completion")
(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-pwz-output-emit-prefix
  (implies (and (syntaxp (not (equal fn-zin-out ''nil))) (true-listp fn-zin-out))
           (equal (fn-zin-emit o fn-zin-st fn-zin-win fn-zin-out)
                  (let ((r (fn-zin-emit o fn-zin-st fn-zin-win nil)))
                   (mv (car r) (mv-nth 1 r) (mv-nth 2 r)
                       (append fn-zin-out (mv-nth 3 r))))))
  :hints (("Goal" :in-theory (enable fn-zin-emit)))))

(local
 (defthm fn-pwz-output-action-prefix
  (implies (and (syntaxp (not (equal fn-zin-out ''nil))) (true-listp fn-zin-out))
           (equal (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                  (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab nil)))
                   (mv (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r)
                       (append fn-zin-out (mv-nth 4 r))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-zin-act) (fn-zin-act-counts fn-zin-emit-out))))))

(local
 (defthm fn-pwz-output-snoc-length
  (equal (len (fn-oct-snoc x o)) (+ 1 (len x)))
  :hints (("Goal" :induct (fn-oct-snoc x o) :in-theory (enable fn-oct-snoc)))))
(local
 (defthm fn-pwz-output-snoc-true-list
  (true-listp (fn-oct-snoc x o))
  :hints (("Goal" :induct (fn-oct-snoc x o) :in-theory (enable fn-oct-snoc)))))

(local
 (defthm fn-pwz-output-action-at-most-one
  (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
   (and (<= (len fn-zin-out) (len (mv-nth 4 r)))
        (<= (len (mv-nth 4 r)) (+ 1 (len fn-zin-out)))
        (implies (true-listp fn-zin-out) (true-listp (mv-nth 4 r)))))
  :rule-classes (:rewrite
    (:linear :corollary (<= (len fn-zin-out) (len (mv-nth 4 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))))
    (:linear :corollary (<= (len (mv-nth 4 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) (+ 1 (len fn-zin-out)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-zin-act fn-zin-emit) (fn-zin-act-counts fn-zin-emit-out))))))

; Proof-only readiness transcript, tied to each actual ACT's complete effects.
(local
 (defun-nx fn-pwz-action-ready-transcript-p (k fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
 (if (zp k) t
  (and (<= (fn-zin-need fn-zin-st) (fn-zin-nbits fn-zin-st))
       (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
        (or (car r)
            (fn-pwz-action-ready-transcript-p (- k 1) (mv-nth 1 r)
                                               (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r))))))))

; One-output ACT reference schedule, proof-only. It preserves the actual
; basic loop's check/pull/refusal order; semantic fuel is not charged STEP fuel.
(defun-nx fn-pwz-atomic-output-loop (b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
 (declare (xargs :measure (nfix b)))
 (if (zp b) (mv :yield 0 ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  (if (>= (fn-zin-out-len fn-zin-out) (nfix lim))
   (mv :full b ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
   (if (> (fn-zin-need fn-zin-st) (fn-zin-nbits fn-zin-st))
    (if (and (natp ip) (< ip (min (nfix end) (fn-octets-len fn-octets))))
     (fn-pwz-atomic-output-loop (- b 1) (+ ip 1) end lim
                                (fn-zin-pull ip fn-zin-st fn-octets)
                                fn-octets fn-zin-win fn-zin-tab fn-zin-out)
     (mv :more b ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
    (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
     (if (car r)
      (mv (list :refused (car r)) (- b 1) ip (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r))
      (fn-pwz-atomic-output-loop (- b 1) ip end lim (mv-nth 1 r) fn-octets
                                 (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r))))))))
(local
 (defthm fn-pwz-unit-step-action-count
  (equal (fn-pwz-step-action-count 1 fn-zin-st fn-zin-win fn-zin-tab fn-zin-out) 1)
  :hints (("Goal" :use ((:instance fn-pwz-step-action-count-room-bound (room 1)))
           :in-theory (disable fn-pwz-step-action-count)))))
(local
 (defthm fn-pwz-output-action-full-tuple
  (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
   (equal (list (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r)) r))
  :hints (("Goal" :in-theory (enable fn-zin-act)))))
(local
 (defthm fn-pwz-unit-step-is-actual-action
  (equal (fn-zin-step 1 fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
         (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
  :hints (("Goal" :expand ((fn-pwz-action-sequence 1 fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                          (:free (s win tab out) (fn-pwz-action-sequence 0 s win tab out)))
           :use ((:instance fn-pwz-actual-step-is-action-trajectory (room 1))
                 (:instance fn-pwz-output-action-full-tuple))
           :in-theory (e/d (fn-pwz-action-sequence) (fn-zin-act fn-zin-step fn-pwz-output-action-full-tuple))))) )

; The reference's one-output scheduling boundary is the actual basic loop,
; including status, remaining fuel, cursor and complete private pool effects.
(local
 (defthm fn-pwz-actual-unit-output-loop-is-atomic
 (implies (and (natp lim) (<= lim (+ 1 (len fn-zin-out))))
          (equal (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                 (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          :in-theory (e/d (fn-zin-loop fn-pwz-atomic-output-loop)
                          (fn-zin-step fn-zin-act fn-zin-loop-counts fn-zin-step-counts fn-zin-act-counts
                           fn-zin-pull fn-zin-need))))))

; A ready, successful actual ACT transcript consumes no input and cannot hit
; its output frontier before its last action. This is semantic fuel only.
(local
 (defthm fn-pwz-ready-atomic-prefix-is-action-sequence
 (implies (and (natp k) (natp lim)
               (<= (+ (len fn-zin-out) k) lim)
               (fn-pwz-action-ready-transcript-p k fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
               (not (car (fn-pwz-action-sequence k fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
          (let ((r (fn-pwz-action-sequence k fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
           (equal (fn-pwz-atomic-output-loop k ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                  (mv :yield 0 ip (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pwz-action-ready-transcript-p k fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
          :in-theory (e/d (fn-pwz-action-ready-transcript-p fn-pwz-action-sequence fn-pwz-atomic-output-loop)
                          (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts))))))

(local
 (defthm fn-pwz-copy-actions-ready
  (implies (and (natp k) (<= k (fn-zin-n fn-zin-st))
                (equal (fn-zin-mode fn-zin-st) 12))
           (fn-pwz-action-ready-transcript-p k fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
  :hints (("Goal" :induct (fn-pwz-action-ready-transcript-p k fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-pwz-action-ready-transcript-p fn-zin-act fn-zin-need fn-zin-emit)
                           (fn-zin-act-counts fn-zin-emit-out))))))

(local
 (defthm fn-pwo-update-nth-same
   (equal (update-nth i x (update-nth i y z)) (update-nth i x z))
   :hints (("Goal" :induct (update-nth i x z)
            :in-theory (enable update-nth)))))

(local
 (defun fn-pwo-index-pair-induction (i j z)
   (declare (xargs :measure (nfix i) :verify-guards nil))
   (if (and (posp i) (posp j))
       (fn-pwo-index-pair-induction (1- i) (1- j) (cdr z))
     z)))

(local
 (defthm fn-pwo-update-nth-commute
   (implies (and (natp i) (natp j) (not (equal i j)))
            (equal (update-nth i x (update-nth j y z))
                   (update-nth j y (update-nth i x z))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-pwo-index-pair-induction i j z)
            :in-theory (enable update-nth)))))

(local
 (defthm fn-pwo-state-set-same
   (equal (fn-zin-set i x (fn-zin-set i y fn-zin-st))
          (fn-zin-set i x fn-zin-st))
   :hints (("Goal" :in-theory (enable fn-zin-set$inline)))))

(local
 (defthm fn-pwo-state-set-commute
   (implies (not (equal i j))
            (equal (fn-zin-set i x (fn-zin-set j y fn-zin-st))
                   (fn-zin-set j y (fn-zin-set i x fn-zin-st))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-zin-set$inline)
            :use ((:instance fn-pwo-update-nth-commute
                            (x (nfix x)) (y (nfix y)) (z (car fn-zin-st))))))))

(local
 (defthm fn-pwo-state-set-canonical-order
   (implies (and (natp i) (natp j) (< j i))
            (equal (fn-zin-set i x (fn-zin-set j y fn-zin-st))
                   (fn-zin-set j y (fn-zin-set i x fn-zin-st))))
   :rule-classes ((:rewrite :loop-stopper nil))
   :hints (("Goal" :use ((:instance fn-pwo-state-set-commute))))))


(local
 (defthm fn-pwo-actual-literal-first-action-effects
   (let* ((entry (fn-zin-tget (+ 723 (fn-zin-lowb (fn-zin-bits fn-zin-st) 9)) fn-zin-tab))
          (width (fn-zin-highb entry 9))
          (octet (fn-zin-lowb entry 9)))
     (implies (and (equal (fn-zin-mode fn-zin-st) 8)
                   (fn-zin-freshp fn-zin-st)
                   (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))
              (equal (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                     (mv nil
                         (fn-zin-set 6 (1+ (fn-zin-tout fn-zin-st))
                                     (fn-zin-set 5 (fn-zin-wrap (1+ (fn-zin-wrap (fn-zin-wpos fn-zin-st))))
                                                 (fn-zin-set 2 (- (fn-zin-nbits fn-zin-st) width)
                                                             (fn-zin-set 1 (fn-zin-highb (fn-zin-bits fn-zin-st) width)
                                                                         fn-zin-st))))
                         (fn-oct-update (fn-zin-wrap (fn-zin-wpos fn-zin-st)) octet fn-zin-win)
                         fn-zin-tab (fn-oct-snoc fn-zin-out octet)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-zin-act fn-zin-decode-bit fn-zin-freshp
                                       fn-zin-lit-ready-p fn-zin-emit fn-zin-lk-base)
                            (fn-zin-emit-out))))))

(local
 (defthm fn-pwo-literal-loop-tout-monotone
   (implies (and (natp tout) (natp nbits))
            (<= tout (mv-nth 3 (fn-zin-lit-loop k bits nbits w tout limit
                                               fn-zin-tab fn-zin-win fn-zin-out))))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-zin-lit-loop-counts))
            :in-theory (disable fn-zin-lit-loop-counts)))))

(local
 (defthm fn-pwo-literal-batch-first-action-and-tail
   (implies (and (posp room)
                 (equal (fn-zin-mode fn-zin-st) 8)
                 (fn-zin-freshp fn-zin-st)
                 (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))
            (equal (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                   (let* ((first (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
                          (tail (fn-zin-lits (1- room) (mv-nth 1 first) (mv-nth 2 first)
                                             (mv-nth 3 first) (mv-nth 4 first))))
                     (mv (1+ (car tail)) (mv-nth 1 tail) (mv-nth 2 tail) (mv-nth 3 tail)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-pwo-actual-literal-first-action-effects))
            :expand ((:free (bits nbits w tout limit tab win out)
                             (fn-zin-lit-loop room bits nbits w tout limit tab win out)))
            :in-theory (e/d (fn-zin-lits fn-zin-lit-ready-p fn-zin-freshp)
                            (fn-zin-act fn-zin-act-counts fn-zin-lit-loop-out-free))))))


(local
 (defun fn-pwo-literal-ready-induction (room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :stobjs (fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                  :verify-guards nil :measure (nfix room)))
  (if (and (posp room) (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))
   (mv-let (why fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
    (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
    (declare (ignore why))
    (fn-pwo-literal-ready-induction (1- room) fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
   (mv fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
(local
 (defthm fn-pwo-literal-stopped-count-zero
  (implies (or (zp room) (not (fn-zin-lit-ready-p fn-zin-st fn-zin-tab)))
   (equal (car (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)) 0))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (bits nbits w tout limit tab win out)
                          (fn-zin-lit-loop room bits nbits w tout limit tab win out)))
           :in-theory (e/d (fn-zin-lits fn-zin-lit-ready-p) (fn-zin-lit-loop-out-free))))))
(local
 (defthm fn-pwo-literal-actions-ready
  (implies (and (equal (fn-zin-mode fn-zin-st) 8) (fn-zin-freshp fn-zin-st))
   (fn-pwz-action-ready-transcript-p
    (car (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
    fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
  :hints (("Goal" :induct (fn-pwo-literal-ready-induction room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-pwz-action-ready-transcript-p fn-zin-need)
                           (fn-zin-act fn-zin-lits fn-zin-lit-ready-p fn-zin-freshp fn-zin-act-counts)))
          ("Subgoal *1/1" :use ((:instance fn-pwo-literal-batch-first-action-and-tail)
                                (:instance fn-pwo-actual-literal-first-action-effects))
           :in-theory (e/d (fn-pwz-action-ready-transcript-p fn-zin-need fn-zin-freshp fn-zin-lit-ready-p)
                           (fn-zin-act fn-zin-lits fn-zin-act-counts))))))

(local
 (defthm fn-pwz-actual-step-selected-actions-ready
 (implies (and (posp room)
               (<= (fn-zin-need fn-zin-st) (fn-zin-nbits fn-zin-st)))
  (fn-pwz-action-ready-transcript-p
   (fn-pwz-step-action-count room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
   fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :expand ((fn-pwz-action-ready-transcript-p 1 fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                   (:free (s win tab out) (fn-pwz-action-ready-transcript-p 0 s win tab out)))
          :in-theory (e/d (fn-pwz-step-action-count max min nfix)
                          (fn-pwz-action-ready-transcript-p fn-zin-act fn-zin-lits fn-zin-need
                           fn-zin-freshp fn-zin-lit-ready-p fn-zin-act-counts))))))

; Actual successful STEP is a ready atomic segment at the same frontier.
; It costs one charged STEP and K semantic ACTs; neither replaces native cost.
(local
 (defthm fn-pwz-actual-successful-step-is-atomic-segment
 (implies (and (posp room)
               (<= (fn-zin-need fn-zin-st) (fn-zin-nbits fn-zin-st))
               (not (car (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
  (let* ((k (fn-pwz-step-action-count room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
         (r (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
   (equal (fn-pwz-atomic-output-loop k ip end (+ (len fn-zin-out) room)
                                      fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          (mv :yield 0 ip (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pwz-step-action-count-room-bound)
                       (:instance fn-pwz-actual-step-selected-actions-ready)
                       (:instance fn-pwz-actual-step-is-action-trajectory)
                       (:instance fn-pwz-ready-atomic-prefix-is-action-sequence
                        (k (fn-pwz-step-action-count room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
                        (lim (+ (len fn-zin-out) room))))
          :in-theory (disable fn-zin-step fn-zin-act fn-pwz-action-sequence
                              fn-pwz-atomic-output-loop fn-pwz-step-action-count
                              fn-pwz-action-ready-transcript-p)))))

(local
 (defthm fn-pwz-actual-refused-step-selects-one-action
  (implies (and (posp room)
                (car (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
   (equal (fn-pwz-step-action-count room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out) 1))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-zin-step fn-zin-match fn-pwz-step-action-count max min nfix)
                           (fn-zin-act fn-zin-lits fn-zin-copy fn-zin-match-out-free))))))

(local
 (defthm fn-pwz-atomic-output-loop-split-budget
  (implies (and (natp b1) (natp b2)
                (equal (car (fn-pwz-atomic-output-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                         fn-zin-out))
                       :yield))
           (equal (fn-pwz-atomic-output-loop (+ b1 b2) ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                  (let ((r (fn-pwz-atomic-output-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                        fn-zin-out)))
                    (fn-pwz-atomic-output-loop b2 (mv-nth 2 r) end lim (mv-nth 3 r) fn-octets
                                 (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)))))
  :hints (("Goal" :in-theory (e/d (fn-pwz-atomic-output-loop) (fn-zin-act fn-zin-pull fn-zin-need)) :induct (fn-pwz-atomic-output-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                       fn-zin-out)))))


; Exact source schedule observer. Terminal remaining charged fuel is retained;
; each successful STEP expands to its actual selected ACT count.
(defun-nx fn-pwz-actual-loop-semantic-fuel
 (b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
 (declare (xargs :measure (nfix b)))
 (cond ((zp b) 0)
       ((<= (nfix lim) (len fn-zin-out)) (nfix b))
       ((< (fn-zin-nbits fn-zin-st) (fn-zin-need fn-zin-st))
        (if (and (natp ip) (< ip (min (nfix end) (fn-octets-len fn-octets))))
         (+ 1 (fn-pwz-actual-loop-semantic-fuel
               (1- b) (1+ ip) end lim (fn-zin-pull ip fn-zin-st fn-octets)
               fn-octets fn-zin-win fn-zin-tab fn-zin-out))
         (nfix b)))
       (t (let* ((room (- (nfix lim) (len fn-zin-out)))
                 (r (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
            (if (car r) (nfix b)
             (+ (fn-pwz-step-action-count room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                (fn-pwz-actual-loop-semantic-fuel
                 (1- b) ip end lim (mv-nth 1 r) fn-octets
                 (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r))))))))

(local
 (defthm fn-pwz-actual-refused-step-is-action
  (implies (and (posp room) (car (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
   (equal (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
          (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
  :hints (("Goal" :use ((:instance fn-pwz-actual-step-is-action-trajectory)
                        (:instance fn-pwz-output-action-full-tuple))
           :expand ((fn-pwz-action-sequence 1 fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                    (:free (s win tab out) (fn-pwz-action-sequence 0 s win tab out)))
           :in-theory (e/d (fn-pwz-action-sequence)
                           (fn-zin-step fn-zin-act fn-pwz-output-action-full-tuple fn-pwz-step-action-count))))))
(local
 (defthm fn-pwz-loop-semantic-fuel-natural
  (natp (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-pwz-actual-loop-semantic-fuel) (fn-zin-act fn-zin-step fn-zin-pull fn-pwz-step-action-count))))))

(local
 (defthm fn-pwz-successful-step-at-lim-rewrite
  (implies (and (natp lim) (< (len fn-zin-out) lim)
                (<= (fn-zin-need fn-zin-st) (fn-zin-nbits fn-zin-st))
                (not (car (fn-zin-step (- lim (len fn-zin-out)) fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
   (let ((r (fn-zin-step (- lim (len fn-zin-out)) fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
    (equal (fn-pwz-atomic-output-loop
            (fn-pwz-step-action-count (- lim (len fn-zin-out)) fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
            ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           (mv :yield 0 ip (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r)))))
  :hints (("Goal" :use ((:instance fn-pwz-actual-successful-step-is-atomic-segment (room (- lim (len fn-zin-out)))))
           :in-theory (disable fn-pwz-atomic-output-loop fn-zin-act fn-zin-step fn-pwz-step-action-count)))))

(local
 (defthm fn-pwz-successful-step-atomic-continuation
  (implies (and (natp n) (natp lim) (< (len fn-zin-out) lim)
                (<= (fn-zin-need fn-zin-st) (fn-zin-nbits fn-zin-st))
                (not (car (fn-zin-step (- lim (len fn-zin-out)) fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
   (let ((r (fn-zin-step (- lim (len fn-zin-out)) fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
    (equal (fn-pwz-atomic-output-loop
            (+ n (fn-pwz-step-action-count (- lim (len fn-zin-out)) fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
            ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           (fn-pwz-atomic-output-loop n ip end lim (mv-nth 1 r) fn-octets
                                      (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r)))))
  :hints (("Goal" :use ((:instance fn-pwz-atomic-output-loop-split-budget
                         (b1 (fn-pwz-step-action-count (- lim (len fn-zin-out)) fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
                         (b2 n)))
           :in-theory (disable fn-pwz-atomic-output-loop fn-zin-act fn-zin-step fn-pwz-step-action-count
                               fn-pwz-atomic-output-loop-split-budget)))))

(local
 (defthm fn-pwz-actual-basic-loop-is-atomic-schedule
 (implies (and (natp b) (natp lim))
  (equal (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
         (fn-pwz-atomic-output-loop
          (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          :in-theory (e/d (fn-zin-loop fn-pwz-actual-loop-semantic-fuel fn-pwz-atomic-output-loop)
                          (fn-zin-act fn-zin-step fn-zin-pull fn-zin-need fn-pwz-step-action-count
                           fn-zin-loop-counts fn-zin-act-counts fn-zin-step-counts
                           fn-pwz-atomic-output-loop-split-budget fn-pwz-actual-refused-step-is-action)))
         ("Subgoal *1/5" :expand ((fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) :use ((:instance fn-pwz-actual-refused-step-is-action
                                (room (- lim (len fn-zin-out))))))
         ("Subgoal *1/6"
          :use ((:instance fn-pwz-successful-step-atomic-continuation
                 (n (let ((r (fn-zin-step (- lim (len fn-zin-out)) fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
                      (fn-pwz-actual-loop-semantic-fuel (1- b) ip end lim (mv-nth 1 r) fn-octets
                                                       (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r))))))
          :in-theory (e/d (fn-zin-loop fn-pwz-actual-loop-semantic-fuel)
                          (fn-pwz-atomic-output-loop fn-zin-act fn-zin-step fn-zin-pull fn-zin-need
                           fn-pwz-step-action-count fn-zin-loop-counts fn-zin-act-counts fn-zin-step-counts
                           fn-pwz-atomic-output-loop-split-budget fn-pwz-actual-refused-step-is-action))))))

; Atomic schedule has no output-dependent batching. Reopening its output
; frontier preserves the exact trajectory and its own remaining fuel.
(local
 (defthm fn-pwz-atomic-loop-split-output
 (implies (and (<= (nfix m) (nfix lim))
               (equal (car (fn-pwz-atomic-output-loop b ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) :full))
  (equal (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
         (let ((r (fn-pwz-atomic-output-loop b ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
          (fn-pwz-atomic-output-loop (mv-nth 1 r) (mv-nth 2 r) end lim (mv-nth 3 r) fn-octets
                                     (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          :in-theory (e/d (fn-pwz-atomic-output-loop)
                          (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts
                           fn-pwz-atomic-output-loop-split-budget))))))

(local
 (defun-nx fn-pwz-atomic-fuel-pair-induction
 (b1 b2 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
 (declare (xargs :measure (nfix b1)))
 (cond ((or (zp b1) (zp b2) (<= (nfix lim) (len fn-zin-out))) nil)
       ((< (fn-zin-nbits fn-zin-st) (fn-zin-need fn-zin-st))
        (if (and (natp ip) (< ip (min (nfix end) (fn-octets-len fn-octets))))
         (fn-pwz-atomic-fuel-pair-induction (1- b1) (1- b2) (1+ ip) end lim
           (fn-zin-pull ip fn-zin-st fn-octets) fn-octets fn-zin-win fn-zin-tab fn-zin-out)
         nil))
       (t (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
            (if (car r) nil
             (fn-pwz-atomic-fuel-pair-induction (1- b1) (1- b2) ip end lim
               (mv-nth 1 r) fn-octets (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r))))))))

; Completed atomic observations agree at any adequate semantic fuel. The
; remaining-fuel field is deliberately absent, not silently equated.
(local
 (defthm fn-pwz-atomic-terminal-observation-fuel-independent
 (let ((r1 (fn-pwz-atomic-output-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
       (r2 (fn-pwz-atomic-output-loop b2 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (and (not (equal (car r1) :yield)) (not (equal (car r2) :yield)))
   (equal (list (car r1) (mv-nth 2 r1) (mv-nth 3 r1) (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1))
          (list (car r2) (mv-nth 2 r2) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2) (mv-nth 6 r2)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pwz-atomic-fuel-pair-induction b1 b2 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          :in-theory (e/d (fn-pwz-atomic-output-loop fn-pwz-atomic-fuel-pair-induction)
                          (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts
                           fn-pwz-atomic-output-loop-split-budget))))))

(local
 (defthm fn-pwz-atomic-completed-budget-padding
 (let ((r (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (and (natp b) (natp extra) (not (equal (car r) :yield)))
   (equal (fn-pwz-atomic-output-loop (+ b extra) ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          (mv (car r) (+ extra (mv-nth 1 r)) (mv-nth 2 r) (mv-nth 3 r)
              (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          :in-theory (e/d (fn-pwz-atomic-output-loop)
                          (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts
                           fn-pwz-atomic-output-loop-split-budget))))))

(defun-nx fn-pwz-semantic-observation (r)
 (list (car r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)))
(local
 (defthm fn-pwz-atomic-remaining-natural
  (implies (natp b)
   (natp (mv-nth 1 (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-pwz-atomic-output-loop)
                           (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts fn-pwz-atomic-output-loop-split-budget))))))

(local
 (defthm fn-pwz-atomic-two-output-windows-compose
 (let* ((r1 (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (r2 (fn-pwz-atomic-output-loop b2 (mv-nth 2 r1) end lim (mv-nth 3 r1) fn-octets
                                       (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1))))
  (implies (and (natp b1) (natp b2) (natp m) (natp lim) (<= (nfix m) (nfix lim))
                (equal (car r1) :full) (not (equal (car r2) :yield)))
   (equal (fn-pwz-semantic-observation
           (fn-pwz-atomic-output-loop (+ b1 b2) ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
          (fn-pwz-semantic-observation r2))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pwz-atomic-completed-budget-padding (b b1) (extra b2) (lim m))
                (:instance fn-pwz-atomic-loop-split-output (b (+ b1 b2)))
                (:instance fn-pwz-atomic-completed-budget-padding
                 (b b2)
                 (extra (mv-nth 1 (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                 (ip (mv-nth 2 (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-st (mv-nth 3 (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-win (mv-nth 4 (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 5 (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out (mv-nth 6 (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))
          :in-theory (e/d (fn-pwz-semantic-observation)
                          (fn-pwz-atomic-output-loop fn-zin-act fn-zin-pull fn-zin-need
                           fn-pwz-atomic-output-loop-split-budget))))))

(local
 (defthm fn-pwz-actual-basic-loop-two-output-windows
 (let* ((r1 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (r2 (fn-zin-loop b2 (mv-nth 2 r1) end lim (mv-nth 3 r1) fn-octets
                              (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1)))
        (whole (fn-zin-loop b0 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (and (natp b0) (natp b1) (natp b2) (natp m) (natp lim) (<= m lim)
                (equal (car r1) :full) (not (equal (car r2) :yield))
                (not (equal (car whole) :yield)))
   (equal (fn-pwz-semantic-observation whole) (fn-pwz-semantic-observation r2))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pwz-actual-basic-loop-is-atomic-schedule (b b0))
                (:instance fn-pwz-actual-basic-loop-is-atomic-schedule (b b1) (lim m))
                (:instance fn-pwz-actual-basic-loop-is-atomic-schedule (b b2)
                 (ip (mv-nth 2 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-st (mv-nth 3 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-win (mv-nth 4 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 5 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-out (mv-nth 6 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
                (:instance fn-pwz-atomic-two-output-windows-compose (b1 (fn-pwz-actual-loop-semantic-fuel b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (b2 (fn-pwz-actual-loop-semantic-fuel b2 (mv-nth 2 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) end lim (mv-nth 3 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) fn-octets (mv-nth 4 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 5 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 6 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))
                (:instance fn-pwz-atomic-terminal-observation-fuel-independent
                 (b1 (fn-pwz-actual-loop-semantic-fuel b0 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (b2 (+ (fn-pwz-actual-loop-semantic-fuel b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out) (fn-pwz-actual-loop-semantic-fuel b2 (mv-nth 2 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) end lim (mv-nth 3 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) fn-octets (mv-nth 4 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 5 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 6 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))))
          :in-theory (e/d (fn-pwz-semantic-observation)
                          (fn-zin-loop fn-pwz-atomic-output-loop fn-pwz-actual-loop-semantic-fuel
                           fn-pwz-atomic-output-loop-split-budget fn-zin-act fn-zin-step fn-zin-pull fn-zin-need))))))

(local
 (defthm fn-pwz-actual-loop-proper-output
  (implies (true-listp fn-zin-out)
   (true-listp (mv-nth 6 (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-zin-loop)
                           (fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-zin-loop-counts fn-zin-step-counts fn-zin-act-counts fn-pwz-actual-refused-step-is-action
                            fn-zin-step-out-free fn-pwz-output-action-prefix))))))

(local
 (defthm fn-pwz-output-nfix-natural
  (implies (natp x) (equal (nfix x) x))
  :hints (("Goal" :in-theory (enable nfix)))))

(local
 (defthm fn-pwz-actual-basic-loop-cleared-output-windows
 (let* ((r1 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (r2 (fn-zin-loop b2 (mv-nth 2 r1) end l (mv-nth 3 r1) fn-octets
                              (mv-nth 4 r1) (mv-nth 5 r1) nil))
        (whole (fn-zin-loop b0 ip end (+ (len (mv-nth 6 r1)) l)
                            fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (and (natp b0) (natp b1) (natp b2) (natp m) (natp l)
                (true-listp fn-zin-out) (equal (car r1) :full)
                (not (equal (car r2) :yield)) (not (equal (car whole) :yield)))
   (equal (fn-pwz-semantic-observation whole)
          (list (car r2) (mv-nth 2 r2) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2)
                (append (mv-nth 6 r1) (mv-nth 6 r2))))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pwz-actual-basic-loop-two-output-windows (lim (+ (len (mv-nth 6 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) l)))
                (:instance fn-zin-loop-stops (b b1) (lim m))
                (:instance fn-zin-loop-out-free
                 (b b2) (lim l) (ip (mv-nth 2 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-st (mv-nth 3 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-win (mv-nth 4 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 5 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-out (mv-nth 6 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))
          :in-theory (e/d (fn-pwz-semantic-observation)
                          (fn-zin-loop fn-zin-loop-out-free fn-pwz-atomic-output-loop
                           fn-pwz-actual-loop-semantic-fuel fn-zin-act fn-zin-step fn-zin-pull fn-zin-need
                           fn-pwz-actual-refused-step-is-action fn-zin-step-out-free fn-pwz-output-action-prefix
                           fn-zin-loop-stops min nfix))))))

(local
 (defthm fn-pwz-actual-completed-loop-budget-positive
  (implies (not (equal (car (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) :yield))
   (posp b))
  :hints (("Goal" :expand ((fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
           :in-theory (disable fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-zin-loop
                               fn-pwz-actual-refused-step-is-action fn-zin-step-out-free fn-pwz-output-action-prefix)))))

(local
 (defthm fn-pwz-actual-basic-loop-is-atomic-natural-frontier
 (implies (natp lim)
  (equal (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
         (fn-pwz-atomic-output-loop
          (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
 :rule-classes nil
 :hints (("Goal" :cases ((zp b))
          :use ((:instance fn-pwz-actual-basic-loop-is-atomic-schedule))
          :expand ((fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                   (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
          :in-theory (disable fn-zin-loop fn-pwz-actual-loop-semantic-fuel fn-pwz-atomic-output-loop
                              fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-pwz-actual-refused-step-is-action))
         ("Subgoal 1" :in-theory (e/d (fn-pwz-atomic-output-loop)
                                     (fn-zin-act fn-zin-step fn-zin-pull fn-zin-need fn-pwz-actual-refused-step-is-action))))))

(local
 (defthm fn-pwz-output-loop-normalized-frontier
  (equal (fn-zin-loop b ip end (nfix lim) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
         (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
  :rule-classes nil
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-zin-loop)
                           (fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-pwz-step-action-count
                            fn-pwz-actual-refused-step-is-action fn-zin-step-out-free fn-pwz-output-action-prefix
                            fn-zin-loop-counts fn-zin-act-counts fn-zin-step-counts
                            fn-pwz-atomic-output-loop-split-budget))))))
(local
 (defthm fn-pwz-output-atomic-normalized-frontier
  (equal (fn-pwz-atomic-output-loop b ip end (nfix lim) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
         (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
  :rule-classes nil
  :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-pwz-atomic-output-loop)
                           (fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-pwz-step-action-count
                            fn-pwz-actual-refused-step-is-action fn-zin-step-out-free fn-pwz-output-action-prefix
                            fn-zin-loop-counts fn-zin-act-counts fn-zin-step-counts
                            fn-pwz-atomic-output-loop-split-budget))))))
(local
 (defthm fn-pwz-output-fuel-normalized-frontier
  (equal (fn-pwz-actual-loop-semantic-fuel b ip end (nfix lim) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
         (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
  :rule-classes nil
  :hints (("Goal" :induct (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-pwz-actual-loop-semantic-fuel)
                           (fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-pwz-step-action-count
                            fn-pwz-actual-refused-step-is-action fn-zin-step-out-free fn-pwz-output-action-prefix
                            fn-zin-loop-counts fn-zin-act-counts fn-zin-step-counts
                            fn-pwz-atomic-output-loop-split-budget))))))

(defthm fn-pwz-actual-basic-loop-is-atomic-unconditionally
 (equal (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
        (fn-pwz-atomic-output-loop
         (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
         ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pwz-actual-basic-loop-is-atomic-natural-frontier (lim (nfix lim)))
                       (:instance fn-pwz-output-loop-normalized-frontier)
                       (:instance fn-pwz-output-fuel-normalized-frontier)
                       (:instance fn-pwz-output-atomic-normalized-frontier
                        (b (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
          :in-theory (disable fn-zin-loop fn-pwz-atomic-output-loop fn-pwz-actual-loop-semantic-fuel
                              fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-pwz-actual-refused-step-is-action))))

(defthm fn-pwz-actual-basic-loop-general-output-windows
 (let* ((r1 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (r2 (fn-zin-loop b2 (mv-nth 2 r1) end lim (mv-nth 3 r1) fn-octets
                              (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1)))
        (whole (fn-zin-loop b0 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (and (<= (nfix m) (nfix lim)) (equal (car r1) :full)
                (not (equal (car r2) :yield)) (not (equal (car whole) :yield)))
   (equal (fn-pwz-semantic-observation whole) (fn-pwz-semantic-observation r2))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pwz-actual-basic-loop-two-output-windows (m (nfix m)) (lim (nfix lim)))
                (:instance fn-pwz-output-loop-normalized-frontier (b b0))
                (:instance fn-pwz-output-loop-normalized-frontier (b b1) (lim m))
                (:instance fn-pwz-output-loop-normalized-frontier (b b2)
                 (ip (mv-nth 2 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-st (mv-nth 3 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-win (mv-nth 4 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 5 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-out (mv-nth 6 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
                (:instance fn-pwz-actual-completed-loop-budget-positive (b b0))
                (:instance fn-pwz-actual-completed-loop-budget-positive (b b1) (lim m))
                (:instance fn-pwz-actual-completed-loop-budget-positive (b b2)
                 (ip (mv-nth 2 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-st (mv-nth 3 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-win (mv-nth 4 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 5 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-out (mv-nth 6 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))
          :in-theory (e/d (fn-pwz-semantic-observation)
                          (fn-zin-loop fn-pwz-atomic-output-loop fn-pwz-actual-loop-semantic-fuel
                           fn-pwz-atomic-output-loop-split-budget fn-zin-act fn-zin-step fn-zin-pull fn-zin-need
                           fn-pwz-actual-completed-loop-budget-positive fn-pwz-actual-refused-step-is-action
                           fn-zin-step-out-free fn-pwz-output-action-prefix)))))

(defthm fn-pwz-actual-basic-loop-general-cleared-windows
 (let* ((r1 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (r2 (fn-zin-loop b2 (mv-nth 2 r1) end l (mv-nth 3 r1) fn-octets
                              (mv-nth 4 r1) (mv-nth 5 r1) nil))
        (whole (fn-zin-loop b0 ip end (+ (len (mv-nth 6 r1)) (nfix l))
                            fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (and (true-listp fn-zin-out) (equal (car r1) :full)
                (not (equal (car r2) :yield)) (not (equal (car whole) :yield)))
   (equal (fn-pwz-semantic-observation whole)
          (list (car r2) (mv-nth 2 r2) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2)
                (append (mv-nth 6 r1) (mv-nth 6 r2))))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pwz-actual-basic-loop-cleared-output-windows (m (nfix m)) (l (nfix l)))
                (:instance fn-pwz-output-loop-normalized-frontier (b b1) (lim m))
                (:instance fn-pwz-output-loop-normalized-frontier (b b2) (lim l)
                 (ip (mv-nth 2 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-st (mv-nth 3 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-win (mv-nth 4 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 5 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-out nil))
                (:instance fn-pwz-actual-completed-loop-budget-positive (b b0) (lim (+ (len (mv-nth 6 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (nfix l))))
                (:instance fn-pwz-actual-completed-loop-budget-positive (b b1) (lim m))
                (:instance fn-pwz-actual-completed-loop-budget-positive (b b2) (lim l)
                 (ip (mv-nth 2 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-st (mv-nth 3 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-win (mv-nth 4 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 5 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-out nil)))
          :in-theory (e/d (fn-pwz-semantic-observation)
                          (fn-zin-loop fn-pwz-atomic-output-loop fn-pwz-actual-loop-semantic-fuel
                           fn-pwz-atomic-output-loop-split-budget fn-zin-act fn-zin-step fn-zin-pull fn-zin-need
                           fn-pwz-actual-completed-loop-budget-positive fn-pwz-actual-refused-step-is-action
                           fn-zin-step-out-free fn-pwz-output-action-prefix)))))
