(in-package "ACL2")

(include-book "post-identity-source-cursor-source-metadata")

(local (include-book "arithmetic/top" :dir :system))

(defun fn-psc-model-source-path-prefix-complete (pos c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((field (fn-psc-model-source-literal-complete pos *fn-inj-path-field* :source-path-field c incoming held))
        (next (fn-psc-step field nil)))
  (if (fn-psc-get ok field)
   (let* ((agent (fn-psc-model-comparison-complete next incoming held))
          (tail-start (fn-psc-step agent nil)))
    (if (fn-psc-get ok agent)
     (fn-psc-step (fn-psc-model-comparison-complete tail-start incoming held) nil)
     tail-start))
   next)))

(defun fn-psc-model-source-path-prefix-cost (pos c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((field-start (fn-psc-literal pos *fn-inj-path-field* :source-path-field c))
        (field (fn-psc-model-comparison-complete field-start incoming held))
        (next (fn-psc-step field nil)))
  (+ 1 (fn-psc-model-comparison-cost field-start incoming held)
   (if (fn-psc-get ok field)
    (+ 1 (fn-psc-model-comparison-cost next incoming held)
     (if (fn-psc-get ok (fn-psc-model-comparison-complete next incoming held))
      (+ 1 (fn-psc-model-comparison-cost
             (fn-psc-step (fn-psc-model-comparison-complete next incoming held) nil) incoming held))
      0))
    0))))

(local (defthm fn-psc-source-path-field-callback
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-path-field))
  (equal (fn-psc-step c nil)
   (if (fn-psc-get ok c)
    (fn-psc-agent-compare (nfix (fn-psc-get pos c)) :source-path-agent c)
    (fn-psc-literal (nfix (fn-psc-get skip c)) *fn-inj-injection-date-field* :source-stamp
     (fn-psc-set has-path nil c)))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control)
   (fn-psc-agent-compare fn-psc-literal nth len update-nth nfix))))))

(local (defthm fn-psc-source-path-agent-callback
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-path-agent))
  (equal (fn-psc-step c nil)
   (if (fn-psc-get ok c)
    (fn-psc-literal (nfix (fn-psc-get pos c)) '(33 110 111 116 45 102 111 114 45 109 97 105 108 13 10)
     :source-path-tail c)
    (fn-psc-literal (nfix (fn-psc-get skip c)) *fn-inj-injection-date-field* :source-stamp
     (fn-psc-set has-path nil c)))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control)
   (fn-psc-agent-compare fn-psc-literal nth len update-nth nfix))))))

(local (defthm fn-psc-source-path-tail-callback
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-path-tail))
  (equal (fn-psc-step c nil)
   (fn-psc-literal (if (fn-psc-get ok c) (nfix (fn-psc-get pos c)) (nfix (fn-psc-get skip c)))
    *fn-inj-injection-date-field* :source-stamp (fn-psc-set has-path (fn-psc-get ok c) c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control)
   (fn-psc-agent-compare fn-psc-literal nth len update-nth nfix))))))

(local (defthm fn-psc-source-agent-comparison-frame
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos))
  (let ((d (fn-psc-model-comparison-complete (fn-psc-agent-compare pos resume c) incoming held)))
   (and (equal (fn-psc-get phase d) :control) (equal (fn-psc-get resume d) resume)
        (iff (fn-psc-get ok d)
         (not (equal (fn-inj-strip (fn-psc-model-retained-agent c incoming)
                                  (nthcdr pos (fn-psc-model-source c incoming held))) :no)))
        (implies (fn-psc-get ok d)
         (equal (fn-psc-get pos d) (+ pos (- (fn-psc-get agent-end c) (fn-psc-get agent-start c)))))
        (fn-psc-source-contextp d incoming held)
        (equal (fn-psc-get k d) (fn-psc-get k c)) (equal (fn-psc-get date d) (fn-psc-get date c))
        (equal (fn-psc-get has-path d) (fn-psc-get has-path c))
        (equal (fn-psc-get aux d) (fn-psc-get aux c)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-agent-compare pos resume c)))
        (:instance fn-psc-comparison-complete-exact-flag (c (fn-psc-agent-compare pos resume c)))
        (:instance fn-psc-comparison-complete-exact-position (c (fn-psc-agent-compare pos resume c)))
        fn-psc-agent-comparison-is-incoming-span-strip)
  :in-theory (e/d (fn-psc-model-retained-agent fn-psc-source-contextp fn-psc-agent-compare fn-psc-compare
                   fn-psc-comparison-statep fn-psc-comparison-positionp fn-psc-model-source nfix)
   (fn-psc-model-comparison-complete fn-psc-comparison-complete-returns-control
    fn-psc-comparison-complete-exact-flag fn-psc-comparison-complete-exact-position
    fn-psc-agent-comparison-is-incoming-span-strip fn-inj-strip fn-inj-take nth nthcdr len update-nth))))))

(local (defthm fn-psc-source-path-callback-preserves-context
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :control)
               (member-eq (fn-psc-get resume c) '(:source-path-field :source-path-agent :source-path-tail)))
  (and (fn-psc-source-contextp (fn-psc-step c nil) incoming held)
       (equal (fn-psc-get skip (fn-psc-step c nil)) (fn-psc-get skip c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-contextp fn-psc-step fn-psc-control
            fn-psc-literal fn-psc-compare fn-psc-agent-compare fn-psc-model-source)
   (nth len update-nth nfix))))))

(local (defthm fn-psc-source-path-comparison-keeps-skip
 (equal (fn-psc-get skip (fn-psc-model-comparison-complete c incoming held)) (fn-psc-get skip c))
 :hints (("Goal" :use ((:instance fn-psc-comparison-complete-preserves-slot (slot 16)))
  :in-theory (disable fn-psc-model-comparison-complete nth)))))

(local (defthm fn-psc-source-path-literal-keeps-skip
 (equal (fn-psc-get skip (fn-psc-literal pos bytes resume c)) (fn-psc-get skip c))
 :hints (("Goal" :in-theory (e/d (fn-psc-literal fn-psc-compare) (nth len update-nth nfix))))))

(local (defthm fn-psc-source-path-agent-constructor-keeps-context
 (implies (fn-psc-source-contextp c incoming held)
  (and (fn-psc-source-contextp (fn-psc-agent-compare pos resume c) incoming held)
       (equal (fn-psc-get skip (fn-psc-agent-compare pos resume c)) (fn-psc-get skip c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-contextp fn-psc-agent-compare fn-psc-compare fn-psc-model-source)
  (nth len update-nth nfix))))))

(local (defthm fn-psc-source-tail-past-end-is-nil
 (implies (and (true-listp xs) (natp i) (<= (len xs) i))
  (equal (nthcdr i xs) nil))
 :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable nthcdr len true-listp)))))

(local (defthm fn-psc-source-tail-head-is-index-byte
 (implies (natp i) (equal (car (nthcdr i xs)) (nth i xs)))
 :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable nthcdr nth)))))

(local (defthm fn-psc-source-nonempty-strip-mismatch-is-no
 (implies (and (consp prefix) (or (not (consp xs)) (not (equal (car xs) (car prefix)))))
  (equal (fn-inj-strip prefix xs) :no))
 :hints (("Goal" :expand ((fn-inj-strip prefix xs)) :in-theory (disable fn-inj-strip)))))

(local (defthm fn-psc-source-buffer-strip-at-is-current-list-strip-all-positions
 (implies (and (natp i) (true-listp xs))
  (equal (fn-inj-strip prefix (nthcdr i xs))
   (if (equal (fn-pbb-strip-at prefix i xs) :no) :no
    (nthcdr (fn-pbb-strip-at prefix i xs) xs))))
 :hints (("Goal" :induct (fn-pbb-strip-at prefix i xs)
  :in-theory (enable fn-pbb-strip-at fn-inj-strip)))))

(local (defthm fn-psc-source-buffer-strip-success-index
 (implies (and (natp i) (true-listp prefix)
               (not (equal (fn-pbb-strip-at prefix i xs) :no)))
  (equal (fn-pbb-strip-at prefix i xs) (+ i (len prefix))))
 :hints (("Goal" :induct (fn-pbb-strip-at prefix i xs)
  :in-theory (e/d (fn-pbb-strip-at) (nth))))))

(local (defthm fn-psc-source-buffer-strip-compose
 (implies (and (true-listp prefix) (natp i))
  (equal (fn-pbb-strip-at (fn-inj-append prefix suffix) i xs)
   (let ((p (fn-pbb-strip-at prefix i xs)))
    (if (equal p :no) :no (fn-pbb-strip-at suffix p xs)))))
 :hints (("Goal" :induct (fn-pbb-strip-at prefix i xs)
  :in-theory (e/d (fn-pbb-strip-at fn-inj-append)
   (nth len  fn-psc-source-buffer-strip-success-index))))))

(local (defthm fn-psc-source-agent-comparison-is-buffer-strip
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos))
  (let* ((d (fn-psc-model-comparison-complete (fn-psc-agent-compare pos resume c) incoming held))
         (p (fn-pbb-strip-at (fn-psc-model-retained-agent c incoming) pos (fn-psc-model-source c incoming held))))
   (and (iff (fn-psc-get ok d) (not (equal p :no)))
        (implies (not (equal p :no)) (equal (fn-psc-get pos d) p)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-agent-comparison-frame
        (:instance fn-psc-source-buffer-strip-at-is-current-list-strip-all-positions
         (prefix (fn-psc-model-retained-agent c incoming)) (i pos) (xs (fn-psc-model-source c incoming held)))
        (:instance fn-psc-source-buffer-strip-success-index
         (prefix (fn-psc-model-retained-agent c incoming)) (i pos) (xs (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-source-contextp fn-psc-model-retained-agent)
   (fn-psc-model-comparison-complete fn-psc-agent-compare fn-psc-model-source fn-inj-strip fn-pbb-strip-at
    fn-psc-source-agent-comparison-frame fn-psc-source-buffer-strip-at-is-current-list-strip-all-positions
    fn-psc-source-buffer-strip-success-index nth nthcdr len nfix))))))

(local (defthm fn-psc-source-path-comparison-keeps-source-and-agent
 (and (equal (fn-psc-model-source (fn-psc-model-comparison-complete c incoming held) incoming held)
             (fn-psc-model-source c incoming held))
      (equal (fn-psc-model-retained-agent (fn-psc-model-comparison-complete c incoming held) incoming)
             (fn-psc-model-retained-agent c incoming)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source fn-psc-model-retained-agent)
  (fn-psc-model-comparison-complete nth nthcdr len nfix))))))

(local (defthm fn-psc-source-path-constructors-keep-source-and-agent
 (and (equal (fn-psc-model-source (fn-psc-agent-compare pos resume c) incoming held) (fn-psc-model-source c incoming held))
      (equal (fn-psc-model-retained-agent (fn-psc-agent-compare pos resume c) incoming) (fn-psc-model-retained-agent c incoming))
      (equal (fn-psc-model-source (fn-psc-literal pos bytes resume c) incoming held) (fn-psc-model-source c incoming held))
      (equal (fn-psc-model-retained-agent (fn-psc-literal pos bytes resume c) incoming) (fn-psc-model-retained-agent c incoming)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source fn-psc-model-retained-agent fn-psc-agent-compare fn-psc-literal fn-psc-compare)
   (nth nthcdr len update-nth nfix))))))

(local (defthm fn-psc-source-path-callback-keeps-source-and-agent
 (implies (and (equal (fn-psc-get phase c) :control)
               (member-eq (fn-psc-get resume c) '(:source-path-field :source-path-agent :source-path-tail)))
  (and (equal (fn-psc-model-source (fn-psc-step c nil) incoming held) (fn-psc-model-source c incoming held))
       (equal (fn-psc-model-retained-agent (fn-psc-step c nil) incoming) (fn-psc-model-retained-agent c incoming))))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source fn-psc-model-retained-agent fn-psc-step fn-psc-control
                fn-psc-agent-compare fn-psc-literal fn-psc-compare)
   (nth nthcdr len update-nth nfix))))))

(local (defthm fn-psc-source-path-literal-complete-unfolds
 (equal (fn-psc-model-comparison-complete (fn-psc-literal pos bytes resume c) incoming held)
        (fn-psc-model-source-literal-complete pos bytes resume c incoming held))
 :hints (("Goal" :in-theory (enable fn-psc-model-source-literal-complete)))))

(local (defthm fn-psc-source-path-literal-complete-keeps-skip
 (equal (fn-psc-get skip (fn-psc-model-source-literal-complete pos bytes resume c incoming held))
        (fn-psc-get skip c))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source-literal-complete)
  (fn-psc-model-comparison-complete fn-psc-literal nth len nfix fn-psc-source-path-literal-complete-unfolds))))))

(local (defthm fn-psc-source-path-literal-constructor-fields
 (and (equal (fn-psc-get phase (fn-psc-literal pos bytes resume c)) :compare)
      (equal (fn-psc-get resume (fn-psc-literal pos bytes resume c)) resume)
      (equal (fn-psc-get base (fn-psc-literal pos bytes resume c)) (nfix pos))
      (equal (fn-psc-get has-path (fn-psc-literal pos bytes resume c)) (fn-psc-get has-path c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-literal fn-psc-compare) (nth len update-nth nfix))))))

(local (defthm fn-psc-source-path-stamp-constructor-context
 (implies (fn-psc-source-contextp c incoming held)
  (fn-psc-source-contextp (fn-psc-literal pos bytes resume (fn-psc-set has-path flag c)) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-contextp fn-psc-model-source fn-psc-literal fn-psc-compare)
  (nth len update-nth nfix))))))

(local (defthm fn-psc-source-path-set-flag-keeps-source-and-agent
 (and (equal (fn-psc-model-source (fn-psc-set has-path flag c) incoming held) (fn-psc-model-source c incoming held))
      (equal (fn-psc-model-retained-agent (fn-psc-set has-path flag c) incoming) (fn-psc-model-retained-agent c incoming)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source fn-psc-model-retained-agent) (nth nthcdr len update-nth nfix))))))

(local (defthm fn-psc-source-path-agent-keeps-skip
 (equal (fn-psc-get skip (fn-psc-agent-compare pos resume c)) (fn-psc-get skip c))
 :hints (("Goal" :in-theory (e/d (fn-psc-agent-compare fn-psc-compare) (nth len update-nth nfix))))))

(local (defthm fn-psc-source-path-comparison-constructors-are-valid
 (and (fn-psc-comparison-statep (fn-psc-literal pos bytes resume c))
      (fn-psc-comparison-statep (fn-psc-agent-compare pos resume c))
      (equal (fn-psc-get phase (fn-psc-agent-compare pos resume c)) :compare))
 :hints (("Goal" :in-theory (e/d (fn-psc-literal fn-psc-agent-compare fn-psc-compare fn-psc-comparison-statep)
  (nth len update-nth nfix))))))

(local (defthm fn-psc-source-byte-run-addition
 (implies (and (natp a) (natp b))
  (equal (fn-psc-model-byte-run (+ a b) c incoming held)
         (fn-psc-model-byte-run b (fn-psc-model-byte-run a c incoming held) incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run a c incoming held)
          :in-theory (e/d (fn-psc-model-byte-run)
                         (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

(local (defthm fn-psc-source-literal-next-is-actual-paid-steps
 (equal (fn-psc-step (fn-psc-model-source-literal-complete pos bytes resume c incoming held) nil)
        (fn-psc-model-byte-run (+ 1 (fn-psc-model-comparison-cost (fn-psc-literal pos bytes resume c) incoming held))
                              (fn-psc-literal pos bytes resume c) incoming held))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-next-is-actual-paid-trace (c (fn-psc-literal pos bytes resume c))))
  :in-theory (e/d (fn-psc-model-source-literal-complete fn-psc-literal fn-psc-compare fn-psc-comparison-statep)
   (fn-psc-source-path-literal-complete-unfolds fn-psc-comparison-next-is-actual-paid-trace fn-psc-model-comparison-complete fn-psc-model-comparison-cost
    fn-psc-step fn-psc-model-byte-run nth len nfix update-nth))))))

(local (defthm fn-psc-source-path-agent-next-is-paid-steps
 (equal (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-agent-compare pos resume c) incoming held) nil)
        (fn-psc-model-byte-run (+ 1 (fn-psc-model-comparison-cost (fn-psc-agent-compare pos resume c) incoming held))
                              (fn-psc-agent-compare pos resume c) incoming held))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-next-is-actual-paid-trace (c (fn-psc-agent-compare pos resume c))))
  :in-theory (e/d (fn-psc-agent-compare fn-psc-compare fn-psc-comparison-statep)
   (fn-psc-comparison-next-is-actual-paid-trace fn-psc-model-comparison-complete fn-psc-model-comparison-cost
    fn-psc-step fn-psc-model-byte-run nth len nfix update-nth fn-psc-source-path-literal-complete-unfolds))))))

(defthm fn-psc-source-path-prefix-complete-frame
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (equal (fn-psc-get skip c) pos))
  (let* ((d (fn-psc-model-source-path-prefix-complete pos c incoming held))
         (p (fn-pbb-strip-at (fn-inj-path-line (fn-psc-model-retained-agent c incoming))
                            pos (fn-psc-model-source c incoming held))))
   (and (equal (fn-psc-get phase d) :compare)
        (equal (fn-psc-get resume d) :source-stamp)
        (equal (fn-psc-get base d) (if (equal p :no) pos p))
        (iff (fn-psc-get has-path d) (not (equal p :no)))
        (fn-psc-source-contextp d incoming held)
        (equal (fn-psc-model-source d incoming held) (fn-psc-model-source c incoming held))
        (equal (fn-psc-model-retained-agent d incoming) (fn-psc-model-retained-agent c incoming)))))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-psc-model-source-path-prefix-complete fn-inj-path-line)
   (fn-psc-model-comparison-complete fn-psc-model-source-literal-complete fn-psc-model-source
    fn-psc-model-retained-agent fn-psc-source-contextp fn-psc-agent-compare fn-psc-literal fn-psc-compare fn-psc-step fn-pbb-strip-at fn-inj-append
    fn-psc-source-literal-next-is-actual-paid-steps fn-psc-source-path-agent-next-is-paid-steps fn-psc-source-byte-run-addition fn-psc-comparison-next-is-actual-paid-trace fn-psc-comparison-complete-is-actual-steps nth len update-nth)))))

(defthm fn-psc-source-path-prefix-complete-is-paid-steps
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos) (equal (fn-psc-get skip c) pos))
  (equal (fn-psc-model-source-path-prefix-complete pos c incoming held)
   (fn-psc-model-byte-run (fn-psc-model-source-path-prefix-cost pos c incoming held) (fn-psc-literal pos *fn-inj-path-field* :source-path-field c) incoming held)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-next-is-actual-paid-trace (c (fn-psc-literal pos *fn-inj-path-field* :source-path-field c)))
   (:instance fn-psc-source-byte-run-addition (a (+ 1 (fn-psc-model-comparison-cost (fn-psc-literal pos *fn-inj-path-field* :source-path-field c) incoming held)))
    (b (if (fn-psc-get ok (fn-psc-model-source-literal-complete pos *fn-inj-path-field* :source-path-field c incoming held)) (+ (+ 1 (fn-psc-model-comparison-cost (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-path-field* :source-path-field c incoming held) nil) incoming held)) (if (fn-psc-get ok (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-path-field* :source-path-field c incoming held) nil) incoming held)) (+ 1 (fn-psc-model-comparison-cost (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-path-field* :source-path-field c incoming held) nil) incoming held) nil) incoming held)) 0)) 0)) (c (fn-psc-literal pos *fn-inj-path-field* :source-path-field c)))
   (:instance fn-psc-source-byte-run-addition (a (+ 1 (fn-psc-model-comparison-cost (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-path-field* :source-path-field c incoming held) nil) incoming held))) (b (if (fn-psc-get ok (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-path-field* :source-path-field c incoming held) nil) incoming held)) (+ 1 (fn-psc-model-comparison-cost (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-path-field* :source-path-field c incoming held) nil) incoming held) nil) incoming held)) 0)) (c (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-path-field* :source-path-field c incoming held) nil)))
   (:instance fn-psc-comparison-next-is-actual-paid-trace (c (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-path-field* :source-path-field c incoming held) nil)))
   (:instance fn-psc-comparison-next-is-actual-paid-trace (c (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-path-field* :source-path-field c incoming held) nil) incoming held) nil))))
  :in-theory (e/d (fn-psc-model-source-path-prefix-complete fn-psc-model-source-path-prefix-cost)
   (fn-psc-model-comparison-complete fn-psc-model-comparison-cost fn-psc-model-source-literal-complete
    fn-psc-literal fn-psc-agent-compare fn-psc-compare fn-psc-step fn-psc-model-byte-run fn-psc-source-contextp
    fn-psc-model-source fn-psc-model-retained-agent
    fn-psc-source-byte-run-addition fn-psc-comparison-next-is-actual-paid-trace fn-psc-comparison-complete-is-actual-steps fn-psc-source-literal-next-is-actual-paid-steps fn-psc-source-path-agent-next-is-paid-steps fn-psc-comparison-statep nth len nfix)))))

(local (in-theory (disable fn-psc-source-path-literal-complete-unfolds)))
