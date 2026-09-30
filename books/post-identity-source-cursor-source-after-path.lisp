; Proof-only full after-Path inverse and actual paid source cursor trace.
(in-package "ACL2")
(include-book "post-identity-source-cursor-source-stamp")
(local (include-book "arithmetic/top" :dir :system))

(local (defthm fn-psc-source-paid-run-preserves-configuration
 (equal (fn-psc-configuration (fn-psc-model-byte-run fuel c incoming held))
        (fn-psc-configuration c))
 :hints (("Goal" :induct (fn-psc-model-byte-run fuel c incoming held)
  :in-theory (e/d (fn-psc-model-byte-run) (fn-psc-step fn-psc-configuration nth len))))))

(local (defthm fn-psc-source-paid-run-preserves-layout
 (implies (equal (len c) 24) (equal (len (fn-psc-model-byte-run fuel c incoming held)) 24))
 :hints (("Goal" :induct (fn-psc-model-byte-run fuel c incoming held)
  :in-theory (e/d (fn-psc-model-byte-run) (fn-psc-step nth len))))))

(local (defthm fn-psc-source-paid-run-preserves-proper-list
 (implies (true-listp c) (true-listp (fn-psc-model-byte-run fuel c incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run fuel c incoming held)
  :in-theory (e/d (fn-psc-model-byte-run) (fn-psc-step nth len true-listp))))))

(local (defthm fn-psc-source-paid-run-preserves-context
 (implies (and (fn-psc-source-contextp c incoming held) (fn-psc-source-resumep c))
  (fn-psc-source-contextp (fn-psc-model-byte-run fuel c incoming held) incoming held))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-paid-run-preserves-configuration fn-psc-source-byte-run-preserves-incoming-agent)
  :in-theory (e/d (fn-psc-source-contextp fn-psc-model-source fn-psc-configuration)
   (fn-psc-model-byte-run fn-psc-source-resumep nth len
    fn-psc-source-paid-run-preserves-configuration fn-psc-source-byte-run-preserves-incoming-agent))))))

(local (defthm fn-psc-source-info-constructor-establishes-resumes
 (implies (and (member-eq (fn-psc-get mode c) '(:source-incoming :source-held))
               (member-eq resume '(:source-info-simple :source-info-v1)))
  (fn-psc-source-resumep (fn-psc-info-compare pos resume c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-resumep fn-psc-info-compare fn-psc-literal fn-psc-compare)
  (nth len update-nth nfix))))))

(local (defthm fn-psc-source-after-stamp-complete-preserves-context
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (fn-psc-source-contextp (fn-psc-model-source-after-stamp-complete pos c incoming held) incoming held))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-info-constructor-establishes-resumes
         (c (fn-psc-set k pos c)) (resume :source-info-v1))
        (:instance fn-psc-source-paid-run-preserves-context
         (fuel (fn-psc-model-source-after-stamp-cost pos c incoming held))
         (c (fn-psc-info-compare pos :source-info-v1 (fn-psc-set k pos c)))))
  :in-theory (e/d (fn-psc-source-contextp fn-psc-source-date-contextp fn-psc-model-source
                   fn-psc-info-compare fn-psc-literal fn-psc-compare)
   (fn-psc-model-source-after-stamp-complete fn-psc-model-source-after-stamp-cost
    fn-psc-model-byte-run fn-psc-source-paid-run-preserves-context fn-psc-source-info-constructor-establishes-resumes nth len update-nth nfix))))))

(local (defthm fn-psc-source-simple-callback
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-info-simple))
  (equal (fn-psc-step c nil)
   (if (fn-psc-get ok c)
       (fn-psc-return t (fn-psc-set resume :source-found c))
       (fn-psc-finish :no-source c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control)
  (fn-psc-return fn-psc-finish nth len update-nth nfix))))))

(local (defthm fn-psc-source-simple-callback-preserves-context
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-info-simple))
  (fn-psc-source-contextp (fn-psc-step c nil) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-contextp fn-psc-model-source fn-psc-return fn-psc-finish)
  (fn-psc-step nth len update-nth))))))

(local (defthm fn-psc-source-simple-complete-is-current-info-strip
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (let* ((d (fn-psc-model-source-simple-complete pos c incoming held))
         (p (fn-pbb-strip-info-at (fn-psc-model-retained-agent c incoming) pos
                                  (fn-psc-model-source c incoming held))))
   (and (equal (fn-psc-get phase d) (if (equal p :no) :done :control))
        (implies (not (equal p :no))
         (and (equal (fn-psc-get resume d) :source-found)
              (equal (fn-psc-get pos d) p) (fn-psc-get ok d)))
        (implies (equal p :no) (equal (fn-psc-result d) :no-source))
        (fn-psc-source-contextp d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-info-complete-is-current-buffer-strip (resume :source-info-simple))
        (:instance fn-psc-source-info-complete-resume-frame (resume :source-info-simple))
        (:instance fn-psc-source-simple-callback
         (c (fn-psc-model-source-info-complete pos :source-info-simple c incoming held)))
        (:instance fn-psc-source-simple-callback-preserves-context
         (c (fn-psc-model-source-info-complete pos :source-info-simple c incoming held))))
  :in-theory (e/d (fn-psc-model-source-simple-complete fn-psc-return fn-psc-finish fn-psc-result)
   (fn-psc-model-source-info-complete fn-psc-source-contextp fn-psc-model-source fn-psc-model-retained-agent
    fn-psc-step fn-psc-source-simple-callback fn-psc-source-simple-callback-preserves-context
    fn-psc-source-info-complete-is-current-buffer-strip fn-psc-source-info-complete-resume-frame
    fn-psc-source-info-complete-is-actual-paid-steps fn-psc-model-byte-run fn-pbb-strip-info-at
    nth nthcdr len update-nth nfix))))))

(local (defthm fn-psc-source-byte-run-addition
 (implies (and (natp a) (natp b))
  (equal (fn-psc-model-byte-run (+ a b) c incoming held)
         (fn-psc-model-byte-run b (fn-psc-model-byte-run a c incoming held) incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run a c incoming held)
          :in-theory (e/d (fn-psc-model-byte-run)
                         (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

(local (defthm fn-psc-source-control-one-paid-step
 (implies (equal (fn-psc-get phase c) :control)
  (equal (fn-psc-model-byte-run 1 c incoming held) (fn-psc-step c nil)))
 :hints (("Goal" :expand ((fn-psc-model-byte-run 1 c incoming held)
                         (:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-model-demanded-byte fn-psc-demand)
   (fn-psc-model-byte-run fn-psc-model-source fn-psc-step nth len nfix))))))

(local (defthm fn-psc-source-simple-complete-is-actual-paid-steps
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-model-source-simple-complete pos c incoming held)
   (fn-psc-model-byte-run (fn-psc-model-source-simple-cost pos c incoming held)
                         (fn-psc-info-compare pos :source-info-simple c) incoming held)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-info-complete-is-actual-paid-steps (resume :source-info-simple))
        (:instance fn-psc-source-byte-run-addition (a (fn-psc-model-source-info-cost pos :source-info-simple c incoming held))
         (b (if (equal (fn-psc-get phase (fn-psc-model-source-info-complete pos :source-info-simple c incoming held)) :control) 1 0))
         (c (fn-psc-info-compare pos :source-info-simple c))))
  :expand ((:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-model-source-simple-complete fn-psc-model-source-simple-cost)
   (fn-psc-model-source-info-complete fn-psc-model-source-info-cost fn-psc-info-compare fn-psc-step
    fn-psc-source-info-complete-is-actual-paid-steps fn-psc-source-byte-run-addition fn-psc-source-simple-callback fn-psc-model-byte-run nth len nfix))))))

(local (defthm fn-psc-source-buffer-strip-success-index
 (implies (and (natp i) (true-listp prefix)
               (not (equal (fn-pbb-strip-at prefix i xs) :no)))
  (equal (fn-pbb-strip-at prefix i xs) (+ i (len prefix))))
 :hints (("Goal" :induct (fn-pbb-strip-at prefix i xs)
  :in-theory (e/d (fn-pbb-strip-at) (nth))))))

(local (defthm fn-psc-source-tail-length
 (implies (and (natp j) (<= j (len xs)))
  (equal (len (nthcdr j xs)) (- (len xs) j)))
 :hints (("Goal" :induct (nthcdr j xs) :in-theory (enable nthcdr len)))))

(local (defthm fn-psc-source-take-is-clamped-take
 (implies (true-listp xs)
  (equal (fn-inj-take k xs) (take (min (nfix k) (len xs)) xs)))
 :hints (("Goal" :induct (fn-inj-take k xs) :in-theory (enable fn-inj-take)))))

(local (defthm fn-psc-source-clamped-date-is-self-prefix
 (implies (and (natp j) (<= j (len xs)) (true-listp xs))
  (equal (fn-oct-slice-list j (min (+ j 31) (len xs)) xs)
         (fn-inj-take 31 (nthcdr j xs))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-oct-slice-list-is-take-nthcdr
          (i j) (n (min (+ j 31) (len xs))) (fn-octets xs)))
  :in-theory (disable fn-oct-slice-list fn-inj-take nthcdr take)))))

(defun fn-psc-model-source-after-path-complete (pos c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((d (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held))
        (e (fn-psc-step d nil)))
  (if (fn-psc-get ok d)
   (let* ((tail (fn-psc-model-comparison-complete e incoming held))
          (next (fn-psc-step tail nil)))
    (if (fn-psc-get ok tail)
     (fn-psc-model-source-after-stamp-complete (fn-psc-get pos next) next incoming held)
     next))
   (fn-psc-model-source-simple-complete pos e incoming held))))

(local (defthm fn-psc-source-stamp-control-preserves-context
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :control)
               (member-eq (fn-psc-get resume c) '(:source-stamp :source-stamp-tail)))
  (and (fn-psc-source-contextp (fn-psc-step c nil) incoming held)
       (equal (fn-psc-model-source (fn-psc-step c nil) incoming held) (fn-psc-model-source c incoming held))
       (equal (fn-psc-model-retained-agent (fn-psc-step c nil) incoming) (fn-psc-model-retained-agent c incoming))
       (equal (fn-psc-get msgid (fn-psc-step c nil)) (fn-psc-get msgid c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-contextp fn-psc-model-source fn-psc-model-retained-agent
             fn-psc-literal fn-psc-info-compare fn-psc-compare fn-psc-finish)
     (fn-psc-step nth nthcdr len update-nth nfix fn-inj-take))))))

(local (defthm fn-psc-source-stamp-tail-control-preserves-date-context
 (implies (and (fn-psc-source-date-contextp c incoming held)
               (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-stamp-tail))
  (and (fn-psc-source-date-contextp (fn-psc-step c nil) incoming held)
       (equal (fn-psc-model-captured-date (fn-psc-step c nil) incoming held)
              (fn-psc-model-captured-date c incoming held))))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-model-captured-date
             fn-psc-info-compare fn-psc-literal fn-psc-compare fn-psc-finish)
     (fn-psc-step nth nthcdr len update-nth nfix fn-inj-take))))))

(local (defthm fn-psc-source-stamp-success-prefix-frame
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held)))
               (not (equal (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held)) :no)))
  (let* ((d (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held))
         (e (fn-psc-step d nil))
         (q (fn-psc-model-comparison-complete e incoming held))
         (j (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held)))
         (r2 (fn-pbb-strip-at '(13 10) (+ j 31) (fn-psc-model-source c incoming held))))
   (and (equal (fn-psc-get phase q) :control)
        (equal (fn-psc-get resume q) :source-stamp-tail)
        (fn-psc-source-contextp q incoming held)
        (equal (fn-psc-get date q) j)
        (iff (fn-psc-get ok q) (not (equal r2 :no)))
        (implies (not (equal r2 :no))
         (and (equal (fn-psc-get pos q) r2) (fn-psc-source-date-contextp q incoming held)))
        (equal (fn-psc-model-source q incoming held) (fn-psc-model-source c incoming held))
        (equal (fn-psc-model-retained-agent q incoming) (fn-psc-model-retained-agent c incoming))
        (equal (fn-psc-get msgid q) (fn-psc-get msgid c)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-buffer-strip-success-index
         (i pos) (prefix *fn-inj-injection-date-field*) (xs (fn-psc-model-source c incoming held)))
        (:instance fn-psc-source-crlf-complete-establishes-captured-date
          (j (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held)))
          (c (fn-psc-set date (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held))
               (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held))))
        (:instance fn-psc-source-literal-complete-frame
           (bytes *fn-inj-injection-date-field*) (resume :source-stamp))
        (:instance fn-psc-source-literal-complete-frame
           (pos (+ 31 (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held))))
           (bytes '(13 10)) (resume :source-stamp-tail)
           (c (fn-psc-set date (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held))
                (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held)))))
  :in-theory (e/d (fn-psc-model-source-literal-complete fn-psc-source-contextp fn-psc-model-source
                   fn-psc-literal fn-psc-compare fn-psc-model-retained-agent nfix)
   (fn-psc-model-comparison-complete fn-psc-step fn-pbb-strip-at fn-inj-take nthcdr
    fn-psc-source-literal-complete-frame fn-psc-source-buffer-strip-success-index
    fn-psc-source-crlf-complete-establishes-captured-date fn-psc-comparison-next-is-actual-paid-trace nth len update-nth))))))

(local (defthm fn-psc-source-stamp-tail-next-frame
 (implies (and (fn-psc-source-date-contextp c incoming held)
               (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-stamp-tail)
               (fn-psc-get ok c) (natp (fn-psc-get pos c)))
  (let ((d (fn-psc-step c nil)))
   (and (fn-psc-source-date-contextp d incoming held)
        (equal (fn-psc-get pos d) (fn-psc-get pos c))
        (equal (fn-psc-model-source d incoming held) (fn-psc-model-source c incoming held))
        (equal (fn-psc-model-retained-agent d incoming) (fn-psc-model-retained-agent c incoming))
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-model-captured-date d incoming held) (fn-psc-model-captured-date c incoming held)))))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-date-contextp fn-psc-source-contextp
            fn-psc-model-source fn-psc-model-retained-agent fn-psc-model-captured-date
            fn-psc-info-compare fn-psc-literal fn-psc-compare)
   (fn-psc-step fn-inj-take nthcdr nth len update-nth))))))

(local (defthm fn-psc-source-context-has-proper-source
 (implies (fn-psc-source-contextp c incoming held)
  (true-listp (fn-psc-model-source c incoming held)))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-contextp) (fn-psc-model-source nth len))))))

(local (defthm fn-psc-source-stamp-good-next-frame
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos) (<= pos (len (fn-psc-model-source c incoming held)))
               (not (equal (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held)) :no)) (not (equal (fn-pbb-strip-at '(13 10) (+ 31 (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held))) (fn-psc-model-source c incoming held)) :no)))
  (let* ((field (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held)) (tail (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held)) (next (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held) nil)) (j (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held))) (r2 (fn-pbb-strip-at '(13 10) (+ 31 (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held))) (fn-psc-model-source c incoming held))))
   (and (fn-psc-get ok field) (fn-psc-get ok tail)
        (fn-psc-source-date-contextp next incoming held)
        (equal (fn-psc-get pos next) r2) (natp r2) (<= r2 (len (fn-psc-model-source c incoming held)))
        (equal (fn-psc-model-captured-date next incoming held)
               (fn-oct-slice-list j (min (+ j 31) (len (fn-psc-model-source c incoming held))) (fn-psc-model-source c incoming held)))
        (equal (fn-psc-model-source next incoming held) (fn-psc-model-source c incoming held))
        (equal (fn-psc-model-retained-agent next incoming) (fn-psc-model-retained-agent c incoming))
        (equal (fn-psc-get msgid next) (fn-psc-get msgid c)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-literal-complete-frame (bytes *fn-inj-injection-date-field*) (resume :source-stamp)) fn-psc-source-stamp-success-prefix-frame (:instance fn-psc-source-stamp-tail-next-frame (c (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held))) (:instance fn-psc-source-clamped-date-is-self-prefix (j (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held))) (xs (fn-psc-model-source c incoming held))) (:instance fn-pbb-strip-at-bounds (prefix *fn-inj-injection-date-field*) (i pos) (fn-octets (fn-psc-model-source c incoming held))) (:instance fn-pbb-strip-at-bounds (prefix '(13 10)) (i (+ 31 (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held)))) (fn-octets (fn-psc-model-source c incoming held))) (:instance fn-psc-source-buffer-strip-success-index (prefix '(13 10)) (i (+ 31 (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held)))) (xs (fn-psc-model-source c incoming held))) (:instance fn-psc-source-buffer-strip-success-index (prefix *fn-inj-injection-date-field*) (i pos) (xs (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-source-date-contextp fn-psc-model-captured-date)
   (fn-psc-source-contextp fn-psc-model-source fn-psc-model-retained-agent fn-psc-step
    fn-psc-model-source-literal-complete fn-psc-model-comparison-complete
    fn-pbb-strip-at fn-inj-take fn-oct-slice-list min nthcdr nth len update-nth nfix
    fn-psc-source-literal-complete-frame fn-psc-source-stamp-success-prefix-frame
    fn-psc-source-stamp-tail-next-frame fn-psc-source-clamped-date-is-self-prefix
    fn-psc-source-buffer-strip-success-index fn-psc-comparison-next-is-actual-paid-trace
    fn-psc-source-info-complete-is-actual-paid-steps (:linear fn-pbb-strip-at-bounds)))))))

(local (defthm fn-psc-source-after-path-no-stamp-is-current-buffer-inverse
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos) (<= pos (len (fn-psc-model-source c incoming held))) (equal (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held)) :no))
  (let* ((p (fn-pbb-source-after-path pos (fn-psc-model-retained-agent c incoming)
             (fn-record-string-octets (fn-psc-get msgid c)) (fn-psc-model-source c incoming held)))
         (d (fn-psc-model-source-after-path-complete pos c incoming held)))
   (and (equal (fn-psc-get phase d) (if p :control :done))
        (implies p (and (equal (fn-psc-get resume d) :source-found)
                        (equal (fn-psc-get pos d) p) (fn-psc-get ok d)))
        (implies (not p) (equal (fn-psc-result d) :no-source))
        (fn-psc-source-contextp d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-literal-complete-frame (bytes *fn-inj-injection-date-field*) (resume :source-stamp)) (:instance fn-psc-source-stamp-control-preserves-context (c (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held))) (:instance fn-psc-source-simple-complete-is-current-info-strip (c (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil))))
  :in-theory (e/d (fn-psc-model-source-after-path-complete fn-pbb-source-after-path fn-psc-result)
   (fn-record-string-octets fn-psc-source-contextp fn-psc-model-source fn-psc-model-retained-agent
    fn-psc-model-source-literal-complete fn-psc-model-comparison-complete fn-psc-step
    fn-psc-model-source-simple-complete fn-psc-model-source-after-stamp-complete
    fn-pbb-strip-at fn-pbb-strip-info-at fn-pbb-source-after-stamp fn-oct-slice-list min fn-inj-take nthcdr
    fn-psc-source-literal-complete-frame fn-psc-source-stamp-control-preserves-context
    fn-psc-source-simple-complete-is-current-info-strip fn-psc-source-stamp-success-prefix-frame
    fn-psc-source-stamp-tail-next-frame fn-psc-source-after-stamp-complete-is-current-buffer-inverse
    fn-psc-source-after-stamp-complete-preserves-context fn-psc-source-stamp-reference-is-fixed-skip
    fn-psc-source-clamped-date-is-self-prefix fn-psc-source-buffer-strip-success-index
    fn-psc-source-after-stamp-complete-is-actual-paid-steps fn-psc-source-simple-complete-is-actual-paid-steps
    fn-psc-source-info-complete-is-actual-paid-steps fn-psc-model-byte-run
    nth len update-nth nfix))))))

(local (defthm fn-psc-source-after-path-bad-stamp-is-current-buffer-inverse
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos) (<= pos (len (fn-psc-model-source c incoming held))) (not (equal (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held)) :no)) (equal (fn-pbb-strip-at '(13 10) (+ 31 (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held))) (fn-psc-model-source c incoming held)) :no))
  (let* ((p (fn-pbb-source-after-path pos (fn-psc-model-retained-agent c incoming)
             (fn-record-string-octets (fn-psc-get msgid c)) (fn-psc-model-source c incoming held)))
         (d (fn-psc-model-source-after-path-complete pos c incoming held)))
   (and (equal (fn-psc-get phase d) (if p :control :done))
        (implies p (and (equal (fn-psc-get resume d) :source-found)
                        (equal (fn-psc-get pos d) p) (fn-psc-get ok d)))
        (implies (not p) (equal (fn-psc-result d) :no-source))
        (fn-psc-source-contextp d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-literal-complete-frame (bytes *fn-inj-injection-date-field*) (resume :source-stamp)) fn-psc-source-stamp-success-prefix-frame (:instance fn-psc-source-stamp-control-preserves-context (c (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held))) (:instance fn-psc-source-stamp-reference-is-fixed-skip (xs (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-model-source-after-path-complete fn-pbb-source-after-path fn-psc-result fn-psc-finish fn-psc-source-contextp)
   (fn-record-string-octets fn-psc-model-source fn-psc-model-retained-agent
    fn-psc-model-source-literal-complete fn-psc-model-comparison-complete fn-psc-step
    fn-psc-model-source-simple-complete fn-psc-model-source-after-stamp-complete
    fn-pbb-strip-at fn-pbb-strip-info-at fn-pbb-source-after-stamp fn-oct-slice-list min fn-inj-take nthcdr
    fn-psc-source-literal-complete-frame fn-psc-source-stamp-control-preserves-context
    fn-psc-source-simple-complete-is-current-info-strip fn-psc-source-stamp-success-prefix-frame
    fn-psc-source-stamp-tail-next-frame fn-psc-source-after-stamp-complete-is-current-buffer-inverse
    fn-psc-source-after-stamp-complete-preserves-context fn-psc-source-stamp-reference-is-fixed-skip
    fn-psc-source-clamped-date-is-self-prefix fn-psc-source-buffer-strip-success-index
    fn-psc-source-after-stamp-complete-is-actual-paid-steps fn-psc-source-simple-complete-is-actual-paid-steps
    fn-psc-source-info-complete-is-actual-paid-steps fn-psc-model-byte-run
    nth len update-nth nfix))))))

(local (defthm fn-psc-source-after-path-good-stamp-is-current-buffer-inverse
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos) (<= pos (len (fn-psc-model-source c incoming held))) (not (equal (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held)) :no)) (not (equal (fn-pbb-strip-at '(13 10) (+ 31 (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held))) (fn-psc-model-source c incoming held)) :no)))
  (let* ((p (fn-pbb-source-after-path pos (fn-psc-model-retained-agent c incoming)
             (fn-record-string-octets (fn-psc-get msgid c)) (fn-psc-model-source c incoming held)))
         (d (fn-psc-model-source-after-path-complete pos c incoming held)))
   (and (equal (fn-psc-get phase d) (if p :control :done))
        (implies p (and (equal (fn-psc-get resume d) :source-found)
                        (equal (fn-psc-get pos d) p) (fn-psc-get ok d)))
        (implies (not p) (equal (fn-psc-result d) :no-source))
        (fn-psc-source-contextp d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-stamp-good-next-frame (:instance fn-psc-source-after-stamp-complete-is-current-buffer-inverse (pos (fn-psc-get pos (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held) nil))) (c (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held) nil))) (:instance fn-psc-source-after-stamp-complete-preserves-context (pos (fn-psc-get pos (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held) nil))) (c (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held) nil))) (:instance fn-psc-source-stamp-reference-is-fixed-skip (xs (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-model-source-after-path-complete fn-pbb-source-after-path)
   (fn-psc-source-stamp-good-next-frame fn-psc-source-contextp fn-psc-source-date-contextp fn-psc-model-captured-date fn-record-string-octets fn-psc-model-source fn-psc-model-retained-agent
    fn-psc-model-source-literal-complete fn-psc-model-comparison-complete fn-psc-step
    fn-psc-model-source-simple-complete fn-psc-model-source-after-stamp-complete
    fn-pbb-strip-at fn-pbb-strip-info-at fn-pbb-source-after-stamp fn-oct-slice-list min fn-inj-take nthcdr
    fn-psc-source-literal-complete-frame fn-psc-source-stamp-control-preserves-context
    fn-psc-source-simple-complete-is-current-info-strip fn-psc-source-stamp-success-prefix-frame
    fn-psc-source-stamp-tail-next-frame fn-psc-source-after-stamp-complete-is-current-buffer-inverse
    fn-psc-source-after-stamp-complete-preserves-context fn-psc-source-stamp-reference-is-fixed-skip
    fn-psc-source-clamped-date-is-self-prefix fn-psc-source-buffer-strip-success-index
    fn-psc-source-after-stamp-complete-is-actual-paid-steps fn-psc-source-simple-complete-is-actual-paid-steps
    fn-psc-source-info-complete-is-actual-paid-steps fn-psc-model-byte-run
    nth len update-nth nfix))))))

(defthm fn-psc-source-after-path-complete-is-current-buffer-inverse
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos) (<= pos (len (fn-psc-model-source c incoming held))))
  (let* ((p (fn-pbb-source-after-path pos (fn-psc-model-retained-agent c incoming)
             (fn-record-string-octets (fn-psc-get msgid c)) (fn-psc-model-source c incoming held)))
         (d (fn-psc-model-source-after-path-complete pos c incoming held)))
   (and (equal (fn-psc-get phase d) (if p :control :done))
        (implies p (and (equal (fn-psc-get resume d) :source-found)
                        (equal (fn-psc-get pos d) p) (fn-psc-get ok d)))
        (implies (not p) (equal (fn-psc-result d) :no-source))
        (fn-psc-source-contextp d incoming held))))
 :hints (("Goal" :do-not-induct t
  :cases ((equal (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held)) :no) (equal (fn-pbb-strip-at '(13 10) (+ 31 (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held))) (fn-psc-model-source c incoming held)) :no))
  :use (fn-psc-source-after-path-no-stamp-is-current-buffer-inverse
        fn-psc-source-after-path-bad-stamp-is-current-buffer-inverse
        fn-psc-source-after-path-good-stamp-is-current-buffer-inverse)
  :in-theory (disable fn-psc-model-source-after-path-complete fn-pbb-source-after-path
    fn-psc-source-contextp fn-psc-model-source fn-psc-model-retained-agent
    fn-pbb-strip-at fn-psc-result nth len
    fn-psc-source-after-path-no-stamp-is-current-buffer-inverse
    fn-psc-source-after-path-bad-stamp-is-current-buffer-inverse
    fn-psc-source-after-path-good-stamp-is-current-buffer-inverse))))

(defun fn-psc-model-source-after-path-cost (pos c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((field (fn-psc-literal pos *fn-inj-injection-date-field* :source-stamp c))
        (d (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held))
        (e (fn-psc-step d nil)))
  (+ 1 (fn-psc-model-comparison-cost field incoming held)
   (if (fn-psc-get ok d)
    (let* ((tail (fn-psc-model-comparison-complete e incoming held))
           (next (fn-psc-step tail nil)))
     (+ 1 (fn-psc-model-comparison-cost e incoming held)
      (if (fn-psc-get ok tail)
       (fn-psc-model-source-after-stamp-cost (fn-psc-get pos next) next incoming held)
       0)))
    (fn-psc-model-source-simple-cost pos e incoming held)))))

(local (defthm fn-psc-source-literal-next-is-actual-paid-steps
 (equal (fn-psc-step (fn-psc-model-source-literal-complete pos bytes resume c incoming held) nil)
        (fn-psc-model-byte-run (+ 1 (fn-psc-model-comparison-cost (fn-psc-literal pos bytes resume c) incoming held))
                              (fn-psc-literal pos bytes resume c) incoming held))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-next-is-actual-paid-trace (c (fn-psc-literal pos bytes resume c))))
  :in-theory (e/d (fn-psc-model-source-literal-complete fn-psc-literal fn-psc-compare fn-psc-comparison-statep)
   (fn-psc-comparison-next-is-actual-paid-trace fn-psc-model-comparison-complete fn-psc-model-comparison-cost
    fn-psc-step fn-psc-model-byte-run nth len nfix update-nth))))))

(local (defthm fn-psc-source-cdr-update-positive
 (implies (posp i)
  (equal (cdr (update-nth i value c)) (update-nth (1- i) value (cdr c))))
 :hints (("Goal" :expand ((update-nth i value c)) :in-theory (enable posp nfix)))))

(local (defthm fn-psc-source-update-overwrites
 (implies (natp i)
  (equal (update-nth i a (update-nth i b c)) (update-nth i a c)))
 :hints (("Goal" :induct (update-nth i b c) :in-theory (enable update-nth)))))

(local (defun fn-psc-source-update-induct (i j c)
 (declare (xargs :guard t :verify-guards nil :measure (nfix i)))
 (if (or (zp i) (zp j)) c (fn-psc-source-update-induct (1- i) (1- j) (cdr c)))))

(local (defthm fn-psc-source-update-order
 (implies (and (natp i) (natp j) (< i j))
  (equal (update-nth j b (update-nth i a c)) (update-nth i a (update-nth j b c))))
 :hints (("Goal" :induct (fn-psc-source-update-induct i j c)
  :in-theory (enable fn-psc-source-update-induct update-nth)))))

(local (defthm fn-psc-source-update-order-by-index
 (implies (and (natp i) (natp j) (< i j))
  (equal (update-nth j b (update-nth i a c)) (update-nth i a (update-nth j b c))))
 :rule-classes ((:rewrite :loop-stopper nil))
 :hints (("Goal" :use fn-psc-source-update-order :in-theory (disable fn-psc-source-update-order update-nth)))))

(local (defthm fn-psc-source-info-constructor-is-idempotent
 (equal (fn-psc-info-compare (fn-psc-get pos (fn-psc-info-compare pos resume c)) resume
          (fn-psc-info-compare pos resume c))
        (fn-psc-info-compare pos resume c))
 :hints (("Goal" :in-theory (e/d (fn-psc-info-compare fn-psc-literal fn-psc-compare nfix)
  (nth len update-nth))))))

(local (defthm fn-psc-source-info-constructor-natural-is-idempotent
 (implies (natp pos)
  (equal (fn-psc-info-compare pos resume (fn-psc-info-compare pos resume c))
         (fn-psc-info-compare pos resume c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-info-compare fn-psc-literal fn-psc-compare nfix) (nth len update-nth))))))

(local (defthm fn-psc-source-after-path-no-stamp-is-actual-paid-steps
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos) (<= pos (len (fn-psc-model-source c incoming held)))
               (equal (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held)) :no))
  (equal (fn-psc-model-source-after-path-complete pos c incoming held)
    (fn-psc-model-byte-run (fn-psc-model-source-after-path-cost pos c incoming held)
        (fn-psc-literal pos *fn-inj-injection-date-field* :source-stamp c) incoming held)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-literal-complete-frame (bytes *fn-inj-injection-date-field*) (resume :source-stamp)) (:instance fn-psc-source-stamp-control-preserves-context (c (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held))) (:instance fn-psc-source-literal-next-is-actual-paid-steps (bytes *fn-inj-injection-date-field*) (resume :source-stamp)) (:instance fn-psc-source-byte-run-addition (a (+ 1 (fn-psc-model-comparison-cost (fn-psc-literal pos *fn-inj-injection-date-field* :source-stamp c) incoming held))) (b (fn-psc-model-source-simple-cost pos (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held)) (c (fn-psc-literal pos *fn-inj-injection-date-field* :source-stamp c))) (:instance fn-psc-source-simple-complete-is-actual-paid-steps (c (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil))))
  :in-theory (e/d (fn-psc-model-source-after-path-complete fn-psc-model-source-after-path-cost nfix)
   (fn-psc-model-source-literal-complete fn-psc-model-comparison-complete fn-psc-model-comparison-cost
    fn-psc-model-source-simple-complete fn-psc-model-source-simple-cost fn-psc-model-source-after-stamp-complete
    fn-psc-step fn-psc-literal fn-psc-info-compare fn-psc-source-contextp fn-psc-model-source
    fn-psc-source-literal-complete-frame fn-psc-source-stamp-control-preserves-context
    fn-psc-source-literal-next-is-actual-paid-steps fn-psc-source-byte-run-addition
    fn-psc-source-simple-complete-is-actual-paid-steps fn-psc-model-byte-run
    fn-psc-comparison-next-is-actual-paid-trace nth len update-nth))))))

(local (defthm fn-psc-source-stamp-tail-issued-info-initializer-is-self
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-stamp-tail)
               (fn-psc-get ok c) (natp (fn-psc-get pos c)))
  (let ((d (fn-psc-step c nil)))
   (equal (fn-psc-info-compare (fn-psc-get pos d) :source-info-v1 (fn-psc-set k (fn-psc-get pos d) d)) d)))
 :hints (("Goal" :in-theory (e/d (fn-psc-info-compare fn-psc-literal fn-psc-compare nfix)
   (fn-psc-step nth len update-nth))))))

(local (defthm fn-psc-source-stamp-after-tail-is-actual-issued-paid-steps
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos) (<= pos (len (fn-psc-model-source c incoming held)))
               (not (equal (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held)) :no)) (not (equal (fn-pbb-strip-at '(13 10) (+ 31 (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held))) (fn-psc-model-source c incoming held)) :no)))
  (equal (fn-psc-model-source-after-stamp-complete (fn-psc-get pos (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held) nil)) (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held) nil) incoming held)
   (fn-psc-model-byte-run (fn-psc-model-source-after-stamp-cost (fn-psc-get pos (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held) nil)) (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held) nil) incoming held)
                         (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held) nil) incoming held)))
 :hints (("Goal" :do-not-induct t :use (fn-psc-source-stamp-good-next-frame fn-psc-source-stamp-success-prefix-frame (:instance fn-psc-source-stamp-tail-issued-info-initializer-is-self (c (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held))) (:instance fn-psc-source-after-stamp-complete-is-actual-paid-steps (pos (fn-psc-get pos (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held) nil))) (c (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held) nil))))
  :in-theory (disable fn-psc-source-contextp fn-psc-model-source fn-psc-source-date-contextp
    fn-psc-model-source-literal-complete fn-psc-model-comparison-complete fn-psc-model-source-after-stamp-complete
    fn-psc-model-source-after-stamp-cost fn-psc-step fn-psc-info-compare fn-psc-model-byte-run fn-pbb-strip-at
    fn-psc-source-stamp-good-next-frame fn-psc-source-stamp-success-prefix-frame
    fn-psc-source-stamp-tail-issued-info-initializer-is-self fn-psc-source-after-stamp-complete-is-actual-paid-steps
    nth len nfix update-nth)))))

(local (defthm fn-psc-source-stamp-tail-entry-is-comparison
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held)))
               (not (equal (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held)) :no)))
  (let ((d (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil)))
   (and (equal (fn-psc-get phase d) :compare) (fn-psc-comparison-statep d))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-literal-complete-frame (bytes *fn-inj-injection-date-field*) (resume :source-stamp)))
  :in-theory (e/d (fn-psc-literal fn-psc-compare fn-psc-comparison-statep)
   (fn-psc-model-source-literal-complete fn-psc-step fn-psc-source-contextp fn-psc-model-source
    fn-psc-source-literal-complete-frame fn-psc-source-literal-next-is-actual-paid-steps
    fn-pbb-strip-at nth len nfix update-nth))))))

(local (defthm fn-psc-source-stamp-tail-next-is-actual-paid-steps
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held)))
               (not (equal (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held)) :no)))
  (let ((d (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil)))
   (equal (fn-psc-step (fn-psc-model-comparison-complete d incoming held) nil)
          (fn-psc-model-byte-run (+ 1 (fn-psc-model-comparison-cost d incoming held)) d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-stamp-tail-entry-is-comparison
        (:instance fn-psc-comparison-next-is-actual-paid-trace
         (c (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil))))
  :in-theory (disable fn-psc-model-source-literal-complete fn-psc-step fn-psc-source-contextp fn-psc-model-source
    fn-psc-source-stamp-tail-entry-is-comparison fn-psc-comparison-next-is-actual-paid-trace
    fn-psc-source-literal-next-is-actual-paid-steps fn-pbb-strip-at fn-psc-model-comparison-complete
    fn-psc-model-comparison-cost fn-psc-model-byte-run fn-psc-comparison-statep nth len nfix update-nth)))))

(local (defthm fn-psc-source-after-path-stamp-is-actual-paid-steps
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos) (<= pos (len (fn-psc-model-source c incoming held)))
               (not (equal (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held)) :no)))
  (equal (fn-psc-model-source-after-path-complete pos c incoming held)
    (fn-psc-model-byte-run (fn-psc-model-source-after-path-cost pos c incoming held)
        (fn-psc-literal pos *fn-inj-injection-date-field* :source-stamp c) incoming held)))
 :hints (("Goal" :do-not-induct t :cases ((equal (fn-pbb-strip-at '(13 10) (+ 31 (fn-pbb-strip-at *fn-inj-injection-date-field* pos (fn-psc-model-source c incoming held))) (fn-psc-model-source c incoming held)) :no))
  :use ((:instance fn-psc-source-literal-complete-frame (bytes *fn-inj-injection-date-field*) (resume :source-stamp)) fn-psc-source-stamp-success-prefix-frame (:instance fn-psc-source-literal-next-is-actual-paid-steps (bytes *fn-inj-injection-date-field*) (resume :source-stamp)) fn-psc-source-stamp-tail-next-is-actual-paid-steps fn-psc-source-stamp-after-tail-is-actual-issued-paid-steps (:instance fn-psc-source-byte-run-addition (a (+ 1 (fn-psc-model-comparison-cost (fn-psc-literal pos *fn-inj-injection-date-field* :source-stamp c) incoming held))) (b (+ (+ 1 (fn-psc-model-comparison-cost (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held)) (if (fn-psc-get ok (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held)) (fn-psc-model-source-after-stamp-cost (fn-psc-get pos (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held) nil)) (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held) nil) incoming held) 0))) (c (fn-psc-literal pos *fn-inj-injection-date-field* :source-stamp c))) (:instance fn-psc-source-byte-run-addition (a (+ 1 (fn-psc-model-comparison-cost (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held))) (b (if (fn-psc-get ok (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held)) (fn-psc-model-source-after-stamp-cost (fn-psc-get pos (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held) nil)) (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil) incoming held) nil) incoming held) 0)) (c (fn-psc-step (fn-psc-model-source-literal-complete pos *fn-inj-injection-date-field* :source-stamp c incoming held) nil))))
  :expand ((:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-model-source-after-path-complete fn-psc-model-source-after-path-cost)
   (fn-psc-model-source-literal-complete fn-psc-model-comparison-complete fn-psc-model-comparison-cost
    fn-psc-model-source-after-stamp-complete fn-psc-model-source-after-stamp-cost
    fn-psc-step fn-psc-literal fn-psc-info-compare fn-psc-source-contextp fn-psc-model-source
    fn-psc-source-literal-complete-frame fn-psc-source-stamp-success-prefix-frame
    fn-psc-source-literal-next-is-actual-paid-steps fn-psc-source-byte-run-addition
    fn-psc-source-stamp-tail-next-is-actual-paid-steps fn-psc-source-stamp-after-tail-is-actual-issued-paid-steps
    fn-psc-source-after-stamp-complete-is-actual-paid-steps fn-psc-model-byte-run
    fn-pbb-strip-at fn-psc-comparison-next-is-actual-paid-trace nth len update-nth nfix
    (:linear fn-pbb-strip-at-bounds)))))))

(defthm fn-psc-source-after-path-complete-is-actual-paid-steps
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos) (<= pos (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-model-source-after-path-complete pos c incoming held)
    (fn-psc-model-byte-run (fn-psc-model-source-after-path-cost pos c incoming held)
        (fn-psc-literal pos *fn-inj-injection-date-field* :source-stamp c) incoming held)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-after-path-no-stamp-is-actual-paid-steps fn-psc-source-after-path-stamp-is-actual-paid-steps)
  :in-theory (disable fn-psc-model-source-after-path-complete fn-psc-model-source-after-path-cost
    fn-psc-model-source fn-psc-source-contextp fn-psc-model-byte-run fn-psc-literal nth len
    fn-psc-source-after-path-no-stamp-is-actual-paid-steps fn-psc-source-after-path-stamp-is-actual-paid-steps))))

(in-theory (disable fn-psc-model-source-after-path-complete fn-psc-model-source-after-path-cost))
