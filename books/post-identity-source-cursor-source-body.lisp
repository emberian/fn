(in-package "ACL2")

(include-book "post-identity-source-cursor-source-path")

(local (include-book "arithmetic/top" :dir :system))

(defun fn-psc-model-source-body-complete (pos c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((prefix (fn-psc-model-source-path-prefix-complete pos c incoming held))
        (recipe (fn-psc-model-source-after-path-complete (fn-psc-get base prefix) prefix incoming held)))
  (if (equal (fn-psc-get phase recipe) :control)
   (let ((next (fn-psc-step recipe nil)))
    (if (fn-psc-get has-path recipe) next (fn-psc-model-v3-unsplice-complete next incoming held)))
   recipe)))

(defun fn-psc-model-source-body-cost (pos c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((prefix (fn-psc-model-source-path-prefix-complete pos c incoming held))
        (recipe (fn-psc-model-source-after-path-complete (fn-psc-get base prefix) prefix incoming held)))
  (+ (fn-psc-model-source-path-prefix-cost pos c incoming held)
     (fn-psc-model-source-after-path-cost (fn-psc-get base prefix) prefix incoming held)
     (if (equal (fn-psc-get phase recipe) :control)
      (+ 1 (if (fn-psc-get has-path recipe) 0
       (fn-psc-model-v3-unsplice-cost (fn-psc-step recipe nil) incoming held))) 0))))

(local (defthm fn-psc-source-byte-run-addition
 (implies (and (natp a) (natp b))
  (equal (fn-psc-model-byte-run (+ a b) c incoming held)
         (fn-psc-model-byte-run b (fn-psc-model-byte-run a c incoming held) incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run a c incoming held)
          :in-theory (e/d (fn-psc-model-byte-run)
                         (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

(local (defthm fn-psc-source-found-callback
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-found))
  (equal (fn-psc-step c nil)
   (if (fn-psc-get has-path c)
    (fn-psc-finish (list :source (nfix (fn-psc-get pos c)) (nfix (fn-psc-get pos c)) (nfix (fn-psc-get pos c))) c)
    (fn-psc-set phase :path-scan (fn-psc-set k (nfix (fn-psc-get pos c))
     (fn-psc-set prev :bol (fn-psc-set aux t c)))))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control)
   (fn-psc-finish nth len update-nth nfix))))))

(local (defthm fn-psc-source-found-enters-v3-context
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-found)
               (not (fn-psc-get has-path c)) (natp (fn-psc-get pos c))
               (<= (fn-psc-get pos c) (len (fn-psc-model-source c incoming held))))
  (let ((d (fn-psc-step c nil)))
   (and (fn-psc-path-finder-statep d incoming held) (equal (fn-psc-get phase d) :path-scan)
        (fn-psc-get aux d) (equal (fn-psc-get k d) (fn-psc-get pos d))
        (fn-psc-source-contextp d incoming held)
        (equal (fn-psc-model-retained-agent d incoming) (fn-psc-model-retained-agent c incoming))
        (equal (fn-psc-model-source d incoming held) (fn-psc-model-source c incoming held)))))
 :hints (("Goal" :in-theory (e/d (fn-psc-path-finder-statep fn-psc-line-statep fn-psc-source-contextp
                           fn-psc-model-source fn-psc-model-retained-agent nfix)
  (fn-psc-step nth len update-nth))))))

(local (defthm fn-psc-source-found-step-keeps-source-position
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-found))
  (equal (fn-psc-get pos (fn-psc-step c nil)) (fn-psc-get pos c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-finish) (fn-psc-step nth len update-nth nfix))))))

(local (defthm fn-psc-source-found-unsplice-result-is-current-buffer-inverse
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :control) (equal (fn-psc-get resume c) :source-found)
               (not (fn-psc-get has-path c)) (natp (fn-psc-get pos c))
               (<= (fn-psc-get pos c) (len (fn-psc-model-source c incoming held))))
  (let ((desc (fn-pbb-unsplice-at (fn-psc-get pos c) (fn-psc-model-retained-agent c incoming)
                                 (fn-psc-model-source c incoming held))))
   (equal (fn-psc-result (fn-psc-model-v3-unsplice-complete (fn-psc-step c nil) incoming held))
          (if desc (cons :source desc) :no-source))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-found-enters-v3-context
        (:instance fn-psc-model-v3-unsplice-is-current-buffer-parser (c (fn-psc-step c nil))))
  :in-theory (e/d (fn-psc-source-contextp fn-psc-model-retained-agent)
   (fn-psc-step fn-psc-model-source fn-psc-model-v3-unsplice-complete fn-psc-result fn-pbb-unsplice-at
    fn-psc-source-found-enters-v3-context fn-psc-model-v3-unsplice-is-current-buffer-parser
    fn-psc-source-found-callback fn-psc-model-v3-unsplice-unfolds fn-psc-path-finder-complete-is-actual-steps
    fn-psc-v3-unsplice-complete-is-actual-steps nth len))))))

(local (defthm fn-psc-source-found-generated-result-is-current-descriptor
 (implies (and (equal (fn-psc-get phase c) :control) (equal (fn-psc-get resume c) :source-found)
               (fn-psc-get has-path c) (natp (fn-psc-get pos c)))
  (and (equal (fn-psc-get phase (fn-psc-step c nil)) :done)
       (equal (fn-psc-result (fn-psc-step c nil))
              (list :source (fn-psc-get pos c) (fn-psc-get pos c) (fn-psc-get pos c)))))
 :hints (("Goal" :in-theory (e/d (fn-psc-finish fn-psc-result nfix)
   (fn-psc-step nth len update-nth))))))

(local (defthm fn-psc-source-body-prefix-base-is-bounded
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held)))
               (equal (fn-psc-get skip c) pos))
  (let ((d (fn-psc-model-source-path-prefix-complete pos c incoming held)))
   (and (natp (fn-psc-get base d))
        (<= (fn-psc-get base d) (len (fn-psc-model-source d incoming held))))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-path-prefix-complete-frame
        (:instance fn-pbb-strip-at-bounds (i pos)
          (prefix (fn-inj-path-line (fn-psc-model-retained-agent c incoming)))
          (fn-octets (fn-psc-model-source c incoming held))))
  :in-theory (e/d (natp)
   (fn-psc-model-source-path-prefix-complete fn-psc-source-contextp fn-psc-model-source fn-psc-model-retained-agent
    fn-psc-source-path-prefix-complete-is-paid-steps fn-psc-model-source-path-prefix-cost fn-pbb-strip-at fn-inj-path-line fn-psc-source-path-prefix-complete-frame fn-pbb-strip-at-bounds nth len))))))

(local (defthm fn-psc-source-body-recipe-frame
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))) (equal (fn-psc-get skip c) pos))
  (let* ((d (fn-psc-model-source-after-path-complete (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held)) (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming held)) (path (fn-pbb-strip-at (fn-inj-path-line (fn-psc-model-retained-agent c incoming)) pos (fn-psc-model-source c incoming held))) (k (fn-pbb-source-after-path (if (equal (fn-pbb-strip-at (fn-inj-path-line (fn-psc-model-retained-agent c incoming)) pos (fn-psc-model-source c incoming held)) :no) pos (fn-pbb-strip-at (fn-inj-path-line (fn-psc-model-retained-agent c incoming)) pos (fn-psc-model-source c incoming held))) (fn-psc-model-retained-agent c incoming) (fn-record-string-octets (fn-psc-get msgid c)) (fn-psc-model-source c incoming held))))
   (and (equal (fn-psc-get phase d) (if k :control :done))
        (implies k (and (equal (fn-psc-get resume d) :source-found) (equal (fn-psc-get pos d) k)
                       (fn-psc-get ok d) (natp k) (<= k (len (fn-psc-model-source c incoming held)))))
        (implies (not k) (equal (fn-psc-result d) :no-source))
        (fn-psc-source-contextp d incoming held)
        (equal (fn-psc-model-source d incoming held) (fn-psc-model-source c incoming held))
        (equal (fn-psc-model-retained-agent d incoming) (fn-psc-model-retained-agent c incoming))
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (iff (fn-psc-get has-path d) (not (equal path :no))))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-path-prefix-complete-frame fn-psc-source-path-prefix-complete-configuration-frame
        fn-psc-source-body-prefix-base-is-bounded
        (:instance fn-psc-source-after-path-complete-is-current-buffer-inverse (pos (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held))) (c (fn-psc-model-source-path-prefix-complete pos c incoming held)))
        (:instance fn-psc-source-after-path-complete-keeps-source-agent-and-msgid (pos (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held))) (c (fn-psc-model-source-path-prefix-complete pos c incoming held)))
        (:instance fn-psc-source-after-path-complete-preserves-generated-path-flag (pos (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held))) (c (fn-psc-model-source-path-prefix-complete pos c incoming held)))
        (:instance fn-pbb-source-after-path-bounds (r1 (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held)))
          (agent (fn-psc-model-retained-agent (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming))
          (msgid (fn-record-string-octets (fn-psc-get msgid (fn-psc-model-source-path-prefix-complete pos c incoming held))))
          (fn-octets (fn-psc-model-source (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming held))))
  :in-theory (e/d (fn-psc-configuration natp)
   (fn-psc-model-source-path-prefix-complete fn-psc-model-source-after-path-complete fn-psc-source-contextp
    fn-psc-model-source fn-psc-model-retained-agent fn-record-string-octets fn-psc-result
    fn-pbb-strip-at fn-inj-path-line fn-pbb-source-after-path
    fn-psc-source-path-prefix-complete-frame fn-psc-source-path-prefix-complete-configuration-frame
    fn-psc-source-body-prefix-base-is-bounded fn-psc-source-after-path-complete-is-current-buffer-inverse
    fn-psc-source-after-path-complete-keeps-source-agent-and-msgid
    fn-psc-source-after-path-complete-preserves-generated-path-flag fn-pbb-source-after-path-bounds
    fn-psc-source-path-prefix-complete-is-paid-steps fn-psc-source-after-path-complete-is-actual-paid-steps nth len))))))

(defthm fn-psc-source-body-complete-is-current-buffer-source-index
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held)))
               (equal (fn-psc-get skip c) pos)
               (equal pos (fn-pbb-skip-at (fn-psc-model-source c incoming held))))
  (let ((desc (fn-pbb-source-index (fn-psc-model-retained-agent c incoming)
                 (fn-record-string-octets (fn-psc-get msgid c)) (fn-psc-model-source c incoming held))))
   (equal (fn-psc-result (fn-psc-model-source-body-complete pos c incoming held))
          (if desc (cons :source desc) :no-source))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-body-recipe-frame
        (:instance fn-psc-source-found-generated-result-is-current-descriptor (c (fn-psc-model-source-after-path-complete (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held)) (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming held)))
        (:instance fn-psc-source-found-unsplice-result-is-current-buffer-inverse (c (fn-psc-model-source-after-path-complete (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held)) (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming held))))
  :in-theory (e/d (fn-psc-model-source-body-complete fn-pbb-source-index)
   (fn-psc-model-source-path-prefix-complete fn-psc-model-source-after-path-complete fn-psc-model-v3-unsplice-complete
    fn-psc-source-contextp fn-psc-model-source fn-psc-model-retained-agent fn-record-string-octets
    fn-pbb-skip-at fn-pbb-strip-at fn-inj-path-line fn-pbb-source-after-path fn-pbb-unsplice-at fn-psc-result fn-psc-step
    fn-psc-source-body-recipe-frame fn-psc-source-found-generated-result-is-current-descriptor
    fn-psc-source-found-unsplice-result-is-current-buffer-inverse fn-psc-source-found-callback
    fn-psc-model-v3-unsplice-unfolds fn-psc-path-finder-complete-is-actual-steps
    fn-psc-source-path-prefix-complete-frame fn-psc-source-after-path-complete-is-current-buffer-inverse
    fn-psc-source-after-path-complete-keeps-source-agent-and-msgid
    fn-psc-source-after-path-complete-preserves-generated-path-flag
    fn-psc-source-path-prefix-complete-is-paid-steps fn-psc-source-after-path-complete-is-actual-paid-steps
    fn-psc-v3-unsplice-complete-is-actual-steps nth len nfix)))))

(local (defthm fn-psc-nonpending-result-forces-done-by-definition
 (implies (not (equal (fn-psc-result c) :pending))
  (equal (fn-psc-get phase c) :done))
 :hints (("Goal" :in-theory (enable fn-psc-result)))))

(defthm fn-psc-source-body-complete-is-terminal-with-current-descriptor
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held)))
               (equal (fn-psc-get skip c) pos)
               (equal pos (fn-pbb-skip-at (fn-psc-model-source c incoming held))))
  (let ((d (fn-psc-model-source-body-complete pos c incoming held)))
   (and (equal (fn-psc-get phase d) :done)
        (or (equal (fn-psc-result d) :no-source)
            (and (equal (car (fn-psc-result d)) :source)
                 (fn-pbb-descp (cdr (fn-psc-result d)) (len (fn-psc-model-source c incoming held))))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-nonpending-result-forces-done-by-definition (c (fn-psc-model-source-body-complete pos c incoming held)))
        fn-psc-source-body-complete-is-current-buffer-source-index
        (:instance fn-pbb-source-index-bounds
          (agent (fn-psc-model-retained-agent c incoming))
          (msgid (fn-record-string-octets (fn-psc-get msgid c)))
          (fn-octets (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-source-contextp)
   (fn-psc-model-source-body-complete fn-psc-model-source fn-psc-model-retained-agent fn-record-string-octets
    fn-psc-nonpending-result-forces-done-by-definition fn-psc-done-result-is-stored fn-pbb-source-index fn-pbb-descp fn-pbb-skip-at fn-psc-result
    fn-psc-source-body-complete-is-current-buffer-source-index fn-pbb-source-index-bounds nth len)))))

(local (defthm fn-psc-source-control-one-paid-step
 (implies (equal (fn-psc-get phase c) :control)
  (equal (fn-psc-model-byte-run 1 c incoming held) (fn-psc-step c nil)))
 :hints (("Goal" :expand ((fn-psc-model-byte-run 1 c incoming held)
                         (:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-model-demanded-byte fn-psc-demand)
   (fn-psc-model-byte-run fn-psc-model-source fn-psc-step nth len nfix))))))

(local (defthm fn-psc-source-body-recipe-is-actual-paid-steps
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))) (equal (fn-psc-get skip c) pos))
  (equal (fn-psc-model-source-after-path-complete (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held)) (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming held) (fn-psc-model-byte-run (+ (fn-psc-model-source-path-prefix-cost pos c incoming held) (fn-psc-model-source-after-path-cost (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held)) (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming held)) (fn-psc-literal pos *fn-inj-path-field* :source-path-field c) incoming held)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-path-prefix-complete-frame fn-psc-source-body-prefix-base-is-bounded
        fn-psc-source-path-prefix-issued-stamp-initializer-is-self
        fn-psc-source-path-prefix-complete-is-paid-steps
        (:instance fn-psc-source-after-path-complete-is-actual-paid-steps (pos (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held))) (c (fn-psc-model-source-path-prefix-complete pos c incoming held)))
        (:instance fn-psc-source-byte-run-addition (a (fn-psc-model-source-path-prefix-cost pos c incoming held)) (b (fn-psc-model-source-after-path-cost (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held)) (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming held)) (c (fn-psc-literal pos *fn-inj-path-field* :source-path-field c))))
  :in-theory (disable fn-psc-model-source-path-prefix-complete fn-psc-model-source-path-prefix-cost
    fn-psc-model-source-after-path-complete fn-psc-model-source-after-path-cost fn-psc-model-byte-run fn-psc-literal
    fn-psc-source-contextp fn-psc-model-source fn-psc-source-path-prefix-complete-frame
    fn-psc-source-body-prefix-base-is-bounded fn-psc-source-path-prefix-issued-stamp-initializer-is-self
    fn-psc-source-path-prefix-complete-is-paid-steps fn-psc-source-after-path-complete-is-actual-paid-steps
    fn-psc-source-byte-run-addition nth len nfix)))))

(defthm fn-psc-source-body-complete-is-actual-paid-steps
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))) (equal (fn-psc-get skip c) pos))
  (equal (fn-psc-model-source-body-complete pos c incoming held)
         (fn-psc-model-byte-run (fn-psc-model-source-body-cost pos c incoming held) (fn-psc-literal pos *fn-inj-path-field* :source-path-field c) incoming held)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-body-recipe-frame fn-psc-source-body-recipe-is-actual-paid-steps
        (:instance fn-psc-source-found-enters-v3-context (c (fn-psc-model-source-after-path-complete (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held)) (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming held)))
        (:instance fn-psc-v3-unsplice-complete-is-actual-steps (c (fn-psc-step (fn-psc-model-source-after-path-complete (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held)) (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming held) nil)))
        (:instance fn-psc-source-control-one-paid-step (c (fn-psc-model-source-after-path-complete (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held)) (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming held)))
        (:instance fn-psc-source-byte-run-addition (a (+ (fn-psc-model-source-path-prefix-cost pos c incoming held) (fn-psc-model-source-after-path-cost (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held)) (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming held))) (b (if (equal (fn-psc-get phase (fn-psc-model-source-after-path-complete (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held)) (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming held)) :control) (+ 1 (if (fn-psc-get has-path (fn-psc-model-source-after-path-complete (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held)) (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming held)) 0 (fn-psc-model-v3-unsplice-cost (fn-psc-step (fn-psc-model-source-after-path-complete (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held)) (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming held) nil) incoming held))) 0)) (c (fn-psc-literal pos *fn-inj-path-field* :source-path-field c)))
        (:instance fn-psc-source-byte-run-addition (a 1)
          (b (if (fn-psc-get has-path (fn-psc-model-source-after-path-complete (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held)) (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming held)) 0 (fn-psc-model-v3-unsplice-cost (fn-psc-step (fn-psc-model-source-after-path-complete (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held)) (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming held) nil) incoming held))) (c (fn-psc-model-source-after-path-complete (fn-psc-get base (fn-psc-model-source-path-prefix-complete pos c incoming held)) (fn-psc-model-source-path-prefix-complete pos c incoming held) incoming held))))
  :expand ((:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-model-source-body-complete fn-psc-model-source-body-cost)
   (fn-psc-model-source-path-prefix-complete fn-psc-model-source-path-prefix-cost
    fn-psc-model-source-after-path-complete fn-psc-model-source-after-path-cost
    fn-psc-model-v3-unsplice-complete fn-psc-model-v3-unsplice-cost fn-psc-model-byte-run fn-psc-step fn-psc-literal
    fn-psc-source-contextp fn-psc-model-source fn-psc-model-retained-agent fn-record-string-octets
    fn-psc-source-body-recipe-frame fn-psc-source-body-recipe-is-actual-paid-steps
    fn-psc-source-found-enters-v3-context fn-psc-v3-unsplice-complete-is-actual-steps
    fn-psc-source-control-one-paid-step fn-psc-source-byte-run-addition fn-psc-source-found-callback
    fn-psc-model-v3-unsplice-unfolds fn-psc-path-finder-complete-is-actual-steps
    fn-psc-source-after-path-complete-is-current-buffer-inverse fn-psc-source-path-prefix-complete-is-paid-steps
    fn-psc-source-after-path-complete-is-actual-paid-steps nth len nfix)))))
