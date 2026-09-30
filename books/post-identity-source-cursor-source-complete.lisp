(in-package "ACL2")

(include-book "post-identity-source-cursor-source-body")

(include-book "post-identity-source-cursor-skip")

(local (include-book "arithmetic/top" :dir :system))

(defun fn-psc-model-source-complete (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((skip (fn-psc-model-skip-complete c incoming held)) (entry (fn-psc-step skip nil)))
  (fn-psc-model-source-body-complete (fn-psc-get pos skip) entry incoming held)))

(defun fn-psc-model-source-cost (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((skip (fn-psc-model-skip-complete c incoming held)) (entry (fn-psc-step skip nil)))
  (+ (fn-psc-model-skip-cost c incoming held) 1
     (fn-psc-model-source-body-cost (fn-psc-get pos skip) entry incoming held))))

(local (defthm fn-psc-source-byte-run-addition
 (implies (and (natp a) (natp b))
  (equal (fn-psc-model-byte-run (+ a b) c incoming held)
         (fn-psc-model-byte-run b (fn-psc-model-byte-run a c incoming held) incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run a c incoming held)
          :in-theory (e/d (fn-psc-model-byte-run)
                         (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

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

(local (defthm fn-psc-source-body-literal-reinitialization-is-self
 (equal (fn-psc-literal pos bytes resume (fn-psc-literal pos bytes resume c))
        (fn-psc-literal pos bytes resume c))
 :hints (("Goal" :in-theory (e/d (fn-psc-literal fn-psc-compare nfix) (nth len update-nth))))))

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

(local (defthm fn-psc-source-start-establishes-skip-context
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :control) (equal (fn-psc-get resume c) :start))
  (and (fn-psc-skip-statep c incoming held) (fn-psc-source-resumep c)
       (true-listp c) (equal (len c) 24)))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-contextp fn-psc-skip-statep fn-psc-source-resumep)
  (fn-psc-model-source nth len nfix))))))

(local (defthm fn-psc-source-skip-complete-frame
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :control) (equal (fn-psc-get resume c) :start))
  (let ((d (fn-psc-model-skip-complete c incoming held)))
   (and (fn-psc-source-contextp d incoming held)
        (equal (fn-psc-get phase d) :control) (equal (fn-psc-get resume d) :after-key)
        (equal (fn-psc-get pos d) (fn-pbb-skip-at (fn-psc-model-source c incoming held)))
        (natp (fn-psc-get pos d)) (<= (fn-psc-get pos d) (len (fn-psc-model-source c incoming held)))
        (equal (fn-psc-model-source d incoming held) (fn-psc-model-source c incoming held))
        (equal (fn-psc-model-retained-agent d incoming) (fn-psc-model-retained-agent c incoming))
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-start-establishes-skip-context fn-psc-skip-complete-is-current-buffer-skip
        fn-psc-skip-complete-is-actual-paid-steps
        (:instance fn-psc-source-paid-run-preserves-context (fuel (fn-psc-model-skip-cost c incoming held))))
  :in-theory (e/d (fn-psc-model-source fn-psc-model-retained-agent)
   (fn-psc-model-skip-complete fn-psc-model-skip-cost fn-psc-model-byte-run fn-psc-source-contextp
    fn-psc-skip-statep fn-psc-source-resumep fn-pbb-skip-at
    fn-psc-source-start-establishes-skip-context fn-psc-skip-complete-is-current-buffer-skip
    fn-psc-skip-complete-is-actual-paid-steps fn-psc-source-paid-run-preserves-context nth nthcdr len nfix))))))

(local (defthm fn-psc-source-after-key-callback
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :control) (equal (fn-psc-get resume c) :after-key))
  (equal (fn-psc-step c nil)
         (fn-psc-literal (nfix (fn-psc-get pos c)) *fn-inj-path-field* :source-path-field
           (fn-psc-set skip (nfix (fn-psc-get pos c)) c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-contextp fn-psc-step fn-psc-control)
  (fn-psc-literal fn-psc-model-source nth len update-nth nfix))))))

(local (defthm fn-psc-source-after-key-entry-frame
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :control) (equal (fn-psc-get resume c) :after-key)
               (natp (fn-psc-get pos c)))
  (let ((d (fn-psc-step c nil)))
   (and (fn-psc-source-contextp d incoming held)
        (equal (fn-psc-get skip d) (fn-psc-get pos c))
        (equal (fn-psc-model-source d incoming held) (fn-psc-model-source c incoming held))
        (equal (fn-psc-model-retained-agent d incoming) (fn-psc-model-retained-agent c incoming))
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-literal (fn-psc-get pos c) *fn-inj-path-field* :source-path-field d) d))))
 :hints (("Goal" :use fn-psc-source-after-key-callback :in-theory (e/d (fn-psc-source-contextp fn-psc-model-source fn-psc-model-retained-agent
                                 fn-psc-literal fn-psc-compare nfix)
  (fn-psc-source-after-key-callback fn-psc-step nth nthcdr len update-nth))))))

(local (defthm fn-psc-source-control-one-paid-step
 (implies (equal (fn-psc-get phase c) :control)
  (equal (fn-psc-model-byte-run 1 c incoming held) (fn-psc-step c nil)))
 :hints (("Goal" :expand ((fn-psc-model-byte-run 1 c incoming held)
                         (:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-model-demanded-byte fn-psc-demand)
   (fn-psc-model-byte-run fn-psc-model-source fn-psc-step nth len nfix))))))

(defthm fn-psc-source-complete-is-current-buffer-source-index
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :control) (equal (fn-psc-get resume c) :start))
  (let* ((d (fn-psc-model-source-complete c incoming held))
         (desc (fn-pbb-source-index (fn-psc-model-retained-agent c incoming)
                 (fn-record-string-octets (fn-psc-get msgid c)) (fn-psc-model-source c incoming held))))
   (and (equal (fn-psc-result d) (if desc (cons :source desc) :no-source))
        (equal (fn-psc-get phase d) :done)
        (or (equal (fn-psc-result d) :no-source)
            (and (equal (car (fn-psc-result d)) :source)
                 (fn-pbb-descp (cdr (fn-psc-result d)) (len (fn-psc-model-source c incoming held))))))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-skip-complete-frame
        (:instance fn-psc-source-after-key-entry-frame (c (fn-psc-model-skip-complete c incoming held)))
        (:instance fn-psc-source-body-complete-is-current-buffer-source-index (pos (fn-psc-get pos (fn-psc-model-skip-complete c incoming held))) (c (fn-psc-step (fn-psc-model-skip-complete c incoming held) nil)))
        (:instance fn-psc-source-body-complete-is-terminal-with-current-descriptor (pos (fn-psc-get pos (fn-psc-model-skip-complete c incoming held))) (c (fn-psc-step (fn-psc-model-skip-complete c incoming held) nil))))
  :in-theory (e/d (fn-psc-model-source-complete)
   (fn-psc-model-skip-complete fn-psc-model-source-body-complete fn-psc-step fn-psc-source-contextp
    fn-psc-model-source fn-psc-model-retained-agent fn-record-string-octets fn-pbb-source-index fn-pbb-skip-at
    fn-pbb-descp fn-psc-result fn-psc-done-result-is-stored
    fn-psc-source-skip-complete-frame fn-psc-source-after-key-entry-frame
    fn-psc-source-body-complete-is-current-buffer-source-index
    fn-psc-source-body-complete-is-terminal-with-current-descriptor
    fn-psc-source-body-complete-is-actual-paid-steps fn-psc-skip-complete-is-actual-paid-steps
    fn-psc-source-after-key-callback nth len)))))

(defthm fn-psc-source-complete-is-actual-paid-steps
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :control) (equal (fn-psc-get resume c) :start))
  (equal (fn-psc-model-source-complete c incoming held)
         (fn-psc-model-byte-run (fn-psc-model-source-cost c incoming held) c incoming held)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-start-establishes-skip-context fn-psc-source-skip-complete-frame
        fn-psc-skip-complete-is-actual-paid-steps
        (:instance fn-psc-source-after-key-entry-frame (c (fn-psc-model-skip-complete c incoming held)))
        (:instance fn-psc-source-control-one-paid-step (c (fn-psc-model-skip-complete c incoming held)))
        (:instance fn-psc-source-body-complete-is-actual-paid-steps (pos (fn-psc-get pos (fn-psc-model-skip-complete c incoming held))) (c (fn-psc-step (fn-psc-model-skip-complete c incoming held) nil)))
        (:instance fn-psc-source-byte-run-addition (a (fn-psc-model-skip-cost c incoming held)) (b (+ 1 (fn-psc-model-source-body-cost (fn-psc-get pos (fn-psc-model-skip-complete c incoming held)) (fn-psc-step (fn-psc-model-skip-complete c incoming held) nil) incoming held))))
        (:instance fn-psc-source-byte-run-addition (a 1) (b (fn-psc-model-source-body-cost (fn-psc-get pos (fn-psc-model-skip-complete c incoming held)) (fn-psc-step (fn-psc-model-skip-complete c incoming held) nil) incoming held)) (c (fn-psc-model-skip-complete c incoming held))))
  :in-theory (e/d (fn-psc-model-source-complete fn-psc-model-source-cost)
   (fn-psc-model-skip-complete fn-psc-model-skip-cost fn-psc-model-source-body-complete fn-psc-model-source-body-cost
    fn-psc-step fn-psc-literal fn-psc-model-byte-run fn-psc-source-contextp fn-psc-model-source
    fn-psc-source-start-establishes-skip-context fn-psc-source-skip-complete-frame
    fn-psc-skip-complete-is-actual-paid-steps fn-psc-source-after-key-entry-frame fn-psc-source-control-one-paid-step
    fn-psc-source-body-complete-is-actual-paid-steps fn-psc-source-byte-run-addition
    fn-psc-source-after-key-callback fn-psc-skip-complete-is-current-buffer-skip
    fn-psc-source-body-complete-is-current-buffer-source-index nth len nfix)))))

(local (defthm fn-psc-source-begin-establishes-full-source-context
 (implies (and (member-eq mode '(:source-incoming :source-held)) (true-listp incoming)
               (true-listp (if (equal mode :source-held) held incoming)) (stringp msgid)
               (natp start) (natp end) (<= start end) (<= end (len incoming))
               (equal n (len (if (equal mode :source-held) held incoming)))
               (equal incoming-n (len incoming)))
  (let ((c (fn-psc-begin mode n msgid (list :agent start end) incoming-n)))
   (and (fn-psc-source-contextp c incoming held)
        (equal (fn-psc-get phase c) :control) (equal (fn-psc-get resume c) :start)
        (equal (fn-psc-model-source c incoming held) (if (equal mode :source-held) held incoming))
        (equal (fn-psc-model-retained-agent c incoming) (fn-inj-take (- end start) (nthcdr start incoming)))
        (equal (fn-psc-get msgid c) msgid))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-psc-begin-fixed-layout (agent-span (list :agent start end)))) :in-theory (e/d (fn-psc-begin fn-psc-source-contextp fn-psc-model-source
                            fn-psc-model-retained-agent nfix)
   (fn-psc-begin-fixed-layout fn-psc-finish nth nthcdr len))))))

(defthm fn-psc-source-begin-paid-completion-is-current-buffer-source-index
 (implies (and (member-eq mode '(:source-incoming :source-held)) (true-listp incoming)
               (true-listp (if (equal mode :source-held) held incoming)) (stringp msgid)
               (natp start) (natp end) (<= start end) (<= end (len incoming))
               (equal n (len (if (equal mode :source-held) held incoming)))
               (equal incoming-n (len incoming)))
  (let* ((c (fn-psc-begin mode n msgid (list :agent start end) incoming-n))
         (d (fn-psc-model-byte-run (fn-psc-model-source-cost c incoming held) c incoming held))
         (desc (fn-pbb-source-index (fn-inj-take (- end start) (nthcdr start incoming))
                  (fn-record-string-octets msgid) (if (equal mode :source-held) held incoming))))
   (and (equal (fn-psc-get phase d) :done)
        (equal (fn-psc-result d) (if desc (cons :source desc) :no-source))
        (or (equal (fn-psc-result d) :no-source)
            (and (equal (car (fn-psc-result d)) :source)
                 (fn-pbb-descp (cdr (fn-psc-result d)) n))))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-begin-establishes-full-source-context
        (:instance fn-psc-source-complete-is-current-buffer-source-index (c (fn-psc-begin mode n msgid (list :agent start end) incoming-n)))
        (:instance fn-psc-source-complete-is-actual-paid-steps (c (fn-psc-begin mode n msgid (list :agent start end) incoming-n))))
  :in-theory (disable fn-psc-begin fn-psc-model-source-complete fn-psc-model-source-cost fn-psc-model-byte-run
    fn-psc-source-contextp fn-psc-model-source fn-psc-model-retained-agent fn-record-string-octets fn-inj-take
    fn-pbb-source-index fn-pbb-descp fn-psc-result fn-psc-done-result-is-stored
    fn-psc-source-begin-establishes-full-source-context fn-psc-source-complete-is-current-buffer-source-index
    fn-psc-source-complete-is-actual-paid-steps nth len nfix))))
