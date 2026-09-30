; Proof-only full incoming agent precedence and exact charged cursor trace.
(in-package "ACL2")
(include-book "post-identity-source-cursor-skip")
(local (include-book "arithmetic/top" :dir :system))

(local (defthm fn-psc-skip-literal-complete-frame
 (implies (and (natp pos) (true-listp bytes)
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held))))
  (let ((d (fn-psc-model-skip-literal-complete pos bytes resume c incoming held)))
   (and (equal (fn-psc-get phase d) :control) (equal (fn-psc-get resume d) resume)
        (equal (fn-psc-get base d) pos)
        (equal (if (fn-psc-get ok d) t nil)
               (not (equal (fn-inj-strip bytes (nthcdr pos (fn-psc-model-source c incoming held))) :no)))
        (implies (fn-psc-get ok d) (equal (fn-psc-get pos d) (+ pos (len bytes))))
        (equal (fn-psc-get n d) (fn-psc-get n c)) (equal (fn-psc-get mode d) (fn-psc-get mode c))
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-get agent-start d) (fn-psc-get agent-start c))
        (equal (fn-psc-get agent-end d) (fn-psc-get agent-end c)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-literal pos bytes resume c)))
        (:instance fn-psc-comparison-complete-exact-flag (c (fn-psc-literal pos bytes resume c)))
        (:instance fn-psc-comparison-complete-exact-position (c (fn-psc-literal pos bytes resume c)))
        (:instance fn-psc-literal-comparison-is-actual-strip))
  :in-theory (e/d (fn-psc-model-skip-literal-complete fn-psc-literal fn-psc-compare
                   fn-psc-comparison-statep fn-psc-comparison-positionp nfix)
   (fn-psc-model-comparison-complete fn-psc-model-source fn-psc-comparison-complete-returns-control
    fn-psc-comparison-complete-exact-flag fn-psc-comparison-complete-exact-position
    fn-psc-literal-comparison-is-actual-strip fn-inj-strip nth nthcdr len update-nth))))))

(defun fn-psc-model-agent-path-field (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-model-comparison-complete
  (fn-psc-step (fn-psc-model-skip-complete c incoming nil) nil) incoming nil))

(defun fn-psc-model-agent-path (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-psc-model-agent-path-field c incoming)))
  (if (fn-psc-get ok d) (fn-psc-model-leading-path-complete d incoming) (fn-psc-step d nil))))

(defun fn-psc-model-agent-complete (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-psc-model-agent-path c incoming)))
  (if (equal (fn-psc-get phase d) :done) d
   (fn-psc-model-block-agent-complete d incoming))))

(local (defthm fn-psc-after-key-agent-control-unfolds
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :after-key)
               (equal (fn-psc-get mode c) :agent) (natp (fn-psc-get pos c)))
  (equal (fn-psc-step c byte)
   (fn-psc-literal (fn-psc-get pos c) *fn-inj-path-field* :agent-path-field
    (fn-psc-set skip (fn-psc-get pos c) c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control)
  (fn-psc-literal nth len update-nth))))))

(local (defthm fn-psc-strip-success-is-exact-drop
 (implies (and (true-listp prefix) (not (equal (fn-inj-strip prefix xs) :no)))
  (equal (fn-inj-strip prefix xs) (nthcdr (len prefix) xs)))
 :hints (("Goal" :induct (fn-inj-strip prefix xs)
  :in-theory (enable fn-inj-strip nthcdr len true-listp)))))

(local (defthm fn-psc-nthcdr-composes-offsets
 (implies (and (natp a) (natp b))
  (equal (nthcdr b (nthcdr a xs)) (nthcdr (+ a b) xs)))
 :hints (("Goal" :induct (nthcdr a xs) :in-theory (enable nthcdr)))))

(local (defthm fn-psc-block-strip-success-bound
 (implies (and (true-listp prefix) (true-listp xs)
               (not (equal (fn-inj-strip prefix xs) :no)))
  (<= (len prefix) (len xs)))
 :hints (("Goal" :induct (fn-inj-strip prefix xs)
  :in-theory (enable fn-inj-strip len true-listp)))))

(local (defthm fn-psc-block-nthcdr-length
 (implies (and (true-listp xs) (natp start) (<= start (len xs)))
  (equal (len (nthcdr start xs)) (- (len xs) start)))
 :hints (("Goal" :induct (nthcdr start xs) :in-theory (enable nthcdr len true-listp)))))

(local (defthm fn-psc-length-of-append
 (equal (len (append a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (len a) :in-theory (enable append len)))))

(local (defthm fn-psc-agent-path-field-frame
 (implies (and (fn-psc-skip-statep c incoming nil) (equal (fn-psc-get mode c) :agent)
               (true-listp c) (equal (len c) 24))
  (let* ((p (fn-pbb-skip-at incoming)) (d (fn-psc-model-agent-path-field c incoming)))
   (and (equal (fn-psc-get phase d) :control) (equal (fn-psc-get resume d) :agent-path-field)
        (equal (fn-psc-get skip d) p)
        (iff (fn-psc-get ok d) (not (equal (fn-inj-strip *fn-inj-path-field* (nthcdr p incoming)) :no)))
        (implies (fn-psc-get ok d) (equal (fn-psc-get pos d) (+ 6 p)))
        (equal (fn-psc-get n d) (len incoming)) (equal (fn-psc-get mode d) :agent)
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-skip-complete-is-current-buffer-skip (held nil))
        (:instance fn-psc-skip-literal-complete-frame (held nil)
         (c (fn-psc-set skip (fn-pbb-skip-at incoming) (fn-psc-model-skip-complete c incoming nil)))
         (pos (fn-pbb-skip-at incoming)) (bytes *fn-inj-path-field*) (resume :agent-path-field)))
  :in-theory (e/d (fn-psc-model-agent-path-field fn-psc-skip-statep fn-psc-model-source
                   fn-psc-model-skip-literal-complete fn-psc-literal fn-psc-compare)
   (fn-psc-step fn-psc-model-comparison-complete fn-psc-skip-complete-is-actual-paid-steps fn-psc-model-skip-complete
    fn-psc-skip-complete-is-current-buffer-skip fn-psc-skip-literal-complete-frame fn-pbb-skip-at
    fn-inj-strip nthcdr len update-nth))))))

(local (defthm fn-psc-agent-path-field-establishes-leading-state
 (implies (and (fn-psc-skip-statep c incoming nil) (equal (fn-psc-get mode c) :agent)
               (true-listp c) (equal (len c) 24)
               (fn-psc-get ok (fn-psc-model-agent-path-field c incoming)))
  (fn-psc-leading-path-statep (fn-psc-model-agent-path-field c incoming) incoming))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-agent-path-field-frame
        (:instance fn-psc-block-strip-success-bound (prefix *fn-inj-path-field*)
         (xs (nthcdr (fn-pbb-skip-at incoming) incoming)))
        (:instance fn-psc-block-nthcdr-length (start (fn-pbb-skip-at incoming)) (xs incoming)))
  :in-theory (e/d (fn-psc-leading-path-statep fn-psc-skip-statep fn-psc-model-source)
   (fn-psc-model-agent-path-field fn-psc-agent-path-field-frame fn-inj-strip fn-pbb-skip-at
    nthcdr len fn-psc-block-strip-success-bound fn-psc-block-nthcdr-length))))))

(local (defthm fn-psc-line-step-preserves-slot
 (implies (and (equal (fn-psc-get phase c) :line) (natp slot)
               (not (member-equal slot '(0 7 15 21 22))))
  (equal (nth slot (fn-psc-step c byte)) (nth slot c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-return nfix)
                               (nth update-nth len))))))

(local (defthm fn-psc-line-complete-preserves-slot
 (implies (and (natp slot) (not (member-equal slot '(0 7 15 21 22))))
  (equal (nth slot (fn-psc-model-line-complete c incoming held)) (nth slot c)))
 :hints (("Goal" :induct (fn-psc-model-line-complete c incoming held)
  :in-theory (e/d (fn-psc-model-line-complete)
                  (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

(local (defthm fn-psc-line-complete-preserves-state
 (implies (and (fn-psc-line-statep c incoming held)
               (equal (fn-psc-get phase c) :line))
  (fn-psc-line-statep (fn-psc-model-line-complete c incoming held) incoming held))
 :hints (("Goal" :induct (fn-psc-model-line-complete c incoming held)
  :in-theory (e/d (fn-psc-model-line-complete)
                  (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

(local (defthm fn-psc-line-complete-exact-position
 (implies (and (fn-psc-line-statep c incoming held)
               (equal (fn-psc-get phase c) :line))
  (equal (fn-psc-get pos (fn-psc-model-line-complete c incoming held))
         (+ (fn-psc-get pos c)
            (len (fn-pb-line (nthcdr (fn-psc-get pos c) (fn-psc-model-source c incoming held)))))))
 :hints (("Goal" :use (fn-psc-line-complete-preserves-value fn-psc-line-complete-returns-control fn-psc-line-complete-preserves-state)
  :in-theory (e/d (fn-psc-model-line-end fn-psc-line-statep nfix)
   (fn-psc-line-complete-preserves-value fn-psc-line-complete-returns-control fn-psc-line-complete-preserves-state
    fn-psc-model-line-complete nth nthcdr len))))))

(local (defthm fn-psc-leading-path-scan-preserves-msgid
 (implies (fn-psc-leading-path-statep c incoming)
  (equal (fn-psc-get msgid (fn-psc-model-leading-path-scan c incoming)) (fn-psc-get msgid c)))
 :hints (("Goal" :use ((:instance fn-psc-line-complete-preserves-slot (slot 4) (held nil) (c (fn-psc-step c nil))))
  :in-theory (e/d (fn-psc-leading-path-statep fn-psc-model-leading-path-scan fn-psc-step fn-psc-control)
    (fn-psc-model-line-complete fn-psc-line-complete-preserves-slot nth len update-nth fn-psc-literal fn-psc-compare))))))

(local (defthm fn-psc-leading-path-failure-entry-frame
 (implies (and (fn-psc-leading-path-statep c incoming)
               (not (equal (fn-psc-get phase (fn-psc-model-leading-path-complete c incoming)) :done)))
  (let ((d (fn-psc-model-leading-path-complete c incoming)))
   (and (equal (fn-psc-get mode d) :agent)
        (equal (fn-psc-get skip d) (fn-psc-get skip c))
        (equal (fn-psc-get n d) (len incoming))
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-get pos d) (fn-psc-get skip c))
        (equal (fn-psc-get base d) (fn-psc-get skip c))
        (equal (fn-psc-get index d) 0) (equal (fn-psc-get ref d) *fn-inj-injection-date-field*)
        (equal (fn-psc-get ref-start d) 0) (equal (fn-psc-get ref-len d) 16)
        (equal (fn-psc-get phase d) :compare) (equal (fn-psc-get resume d) :agent-stamp))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-leading-path-scan-frame fn-psc-leading-path-scan-preserves-msgid
        (:instance fn-psc-comparison-complete-returns-control
         (held nil) (c (fn-psc-step (fn-psc-model-leading-path-scan c incoming) nil))))
  :expand ((:free (c) (fn-psc-model-byte-run 1 c incoming nil))
           (:free (c) (fn-psc-model-byte-run 0 c incoming nil)))
  :in-theory (e/d (fn-psc-model-leading-path-complete fn-psc-leading-path-statep
                   fn-psc-step fn-psc-control fn-psc-literal fn-psc-compare fn-psc-finish fn-psc-demand
                   fn-psc-model-demanded-byte fn-psc-model-source fn-psc-comparison-statep nfix)
   (fn-psc-model-leading-path-scan fn-psc-model-comparison-complete fn-psc-model-byte-run fn-psc-leading-path-complete-is-actual-steps fn-psc-leading-path-scan-is-actual-steps
    fn-psc-leading-path-scan-frame fn-psc-leading-path-scan-preserves-msgid
    fn-psc-comparison-complete-returns-control fn-psc-comparison-complete-is-actual-steps fn-psc-comparison-next-is-actual-paid-trace nth len update-nth fn-inj-strip nthcdr))))))

(defun fn-psc-agent-statep (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (and (fn-psc-skip-statep c incoming nil) (equal (fn-psc-get mode c) :agent)
      (true-listp c) (equal (len c) 24) (stringp (fn-psc-get msgid c))))

(local (defthm fn-psc-agent-path-failure-entry-frame
 (implies (and (fn-psc-agent-statep c incoming)
               (not (equal (fn-psc-get phase (fn-psc-model-agent-path c incoming)) :done)))
  (let ((d (fn-psc-model-agent-path c incoming)))
   (and (fn-psc-block-statep d incoming)
        (equal (fn-psc-get skip d) (fn-pbb-skip-at incoming))
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-get pos d) (fn-pbb-skip-at incoming))
        (equal (fn-psc-get base d) (fn-pbb-skip-at incoming))
        (equal (fn-psc-get index d) 0) (equal (fn-psc-get ref d) *fn-inj-injection-date-field*)
        (equal (fn-psc-get ref-start d) 0) (equal (fn-psc-get ref-len d) 16)
        (equal (fn-psc-get phase d) :compare) (equal (fn-psc-get resume d) :agent-stamp))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-agent-path-field-frame fn-psc-agent-path-field-establishes-leading-state
        (:instance fn-psc-leading-path-failure-entry-frame (c (fn-psc-model-agent-path-field c incoming))))
  :in-theory (e/d (fn-psc-agent-statep fn-psc-model-agent-path fn-psc-block-statep
                   fn-psc-skip-statep fn-psc-model-source fn-psc-step fn-psc-control fn-psc-literal fn-psc-compare nfix)
   (fn-psc-model-agent-path-field fn-psc-model-leading-path-complete fn-psc-agent-path-field-frame
    fn-psc-agent-path-field-establishes-leading-state fn-psc-leading-path-failure-entry-frame
    fn-psc-leading-path-complete-is-actual-steps fn-pbb-skip-at fn-psc-model-byte-run nth len update-nth))))))

(local (defthm fn-psc-nonpending-result-is-done
 (implies (not (equal (fn-psc-result c) :pending)) (equal (fn-psc-get phase c) :done))
 :hints (("Goal" :in-theory (enable fn-psc-result)))))

(local (defthm fn-psc-leading-path-done-result-not-pending
 (implies (and (fn-psc-leading-path-statep c incoming)
               (equal (fn-psc-get phase (fn-psc-model-leading-path-complete c incoming)) :done))
  (not (equal (fn-psc-result (fn-psc-model-leading-path-complete c incoming)) :pending)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-leading-path-scan-frame
        (:instance fn-psc-comparison-complete-returns-control
          (held nil) (c (fn-psc-step (fn-psc-model-leading-path-scan c incoming) nil))))
  :expand ((:free (c) (fn-psc-model-byte-run 1 c incoming nil)) (:free (c) (fn-psc-model-byte-run 0 c incoming nil)))
  :in-theory (e/d (fn-psc-model-leading-path-complete fn-psc-leading-path-statep fn-psc-step fn-psc-control
                   fn-psc-literal fn-psc-compare fn-psc-finish fn-psc-result fn-psc-demand fn-psc-model-demanded-byte
                   fn-psc-model-source fn-psc-comparison-statep nfix)
   (fn-psc-model-leading-path-scan fn-psc-model-comparison-complete fn-psc-model-byte-run
    fn-psc-leading-path-complete-is-actual-steps fn-psc-leading-path-scan-is-actual-steps
    fn-psc-comparison-complete-is-actual-steps fn-psc-comparison-next-is-actual-paid-trace
    fn-psc-leading-path-scan-frame fn-psc-comparison-complete-returns-control nth len update-nth fn-inj-strip nthcdr))))))

(local (defthm fn-psc-strip-field-from-first-line
 (implies (and (true-listp prefix) (not (member-equal 10 prefix)) (true-listp xs))
  (equal (fn-inj-strip prefix (fn-pb-line xs))
   (if (equal (fn-inj-strip prefix xs) :no) :no (fn-pb-line (fn-inj-strip prefix xs)))))
 :hints (("Goal" :induct (fn-inj-strip prefix xs)
  :in-theory (enable fn-inj-strip fn-pb-line member-equal true-listp)))))

(local (defthm fn-psc-no-path-field-has-no-path-agent
 (implies (and (true-listp xs) (equal (fn-inj-strip *fn-inj-path-field* xs) :no))
  (equal (fn-pb-path-line-agent xs) nil))
 :hints (("Goal" :use ((:instance fn-psc-strip-field-from-first-line (prefix *fn-inj-path-field*)))
  :in-theory (e/d (fn-pb-path-line-agent) (fn-pb-line fn-inj-strip fn-psc-strip-field-from-first-line))))))

(defun fn-psc-model-agent-span-octets (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (let ((r (fn-psc-result c)))
  (if (and (consp r) (equal (car r) :agent))
   (fn-inj-take (- (caddr r) (cadr r)) (nthcdr (cadr r) incoming)) nil)))

(local (defthm fn-psc-block-agent-span-is-current-agent
 (implies (fn-psc-block-statep c incoming)
  (equal (fn-psc-model-agent-span-octets (fn-psc-model-block-agent-complete c incoming) incoming)
   (fn-pb-block-agent (nthcdr (fn-psc-get skip c) incoming) (fn-record-string-octets (fn-psc-get msgid c)))))
 :hints (("Goal" :do-not-induct t :use fn-psc-block-agent-result-is-current-block-agent
  :in-theory (e/d (fn-psc-model-agent-span-octets)
   (fn-psc-result fn-psc-done-result-is-stored fn-psc-nonpending-result-is-done fn-psc-model-block-agent-complete fn-psc-model-block-info fn-pb-block-agent
    fn-psc-block-agent-result-is-current-block-agent fn-inj-take nthcdr len))))))

(local (defthm fn-psc-agent-path-span-is-current-path-agent
 (implies (fn-psc-agent-statep c incoming)
  (let* ((d (fn-psc-model-agent-path c incoming))
         (agent (fn-pb-path-line-agent (nthcdr (fn-pbb-skip-at incoming) incoming))))
   (and (iff (equal (fn-psc-get phase d) :done) agent)
        (equal (fn-psc-model-agent-span-octets d incoming) agent))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-agent-path-field-frame fn-psc-agent-path-field-establishes-leading-state
        (:instance fn-psc-leading-path-done-result-not-pending (c (fn-psc-model-agent-path-field c incoming)))
        (:instance fn-psc-nonpending-result-is-done (c (fn-psc-model-leading-path-complete (fn-psc-model-agent-path-field c incoming) incoming)))
        (:instance fn-psc-leading-path-result-is-current-path-agent (c (fn-psc-model-agent-path-field c incoming))))
  :in-theory (e/d (fn-psc-agent-statep fn-psc-skip-statep fn-psc-model-source fn-psc-model-agent-path
                   fn-psc-model-agent-span-octets fn-psc-result fn-psc-step fn-psc-control fn-psc-literal fn-psc-compare nfix)
   (fn-psc-model-agent-path-field fn-psc-model-leading-path-complete fn-psc-leading-path-result-is-current-path-agent
    fn-psc-leading-path-complete-is-actual-steps fn-psc-agent-path-field-frame fn-psc-agent-path-field-establishes-leading-state
    fn-pbb-skip-at fn-pb-path-line-agent fn-inj-take fn-inj-strip nthcdr nth len update-nth))))))

(defthm fn-psc-agent-span-is-current-path-agent
 (implies (fn-psc-agent-statep c incoming)
  (equal (fn-psc-model-agent-span-octets (fn-psc-model-agent-complete c incoming) incoming)
   (fn-pb-path-agent incoming (fn-record-string-octets (fn-psc-get msgid c)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-agent-path-span-is-current-path-agent fn-psc-agent-path-failure-entry-frame
        (:instance fn-psc-block-agent-span-is-current-agent (c (fn-psc-model-agent-path c incoming)))
        (:instance fn-pbb-skip-at-is-cll-skip (fn-octets incoming)))
  :in-theory (e/d (fn-psc-agent-statep fn-psc-skip-statep fn-psc-model-source
                   fn-psc-model-agent-complete fn-pb-path-agent)
   (fn-psc-model-agent-path fn-psc-model-agent-span-octets fn-psc-model-block-agent-complete
    fn-psc-agent-path-span-is-current-path-agent fn-psc-agent-path-failure-entry-frame fn-psc-block-agent-span-is-current-agent
    fn-pbb-skip-at-is-cll-skip fn-pbb-skip-at fn-cll-skip fn-pb-path-line-agent fn-pb-block-agent
    fn-record-string-octets nth nthcdr len)))))

(local (defthm fn-psc-byte-run-preserves-shape
 (and (implies (equal (len c) 24) (equal (len (fn-psc-model-byte-run fuel c incoming held)) 24))
      (implies (true-listp c) (true-listp (fn-psc-model-byte-run fuel c incoming held))))
 :hints (("Goal" :induct (fn-psc-model-byte-run fuel c incoming held)
  :in-theory (e/d (fn-psc-model-byte-run)
   (fn-psc-step fn-psc-model-demanded-byte nth len update-nth))))))

(local (defthm fn-psc-agent-path-preserves-shape
 (implies (fn-psc-agent-statep c incoming)
  (and (true-listp (fn-psc-model-agent-path c incoming)) (equal (len (fn-psc-model-agent-path c incoming)) 24)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-agent-path-field-establishes-leading-state
        (:instance fn-psc-leading-path-complete-is-actual-steps (c (fn-psc-model-agent-path-field c incoming))))
  :in-theory (e/d (fn-psc-agent-statep fn-psc-model-agent-path fn-psc-model-agent-path-field)
   (fn-psc-step fn-psc-model-comparison-complete fn-psc-model-byte-run fn-psc-model-skip-complete
    nth len update-nth))))))

(local (defthm fn-psc-update-current-slot-is-same
 (implies (and (natp slot) (< slot (len c)) (true-listp c))
  (equal (update-nth slot (nth slot c) c) c))
 :hints (("Goal" :induct (nth slot c)
  :in-theory (enable nth update-nth len true-listp)))))

(local (defthm fn-psc-compare-current-fields-is-same
 (implies (and (true-listp c) (equal (len c) 24)
               (equal (fn-psc-get phase c) :compare)
               (equal (fn-psc-get index c) 0)
               (equal (fn-psc-get base c) (fn-psc-get pos c))
               (natp (fn-psc-get pos c)) (natp (fn-psc-get ref-start c))
               (natp (fn-psc-get ref-len c)))
  (equal (fn-psc-compare (fn-psc-get pos c) (fn-psc-get ref c)
          (fn-psc-get ref-start c) (fn-psc-get ref-len c) (fn-psc-get resume c) c) c))
 :hints (("Goal" :use ((:instance fn-psc-update-current-slot-is-same (slot 0))
                         (:instance fn-psc-update-current-slot-is-same (slot 8))
                         (:instance fn-psc-update-current-slot-is-same (slot 12)))
  :in-theory (e/d (fn-psc-compare nfix)
                                (nth update-nth len true-listp))))))

(local (defthm fn-psc-agent-failed-path-is-actual-block-entry
 (implies (and (fn-psc-agent-statep c incoming)
               (not (equal (fn-psc-get phase (fn-psc-model-agent-path c incoming)) :done)))
  (let ((d (fn-psc-model-agent-path c incoming)))
   (equal (fn-psc-literal (fn-psc-get skip d) *fn-inj-injection-date-field* :agent-stamp d) d)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-agent-path-failure-entry-frame fn-psc-agent-path-preserves-shape
        (:instance fn-psc-compare-current-fields-is-same (c (fn-psc-model-agent-path c incoming))))
  :in-theory (e/d (fn-psc-literal) (fn-psc-compare fn-psc-model-agent-path fn-psc-agent-statep
    fn-psc-agent-path-failure-entry-frame fn-psc-agent-path-preserves-shape
    fn-psc-compare-current-fields-is-same nth len nfix update-nth))))))

(local (defthm fn-psc-byte-run-addition
 (implies (and (natp a) (natp b))
  (equal (fn-psc-model-byte-run (+ a b) c incoming held)
         (fn-psc-model-byte-run b (fn-psc-model-byte-run a c incoming held) incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run a c incoming held)
          :in-theory (e/d (fn-psc-model-byte-run)
                         (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

(defun fn-psc-model-agent-path-field-cost (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (+ 1 (fn-psc-model-comparison-cost (fn-psc-step (fn-psc-model-skip-complete c incoming nil) nil) incoming nil)))

(defun fn-psc-model-agent-path-finish-cost (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-psc-model-agent-path-field c incoming)))
  (if (fn-psc-get ok d) (fn-psc-model-leading-path-cost d incoming) 1)))

(defun fn-psc-model-agent-block-cost (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-psc-model-agent-path c incoming)))
  (if (equal (fn-psc-get phase d) :done) 0 (fn-psc-model-block-agent-cost d incoming))))

(defun fn-psc-model-agent-cost (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (+ (fn-psc-model-skip-cost c incoming nil) (fn-psc-model-agent-path-field-cost c incoming)
    (fn-psc-model-agent-path-finish-cost c incoming) (fn-psc-model-agent-block-cost c incoming)))

(local (defthm fn-psc-agent-path-field-is-paid-trace
 (implies (fn-psc-agent-statep c incoming)
  (equal (fn-psc-model-agent-path-field c incoming)
   (fn-psc-model-byte-run (fn-psc-model-agent-path-field-cost c incoming) (fn-psc-model-skip-complete c incoming nil) incoming nil)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-is-actual-steps (held nil)
         (c (fn-psc-step (fn-psc-model-skip-complete c incoming nil) nil)))
        (:instance fn-psc-byte-run-addition (held nil) (a 1)
         (c (fn-psc-model-skip-complete c incoming nil))
         (b (fn-psc-model-comparison-cost (fn-psc-step (fn-psc-model-skip-complete c incoming nil) nil) incoming nil))))
  :expand ((fn-psc-model-byte-run 1 (fn-psc-model-skip-complete c incoming nil) incoming nil)
           (:free (c) (fn-psc-model-byte-run 0 c incoming nil)))
  :in-theory (e/d (fn-psc-model-agent-path-field fn-psc-model-agent-path-field-cost fn-psc-demand fn-psc-model-demanded-byte
                   fn-psc-agent-statep)
   (fn-psc-step fn-psc-model-skip-complete fn-psc-model-byte-run fn-psc-model-comparison-complete
    fn-psc-model-comparison-cost fn-psc-comparison-complete-is-actual-steps fn-psc-byte-run-addition
    fn-psc-skip-complete-is-actual-paid-steps nth len))))))

(local (defthm fn-psc-agent-path-finish-is-paid-trace
 (implies (fn-psc-agent-statep c incoming)
  (equal (fn-psc-model-agent-path c incoming)
   (fn-psc-model-byte-run (fn-psc-model-agent-path-finish-cost c incoming) (fn-psc-model-agent-path-field c incoming) incoming nil)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-agent-path-field-frame fn-psc-agent-path-field-establishes-leading-state
        (:instance fn-psc-leading-path-complete-is-actual-steps (c (fn-psc-model-agent-path-field c incoming))))
  :expand ((fn-psc-model-byte-run 1 (fn-psc-model-agent-path-field c incoming) incoming nil)
           (:free (c) (fn-psc-model-byte-run 0 c incoming nil)))
  :in-theory (e/d (fn-psc-model-agent-path fn-psc-model-agent-path-finish-cost fn-psc-agent-statep
                   fn-psc-demand fn-psc-model-demanded-byte)
   (fn-psc-model-agent-path-field fn-psc-model-leading-path-complete fn-psc-model-leading-path-cost
    fn-psc-model-byte-run fn-psc-step fn-psc-agent-path-field-frame fn-psc-agent-path-field-establishes-leading-state
    fn-psc-leading-path-complete-is-actual-steps fn-psc-agent-path-field-is-paid-trace nth len))))))

(local (defthm fn-psc-agent-block-is-paid-trace
 (implies (fn-psc-agent-statep c incoming)
  (equal (fn-psc-model-agent-complete c incoming)
   (fn-psc-model-byte-run (fn-psc-model-agent-block-cost c incoming) (fn-psc-model-agent-path c incoming) incoming nil)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-agent-path-failure-entry-frame fn-psc-agent-path-preserves-shape fn-psc-agent-failed-path-is-actual-block-entry
        (:instance fn-psc-block-agent-complete-is-actual-paid-steps (c (fn-psc-model-agent-path c incoming))))
  :expand ((:free (c) (fn-psc-model-byte-run 0 c incoming nil)))
  :in-theory (e/d (fn-psc-model-agent-complete fn-psc-model-agent-block-cost)
   (fn-psc-agent-statep fn-psc-model-agent-path fn-psc-model-block-agent-complete fn-psc-model-block-agent-cost
    fn-psc-model-byte-run fn-psc-literal fn-psc-block-agent-complete-is-actual-paid-steps
    fn-psc-agent-path-failure-entry-frame fn-psc-agent-path-preserves-shape fn-psc-agent-failed-path-is-actual-block-entry
    fn-psc-agent-path-finish-is-paid-trace nth len))))))

(defthm fn-psc-agent-complete-is-actual-paid-steps
 (implies (fn-psc-agent-statep c incoming)
  (equal (fn-psc-model-agent-complete c incoming)
   (fn-psc-model-byte-run (fn-psc-model-agent-cost c incoming) c incoming nil)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-skip-complete-is-actual-paid-steps (held nil))
        fn-psc-agent-path-field-is-paid-trace fn-psc-agent-path-finish-is-paid-trace fn-psc-agent-block-is-paid-trace
        (:instance fn-psc-byte-run-addition (held nil)
         (a (fn-psc-model-skip-cost c incoming nil))
         (b (+ (fn-psc-model-agent-path-field-cost c incoming) (fn-psc-model-agent-path-finish-cost c incoming)
               (fn-psc-model-agent-block-cost c incoming))))
        (:instance fn-psc-byte-run-addition (held nil) (c (fn-psc-model-skip-complete c incoming nil))
         (a (fn-psc-model-agent-path-field-cost c incoming))
         (b (+ (fn-psc-model-agent-path-finish-cost c incoming) (fn-psc-model-agent-block-cost c incoming))))
        (:instance fn-psc-byte-run-addition (held nil) (c (fn-psc-model-agent-path-field c incoming))
         (a (fn-psc-model-agent-path-finish-cost c incoming)) (b (fn-psc-model-agent-block-cost c incoming))))
  :in-theory (e/d (fn-psc-model-agent-cost fn-psc-agent-statep)
   (fn-psc-model-agent-complete fn-psc-model-agent-path fn-psc-model-agent-path-field fn-psc-model-skip-complete
    fn-psc-model-skip-cost fn-psc-model-agent-path-field-cost fn-psc-model-agent-path-finish-cost fn-psc-model-agent-block-cost
    fn-psc-model-byte-run fn-psc-skip-complete-is-actual-paid-steps fn-psc-agent-path-field-is-paid-trace
    fn-psc-agent-path-finish-is-paid-trace fn-psc-agent-block-is-paid-trace fn-psc-byte-run-addition
    fn-psc-agent-path-span-is-current-path-agent  nth len update-nth)))))

(defthm fn-psc-leading-path-result-is-bounded
 (implies (fn-psc-leading-path-statep c incoming)
  (let ((r (fn-psc-result (fn-psc-model-leading-path-complete c incoming))))
   (or (equal r :pending) (fn-psc-agent-resultp r (len incoming)))))
 :hints (("Goal" :do-not-induct t
  :expand ((:free (a end) (len (list :agent a end))) (:free (a end) (len (list a end))) (:free (end) (len (list end))))
  :use (fn-psc-leading-path-complete-result fn-psc-leading-path-scan-frame)
  :in-theory (e/d (fn-psc-agent-resultp fn-psc-leading-path-statep)
   (fn-psc-result fn-psc-done-result-is-stored fn-psc-model-leading-path-complete fn-psc-leading-path-complete-result
    fn-psc-leading-path-result-is-current-path-agent fn-psc-leading-path-complete-is-actual-steps
    fn-psc-leading-path-scan-frame fn-psc-model-leading-path-scan fn-pb-line fn-inj-strip nth len nthcdr)))))

(local (defthm fn-psc-agent-path-done-is-bounded
 (implies (and (fn-psc-agent-statep c incoming)
               (equal (fn-psc-get phase (fn-psc-model-agent-path c incoming)) :done))
  (fn-psc-agent-resultp (fn-psc-result (fn-psc-model-agent-path c incoming)) (len incoming)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-agent-path-field-frame fn-psc-agent-path-field-establishes-leading-state
        (:instance fn-psc-leading-path-result-is-bounded (c (fn-psc-model-agent-path-field c incoming)))
        (:instance fn-psc-leading-path-done-result-not-pending (c (fn-psc-model-agent-path-field c incoming))))
  :in-theory (e/d (fn-psc-agent-statep fn-psc-model-agent-path fn-psc-step fn-psc-control fn-psc-literal fn-psc-compare)
   (fn-psc-agent-resultp fn-psc-result fn-psc-model-agent-path-field fn-psc-model-leading-path-complete
    fn-psc-leading-path-complete-is-actual-steps fn-psc-agent-path-field-frame
    fn-psc-agent-path-field-establishes-leading-state fn-psc-leading-path-result-is-bounded
    fn-psc-leading-path-done-result-not-pending fn-psc-agent-path-field-is-paid-trace fn-psc-agent-path-finish-is-paid-trace
    nth len nfix update-nth))))))

(defthm fn-psc-agent-result-is-bounded
 (implies (fn-psc-agent-statep c incoming)
  (fn-psc-agent-resultp (fn-psc-result (fn-psc-model-agent-complete c incoming)) (len incoming)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-agent-path-done-is-bounded fn-psc-agent-path-failure-entry-frame
        (:instance fn-psc-block-agent-result-is-bounded (c (fn-psc-model-agent-path c incoming))))
  :in-theory (e/d (fn-psc-model-agent-complete)
   (fn-psc-block-agent-result-is-current-block-agent fn-psc-info-agent-result-is-current-info-agent fn-psc-leading-path-result-is-current-path-agent fn-psc-done-result-is-stored fn-psc-agent-statep fn-psc-agent-resultp fn-psc-result fn-psc-model-agent-path fn-psc-model-block-agent-complete
    fn-psc-agent-complete-is-actual-paid-steps fn-psc-agent-block-is-paid-trace fn-psc-block-agent-complete-is-actual-paid-steps
    fn-psc-agent-path-done-is-bounded fn-psc-agent-path-failure-entry-frame fn-psc-block-agent-result-is-bounded
    nth len)))))
(defthm fn-psc-agent-begin-establishes-complete-state
 (implies (and (true-listp incoming) (stringp msgid))
  (fn-psc-agent-statep (fn-psc-begin :agent (len incoming) msgid '(:agent 0 0) (len incoming)) incoming))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-begin-fixed-layout (mode :agent) (n (len incoming)) (agent-span '(:agent 0 0)) (incoming-n (len incoming))))
  :in-theory (e/d (fn-psc-agent-statep fn-psc-skip-statep fn-psc-model-source fn-psc-begin nfix)
  (nth update-nth len fn-psc-begin-fixed-layout)))))
(defthm fn-psc-agent-begin-paid-result-is-exact-and-bounded
 (implies (and (true-listp incoming) (stringp msgid))
  (let* ((c (fn-psc-begin :agent (len incoming) msgid '(:agent 0 0) (len incoming)))
         (d (fn-psc-model-byte-run (fn-psc-model-agent-cost c incoming) c incoming nil)))
   (and (fn-psc-agent-resultp (fn-psc-result d) (len incoming))
        (equal (fn-psc-model-agent-span-octets d incoming)
               (fn-pb-path-agent incoming (fn-record-string-octets msgid))))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-agent-begin-establishes-complete-state
        (:instance fn-psc-agent-result-is-bounded (c (fn-psc-begin :agent (len incoming) msgid '(:agent 0 0) (len incoming))))
        (:instance fn-psc-agent-span-is-current-path-agent (c (fn-psc-begin :agent (len incoming) msgid '(:agent 0 0) (len incoming))))
        (:instance fn-psc-agent-complete-is-actual-paid-steps (c (fn-psc-begin :agent (len incoming) msgid '(:agent 0 0) (len incoming)))))
  :in-theory (e/d (fn-psc-begin)
   (fn-psc-agent-statep fn-psc-agent-resultp fn-psc-result fn-psc-model-agent-span-octets fn-psc-model-agent-complete
    fn-psc-model-agent-cost fn-psc-model-byte-run fn-pb-path-agent fn-record-string-octets
    fn-psc-agent-begin-establishes-complete-state fn-psc-agent-result-is-bounded fn-psc-agent-span-is-current-path-agent
    fn-psc-agent-complete-is-actual-paid-steps nth len)))))

(in-theory (disable fn-psc-agent-statep fn-psc-model-agent-block-cost fn-psc-model-agent-complete fn-psc-model-agent-cost fn-psc-model-agent-path fn-psc-model-agent-path-field fn-psc-model-agent-path-field-cost fn-psc-model-agent-path-finish-cost fn-psc-model-agent-span-octets))
