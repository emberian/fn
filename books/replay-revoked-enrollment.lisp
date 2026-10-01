; Revoked verdict semantic continuation over the actual ORIGINAL snapshots.
; The typed STXE child and parsed enrollment ledger are carried producer
; obligations, not caller Booleans or served whole-state recognizers.
(in-package "ACL2")
(include-book "replay-enrollment-lookup")

; Fixed9: phase, ORIGINALctx, actual parsed verdict child, borrowed keys,
; exact enrollment ledger, issued source, selector, comparison/lookup, result.
(defun fn-rse-revoked-state (phase ctx child keys evidence source selector worker checked)
 (declare (xargs :guard t))
 (list phase ctx child keys evidence source selector worker checked))
(defun fn-rse-revoked-finish (s checked)
 (declare (xargs :guard t))
 (fn-rse-revoked-state :done (fn-rsc-at 1 s) (fn-rsc-at 2 s)
  (fn-rsc-at 3 s) (fn-rsc-at 4 s) (fn-rsc-at 5 s)
  (fn-rsc-at 6 s) (fn-rsc-at 7 s) checked))
(defun fn-rse-revoked-begin (ctx child keys evidence source)
 (declare (xargs :guard t))
 (cond
  ((not (eq (fn-stxk-context-kind ctx) :ok))
   (fn-rse-revoked-state :done ctx child keys evidence source nil nil ctx))
  ((not (equal (fn-stxe-sequence child) (fn-stxk-context-next ctx)))
   (fn-rse-revoked-state :done ctx child keys evidence source nil nil
                         (fn-stxk-fault ctx :sequence)))
  ((not (eq (fn-stxe-token child) :revoked))
   (fn-rse-revoked-state :done ctx child keys evidence source nil nil
                         (fn-stxk-fault ctx :composite-verdict)))
  (t (fn-rse-revoked-state :select ctx child keys evidence source
      (fn-rsc-begin (fn-stxe-keyring-generation child)
                     (fn-stxk-context-snapshots ctx) source) nil nil))))
(defun fn-rse-revoked-step (s)
 (declare (xargs :guard t))
 (if (not (fn-rsc-widthp 9 s)) (mv :refused s)
  (let ((phase (fn-rsc-at 0 s)) (ctx (fn-rsc-at 1 s))
        (child (fn-rsc-at 2 s)) (keys (fn-rsc-at 3 s))
        (evidence (fn-rsc-at 4 s)) (source (fn-rsc-at 5 s))
        (selector (fn-rsc-at 6 s)) (worker (fn-rsc-at 7 s)))
   (cond
    ((eq phase :done) (mv :done s))
    ((eq phase :select)
     (mv-let (word next) (fn-rsc-step selector)
      (cond
       ((eq word :refused) (mv :refused s))
       ((not (eq word :done))
        (mv :working (fn-rse-revoked-state :select ctx child keys evidence source next nil nil)))
       ((null (fn-rsc-at 3 next))
        (mv :done (fn-rse-revoked-finish s (fn-stxk-fault ctx :composite-binding))))
       (t (mv :working (fn-rse-revoked-state :profile ctx child keys evidence source next
        (fn-rse-equality-begin-tails (fn-stxk-profile (fn-rsc-at 3 next))
                                    *fn-hsig-revoked-profile* source) nil))))))
    ((member-eq phase '(:profile :principal))
     (mv-let (word next) (fn-rse-equality-step worker)
      (cond
       ((eq word :refused) (mv :refused s))
       ((not (eq word :done))
        (mv :working (fn-rse-revoked-state phase ctx child keys evidence source selector next nil)))
       ((not (fn-rsc-at 7 next))
        (mv :done (fn-rse-revoked-finish s (fn-stxk-fault ctx :composite-binding))))
       ((eq phase :profile)
        (mv :working (fn-rse-revoked-state :principal ctx child keys evidence source selector
         (fn-rse-equality-begin-tails (fn-stxk-snapshot (fn-rsc-at 3 selector))
                                     (fn-stxe-detail child) source) nil)))
       (t (mv :working (fn-rse-revoked-state :enrollment ctx child keys evidence source selector
        (fn-rse-lookup-begin (fn-stxe-detail child) keys evidence source) nil))))))
    ((eq phase :enrollment)
     (mv-let (word next) (fn-rse-lookup-step worker)
      (cond
       ((eq word :refused) (mv :refused s))
       ((not (eq word :done))
        (mv :working (fn-rse-revoked-state :enrollment ctx child keys evidence source selector next nil)))
       ((not (eq (fn-rsc-at 0 next) :found))
        (mv :done (fn-rse-revoked-finish s (fn-stxk-fault ctx :composite-binding))))
       (t (mv :done (fn-rse-revoked-finish s
        (fn-stxk-context :ok (1+ (nfix (fn-stxk-context-next ctx)))
         (fn-stxk-context-snapshots ctx) (cons child (fn-stxk-context-verdicts ctx))
         (fn-stxk-context-current-generation ctx) nil)))))))
    (t (mv :refused s))))))
(defun fn-rse-revoked-readout (s)
 (declare (xargs :guard t))
 (if (not (fn-rsc-widthp 9 s)) :refused
  (if (eq (fn-rsc-at 0 s) :done)
   (list :produced (fn-rsc-at 8 s) (fn-rsc-at 2 s) (fn-rsc-at 5 s))
   :pending)))

; This custody boundary does not supply parser semantics or allocation
; authority. The actual caller retains these SAME aliases until installation.
(defthm fn-rse-revoked-step-preserves-original-operation-custody
 (implies (fn-rsc-widthp 9 s)
  (let ((next (mv-nth 1 (fn-rse-revoked-step s))))
   (and (fn-rsc-widthp 9 next)
        (equal (fn-rsc-at 1 next) (fn-rsc-at 1 s))
        (equal (fn-rsc-at 2 next) (fn-rsc-at 2 s))
        (equal (fn-rsc-at 3 next) (fn-rsc-at 3 s))
        (equal (fn-rsc-at 4 next) (fn-rsc-at 4 s))
        (equal (fn-rsc-at 5 next) (fn-rsc-at 5 s)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-rse-revoked-step fn-rse-revoked-finish fn-rse-revoked-state
        fn-rsc-at fn-rsc-widthp)
       (fn-rsc-step fn-rse-equality-step fn-rse-lookup-step
        fn-rse-equality-begin-tails fn-rse-lookup-begin fn-stxk-context
        fn-stxk-context-next fn-stxk-context-snapshots
        fn-stxk-context-verdicts fn-stxk-context-current-generation
        fn-stxk-fault fn-stxk-profile fn-stxk-snapshot fn-stxe-detail)))))
