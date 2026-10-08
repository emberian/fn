; Enter the composed machine from the actual recovered/idle kernel and
; scheduler. Native OPEN uses the counted representation of this same entry.
(in-package "ACL2")
(include-book "owner-commit-durability-concrete")
(local (in-theory (disable (tau-system))))

(defun fn-ocp-gc-open (ks s unit extent bmax omax)
  (declare (xargs :guard (true-listp ks)))
  (let ((d (fn-lgk-pipe-kernel-count ks))
        (h (nth 1 ks)))
    (list (fn-lgk-pipe-make ks nil) s (fn-ocvm-make d d 0 0 nil)
          (if (natp h) h (list-fix h))
          :idle :idle nil nil nil nil unit extent bmax omax nil)))

; Entry equation: OPEN constructs the idle boundary; subsequent entries
; call the dispatcher, and never reconstruct state from observed receipts.
(defthm fn-ocp-gc-open-projects
  (equal (fn-ocp-gc-project (fn-ocp-gc-open ks s unit extent bmax omax))
         (fn-ocp-gc-open (fn-lgk-pipe-kernel-view ks) s unit extent bmax omax))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-open fn-ocp-gc-project
            fn-lgk-pipe-project fn-lgk-pipe-kernel-count fn-lgk-pipe-kernel-view
            fn-lgc-of fn-lgc-make fn-lgc-count fn-ocp-gc-history-count))))

(defthm fn-ocp-gc-open-linked
  (implies
   (and (fn-lgk-pipe-okp (fn-lgk-pipe-make ks nil) (fn-lgk-committed ks))
        (not (fn-lgk-batch ks)) (not (fn-lgk-inflight ks))
        (member-eq (fn-lgk-phase ks) '(:ready :fenced))
        (equal (fn-otm-phase-of s) :idle) (not (fn-otm-next-of s))
        (fn-ocp-gc-profilep unit extent bmax omax))
   (fn-ocp-gc-linkedp (fn-ocp-gc-open ks s unit extent bmax omax)))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-open fn-ocp-gc-linkedp
            fn-lgk-pipe-okp fn-lgk-pipe-d fn-lgk-pipe-kernel-count
            fn-ocvm-inv fn-ocvm-make fn-lgk-committed))))

; Read the next physical effect from the composed job. APPEND behind a
; barrier is an issue/receipt pair: no write is offered before :writing.
(defun fn-ocp-gc-job-effect (x which)
  (declare (xargs :guard (true-listp x)))
  (if (member-eq (nth 4 x) '(:stopped :stopped-drain)) :uncertain
    (let ((phase (nth (if (equal which :next) 5 4) x)))
      (if (equal which :next)
          (case phase (:append :wait) (:writing :append) (:fence :ready)
            (otherwise phase))
        phase))))
(defthm fn-ocp-gc-job-effect-is-the-phase-by-definition
  (implies (and (not (equal which :next))
                (not (member-eq (nth 4 x) '(:stopped :stopped-drain))))
    (equal (fn-ocp-gc-job-effect x which) (nth 4 x))))
(defthm fn-ocp-gc-resolution-effect-is-after-the-fence
  (implies (and (fn-ocp-gc-linkedp x)
                (equal (fn-ocp-gc-job-effect x :current) :resolutions))
    (equal (fn-lgk-pipe-d (nth 0 x))
           (+ (fn-ocvm-c (nth 2 x)) (fn-ocvm-a (nth 2 x)))))
  :hints (("Goal" :in-theory
           (e/d (fn-ocp-gc-job-effect fn-ocp-gc-linkedp)
                (fn-lgk-pipe-okp fn-lgk-pipe-d fn-lgk-pipe-ks fn-lgk-batch
                 fn-lgk-phase fn-lgk-inflight fn-ocvm-inv fn-ocvm-w
                 fn-ocvm-c fn-ocvm-a fn-ocvm-b fn-ocvm-views
                 fn-otm-phase-of fn-otm-next-of nth len true-listp)))))

; A queued drain cannot consume the sole append role while an independent
; prefix/frames operation still owns it. All original fairness rules remain.
(defun fn-ocp-gc-committer-wake (s returned queued waiting append-idle append-returned)
  (declare (xargs :guard t))
  (if (and (not append-idle) (not append-returned)) :wait
    (let ((wake (fn-otm-held-committer-wake s returned queued waiting)))
      (if (and (equal wake :start-next) (not append-idle)) :wait wake))))
(defthm fn-ocp-gc-next-needs-idle-append-role
  (implies (equal (fn-ocp-gc-committer-wake s returned queued waiting append-idle append-returned) :start-next)
    (and append-idle
         (equal (fn-otm-held-committer-wake s returned queued waiting) :start-next)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-otm-held-committer-wake))))

(defthm fn-ocp-gc-collect-waits-for-append-return
  (implies (equal (fn-ocp-gc-committer-wake s returned queued waiting append-idle append-returned) :collect)
    (or append-idle append-returned))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-otm-held-committer-wake))))
