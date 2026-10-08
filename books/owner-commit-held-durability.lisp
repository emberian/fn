; The held caller extends the pipeline without narrowing LINKEDP or its
; preservation keystone. This additional reachable-state invariant proves
; that the held/no-next completion arm is the one the native caller takes.
(in-package "ACL2")
(include-book "owner-commit-durability")
(local (in-theory (disable (tau-system))))

(defun fn-ocp-gc-held-coherentp (x)
  (declare (xargs :guard (true-listp x)))
  (implies (fn-otm-held (nth 1 x))
    (and (equal (nth 5 x) :idle)
         (member-eq (nth 4 x) '(:intents :extend :append :fence
                               :resolutions :done :collected :stopped)))))

(defthm fn-ocp-gc-held-coherent-initially
  (fn-ocp-gc-held-coherentp (fn-ocp-gc-init unit extent bmax omax))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-init fn-otm-init fn-otm-held))))

(local
 (defthm fn-ocp-gc-ordinary-event-keeps-held
  (equal (fn-otm-held (fn-ocp-gc-event-state s e)) (fn-otm-held s))
  :hints (("Goal" :in-theory (e/d (fn-ocp-gc-event-state) (fn-otm-commit-event))))))
(local
 (defthm fn-ocp-gc-finish-clears-held
  (implies (and (fn-otm-held s) (not (fn-otm-next-of s))
                (equal (fn-otm-phase-of s) :fenced))
    (and (not (fn-otm-held (fn-ocp-gc-finish-state s)))
         (equal (fn-ocp-gc-finish-action s) :submit)))
  :hints (("Goal"
           :use ((:instance fn-otm-held-event-is-the-held-step (event :completed)))
           :in-theory
           (e/d (fn-ocp-gc-finish-state fn-ocp-gc-finish-action fn-ocp-gc-finish-event fn-och-step)
                (fn-otm-held-event fn-otm-held-event-is-the-held-step fn-otm-held
                 fn-otm-phase-of fn-otm-next-of fn-otm-disk fn-otm-clock))))))
(local
 (defthm fn-ocp-gc-gate-keeps-held
  (equal (fn-otm-held (nth 1 (fn-ocp-gc-gate x event))) (fn-otm-held (nth 1 x)))
  :hints (("Goal" :in-theory
           (e/d (fn-ocp-gc-gate fn-otm-disk-step fn-otm-note-step fn-otm-note)
                (fn-otm-held fn-otm-next fn-otm-observe fn-otm-disk-event
                 fn-otm-jline fn-otm-journal-entry fn-otm-log-line))))))

(local (in-theory
 (disable fn-otm-held fn-otm-phase-of fn-otm-next-of fn-ocp-gc-event-state
          fn-ocp-gc-event-action fn-ocp-gc-finish-state fn-ocp-gc-finish-action
          fn-otm-held-event fn-ocp-gc-gate fn-ocvm-inv fn-ocvm-step fn-ocvm-make
          fn-lgk-pipe-okp fn-lgk-pipe-take fn-lgk-pipe-fence fn-lgk-pipe-fail
          fn-lgk-pipe-ack fn-lgk-pipe-consume fn-lgk-behind-state
          fn-lgk-behind-effect fn-lgk-behind-admitsp fn-lgc-append-admitsp
          fn-lgk-pipe-kernel-append fn-ocp-gc-seal-extent fn-oqw-step
          fn-ocvm-w fn-ocvm-a fn-ocvm-b fn-ocvm-c fn-ocvm-views
          fn-lgk-pipe-ks fn-lgk-batch fn-lgk-phase fn-ocp-gc-history-extend
          nth update-nth len true-listp)))

(local
 (defthm fn-ocp-gc-drain-keeps-held-coherent
  (implies (fn-ocp-gc-held-coherentp x)
    (and (fn-ocp-gc-held-coherentp (fn-ocp-gc-begin x nextp))
         (fn-ocp-gc-held-coherentp (fn-ocp-gc-reserve x nextp txid))
         (fn-ocp-gc-held-coherentp (fn-ocp-gc-take x nextp record txid))
         (fn-ocp-gc-held-coherentp (fn-ocp-gc-member x nextp outcome))
         (fn-ocp-gc-held-coherentp (fn-ocp-gc-seal x nextp frames))
         (fn-ocp-gc-held-coherentp (fn-ocp-gc-append-issue x))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-ocp-gc-held-coherentp fn-ocp-gc-begin
                    fn-ocp-gc-reserve fn-ocp-gc-take fn-ocp-gc-member
                    fn-ocp-gc-seal fn-ocp-gc-append-issue)))))
(local
 (defthm fn-ocp-gc-effects-keep-held-coherent
  (implies (fn-ocp-gc-held-coherentp x)
    (and (fn-ocp-gc-held-coherentp (fn-ocp-gc-stop x))
         (fn-ocp-gc-held-coherentp (fn-ocp-gc-io x nextp word))
         (fn-ocp-gc-held-coherentp (fn-ocp-gc-collect x))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-ocp-gc-held-coherentp fn-ocp-gc-stop fn-ocp-gc-io
                               fn-ocp-gc-collect fn-oqw-step)))))

(local
 (defthm fn-ocp-gc-linked-collected-fields
  (implies (and (fn-ocp-gc-linkedp x) (equal (nth 4 x) :collected))
    (and (equal (fn-otm-phase-of (nth 1 x)) :fenced)
         (implies (equal (nth 5 x) :idle) (not (fn-otm-next-of (nth 1 x))))))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-linkedp)))))
(local
 (defthm fn-ocp-gc-finish-keeps-no-held
  (implies (not (fn-otm-held s))
    (not (fn-otm-held (fn-ocp-gc-finish-state s))))
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-finish-state fn-ocp-gc-finish-event fn-ocp-gc-event-state)))))
(local
 (defthm fn-ocp-gc-advance-keeps-held-coherent
  (implies (and (fn-ocp-gc-linkedp x) (fn-ocp-gc-held-coherentp x))
    (fn-ocp-gc-held-coherentp (fn-ocp-gc-advance x)))
  :hints (("Goal" :cases ((fn-otm-held (nth 1 x)))
           :use ((:instance fn-ocp-gc-finish-clears-held (s (nth 1 x))))
           :in-theory (e/d (fn-ocp-gc-held-coherentp fn-ocp-gc-advance)
                                    (fn-ocp-gc-linkedp))))))
(local
 (defthm fn-ocp-gc-gate-keeps-job-phases
  (and (equal (nth 4 (fn-ocp-gc-gate x event)) (nth 4 x))
       (equal (nth 5 (fn-ocp-gc-gate x event)) (nth 5 x)))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-gate)))))
(local
 (defthm fn-ocp-gc-gate-keeps-held-coherent
  (implies (fn-ocp-gc-held-coherentp x)
    (fn-ocp-gc-held-coherentp (fn-ocp-gc-gate x event)))
  :hints (("Goal" :in-theory (e/d (fn-ocp-gc-held-coherentp) (fn-ocp-gc-gate))))))
(local
 (defthm fn-ocp-gc-linked-drain-fields
  (implies (and (fn-ocp-gc-linkedp x) (equal (nth 4 x) :drain))
    (and (equal (fn-otm-phase-of (nth 1 x)) :idle)
         (equal (nth 5 x) :idle)))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-linkedp)))))
(local
 (defthm fn-ocp-gc-seal-current-keeps-next-phase
  (equal (nth 5 (fn-ocp-gc-seal x nil frames)) (nth 5 x))
  :hints (("Goal" :in-theory (union-theories '(fn-ocp-gc-seal nth-update-nth (:e nfix) (:e equal))
                                                  (theory 'minimal-theory))))))
(local
 (defthm fn-ocp-gc-empty-held-keeps-no-held
  (implies (not (fn-otm-held s))
    (not (fn-otm-held (mv-nth 1 (fn-otm-held-event s :started-none-held)))))
  :hints (("Goal"
           :use ((:instance fn-otm-held-event-is-the-held-step (event :started-none-held)))
           :in-theory (e/d (fn-och-step)
                           (fn-otm-held-event fn-otm-held-event-is-the-held-step
                            fn-otm-disk fn-otm-clock))))))
(local
 (defthm fn-ocp-gc-seal-held-keeps-held-coherent
  (implies (and (fn-ocp-gc-linkedp x) (fn-ocp-gc-held-coherentp x))
    (fn-ocp-gc-held-coherentp (fn-ocp-gc-seal-held x frames)))
  :hints (("Goal"
           :use ((:instance fn-ocp-gc-drain-keeps-held-coherent (nextp nil)))
           :in-theory
           (e/d (fn-ocp-gc-held-coherentp fn-ocp-gc-seal-held)
                (fn-ocp-gc-linkedp fn-ocp-gc-seal fn-otm-held-event))))))

(local
 (defthm fn-ocp-gc-held-output-update
  (implies (member-eq n '(8 9 14))
    (equal (fn-ocp-gc-held-coherentp (update-nth n value x))
           (fn-ocp-gc-held-coherentp x)))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-held-coherentp)))))
(local
 (defthm fn-ocp-gc-linked-cleared-outputs
  (implies (fn-ocp-gc-linkedp x)
    (fn-ocp-gc-linkedp (update-nth 14 nil (update-nth 9 nil (update-nth 8 nil x)))))
  :hints (("Goal"
           :use ((:instance fn-ocp-gc-linkedp-preserved (event '(:clear-outputs))))
           :in-theory (e/d (fn-ocp-gc-host-step) (fn-ocp-gc-linkedp))))))

(defthm fn-ocp-gc-held-coherent-preserved
  (implies (and (fn-ocp-gc-linkedp x) (fn-ocp-gc-held-coherentp x))
    (fn-ocp-gc-held-coherentp (fn-ocp-gc-host-step x event)))
  :hints (("Goal" :do-not-induct t
           :in-theory
           (e/d (fn-ocp-gc-host-step)
                (fn-ocp-gc-held-coherentp fn-ocp-gc-linkedp
                 fn-ocp-gc-seal-held fn-ocp-gc-advance
                 fn-ocp-gc-begin fn-ocp-gc-reserve fn-ocp-gc-take fn-ocp-gc-member
                 fn-ocp-gc-seal fn-ocp-gc-append-issue fn-ocp-gc-io
                 fn-ocp-gc-stop fn-ocp-gc-collect)))))
