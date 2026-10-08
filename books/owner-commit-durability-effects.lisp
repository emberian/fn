; Invariant proofs over the one guarded dispatcher.
(in-package "ACL2")
(include-book "owner-commit-durability-steps")
(local (in-theory
 (disable fn-lgk-pipe-countedp fn-lgk-pipe-kernel-view fn-lgk-pipe-kernel-count
          fn-lgk-pipe-kernel-append fn-lgk-pipe-kernel-fence fn-lgk-pipe-kernel-fail
          fn-lgk-pipe-kernel-ack fn-lgk-pipe-kernel-take fn-lgk-pipe-kernel-octets
          fn-lgk-pipe-kernel-fitsp)))

; Preservation arm lemmas, then the composed keystones.
(local (in-theory
 (disable (tau-system) nth len true-listp update-nth
          fn-lgk-pipe-okp fn-lgk-pipe-ks fn-lgk-pipe-behind fn-lgk-pipe-d
          fn-lgk-pipe-acked fn-lgk-pipe-fence fn-lgk-pipe-fail fn-lgk-pipe-ack
          fn-lgk-behind-state fn-lgk-behind-effect fn-lgk-behind-admitsp
          fn-lgk-phase fn-lgk-batch fn-lgk-inflight fn-lgk-committed fn-lgk-acked
          fn-lgk-last fn-lgk-append fn-lgc-append-admitsp fn-olr-gc-prepare
          fn-ocp-gc-linkedp fn-ocp-gc-profilep  fn-ocp-gc-io
          fn-ocp-gc-stop fn-ocp-gc-collect fn-ocp-gc-advance fn-ocp-gc-host-step
          fn-ocp-gc-event-state fn-ocp-gc-event-action fn-ocp-gc-pick
          fn-ocp-gc-finish-state fn-ocp-gc-finish-action fn-ocp-gc-finish-event
          fn-ocp-open-next fn-ocp-ocs fn-ocs-phase fn-otm-phase-of fn-otm-next-of
          fn-otm-ocp fn-otm-held fn-otm-held-event fn-ocvm-inv fn-ocvm-w
          fn-ocvm-c fn-ocvm-a fn-ocvm-b fn-ocvm-views fn-ocvm-step
          fn-oqw-step fn-oqw-start fn-ocp-gc-reveals-okp fn-ocp-gc-cuts-okp
          fn-ocv-gc-prefix-durablep fn-ocv-reader-view)))

(defthm fn-ocp-gc-linkedp-output-update
  (implies (and (fn-ocp-gc-linkedp x) (member-equal n '(8 9 14)))
           (fn-ocp-gc-linkedp (update-nth n value x)))
  :hints (("Goal" :cases ((equal n 8) (equal n 9) (equal n 14))
           :in-theory (e/d (fn-ocp-gc-linkedp) ((tau-system) nth len true-listp update-nth)))))

(defthm fn-ocp-gc-event-state-fields
  (and (equal (fn-otm-phase-of (fn-ocp-gc-event-state s e))
              (mv-nth 1 (fn-ocp-commit-step (fn-otm-phase-of s)
                                           (fn-otm-next-of s) e)))
       (equal (fn-otm-next-of (fn-ocp-gc-event-state s e))
              (mv-nth 2 (fn-ocp-commit-step (fn-otm-phase-of s)
                                           (fn-otm-next-of s) e))))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-event-state fn-otm-commit-event
                                    fn-otm-phase-of fn-otm-next-of fn-ocp-commit-event
                                    fn-ocp-ocs fn-ocp-open-next))))

(defthm fn-ocp-gc-finish-state-fields
  (and (equal (fn-otm-phase-of (fn-ocp-gc-finish-state s))
              (fn-otm-phase-of (fn-ocp-gc-event-state s :completed)))
       (equal (fn-otm-next-of (fn-ocp-gc-finish-state s))
              (fn-otm-next-of (fn-ocp-gc-event-state s :completed))))
  :hints (("Goal"
           :use ((:instance fn-otm-held-event-is-the-held-step (event :completed))
                 (:instance fn-ocp-gc-event-state-fields (e :completed)))
           :in-theory
           (e/d (fn-ocp-gc-finish-state fn-ocp-gc-finish-event fn-ocp-gc-event-state fn-och-step fn-ocp-commit-step)
                (fn-ocp-gc-event-state-fields fn-otm-disk fn-otm-clock
                 fn-otm-held-event fn-otm-held-event-is-the-held-step
                 fn-otm-phase-of fn-otm-next-of fn-otm-held fn-otm-commit-event)))))

(defthm fn-ocp-gc-list-constructors
  (and (equal (len (cons a b)) (+ 1 (len b)))
       (equal (true-listp (cons a b)) (true-listp b)))
  :hints (("Goal" :in-theory (enable len true-listp))))

(defthm fn-ocp-gc-stop-preserves-linkedp
  (implies (and (fn-ocp-gc-linkedp x)
                (not (member-eq (nth 4 x) '(:idle :collected :stopped))))
           (fn-ocp-gc-linkedp (fn-ocp-gc-stop x)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-ocp-gc-stop fn-ocp-gc-linkedp))))

(defthm fn-ocp-gc-io-preserves-linkedp
  (implies (and (fn-ocp-gc-linkedp x) (not (equal (nth 4 x) :stopped)))
           (fn-ocp-gc-linkedp (fn-ocp-gc-io x nextp word)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-ocp-gc-io fn-ocp-gc-linkedp fn-oqw-step))))

(defthm fn-ocp-gc-collect-preserves-linkedp
  (implies (fn-ocp-gc-linkedp x) (fn-ocp-gc-linkedp (fn-ocp-gc-collect x)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-ocp-gc-linkedp fn-ocp-gc-collect))))

(defthm fn-ocvm-gc-fields-of-make
  (let ((m (fn-ocvm-make w c a b views)))
    (and (equal (fn-ocvm-w m) (nfix w))
         (equal (fn-ocvm-c m) (nfix c))
         (equal (fn-ocvm-a m) (nfix a))
         (equal (fn-ocvm-b m) (nfix b))
         (equal (fn-ocvm-views m) views)))
  :hints (("Goal" :in-theory (enable fn-ocvm-w fn-ocvm-c fn-ocvm-a
                                    fn-ocvm-b fn-ocvm-views))))

(defthm fn-ocvm-gc-complete-fields
  (let ((q (fn-ocvm-step m '(:complete))))
    (and (equal (fn-ocvm-w q) (fn-ocvm-w m))
         (equal (fn-ocvm-c q) (+ (fn-ocvm-c m) (fn-ocvm-a m)))
         (equal (fn-ocvm-a q) (fn-ocvm-b m))
         (equal (fn-ocvm-b q) 0)
         (equal (fn-ocvm-views q)
                (fn-ocv-capture (fn-ocvm-views m) :complete (fn-ocvm-w m)))))
  :hints (("Goal" :in-theory (e/d (fn-ocvm-step) (fn-ocvm-make)))))

(defthm fn-ocvm-gc-complete-preserves-inv
  (implies (fn-ocvm-inv m) (fn-ocvm-inv (fn-ocvm-step m '(:complete))))
  :hints (("Goal" :in-theory (e/d (fn-ocvm-inv fn-ocvm-step) (fn-ocvm-make)))))

(defthm fn-ocp-gc-advance-preserves-linkedp
  (implies (fn-ocp-gc-linkedp x) (fn-ocp-gc-linkedp (fn-ocp-gc-advance x)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ocp-gc-linkedp fn-ocp-gc-advance)
                           (fn-lgk-pipe-make fn-lgc-of fn-lg-append-admitsp)))))

(defthm fn-ocp-gc-pick-fields
  (and (equal (fn-otm-next-of (fn-ocp-gc-pick s w)) (fn-otm-next-of s))
       (equal (fn-otm-phase-of (fn-ocp-gc-pick s w))
              (fn-otm-phase-of s)))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-pick fn-otm-next
                                    fn-otm-phase-of fn-otm-next-of))))

(defthm fn-ocp-gc-pick-preserves-linkedp
  (implies (fn-ocp-gc-linkedp x)
           (fn-ocp-gc-linkedp (update-nth 1 (fn-ocp-gc-pick (nth 1 x) w) x)))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-linkedp))))

