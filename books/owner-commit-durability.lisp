; Invariant proofs over the one guarded dispatcher.
(in-package "ACL2")
(include-book "owner-commit-durability-steps")
(local (in-theory
 (disable fn-lgk-pipe-countedp fn-lgk-pipe-kernel-view fn-lgk-pipe-kernel-count
          fn-lgk-pipe-kernel-append fn-lgk-pipe-kernel-fence fn-lgk-pipe-kernel-fail
          fn-lgk-pipe-kernel-ack fn-lgk-pipe-kernel-take fn-lgk-pipe-kernel-octets
          fn-lgk-pipe-kernel-fitsp)))

(local (include-book "owner-commit-durability-effects"))
(local (include-book "owner-commit-durability-drain"))
(defthm fn-ocp-gc-linkedp-initially
  (implies (fn-ocp-gc-profilep unit extent bmax omax)
           (fn-ocp-gc-linkedp (fn-ocp-gc-init unit extent bmax omax)))
  :rule-classes nil)

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

(local
 (defthm fn-ocp-gc-gate-record-fields
  (and (equal (nth 0 (fn-ocp-gc-gate x event)) (nth 0 x))
       (equal (nth 4 (fn-ocp-gc-gate x event)) (nth 4 x))
       (equal (nth 8 (fn-ocp-gc-gate x event)) (nth 8 x)))
  :hints (("Goal" :in-theory (e/d (fn-ocp-gc-gate)
                                  (fn-otm-next fn-otm-observe fn-otm-disk-step fn-otm-note-step))))))

(local
 (defthm fn-otm-gc-observe-constructors
  (and (equal (fn-ocp-ocs (fn-ocp-make o n p)) o)
       (equal (fn-ocp-open-next (fn-ocp-make o n p)) (if n t nil))
       (equal (fn-ocs-phase (fn-ocs-make o (fn-ocs-phase s) i)) (fn-ocs-phase s)))
  :hints (("Goal" :in-theory (enable fn-ocp-ocs fn-ocp-open-next fn-ocp-make
                                    fn-ocs-phase fn-ocs-make)))))

(local
 (defthm fn-otm-gc-noncommit-fields
  (and
   (equal (fn-otm-phase-of (fn-otm-observe s class hold wait)) (fn-otm-phase-of s))
   (equal (fn-otm-next-of (fn-otm-observe s class hold wait)) (fn-otm-next-of s))
   (equal (fn-otm-phase-of (cadr (fn-otm-disk-step s kind reading arg))) (fn-otm-phase-of s))
   (equal (fn-otm-next-of (cadr (fn-otm-disk-step s kind reading arg))) (fn-otm-next-of s))
   (equal (fn-otm-phase-of (car (fn-otm-note-step s a b))) (fn-otm-phase-of s))
   (equal (fn-otm-next-of (car (fn-otm-note-step s a b))) (fn-otm-next-of s)))
  :hints (("Goal" :in-theory
           (e/d (fn-otm-phase-of fn-otm-next-of fn-otm-observe fn-ocp-observe fn-ocs-observe
                  fn-otm-disk-step fn-otm-note-step fn-otm-disk-event fn-otm-note)
                (fn-otm-dc-event fn-otm-jline fn-otm-journal-entry fn-otm-log-line
                 fn-otm-clock fn-otm-disk fn-otm-keep fn-ocm-observe
                 fn-ocs-ocm fn-ocs-lasti fn-ocp-passes fn-ocp-make fn-ocs-make))))))

(local
 (defthm fn-ocp-gc-scheduler-update-preserves-linkedp
  (implies (and (fn-ocp-gc-linkedp x)
                (equal (fn-otm-phase-of s) (fn-otm-phase-of (nth 1 x)))
                (equal (fn-otm-next-of s) (fn-otm-next-of (nth 1 x))))
           (fn-ocp-gc-linkedp (update-nth 1 s x)))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-linkedp)))))

(local
 (defthm fn-otm-gc-pick-fields
  (and (equal (fn-otm-phase-of (mv-nth 1 (fn-otm-next s w))) (fn-otm-phase-of s))
       (equal (fn-otm-next-of (mv-nth 1 (fn-otm-next s w))) (fn-otm-next-of s)))
  :hints (("Goal" :use fn-ocp-gc-pick-fields
           :in-theory (e/d (fn-ocp-gc-pick) (fn-otm-next fn-ocp-gc-pick-fields))))))

(local
 (defthm fn-ocp-gc-gate-preserves-linkedp
  (implies (fn-ocp-gc-linkedp x)
           (fn-ocp-gc-linkedp (fn-ocp-gc-gate x event)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ocp-gc-gate)
                           (fn-otm-next fn-otm-observe fn-otm-disk-step fn-otm-note-step
                            fn-ocp-gc-pick-fields fn-otm-disk-step-unfolds))))))

(local (in-theory (disable fn-ocp-gc-begin fn-ocp-gc-reserve fn-ocp-gc-take
                           fn-ocp-gc-member fn-ocp-gc-seal fn-ocp-gc-seal-held fn-lgk-pipe-consume
                           fn-ocp-gc-append-issue fn-ocp-gc-gate)))

(local
 (defthm fn-ocp-gc-seal-held-scheduler-fields
  (implies (and (fn-ocp-gc-linkedp x) (equal (nth 4 x) :drain)
                (not (fn-otm-held (nth 1 x))))
   (let* ((y (fn-ocp-gc-seal x nil frames))
          (e (case (nth 4 y) (:intents :started-held) (:idle :started-none-held)))
          (s (mv-nth 1 (fn-otm-held-event (nth 1 x) e))))
    (implies e
     (and (equal (fn-otm-phase-of s) (fn-otm-phase-of (nth 1 y)))
          (equal (fn-otm-next-of s) (fn-otm-next-of (nth 1 y)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-otm-held-event-is-the-held-step
                            (s (nth 1 x)) (event :started-held))
                 (:instance fn-otm-held-event-is-the-held-step
                            (s (nth 1 x)) (event :started-none-held)))
           :in-theory
           (e/d (fn-ocp-gc-seal fn-ocp-gc-linkedp fn-och-step)
                (fn-otm-held-event fn-otm-held-event-is-the-held-step
                 fn-otm-disk fn-otm-clock fn-ocp-gc-seal-extent fn-ocvm-make
                 fn-lgk-pipe-make fn-lgc-of fn-lg-append-admitsp))))))
(local
 (defthm fn-ocp-gc-seal-held-preserves-linkedp
  (implies (fn-ocp-gc-linkedp x) (fn-ocp-gc-linkedp (fn-ocp-gc-seal-held x frames)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ocp-gc-seal-held-scheduler-fields)
                 (:instance fn-ocp-gc-seal-preserves-linkedp (nextp nil)))
           :in-theory (e/d (fn-ocp-gc-seal-held)
                           (fn-ocp-gc-seal fn-ocp-gc-linkedp
                            fn-otm-held-event
                            fn-ocp-gc-seal-held-scheduler-fields))))))

(defthm fn-ocp-gc-linkedp-preserved
  (implies (fn-ocp-gc-linkedp x)
           (fn-ocp-gc-linkedp (fn-ocp-gc-host-step x event)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-ocp-gc-pick-preserves-linkedp
                            (x (update-nth 14 nil (update-nth 9 nil (update-nth 8 nil x))))
                            (w (nth 1 event)))
                 (:instance fn-ocp-gc-drain-is-stoppable
                            (x (update-nth 14 nil (update-nth 9 nil (update-nth 8 nil x))))
                            (nextp (equal (nth 1 event) :next))))
           :in-theory (e/d (fn-ocp-gc-host-step) (fn-ocp-gc-pick-preserves-linkedp)))))

(local
 (defthm fn-ocv-gc-take-durable-prefix
  (implies (and (natp n) (<= n (len a))) (fn-lg-prefixp (take n (append a b)) a))
  :hints (("Goal" :induct (take n a) :in-theory (enable len fn-lg-prefixp)))))

(local
 (defthm fn-ocv-gc-prefix-durable-under-link
  (implies (and (fn-lgk-pipe-okp p h) (natp cut) (<= cut (fn-lgk-pipe-d p)))
           (fn-ocv-gc-prefix-durablep h p cut))
  :hints (("Goal" :in-theory (enable fn-ocv-gc-prefix-durablep fn-lgk-pipe-okp
                                    fn-lgk-pipe-d fn-olr-linkp)))))

(local
 (defthm fn-ocp-gc-linkedp-frontiers
  (implies (fn-ocp-gc-linkedp x)
    (and (fn-lgk-pipe-okp (nth 0 x) (nth 3 x))
         (<= (fn-ocvm-c (nth 2 x)) (fn-lgk-pipe-d (nth 0 x)))
         (fn-ocvm-inv (nth 2 x))))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-linkedp)))))

(local
 (defthm fn-ocvm-gc-reader-view
  (implies (fn-ocvm-inv m)
    (equal (fn-ocv-reader-view (fn-ocvm-views m) (fn-ocvm-w m)) (fn-ocvm-c m)))
  :hints (("Goal" :in-theory (enable fn-ocvm-inv fn-ocv-reader-view)))))

(local
 (defthm fn-ocp-gc-complete-cut-is-durable
  (implies (and (fn-ocp-gc-linkedp x) (member-eq (nth 4 x) '(:resolutions :done :collected)))
    (equal (+ (fn-ocvm-a (nth 2 x)) (fn-ocvm-c (nth 2 x))) (fn-lgk-pipe-d (nth 0 x))))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-linkedp)))))

(local
 (defthm fn-ocp-gc-linkedp-kernel
  (implies (fn-ocp-gc-linkedp x) (fn-lgk-pipe-okp (nth 0 x) (nth 3 x)))
  :rule-classes :forward-chaining))

(local
 (defthm fn-ocp-gc-drain-arms-preserve-cuts
  (and (equal (nth 8 (fn-ocp-gc-begin x nextp)) (nth 8 x))
       (equal (nth 8 (fn-ocp-gc-reserve x nextp txid)) (nth 8 x))
       (equal (nth 8 (fn-ocp-gc-take x nextp record txid)) (nth 8 x))
       (equal (nth 8 (fn-ocp-gc-member x nextp outcome)) (nth 8 x))
       (equal (nth 8 (fn-ocp-gc-seal x nextp frames)) (nth 8 x))
       (equal (nth 8 (fn-ocp-gc-seal-held x frames)) (nth 8 x))
       (equal (nth 8 (fn-ocp-gc-append-issue x)) (nth 8 x))
       (equal (nth 8 (fn-ocp-gc-gate x event)) (nth 8 x)))
  :hints (("Goal" :in-theory
           (e/d (fn-ocp-gc-begin fn-ocp-gc-reserve fn-ocp-gc-take
                  fn-ocp-gc-member fn-ocp-gc-seal fn-ocp-gc-seal-held fn-ocp-gc-append-issue fn-ocp-gc-gate)
                (fn-otm-held-event fn-lgk-pipe-take fn-ocp-gc-seal-extent fn-lgk-pipe-kernel-octets
                 fn-lgc-append-admitsp fn-lgk-pipe-make))))))

(defthm fn-ocp-gc-reveals-are-durable
  (implies (fn-ocp-gc-linkedp x)
           (fn-ocp-gc-reveals-okp (fn-ocp-gc-host-step x event)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :use fn-ocp-gc-linkedp-preserved
           :in-theory (enable fn-ocp-gc-reveals-okp fn-ocp-gc-cuts-okp fn-ocp-gc-host-step
                               fn-ocp-gc-io fn-ocp-gc-collect
                              fn-ocp-gc-advance fn-ocp-gc-stop))))

(local
 (defthm fn-ocp-gc-stopped-step-fields
  (implies (equal (nth 4 x) :stopped)
    (and (equal (nth 0 (fn-ocp-gc-host-step x event)) (nth 0 x))
         (equal (nth 4 (fn-ocp-gc-host-step x event)) :stopped)))
  :hints (("Goal" :in-theory
           (union-theories '(fn-ocp-gc-host-step fn-ocp-gc-close fn-ocp-gc-gate
                             nth-update-nth (:e nfix) (:e equal) (:e member-equal))
                           (theory 'minimal-theory))))))

(local
 (defthm fn-ocp-gc-stopped-run-fields
  (implies (equal (nth 4 x) :stopped)
    (and (equal (nth 0 (fn-ocp-gc-run x events)) (nth 0 x))
         (equal (nth 4 (fn-ocp-gc-run x events)) :stopped)))
  :hints (("Goal" :induct (fn-ocp-gc-run x events)
           :in-theory (disable fn-ocp-gc-host-step)))))

(local
 (defthm fn-ocp-gc-stop-member-releases
  (subsetp-equal (fn-ocs-member-releases :stop outcomes)
                 '(:own-uncertain :uncertain-reply :close))
  :hints (("Goal" :induct (len outcomes)
           :in-theory (enable len fn-ocs-member-releases fn-ocs-member-release)))))

(local
 (defthm fn-ocp-gc-event-action-fields
  (equal (fn-ocp-gc-event-action s e)
         (mv-nth 0 (fn-ocp-commit-step (fn-otm-phase-of s)
                                      (fn-otm-next-of s) e)))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-event-action fn-otm-commit-event
                                    fn-otm-phase-of fn-otm-next-of fn-ocp-commit-event)))))

(defthm fn-ocp-gc-failure-fences-both-batches
  (implies (fn-ocp-gc-failure-hyp x) (fn-ocp-gc-failure-okp x events))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ocp-gc-failure-hyp fn-ocp-gc-failure-okp
                            fn-ocp-gc-host-step fn-ocp-gc-io fn-ocp-gc-stop fn-ocp-gc-linkedp)
                           (fn-ocp-gc-run fn-ocs-member-releases)))))

(defthm fn-ocp-gc-event-action-by-definition
  (equal (fn-ocp-gc-event-action s e) (mv-nth 0 (fn-otm-commit-event s e)))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-event-action))))

(defthm fn-ocp-gc-event-state-by-definition
  (equal (fn-ocp-gc-event-state s e) (mv-nth 1 (fn-otm-commit-event s e)))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-event-state))))

(defthm fn-ocp-gc-pick-by-definition
  (equal (fn-ocp-gc-pick s w) (mv-nth 1 (fn-otm-next s w)))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-pick))))
