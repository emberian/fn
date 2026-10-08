; Invariant proofs over the one guarded dispatcher.
(in-package "ACL2")
(include-book "owner-commit-durability-steps")
(local (in-theory
 (disable fn-lgk-pipe-countedp fn-lgk-pipe-kernel-view fn-lgk-pipe-kernel-count
          fn-lgk-pipe-kernel-append fn-lgk-pipe-kernel-fence fn-lgk-pipe-kernel-fail
          fn-lgk-pipe-kernel-ack fn-lgk-pipe-kernel-take fn-lgk-pipe-kernel-octets
          fn-lgk-pipe-kernel-fitsp)))

(local (include-book "owner-commit-durability-effects"))
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

(defthm fn-ocvm-gc-start-fields
  (let ((q (fn-ocvm-step (if nextp m (fn-ocvm-step m '(:drop)))
                         (list (if nextp :next :start) (len records)))))
    (and (equal (fn-ocvm-w q) (+ (fn-ocvm-w m) (len records)))
         (equal (fn-ocvm-c q) (fn-ocvm-c m))
         (equal (fn-ocvm-a q) (if nextp (fn-ocvm-a m) (len records)))
         (equal (fn-ocvm-b q) (if nextp (len records) (fn-ocvm-b m)))
         (equal (fn-ocvm-views q)
                (if nextp (fn-ocv-capture (fn-ocvm-views m) :next (fn-ocvm-w m))
                  (list (fn-ocvm-w m))))))
  :hints (("Goal" :in-theory (e/d (fn-ocvm-step) (fn-ocvm-make)))))

(defthm fn-ocvm-gc-start-preserves-inv
  (implies (and (fn-ocvm-inv m) (equal (fn-ocvm-b m) 0)
                (if nextp (consp (fn-ocvm-views m)) (equal (fn-ocvm-a m) 0)))
    (fn-ocvm-inv (fn-ocvm-step (if nextp m (fn-ocvm-step m '(:drop)))
                               (list (if nextp :next :start) (len records)))))
  :hints (("Goal" :in-theory (e/d (fn-ocvm-inv fn-ocvm-step) (fn-ocvm-make)))))



(defthm fn-ocp-gc-begin-preserves-linkedp
  (implies (fn-ocp-gc-linkedp x)
           (fn-ocp-gc-linkedp (fn-ocp-gc-begin x nextp)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ocvm-gc-start-fields (m (nth 2 x)) (records nil))
                 (:instance fn-ocvm-gc-start-preserves-inv (m (nth 2 x)) (records nil)))
           :in-theory (e/d (fn-ocp-gc-linkedp fn-ocp-gc-begin)
                           (fn-ocvm-gc-start-fields fn-ocvm-gc-start-preserves-inv)))))

(defthm fn-ocp-gc-member-preserves-linkedp
  (implies (fn-ocp-gc-linkedp x)
           (fn-ocp-gc-linkedp (fn-ocp-gc-member x nextp outcome)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-ocp-gc-linkedp fn-ocp-gc-member))))

(defthm fn-ocp-gc-reserve-preserves-linkedp
  (implies (fn-ocp-gc-linkedp x)
           (fn-ocp-gc-linkedp (fn-ocp-gc-reserve x nextp txid)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ocp-gc-linkedp fn-ocp-gc-reserve)
                           (fn-lgk-pipe-consume)))))

(defthm fn-ocp-gc-take-preserves-linkedp
  (implies (and (fn-ocp-gc-linkedp x)
                (not (member-eq (nth 4 x) '(:stopped :stopped-drain))))
           (fn-ocp-gc-linkedp (fn-ocp-gc-take x nextp record txid)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgk-pipe-take-linked-fields
                    (p (nth 0 x)) (h (nth 3 x))
                    (count (len (fn-lgk-batch (fn-lgk-pipe-ks (nth 0 x)))))
                    (octets (fn-lg-pack-len (fn-lgk-batch (fn-lgk-pipe-ks (nth 0 x)))))
                    (bmax (nth 12 x)) (omax (nth 13 x)) (unit (nth 10 x))))
           :in-theory (e/d (fn-ocp-gc-linkedp fn-ocp-gc-take fn-ocvm-inv)
                           (fn-lgk-pipe-take fn-lgk-pipe-take-linked-fields fn-ocvm-make)))))

(defthm fn-ocp-gc-seal-extent-natp
  (natp (fn-ocp-gc-seal-extent x))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-ocp-gc-seal-extent fn-olr-next-extent))))

(defthm fn-ocp-gc-seal-preserves-linkedp
  (implies (and (fn-ocp-gc-linkedp x)
                (not (member-eq (nth 4 x) '(:stopped :stopped-drain))))
           (fn-ocp-gc-linkedp (fn-ocp-gc-seal x nextp frames)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ocp-gc-linkedp fn-ocp-gc-seal fn-ocvm-inv
                            fn-ocvm-step fn-ocp-gc-profilep)
                           (fn-ocp-gc-seal-extent fn-ocvm-make fn-lgk-pipe-make
                            fn-lgc-of fn-lg-append-admitsp)))))

(defthm fn-ocp-gc-drain-is-stoppable
  (implies (and (fn-ocp-gc-linkedp x)
                (not (member-eq (nth 4 x) '(:stopped :stopped-drain)))
                (equal (nth (if nextp 5 4) x) :drain))
           (not (member-eq (nth 4 x) '(:idle :collected :stopped))))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-linkedp))))

(defthm fn-ocp-gc-append-issue-preserves-linkedp
  (implies (fn-ocp-gc-linkedp x)
           (fn-ocp-gc-linkedp (fn-ocp-gc-append-issue x)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgk-append-behind-safe
                    (p (nth 0 x)) (h (nth 3 x)) (unit (nth 10 x)) (extent (nth 11 x))))
           :in-theory (e/d (fn-ocp-gc-linkedp fn-ocp-gc-append-issue)
                           (fn-lgk-pipe-make fn-lgk-behind-effect)))))

