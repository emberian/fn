; PRF-1362: carry the unconsumed configuration tail beside the paused roots.
(in-package "ACL2")
(include-book "store-finalize-incremental")

(defun fn-pck-config-tail (n rest)
  (declare (xargs :guard (natp n)))
  (if (zp n) rest
    (fn-pck-config-tail (1- n) (if (consp rest) (cdr rest) nil))))

(defthm fn-pck-config-tail-is-nthcdr
  (equal (fn-pck-config-tail n rest) (nthcdr n rest)))

(defun fn-pck-cpr-cursorp (r ix rest configs)
  (declare (xargs :guard t))
  (and (fn-sfi-cpr-carriedp r ix)
       (equal rest (fn-sco-nthcdr (nfix (fn-sco-at 2 r)) configs))))

(defthm fn-pck-cpr-cursor-at-open
  (implies (fn-sfi-carry c)
           (fn-pck-cpr-cursorp
            (fn-sco-cpr c) (fn-sfi-carry c)
            (fn-sco-nthcdr (nfix (fn-sco-at 2 (fn-sco-cpr c))) configs)
            configs))
  :hints (("Goal" :use fn-sfi-carry-is-carried
           :in-theory (e/d (fn-pck-cpr-cursorp)
                           (fn-sfi-cpr-carriedp fn-sfi-carry fn-sco-cpr
                            fn-sco-at fn-sco-nthcdr fn-sfi-carry-is-carried)))))

(defun fn-pck-cpr-resume-from (r rest events ix)
  (declare (xargs :guard (fn-sfi-cpr-carriedp r ix) :verify-guards nil))
  (let* ((cs (fn-sco-at 2 r))
         (pair (fn-sfi-cpr-prefix-carried
                (fn-sco-at 1 r) rest events cs (fn-sco-at 3 r) ix))
         (next (car pair)))
    ; On a fault the caller refuses publication. No fault cursor is adopted.
    ; A successful cursor skips only the configurations consumed by THIS delta.
    (list next (cdr pair)
          (if (fn-sco-pausedp next)
              (fn-pck-config-tail
               (nfix (- (nfix (fn-sco-at 2 next)) (nfix cs))) rest)
            rest))))

(verify-guards fn-pck-cpr-resume-from
  :hints (("Goal" :in-theory
           (e/d (fn-sfi-cpr-carriedp)
                (fn-cnode-statep fn-rii-okp fn-sco-at
                 fn-sfi-cpr-prefix-carried fn-sco-pausedp)))))

(defthm fn-pck-cpr-resume-from-is-sco-cpr-resume
  (implies (fn-pck-cpr-cursorp r ix rest configs)
           (equal (car (fn-pck-cpr-resume-from r rest events ix))
                  (fn-sco-cpr-resume r configs events)))
  :hints (("Goal"
           :use ((:instance fn-rii-sco-cpr-prefix-is-sco-cpr-prefix
                            (cn (fn-sco-at 1 r))
                            (configs rest)
                            (config-sequence (fn-sco-at 2 r))
                            (event-sequence (fn-sco-at 3 r))))
           :in-theory
           (union-theories
            '(fn-pck-cpr-cursorp fn-pck-cpr-resume-from
              fn-sfi-cpr-carriedp fn-sco-cpr-resume
              fn-sfi-cpr-prefix-carried-car car-cons cdr-cons)
            (theory 'minimal-theory)))))

; The shared comparator exports its fact without rewrite rules. Keep the
; induction aid local to this proof book.
(local
 (defthm pck-cursor-config-firstp-has-config
  (implies (fn-cpr-config-firstp configs events) (consp configs))
  :hints (("Goal" :by fn-cpr-config-firstp-has-config))))

(defthm pck-cursor-prefix-counter-bounds
  (let ((r (car (fn-sfi-cpr-prefix-carried cn configs events cs es ix))))
    (implies (fn-sco-pausedp r)
             (and (<= (nfix cs) (nfix (fn-sco-at 2 r)))
                  (<= (nfix (fn-sco-at 2 r)) (+ (nfix cs) (len configs))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-sfi-cpr-prefix-carried cn configs events cs es ix)
           :in-theory
           (e/d (fn-sfi-cpr-prefix-carried
                 fn-sco-pausedp fn-sco-paused fn-sco-at fn-replay-fault
                 pck-cursor-config-firstp-has-config)
                (fn-cnode-statep fn-node-statep fn-cpr-config-firstp
                 fn-rii-cpr-apply-event fn-cpr-apply-event fn-cnode-apply-config
                 fn-cnode-record-acceptablep fn-cnode-carried-acceptablep
                 fn-cfg-recordp fn-store-event-p fn-replay-apply-record
                 fn-replay-advance-okp fn-replay-advance-txid
                 fn-rii-ix-next fn-rii-okp fn-sfi-cpr-prefix-carried-car)))))

(defun fn-pck-cpr-resume-from-steps (r rest events ix)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sfi-cpr-prefix-carried-steps
   (fn-sco-at 1 r) rest events (fn-sco-at 2 r) (fn-sco-at 3 r) ix))

(defun fn-pck-configs-consumed (r next)
  (declare (xargs :guard t))
  (nfix (- (nfix (fn-sco-at 2 next)) (nfix (fn-sco-at 2 r)))))

(defthm pck-cursor-len-tail
  (implies (and (natp n) (<= n (len x)))
           (equal (len (nthcdr n x)) (- (len x) n)))
  :hints (("Goal" :induct (nthcdr n x))))

(defthm fn-pck-cpr-resume-from-consumes-its-tail
  (let* ((out (fn-pck-cpr-resume-from r rest events ix))
         (k (fn-pck-configs-consumed r (car out))))
    (implies (fn-sco-pausedp (car out))
             (and (<= k (len rest))
                  (equal (len (caddr out)) (- (len rest) k)))) )
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance pck-cursor-prefix-counter-bounds
                            (cn (fn-sco-at 1 r)) (configs rest)
                            (cs (fn-sco-at 2 r)) (es (fn-sco-at 3 r))))
           :in-theory
           (e/d (fn-pck-cpr-resume-from fn-pck-configs-consumed)
                (fn-sco-at fn-sco-pausedp fn-sfi-cpr-prefix-carried
                 fn-sfi-cpr-prefix-carried-car)))))

(defun fn-pck-publications-configs-consumed (r rest ix deltas)
  (declare (xargs :guard t :verify-guards nil :measure (len deltas)))
  (if (not (consp deltas)) 0
    (let ((out (fn-pck-cpr-resume-from r rest (car deltas) ix)))
      (if (not (fn-sco-pausedp (car out))) 0
        (+ (fn-pck-configs-consumed r (car out))
           (fn-pck-publications-configs-consumed
            (car out) (caddr out) (cadr out) (cdr deltas)))))))

(defthm fn-pck-publications-configs-consumed-at-most-once
  (<= (fn-pck-publications-configs-consumed r rest ix deltas) (len rest))
  :rule-classes nil
  :hints (("Goal" :induct (fn-pck-publications-configs-consumed r rest ix deltas)
           :in-theory (disable fn-pck-cpr-resume-from fn-pck-configs-consumed
                               fn-sco-pausedp))
          ("Subgoal *1/3"
           :use ((:instance fn-pck-cpr-resume-from-consumes-its-tail
                            (events (car deltas)))))))

(defthm pck-cursor-tail-compose
  (implies (and (natp a) (natp b))
           (equal (nthcdr b (nthcdr a x)) (nthcdr (+ a b) x)))
  :hints (("Goal" :induct (nthcdr a x))))

(defthm pck-cursor-cancel-offset
  (implies (and (integerp a) (integerp b))
           (equal (+ a (- a) b) b))
  :hints (("Goal" :in-theory (enable associativity-of-+ commutativity-2-of-+
                                    inverse-of-+ unicity-of-0 fix))))

(defthm pck-cursor-advance-tail
  (implies (and (natp a) (natp b) (<= a b))
           (equal (nthcdr (- b a) (nthcdr a x)) (nthcdr b x)))
  :hints (("Goal" :use ((:instance pck-cursor-tail-compose (b (- b a))))
           :in-theory (e/d (associativity-of-+ inverse-of-+ unicity-of-0)
                           (nthcdr pck-cursor-tail-compose)))))

(defthm fn-pck-cpr-resume-from-keeps-cursor
  (let ((out (fn-pck-cpr-resume-from r rest events ix)))
    (implies (and (fn-pck-cpr-cursorp r ix rest configs)
                  (fn-sco-pausedp (car out)))
             (fn-pck-cpr-cursorp (car out) (cadr out) (caddr out) configs)))
  :hints (("Goal"
           :use ((:instance fn-sfi-cpr-prefix-carried-keeps-carried
                            (cn (fn-sco-at 1 r)) (configs rest)
                            (cs (fn-sco-at 2 r)) (es (fn-sco-at 3 r)))
                 (:instance pck-cursor-prefix-counter-bounds
                            (cn (fn-sco-at 1 r)) (configs rest)
                            (cs (fn-sco-at 2 r)) (es (fn-sco-at 3 r))))
           :in-theory
           (e/d (fn-pck-cpr-cursorp fn-pck-cpr-resume-from
                 fn-sfi-cpr-carriedp fn-sco-nthcdr)
                (fn-cnode-statep fn-rii-okp fn-sco-at fn-sco-pausedp
                 fn-sfi-cpr-prefix-carried fn-sfi-cpr-prefix-carried-car
                 fn-sfi-cpr-prefix-carried-keeps-carried)))))

(defthm fn-pck-cpr-prefix-steps-by-consumed-configs
  (let ((r (car (fn-sfi-cpr-prefix-carried cn configs events cs es ix))))
    (implies (fn-sco-pausedp r)
             (<= (fn-sfi-cpr-prefix-carried-steps cn configs events cs es ix)
                 (+ (len events) (- (nfix (fn-sco-at 2 r)) (nfix cs))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-sfi-cpr-prefix-carried cn configs events cs es ix)
           :in-theory
           (e/d (fn-sfi-cpr-prefix-carried
                 fn-sco-pausedp fn-sco-paused fn-sco-at fn-replay-fault
                 fn-sfi-cpr-prefix-carried-steps)
                (fn-cnode-statep fn-node-statep fn-cpr-config-firstp
                 fn-rii-cpr-apply-event fn-cpr-apply-event fn-cnode-apply-config
                 fn-cnode-record-acceptablep fn-cnode-carried-acceptablep
                 fn-cfg-recordp fn-store-event-p fn-replay-apply-record
                 fn-replay-advance-okp fn-replay-advance-txid
                 fn-rii-ix-next fn-rii-okp fn-sfi-cpr-prefix-carried-car)))))

(defthm fn-pck-cpr-resume-from-steps-bounded
  (let ((out (fn-pck-cpr-resume-from r rest events ix)))
    (implies (fn-sco-pausedp (car out))
             (<= (fn-pck-cpr-resume-from-steps r rest events ix)
                 (+ (len events) (fn-pck-configs-consumed r (car out))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-pck-cpr-prefix-steps-by-consumed-configs
                            (cn (fn-sco-at 1 r)) (configs rest)
                            (cs (fn-sco-at 2 r)) (es (fn-sco-at 3 r))))
           :in-theory
           (e/d (fn-pck-cpr-resume-from fn-pck-cpr-resume-from-steps
                 fn-pck-configs-consumed)
                (fn-sco-at fn-sco-pausedp fn-sfi-cpr-prefix-carried
                 fn-sfi-cpr-prefix-carried-car fn-sfi-cpr-prefix-carried-steps)))))

(defthm pck-cursor-tail-length-bounded
  (<= (len (nthcdr n x)) (len x))
  :rule-classes :linear
  :hints (("Goal" :induct (nthcdr n x))))

(defthm fn-pck-publications-consume-at-most-the-configs
  (implies (fn-pck-cpr-cursorp r ix rest configs)
           (<= (fn-pck-publications-configs-consumed r rest ix deltas)
               (len configs)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-pck-publications-configs-consumed-at-most-once))
           :in-theory
           (e/d (fn-pck-cpr-cursorp fn-sco-nthcdr)
                (fn-pck-publications-configs-consumed fn-sfi-cpr-carriedp
                 fn-sco-at nthcdr)))))
