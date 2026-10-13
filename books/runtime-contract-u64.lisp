; fn: the admitted executable configuration and state identities are fixed width.
(in-package "ACL2")
(include-book "runtime-contract-exec-is")
(include-book "runtime-contract-exhaustion")

(defthm fn-rtc-slot-id-and-incarnation-are-u64
  (implies (and (fn-rtc-invp s)
                (fn-rtc-st-cfg-okp (fn-rtc-config s))
                (natp j)
                (< j (fn-rtc-nslots (fn-rtc-config s))))
           (and (fn-rtc-u64p j)
                (fn-rtc-u64p (fn-rtc-s-inc (fn-rtc-slot j s)))))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-rtc-st-cfg-okp fn-rtc-u64p natp
               (:type-prescription fn-rtc-nslots) (:executable-counterpart expt)))
           :use fn-rtc-invp-slot-incarnation-is-u64)))
(defthm fn-rtc-step*-keeps-fixed-width-admission
  (implies (and (fn-rtc-invp s) (fn-rtc-st-cfg-okp (fn-rtc-config s)))
           (and (fn-rtc-invp (mv-nth 0 (fn-rtc-step* s e q)))
                (fn-rtc-st-cfg-okp
                  (fn-rtc-config (mv-nth 0 (fn-rtc-step* s e q))))))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-rtc-step*-config-frame fn-rtc-step*-preserves-invp)))))
(defthm fn-rtc-x-step*-preserves-invp
  (implies (and (fn-rtc-st-p fn-rtc-st) (fn-rtc-invp fn-rtc-st))
           (fn-rtc-invp (mv-nth 0 (fn-rtc-x-step* e q fn-rtc-st))))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-rtc-x-step*-is fn-rtc-step*-preserves-invp)))))
(defthm fn-rtc-x-step*-keeps-slot-incarnation-u64
  (implies (and (fn-rtc-st-p fn-rtc-st) (fn-rtc-invp fn-rtc-st))
           (fn-rtc-u64p (fn-rtc-s-inc
             (fn-rtc-slot j (mv-nth 0 (fn-rtc-x-step* e q fn-rtc-st))))))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-rtc-x-step*-is fn-rtc-step*-keeps-slot-incarnation-u64)))))

(local (defthm fn-rtc-u64-nthcdr-parts
  (and (equal (car (nthcdr h l)) (nth h l))
       (equal (cdr (nthcdr h l)) (nthcdr (+ 1 (nfix h)) l))
       (implies (true-listp l) (iff (consp (nthcdr h l)) (< (nfix h) (len l)))))
  :hints (("Goal" :in-theory (enable nth nthcdr)))))
(local (defthm fn-rtc-u64-st-slots-shape
  (implies (fn-rtc-st-p fn-rtc-st)
           (and (true-listp (fn-rtc-slots fn-rtc-st))
                (equal (len (fn-rtc-slots fn-rtc-st))
                       (fn-rtc-nslots (fn-rtc-config fn-rtc-st)))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-st-p-is-shapep fn-rtc-shapep)
                (fn-rtc-configp fn-rtc-pool-shapep fn-rtc-nslots fn-rtc-nbufs
                 fn-rtc-config fn-rtc-slots fn-rtc-mstates fn-rtc-pool fn-rtc-get))))))
(defthm fn-rtc-x-slots-exhausted-loop-is
  (implies (and (fn-rtc-st-p fn-rtc-st) (natp i) (natp nstatic)
                (equal n (fn-rtc-nslots (fn-rtc-config fn-rtc-st))))
           (equal (fn-rtc-x-slots-exhausted-loop i n nstatic fn-rtc-st)
                  (fn-rtc-slots-exhaustedp i nstatic
                    (nthcdr i (fn-rtc-slots fn-rtc-st)))))
  :hints (("Goal" :induct (fn-rtc-x-slots-exhausted-loop i n nstatic fn-rtc-st)
           :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-rtc-x-slots-exhausted-loop fn-rtc-slots-exhaustedp
               fn-rtc-st-slot fn-rtc-st$a-slot fn-rtc-slot fn-rtc-c-get-is-nth
               fn-rtc-u64-st-slots-shape fn-rtc-u64-nthcdr-parts
               natp nfix zp car-cons cdr-cons unicity-of-0 fix
               commutativity-of-+ fold-consts-in-+ default-+-1 default-+-2
               (:type-prescription fn-rtc-nslots) (:type-prescription nfix)
               (:executable-counterpart binary-+) (:executable-counterpart unary--))))))
(defthm fn-rtc-x-slots-exhaustedp-is
  (implies (fn-rtc-st-p fn-rtc-st)
           (equal (fn-rtc-x-slots-exhaustedp fn-rtc-st)
                  (fn-rtc-slots-exhaustedp 0 (fn-rtc-nstatic (fn-rtc-config fn-rtc-st))
                                           (fn-rtc-slots fn-rtc-st))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-x-slots-exhaustedp fn-rtc-st-config fn-rtc-x-slots-exhausted-loop-is)
                (fn-rtc-x-slots-exhausted-loop fn-rtc-slots-exhaustedp fn-rtc-nslots fn-rtc-nstatic)))))
