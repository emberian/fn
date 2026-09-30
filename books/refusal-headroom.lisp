; W8/P12: repeated post-reservation refusals consume finite Store identities.
; This reference iteration composes the actual host-called reserve/refuse
; functions.  Preflight refusals before reserve are a separate zero-use path.
(in-package "ACL2")
(include-book "refusal-effect")

(local (in-theory (disable fn-sn-statep fn-replay-advance-okp
                           fn-olr-sn-reserve fn-sn-refuse-reservation
                           fn-olr-sn-reserve-is-the-file-route-by-definition)))

(defun fn-rfh-ready-p (s)
  (declare (xargs :guard t))
  (and (fn-sn-statep s)
       (equal (fn-sf-phase (fn-sn-files s)) :ready)
       (fn-replay-advance-okp (fn-sn-node s)
                             (+ 1 (fn-sf-frontier (fn-sn-files s))))))

(defun fn-rfh-step (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (fn-sn-refuse-reservation (fn-olr-sn-reserve s)
                            (fn-sf-frontier (fn-sn-files s))))

; fn-olr-sn-reserve is an existing unguard-verified boundary driver.
; This logical reference iteration does not claim a served implementation.

(defthm fn-rfh-step-preserves-state
  (implies (fn-sn-statep s) (fn-sn-statep (fn-rfh-step s)))
  :hints (("Goal" :use (fn-rfx-reserve-preserves-state
                       (:instance fn-sn-refuse-reservation-preserves-state
                                  (s (fn-olr-sn-reserve s))
                                  (txid (fn-sf-frontier (fn-sn-files s)))))
           :in-theory (disable fn-rfx-reserve-preserves-state
                               fn-sn-refuse-reservation-preserves-state))))

(defthm fn-rfh-step-below-ceiling-advances-one
  (implies (and (fn-rfh-ready-p s)
                (< (fn-sf-frontier (fn-sn-files s)) *fn-sf-max-uint*))
           (and (equal (fn-sf-phase (fn-sn-files (fn-rfh-step s))) :ready)
                (equal (fn-sf-frontier (fn-sn-files (fn-rfh-step s)))
                       (+ 1 (fn-sf-frontier (fn-sn-files s))))
                (equal (fn-state-next-txid
                        (fn-node-acceptance (fn-sn-node (fn-rfh-step s))))
                       (+ 1 (fn-sf-frontier (fn-sn-files s))))))
  :hints (("Goal" :use
           ((:instance fn-rfx-refused-post-consumes-one-txid
                       (txid (fn-sf-frontier (fn-sn-files s)))))
           :in-theory (disable fn-rfx-refused-post-consumes-one-txid))))

(local
 (defthm fn-rfh-advance-remains-idle-for-successor
   (implies (fn-replay-advance-okp node n)
            (fn-replay-advance-okp (fn-replay-advance-txid node n) (+ 1 n)))
   :hints (("Goal" :use ((:instance fn-replay-advance-preserves-node-statep
                                   (recorded-txid n)))
            :in-theory (e/d (fn-replay-advance-okp fn-replay-advance-txid)
                            (fn-node-statep))))))

(local
 (defthm fn-rfh-reserved-refusal-enabled
   (implies (and (fn-rfh-ready-p s)
                 (< (fn-sf-frontier (fn-sn-files s)) *fn-sf-max-uint*))
            (fn-sn-refuse-reservation-enabledp
             (fn-olr-sn-reserve s) (fn-sf-frontier (fn-sn-files s))))
   :hints (("Goal" :use (fn-rfx-reserve-preserves-state
                         fn-olr-sn-reserve-reaches-reserved
                         fn-rfx-reserve-keeps-the-node
                         (:instance fn-olr-sf-statep-of-sn-statep))
            :in-theory (e/d (fn-sn-refuse-reservation-enabledp fn-sf-statep)
                            (fn-sn-statep fn-replay-advance-okp))))))

(defthm fn-rfh-step-below-ceiling-preserves-ready
  (implies (and (fn-rfh-ready-p s)
                (< (fn-sf-frontier (fn-sn-files s)) *fn-sf-max-uint*))
           (fn-rfh-ready-p (fn-rfh-step s)))
  :hints (("Goal" :use ((:instance fn-rfh-advance-remains-idle-for-successor
                                   (node (fn-sn-node s))
                                   (n (+ 1 (fn-sf-frontier (fn-sn-files s)))))
                        fn-rfh-step-preserves-state
                        fn-rfh-step-below-ceiling-advances-one
                        fn-rfh-reserved-refusal-enabled
                        fn-rfx-reserve-keeps-the-node
                        fn-olr-sn-reserve-reaches-reserved
                        (:instance fn-sn-refuse-reservation-is-exact-advance
                         (s (fn-olr-sn-reserve s))
                         (txid (fn-sf-frontier (fn-sn-files s)))))
           :in-theory (disable fn-sn-statep fn-replay-advance-okp
                               fn-sn-refuse-reservation-enabledp))))

(defthm fn-rfh-ceiling-reservation-keeps-files
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready)
                (not (< (fn-sf-frontier (fn-sn-files s)) *fn-sf-max-uint*)))
           (equal (fn-sn-files (fn-olr-sn-reserve s)) (fn-sn-files s)))
  :hints (("Goal" :use fn-olr-sf-statep-of-sn-statep
           :in-theory (e/d (fn-olr-sn-reserve-is-the-file-route-by-definition
                            fn-sn-file-step fn-sf-start-frontier
                            fn-sf-frontier-file-result fn-sf-frontier-replace-result
                            fn-sf-frontier-dir-result)
                           (fn-sn-io fn-sn-statep fn-sf-statep)))))

(defthm fn-rfh-step-at-ceiling-keeps-files-and-node
  (implies (and (fn-rfh-ready-p s)
                (not (< (fn-sf-frontier (fn-sn-files s)) *fn-sf-max-uint*)))
           (and (equal (fn-sn-files (fn-rfh-step s)) (fn-sn-files s))
                (equal (fn-sn-node (fn-rfh-step s)) (fn-sn-node s))))
  :hints (("Goal" :use (fn-rfx-reserve-preserves-state
                         fn-rfh-ceiling-reservation-keeps-files
                         fn-rfx-reserve-keeps-the-node)
           :in-theory (enable fn-sn-refuse-reservation
                              fn-sn-refuse-reservation-enabledp))))

(defthm fn-rfh-step-preserves-ready
  (implies (fn-rfh-ready-p s) (fn-rfh-ready-p (fn-rfh-step s)))
  :hints (("Goal" :cases ((< (fn-sf-frontier (fn-sn-files s)) *fn-sf-max-uint*))
           :use (fn-rfh-step-below-ceiling-preserves-ready
                 fn-rfh-step-at-ceiling-keeps-files-and-node
                 fn-rfh-step-preserves-state)
           :in-theory (disable fn-rfh-step))))

(defun fn-rfh-run (n s)
  (declare (xargs :guard (and (natp n) (fn-sn-statep s)) :verify-guards nil))
  (if (zp n) s (fn-rfh-run (1- n) (fn-rfh-step s))))

(defthm fn-rfh-run-preserves-ready
  (implies (fn-rfh-ready-p s) (fn-rfh-ready-p (fn-rfh-run n s)))
  :hints (("Goal" :induct (fn-rfh-run n s)
           :in-theory (disable fn-rfh-ready-p fn-rfh-step))))

(local
 (defthm fn-rfh-ready-frontier-bounds
   (implies (fn-rfh-ready-p s)
            (and (natp (fn-sf-frontier (fn-sn-files s)))
                 (<= (fn-sf-frontier (fn-sn-files s)) *fn-sf-max-uint*)))
   :hints (("Goal" :use fn-olr-sf-statep-of-sn-statep
            :in-theory (enable fn-sf-statep fn-record-uint32p)))))

(defthm fn-rfh-n-refusals-have-exact-bounded-frontier
  (implies (fn-rfh-ready-p s)
           (equal (fn-sf-frontier (fn-sn-files (fn-rfh-run n s)))
                  (min *fn-sf-max-uint*
                       (+ (nfix n) (fn-sf-frontier (fn-sn-files s))))))
  :hints (("Goal" :induct (fn-rfh-run n s)
           :in-theory (disable fn-rfh-ready-p fn-rfh-step))
          ("Subgoal *1/1" :use fn-rfh-ready-frontier-bounds
           :in-theory (e/d (natp) (fn-rfh-ready-frontier-bounds fn-rfh-ready-p fn-rfh-step)))
          ("Subgoal *1/2" :cases
            ((< (fn-sf-frontier (fn-sn-files s)) *fn-sf-max-uint*))
           :use (fn-rfh-ready-frontier-bounds
                 fn-rfh-step-at-ceiling-keeps-files-and-node
                 fn-rfh-step-below-ceiling-advances-one))))

(local
 (defthm fn-rfh-reserve-always-keeps-records
   (equal (fn-sf-records (fn-sn-files (fn-olr-sn-reserve s)))
          (fn-sf-records (fn-sn-files s)))
   :hints (("Goal" :in-theory
     (enable fn-olr-sn-reserve-is-the-file-route-by-definition
             fn-sn-io fn-sn-file-step fn-sf-records-of-start-frontier
             fn-sf-records-of-frontier-file-result
             fn-sf-records-of-frontier-replace-result
             fn-sf-records-of-frontier-dir-result)))))

; No readiness hypothesis: these transitions never publish a record or
; change configuration, even when their current phase refuses advancement.
(defthm fn-rfh-step-keeps-records-and-configuration
  (and (equal (fn-sf-records (fn-sn-files (fn-rfh-step s)))
              (fn-sf-records (fn-sn-files s)))
       (equal (fn-sn-groups (fn-rfh-step s)) (fn-sn-groups s))
       (equal (fn-sn-capacity (fn-rfh-step s)) (fn-sn-capacity s)))
  :hints (("Goal" :use
    ((:instance fn-snrt-refuse-keeps-records
                (s (fn-olr-sn-reserve s))
                (txid (fn-sf-frontier (fn-sn-files s))))
     fn-rfh-reserve-always-keeps-records
     fn-rfx-reserve-keeps-the-configuration
     (:instance fn-sn-refuse-reservation-preserves-configuration
                (s (fn-olr-sn-reserve s))
                (txid (fn-sf-frontier (fn-sn-files s)))))
    :in-theory (disable fn-sn-refuse-reservation fn-olr-sn-reserve))))

(defthm fn-rfh-n-refusals-keep-records-and-configuration
  (and (equal (fn-sf-records (fn-sn-files (fn-rfh-run n s)))
              (fn-sf-records (fn-sn-files s)))
       (equal (fn-sn-groups (fn-rfh-run n s)) (fn-sn-groups s))
       (equal (fn-sn-capacity (fn-rfh-run n s)) (fn-sn-capacity s)))
  :hints (("Goal" :induct (fn-rfh-run n s)
           :in-theory (disable fn-rfh-ready-p fn-rfh-step))))

; fnn-log-reserve asks fn-store-metadata-frontier-next, whose ACL2 subject
; is fn-bs-frontier-next, BEFORE changing the log kernel or issuing reserve.
; NIL becomes the existing named finite transaction-ID domain refusal.
(defthm fn-rfh-exhaustion-is-exactly-consumed-headroom
  (implies (fn-rfh-ready-p s)
           (iff (not (fn-bs-frontier-next
                       (fn-sf-frontier (fn-sn-files (fn-rfh-run n s)))))
                (<= (- *fn-sf-max-uint* (fn-sf-frontier (fn-sn-files s)))
                    (nfix n))))
  :hints (("Goal" :use fn-rfh-ready-frontier-bounds
           :in-theory (e/d (fn-bs-frontier-next natp)
                            (fn-rfh-ready-p fn-rfh-run
                             fn-rfh-ready-frontier-bounds)))))

; Reference iteration only: subsequent proofs explicitly open these drivers.
(in-theory (disable fn-rfh-ready-p fn-rfh-step fn-rfh-run))
