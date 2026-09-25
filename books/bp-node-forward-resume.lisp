; The operator's resume of a stranded forwarding row (spec bp-node-machine
; 4.3.1).  `bp-node resume JOURNAL NODE-ID ARRIVAL' (host/native/bp-node.lisp
; fnn-command-bp-node-resume) steps fn-bpnp-step (host/native/bp-service.lisp
; fnn-bps-foundation-step) with (:operator-resume ARRIVAL), publishes the
; kind 9 it proposes, and steps (:persist-result EPOCH OP :durable), whose arm
; applies the record with fn-bpnp-forward-result-apply, the function ordered
; FNBS replay also calls (bp-fnbs-family-replay.lisp).
(in-package "ACL2")
(include-book "bp-node-forward-retry")
(set-verify-guards-eagerness 0)

;; The step the host calls, on an :operator-resume event, is the resume arm
;; unless an uncertain publication has fenced the machine.
(defthm fn-bpnp-step-operator-resume-is-the-resume-arm
  (equal (fn-bpnp-step st (list :operator-resume arrival))
         (if (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain)
             (fn-bpnf-answer st nil)
           (fn-bpnp-operator-resume-step st arrival)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnp-step fn-bpnp-domain-recover-eventp
                                fn-bpnp-conflict-held fn-cbor-ag-car
                                car-cons cdr-cons)
                              (theory 'minimal-theory)))))

;; KEYSTONE (refusal).  Over the step the host calls: a resume that proposes
;; a durable record proposes exactly the :resumed kind 9 naming the row's
;; arrival, its primary identity and its last attempt, and only for a row
;; whose uncertain attempt reached the retry bound for the row's next hop at
;; the current epoch.  Every other resume answers (:resume-refused ARRIVAL
;; REASON) and leaves the state unchanged.
(defthm fn-bpnp-step-resume-writes-only-for-a-stranded-row
  (let* ((answer (fn-bpnp-step st (list :operator-resume arrival)))
         (effect (car (fn-bpnf-answer-effects answer)))
         (h (fn-bpnf-find-arrival arrival (fn-bpnf-held-list st)))
         (record (fn-bpn-nth 3 effect)))
    (implies (equal (car effect) :persist-forward-result)
             (and (fn-bpnp-stranded-slotp (fn-bpn-nth 13 h) (fn-bpnf-epoch st)
                                          (fn-bpn-nth 11 h))
                  (equal (fn-bpn-nth 12 h) '(:forward-pending))
                  (equal record (fn-bpnp-resume-record st arrival))
                  (equal (fn-bpn-nth 3 record) arrival)
                  (equal (fn-bpn-nth 4 record) (fn-bpah-held-primary-identity h))
                  (equal (fn-bpn-nth 5 record) (fn-bpn-nth 1 (fn-bpn-nth 13 h)))
                  (equal (fn-bpn-nth 6 record) (fn-bpn-nth 2 (fn-bpn-nth 13 h)))
                  (equal (fn-bpn-nth 8 record) :resumed))))
  :hints (("Goal" :in-theory (e/d (fn-bpnp-operator-resume-step
                                   fn-bpnp-resume-refusal
                                   fn-bpnp-resume-record
                                   fn-bpnp-forward-result-record
                                   fn-bpnf-answer-effects fn-bpnf-answer)
                                  (fn-bpnp-forward-result-apply
                                   fn-bpnd-held-delta fn-bpnd-admitp
                                   fn-bpnp-result-frame
                                   fn-bpnp-stranded-slotp
                                   fn-bpah-held-primary-identity
                                   fn-bpnf-state-with-arrival
                                   fn-bpnp-with-runtime fn-bpnp-with-credit)))))

(defthm fn-bpnp-step-resume-refusal-keeps-the-state
  (let ((reason (fn-bpnp-resume-refusal st arrival)))
    (implies (and reason
                  (not (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain)))
             (equal (fn-bpnp-step st (list :operator-resume arrival))
                    (fn-bpnf-answer
                     st (list (list :resume-refused arrival reason))))))
  :hints (("Goal" :in-theory (e/d (fn-bpnp-operator-resume-step)
                                  (fn-bpnp-resume-refusal
                                   fn-bpnp-forward-result-apply)))))

;; KEYSTONE (re-arm).  A :resumed kind 9 that applies (live at
;; :persist-result, or at replay: both call fn-bpnp-forward-result-apply)
;; replaces the row by the same row with its attempt slot cleared: same
;; arrival, same held bundle and primary identity, still forward-pending to
;; the same next hop.  So it is a forward candidate for that next hop at any
;; epoch while its bundle is live, the scan offers it
;; (fn-bpnp-forward-scan-offers-the-only-candidate) with the forwarding
;; image of the unchanged held primary
;; (fn-bpnp-forward-image-keeps-the-held-primary), and its next kind 8
;; counts from 0 (fn-bpnp-attempted-held on an empty slot).
(defthm fn-bpnp-resumed-result-clears-only-the-slot
  (let* ((arrival (fn-bpn-nth 3 record))
         (h (fn-bpnf-find-arrival arrival held))
         (applied (fn-bpnp-forward-result-apply record held)))
    (implies (and (equal (car applied) :ready)
                  (equal (fn-bpn-nth 8 record) :resumed))
             (and (equal (fn-bpn-nth 2 applied) (update-nth 13 nil h))
                  (fn-bpnp-stranded-slotp (fn-bpn-nth 13 h) (fn-bpn-nth 1 record)
                                          (fn-bpn-nth 11 h)))))
  :hints (("Goal" :in-theory (e/d (fn-bpnp-forward-result-apply
                                   fn-bpnp-forward-result-matches-heldp
                                   fn-bpnp-resume-slot-namesp
                                   fn-bpnp-forward-result-held
                                   fn-bpnp-forward-result-slot
                                   fn-bpnp-forward-terminalp)
                                  (fn-bpnp-forward-result-recordp
                                   fn-bpnp-stranded-slotp
                                   fn-bpnp-attempt-slot-namesp
                                   fn-bpnp-forward-result-replace
                                   fn-bpah-held-primary-identity)))))

(defthm fn-bpnp-resumed-row-is-a-forward-candidate
  (let* ((arrival (fn-bpn-nth 3 record))
         (h (fn-bpnf-find-arrival arrival held))
         (applied (fn-bpnp-forward-result-apply record held))
         (row (fn-bpn-nth 2 applied)))
    (implies (and (equal (car applied) :ready)
                  (equal (fn-bpn-nth 8 record) :resumed)
                  (natp arrival)
                  (equal (fn-bpnp-held-expiry row observation) :live))
             (and (fn-bpnp-forward-candidatep row (fn-bpn-nth 11 h)
                                              observation epoch)
                  (equal (fn-bpah-held-primary-identity row)
                         (fn-bpah-held-primary-identity h))
                  (equal (fn-bpn-nth 3 row) arrival)
                  (equal (fn-bpn-nth 11 row) (fn-bpn-nth 11 h)))))
  :hints (("Goal"
           :use ((:instance fn-bpnp-resumed-result-clears-only-the-slot))
           :in-theory (e/d (fn-bpnp-forward-candidatep
                            fn-bpnp-forward-result-apply
                            fn-bpnp-forward-result-matches-heldp
                            fn-bpah-held-primary-identity)
                           (fn-bpnp-resumed-result-clears-only-the-slot
                            fn-bpnp-forward-result-recordp
                            fn-bpnp-resume-slot-namesp
                            fn-bpnp-attempt-slot-namesp
                            fn-bpnp-forward-result-replace
                            fn-bpnp-forward-result-held
                            fn-bpnp-held-expiry
                            fn-bpnp-stranded-slotp)))))

;; Connection-local uncertainty.  A kind 9 :uncertain (the host's reading of
;; a connection that failed after the durable kind 8, fn-bpnp-tcpcl-outcome)
;; keeps the attempt slot and its count under the :uncertain head: the row
;; is not settled, it is an uncertain attempt at every epoch, and its retry
;; count is exactly the attempt's.
(defthm fn-bpnp-uncertain-result-keeps-the-count
  (let* ((arrival (fn-bpn-nth 3 record))
         (h (fn-bpnf-find-arrival arrival held))
         (applied (fn-bpnp-forward-result-apply record held))
         (slot (fn-bpn-nth 13 (fn-bpn-nth 2 applied))))
    (implies (and (equal (car applied) :ready)
                  (equal (fn-bpn-nth 8 record) :uncertain))
             (and (equal (fn-bpnp-attempt-retries slot)
                         (fn-bpnp-attempt-retries (fn-bpn-nth 13 h)))
                  (fn-bpnp-uncertain-attemptp slot epoch (fn-bpn-nth 11 h))
                  (equal (fn-bpn-nth 12 (fn-bpn-nth 2 applied))
                         '(:forward-pending)))))
  :hints (("Goal" :in-theory (e/d (fn-bpnp-forward-result-apply
                                   fn-bpnp-forward-result-matches-heldp
                                   fn-bpnp-attempt-slot-namesp
                                   fn-bpnp-forward-result-held
                                   fn-bpnp-forward-result-slot
                                   fn-bpnp-forward-terminalp
                                   fn-bpnp-attempt-retries
                                   fn-bpnp-uncertain-attemptp)
                                  (fn-bpnp-forward-result-recordp
                                   fn-bpnp-forward-result-replace
                                   fn-bpah-held-primary-identity)))))

;; No transfer reads as :resumed: the host's TCPCL reading never produces
;; it, and the :forward-result host event refuses it.
(defthm fn-bpnp-no-transfer-reads-as-resumed
  (and (not (equal (fn-bpnp-tcpcl-outcome observed reason) :resumed))
       (not (fn-bpnp-host-eventp
             (list :forward-result e o session :resumed obs))))
  :hints (("Goal" :in-theory (enable fn-bpnp-tcpcl-outcome fn-bpnp-host-eventp
                                     fn-bpnp-transfer-outcomep))))
