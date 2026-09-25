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
(local
 (defthm fn-bpnrs-nth-one-of-event
   (equal (fn-bpn-nth 1 (list :operator-resume arrival)) arrival)
   :hints (("Goal" :expand ((fn-bpn-nth 1 (list :operator-resume arrival))
                            (fn-bpn-nth 0 (list arrival)))
            :in-theory (enable fn-cbor-ag-car)))))

; The two-field event carries no budgets: the defaults.  A row stranded by
; busy answers takes the kind-20 resume (bp-node-busy-delivery.lisp); every
; other row this forwarding resume.
(defthm fn-bpnp-step-operator-resume-is-the-resume-arm
  (equal (fn-bpnp-step st (list :operator-resume arrival))
         (if (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain)
             (fn-bpnf-answer st nil)
           (if (fn-bpnp-busy-strandedp
                (fn-bpnf-find-arrival arrival (fn-bpnf-held-list st))
                *fn-bpnp-max-forward-retries*)
               (fn-bpnp-busy-resume-step st arrival
                                         *fn-bpnp-max-forward-retries*)
             (fn-bpnp-operator-resume-step st arrival
                                           *fn-bpnp-max-forward-retries*))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnp-step fn-bpnp-domain-recover-eventp
                                fn-bpnp-conflict-held fn-cbor-ag-car
                                fn-bpnrs-nth-one-of-event
                                fn-bpnp-event-budgets len true-listp
                                (:e fn-bpnp-default-budgets)
                                (:e fn-bpnp-budget-retries) (:e nfix)
                                (:e binary-+) (:e equal) (:e len)
                                car-cons cdr-cons)
                              (theory 'minimal-theory)))))

;; KEYSTONE (refusal).  Over the step the host calls: a resume that proposes
;; a durable record proposes exactly the :resumed kind 9 naming the row's
;; arrival, its primary identity and its last attempt, and only for a row
;; whose uncertain attempt reached the retry bound for the row's next hop at
;; the current epoch.  Every other resume answers (:resume-refused ARRIVAL
;; REASON) and leaves the state unchanged.
(local
 (defthm fn-bpnrs-nth-of-cons
   (equal (fn-bpn-nth n (cons a b))
          (if (zp n) a (fn-bpn-nth (1- n) b)))
   :hints (("Goal" :expand ((fn-bpn-nth n (cons a b)))
            :in-theory (enable fn-cbor-ag-car)))))

(local
 (defthm fn-bpnrs-resume-step-proposal
   (let ((effect (car (fn-bpnf-answer-effects
                       (fn-bpnp-operator-resume-step st arrival budget)))))
     (implies (equal (car effect) :persist-forward-result)
              (and (not (fn-bpnp-resume-refusal st arrival budget))
                   (equal (fn-bpn-nth 3 effect)
                          (fn-bpnp-resume-record st arrival)))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-operator-resume-step
                                 fn-bpnf-answer-effects fn-bpnf-answer
                                 fn-bpnrs-nth-of-cons car-cons cdr-cons
                                 (:e zp) (:e binary-+) (:e unary--)
                                 (:e fn-bpn-nth) (:e car) (:e equal))
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bpnrs-no-refusal-is-stranded
   (let ((h (fn-bpnf-find-arrival arrival (fn-bpnf-held-list st))))
     (implies (not (fn-bpnp-resume-refusal st arrival budget))
              (and (fn-bpnp-stranded-slotp (fn-bpn-nth 13 h) (fn-bpnf-epoch st)
                                           (fn-bpn-nth 11 h) budget)
                   (equal (fn-bpn-nth 12 h) '(:forward-pending)))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-resume-refusal)
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bpnrs-resume-record-fields
   (let ((record (fn-bpnp-resume-record st arrival))
         (h (fn-bpnf-find-arrival arrival (fn-bpnf-held-list st))))
     (and (equal (fn-bpn-nth 3 record) arrival)
          (equal (fn-bpn-nth 4 record) (fn-bpah-held-primary-identity h))
          (equal (fn-bpn-nth 5 record) (fn-bpn-nth 1 (fn-bpn-nth 13 h)))
          (equal (fn-bpn-nth 6 record) (fn-bpn-nth 2 (fn-bpn-nth 13 h)))
          (equal (fn-bpn-nth 8 record) :resumed)))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-resume-record
                                 fn-bpnp-forward-result-record
                                 fn-bpnrs-nth-of-cons (:e zp) (:e binary-+)
                                 (:e unary--))
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bpnrs-busy-resume-writes-no-kind-nine
   (not (equal (car (car (fn-bpnf-answer-effects
                          (fn-bpnp-busy-resume-step st arrival budget))))
               :persist-forward-result))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-busy-resume-step
                                 fn-bpnf-answer-effects fn-bpnf-answer
                                 fn-bpnrs-nth-of-cons car-cons cdr-cons
                                 (:e zp) (:e binary-+) (:e unary--)
                                 (:e fn-bpn-nth) (:e car) (:e equal))
                               (theory 'minimal-theory))))))

(defthm fn-bpnp-step-resume-writes-only-for-a-stranded-row
  (let* ((answer (fn-bpnp-step st (list :operator-resume arrival)))
         (effect (car (fn-bpnf-answer-effects answer)))
         (h (fn-bpnf-find-arrival arrival (fn-bpnf-held-list st)))
         (record (fn-bpn-nth 3 effect)))
    (implies (equal (car effect) :persist-forward-result)
             (and (fn-bpnp-stranded-slotp (fn-bpn-nth 13 h) (fn-bpnf-epoch st)
                                          (fn-bpn-nth 11 h)
                                          *fn-bpnp-max-forward-retries*)
                  (equal (fn-bpn-nth 12 h) '(:forward-pending))
                  (equal record (fn-bpnp-resume-record st arrival))
                  (equal (fn-bpn-nth 3 record) arrival)
                  (equal (fn-bpn-nth 4 record) (fn-bpah-held-primary-identity h))
                  (equal (fn-bpn-nth 5 record) (fn-bpn-nth 1 (fn-bpn-nth 13 h)))
                  (equal (fn-bpn-nth 6 record) (fn-bpn-nth 2 (fn-bpn-nth 13 h)))
                  (equal (fn-bpn-nth 8 record) :resumed))))
  :hints (("Goal"
           :use (fn-bpnp-step-operator-resume-is-the-resume-arm
                 (:instance fn-bpnrs-resume-step-proposal
                            (budget *fn-bpnp-max-forward-retries*))
                 (:instance fn-bpnrs-no-refusal-is-stranded
                            (budget *fn-bpnp-max-forward-retries*))
                 (:instance fn-bpnrs-busy-resume-writes-no-kind-nine
                            (budget *fn-bpnp-max-forward-retries*))
                 fn-bpnrs-resume-record-fields)
           :in-theory (union-theories
                       '(fn-bpnf-answer-effects fn-bpnf-answer
                         fn-bpnrs-nth-of-cons car-cons cdr-cons
                         (:e zp) (:e binary-+) (:e unary--) (:e fn-bpn-nth)
                         (:e car))
                       (theory 'minimal-theory)))))

(defthm fn-bpnp-step-resume-refusal-keeps-the-state
  (let ((reason (fn-bpnp-resume-refusal st arrival
                                        *fn-bpnp-max-forward-retries*)))
    (implies (and reason
                  (not (fn-bpnp-busy-strandedp
                        (fn-bpnf-find-arrival arrival (fn-bpnf-held-list st))
                        *fn-bpnp-max-forward-retries*))
                  (not (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain)))
             (equal (fn-bpnp-step st (list :operator-resume arrival))
                    (fn-bpnf-answer
                     st (list (list :resume-refused arrival reason))))))
  :hints (("Goal" :use fn-bpnp-step-operator-resume-is-the-resume-arm
           :in-theory (e/d (fn-bpnp-operator-resume-step)
                                  (fn-bpnp-resume-refusal fn-bpnp-step
                                   fn-bpnp-step-operator-resume-is-the-resume-arm
                                   fn-bpnp-busy-strandedp
                                   fn-bpnp-busy-resume-step
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
(local
 (defthm fn-bpnrs-nth-of-nil
   (equal (fn-bpn-nth n nil) nil)
   :hints (("Goal" :in-theory (enable fn-bpn-nth fn-cbor-ag-car)))))

(local
 (defun fn-bpnrs-nth-update-induct (i j l)
   (if (or (zp i) (zp j)) (list i j l)
     (fn-bpnrs-nth-update-induct (1- i) (1- j) (cdr l)))))

(local
 (defthm fn-bpnrs-nth-of-update-nth
   (implies (and (natp i) (natp j) (not (equal i j)))
            (equal (fn-bpn-nth i (update-nth j v l))
                   (fn-bpn-nth i l)))
   :hints (("Goal" :induct (fn-bpnrs-nth-update-induct i j l)
            :in-theory (union-theories
                        '(fn-bpn-nth fn-cbor-ag-car update-nth car-cons cdr-cons
                          zp natp fn-bpnrs-nth-of-nil
                          (:induction fn-bpnrs-nth-update-induct)
                          (:e zp) (:e natp) (:e car) (:e cdr) (:e <)
                          (:e binary-+) (:e unary--) fix)
                        (theory 'minimal-theory))))))

(local
 (defthm fn-bpnrs-nth-of-update-nth-same
   (implies (natp i)
            (equal (fn-bpn-nth i (update-nth i v l)) v))
   :hints (("Goal" :induct (fn-bpnrs-nth-update-induct i i l)
            :in-theory (union-theories
                        '(fn-bpn-nth fn-cbor-ag-car update-nth car-cons cdr-cons
                          zp natp
                          (:induction fn-bpnrs-nth-update-induct)
                          (:e zp) (:e natp) (:e car) (:e cdr) (:e <)
                          (:e binary-+) (:e unary--) fix)
                        (theory 'minimal-theory))))))

; The apply, opened once: a :ready result is the matched row's settlement.
(local
 (defthm fn-bpnrs-apply-ready
   (let* ((h (fn-bpnf-find-arrival (fn-bpn-nth 3 record) held))
          (applied (fn-bpnp-forward-result-apply record held)))
     (implies (equal (car applied) :ready)
              (and (fn-bpnp-forward-result-matches-heldp record h)
                   (equal (fn-bpn-nth 2 applied)
                          (fn-bpnp-forward-result-held
                           h (fn-bpn-nth 8 record))))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-forward-result-apply
                                 fn-bpnrs-nth-of-cons car-cons cdr-cons
                                 (:e zp) (:e binary-+) (:e unary--)
                                 (:e fn-bpn-nth) (:e car))
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bpnrs-resumed-held
   (equal (fn-bpnp-forward-result-held h :resumed) (update-nth 13 nil h))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-forward-result-held
                                 fn-bpnp-forward-result-slot
                                 fn-bpnp-forward-terminalp
                                 (:e equal))
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bpnrs-resumed-match
   (implies (and (fn-bpnp-forward-result-matches-heldp record h)
                 (equal (fn-bpn-nth 8 record) :resumed))
            (and (fn-bpnp-uncertain-attemptp (fn-bpn-nth 13 h) (fn-bpn-nth 1 record)
                                             (fn-bpn-nth 11 h))
                 (equal (fn-bpn-nth 0 h) :bpnf-held)
                 (equal (fn-bpn-nth 3 h) (fn-bpn-nth 3 record))
                 (equal (fn-bpn-nth 12 h) '(:forward-pending))
                 (null (fn-bpn-nth 14 h))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-forward-result-matches-heldp
                                 fn-bpnp-resume-slot-namesp)
                               (theory 'minimal-theory))))))

(defthm fn-bpnp-resumed-result-clears-only-the-slot
  (let* ((arrival (fn-bpn-nth 3 record))
         (h (fn-bpnf-find-arrival arrival held))
         (applied (fn-bpnp-forward-result-apply record held)))
    (implies (and (equal (car applied) :ready)
                  (equal (fn-bpn-nth 8 record) :resumed))
             (and (equal (fn-bpn-nth 2 applied) (update-nth 13 nil h))
                  (fn-bpnp-uncertain-attemptp (fn-bpn-nth 13 h) (fn-bpn-nth 1 record)
                                              (fn-bpn-nth 11 h)))))
  :hints (("Goal"
           :use (fn-bpnrs-apply-ready
                 (:instance fn-bpnrs-resumed-match
                            (h (fn-bpnf-find-arrival (fn-bpn-nth 3 record) held))))
           :in-theory (union-theories '(fn-bpnrs-resumed-held)
                                      (theory 'minimal-theory)))))

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
                                              observation epoch budget)
                  (equal (fn-bpah-held-primary-identity row)
                         (fn-bpah-held-primary-identity h))
                  (equal (fn-bpn-nth 3 row) arrival)
                  (equal (fn-bpn-nth 11 row) (fn-bpn-nth 11 h)))))
  :hints (("Goal"
           :use (fn-bpnrs-apply-ready
                 (:instance fn-bpnrs-resumed-match
                            (h (fn-bpnf-find-arrival (fn-bpn-nth 3 record) held))))
           :in-theory (union-theories
                       '(fn-bpnrs-resumed-held fn-bpnp-forward-candidatep
                         fn-bpah-held-primary-identity fn-bpnf-held-bundle
                         fn-bpnrs-nth-of-update-nth fn-bpnrs-nth-of-update-nth-same
                         (:e natp) (:e equal))
                       (theory 'minimal-theory)))))

;; Connection-local uncertainty.  A kind 9 :uncertain (the host's reading of
;; a connection that failed after the durable kind 8, fn-bpnp-tcpcl-outcome)
;; keeps the attempt slot and its count under the :uncertain head: the row
;; is not settled, it is an uncertain attempt at every epoch, and its retry
;; count is exactly the attempt's.
(local
 (defthm fn-bpnrs-uncertain-match
   (implies (and (fn-bpnp-forward-result-matches-heldp record h)
                 (equal (fn-bpn-nth 8 record) :uncertain))
            (and (consp (fn-bpn-nth 13 h))
                 (equal (fn-bpn-nth 3 (fn-bpn-nth 13 h)) (fn-bpn-nth 11 h))
                 (equal (fn-bpn-nth 12 h) '(:forward-pending))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-forward-result-matches-heldp
                                 fn-bpnp-attempt-slot-namesp len
                                 (:e equal) (:e <) (:e binary-+))
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bpnrs-uncertain-held
   (implies (consp (fn-bpn-nth 13 h))
            (equal (fn-bpnp-forward-result-held h :uncertain)
                   (update-nth 13 (cons :uncertain (cdr (fn-bpn-nth 13 h))) h)))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-forward-result-held
                                 fn-bpnp-forward-result-slot
                                 fn-bpnp-forward-terminalp
                                 (:e equal))
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bpnrs-nth-of-consp
   (implies (consp s)
            (equal (fn-bpn-nth n s)
                   (if (zp n) (car s) (fn-bpn-nth (1- n) (cdr s)))))
   :hints (("Goal" :expand ((fn-bpn-nth n s))
            :in-theory (enable fn-cbor-ag-car)))))

(local
 (defthm fn-bpnrs-uncertain-slot
   (let ((slot (cons :uncertain (cdr s))))
     (implies (consp s)
              (and (equal (fn-bpnp-attempt-retries slot)
                          (fn-bpnp-attempt-retries s))
                   (implies (equal (fn-bpn-nth 3 s) peer)
                            (fn-bpnp-uncertain-attemptp slot epoch peer)))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-attempt-retries
                                 fn-bpnp-uncertain-attemptp
                                 fn-bpnrs-nth-of-consp car-cons cdr-cons
                                 (:e zp) (:e binary-+) (:e unary--)
                                 (:e equal))
                               (theory 'minimal-theory))))))

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
  :hints (("Goal"
           :use (fn-bpnrs-apply-ready
                 (:instance fn-bpnrs-uncertain-match
                            (h (fn-bpnf-find-arrival (fn-bpn-nth 3 record) held)))
                 (:instance fn-bpnrs-uncertain-slot
                            (s (fn-bpn-nth 13 (fn-bpnf-find-arrival
                                               (fn-bpn-nth 3 record) held)))
                            (peer (fn-bpn-nth 11 (fn-bpnf-find-arrival
                                                  (fn-bpn-nth 3 record) held)))))
           :in-theory (union-theories
                       '(fn-bpnrs-uncertain-held
                         fn-bpnrs-nth-of-update-nth fn-bpnrs-nth-of-update-nth-same
                         (:e natp) (:e equal))
                       (theory 'minimal-theory)))))

;; No transfer reads as :resumed: the host's TCPCL reading never produces
;; it, and the :forward-result host event refuses it.
(defthm fn-bpnp-no-transfer-reads-as-resumed
  (and (not (equal (fn-bpnp-tcpcl-outcome observed reason) :resumed))
       (not (fn-bpnp-host-eventp
             (list :forward-result e o session :resumed obs))))
  :hints (("Goal" :in-theory (enable fn-bpnp-tcpcl-outcome fn-bpnp-host-eventp
                                     fn-bpnp-transfer-outcomep))))
