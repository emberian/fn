; When a node rotates its BP journal by itself (lane bp-rotation, F7).
;
; Until now the journal rotated only when the operator ran `bp-node
; checkpoint' with the node stopped, so a node that nobody checkpointed
; filled its generation's received namespace (*fn-bpnf-received-max-
; records*, 8,192 records) and then refused custody.  The profile now
; carries a rotation threshold (books/bp-node-profile, profile 3,
; fn-bpnpf-rotate-records), and the open of a node verb (bp-node serve and
; dispatch; host/native/bp-service.lisp fnn-bps-rotate-when-due) asks
; fn-bpnrd-due-rotation-event whether to rotate.  When the recovered
; generation's record count has reached the threshold and the recovered
; state is quiescent, it answers exactly the event `bp-node checkpoint'
; drives, (:rotate G CK): G fn-bpnr-next-generation's answer, CK the
; checkpoint of the recovery event the open carried.  The machine then
; decides as it always did (fn-bpnp-rotate-step), and the host publishes
; with the same program, so every crash keystone of the rotation
; (fn-bpnr-rotation-crash-recovers-old-or-new, fn-bpnr-retirement-cut-
; keeps-open-view) covers the natural rotation unchanged.  After a durable
; selection the host reopens the journal: the reopen is the recovery the
; keystone below names.
(in-package "ACL2")
(include-book "bp-node-rotation")
(include-book "bp-node-profile")
(set-verify-guards-eagerness 0)

(defun fn-bpnrd-duep (st profile)
  (declare (xargs :guard t))
  (let ((threshold (fn-bpnpf-rotate-records profile)))
    (and (fn-bpnpf-node-profilep profile)
         (natp (fn-bpnp-used st))
         (<= threshold (fn-bpnp-used st))
         (fn-bpnp-rotation-quiescentp st))))

; The event the host drives at a node verb's open, or NIL (no rotation).
; SELECTED is the selected generation (fn-bpnr-plan-generation of the open's
; plan), NAMES the journal root's names, EVENT the recovery event the open
; drove.
(defun fn-bpnrd-due-rotation-event (st profile selected names event)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-bpnrd-duep st profile)
      (let ((g (fn-bpnr-next-generation selected names)))
        (list :rotate g (fn-bpnr-checkpoint-of-event event g)))
    nil))

; The rotation is due exactly when the threshold is reached from a quiescent
; state; the event names a generation above the selected one and the
; checkpoint of the open's recovery event.
(defthm fn-bpnrd-due-rotation-event-by-definition
  (let ((rot (fn-bpnrd-due-rotation-event st profile selected names event)))
    (and (iff rot (and (fn-bpnpf-node-profilep profile)
                       (natp (fn-bpnp-used st))
                       (<= (fn-bpnpf-rotate-records profile) (fn-bpnp-used st))
                       (fn-bpnp-rotation-quiescentp st)))
         (implies rot
                  (and (equal (car rot) :rotate)
                       (< (nfix selected) (fn-bpn-nth 1 rot))
                       (equal (fn-bpn-nth 2 rot)
                              (fn-bpnr-checkpoint-of-event
                               event (fn-bpn-nth 1 rot)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-next-generation-exceeds-selected))
           :in-theory (union-theories
                       '(fn-bpnrd-due-rotation-event fn-bpnrd-duep
                         fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons iff
                         (:e zp) (:e natp) (:e binary-+) (:e not) (:e equal))
                       (theory 'minimal-theory)))))

(local
 (defthm fn-bpnrd-due-event-checkpoint
   (implies (and (not (equal (car plan0) :damaged))
                 (fn-bpnrd-due-rotation-event
                  st profile selected names
                  (append (fn-bpnr-recover-auto-event
                           st0 base-records sequence-ready rows0 plan0)
                          (list domain))))
            (equal (fn-bpn-nth 2 (fn-bpnrd-due-rotation-event
                                  st profile selected names
                                  (append (fn-bpnr-recover-auto-event
                                           st0 base-records sequence-ready
                                           rows0 plan0)
                                          (list domain))))
                   (fn-bpnr-checkpoint-of-replay
                    (fn-bpn-nth 1 (fn-bpnrd-due-rotation-event
                                   st profile selected names
                                   (append (fn-bpnr-recover-auto-event
                                            st0 base-records sequence-ready
                                            rows0 plan0)
                                           (list domain))))
                    (fn-bpnr-replay-from (fn-bpnr-plan-checkpoint plan0) rows0
                                         (fn-bpnf-base st0))
                    (len rows0))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bpnr-recover-event-shape
                             (st st0) (rows rows0) (plan plan0)))
            :in-theory (union-theories
                        '(fn-bpnrd-due-rotation-event fn-bpnr-checkpoint-of-event
                          fn-bpn-nth fn-cbor-ag-car binary-append car-cons cdr-cons
                          (:e zp) (:e natp) (:e binary-+) (:e not) (:e equal))
                        (theory 'minimal-theory))))))

; No due event, no publication: the machine refuses a rotation that names
; no generation.
(local
 (defthm fn-bpnrd-rotate-step-without-generation
   (equal (car (car (fn-bpnf-answer-effects (fn-bpnp-rotate-step st nil ck))))
          :rotation-refused)
   :hints (("Goal" :do-not-induct t
            :in-theory '(fn-bpnp-rotate-step fn-bpnf-answer
                         fn-bpnf-answer-effects fn-bpn-nth car-cons cdr-cons
                         (:e fn-frame-natp) (:e zp) (:e natp) (:e not)
                         (:e binary-+) (:e fn-cbor-ag-car) (:e equal))))))

;; KEYSTONE (a natural rotation preserves the BP store relation).  Let the
;; open have driven the recovery event the host builds (the auto event over
;; the generation's rows ROWS0 under plan PLAN0, with ACL2's clock-domain
;; decision appended), leaving the machine in ST at that event's epoch.  If
;; the rotation is due and the machine proposes its publication, the
;; checkpoint it publishes, read back as the next open reads it, recovers
;; exactly what full recovery over the old generation does: with no later
;; rows the same replay (held rows, handoffs, arrival frontier) at the
;; rotation's own operation frontier and a zero row count; with later rows
;; that start after it, recovery over the old rows followed by them.
(defthm fn-bpnrd-due-rotation-preserves-recovery
  (let* ((full (fn-bpnr-recover-auto-event st0 base-records sequence-ready
                                           rows0 plan0))
         (e (fn-bpn-nth 1 full))
         (rot (fn-bpnrd-due-rotation-event st profile selected names
                                            (append full (list domain))))
         (eff (car (fn-bpnf-answer-effects
                    (fn-bpnp-rotate-step st (fn-bpn-nth 1 rot)
                                         (fn-bpn-nth 2 rot)))))
         (budget (fn-bpnr-depth-budget
                  (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))))
         (reopen (fn-bpnr-recover-auto-event
                  st0 base-records sequence-ready suffix
                  (fn-bpnr-selection-plan
                   t (fn-bpnr-checkpoint-octets (fn-bpn-nth 4 eff) budget)
                   budget))))
    (implies (and (equal (car eff) :persist-checkpoint)
                  (equal (fn-bpnf-epoch st) e)
                  (true-listp rows0)
                  (not (equal (car plan0) :damaged))
                  (equal (car (fn-bpnr-replay-from
                               (fn-bpnr-plan-checkpoint plan0) rows0
                               (fn-bpnf-base st0)))
                         :ready)
                  (fn-bpnr-rows-start-after suffix (cons e 0)))
             (and (implies (null suffix)
                           (equal reopen
                                  (list :recover-fnbs (1+ e) base-records
                                        sequence-ready
                                        (update-nth 3 (cons e 0)
                                                    (fn-bpn-nth 4 full))
                                        0)))
                  (implies (consp suffix)
                           (equal reopen
                                  (update-nth 5 (len suffix)
                                              (fn-bpnr-recover-auto-event
                                               st0 base-records sequence-ready
                                               (append rows0 suffix)
                                               plan0)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((fn-bpnrd-due-rotation-event
                    st profile selected names
                    (append (fn-bpnr-recover-auto-event
                             st0 base-records sequence-ready rows0 plan0)
                            (list domain))))
           :use ((:instance fn-bpnrd-due-event-checkpoint)
                 (:instance fn-bpnrd-rotate-step-without-generation
                            (ck nil))
                 (:instance fn-bpnp-rotate-step-proposes-only-own-projection
                            (generation
                             (fn-bpn-nth 1 (fn-bpnrd-due-rotation-event
                                            st profile selected names
                                            (append (fn-bpnr-recover-auto-event
                                                     st0 base-records
                                                     sequence-ready rows0 plan0)
                                                    (list domain)))))
                            (ck
                             (fn-bpn-nth 2 (fn-bpnrd-due-rotation-event
                                            st profile selected names
                                            (append (fn-bpnr-recover-auto-event
                                                     st0 base-records
                                                     sequence-ready rows0 plan0)
                                                    (list domain))))))
                 (:instance fn-bpnr-recover-from-checkpoint-equals-full-recover
                            (st st0)
                            (ck1
                             (fn-bpn-nth 2 (fn-bpnrd-due-rotation-event
                                            st profile selected names
                                            (append (fn-bpnr-recover-auto-event
                                                     st0 base-records
                                                     sequence-ready rows0 plan0)
                                                    (list domain)))))
                            (generation
                             (fn-bpn-nth 1 (fn-bpnrd-due-rotation-event
                                            st profile selected names
                                            (append (fn-bpnr-recover-auto-event
                                                     st0 base-records
                                                     sequence-ready rows0 plan0)
                                                    (list domain)))))
                            (covered (len rows0))
                            (budget (fn-bpnr-depth-budget
                                     (fn-bpn-machine-state-max-jobs
                                      (fn-bpnf-base st))))))
           :in-theory (union-theories
                       '(fn-bpnr-checkpoint-of-statep (:e fn-bpn-nth))
                       (theory 'minimal-theory)))))
