; The served BP progress step keeps its own guard premises.
;
; bp-node-progress-guards carries three premises into fn-bpnp-step, the
; function host/native/bp-service.lisp:172 calls after fn-bpnp-host-eventp:
; the base machine state, the session table and the held list's shape.  This
; book proves that one host step preserves all three, so a state that holds
; them at open holds them after every host step.
;
; The base premise carried is fn-bpn-machine-invariantp, which is the guard's
; fn-bpn-machine-statep plus the token and pending bounds.  The base only
; changes through fn-bpn-step, fn-bpn-restart-step and fn-bpn-propose, and
; their existing preservation lemmas (bp-node-machine-invariants) are stated
; for the invariant: a statep-only base whose next token sits at the u64
; bound is not closed under a durable persist.  Initial and recovered bases
; satisfy the invariant, so the stronger premise is the one open provides.
;
; The predicate below is a proof-side recognizer only; the served step never
; runs it.
(in-package "ACL2")
(include-book "bp-node-progress")
(include-book "bp-node-machine-invariants")

(defun fn-bpnp-step-guard-premisesp (st)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bpn-machine-invariantp (fn-bpnf-base st))
       (fn-bpnp-session-listp (fn-bpnp-sessions st))
       (true-listp (fn-bpnf-held-list st))))

(defthm fn-bpnp-step-guard-premisesp-implies-guard
  (implies (and (fn-bpnp-step-guard-premisesp st)
                (fn-bpnp-host-eventp event))
           (and (fn-bpn-machine-statep (fn-bpnf-base st))
                (fn-bpnp-session-listp (fn-bpnp-sessions st))
                (true-listp (fn-bpnf-held-list st))
                (fn-bpnp-host-eventp event)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnp-step-guard-premisesp
                                fn-bpn-machine-invariantp)
                              (theory 'minimal-theory)))))

;; ---------------------------------------------------------------------
;; Shape facts.  Every state the steps build is one of the ten-slot
;; constructors, the progress slot writers, or an argument returned as is.

(local
 (defthm fn-bpnpp-nth-of-nil
   (equal (fn-bpn-nth n nil) nil)
   :hints (("Goal" :in-theory (enable fn-bpn-nth fn-cbor-ag-car)))))

(local
 (defun fn-bpnpp-nth-update-induct (i j l)
   (if (or (zp i) (zp j)) (list i j l)
     (fn-bpnpp-nth-update-induct (1- i) (1- j) (cdr l)))))

(local
 (defthm fn-bpnpp-nth-of-update-nth
   (implies (and (natp i) (natp j) (not (equal i j)))
            (equal (fn-bpn-nth i (update-nth j v l))
                   (fn-bpn-nth i l)))
   :hints (("Goal" :induct (fn-bpnpp-nth-update-induct i j l)
            :in-theory (union-theories
                        '(fn-bpn-nth fn-cbor-ag-car update-nth car-cons cdr-cons
                          zp natp fn-bpnpp-nth-of-nil
                          (:induction fn-bpnpp-nth-update-induct)
                          (:e zp) (:e natp) (:e car) (:e cdr) (:e <)
                          (:e binary-+) (:e unary--) fix)
                        (theory 'minimal-theory))))))

(local
 (defun fn-bpnpp-nth-induct (n l)
   (if (zp n) (list n l) (fn-bpnpp-nth-induct (1- n) (cdr l)))))

(local
 (defthm fn-bpnpp-nth-of-update-nth-same
   (implies (natp n)
            (equal (fn-bpn-nth n (update-nth n v l)) v))
   :hints (("Goal" :induct (fn-bpnpp-nth-induct n l)
            :in-theory (union-theories
                        '(fn-bpn-nth fn-cbor-ag-car update-nth car-cons cdr-cons
                          zp natp (:induction fn-bpnpp-nth-induct)
                          (:e zp) (:e natp) (:e car) (:e cdr) (:e <)
                          (:e binary-+) (:e unary--) fix)
                        (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-slot-writer-fields
   (and (equal (fn-bpnf-base (fn-bpnp-with-waits st w)) (fn-bpnf-base st))
        (equal (fn-bpnf-held-list (fn-bpnp-with-waits st w))
               (fn-bpnf-held-list st))
        (equal (fn-bpnp-sessions (fn-bpnp-with-waits st w))
               (fn-bpnp-sessions st))
        (equal (fn-bpnf-base (fn-bpnp-with-credit st u d)) (fn-bpnf-base st))
        (equal (fn-bpnf-held-list (fn-bpnp-with-credit st u d))
               (fn-bpnf-held-list st))
        (equal (fn-bpnp-sessions (fn-bpnp-with-credit st u d))
               (fn-bpnp-sessions st))
        (equal (fn-bpnf-base (fn-bpnp-with-runtime st s p)) (fn-bpnf-base st))
        (equal (fn-bpnf-held-list (fn-bpnp-with-runtime st s p))
               (fn-bpnf-held-list st))
        (equal (fn-bpnp-sessions (fn-bpnp-with-runtime st s p))
               (if (true-listp st) s (fn-bpnp-sessions st))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-with-waits fn-bpnp-with-credit
                                 fn-bpnp-with-runtime fn-bpnf-base
                                 fn-bpnf-held-list fn-bpnp-sessions
                                 fn-bpnpp-nth-of-update-nth
                                 fn-bpnpp-nth-of-update-nth-same
                                 natp (:e natp) (:e equal))
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-constructor-fields
   (and (equal (fn-bpnf-base (fn-bpnf-state-with-arrival
                              b h o ho c i w e n a)) b)
        (equal (fn-bpnf-held-list (fn-bpnf-state-with-arrival
                                   b h o ho c i w e n a)) h)
        (equal (fn-bpnp-sessions (fn-bpnf-state-with-arrival
                                  b h o ho c i w e n a)) nil)
        (equal (fn-bpnf-answer-state (fn-bpnf-answer s effects)) s))
   :hints (("Goal" :in-theory (enable fn-bpnf-state-with-arrival fn-bpnf-base
                                      fn-bpnf-held-list fn-bpnp-sessions
                                      fn-bpnf-answer fn-bpnf-answer-state
                                      fn-bpn-nth fn-cbor-ag-car)))))

(local
 (defthm fn-bpnpp-true-listp-cons
   (equal (true-listp (cons a b)) (true-listp b))
   :hints (("Goal" :in-theory (union-theories '(true-listp car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-premises-components
   (implies (fn-bpnp-step-guard-premisesp st)
            (and (fn-bpn-machine-invariantp (fn-bpnf-base st))
                 (fn-bpnp-session-listp (fn-bpnp-sessions st))
                 (true-listp (fn-bpnf-held-list st))))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (union-theories '(fn-bpnp-step-guard-premisesp)
                                              (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-premises-of-state-with-arrival
   (equal (fn-bpnp-step-guard-premisesp
           (fn-bpnf-state-with-arrival b h o ho c i w e n a))
          (and (fn-bpn-machine-invariantp b) (true-listp h)))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-step-guard-premisesp
                                 fn-bpnpp-constructor-fields
                                 (:e fn-bpnp-session-listp))
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-premises-of-slot-writers
   (and (equal (fn-bpnp-step-guard-premisesp (fn-bpnp-with-waits st w))
               (fn-bpnp-step-guard-premisesp st))
        (equal (fn-bpnp-step-guard-premisesp (fn-bpnp-with-credit st u d))
               (fn-bpnp-step-guard-premisesp st))
        (implies (and (fn-bpnp-step-guard-premisesp st)
                      (fn-bpnp-session-listp s))
                 (fn-bpnp-step-guard-premisesp
                  (fn-bpnp-with-runtime st s p))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-step-guard-premisesp
                                 fn-bpnpp-slot-writer-fields)
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-premises-of-with-issued
   (implies (fn-bpnp-step-guard-premisesp st)
            (fn-bpnp-step-guard-premisesp (fn-bpnf-with-issued st i)))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnf-with-issued
                                 fn-bpnpp-premises-components
                                 fn-bpnpp-premises-of-state-with-arrival)
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-premises-of-with-base
   (implies (and (true-listp (fn-bpnf-held-list st))
                 (fn-bpn-machine-invariantp b))
            (fn-bpnp-step-guard-premisesp (fn-bpnf-with-base st b)))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnf-with-base
                                 fn-bpnpp-premises-of-state-with-arrival)
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-premises-of-progress-with-issued
   (implies (fn-bpnp-step-guard-premisesp st)
            (fn-bpnp-step-guard-premisesp (fn-bpnp-with-issued st i)))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-with-issued
                                 fn-bpnpp-premises-components
                                 fn-bpnpp-premises-of-slot-writers
                                 fn-bpnpp-premises-of-with-issued)
                               (theory 'minimal-theory))))))

;; ---------------------------------------------------------------------
;; Held-list appliers return a true list whenever they report :ready.

(local
 (defthm fn-bpnpp-replace-dispatched-true-listp
   (implies (true-listp held) (true-listp (fn-bpnp-replace-dispatched a p held)))
   :hints (("Goal" :induct (fn-bpnp-replace-dispatched a p held)
            :in-theory (union-theories
                        '(fn-bpnp-replace-dispatched (:induction fn-bpnp-replace-dispatched) true-listp atom
                          car-cons cdr-cons)
                        (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-attempt-replace-true-listp
   (implies (true-listp held) (true-listp (fn-bpnp-attempt-replace a r held)))
   :hints (("Goal" :induct (fn-bpnp-attempt-replace a r held)
            :in-theory (union-theories
                        '(fn-bpnp-attempt-replace (:induction fn-bpnp-attempt-replace) true-listp atom
                          car-cons cdr-cons)
                        (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-forward-result-replace-true-listp
   (implies (true-listp held) (true-listp (fn-bpnp-forward-result-replace a o held)))
   :hints (("Goal" :induct (fn-bpnp-forward-result-replace a o held)
            :in-theory (union-theories
                        '(fn-bpnp-forward-result-replace (:induction fn-bpnp-forward-result-replace) true-listp atom
                          car-cons cdr-cons)
                        (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-retain-other-rows-true-listp
   (true-listp (fn-bpnf-family-retain-other-rows held consumed))
   :hints (("Goal" :induct (fn-bpnf-family-retain-other-rows held consumed)
            :in-theory (union-theories
                        '(fn-bpnf-family-retain-other-rows (:induction fn-bpnf-family-retain-other-rows) true-listp atom
                          car-cons cdr-cons)
                        (theory 'minimal-theory))))))

(local
 (deftheory fn-bpnpp-replacements-true-listp
   '(fn-bpnpp-replace-dispatched-true-listp fn-bpnpp-attempt-replace-true-listp
     fn-bpnpp-forward-result-replace-true-listp
     fn-bpnpp-retain-other-rows-true-listp)))

(local
 (defthm fn-bpnpp-ready-appliers-true-listp
   (and (implies (and (equal (car (fn-bpnp-dispatch-apply r held)) :ready)
                      (true-listp held))
                 (true-listp (fn-bpn-nth 1 (fn-bpnp-dispatch-apply r held))))
        (implies (and (equal (car (fn-bpnp-attempt-apply r held)) :ready)
                      (true-listp held))
                 (true-listp (fn-bpn-nth 1 (fn-bpnp-attempt-apply r held))))
        (implies (and (equal (car (fn-bpnp-forward-result-apply r held)) :ready)
                      (true-listp held))
                 (true-listp (fn-bpn-nth 1 (fn-bpnp-forward-result-apply
                                            r held)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                        '(fn-bpnp-dispatch-apply fn-bpnp-attempt-apply
                          fn-bpnp-forward-result-apply
                          fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons
                          zp natp (:e zp) (:e natp) (:e binary-+)
                          (:e fn-cbor-ag-car) (:e fn-bpn-nth))
                        (union-theories
                         (theory 'fn-bpnpp-replacements-true-listp)
                         (theory 'minimal-theory)))))))

(local
 (defthm fn-bpnpp-family-apply-at-true-listp
   (implies (equal (fn-cbor-ag-car (fn-bpnf-family-apply-at st r a)) :ready)
            (true-listp (fn-bpn-nth 1 (fn-bpnf-family-apply-at st r a))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                        '(fn-bpnf-family-apply-at fn-bpnf-family-apply
                          fn-bpnpp-true-listp-cons
                          fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons
                          zp natp (:e zp) (:e natp) (:e binary-+)
                          (:e fn-cbor-ag-car) (:e fn-bpn-nth))
                        (union-theories
                         (theory 'fn-bpnpp-replacements-true-listp)
                         (theory 'minimal-theory)))))))

(local
 (defthm fn-bpnpp-apply-delivery-true-listp
   (implies (true-listp held)
            (true-listp (mv-nth 1 (fn-bpah-apply-delivery r held))))
   :hints (("Goal" :induct (fn-bpah-apply-delivery r held)
            :in-theory (union-theories
                        '(fn-bpah-apply-delivery (:induction fn-bpah-apply-delivery) true-listp atom mv-nth
                          car-cons cdr-cons zp (:e zp) (:e binary-+)
                          (:e unary--) (:e mv-nth))
                        (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-apply-delete-true-listp
   (implies (true-listp held)
            (true-listp (mv-nth 1 (fn-bpn-report-apply-delete r held))))
   :hints (("Goal" :induct (fn-bpn-report-apply-delete r held)
            :in-theory (union-theories
                        '(fn-bpn-report-apply-delete (:induction fn-bpn-report-apply-delete) true-listp atom mv-nth
                          car-cons cdr-cons zp (:e zp) (:e binary-+)
                          (:e unary--) (:e mv-nth))
                        (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-recovery-held-true-listp
   (implies (fn-bpnf-recovery-heldp held m o)
            (true-listp held))
   :hints (("Goal" :expand ((fn-bpnf-recovery-heldp held m o))
            :in-theory (disable fn-bpnf-heldp fn-bpnf-held-octets)))))

;; The queue arm's effects are the machine's effect vocabulary.
(local
 (defthm fn-bpnpp-queue-effects
   (and (fn-bpn-effect-listp
         (list (list :bundle-queue-accepted a b c d :durable)))
        (fn-bpn-effectp (list :bundle-queue-refused a b c :persistence-refused))
        (fn-bpn-effectp (list :bundle-queue-uncertain a b c :persistence)))))

;; ---------------------------------------------------------------------
;; Session table.

(local
 (defthm fn-bpnpp-remove-peer-session-listp
   (implies (fn-bpnp-session-listp sessions)
            (fn-bpnp-session-listp
             (fn-bpnp-remove-peer-session peer sessions)))
   :hints (("Goal" :induct (fn-bpnp-remove-peer-session peer sessions)
            :in-theory (union-theories
                        '(fn-bpnp-remove-peer-session fn-bpnp-session-listp
                          (:induction fn-bpnp-remove-peer-session) atom
                          car-cons cdr-cons)
                        (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-open-session-listp
   (implies (and (fn-bpnp-session-listp sessions)
                 (fn-bpnp-sessionp (fn-bpnp-session peer session mru)))
            (fn-bpnp-session-listp
             (fn-bpnp-open-session sessions peer session mru)))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-open-session fn-bpnp-session-listp
                                 fn-bpnpp-remove-peer-session-listp
                                 car-cons cdr-cons)
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-session-event-row
   (implies (and (fn-bpnp-host-eventp event)
                 (equal (fn-cbor-ag-car event) :session))
            (fn-bpnp-sessionp
             (fn-bpnp-session (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
                              (fn-bpn-nth 4 event))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnp-host-eventp fn-bpnp-sessionp
                                                 fn-bpnp-session)
                            (fn-bpp-eidp fn-bpnp-session-idp
                             fn-clock-observationp fn-bpnf-host-eventp
                             fn-bpnp-routesp fn-bpnp-forward-outcomep))))))

;; The host event supplies the delegated arms' own premises.
(local
 (defthm fn-bpnpp-delegate-event-premises
   (implies (and (fn-bpnp-host-eventp event)
                 (not (equal (fn-cbor-ag-car event) :progress)))
            (and (or (not (equal (fn-cbor-ag-car event) :base))
                     (fn-bpn-machine-eventp (fn-bpn-nth 1 event)))
                 (or (not (equal (fn-cbor-ag-car event) :recover-fnbs))
                     (and (true-listp (fn-bpn-nth 2 event))
                          (<= (len (fn-bpn-nth 2 event))
                              *fn-bpn-machine-max-records*)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnp-host-eventp fn-bpnf-host-eventp)
                            (fn-bpn-machine-eventp fn-bpb-bundlep
                             fn-bpp-blockp fn-bpn-nth-is-nth-on-true-lists
                             fn-bpf-fragment-listp-is-a-true-list
                             fn-bpf-fragment-listp fn-bpf-fragmentp
                             fn-cp-idp))))
   :rule-classes nil))

;; BP-R17's deferral writes only the marker (slot 7) and the waits (11).
(local
 (defthm fn-bpnpp-nth-is-nth
   (implies (natp n)
            (equal (fn-bpn-nth n xs) (nth n xs)))
   :hints (("Goal" :induct (fn-bpn-nth n xs)
            :in-theory (enable fn-bpn-nth nth fn-cbor-ag-car)))))

(local
 (defthm fn-bpnpp-premises-of-busy-slots
   (equal (fn-bpnp-step-guard-premisesp
           (update-nth 11 w (update-nth 7 nil st)))
          (fn-bpnp-step-guard-premisesp st))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-step-guard-premisesp
                                 fn-bpnf-base fn-bpnp-sessions
                                 fn-bpnf-held-list fn-bpnpp-nth-is-nth
                                 nth-update-nth (:e natp) (:e nfix)
                                 (:e equal))
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-true-listp-of-deferral-replace
   (implies (true-listp held)
            (true-listp (fn-bpnp-deferral-replace arrival count held)))
   :hints (("Goal" :in-theory (enable fn-bpnp-deferral-replace)))))

; The kind-20 persist arm writes the held list (slot 2) whole.
(local
 (defthm fn-bpnpp-premises-of-held-write
   (implies (true-listp h)
            (equal (fn-bpnp-step-guard-premisesp (update-nth 2 h st))
                   (and (fn-bpn-machine-invariantp (fn-bpnf-base st))
                        (fn-bpnp-session-listp (fn-bpnp-sessions st)))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-step-guard-premisesp
                                 fn-bpnf-base fn-bpnp-sessions
                                 fn-bpnf-held-list fn-bpnpp-nth-is-nth
                                 nth-update-nth (:e natp) (:e nfix)
                                 (:e equal))
                               (theory 'minimal-theory))))))

(local (in-theory (disable fn-bpnpp-nth-is-nth)))

(local (in-theory (disable fn-bpnp-step-guard-premisesp)))

(local
 (deftheory fn-bpnpp-theory
   (union-theories
    '(fn-bpnpp-constructor-fields fn-bpnpp-slot-writer-fields
      fn-bpnpp-premises-components
      fn-bpnpp-premises-of-state-with-arrival
      fn-bpnpp-premises-of-slot-writers
      fn-bpnpp-premises-of-with-issued
      fn-bpnpp-premises-of-with-base
      fn-bpnpp-premises-of-progress-with-issued
      fn-bpnpp-true-listp-cons
      fn-bpnpp-ready-appliers-true-listp
      fn-bpnpp-family-apply-at-true-listp
      fn-bpnpp-apply-delivery-true-listp
      fn-bpnpp-apply-delete-true-listp
      fn-bpnpp-recovery-held-true-listp
      fn-bpnpp-queue-effects
      fn-bpn-step-preserves-machine-invariant
      fn-bpn-restart-step-preserves-machine-invariant
      fn-bpn-propose-preserves-machine-invariant
      (:e fn-cbor-ag-car) (:e fn-bpnp-session-listp))
    (theory 'minimal-theory))))

;; ---------------------------------------------------------------------
;; One lemma per step, each opening only that step.

(defmacro fn-bpnpp-defkeep (name call defs &key hyps event)
  `(local
    (defthm ,name
      (implies (and (fn-bpnp-step-guard-premisesp st)
                    ,@(and event
                           '((or (not (equal (fn-cbor-ag-car event) :base))
                                 (fn-bpn-machine-eventp (fn-bpn-nth 1 event)))
                             (or (not (equal (fn-cbor-ag-car event)
                                             :recover-fnbs))
                                 (and (true-listp (fn-bpn-nth 2 event))
                                      (<= (len (fn-bpn-nth 2 event))
                                          *fn-bpn-machine-max-records*)))))
                    ,@hyps)
               (fn-bpnp-step-guard-premisesp (fn-bpnf-answer-state ,call)))
      :hints (("Goal" :do-not-induct t
               :in-theory (union-theories ',defs
                                          (theory 'fn-bpnpp-theory)))))))

(fn-bpnpp-defkeep fn-bpnpp-deliver-step
  (fn-bpah-deliver-step st key node)
  (fn-bpah-deliver-step))

(fn-bpnpp-defkeep fn-bpnpp-deliver-result-step
  (fn-bpah-deliver-result-step st epoch marker-id key
                                                status detail)
  (fn-bpah-deliver-result-step))

(fn-bpnpp-defkeep fn-bpnpp-persist-delivery-step
  (fn-bpah-persist-delivery-step st epoch operation-id
                                                  result)
  (fn-bpah-persist-delivery-step))

(fn-bpnpp-defkeep fn-bpnpp-recover-fnbs-step
  (fn-bpnf-recover-fnbs-step st new-epoch base-records
                                              sequence-ready replay-result)
  (fn-bpnf-recover-fnbs-step)
  :hyps ((true-listp base-records)
                    (<= (len base-records) *fn-bpn-machine-max-records*)))

(fn-bpnpp-defkeep fn-bpnpp-foundation-step
  (fn-bpnf-step st event)
  (fn-bpnf-step fn-bpnpp-deliver-step
                           fn-bpnpp-deliver-result-step
                           fn-bpnpp-persist-delivery-step
                           fn-bpnpp-recover-fnbs-step)
  :event t)

(fn-bpnpp-defkeep fn-bpnpp-family-propose-step
  (fn-bpnf-family-propose-step st anchor-arrival observation)
  (fn-bpnf-family-propose-step))

(fn-bpnpp-defkeep fn-bpnpp-family-persist-step
  (fn-bpnf-family-persist-step st epoch op result)
  (fn-bpnf-family-persist-step))

(fn-bpnpp-defkeep fn-bpnpp-fragment-step
  (fn-bpnf-fragment-step st event)
  (fn-bpnf-fragment-step fn-bpnpp-foundation-step
                           fn-bpnpp-family-propose-step
                           fn-bpnpp-family-persist-step)
  :event t)

(fn-bpnpp-defkeep fn-bpnpp-delete-propose-step
  (fn-bpn-report-delete-propose-step st observation enabled)
  (fn-bpn-report-delete-propose-step))

(fn-bpnpp-defkeep fn-bpnpp-delete-persist-step
  (fn-bpn-report-delete-persist-step st epoch op result)
  (fn-bpn-report-delete-persist-step))

(fn-bpnpp-defkeep fn-bpnpp-report-step
  (fn-bpn-report-step st event)
  (fn-bpn-report-step fn-bpnpp-fragment-step
                           fn-bpnpp-delete-propose-step
                           fn-bpnpp-delete-persist-step)
  :event t)

(fn-bpnpp-defkeep fn-bpnpp-queue-step
  (fn-bpn-report-queue-step st arrival sequence route
                                             observation)
  (fn-bpn-report-queue-step))

(fn-bpnpp-defkeep fn-bpnpp-report-author-step
  (fn-bpn-report-author-step st event)
  (fn-bpn-report-author-step fn-bpnpp-report-step
                           fn-bpnpp-queue-step)
  :event t)

;; The credit refusal of a delivery re-enters the author step with a
;; :deliver-result event, which is neither a base nor a recovery event.
(fn-bpnpp-defkeep fn-bpnpp-credit-refusal
  (fn-bpnp-credit-refusal st event kind)
  (fn-bpnp-credit-refusal fn-bpnpp-report-author-step
                           fn-cbor-ag-car car-cons))

(fn-bpnpp-defkeep fn-bpnpp-delegate-with-credit
  (fn-bpnp-delegate-with-credit st event)
  (fn-bpnp-delegate-with-credit
                           fn-bpnpp-report-author-step
                           fn-bpnpp-credit-refusal)
  :event t)

(local
 (defthm fn-bpnpp-preserve-runtime-answer
   (implies (and (fn-bpnp-step-guard-premisesp (fn-bpnf-answer-state answer))
                 (fn-bpnp-session-listp (fn-bpnp-sessions st)))
            (fn-bpnp-step-guard-premisesp
             (fn-bpnf-answer-state
              (fn-bpnp-preserve-runtime-answer answer st recovery))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-bpnp-preserve-runtime-answer)
                                       (theory 'fn-bpnpp-theory))))))

(fn-bpnpp-defkeep fn-bpnpp-transit-dispatch-step
  (fn-bpnp-transit-dispatch-step st h peer node)
  (fn-bpnp-transit-dispatch-step))

(fn-bpnpp-defkeep fn-bpnpp-progress-step
  (fn-bpnp-progress-step st node observation routes
                                          generation budget)
  (fn-bpnp-progress-step fn-bpnpp-deliver-step
                           fn-bpnpp-transit-dispatch-step))

(fn-bpnpp-defkeep fn-bpnpp-dispatch-persist-step
  (fn-bpnp-dispatch-persist-step st epoch op result)
  (fn-bpnp-dispatch-persist-step))

(fn-bpnpp-defkeep fn-bpnpp-clock-domain-fence
  (fn-bpnp-clock-domain-fence st plan)
  (fn-bpnp-clock-domain-fence))

(fn-bpnpp-defkeep fn-bpnpp-conflict-propose-step
  (fn-bpnp-conflict-propose-step st event h)
  (fn-bpnp-conflict-propose-step fn-bpnp-with-next-issued
   fn-bpnp-conflict-refusal))

(fn-bpnpp-defkeep fn-bpnpp-busy-delivery-step
  (fn-bpnp-busy-delivery-step st epoch op key observation budgets)
  (fn-bpnp-busy-delivery-step fn-bpnp-with-next-issued
   fn-bpnpp-premises-of-busy-slots))

(fn-bpnpp-defkeep fn-bpnpp-deferral-persist-step
  (fn-bpnp-deferral-persist-step st epoch op result)
  (fn-bpnp-deferral-persist-step fn-bpnp-deferral-apply
   fn-bpnpp-premises-of-held-write fn-bpnpp-true-listp-of-deferral-replace))

(fn-bpnpp-defkeep fn-bpnpp-busy-resume-step
  (fn-bpnp-busy-resume-step st arrival budget)
  (fn-bpnp-busy-resume-step fn-bpnp-with-next-issued))

(fn-bpnpp-defkeep fn-bpnpp-conflict-persist-step
  (fn-bpnp-conflict-persist-step st epoch op result)
  (fn-bpnp-conflict-persist-step fn-bpnp-conflict-refusal))

(fn-bpnpp-defkeep fn-bpnpp-start-one
  (fn-bpnp-start-one st peer session mru observation budget)
  (fn-bpnp-start-one))

(fn-bpnpp-defkeep fn-bpnpp-attempt-persist-step
  (fn-bpnp-attempt-persist-step st epoch op result)
  (fn-bpnp-attempt-persist-step))

(fn-bpnpp-defkeep fn-bpnpp-forward-result-propose-step
  (fn-bpnp-forward-result-propose-step
                    st attempt-epoch attempt-op session outcome observation)
  (fn-bpnp-forward-result-propose-step))

(fn-bpnpp-defkeep fn-bpnpp-operator-resume-step
  (fn-bpnp-operator-resume-step st arrival budget)
  (fn-bpnp-operator-resume-step))

(fn-bpnpp-defkeep fn-bpnpp-forward-result-persist-step
  (fn-bpnp-forward-result-persist-step st epoch op result)
  (fn-bpnp-forward-result-persist-step))

;; ---------------------------------------------------------------------
;; KEYSTONE.  The served step keeps the conjunction of its guard premises
;; (base premise carried as the machine invariant) over every host event.

(defthm fn-bpnp-step-preserves-guard-premises
  (implies (and (fn-bpnp-step-guard-premisesp st)
                (fn-bpnp-host-eventp event))
           (fn-bpnp-step-guard-premisesp
            (fn-bpnf-answer-state (fn-bpnp-step st event))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnpp-delegate-event-premises)
                 (:instance fn-bpnpp-session-event-row))
           :in-theory (union-theories
                       '(fn-bpnp-step
                         fn-bpnpp-remove-peer-session-listp
                         fn-bpnpp-open-session-listp
                         fn-bpnpp-start-one fn-bpnpp-forward-result-propose-step
                         fn-bpnpp-operator-resume-step
                         fn-bpnpp-progress-step fn-bpnpp-dispatch-persist-step
                         fn-bpnpp-attempt-persist-step
                         fn-bpnpp-forward-result-persist-step
                         fn-bpnpp-clock-domain-fence
                         fn-bpnpp-conflict-propose-step
                         fn-bpnpp-conflict-persist-step
                         fn-bpnpp-busy-delivery-step
                         fn-bpnpp-deferral-persist-step
                         fn-bpnpp-busy-resume-step
                         fn-bpnpp-delegate-with-credit
                         fn-bpnpp-preserve-runtime-answer)
                       (theory 'fn-bpnpp-theory)))))

;; The three guard premises, each as its own statement over the same
;; carried conjunction.
(defthm fn-bpnp-step-preserves-session-listp
  (implies (and (fn-bpnp-step-guard-premisesp st)
                (fn-bpnp-host-eventp event))
           (fn-bpnp-session-listp
            (fn-bpnp-sessions (fn-bpnf-answer-state (fn-bpnp-step st event)))))
  :hints (("Goal" :use fn-bpnp-step-preserves-guard-premises
           :in-theory (union-theories '(fn-bpnp-step-guard-premisesp)
                                      (theory 'minimal-theory)))))

(defthm fn-bpnp-step-preserves-held-true-listp
  (implies (and (fn-bpnp-step-guard-premisesp st)
                (fn-bpnp-host-eventp event))
           (true-listp
            (fn-bpnf-held-list (fn-bpnf-answer-state (fn-bpnp-step st event)))))
  :hints (("Goal" :use fn-bpnp-step-preserves-guard-premises
           :in-theory (union-theories '(fn-bpnp-step-guard-premisesp)
                                      (theory 'minimal-theory)))))

(defthm fn-bpnp-step-preserves-base-statep
  (implies (and (fn-bpnp-step-guard-premisesp st)
                (fn-bpnp-host-eventp event))
           (and (fn-bpn-machine-invariantp
                 (fn-bpnf-base (fn-bpnf-answer-state (fn-bpnp-step st event))))
                (fn-bpn-machine-statep
                 (fn-bpnf-base (fn-bpnf-answer-state (fn-bpnp-step st event))))))
  :hints (("Goal" :use fn-bpnp-step-preserves-guard-premises
           :in-theory (union-theories '(fn-bpnp-step-guard-premisesp
                                        fn-bpn-machine-invariantp)
                                      (theory 'minimal-theory)))))

;; ---------------------------------------------------------------------
;; Recovery clears the volatile runtime fields.  A recovery event reaches
;; fn-bpnf-recover-fnbs-step through the four delegating layers; its answer
;; is either a :restart-fault or a :restart-ready over a freshly built state.

(local
 (defthm fn-bpnpp-answer-effects-of-answer
   (equal (fn-bpnf-answer-effects (fn-bpnf-answer s effects)) effects)
   :hints (("Goal" :in-theory (enable fn-bpnf-answer fn-bpnf-answer-effects
                                      fn-bpn-nth fn-cbor-ag-car)))))

(local
 (defthm fn-bpnpp-recover-fnbs-step-outcome
   (let ((tag (fn-bpn-nth 0 (fn-bpn-nth 0 (fn-bpnf-answer-effects
                                           (fn-bpnf-recover-fnbs-step
                                            st e r s rr))))))
     (implies (not (equal tag :restart-fault))
              (and (equal tag :restart-ready)
                   (true-listp (fn-bpnf-answer-state
                                (fn-bpnf-recover-fnbs-step st e r s rr))))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                        '(fn-bpnf-recover-fnbs-step fn-bpnf-answer
                          fn-bpnf-answer-state fn-bpnf-answer-effects
                          fn-bpnf-state-with-arrival fn-bpn-nth fn-cbor-ag-car
                          fn-bpnpp-true-listp-cons car-cons cdr-cons
                          zp natp (:e zp) (:e natp) (:e true-listp)
                          (:e binary-+) (:e unary--) (:e <) (:e equal))
                        (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-author-step-of-recovery
   (implies (equal (fn-cbor-ag-car event) :recover-fnbs)
            (equal (fn-bpn-report-author-step st event)
                   (fn-bpnf-recover-fnbs-step
                    st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
                    (fn-bpn-nth 3 event) (fn-bpn-nth 4 event))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                        '(fn-bpn-report-author-step fn-bpn-report-step
                          fn-bpnf-fragment-step fn-bpnf-step (:e equal))
                        (theory 'minimal-theory))))))

(local
 (defthm fn-bpnpp-slot-writers-true-listp
   (implies (true-listp st)
            (and (true-listp (fn-bpnp-with-waits st w))
                 (true-listp (fn-bpnp-with-credit st u d))))
   :hints (("Goal" :in-theory (enable fn-bpnp-with-waits fn-bpnp-with-credit)))))

(local
 (defthm fn-bpnpp-delegate-recovery-ready
   (implies (and (equal (fn-cbor-ag-car event) :recover-fnbs)
                 (equal (fn-bpn-nth 0 (fn-bpn-nth 0 (fn-bpnf-answer-effects
                                                     (fn-bpnp-delegate-with-credit
                                                      st event))))
                        :restart-ready))
            (true-listp (fn-bpnf-answer-state
                         (fn-bpnp-delegate-with-credit st event))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bpnpp-recover-fnbs-step-outcome
                             (e (fn-bpn-nth 1 event)) (r (fn-bpn-nth 2 event))
                             (s (fn-bpn-nth 3 event)) (rr (fn-bpn-nth 4 event))))
            :in-theory (union-theories
                        '(fn-bpnp-delegate-with-credit
                          fn-bpnpp-author-step-of-recovery
                          fn-bpnp-credit-proposal-kind
                          fn-bpnpp-slot-writers-true-listp
                          fn-bpnpp-answer-effects-of-answer
                          fn-bpnpp-constructor-fields
                          (:e equal))
                        (theory 'minimal-theory))))))

;; A recovery whose first effect is :restart-ready leaves no outbound
;; session and no pending kind-8 wire.  The recovery-event hypothesis scopes
;; the statement to the arm the proof opens; only fn-bpnf-recover-fnbs-step
;; builds a :restart-ready effect, so it has no separating must-fail.
(defthm fn-bpnp-recovery-success-clears-sessions-and-pending-image
  (implies (and (equal (fn-cbor-ag-car event) :recover-fnbs)
                (equal (fn-bpn-nth 0 (fn-bpn-nth 0 (fn-bpnf-answer-effects
                                                    (fn-bpnp-step st event))))
                       :restart-ready))
           (and (null (fn-bpnp-sessions
                       (fn-bpnf-answer-state (fn-bpnp-step st event))))
                (null (fn-bpnp-pending-image
                       (fn-bpnf-answer-state (fn-bpnp-step st event))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnpp-delegate-recovery-ready))
           :in-theory (union-theories
                       '(fn-bpnp-step fn-bpnp-preserve-runtime-answer
                         fn-bpnp-with-runtime fn-bpnp-sessions
                         fn-bpnp-pending-image
                         fn-bpnpp-nth-of-update-nth
                         fn-bpnpp-nth-of-update-nth-same
                         fn-bpnpp-answer-effects-of-answer
                         fn-bpnpp-constructor-fields
                         fn-bpnp-conflict-held fn-bpnp-clock-domain-fence
                         fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons
                         natp (:e natp) (:e equal))
                       (theory 'minimal-theory)))))

;; ---------------------------------------------------------------------
;; The kind-8 retry count survives recovery (spec bp-node-machine 4.3.1).
;; The count lives in each held row's attempt slot, (:forwarding epoch op
;; peer session retries).  No kind-8 record stores it: ordered replay derives
;; it, one durable kind 8 at a time, through fn-bpnp-attempt-apply, the
;; function the live :persist-result arm also calls.  What recovery must not
;; do is reset it; these two theorems say it installs the replayed rows
;; exactly, so the count after recovery is the count the durable rows give.

(local
 (defthm fn-bpnpp-recover-fnbs-step-ready-held
   (implies (equal (fn-bpn-nth 0 (fn-bpn-nth 0 (fn-bpnf-answer-effects
                                              (fn-bpnf-recover-fnbs-step
                                               st e r s rr))))
                   :restart-ready)
            (equal (fn-bpnf-held-list (fn-bpnf-answer-state
                                       (fn-bpnf-recover-fnbs-step st e r s rr)))
                   (fn-bpn-nth 1 rr)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                        '(fn-bpnf-recover-fnbs-step fn-bpnf-answer
                          fn-bpnf-answer-state fn-bpnf-answer-effects
                          fn-bpnpp-constructor-fields
                          fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons
                          zp natp (:e zp) (:e natp) (:e equal))
                        (theory 'minimal-theory))))))

;; KEYSTONE.  A recovery through fn-bpnp-step that answers :restart-ready
;; installs, as its held list, exactly the replay result the event carries.
;; The recovery-event hypothesis scopes the statement to the arm the proof
;; opens (only fn-bpnf-recover-fnbs-step builds :restart-ready, so it has no
;; separating must-fail); without :restart-ready (a clock-domain fence) the
;; held list is the one before recovery.
(defthm fn-bpnp-recovery-success-installs-the-replayed-held
  (implies (and (equal (fn-cbor-ag-car event) :recover-fnbs)
                (equal (fn-bpn-nth 0 (fn-bpn-nth 0 (fn-bpnf-answer-effects
                                                    (fn-bpnp-step st event))))
                       :restart-ready))
           (equal (fn-bpnf-held-list
                   (fn-bpnf-answer-state (fn-bpnp-step st event)))
                  (fn-bpn-nth 1 (fn-bpn-nth 4 event))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnpp-recover-fnbs-step-ready-held
                            (e (fn-bpn-nth 1 event)) (r (fn-bpn-nth 2 event))
                            (s (fn-bpn-nth 3 event)) (rr (fn-bpn-nth 4 event)))
                 (:instance fn-bpnpp-recover-fnbs-step-outcome
                            (e (fn-bpn-nth 1 event)) (r (fn-bpn-nth 2 event))
                            (s (fn-bpn-nth 3 event)) (rr (fn-bpn-nth 4 event))))
           :in-theory (union-theories
                       '(fn-bpnp-step fn-bpnp-preserve-runtime-answer
                         fn-bpnp-delegate-with-credit
                         fn-bpnpp-author-step-of-recovery
                         fn-bpnp-credit-proposal-kind
                         fn-bpnpp-slot-writer-fields
                         fn-bpnpp-answer-effects-of-answer
                         fn-bpnpp-constructor-fields
                         fn-bpnp-conflict-held fn-bpnp-clock-domain-fence
                         fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons
                         natp (:e natp) (:e equal))
                       (theory 'minimal-theory)))))

;; The same, over the event the host builds (host/native/bp-service.lisp,
;; the recovery path: fn-bpnf-family-recover-auto-event over the rows read
;; from the FNBS directory, with ACL2's clock-domain decision appended): the
;; held rows, and so every attempt slot's retry count, after a ready
;; recovery are those fn-bpnf-family-replay-rows computes from the durable
;; rows.  A process restart therefore cannot reset the count below what the
;; durable kind-8 rows record.
(defthm fn-bpnp-host-recovery-installs-the-durable-replay
  (let ((event (append (fn-bpnf-family-recover-auto-event
                        st base-records sequence-ready rows)
                       (list domain))))
    (implies (equal (fn-bpn-nth 0 (fn-bpn-nth 0 (fn-bpnf-answer-effects
                                                 (fn-bpnp-step st event))))
                    :restart-ready)
             (equal (fn-bpnf-held-list
                     (fn-bpnf-answer-state (fn-bpnp-step st event)))
                    (fn-bpn-nth 1 (fn-bpnf-family-replay-rows
                                   rows (fn-bpnf-base st))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-recovery-success-installs-the-replayed-held
                            (event (append (fn-bpnf-family-recover-auto-event
                                            st base-records sequence-ready rows)
                                           (list domain)))))
           :in-theory (union-theories
                       '(fn-bpnf-family-recover-auto-event
                         fn-bpn-nth fn-cbor-ag-car binary-append
                         car-cons cdr-cons zp natp
                         (:e zp) (:e natp) (:e binary-+) (:e equal) (:e consp) (:e <))
                       (theory 'minimal-theory)))))

;; Open: the host builds fn-bpnf-initial-state and refuses to serve unless
;; its base satisfies fn-bpn-machine-invariantp (host/native/bp-service.lisp,
;; the two invariant checks in the open path).  That check is the whole
;; premise: the initial session table and held list are empty.
(defthm fn-bpnp-initial-state-guard-premises
  (implies (fn-bpn-machine-invariantp
            (fn-bpnf-base (fn-bpnf-initial-state config max-held max-octets)))
           (fn-bpnp-step-guard-premisesp
            (fn-bpnf-initial-state config max-held max-octets)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnf-initial-state fn-bpnf-state
                         (:e true-listp) (:e fn-bpnf-base)
                         (:e fn-bpn-machine-invariantp))
                       (theory 'fn-bpnpp-theory)))))

;; Over a host trace: premises at open hold after every step.
(defun fn-bpnp-host-trace (st events)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom events) st
    (fn-bpnp-host-trace (fn-bpnf-answer-state (fn-bpnp-step st (car events)))
                        (cdr events))))

(defun fn-bpnp-host-event-listp (events)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom events) t
    (and (fn-bpnp-host-eventp (car events))
         (fn-bpnp-host-event-listp (cdr events)))))

(defthm fn-bpnp-host-trace-preserves-guard-premises
  (implies (and (fn-bpnp-step-guard-premisesp st)
                (fn-bpnp-host-event-listp events))
           (fn-bpnp-step-guard-premisesp (fn-bpnp-host-trace st events)))
  :hints (("Goal" :induct (fn-bpnp-host-trace st events)
           :in-theory (union-theories
                       '(fn-bpnp-host-trace fn-bpnp-host-event-listp
                         fn-bpnp-step-preserves-guard-premises)
                       (theory 'minimal-theory)))))
