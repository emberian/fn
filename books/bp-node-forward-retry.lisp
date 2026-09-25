; Retry after an uncertain forwarding attempt (spec bp-node-machine 4.3.1;
; decision candidate of 2026-09-24, default adopted by the coordinator,
; pending ember).  The host calls fn-bpnp-step (host/native/bp-service.lisp
; fnn-bps-foundation-step); its :session arm calls fn-bpnp-start-one, which
; selects with fn-bpnp-forward-scan, and its :persist-result arm for an
; :attempt calls fn-bpnp-attempt-persist-step, which applies kind 8 with
; fn-bpnp-attempt-apply, the function ordered FNBS replay also calls.
(in-package "ACL2")
(include-book "bp-node-progress")
(set-verify-guards-eagerness 0)

; Every row of ORDERED other than H is not a forward candidate.
(defun fn-bpnp-only-forward-candidatep (ordered h peer observation epoch budget)
  (declare (xargs :guard t :measure (acl2-count ordered)))
  (if (atom ordered) t
    (and (or (equal (car ordered) h)
             (not (fn-bpnp-forward-candidatep
                   (car ordered) peer observation epoch budget)))
         (fn-bpnp-only-forward-candidatep
          (cdr ordered) h peer observation epoch budget))))

;; (a) Selection keystone.  A row left with an uncertain attempt under the
;; bound is a forward candidate; when no other row competes for this
;; session's peer and it fits and is not waiting, the scan the step calls
;; returns it with its forwarding image and the waits unchanged.
;; Competition among candidates is the arrival-order fairness of N03/N04
;; and is not claimed here.
(defthm fn-bpnp-forward-scan-offers-the-only-candidate
  (implies (and (member-equal h ordered)
                (fn-bpnp-only-forward-candidatep
                 ordered h peer observation epoch budget)
                (fn-bpnp-forward-candidatep h peer observation epoch budget)
                (not (fn-bpnp-forward-mru-waitp h peer mru waits))
                (not (fn-bpnp-credit-blockedp h waits free))
                (equal (car (fn-bpnp-forward-image h node observation)) :ready)
                (<= (len (fn-bpn-nth 1 (fn-bpnp-forward-image
                                        h node observation)))
                    mru))
           (equal (fn-bpnp-forward-scan
                   ordered peer mru node observation waits free epoch budget)
                  (list :ready h
                        (fn-bpn-nth 1 (fn-bpnp-forward-image h node observation))
                        (fn-bpb-bundle-age
                         (fn-bpn-nth 2 (fn-bpnp-forward-image h node observation)))
                        waits)))
  :hints (("Goal" :induct (fn-bpnp-forward-scan
                           ordered peer mru node observation waits free epoch
                           budget)
           :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (union-theories
                       '(fn-bpnp-forward-scan fn-bpnp-only-forward-candidatep
                         member-equal)
                       (theory 'minimal-theory)))))

;; The uncertain slot is what makes the row a candidate: the same row with
;; an attempt of the current epoch (a live attempt) is not one.
(defthm fn-bpnp-uncertain-attempt-row-is-a-forward-candidate-by-definition
  (implies (and (equal (fn-bpn-nth 0 h) :bpnf-held)
                (natp (fn-bpn-nth 3 h))
                (equal (fn-bpn-nth 11 h) peer)
                (equal (fn-bpn-nth 12 h) '(:forward-pending))
                (null (fn-bpn-nth 14 h))
                (equal (fn-bpnp-held-expiry h observation) :live)
                (fn-bpnp-uncertain-attemptp (fn-bpn-nth 13 h) epoch peer)
                (< (fn-bpnp-attempt-retries (fn-bpn-nth 13 h)) (nfix budget)))
           (fn-bpnp-forward-candidatep h peer observation epoch budget))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnp-forward-candidatep
                                fn-bpnp-retry-eligible-slotp)
                              (theory 'minimal-theory)))))

;; A stranded report is only a report: never an attempt proposal.
(defthm fn-bpnp-stranded-effects-propose-nothing
  (not (equal (car (car (fn-bpnp-stranded-effects held peer epoch budget)))
              :persist-attempt))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnp-stranded-effects car-cons
                                (:executable-counterpart equal))
                              (theory 'minimal-theory)))))

(local
 (defthm fn-bpnp-true-listp-of-slot-writers
   (and (true-listp (fn-bpnf-state-with-arrival b h o ho c i w e n a))
        (implies (true-listp st) (true-listp (fn-bpnp-with-waits st waits)))
        (implies (true-listp st)
                 (true-listp (fn-bpnp-with-credit st used debt))))))

(local
 (defthm fn-bpnp-pending-image-of-with-runtime
   (implies (true-listp st)
            (equal (fn-bpnp-pending-image (fn-bpnp-with-runtime st s p)) p))
   :hints (("Goal" :in-theory (enable fn-bpn-nth)))))

;; Bridge to the called step.  First start-one: an offer names the row the
;; scan chose, with its primary identity, and the pending image is the scan's
;; forwarding image of that row.
(defthm fn-bpnp-start-one-offer-is-the-scan-choice
  (let* ((answer (fn-bpnp-start-one st peer session mru observation budget))
         (effect (car (fn-bpnf-answer-effects answer)))
         (record (fn-bpn-nth 3 effect))
         (scan (fn-bpnp-forward-scan
                (reverse (fn-bpnf-held-list st)) peer mru
                (fn-bpn-config-node-id
                 (fn-bpn-machine-state-config (fn-bpnf-base st)))
                observation (fn-bpnp-waits st)
                (fn-bpnd-free (fn-bpnp-used st) (fn-bpnp-debt st)
                              *fn-bpnp-control-margin*)
                (fn-bpnf-epoch st) budget)))
    (implies (equal (car effect) :persist-attempt)
             (and (equal (car scan) :ready)
                  (equal (fn-bpn-nth 3 record) (fn-bpn-nth 3 (fn-bpn-nth 1 scan)))
                  (equal (fn-bpn-nth 4 record)
                         (fn-bpah-held-primary-identity (fn-bpn-nth 1 scan)))
                  (equal (fn-bpn-nth 2 (fn-bpnp-pending-image
                                        (fn-bpnf-answer-state answer)))
                         (fn-bpn-nth 2 scan)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (union-theories
                       '(fn-bpnp-start-one fn-bpnf-answer fn-bpnf-answer-state
                         fn-bpnf-answer-effects fn-bpn-nth
                         fn-bpnp-forward-attempt-record
                         fn-bpnp-stranded-effects-propose-nothing
                         fn-bpnp-true-listp-of-slot-writers
                         fn-bpnp-pending-image-of-with-runtime
                         fn-cbor-ag-car natp
                         (:executable-counterpart natp)
                         (:executable-counterpart not)
                         car-cons cdr-cons
                         (:executable-counterpart equal)
                         (:executable-counterpart car)
                         (:executable-counterpart zp)
                         (:executable-counterpart fn-bpn-nth))
                       (theory 'minimal-theory)))))

(local
 (defthm fn-bpnp-with-runtime-keeps-selection-inputs
   (and (equal (fn-bpnf-held-list (fn-bpnp-with-runtime st s p))
               (fn-bpnf-held-list st))
        (equal (fn-bpnf-base (fn-bpnp-with-runtime st s p)) (fn-bpnf-base st))
        (equal (fn-bpnp-waits (fn-bpnp-with-runtime st s p)) (fn-bpnp-waits st))
        (equal (fn-bpnp-used (fn-bpnp-with-runtime st s p)) (fn-bpnp-used st))
        (equal (fn-bpnp-debt (fn-bpnp-with-runtime st s p)) (fn-bpnp-debt st))
        (equal (fn-bpnf-epoch (fn-bpnp-with-runtime st s p)) (fn-bpnf-epoch st)))
   :hints (("Goal" :in-theory (enable fn-bpn-nth)))))

;; Then the step the host calls: its :session open arm is start-one on the
;; state with the session installed, and the selection inputs are the
;; state's own.
(defthm fn-bpnp-step-session-offer-is-the-scan-choice
  (let* ((answer (fn-bpnp-step st (list :session peer session t mru observation)))
         (budget *fn-bpnp-max-forward-retries*)
         (effect (car (fn-bpnf-answer-effects answer)))
         (record (fn-bpn-nth 3 effect))
         (scan (fn-bpnp-forward-scan
                (reverse (fn-bpnf-held-list st)) peer mru
                (fn-bpn-config-node-id
                 (fn-bpn-machine-state-config (fn-bpnf-base st)))
                observation (fn-bpnp-waits st)
                (fn-bpnd-free (fn-bpnp-used st) (fn-bpnp-debt st)
                              *fn-bpnp-control-margin*)
                (fn-bpnf-epoch st) budget)))
    (implies (equal (car effect) :persist-attempt)
             (and (equal (car scan) :ready)
                  (equal (fn-bpn-nth 3 record) (fn-bpn-nth 3 (fn-bpn-nth 1 scan)))
                  (equal (fn-bpn-nth 4 record)
                         (fn-bpah-held-primary-identity (fn-bpn-nth 1 scan)))
                  (equal (fn-bpn-nth 2 (fn-bpnp-pending-image
                                        (fn-bpnf-answer-state answer)))
                         (fn-bpn-nth 2 scan)))))
  :hints (("Goal"
           :use ((:instance fn-bpnp-start-one-offer-is-the-scan-choice
                            (budget *fn-bpnp-max-forward-retries*)
                            (st (fn-bpnp-with-runtime
                                 st (fn-bpnp-open-session
                                     (fn-bpnp-sessions st) peer session mru)
                                 (fn-bpnp-pending-image st)))))
           :in-theory (union-theories
                       '(fn-bpnp-step fn-bpnp-with-runtime-keeps-selection-inputs
                         fn-bpnp-event-budgets fn-bpnp-budgetsp len true-listp
                         (:e fn-bpnp-default-budgets) (:e fn-bpnp-budget-retries)
                         (:e nfix) (:e binary-+) (:e len) (:e true-listp)
                         fn-bpnp-domain-recover-eventp fn-bpnp-conflict-held
                         fn-cbor-ag-car fn-bpn-nth fn-bpnf-answer-effects
                         fn-bpnf-answer fn-bpnf-answer-state natp
                         (:executable-counterpart natp)
                         (:executable-counterpart not)
                         car-cons cdr-cons (:executable-counterpart equal)
                         (:executable-counterpart zp)
                         (:executable-counterpart fn-bpn-nth))
                       (theory 'minimal-theory)))))

(local
 (defthm fn-bpnp-primary-of-make-bundle
   (equal (fn-bpb-bundle-primary (fn-bpb-make-bundle primary blocks payload))
          primary)
   :hints (("Goal" :in-theory (enable fn-bpb-bundle-primary fn-bpb-make-bundle)))))

;; (b) The offered image is the held bundle re-encoded with its primary block
;; unchanged: same source, creation timestamp and sequence.  A retry offers
;; the original bundle identity; no sequence is reserved on this path.
(defthm fn-bpnp-forward-image-keeps-the-held-primary
  (implies (equal (car (fn-bpnp-forward-image h node observation)) :ready)
           (and (equal (fn-bpn-nth 1 (fn-bpnp-forward-image h node observation))
                       (fn-bpb-encode
                        (fn-bpn-nth 2 (fn-bpnp-forward-image h node observation))))
                (equal (fn-bpb-bundle-primary
                        (fn-bpn-nth 2 (fn-bpnp-forward-image h node observation)))
                       (fn-bpb-bundle-primary (fn-bpnf-held-bundle h)))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnp-forward-image
                                fn-bpnp-primary-of-make-bundle
                                fn-bpn-nth natp fn-cbor-ag-car
                                car-cons cdr-cons
                                (:executable-counterpart equal)
                                (:executable-counterpart natp)
                                (:executable-counterpart not)
                                (:executable-counterpart zp))
                              (theory 'minimal-theory)))))

;; (c) The retry budget.  The budget is the live proposal's check: the
;; scan offers only a forward candidate, whose slot is empty or under the
;; configured budget.  A kind 8 applied to a row it matches counts exactly
;; one more than the slot it replaces (0 on a row with no attempt).
(defun fn-bpnp-retries-boundedp (held budget)
  (declare (xargs :guard t :measure (acl2-count held)))
  (if (atom held) t
    (and (<= (fn-bpnp-attempt-retries (fn-bpn-nth 13 (car held)))
             (nfix budget))
         (fn-bpnp-retries-boundedp (cdr held) budget))))

(defthm fn-bpnp-forward-scan-offers-a-candidate
  (let ((scan (fn-bpnp-forward-scan
               ordered peer mru node observation waits free epoch budget)))
    (implies (equal (car scan) :ready)
             (fn-bpnp-forward-candidatep (fn-bpn-nth 1 scan) peer observation
                                         epoch budget)))
  :hints (("Goal" :induct (fn-bpnp-forward-scan
                           ordered peer mru node observation waits free epoch
                           budget)
           :in-theory (union-theories
                       '(fn-bpnp-forward-scan fn-bpn-nth car-cons cdr-cons
                         fn-cbor-ag-car (:e equal) (:e zp) (:e natp) natp
                         (:e fn-bpn-nth))
                       (theory 'minimal-theory)))))

(defthm fn-bpnp-attempted-held-counts-one-more
  (equal (fn-bpnp-attempt-retries
          (fn-bpn-nth 13 (fn-bpnp-attempted-held h record)))
         (if (fn-bpn-nth 13 h)
             (1+ (fn-bpnp-attempt-retries (fn-bpn-nth 13 h)))
           0))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnp-attempted-held
                                fn-bpnp-attempt-retries
                                fn-bpn-nth-is-nth-on-true-lists
                                nth-update-nth true-listp-update-nth
                                nfix natp
                                car-cons cdr-cons nth-0-cons nth-add1
                                (:executable-counterpart equal)
                                (:executable-counterpart natp)
                                (:executable-counterpart nfix)
                                (:executable-counterpart zp)
                                (:executable-counterpart not)
                                (:executable-counterpart binary-+)
                                (:executable-counterpart <)
                                (:executable-counterpart nth))
                              (theory 'minimal-theory)))))

; A row the kind 8 names that was under the budget stays within it.
(defun fn-bpnp-under-budgetp (h budget)
  (declare (xargs :guard t))
  (or (null (fn-bpn-nth 13 h))
      (< (fn-bpnp-attempt-retries (fn-bpn-nth 13 h)) (nfix budget))))

(defthm fn-bpnp-attempted-held-retries-within-bound
  (implies (fn-bpnp-under-budgetp h budget)
           (<= (fn-bpnp-attempt-retries
                (fn-bpn-nth 13 (fn-bpnp-attempted-held h record)))
               (nfix budget)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnp-attempted-held-counts-one-more
                                fn-bpnp-under-budgetp nfix natp
                                (:e nfix) (:e natp) (:e <) (:e binary-+))
                              (theory 'ground-zero)))))

(local
 (defthm fn-bpnp-attempt-replace-within-bound
   (implies (and (fn-bpnp-retries-boundedp held budget)
                 (fn-bpnp-under-budgetp
                  (fn-bpnf-find-arrival arrival held) budget))
            (fn-bpnp-retries-boundedp
             (fn-bpnp-attempt-replace arrival record held) budget))
   :hints (("Goal" :induct (fn-bpnp-attempt-replace arrival record held)
            :in-theory (union-theories
                        '(fn-bpnp-attempt-replace fn-bpnp-retries-boundedp
                          fn-bpnf-find-arrival
                          fn-bpnp-attempted-held-retries-within-bound
                          car-cons cdr-cons
                          (:executable-counterpart fn-bpnp-retries-boundedp)
                          (:executable-counterpart equal)
                          (:executable-counterpart not)
                          (:induction fn-bpnp-attempt-replace))
                        (theory 'minimal-theory))))))

(defthm fn-bpnp-attempt-apply-bounds-retries
  (let ((applied (fn-bpnp-attempt-apply record held)))
    (implies (and (equal (car applied) :ready)
                  (fn-bpnp-retries-boundedp held budget)
                  (fn-bpnp-under-budgetp
                   (fn-bpnf-find-arrival (fn-bpn-nth 3 record) held) budget))
             (and (fn-bpnp-retries-boundedp (fn-bpn-nth 1 applied) budget)
                  (<= (fn-bpnp-attempt-retries (fn-bpn-nth 13 (fn-bpn-nth 2 applied)))
                      (nfix budget)))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnp-attempt-apply
                                fn-bpnp-attempt-replace-within-bound
                                fn-bpnp-attempted-held-retries-within-bound
                                fn-bpn-nth natp fn-cbor-ag-car car-cons cdr-cons
                                (:executable-counterpart equal)
                                (:executable-counterpart natp)
                                (:executable-counterpart not)
                                (:executable-counterpart zp))
                              (theory 'minimal-theory)))))

;; Slot writers leave other slots (the idiom of bp-node-progress-premises).
(local
 (defthm fn-bpnfr-nth-of-nil
   (equal (fn-bpn-nth n nil) nil)
   :hints (("Goal" :in-theory (enable fn-bpn-nth fn-cbor-ag-car)))))

(local
 (defun fn-bpnfr-nth-update-induct (i j l)
   (if (or (zp i) (zp j)) (list i j l)
     (fn-bpnfr-nth-update-induct (1- i) (1- j) (cdr l)))))

(local
 (defthm fn-bpnfr-nth-of-update-nth
   (implies (and (natp i) (natp j) (not (equal i j)))
            (equal (fn-bpn-nth i (update-nth j v l))
                   (fn-bpn-nth i l)))
   :hints (("Goal" :induct (fn-bpnfr-nth-update-induct i j l)
            :in-theory (union-theories
                        '(fn-bpn-nth fn-cbor-ag-car update-nth car-cons cdr-cons
                          zp natp fn-bpnfr-nth-of-nil
                          (:induction fn-bpnfr-nth-update-induct)
                          (:e zp) (:e natp) (:e car) (:e cdr) (:e <)
                          (:e binary-+) (:e unary--) fix)
                        (theory 'minimal-theory))))))

(local
 (defthm fn-bpnp-held-list-of-writers
   (and (equal (fn-bpnf-held-list (fn-bpnp-with-runtime st s p))
               (fn-bpnf-held-list st))
        (equal (fn-bpnf-held-list (fn-bpnp-with-credit st u d))
               (fn-bpnf-held-list st))
        (equal (fn-bpnf-held-list (fn-bpnp-with-waits st w))
               (fn-bpnf-held-list st))
        (equal (fn-bpnf-held-list (fn-bpnp-with-issued st i))
               (fn-bpnf-held-list st))
        (equal (fn-bpnf-held-list
                (fn-bpnf-state-with-arrival b h o ho c i w e n a))
               h))
   :hints (("Goal" :in-theory (union-theories
                    '(fn-bpnf-held-list fn-bpnp-with-runtime fn-bpnp-with-credit
                      fn-bpnp-with-waits fn-bpnp-with-issued fn-bpnf-with-issued
                      fn-bpnf-state-with-arrival fn-bpnfr-nth-of-update-nth
                      fn-bpn-nth natp
                      fn-cbor-ag-car car-cons cdr-cons
                      (:executable-counterpart equal)
                      (:executable-counterpart natp)
                      (:executable-counterpart not)
                      (:executable-counterpart zp)
                      (:executable-counterpart binary-+)
                      (:executable-counterpart unary--))
                    (theory 'minimal-theory))))))

;; (c) over the step the host calls: the :persist-result arm for an issued
;; kind 8, the only served arm that writes an attempt slot, keeps every held
;; row's retry count within the bound.
(defthm fn-bpnp-step-attempt-persist-preserves-the-retry-bound
  (implies (and (fn-bpnp-retries-boundedp (fn-bpnf-held-list st) budget)
                (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :attempt)
                (fn-bpnp-under-budgetp
                 (fn-bpnf-find-arrival
                  (fn-bpn-nth 3 (fn-bpn-nth 4 (fn-bpnf-issued st)))
                  (fn-bpnf-held-list st))
                 budget))
           (fn-bpnp-retries-boundedp
            (fn-bpnf-held-list
             (fn-bpnf-answer-state
              (fn-bpnp-step st (list :persist-result epoch op result))))
            budget))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnp-domain-recover-eventp fn-bpnp-conflict-held
                         fn-bpnp-step fn-bpnp-attempt-persist-step
                                fn-bpnp-held-list-of-writers
                                fn-bpnp-attempt-apply-bounds-retries
                                fn-bpnf-answer fn-bpnf-answer-state
                                fn-bpn-nth natp fn-cbor-ag-car car-cons cdr-cons
                                (:executable-counterpart equal)
                                (:executable-counterpart natp)
                                (:executable-counterpart not)
                                (:executable-counterpart zp))
                              (theory 'minimal-theory)))))
;; ---------------------------------------------------------------------
;; The sender's reading of a TCPCL refusal (RFC 9174 5.2.4; spec
;; bp-node-machine 4.3.1).  host/native/bp-node.lisp fnn-bpnode-forward-contact
;; calls fn-bpnp-tcpcl-outcome with the connection's outcome and the Reason
;; Code of the peer's XFER_REFUSE, and hands the result to fn-bpnp-step as the
;; :forward-result event's outcome.

;; A peer refusal is its own result, never :failed, and keeps its reason.
(defthm fn-bpnp-tcpcl-outcome-keeps-the-refusal-reason
  (implies (fn-frame-natp reason)
           (and (equal (fn-bpnp-tcpcl-outcome :refused reason)
                       (list :refused reason))
                (fn-bpnp-forward-outcomep
                 (fn-bpnp-tcpcl-outcome :refused reason))))
  :hints (("Goal" :in-theory (enable fn-bpnp-tcpcl-outcome
                                     fn-bpnp-forward-outcomep))))

;; KEYSTONE.  The proposal fn-bpnp-step makes for a :forward-result event
;; records the event's outcome in the kind-9 record, unchanged: every
;; refusal reason reaches the durable result distinctly.
(defthm fn-bpnp-step-forward-result-records-the-transport-outcome
  (let ((effect (car (fn-bpnf-answer-effects (fn-bpnp-step st event)))))
    (implies (and (equal (fn-cbor-ag-car event) :forward-result)
                  (equal (car effect) :persist-forward-result))
             (equal (fn-bpn-nth 8 (fn-bpn-nth 3 effect))
                    (fn-bpn-nth 4 event))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnp-step fn-bpnp-forward-result-propose-step
                         fn-bpnp-forward-result-record
                         fn-bpnp-domain-recover-eventp fn-bpnp-conflict-held
                         fn-bpnf-answer fn-bpnf-answer-effects
                         fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons natp (:e natp) (:e car)
                         (:e zp) (:e binary-+) (:e equal))
                       (theory 'minimal-theory)))))

;; KEYSTONE.  Completed (reason 1): the peer already holds the complete
;; bundle.  Applying its kind 9 (fn-bpnp-forward-result-apply, which the
;; :persist-result arm and ordered replay both call) gives exactly the
;; answer, rows and row that :sent gives: the row is forwarded and its
;; attempt cleared.  The receiver still acknowledges a duplicate
;; (fn-bpnf-receive-decision); this is only the sender's meaning of reason 1.
(encapsulate ()
(local
 (defthm fn-bpnfr-held-completed-is-held-sent
   (equal (fn-bpnp-forward-result-held h '(:refused 1))
          (fn-bpnp-forward-result-held h :sent))
   :hints (("Goal" :in-theory (enable fn-bpnp-forward-result-held
                                      fn-bpnp-forward-terminalp)))))
(local
 (defthm fn-bpnfr-replace-completed-is-replace-sent
   (equal (fn-bpnp-forward-result-replace arrival '(:refused 1) held)
          (fn-bpnp-forward-result-replace arrival :sent held))
   :hints (("Goal" :induct (fn-bpnp-forward-result-replace arrival :sent held)
            :in-theory (union-theories
                        '(fn-bpnp-forward-result-replace
                          fn-bpnfr-held-completed-is-held-sent)
                        (theory 'minimal-theory))))))
(defthm fn-bpnp-completed-refusal-settles-as-sent
  (equal (fn-bpnp-forward-result-apply
          (fn-bpnp-forward-result-record
           epoch op arrival identity attempt-epoch attempt-op session
           (fn-bpnp-tcpcl-outcome :refused 1))
          held)
         (fn-bpnp-forward-result-apply
          (fn-bpnp-forward-result-record
           epoch op arrival identity attempt-epoch attempt-op session :sent)
          held))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnp-forward-result-apply
                         fn-bpnp-forward-result-matches-heldp
                         fn-bpnp-forward-result-recordp
                         fn-bpnp-forward-result-record
                         fn-bpnfr-held-completed-is-held-sent
                         fn-bpnfr-replace-completed-is-replace-sent
                         fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons
                         natp (:e natp)
                         (:e fn-bpnp-tcpcl-outcome) (:e fn-bpnp-forward-outcomep)
                         (:e zp) (:e binary-+) (:e equal) (:e len) (:e true-listp)
                         len true-listp)
                       (theory 'minimal-theory))))))

;; Every other reason stays a non-terminal result: the row stays forward
;; pending for a later session.
(defthm fn-bpnp-other-refusal-is-not-settled
  (implies (and (fn-frame-natp reason) (not (equal reason 1)))
           (not (fn-bpnp-forward-terminalp
                 (fn-bpnp-tcpcl-outcome :refused reason))))
  :hints (("Goal" :in-theory (enable fn-bpnp-tcpcl-outcome
                                     fn-bpnp-forward-terminalp))))
