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
(defun fn-bpnp-only-forward-candidatep (ordered h peer observation epoch)
  (declare (xargs :guard t :measure (acl2-count ordered)))
  (if (atom ordered) t
    (and (or (equal (car ordered) h)
             (not (fn-bpnp-forward-candidatep
                   (car ordered) peer observation epoch)))
         (fn-bpnp-only-forward-candidatep
          (cdr ordered) h peer observation epoch))))

;; (a) Selection keystone.  A row left with an uncertain attempt under the
;; bound is a forward candidate; when no other row competes for this
;; session's peer and it fits and is not waiting, the scan the step calls
;; returns it with its forwarding image and the waits unchanged.
;; Competition among candidates is the arrival-order fairness of N03/N04
;; and is not claimed here.
(defthm fn-bpnp-forward-scan-offers-the-only-candidate
  (implies (and (member-equal h ordered)
                (fn-bpnp-only-forward-candidatep
                 ordered h peer observation epoch)
                (fn-bpnp-forward-candidatep h peer observation epoch)
                (not (fn-bpnp-forward-mru-waitp h peer mru waits))
                (not (fn-bpnp-credit-blockedp h waits free))
                (equal (car (fn-bpnp-forward-image h node observation)) :ready)
                (<= (len (fn-bpn-nth 1 (fn-bpnp-forward-image
                                        h node observation)))
                    mru))
           (equal (fn-bpnp-forward-scan
                   ordered peer mru node observation waits free epoch)
                  (list :ready h
                        (fn-bpn-nth 1 (fn-bpnp-forward-image h node observation))
                        (fn-bpb-bundle-age
                         (fn-bpn-nth 2 (fn-bpnp-forward-image h node observation)))
                        waits)))
  :hints (("Goal" :induct (fn-bpnp-forward-scan
                           ordered peer mru node observation waits free epoch)
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
                (< (fn-bpnp-attempt-retries (fn-bpn-nth 13 h))
                   *fn-bpnp-max-forward-retries*))
           (fn-bpnp-forward-candidatep h peer observation epoch))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnp-forward-candidatep
                                fn-bpnp-retry-eligible-slotp)
                              (theory 'minimal-theory)))))

;; A stranded report is only a report: never an attempt proposal.
(defthm fn-bpnp-stranded-effects-propose-nothing
  (not (equal (car (car (fn-bpnp-stranded-effects held peer epoch)))
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
  (let* ((answer (fn-bpnp-start-one st peer session mru observation))
         (effect (car (fn-bpnf-answer-effects answer)))
         (record (fn-bpn-nth 3 effect))
         (scan (fn-bpnp-forward-scan
                (reverse (fn-bpnf-held-list st)) peer mru
                (fn-bpn-config-node-id
                 (fn-bpn-machine-state-config (fn-bpnf-base st)))
                observation (fn-bpnp-waits st)
                (fn-bpnd-free (fn-bpnp-used st) (fn-bpnp-debt st)
                              *fn-bpnp-control-margin*)
                (fn-bpnf-epoch st))))
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
         (effect (car (fn-bpnf-answer-effects answer)))
         (record (fn-bpn-nth 3 effect))
         (scan (fn-bpnp-forward-scan
                (reverse (fn-bpnf-held-list st)) peer mru
                (fn-bpn-config-node-id
                 (fn-bpn-machine-state-config (fn-bpnf-base st)))
                observation (fn-bpnp-waits st)
                (fn-bpnd-free (fn-bpnp-used st) (fn-bpnp-debt st)
                              *fn-bpnp-control-margin*)
                (fn-bpnf-epoch st))))
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
                            (st (fn-bpnp-with-runtime
                                 st (fn-bpnp-open-session
                                     (fn-bpnp-sessions st) peer session mru)
                                 (fn-bpnp-pending-image st)))))
           :in-theory (union-theories
                       '(fn-bpnp-step fn-bpnp-with-runtime-keeps-selection-inputs
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

;; (c) The retry bound.
(defun fn-bpnp-retries-boundedp (held)
  (declare (xargs :guard t :measure (acl2-count held)))
  (if (atom held) t
    (and (<= (fn-bpnp-attempt-retries (fn-bpn-nth 13 (car held)))
             *fn-bpnp-max-forward-retries*)
         (fn-bpnp-retries-boundedp (cdr held)))))

;; A kind 8 applied to a row it matches leaves a retry count within the
;; bound: 0 on a row with no attempt, one more than an uncertain slot's count,
;; which the match requires to be below the bound.
(defthm fn-bpnp-attempted-held-retries-within-bound
  (implies (fn-bpnp-attempt-matches-heldp record h)
           (<= (fn-bpnp-attempt-retries
                (fn-bpn-nth 13 (fn-bpnp-attempted-held h record)))
               *fn-bpnp-max-forward-retries*))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnp-attempt-matches-heldp
                                fn-bpnp-attempted-held
                                fn-bpnp-retry-eligible-slotp
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

(local
 (defthm fn-bpnp-attempt-replace-within-bound
   (implies (and (fn-bpnp-retries-boundedp held)
                 (fn-bpnp-attempt-matches-heldp
                  record (fn-bpnf-find-arrival arrival held)))
            (fn-bpnp-retries-boundedp
             (fn-bpnp-attempt-replace arrival record held)))
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
                  (fn-bpnp-retries-boundedp held))
             (and (fn-bpnp-retries-boundedp (fn-bpn-nth 1 applied))
                  (<= (fn-bpnp-attempt-retries (fn-bpn-nth 13 (fn-bpn-nth 2 applied)))
                      *fn-bpnp-max-forward-retries*))))
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
  (implies (and (fn-bpnp-retries-boundedp (fn-bpnf-held-list st))
                (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :attempt))
           (fn-bpnp-retries-boundedp
            (fn-bpnf-held-list
             (fn-bpnf-answer-state
              (fn-bpnp-step st (list :persist-result epoch op result))))))
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
