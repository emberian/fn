(in-package "ACL2")
(include-book "../../books/bp-node-fragment-step")
(include-book "../../books/bp-app-handoff-time")
(include-book "../../books/bp-node-receive-boundary")
(include-book "bp-node-fragment-plan-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpnfs-live-observation* (fn-clock-observation 1 2343 0 t))
(assert-event (equal (fn-bpah-held-expiry *bpnff-p3* *bpnfs-live-observation*) :live))
(assert-event (equal (fn-bpah-held-expiry *bpnff-p0* *bpnfs-live-observation*) :live))
(assert-event (equal (car (fn-bpnf-family-plan-at
                           *bpnff-state* *bpnff-p3*
                           *bpnfs-live-observation*)) :ready))
(defun bpnfs-proposal ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-fragment-step
   *bpnff-state* (list :family 0 *bpnfs-live-observation*)))
(defun bpnfs-pending ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-answer-state (bpnfs-proposal)))
(assert-event
 (equal (car (car (fn-bpnf-answer-effects (bpnfs-proposal))))
        :persist-family))
(assert-event
 (equal (fn-bpnf-held-list (bpnfs-pending))
        (fn-bpnf-held-list *bpnff-state*)))
(assert-event
 (equal (fn-bpnf-next-arrival (bpnfs-pending))
        (1+ (fn-bpnf-next-arrival *bpnff-state*))))
(defun bpnfs-durable ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-fragment-step (bpnfs-pending)
                         '(:persist-result 3 0 :durable)))
(assert-event
 (and (equal (car (car (fn-bpnf-answer-effects (bpnfs-durable))))
             :family-ready)
      (equal (len (fn-bpnf-held-list
                   (fn-bpnf-answer-state (bpnfs-durable)))) 5)
      (not (member-equal *bpnff-p3*
                         (fn-bpnf-held-list
                          (fn-bpnf-answer-state (bpnfs-durable)))))
      (not (member-equal *bpnff-p0*
                         (fn-bpnf-held-list
                          (fn-bpnf-answer-state (bpnfs-durable)))))))
(defun bpnfs-uncertain ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-answer-state
   (fn-bpnf-fragment-step (bpnfs-pending)
                          '(:persist-result 3 0 :uncertain))))
(assert-event
 (equal (fn-bpnf-fragment-step
         (bpnfs-uncertain) '(:persist-result 3 0 :durable))
        (fn-bpnf-answer (bpnfs-uncertain) nil)))
(assert-event
 (equal (fn-bpnf-fragment-step
         (bpnfs-uncertain) (list :family 2 *bpnfs-live-observation*))
        (fn-bpnf-answer (bpnfs-uncertain) nil)))
(must-fail
 (assert-event
  (equal (fn-bpnf-held-list
          (fn-bpnf-answer-state (bpnfs-durable)))
         (fn-bpnf-held-list *bpnff-state*))))

; Both wire fragments now pass the carrier boundary, while the application
; ADU boundary still refuses fragment delivery.  At the later observation
; the first fragment is expired, so the family selector must not consume it.
(defconst *bpnfs-age-zero* (fn-bpb-bundle-age-block 2 0 0 0))
(defconst *bpnfs-aged-b3*
  (fn-bpb-make-bundle (fn-bpb-bundle-primary *bpnff-b3*)
                      (list *bpnfs-age-zero*)
                      (fn-bpb-bundle-payload *bpnff-b3*)))
(defconst *bpnfs-fresh-b0*
  (fn-bpb-make-bundle (fn-bpb-bundle-primary *bpnff-b0*)
                      (list *bpnfs-age-zero*)
                      (fn-bpb-bundle-payload *bpnff-b0*)))
(defconst *bpnfs-age-arrival* (fn-clock-observation 0 0 0 nil))
(defconst *bpnfs-age-later* (fn-clock-observation 60000001 0 0 nil))
(defconst *bpnfs-aged-p3*
  (update-nth 9
              (fn-bpnf-received-anchor *bpnfs-aged-b3*
                                       *bpnfs-age-arrival*)
              (fn-bpnfft-held '(112) 0 *bpnfs-aged-b3*
                               '(:dispatch-pending) nil)))
(defconst *bpnfs-fresh-p0*
  (update-nth 9
              (fn-bpnf-received-anchor *bpnfs-fresh-b0*
                                       *bpnfs-age-later*)
              (fn-bpnfft-held '(112) 1 *bpnfs-fresh-b0*
                               '(:dispatch-pending) nil)))
(defconst *bpnfs-expiry-state*
  (fn-bpnf-state (fn-bpnf-base *bpnff-state*)
                 (list *bpnfs-fresh-p0* *bpnfs-aged-p3*)
                 nil nil nil nil nil 3 0))
(assert-event (fn-bpnf-heldp *bpnfs-aged-p3*))
(assert-event (fn-bpnf-heldp *bpnfs-fresh-p0*))
(assert-event
 (fn-bpnf-receive-wire-readyp
  (fn-bpnf-receive-wire-event
         *bpnff-config* (fn-bpb-encode *bpnfs-aged-b3*)
         *bpnfs-age-arrival* (fn-bpn-nth 4 *bpnfs-aged-p3*))))
(assert-event
 (fn-bpnf-receive-wire-readyp
  (fn-bpnf-receive-wire-event
         *bpnff-config* (fn-bpb-encode *bpnfs-fresh-b0*)
         *bpnfs-age-later* (fn-bpn-nth 4 *bpnfs-fresh-p0*))))
(assert-event
 (equal (fn-bpn-outcome-reason
         (fn-bpn-receive *bpnff-config*
                         (fn-bpb-encode *bpnfs-aged-b3*)
                         *bpnfs-age-arrival*))
        :fragment-not-reassembled))
(must-fail
 (assert-event
  (equal (car (fn-bpnf-family-next
              *bpnfs-expiry-state* *bpnfs-age-later*)) :ready)))

; A blocked old family must not starve a later independent principal family.
(defconst *bpnfs-other-p3*
  (update-nth 9
              (fn-bpnf-received-anchor *bpnfs-aged-b3* *bpnfs-age-later*)
              (fn-bpnfft-held '(113) 2 *bpnfs-aged-b3*
                               '(:dispatch-pending) nil)))
(defconst *bpnfs-other-p0*
  (update-nth 9
              (fn-bpnf-received-anchor *bpnfs-fresh-b0* *bpnfs-age-later*)
              (fn-bpnfft-held '(113) 3 *bpnfs-fresh-b0*
                               '(:dispatch-pending) nil)))
(defconst *bpnfs-other-family-state*
  (fn-bpnf-state (fn-bpnf-base *bpnff-state*)
                 (list *bpnfs-fresh-p0* *bpnfs-aged-p3*
                       *bpnfs-other-p3* *bpnfs-other-p0*)
                 nil nil nil nil nil 3 0))
(assert-event
 (and (fn-bpnf-heldp *bpnfs-other-p3*)
      (fn-bpnf-heldp *bpnfs-other-p0*)
      (equal (fn-bpnf-family-next
              *bpnfs-other-family-state* *bpnfs-age-later*)
             '(:ready 2))))
(assert-event (equal (fn-bpah-held-expiry *bpnfs-aged-p3* *bpnfs-age-later*)
                     :expired))
(assert-event (equal (fn-bpah-held-expiry *bpnfs-fresh-p0* *bpnfs-age-later*)
                     :live))
(assert-event (equal (car (fn-bpnf-family-next
                           *bpnfs-expiry-state* *bpnfs-age-later*)) nil))
(assert-event (equal (car (car (fn-bpnf-answer-effects
                         (fn-bpnf-fragment-step
                          *bpnfs-expiry-state*
                          (list :family 0 *bpnfs-age-later*)))))
                     nil))

;; fn-bpnf-family-without-offset-zero-is-not-ready (PRF-134): the selector
;; skips a family whose offset-zero row is not held.  Witness: p3 held
;; without p0 has no offset-zero source and is not ready; hypothesis removal:
;; with p0 held the same anchor's plan is ready.
(defconst *bpnfs-no-zero-state*
  (fn-bpnf-state (fn-bpnf-base *bpnff-state*) (list *bpnff-p3*)
                 nil nil nil nil nil 3 0))
(assert-event
 (and (not (fn-bpnf-offset-zero-source
            (fn-bpnf-active-set *bpnfs-no-zero-state* *bpnff-p3*)))
      (not (equal (fn-cbor-ag-car (fn-bpnf-family-plan-at
                                   *bpnfs-no-zero-state* *bpnff-p3*
                                   *bpnfs-live-observation*))
                  :ready))
      (null (fn-bpnf-family-next *bpnfs-no-zero-state*
                                 *bpnfs-live-observation*))))
(assert-event
 (and (fn-bpnf-offset-zero-source
       (fn-bpnf-active-set *bpnff-state* *bpnff-p3*))
      (equal (fn-cbor-ag-car (fn-bpnf-family-plan-at
                              *bpnff-state* *bpnff-p3*
                              *bpnfs-live-observation*))
             :ready)))

;; PRF-136 (bp-lifecycle-5): the served selector reads the rows' primary
;; blocks and plans a row only when its family holds an offset-zero fragment.
(defconst *bpnfs-held* (fn-bpnf-held-list *bpnff-state*))
(defconst *bpnfs-zero* (fn-bpnf-zero-family-keys *bpnfs-held*))
(defconst *bpnfs-p3-key* (fn-bpnf-fragment-family-key *bpnff-p3*))

;; fn-bpnf-family-select-is-aux, reachable witness: the host's own call
;; (held = the held list, nothing tried, zero = its offset-zero keys); every
;; hypothesis holds and both selectors answer p3's arrival.
(assert-event
 (and (subsetp-equal *bpnfs-held* (fn-bpnf-held-list *bpnff-state*))
      (fn-bpnf-family-keys-not-readyp *bpnff-state* *bpnfs-held* nil
                                      *bpnfs-live-observation*)
      (equal *bpnfs-zero* (list *bpnfs-p3-key*))
      (equal (fn-bpnf-family-select *bpnff-state* *bpnfs-held*
                                    *bpnfs-live-observation* nil *bpnfs-zero*)
             '(:ready 0))
      (equal (fn-bpnf-family-next-aux *bpnff-state* *bpnfs-held*
                                      *bpnfs-live-observation*)
             '(:ready 0))
      (equal (fn-bpnf-family-next *bpnff-state* *bpnfs-live-observation*)
             '(:ready 0))))

;; Without the zero-key hypothesis (ZERO nil): the other two hold, and the
;; select skips the ready family the reference selector answers.
(assert-event
 (and (subsetp-equal *bpnfs-held* (fn-bpnf-held-list *bpnff-state*))
      (fn-bpnf-family-keys-not-readyp *bpnff-state* *bpnfs-held* nil
                                      *bpnfs-live-observation*)
      (not (equal nil (fn-bpnf-zero-family-keys *bpnfs-held*)))
      (not (equal (fn-bpnf-family-select *bpnff-state* *bpnfs-held*
                                         *bpnfs-live-observation* nil nil)
                  (fn-bpnf-family-next-aux *bpnff-state* *bpnfs-held*
                                           *bpnfs-live-observation*)))))

;; Without the tried invariant (p3's ready family marked tried): the other
;; two hold, and the answers differ.
(assert-event
 (and (subsetp-equal *bpnfs-held* (fn-bpnf-held-list *bpnff-state*))
      (not (fn-bpnf-family-keys-not-readyp *bpnff-state* *bpnfs-held*
                                           (list *bpnfs-p3-key*)
                                           *bpnfs-live-observation*))
      (equal *bpnfs-zero* (fn-bpnf-zero-family-keys *bpnfs-held*))
      (not (equal (fn-bpnf-family-select *bpnff-state* *bpnfs-held*
                                         *bpnfs-live-observation*
                                         (list *bpnfs-p3-key*) *bpnfs-zero*)
                  (fn-bpnf-family-next-aux *bpnff-state* *bpnfs-held*
                                           *bpnfs-live-observation*)))))

;; Without the subset hypothesis: a row that is not held (p3 with another
;; token, the same family and arrival) is planned against the held list, is
;; not ready, and marks its family tried before the held p3 is reached.
(defconst *bpnfs-p3-copy* (update-nth 15 99 *bpnff-p3*))
(assert-event
 (and (fn-bpnf-heldp *bpnfs-p3-copy*)
      (not (subsetp-equal (cons *bpnfs-p3-copy* *bpnfs-held*)
                          (fn-bpnf-held-list *bpnff-state*)))
      (fn-bpnf-family-keys-not-readyp *bpnff-state* *bpnfs-held* nil
                                      *bpnfs-live-observation*)
      (equal *bpnfs-zero* (fn-bpnf-zero-family-keys *bpnfs-held*))
      (not (equal (fn-bpnf-family-select *bpnff-state*
                                         (cons *bpnfs-p3-copy* *bpnfs-held*)
                                         *bpnfs-live-observation* nil
                                         *bpnfs-zero*)
                  (fn-bpnf-family-next-aux *bpnff-state*
                                           (cons *bpnfs-p3-copy* *bpnfs-held*)
                                           *bpnfs-live-observation*)))))

;; fn-bpnf-family-select-plans-bound (no hypotheses): the host's call on the
;; state above plans one row, of the two whose family holds offset zero; the
;; SCN-077 shape (the family's offset zero not yet held) plans none.
(assert-event
 (and (equal (fn-bpnf-family-select-plans *bpnff-state* *bpnfs-held*
                                          *bpnfs-live-observation* nil
                                          *bpnfs-zero*)
             1)
      (equal (fn-bpnf-rows-in-zero-families *bpnfs-held* *bpnfs-zero*) 2)
      (equal (fn-bpnf-zero-family-keys
              (fn-bpnf-held-list *bpnfs-no-zero-state*))
             nil)
      (equal (fn-bpnf-family-select-plans
              *bpnfs-no-zero-state* (fn-bpnf-held-list *bpnfs-no-zero-state*)
              *bpnfs-live-observation* nil nil)
             0)))

;; fn-bpnf-family-select-steps-bound, witness: no row planned, one row, one
;; step.
(assert-event
 (and (equal (fn-bpnf-family-select-plans
              *bpnfs-no-zero-state* (fn-bpnf-held-list *bpnfs-no-zero-state*)
              *bpnfs-live-observation* nil nil)
             0)
      (equal (fn-bpnf-family-select-steps
              *bpnfs-no-zero-state* (fn-bpnf-held-list *bpnfs-no-zero-state*)
              *bpnfs-live-observation* nil nil)
             1)
      (<= 1 (* (len (fn-bpnf-held-list *bpnfs-no-zero-state*)) (+ 1 0 0)))))

;; Without the no-plan hypothesis: p0's family alone is planned (not ready)
;; and tried, so the next row's comparisons exceed the bound.
(defconst *bpnfs-steps-other*
  (update-nth 15 5 (update-nth 3 5 *bpnfs-other-p3*)))
(defconst *bpnfs-steps-state*
  (fn-bpnf-state (fn-bpnf-base *bpnff-state*)
                 (list *bpnff-p0* *bpnfs-steps-other*)
                 nil nil nil nil nil 3 0))
(defconst *bpnfs-steps-zero*
  (fn-bpnf-zero-family-keys (fn-bpnf-held-list *bpnfs-steps-state*)))
(assert-event
 (and (fn-bpnf-heldp *bpnfs-steps-other*)
      (fn-bpnf-fragment-candidatep *bpnfs-steps-other*)
      (not (equal (fn-bpnf-family-select-plans
                   *bpnfs-steps-state* (fn-bpnf-held-list *bpnfs-steps-state*)
                   *bpnfs-live-observation* nil *bpnfs-steps-zero*)
                  0))
      (> (fn-bpnf-family-select-steps
          *bpnfs-steps-state* (fn-bpnf-held-list *bpnfs-steps-state*)
          *bpnfs-live-observation* nil *bpnfs-steps-zero*)
         (* (len (fn-bpnf-held-list *bpnfs-steps-state*))
            (+ 1 (len *bpnfs-steps-zero*) 0)))))
