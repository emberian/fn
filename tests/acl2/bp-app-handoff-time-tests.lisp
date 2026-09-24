(in-package "ACL2")
(include-book "../../books/bp-app-handoff-time")
(include-book "bp-app-handoff-tests")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpaht-arrival* (fn-clock-observation 1000 0 0 nil))
(defconst *bpaht-live* (fn-clock-observation 1001 0 0 nil))
(defconst *bpaht-expired* (fn-clock-observation 3601002 0 0 nil))
(defconst *bpaht-anchored-held*
  (update-nth 9 (fn-bpnf-received-anchor *bpah-bundle* *bpaht-arrival*)
              *bpah-held*))
(defconst *bpaht-state*
  (fn-bpnf-state (fn-bpnf-base *bpah-state*)
                 (list *bpaht-anchored-held*)
                 (fn-bpnf-outcomes *bpah-state*)
                 (fn-bpnf-handoffs *bpah-state*)
                 (fn-bpnf-correlation *bpah-state*)
                 (fn-bpnf-issued *bpah-state*)
                 (fn-bpnf-waits *bpah-state*)
                 (fn-bpnf-epoch *bpah-state*)
                 (fn-bpnf-next-op *bpah-state*)))

(assert-event (equal (car (fn-bpah-pending-decision-at
                           *bpaht-state* *bpah-local* *bpaht-live*))
                     :ready))
(assert-event (null (fn-bpah-pending-decision-at
                     *bpaht-state* *bpah-local* *bpaht-expired*)))
(assert-event (equal (car (fn-bpah-pending-decision-at
                           *bpah-state* *bpah-local* *bpaht-live*))
                     :uncertain))
(must-fail
 (assert-event
  (equal (car (fn-bpah-pending-decision-at
               *bpah-state* *bpah-local* *bpaht-live*)) :ready)))
(must-fail
 (assert-event
  (equal (car (fn-bpah-pending-decision-at
               *bpaht-state* *bpah-local* *bpaht-expired*)) :ready)))

; A3 served selector: two kind-5 publications produce an older clock-uncertain
; request (no Bundle Age block, no usable wall) and a newer live request.
; The owner calls fn-bpah-pending-decision-at before its :deliver step.  Clock
; uncertainty on the first row does not authorize delivering or deleting it,
; and does not hide the second row.  Publication uncertainty is different:
; an issued uncertain operation still fences the foundation step below.
(defconst *bpaht-wall-less* (fn-clock-observation 1001 0 0 nil))
(defconst *bpaht-wall-arrival* (fn-clock-observation 1000 10000 0 t))
(defconst *bpaht-old-authored*
  (fn-bpn-send-bundle *bpah-config* *bpah-local*
                      *bpah-adu* 7 *bpaht-wall-arrival*))
(defconst *bpaht-old-bundle*
  (fn-bpb-make-bundle
   (fn-bpb-bundle-primary *bpaht-old-authored*)
   (list (car (fn-bpb-bundle-blocks *bpaht-old-authored*)))
   (fn-bpb-bundle-payload *bpaht-old-authored*)))
(defconst *bpaht-new-bundle*
  (fn-bpn-send-bundle *bpah-config* *bpah-local*
                      *bpah-adu* 8 *bpah-obs*))
(defconst *bpaht-cold*
  (fn-bpnf-state (fn-bpnf-base *bpah-state*) nil nil nil nil nil nil 1 0))
(defconst *bpaht-old-proposal*
  (fn-bpnf-step
   *bpaht-cold*
   (list :receive-bundle *bpaht-old-bundle*
         (fn-bpb-encode *bpaht-old-bundle*) *bpah-ingress*
         *bpaht-wall-arrival*)))
(defconst *bpaht-old-accepted*
  (fn-bpnf-step (fn-bpnf-answer-state *bpaht-old-proposal*)
                 '(:persist-result 1 0 :durable)))
(defconst *bpaht-new-proposal*
  (fn-bpnf-step
   (fn-bpnf-answer-state *bpaht-old-accepted*)
   (list :receive-bundle *bpaht-new-bundle*
         (fn-bpb-encode *bpaht-new-bundle*) *bpah-ingress* *bpaht-arrival*)))
(defconst *bpaht-new-accepted*
  (fn-bpnf-step (fn-bpnf-answer-state *bpaht-new-proposal*)
                 '(:persist-result 1 1 :durable)))
(defconst *bpaht-two-held* (fn-bpnf-answer-state *bpaht-new-accepted*))
(defconst *bpaht-old-held* (second (fn-bpnf-held-list *bpaht-two-held*)))
(defconst *bpaht-new-held* (first (fn-bpnf-held-list *bpaht-two-held*)))
(defconst *bpaht-two-decision*
  (fn-bpah-pending-decision-at
   *bpaht-two-held* *bpah-local* *bpaht-wall-less*))

(assert-event (fn-bpb-bundlep *bpaht-old-bundle*))
(assert-event (fn-bpb-bundlep *bpaht-new-bundle*))
(assert-event
 (fn-bpn-acceptedp
  (fn-bpn-receive *bpah-config*
                  (fn-bpb-encode *bpaht-old-bundle*)
                  *bpaht-wall-arrival*)))
(assert-event
 (fn-bpn-acceptedp
  (fn-bpn-receive *bpah-config*
                  (fn-bpb-encode *bpaht-new-bundle*)
                  *bpaht-arrival*)))
(assert-event (not (equal (fn-bpb-bundle-id *bpaht-old-bundle*)
                          (fn-bpb-bundle-id *bpaht-new-bundle*))))
(assert-event (equal (car (car (fn-bpnf-answer-effects *bpaht-old-proposal*)))
                     :persist))
(assert-event (equal (third (car (fn-bpnf-answer-effects *bpaht-old-accepted*)))
                     :stored))
(assert-event (equal (car (car (fn-bpnf-answer-effects *bpaht-new-proposal*)))
                     :persist))
(assert-event (equal (third (car (fn-bpnf-answer-effects *bpaht-new-accepted*)))
                     :stored))
(assert-event (equal (len (fn-bpnf-held-list *bpaht-two-held*)) 2))
(assert-event (fn-bpnf-heldp *bpaht-old-held*))
(assert-event (fn-bpnf-heldp *bpaht-new-held*))
(assert-event (fn-bpah-local-pendingp *bpaht-old-held* *bpah-local*))
(assert-event (fn-bpah-local-pendingp *bpaht-new-held* *bpah-local*))
(assert-event (< (fn-bpn-nth 3 *bpaht-old-held*)
                 (fn-bpn-nth 3 *bpaht-new-held*)))
(assert-event (equal (fn-bpah-held-expiry *bpaht-old-held*
                                           *bpaht-wall-less*) :uncertain))
(assert-event (equal (fn-bpah-held-expiry *bpaht-new-held*
                                           *bpaht-wall-less*) :live))
(assert-event
 (equal (fn-bpah-select-oldest-at
         (fn-bpnf-held-list *bpaht-two-held*)
         *bpah-local* *bpaht-wall-less* nil)
        *bpaht-new-held*))
(assert-event (equal (car *bpaht-two-decision*) :ready))
(assert-event
 (equal (second (second *bpaht-two-decision*))
        (fn-bpnf-held-key (fn-bpnf-held-principal *bpaht-new-held*)
                           (fn-bpnf-held-id *bpaht-new-held*))))
(assert-event
 (equal (fn-bpnf-held-list
         (fn-bpnf-answer-state
          (fn-bpnf-step *bpaht-two-held*
                         (list :deliver (second (second *bpaht-two-decision*))
                               *bpah-local*))))
        (fn-bpnf-held-list *bpaht-two-held*)))
(assert-event
 (equal (car (car (fn-bpnf-answer-effects
                   (fn-bpnf-step *bpaht-two-held*
                                  (list :deliver
                                        (second (second *bpaht-two-decision*))
                                        *bpah-local*)))))
        :deliver))
(defconst *bpaht-new-key* (second (second *bpaht-two-decision*)))
(defconst *bpaht-delivery-start*
  (fn-bpnf-step *bpaht-two-held*
                 (list :deliver *bpaht-new-key* *bpah-local*)))
(defconst *bpaht-delivery-result*
  (fn-bpnf-step
   (fn-bpnf-answer-state *bpaht-delivery-start*)
   (list :deliver-result 1 2 *bpaht-new-key*
         :request-accepted '(114 105 100))))
(defconst *bpaht-delivery-durable*
  (fn-bpnf-step
   (fn-bpnf-answer-state *bpaht-delivery-result*)
   '(:persist-result 1 3 :durable)))
(defconst *bpaht-delivered-state*
  (fn-bpnf-answer-state *bpaht-delivery-durable*))
(assert-event (equal (car (car (fn-bpnf-answer-effects
                                *bpaht-delivery-result*)))
                     :persist-delivery))
(assert-event
 (equal (car (car (fn-bpnf-answer-effects *bpaht-delivery-durable*)))
        :delivery-answer))
(assert-event
 (equal (second (car (fn-bpnf-answer-effects *bpaht-delivery-durable*)))
        :durable))
(assert-event
 (equal (fn-bpnf-find-held
         (fn-bpnf-held-key (fn-bpnf-held-principal *bpaht-old-held*)
                            (fn-bpnf-held-id *bpaht-old-held*))
         (fn-bpnf-held-list *bpaht-delivered-state*))
        *bpaht-old-held*))
(assert-event
 (equal (fn-bpn-nth 12
         (fn-bpnf-find-held *bpaht-new-key*
                            (fn-bpnf-held-list *bpaht-delivered-state*)))
        '(:dispatch-done)))
(assert-event (equal (len (fn-bpnf-handoffs *bpaht-delivered-state*)) 1))

; If every eligible local carrier has only clock uncertainty, the selector
; still reports uncertainty.  A publication uncertainty fences even if the
; read-only selector can describe a live carrier.
(assert-event
 (equal (car (fn-bpah-pending-decision-at
              (fn-bpnf-answer-state *bpaht-old-accepted*)
              *bpah-local* *bpaht-wall-less*)) :uncertain))
(defconst *bpaht-issued-uncertain*
  (fn-bpnf-with-issued
   *bpaht-two-held*
   (fn-bpnf-operation 1 2 :store *bpaht-new-held* :uncertain)))
(assert-event
 (equal (car (fn-bpah-pending-decision-at
              *bpaht-issued-uncertain* *bpah-local*
              *bpaht-wall-less*)) :ready))
(assert-event
 (equal (fn-bpnf-answer-state
         (fn-bpnf-step *bpaht-issued-uncertain*
                        (list :deliver (second (second *bpaht-two-decision*))
                              *bpah-local*)))
        *bpaht-issued-uncertain*))
(assert-event
 (not (equal (car (car (fn-bpnf-answer-effects
                        (fn-bpnf-step
                         *bpaht-issued-uncertain*
                         (list :deliver
                               (second (second *bpaht-two-decision*))
                               *bpah-local*)))))
             :deliver)))

; The selector's live-seed hypothesis has teeth: an already-selected
; uncertain row survives an empty scan, so its conclusion would be false.
(assert-event
 (equal (fn-bpah-select-oldest-at nil *bpah-local*
                                    *bpaht-wall-less* *bpaht-old-held*)
        *bpaht-old-held*))
(must-fail
 (assert-event
  (equal (fn-bpah-held-expiry
          (fn-bpah-select-oldest-at nil *bpah-local*
                                     *bpaht-wall-less* *bpaht-old-held*)
          *bpaht-wall-less*) :live)))
(assert-event
 (null (fn-bpah-select-oldest-at nil *bpah-local*
                                    *bpaht-wall-less* nil)))
(must-fail
 (assert-event
  (equal (fn-bpah-held-expiry
          (fn-bpah-select-oldest-at nil *bpah-local*
                                     *bpaht-wall-less* nil)
          *bpaht-wall-less*) :live)))
