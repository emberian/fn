; Teeth for books/owner-prepare-outcome-topic.lisp: the topic entry's
; consumer-projection refusal against the consumer relation.
(in-package "ACL2")
(include-book "owner-prepare-outcome-tests")
(include-book "../../books/owner-prepare-outcome-topic")

(defun pott-install (oc)
  ; The topic install ACL2 proposes at OC's coordinates (the host's
  ; fn-owner-topic-propose), or NIL.
  (let ((p (fn-th-local-propose :install (fn-sn-topic (lgt-store oc)) (psa-txid oc) 0 1000
                                (make-list 32 :initial-element 7) 0)))
    (and (equal (car p) :ok) (cadr p))))

; -----------------------------------------------------------------------------
; fn-pout-staged-topic-passes-the-consumer-projection and
; fn-pout-topic-entry-is-the-store-prepare-under-the-consumer-relation.
; REACHABLE, consumer unbootstrapped: the reserved configured owner.
(defconst *pott-s0* (lgt-store *lgt-reserved*))
(assert-event (fn-sn-statep *pott-s0*))
(assert-event (fn-snt-consumerp *pott-s0*))
(assert-event (null (fn-sn-consumer *pott-s0*)))
(assert-event (not (equal (fn-sn-prepare-topic *pott-s0* *pse-topic-event*) *pott-s0*)))
(assert-event (eq (car (fn-cpe-projection-step (fn-sn-consumer *pott-s0*) *pse-topic-event*
                                               (fn-sn-identity-next *pott-s0*)))
                  :ok))
(assert-event (equal (lgt-store (second (pot-topic *lgt-reserved* *pse-topic-event*)))
                     (fn-sn-prepare-topic *pott-s0* *pse-topic-event*)))
; REACHABLE, consumer bootstrapped: the owner after the consumer bootstrap
; completed, reserved again; the install ACL2 proposes there.
(defconst *pott-c-reserved* (fn-olr-ocfg-reserve *pse-consumer-finished*))
(defconst *pott-s1* (lgt-store *pott-c-reserved*))
(defconst *pott-e1* (pott-install *pott-c-reserved*))
(assert-event (fn-th-topic-eventp *pott-e1*))
(assert-event (equal (lgt-phase *pott-c-reserved*) :reserved))
(assert-event (fn-sn-statep *pott-s1*))
(assert-event (fn-snt-consumerp *pott-s1*))
(assert-event (consp (fn-sn-consumer *pott-s1*)))
(assert-event (equal (fn-cp-nth 3 (fn-sn-consumer *pott-s1*)) (fn-sn-identity-next *pott-s1*)))
(assert-event (not (equal (fn-sn-prepare-topic *pott-s1* *pott-e1*) *pott-s1*)))
(assert-event (eq (car (fn-cpe-projection-step (fn-sn-consumer *pott-s1*) *pott-e1*
                                               (fn-sn-identity-next *pott-s1*)))
                  :ok))
(defconst *pott-t1* (pot-topic *pott-c-reserved* *pott-e1*))
(assert-event (equal (first *pott-t1*) :prepared))
(assert-event (equal (lgt-store (second *pott-t1*)) (fn-sn-prepare-topic *pott-s1* *pott-e1*)))

; CORRUPTED-STATE hypothesis-removal witness (fn-snt-consumerp): the same
; reserved owner with its carried consumer frontier moved one past the next
; sequence.  The owner's carried invariant fn-lgoc-invariantp still holds
; (it does not read the consumer projection) and fn-sn-statep holds; the
; consumer relation fails; fn-sn-prepare-topic would stage the install, but
; the projection refuses it, so the entry answers :refused and its Store is
; not fn-sn-prepare-topic's: both conclusions fail.  This is the state the
; entry's projection test exists for.
(defconst *pott-bad*
  (let ((c (fn-sn-consumer *pott-s1*)))
    (fn-ocfg-with-owner
     *pott-c-reserved*
     (fn-ocl-owner-with-store
      (fn-ocfg-owner *pott-c-reserved*)
      (fn-sn-with-consumer *pott-s1* (fn-cpe-projection-advance c (1+ (fn-cp-nth 3 c))))))))
(defconst *pott-sb* (lgt-store *pott-bad*))
(assert-event (fn-lgoc-invariantp *pott-bad*))
(assert-event (fn-sn-statep *pott-sb*))
(assert-event (not (fn-snt-consumerp *pott-sb*)))
(assert-event (not (equal (fn-sn-prepare-topic *pott-sb* *pott-e1*) *pott-sb*)))
(assert-event (not (eq (car (fn-cpe-projection-step (fn-sn-consumer *pott-sb*) *pott-e1*
                                                    (fn-sn-identity-next *pott-sb*)))
                       :ok)))
(defconst *pott-tb* (pot-topic *pott-bad* *pott-e1*))
(assert-event (equal (first *pott-tb*) :refused))
(assert-event (not (equal (lgt-store (second *pott-tb*))
                          (fn-sn-prepare-topic *pott-sb* *pott-e1*))))
