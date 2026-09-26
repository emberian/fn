; Conditional progress of the base job offer (spec bp-node-machine 5.7):
; under A-BP-CONTACT (books/assumptions.lisp), one contact offers a ready job
; within the number of jobs at or ahead of it.  Safety (what an offer starts,
; what settles it) is books/bp-node-job-offer.lisp and holds in every
; environment; this book adds only the named assumption.
(in-package "ACL2")
(include-book "bp-node-job-offer")
(include-book "assumptions")

(defthm fn-bpnj-unoffered-is-no-longer-than-its-keys
  (<= (len (fn-bpnj-unoffered keys offered)) (len keys))
  :rule-classes :linear)

;; KEYSTONE (conditional progress).  If a contact to PEER sustains the asks
;; A-BP-CONTACT names, and in every ask the job KEY names stays ready with
;; the same PREFIX of keys at or ahead of it, and the prefix is no longer
;; than the asks, then the host's first ask is answered with an offer and the
;; contact offers KEY.  The environment may do
;; anything else between two asks: requeue, refuse or finish other jobs.
(defthm fn-bpnj-contact-offers-a-ready-job-under-a-bp-contact
  (implies (and (fn-bpnj-stays-ready-p sts peer routing key prefix)
                (member-equal key prefix)
                (<= (len prefix) (fn-assume-bp-contact-asks peer))
                (equal (len sts) (fn-assume-bp-contact-asks peer)))
           (and (equal (car (fn-bpnj-contact-next (car sts) peer routing nil)) :offer)
                (member-equal key (fn-bpnj-contact-offers sts peer routing nil))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnj-contact-offers-a-ready-job-within-its-prefix
                  (offered nil))
                 (:instance fn-bpnj-unoffered-is-no-longer-than-its-keys
                  (keys prefix) (offered nil))
                 (:instance fn-bpnj-unoffered-key-counts (keys prefix) (offered nil))
                 (:instance fn-bpnj-one-ask-offers-within-the-prefix
                  (st (car sts)) (offered nil)))
           :in-theory (union-theories '(member-equal (:e member-equal) fn-bpnj-stays-ready-p
                                        len (:type-prescription len) fn-bpn-nth fn-cbor-ag-car
                                        (:e zp) (:e natp) zp natp)
                                      (theory 'minimal-theory)))))
