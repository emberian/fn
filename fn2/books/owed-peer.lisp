; Peering's keystones (layer E4; fn2/docs/e-surface.md section 13.7),
; statement first over the peer reference model (peer-model.lisp), owed with
; teeth (tests/peer-witnesses.lisp: the positive witnesses, each asserting its
; antecedent, and a fault per keystone the same witness catches). K-P2
; (transit refines the shared acceptance transaction) and K-P3b (progress
; under stated assumptions) are stated over D5 3/n's served peer path when it
; lands; the model has no carrier preparation to refine.
(in-package "ACL2")
(include-book "peer-model")
(fn2-book-layer :e)

(defthm-owed fn2-pm-peer-claim (a b)
  (implies (and (null (fn2-pm-get :faults a)) (null (fn2-pm-get :faults b)))
           (fn2-pm-kp1 a b))
  :schema :invariant :from (:operation-set fn2-consumer)
  :teeth (fn2-pmt-positive fn2-pmt-negative)
  :doc "K-P1: within one namespace and interpretation, two nodes that have durably incorporated the same evidence with no gap have equal evidence bindings and equal conflict predicates, whatever their own history entries say. Teeth: opposite first arrivals (W1) and two candidate sets meeting under exhausted funding, repaired (W2); a binding that folds local first arrival (fault :first-arrival).")

(defthm-owed fn2-pm-feed-safety (ops budget)
  (let ((st (fn2-pm-run ops (fn2-pm-node 'n budget nil))))
    (fn2-pm-kp3a (len (fn2-pm-get :feed st)) st))
  :schema :invariant :from (:operation-set fn2-consumer)
  :teeth (fn2-pmt-positive fn2-pmt-negative)
  :doc "K-P3a: every installed delivery responsibility stays a row, pending or offered, or holds exactly the terminal disposition first logged for it; no operation loses one. Teeth: F2 (a deferred head, mixed phases, a stale reply, a restart with an attempt unresolved, losses reaching the bound). Progress (K-P3b) is stated over the served path under its assumptions.")

(defthm-owed fn2-pm-one-terminal (ops budget)
  (fn2-pm-kp4 (fn2-pm-run ops (fn2-pm-node 'n budget nil)))
  :schema :invariant :from (:operation-set fn2-consumer)
  :teeth (fn2-pmt-positive fn2-pmt-negative)
  :doc "K-P4: at most one durable terminal disposition per delivery identity, across restarts, duplicate and stale replies. Teeth: F2's stale 439 after a 239; a row that takes a second terminal (fault :double-terminal).")

(defthm-owed fn2-pm-custody (ops budget)
  (fn2-pm-kp5 (fn2-pm-run ops (fn2-pm-node 'n budget nil)))
  :schema :invariant :from (:operation-set fn2-consumer)
  :teeth (fn2-pmt-positive fn2-pmt-negative)
  :doc "K-P5: a forward pin (fn1 bp-design.md 1.1) is released only by the application receipt ADU naming it from its destination (fn1 bp-receipt.md), or by the operator's waiver naming it (carry drop --abandon); a TCPCL XFER_ACK (RFC 9174 5.2.3), another pin's receipt and another node's receipt release nothing. Teeth: W7 (three refusals and one release, and a second release refused); an XFER_ACK that releases (fault :xfer-ack-releases).")

(defthm-owed fn2-pm-reclaimed-duplicate (name subject eid deps st)
  (implies (and (null (fn2-pm-get :faults st))
                (equal (cadr (fn2-pm-history-entry name st)) subject)
                (member-equal name (fn2-pm-get :reclaimed st)))
           (mv-let (o after) (fn2-pm-accept name subject eid deps st)
             (and (eq o :duplicate)
                  (equal (fn2-pm-get :allocations after) (fn2-pm-get :allocations st))
                  (equal (fn2-pm-get :pins after) (fn2-pm-get :pins st)))))
  :schema :invariant :from (:operation-set fn2-consumer)
  :teeth (fn2-pmt-positive fn2-pmt-negative)
  :doc "K-P6: an IHAVE or TAKETHIS matching a history entry whose body was reclaimed is a duplicate (435/439), allocates no article number and changes no pin. Teeth: W7; a reoffer that republishes (fault :resurrect).")
