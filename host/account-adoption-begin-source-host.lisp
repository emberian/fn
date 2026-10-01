; Actual lexical phase2 source application. The compiled installer must bind
; this protocol callable and its complete source-evaluation/body closure.
; Its current explicit unavailable result prevents all initial constructors.
(in-package "ACL2")
(include-book "account-adoption-turn-host")
(include-book "../books/account-adoption-operation-source")

(defun fn-owner-account-begin-resources
 (config bindings entropy slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :mode :program :guard (boundp-global 'fn-owner state)))
 (if (not (and (fn-ats-matchingp slot nonce fn-allocation-turn-slots fn-page-read-pool)
               (eq (fn-ats-kindsi slot fn-allocation-turn-slots) :owner-control)
               (eql (fn-ats-phasesi slot fn-allocation-turn-slots) 2)))
     (mv :account-begin-source-unavailable nil)
  (mv-let (installed family)
   (fn-owner-runtime-operation-source :account-adoption-begin fn-page-read-pool state)
   (declare (ignore family))
   (if (not (eq installed :runtime-operation-available))
       (mv :account-begin-source-unavailable nil)
    (mv-let (word actual-family roles resources)
     (fn-cado-begin-operation-source config bindings entropy
       (fn-owner-config state)
       (fn-cp-nth 2 (fn-sn-consumer (fn-owner-store state)))
       (fn-state-next-txid (fn-node-acceptance (fn-sn-node (fn-owner-store state)))))
     (declare (ignore actual-family roles))
     ; This callable has no positive branch. A future complete recipe must
     ; join its exact compiler binding, role table and original result ABI;
     ; this source cut does not authorize an arbitrary available atom.
     (mv word resources))))))

(defun fn-owner-account-adoption-begin-prepay
 (config bindings entropy slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :mode :program :guard (boundp-global 'fn-owner state)))
 (mv-let (available resources)
  (fn-owner-account-begin-resources config bindings entropy slot nonce
     fn-allocation-turn-slots fn-page-read-pool state)
  (if (not (and (eq available :account-operation-resources-available)
                (fn-cado-widthp 8 resources)
                (eq (fn-cp-nth 0 resources) :account-adoption-resources)
                (eq (fn-cp-nth 1 resources) :begin)
                (natp (fn-cp-nth 5 resources))))
      (mv :account-turn-resources-unavailable nil fn-allocation-turn-slots fn-page-read-pool)
   (mv-let (paid fn-allocation-turn-slots fn-page-read-pool)
    (fn-ats-prepay-body-internal slot nonce (fn-cp-nth 5 resources)
       fn-allocation-turn-slots fn-page-read-pool)
    (mv paid resources fn-allocation-turn-slots fn-page-read-pool)))))
