(in-package "ACL2")
(include-book "../../books/admission-semantic-node")
(defconst *asn-node* (fn-node-initial-state nil 4))
(defconst *asn-event* '(:consumer-authority 1 2 0 (:authority-begin (65) 0 1 7)))
; Logical source witness, not an installed issuer/BODY witness.
(defthm asn-node-family-positive
 (and (posp 1) (fn-node-statep *asn-node*)
      (fn-store-event-p *asn-event*) (fn-evc-authorityp *asn-event*)
      (eq (mv-nth 0 (fn-asn-authority-node-one 1 *asn-node* *asn-event*)) :node-ready)
      (equal (mv-nth 1 (fn-asn-authority-node-one 1 *asn-node* *asn-event*))
             (fn-replay-apply-record *asn-node* *asn-event*))
      (equal (mv-nth 2 (fn-asn-authority-node-one 1 *asn-node* *asn-event*)) '(:same))
      (equal (mv-nth 3 (fn-asn-authority-node-one 1 *asn-node* *asn-event*)) 0)))
;@hypothesis-removal-witness fn-asn-authority-node-one-is-replay-apply-record
(defthm asn-node-zero-fuel-removal
 (and (not (posp 0)) (fn-node-statep *asn-node*)
      (fn-store-event-p *asn-event*) (fn-evc-authorityp *asn-event*)
      (eq (mv-nth 0 (fn-asn-authority-node-one 0 *asn-node* *asn-event*)) :yield)
      (equal (mv-nth 1 (fn-asn-authority-node-one 0 *asn-node* *asn-event*)) *asn-node*)
      (not (equal (fn-replay-apply-record *asn-node* *asn-event*)
                  (if (eq (mv-nth 0 (fn-asn-authority-node-one 0 *asn-node* *asn-event*)) :node-ready)
                      (mv-nth 1 (fn-asn-authority-node-one 0 *asn-node* *asn-event*)) nil)))))

(defconst *asn-cn* (fn-cnode-make *asn-node* '(0 (nil 4 nil nil nil nil nil nil nil nil nil))))
(defthm asn-configured-family-positive
 (and (posp 1) (fn-cnode-statep *asn-cn*)
      (fn-store-event-p *asn-event*) (fn-evc-authorityp *asn-event*)
      (eq (mv-nth 0 (fn-asn-authority-one 1 *asn-cn* *asn-event*)) :node-ready)
      (equal (mv-nth 1 (fn-asn-authority-one 1 *asn-cn* *asn-event*))
             (fn-cpr-apply-event *asn-cn* *asn-event*))
      (equal (mv-nth 2 (fn-asn-authority-one 1 *asn-cn* *asn-event*)) '(:same))
      (equal (mv-nth 3 (fn-asn-authority-one 1 *asn-cn* *asn-event*)) 0)))
;@hypothesis-removal-witness fn-asn-authority-one-is-cpr-apply-event
(defthm asn-configured-zero-fuel-removal
 (and (not (posp 0)) (fn-cnode-statep *asn-cn*)
      (fn-store-event-p *asn-event*) (fn-evc-authorityp *asn-event*)
      (eq (mv-nth 0 (fn-asn-authority-one 0 *asn-cn* *asn-event*)) :yield)
      (equal (mv-nth 1 (fn-asn-authority-one 0 *asn-cn* *asn-event*)) *asn-cn*)
      (not (equal (fn-cpr-apply-event *asn-cn* *asn-event*)
                  (if (eq (mv-nth 0 (fn-asn-authority-one 0 *asn-cn* *asn-event*)) :node-ready)
                      (mv-nth 1 (fn-asn-authority-one 0 *asn-cn* *asn-event*)) nil)))))
