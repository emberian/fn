; One row's kind-8 reservation and kind-9 settlement are shared by replay.
(in-package "ACL2")
(include-book "../../books/bp-forward-attempt")
(include-book "../../books/bp-node-dispatch")
(include-book "../../books/bp-node-debt")
(include-book "must-fail-checked")

(defconst *bpnfa-local* (cons :dtn '(47 47 98 112 45 108 111 99 97 108 47)))
(defconst *bpnfa-peer* (cons :dtn '(47 47 98 112 45 112 101 101 114 47)))
(defconst *bpnfa-config* (fn-bpn-config *bpnfa-local* 3600000 2 32 1048576))
(defconst *bpnfa-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *bpnfa-bundle*
  (fn-bpn-send-bundle *bpnfa-config* *bpnfa-peer* '(1 2 3 4) 1 *bpnfa-obs*))
(defconst *bpnfa-h0*
  (fn-bpnf-held nil (fn-bpb-bundle-id *bpnfa-bundle*) 0 nil nil nil
                *bpnfa-bundle* (fn-bpb-encode *bpnfa-bundle*)
                '(:observed-age 0 1000) nil nil '(:dispatch-pending)
                nil nil 0))
(defconst *bpnfa-dispatch*
  (fn-bpnp-dispatch-record 0 0 0
                             (fn-bpah-held-primary-identity *bpnfa-h0*)
                             *bpnfa-peer*))
(defconst *bpnfa-dispatched*
  (fn-bpnp-dispatch-apply *bpnfa-dispatch* (list *bpnfa-h0*)))
(defconst *bpnfa-h1* (fn-bpn-nth 2 *bpnfa-dispatched*))
(defconst *bpnfa-image*
  (fn-bpnp-forward-image *bpnfa-h1* *bpnfa-local* *bpnfa-obs*))
(defconst *bpnfa-attempt*
 (fn-bpnp-forward-attempt-record
   0 1 0 (fn-bpah-held-primary-identity *bpnfa-h1*)
   *bpnfa-peer* (cons 0 1) 0))
(defconst *bpnfa-attempt-applied*
  (fn-bpnp-attempt-apply *bpnfa-attempt* (list *bpnfa-h1*)))
(defconst *bpnfa-h2* (fn-bpn-nth 2 *bpnfa-attempt-applied*))
(defconst *bpnfa-failed*
  (fn-bpnp-forward-result-record
   0 2 0 (fn-bpah-held-primary-identity *bpnfa-h2*)
   0 1 (cons 0 1) :failed))
(defconst *bpnfa-sent*
  (fn-bpnp-forward-result-record
   0 2 0 (fn-bpah-held-primary-identity *bpnfa-h2*)
   0 1 (cons 0 1) :sent))

(assert-event (equal (car *bpnfa-dispatched*) :ready))
(assert-event (equal (car *bpnfa-image*) :ready))
(assert-event (equal (car *bpnfa-attempt-applied*) :ready))
(assert-event (equal (fn-bpnd-held-debt *bpnfa-h1* *bpnfa-local*) 2))
(assert-event (equal (fn-bpnd-held-debt *bpnfa-h2* *bpnfa-local*) 3))
(assert-event
 (let ((applied (fn-bpnp-forward-result-apply
                 *bpnfa-failed* (list *bpnfa-h2*))))
   (and (equal (car applied) :ready)
        (equal (fn-bpn-nth 12 (fn-bpn-nth 2 applied))
               '(:forward-pending))
        (null (fn-bpn-nth 13 (fn-bpn-nth 2 applied)))
        (equal (fn-bpnd-held-debt (fn-bpn-nth 2 applied) *bpnfa-local*) 2))))
(assert-event
 (let ((applied (fn-bpnp-forward-result-apply
                 *bpnfa-sent* (list *bpnfa-h2*))))
   (and (equal (car applied) :ready)
        (equal (fn-bpn-nth 12 (fn-bpn-nth 2 applied))
               '(:dispatch-done))
        (null (fn-bpn-nth 13 (fn-bpn-nth 2 applied)))
        (equal (fn-bpnd-held-debt (fn-bpn-nth 2 applied) *bpnfa-local*) 1))))
(assert-event
 (equal (car (fn-bpnp-forward-result-apply
              (fn-bpnp-forward-result-record
               0 2 0 (fn-bpah-held-primary-identity *bpnfa-h2*)
               0 1 (cons 0 2) :sent)
              (list *bpnfa-h2*)))
        :fault))

; KEYSTONE teeth (PRF-1035,
; fn-bpnp-configured-budgets-admits-exactly-the-frame-bounded-positive-budgets):
; absent rows take the defaults; configured rows are carried and read back by
; name; a zero retry budget, a negative backoff and an over-frame backoff are
; refused (nil, which bp-node.lisp refuses).
(assert-event
 (and (equal (fn-bpnp-configured-budgets nil nil)
             (fn-bpnp-budgets *fn-bpnp-default-owner-backoff*
                              *fn-bpnp-max-forward-retries*))
      (fn-frame-natp 7) (fn-frame-natp 2) (< 0 2)
      (fn-bpnp-budgetsp (fn-bpnp-configured-budgets 7 2))
      (equal (fn-bpnp-configured-budgets 7 2) (fn-bpnp-budgets 7 2))
      (equal (fn-bpnp-budget-backoff (fn-bpnp-configured-budgets 7 2)) 7)
      (equal (fn-bpnp-budget-retries (fn-bpnp-configured-budgets 7 2)) 2)
      (equal (fn-bpnp-budget-retries (fn-bpnp-configured-budgets 7 nil))
             *fn-bpnp-max-forward-retries*)))
(assert-event
 (and (null (fn-bpnp-configured-budgets 7 0))
      (null (fn-bpnp-configured-budgets -1 2))
      (not (fn-frame-natp (1+ *fn-frame-max-nat*)))
      (null (fn-bpnp-configured-budgets (1+ *fn-frame-max-nat*) 2))))
(must-fail-checked
 (assert-event (fn-bpnp-budgetsp (fn-bpnp-configured-budgets 7 0))))
