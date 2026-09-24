; Exact FNBS attempt/result frames and cross-kind refusal.
(in-package "ACL2")
(include-book "../../books/bp-fnbs-forward-codec")

(defconst *bpnfc-peer* (cons :dtn '(47 47 98 112 45 112 101 101 114 47)))
(defconst *bpnfc-identity* '(1 2 3 4))
(defconst *bpnfc-attempt*
  (fn-bpnp-forward-attempt-record
   1 2 3 *bpnfc-identity* *bpnfc-peer* (cons 0 7) 25))
(defconst *bpnfc-result*
  (fn-bpnp-forward-result-record
   1 3 3 *bpnfc-identity* 1 2 (cons 0 7) :sent))

(assert-event (fn-bpnp-forward-attempt-recordp *bpnfc-attempt*))
(assert-event (fn-bpnp-forward-result-recordp *bpnfc-result*))
(assert-event (not (equal (fn-bpnp-attempt-frame *bpnfc-attempt*) :bad)))
(assert-event (not (equal (fn-bpnp-result-frame *bpnfc-result*) :bad)))
(assert-event
 (equal (fn-bpnp-attempt-unframe (fn-bpnp-attempt-frame *bpnfc-attempt*))
        *bpnfc-attempt*))
(assert-event
 (equal (fn-bpnp-result-unframe (fn-bpnp-result-frame *bpnfc-result*))
        *bpnfc-result*))
(assert-event
 (not (fn-bpnp-result-unframe (fn-bpnp-attempt-frame *bpnfc-attempt*))))
(assert-event
 (not (fn-bpnp-attempt-unframe (fn-bpnp-result-frame *bpnfc-result*))))
(assert-event
 (not (fn-bpnp-attempt-unframe
       (append (fn-bpnp-attempt-frame *bpnfc-attempt*) '(0)))))
(assert-event
 (equal (fn-bpnp-attempt-frame
         (fn-bpnp-forward-attempt-record
          1 2 3 *bpnfc-identity* *bpnfc-peer* (cons 0 7)
          (1+ *fn-frame-max-nat*)))
        :bad))
