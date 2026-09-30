; The actual native charge producer and the profile/codec field domain.
(in-package "ACL2")
(include-book "identity-invariants")
(include-book "post-fields")

(defun fn-store-charge (length)
  (declare (xargs :guard t))
  (if (natp length) (fn-charge-for-payload length) 0))

; The record codec ceiling is the supported representation domain. This
; proves the actual host-called producer's output before record interning;
; no later staging/refusal is used to justify the input to the intern.
(defthm fn-store-charge-is-positive-and-representable
  (implies (fn-pfld-payload-sizep length)
           (and (posp (fn-store-charge length))
                (fn-record-uint32p (fn-store-charge length))))
  :hints (("Goal"
           :use ((:instance fn-charge-for-payload-monotone
                            (m length) (n *fn-record-max-payload*)))
           :in-theory (e/d (fn-store-charge fn-pfld-payload-sizep
                            fn-record-uint32p)
                           (fn-charge-for-payload)))))

(in-theory (disable fn-store-charge))
