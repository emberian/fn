; Unchanged u32 record scalar domain.
(in-package "ACL2")
(include-book "cbor")

(defun fn-record-uint32p (n)
  (and (natp n) (<= n *fn-cbor-max-uint*)))

(verify-guards fn-record-uint32p)
