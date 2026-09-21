; ACL2-facing boundary for native hybrid signing and verification.
(in-package "ACL2")
(include-book "../books/hybrid-signature")

(defun fn-hsig-host-preimage (principal keys source)
  (declare (xargs :mode :program))
  (if (fn-hsig-subject-p principal keys source)
      (fn-hsig-signed-preimage principal keys source)
    nil))

(defun fn-hsig-host-authorize
    (principal keys source signatures observed-ml-key ed ml)
  (declare (xargs :mode :program))
  (fn-hsig-authorize principal keys source signatures observed-ml-key ed ml))
