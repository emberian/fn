; The OVER line funded by the owner's installed memory configuration.
(in-package "ACL2")
(include-book "memory-model")
(include-book "native-live-status")

(defun fn-ovr-pool-line-status (state)
  (declare (xargs :stobjs state :guard t))
  (if (and (boundp-global 'fn-owner-memory-lease-cfg state)
           (boundp-global 'fn-owner-store-profile state))
      (append (fn-nls-text "over-pool-line ")
              (fn-nls-nat
               (fn-ovr-over-capl-of
                (f-get-global 'fn-owner-store-profile state)
                (f-get-global 'fn-owner-memory-lease-cfg state)))
              *fn-nls-lf*)
    nil))
