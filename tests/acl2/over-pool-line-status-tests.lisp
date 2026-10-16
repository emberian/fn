(in-package "ACL2")
(include-book "../../books/over-pool-line-status")

(defconst *ovrps-profile* *fn-bs-profile-development*)
(defconst *ovrps-cfg* '(2 nil 0 0 nil 0 0 0 nil 12 2 nil 0 2258))

; The whole line comes from the carried configuration, including its LF.
(defthm fn-ovr-pool-line-status-of-installed-coordinates
  (equal
   (fn-ovr-pool-line-status
    (put-global 'fn-owner-memory-lease-cfg cfg
                (put-global 'fn-owner-store-profile profile state)))
   (append (fn-nls-text "over-pool-line ")
           (fn-nls-nat (fn-ovr-over-capl-of profile cfg))
           *fn-nls-lf*))
  :hints (("Goal" :in-theory
           (e/d (fn-ovr-pool-line-status)
                (fn-ovr-over-capl-of fn-nls-text fn-nls-nat)))))

; Lowering admission A does not shrink the stored-record line.
(assert-event
 (equal (fn-ovr-over-capl-of
         (update-nth *fn-bs-pf-max-article-octets* 1 *ovrps-profile*) *ovrps-cfg*)
        (fn-ovr-over-capl
         (fn-mm-cfg-header-octets *ovrps-cfg*) *fn-record-max-payload*
         (fn-mm-cfg-server-octets *ovrps-cfg*))))
