; Actual first consumer bootstrap: bounded initial carries from parsed field
; lengths. This seed has no adopted accounts, pending preparation or usable
; authority namespace. Nonempty recovery must consume actual durable stages.
(in-package "ACL2")
(include-book "consumer-account-carried")

(defun fn-caac-initial (history incarnation frontier history-octets incarnation-octets)
  (declare (xargs :guard t))
  (let* ((cp (fn-cp-initial history incarnation frontier))
         (fields (list (fn-caac-atom :consumer-state)
                       (fn-scs-octets (nfix history-octets))
                       (fn-scs-octets (nfix incarnation-octets))
                       (fn-caac-atom frontier) (fn-caac-atom 1)
                       (fn-caac-atom nil) (fn-caac-atom nil))))
    (mv cp (fn-caac-metadata cp fields nil nil))))

(defthm fn-caac-initial-keeps-logical-state-by-definition
  (equal (mv-nth 0 (fn-caac-initial history incarnation frontier hn in))
         (fn-cp-initial history incarnation frontier))
  :hints (("Goal" :in-theory (enable fn-caac-initial))))

(defthm fn-caac-initial-seven-fields-correspond
  (implies (and (fn-scc-octet-listp history)
                (equal hn (len history))
                (fn-scc-octet-listp incarnation)
                (equal in (len incarnation))
                (integerp frontier))
           (fn-scs-correspondsp
            (fn-cp-nth 1 (mv-nth 1 (fn-caac-initial history incarnation frontier hn in)))
            (fn-cp-initial history incarnation frontier)))
  :hints (("Goal"
           :use ((:instance fn-scs-octets-establishes-canonical-size (xs history) (n hn))
                 (:instance fn-scs-octets-establishes-canonical-size (xs incarnation) (n in)))
           :in-theory
           (e/d (fn-caac-initial fn-caac-metadata fn-caac-authority-carry
                  fn-caac-list-carry fn-caac-pending-carry fn-caac-atom
                  fn-cp-initial fn-cp-state fn-cp-state-carry fn-cp-nth
                  fn-scs-correspondsp fn-cait-size)
                (fn-scs-summary fn-scs-octets fn-scs-atom fn-caac-spine)))))
