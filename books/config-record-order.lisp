; Exact physical journal comparator shared by configured replay and account
; authority replay. Configuration ties precede Store events, in config order.
; Definitions/statements extracted verbatim from config-physical-replay.
(in-package "ACL2")
(include-book "config")
(include-book "store-events")

(defun fn-cpr-config-firstp (configs events)
  (declare (xargs :guard t))
  (and (consp configs)
       (or (not (consp events))
           (<= (nfix (fn-cfg-record-txid (car configs)))
               (nfix (fn-store-event-txid (car events)))))))

(defthm fn-cpr-config-firstp-has-config
  (implies (fn-cpr-config-firstp configs events) (consp configs))
  :hints (("Goal" :in-theory (enable fn-cpr-config-firstp))))
