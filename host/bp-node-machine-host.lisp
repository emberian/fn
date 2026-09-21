; Flat projections used by the native outbound BP lifecycle service.
; host/native/bp-service.lisp calls fn-bpn-step itself; these wrappers expose
; records and frames without giving the host a second transition function.

(in-package "ACL2")

(defun fn-bpn-host-machine-initial (config max-jobs max-octets)
  (fn-bpn-initial-machine-state config max-jobs max-octets))

(defun fn-bpn-host-machine-statep (st)
  (and (fn-bpn-machine-statep st) t))

(defun fn-bpn-host-answer-state (answer)
  (fn-bpn-answer-state answer))

(defun fn-bpn-host-answer-effects (answer)
  (fn-bpn-answer-effects answer))

(defun fn-bpn-host-ready-peers (st)
  (if (fn-bpn-machine-statep st)
      (fn-bpn-ready-peers (fn-bpn-machine-state-jobs st))
    nil))

(defun fn-bpn-host-existing-sequence (st work attempt generation)
  (fn-bpn-existing-sequence st (list work attempt generation)))

(defun fn-bpn-host-existing-sequence-p (answer)
  (and (fn-bpn-existing-sequencep answer) t))

(defun fn-bpn-host-existing-sequence-value (answer)
  (if (fn-bpn-existing-sequencep answer) (nth 1 answer) nil))

(defun fn-bpn-host-lifecycle-record-frame (record)
  (if (fn-bpn-lifecycle-recordp record)
      (fn-bpn-lifecycle-record-frame record)
    nil))

(defun fn-bpn-host-lifecycle-record-unframe (octets)
  (if (fn-cbor-octet-listp octets)
      (fn-bpn-lifecycle-record-unframe octets)
    nil))

(defun fn-bpn-host-lifecycle-frame-limit ()
  (fn-bpn-lifecycle-frame-limit))

(defun fn-bpn-host-machine-max-jobs () *fn-bpn-machine-max-jobs*)
(defun fn-bpn-host-machine-max-octets () *fn-bpn-machine-max-octets*)
(defun fn-bpn-host-machine-max-records () *fn-bpn-machine-max-records*)
