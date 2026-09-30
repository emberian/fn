; Flat projections used by the native outbound BP lifecycle service.
; host/native/bp-service.lisp calls fn-bpn-step itself; these wrappers expose
; records and frames without giving the host a second transition function.

(in-package "ACL2")
(include-book "../books/bp-node-host-machine")

(defun fn-bpn-host-ready-peers (st)
  ; fnn-bps-open checks the initial invariant once.  Its only later state
  ; writes are fn-bpn-step answers, whose transition preserves it.
  (fn-bpn-ready-peers (fn-bpn-machine-state-jobs st)))

; fn-bpn-host-existing-sequence, fn-bpn-host-existing-sequence-p and
; fn-bpn-host-existing-sequence-value are books/bp-node-host-machine.lisp's
; (guard-verified, with the keystone PRF-1031).

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

(defun fn-bpn-host-lifecycle-record-name (token)
  (fn-bpn-lifecycle-record-name token))

(defun fn-bpn-host-lifecycle-recovery (names records)
  (fn-bpn-lifecycle-recovery names records))

(defun fn-bpn-host-lifecycle-recovery-ready-p (answer)
  (and (equal (car answer) :ready) t))

(defun fn-bpn-host-lifecycle-recovery-records (answer)
  (fn-bpn-lifecycle-recovery-records answer))

(defun fn-bpn-host-lifecycle-recovery-stages (answer)
  (fn-bpn-lifecycle-recovery-stages answer))

; fn-bpn-host-lifecycle-recovery-agrees-p: books/bp-node-host-machine (guard-verified, with its keystone).

(defun fn-bpn-host-lifecycle-publication-authorize
  (st token record lock-owned final-absent)
  (fn-bpn-lifecycle-publication-authorize
   st token record lock-owned final-absent))

(defun fn-bpn-host-lifecycle-publication-operationp (operation)
  (if (fn-bpn-lifecycle-publication-operationp operation) t nil))

(defun fn-bpn-host-lifecycle-publication-operation-token (operation)
  (fn-bpn-lifecycle-publication-operation-token operation))

(defun fn-bpn-host-lifecycle-publication-operation-record (operation)
  (fn-bpn-lifecycle-publication-operation-record operation))

(defun fn-bpn-host-lifecycle-publication-operation-publication (operation)
  (fn-bpn-lifecycle-publication-operation-publication operation))

(defun fn-bpn-host-machine-max-jobs () *fn-bpn-machine-max-jobs*)
(defun fn-bpn-host-machine-max-octets () *fn-bpn-machine-max-octets*)
