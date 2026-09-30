; Core decision for a carried selected-call boundary. Availability is an
; observation made at startup; carry is an ACL2-produced boundary status.
; This does not validate a store, prove a caller invariant, or price a call.
(in-package "ACL2")
(defun fn-srt-status (available carry fault)
 (declare (xargs :guard t))
 (cond (fault :fault) ((not available) :unavailable)
       ((not (eq carry :ready)) :refused) (t :ready)))
(defthm fn-srt-status-ready-requires-carried-ready
 (implies (equal (fn-srt-status available carry fault) :ready)
          (and available (equal carry :ready) (not fault)))
 :rule-classes nil)
