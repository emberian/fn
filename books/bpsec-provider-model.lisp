; Logical provider relation for the BPSec immutable-span boundary.
; This defines a premise; it does not install or authenticate a host provider.
(in-package "ACL2")
(include-book "bpsec-model")

(defun fn-bps-backingsp (backings)
  (declare (xargs :guard t))
  (if (consp backings)
      (and (consp (car backings)) (fn-cbor-octet-listp (cdar backings))
           (not (consp (fn-bps-backing-entry (caar backings) (cdr backings))))
           (fn-bps-backingsp (cdr backings))) (null backings)))

(defun fn-bps-window-backing-matchp (window backings)
  (declare (xargs :guard t))
  (and (fn-bps-backingsp backings) (fn-bps-windowp window)
       (consp (fn-bps-backing-entry (fn-bps-field 1 window) backings))
       (equal (fn-bps-field 3 window)
              (fn-bps-span-octets
               (fn-bps-span-make :bytes-span (fn-bps-field 1 window)
                                  (fn-bps-field 2 window) (len (fn-bps-field 3 window))) backings))))

; A matching identity/offset cannot turn substituted bytes into a provider
; witness. Empty slices likewise require a real, present backing entry.
(assert-event
 (let ((backings '((:input 129 1 1 0))))
   (and (fn-bps-backingsp backings)
        (fn-bps-window-backing-matchp (fn-bps-window-make :input 0 '(129 1)) backings)
        (not (fn-bps-window-backing-matchp (fn-bps-window-make :input 0 '(129 0)) backings))
        (not (fn-bps-window-backing-matchp (fn-bps-window-make :absent 0 nil) backings)))))
(assert-event (not (fn-bps-backingsp '((:input 1) (:input 2)))))
