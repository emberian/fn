; Startup classification never silently converts an invalid enabled profile to off.
(in-package "ACL2")
(include-book "../books/host-boundary")
(defconst *fn2-compress-settings-probe*
 '((:compress-enabled . t) (:compress-input-quantum . 128)
   (:compress-output-quantum . 256) (:compress-expansion-ratio . 8)
   (:compress-expansion-burst . 1024) (:pool-classes . ((4 . 4096)))))
(assert-event
 (mv-let (code iq oq ratio burst capacity) (fn2-host-compress-settings *fn2-compress-settings-probe*)
  (equal (list code iq oq ratio burst capacity) '(:ok 128 256 8 1024 4096))))
(assert-event
 (mv-let (code iq oq ratio burst capacity) (fn2-host-compress-settings nil)
  (equal (list code iq oq ratio burst capacity) '(:off 0 0 0 0 0))))
(assert-event
 (mv-let (code iq oq ratio burst capacity)
  (fn2-host-compress-settings (put-assoc-equal :compress-expansion-burst 0 *fn2-compress-settings-probe*))
  (equal (list code iq oq ratio burst capacity) '(:compress-profile 0 0 0 0 0))))
