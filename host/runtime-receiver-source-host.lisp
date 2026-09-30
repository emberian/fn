; Installed receiver association readout. Current source has no qualified
; runtime installer, so neither provider shape nor a retained current token
; can manufacture availability. The successful ABI is :current/token/instance.
(in-package "ACL2")
(include-book "../books/runtime-operation-source")
(include-book "../books/receiver-turn-controller")
(include-book "../books/receiver-capacity-current")
(defun fn-owner-runtime-receiver-source
  (fn-rx-provider fn-receiver-turn fn-rx-capacity-current
                  fn-page-read-pool state)
  (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn
                          fn-rx-capacity-current fn-page-read-pool state)
                  :guard t))
  (declare (ignore fn-rx-provider fn-receiver-turn fn-rx-capacity-current
                   fn-page-read-pool state))
  (mv :receiver-unavailable nil nil))
