; Actual installed source gate. CURRENT is the same retained control stobj;
; the runtime getter has no caller-supplied installation Boolean.
(in-package "ACL2")
(include-book "runtime-receiver-source-host")
(include-book "../books/connection-receiver-source")
(include-book "../books/state-globals")

(defun fn-owner-rx-connection-issued (state)
 (declare (xargs :stobjs state :guard t))
 (if (f-boundp-global 'fn-owner-rx-connection-issued state)
     (f-get-global 'fn-owner-rx-connection-issued state) nil))

(defun fn-owner-rx-parser-source-currentp
 (id holder ticket fn-rx-provider fn-receiver-turn fn-rx-capacity-current
  fn-page-read-pool state)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-rx-capacity-current
                          fn-page-read-pool state) :mode :program))
 (mv-let (word capacity instance)
  (fn-owner-runtime-receiver-source fn-rx-provider fn-receiver-turn
                                    fn-rx-capacity-current fn-page-read-pool state)
  (and (eq word :current)
       (fn-crx-turn-currentp (fn-owner-rx-connection-issued state)
                             id holder ticket capacity instance)
       (fn-owner-rx-turn-consumablep ticket fn-rx-provider
                                     fn-receiver-turn fn-page-read-pool))))

(defun fn-owner-rx-connection-revoke (id holder state)
 (declare (xargs :stobjs state :guard t))
 (f-put-global 'fn-owner-rx-connection-issued
   (fn-crx-revoke (fn-owner-rx-connection-issued state) id holder) state))
