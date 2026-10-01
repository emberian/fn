; Ordinary nonquery source seam, not a synthetic IRQ or storage issuer.
; The genuine outgoing allocator/factory is still unavailable. No constructor,
; claim mutation, bundle publication or alias release occurs on this path.
(in-package "ACL2")
(include-book "receiver-turn-controller")
(include-book "outgoing-operation-source")
(defun fn-owner-rx-output-start
 (episode fuel fn-rx-provider fn-receiver-turn fn-page-read-pool state)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool state)
                 :guard t))
 (cond
  ((not (natp fuel))
   (mv :bad-output-fuel nil fuel fn-receiver-turn fn-page-read-pool state))
  ((fn-rxt-output-bundle fn-receiver-turn)
   (mv :output-busy nil fuel fn-receiver-turn fn-page-read-pool state))
  (t
   (mv-let (word source preOC RC step)
    (fn-owner-rx-turn-response-result episode fn-rx-provider fn-receiver-turn
                                    fn-page-read-pool)
    (declare (ignore source preOC RC step))
    (cond
     ((not (eq word :response-result))
      (mv :unavailable-response nil fuel fn-receiver-turn fn-page-read-pool state))
     ((not (fn-owner-outgoing-operation-installation state))
      (mv :unavailable-output-operation nil fuel fn-receiver-turn fn-page-read-pool state))
     ; No genuine storage factory receipt exists yet. A non-NIL descriptor
     ; cannot silently supply it, and does not authorize allocating a job.
     (t (mv :unavailable-output-factory nil fuel fn-receiver-turn fn-page-read-pool state)))))))
