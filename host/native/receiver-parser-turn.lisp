;;; Fixed native transport for the retained receiver/parser controller.
;;; The caller holds the owner mutex inside fnn-owner-shared-action-locked.
;;; Constructor/BODY funding and scheduler/output lifetime are separate joins;
;;; a callback's presence never establishes those grants.
(in-package "ACL2")

(defun fnn-owner-receiver-turn-parser-locked (service cid node sched ticket)
  "Pass the actual retained connection and receiver objects to the core."
  (let ((runtime (fnn-owner-service-receiver-runtime service)))
    (unless (fnn-owner-receiver-turn-runtime-p runtime)
      (fnn-fixed-callback-fail 'fn-owner-rx-turn-parser-span
                               :receiver-startup-incomplete nil))
    (unless node
      (fnn-fixed-callback-fail 'fn-owner-rx-turn-parser-span
                               :connection-custody-missing nil))
    (let ((callback (fnn-owner-receiver-turn-runtime-parser runtime)))
      (unless callback
        (fnn-fixed-callback-fail 'fn-owner-rx-turn-parser-span
                                 :parser-callback-unavailable nil))
      (sb-thread:with-mutex (*fnn-extent-lock*)
        (multiple-value-bind (word step episode provider turn pool state)
            (fnn-core-mv 'fn-owner-rx-turn-parser-span
              (funcall callback cid (fnn-connection-custody-token node)
                       sched ticket
                       (fnn-owner-receiver-turn-runtime-provider runtime)
                       (fnn-owner-receiver-turn-runtime-turn runtime)
                       (fnn-owner-receiver-turn-runtime-current runtime)
                       (fnn-owner-service-connection-pool service)
                       (fnn-live-arena) (fnn-live-cat) *the-live-state*))
          (declare (ignore state))
          ;; Store every returned root before the caller handles the word or
          ;; exposes a response. No host reconstruction of the core episode.
          (setf (fnn-owner-receiver-turn-runtime-provider runtime) provider
                (fnn-owner-receiver-turn-runtime-turn runtime) turn
                (fnn-owner-service-connection-pool service) pool)
          (values word step episode))))))
