; Recover the actual original POST source before any stored-only metadata.
; This boundary never consults the current configuration's injecting agent.
(in-package "ACL2")
(include-book "acceptance-binding")
(include-book "poster-bytes-invariants")

(defun fn-abi-post-source (decision)
  (declare (xargs :guard t))
  (if (fn-inj-injectedp decision)
      (let* ((octets (fn-inj-decision-octets decision))
             (msgid (fn-inj-decision-msgid decision))
             (agent (fn-pb-path-agent octets msgid)))
        (fn-inj-source-of octets agent msgid))
    nil))

(defthm fn-abi-post-source-recovers-successful-post
  (implies (fn-inj-injectedp (fn-inj-decide source config obs))
           (equal (fn-abi-post-source (fn-inj-decide source config obs))
                  (cons t source)))
  :hints (("Goal"
           :use (fn-pb-path-agent-of-an-injection
                 (:instance fn-inj-source-of-inverts-the-injection
                            (observation obs)))
           :in-theory (e/d (fn-abi-post-source)
                            (fn-inj-decide fn-inj-injectedp fn-pb-path-agent
                             fn-inj-source-of fn-inj-decision-octets
                             fn-inj-decision-msgid)))))

(defun fn-abi-post-binding (decision)
  (declare (xargs :guard t))
  (let ((original (fn-abi-post-source decision)))
    (if (and (consp original) (car original))
        (fn-ab-for-received :post-d25 (cdr original))
      nil)))

(defthm fn-abi-post-binding-is-valid-or-refused
  (or (null (fn-abi-post-binding decision))
      (fn-ab-p (fn-abi-post-binding decision)))
  :hints (("Goal" :in-theory (e/d (fn-abi-post-binding)
                                   (fn-ab-p fn-ab-for-received)))))

; The submission's context was selected by its actual ingress constructor.
; Received bytes are read before stored-only Path/Injection-Info/Cancel-Lock
; rewriting, and the successful POST arm requires the inverse's success.
(defun fn-abi-sub-binding (sub)
  (declare (xargs :guard t))
  (case (fn-own-sub-source-context sub)
    (:post-d25 (fn-abi-post-binding (fn-own-sub-decision sub)))
    (:relay-v1 (fn-ab-for-received :relay-v1 (fn-own-sub-octets sub)))
    (:native-source (fn-ab-for-received :native-source (fn-own-sub-octets sub)))
    (otherwise nil)))

(defthm fn-abi-sub-binding-is-valid-or-refused
  (or (null (fn-abi-sub-binding sub)) (fn-ab-p (fn-abi-sub-binding sub)))
  :hints (("Goal" :in-theory (e/d (fn-abi-sub-binding)
                                   (fn-ab-p fn-ab-for-received
                                    fn-abi-post-binding)))))

(in-theory (disable fn-abi-post-source fn-abi-post-binding fn-abi-sub-binding))
