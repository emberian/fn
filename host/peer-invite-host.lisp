; ACL2-facing boundary for the peering verbs (PRF-097, books/peer-invite.lisp).
; Every decision is the book's; these wrappers only name it for the image.
(in-package "ACL2")
(include-book "../books/peer-invite")
(include-book "../books/peer-invite-retry")

(defun fn-pinv-host-observation-subject (received)
  (declare (xargs :mode :program))
  (fn-pinv-observation-subject received))

(definterface fn-pinv-host-observation-subject
  :class ::program)

(defun fn-pinv-host-issue-plan (received observed-ml ed ml invitations
                                         snapshots)
  (declare (xargs :mode :program))
  (fn-pinv-issue-plan received observed-ml ed ml invitations snapshots))

(definterface fn-pinv-host-issue-plan
  :class ::program)

(defun fn-pinv-host-accept-step (sequence txid generation received observed-ml
                                          ed ml snapshots)
  (declare (xargs :mode :program))
  (fn-pinv-accept-step sequence txid generation received observed-ml ed ml
                       snapshots))

(definterface fn-pinv-host-accept-step
  :class ::program)

(defun fn-pinv-host-confirm-step (sequence txid generation received observed-ml
                                           ed ml invitations snapshots)
  (declare (xargs :mode :program))
  (fn-pinv-confirm-step sequence txid generation received observed-ml ed ml
                        invitations snapshots))

(definterface fn-pinv-host-confirm-step
  :class ::program)

(defun fn-pinv-host-invitation-source (date-ms nonce principal token keys name
                                               path groups host port
                                               inviter-host inviter-port)
  (declare (xargs :mode :program))
  (fn-pinv-invitation-source date-ms nonce principal token keys name path
                             groups host port inviter-host inviter-port))

(definterface fn-pinv-host-invitation-source
  :class ::program)

; PRF-160: the accept's plan over the invitation and the live peers table:
; (:configure DELTAS) configures the inviter as a peer before the enrolment.
(defun fn-pinv-host-accept-record-plan (received observed-ml ed ml snapshots
                                                 peers)
  (declare (xargs :mode :program))
  (fn-pinv-accept-record-plan received observed-ml ed ml snapshots peers))

 ; PKT497: committed adoption receipt decides a crash retry in ACL2.
(defun fn-par-host-accept-record-plan (received observed-ml ed ml snapshots
                                             peers ident generation)
  (declare (xargs :mode :logic :guard t))
  (fn-par-accept-record-plan received observed-ml ed ml snapshots peers ident generation))

(definterface fn-par-host-accept-record-plan
  :class :common-lisp-compliant
  :delegates fn-par-accept-record-plan)

(defun fn-pinv-host-acceptance-source (date-ms received observed-ml ed ml
                                               principal token keys path
                                               reachable)
  (declare (xargs :mode :program))
  (fn-pinv-acceptance-source date-ms received observed-ml ed ml principal token
                             keys path reachable))

(definterface fn-pinv-host-acceptance-source
  :class ::program)

(defun fn-pinv-host-genesis-principal (ed ml token)
  (declare (xargs :mode :program))
  (fn-pinv-genesis-principal ed ml token))

(definterface fn-pinv-host-genesis-principal
  :class ::program)

(defun fn-pinv-host-request-encode (kind received)
  (declare (xargs :mode :program))
  (fn-pinv-request-encode kind received))

(definterface fn-pinv-host-request-encode
  :class ::program)

(defun fn-pinv-host-request-decode (kind octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-pinv-request-decode kind octets))

(definterface fn-pinv-host-request-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(defun fn-pinv-host-kind (verb)
  (declare (xargs :mode :program))
  (cond ((equal verb :issue) *fn-pinv-issue-kind*)
        ((equal verb :accept) *fn-pinv-accept-kind*)
        ((equal verb :confirm) *fn-pinv-confirm-kind*)
        (t nil)))

(definterface fn-pinv-host-kind
  :class ::program)

; The live owner's invitations slot and its staging step for one delta.
(defun fn-pinv-host-owner-invitations (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-cfg-invitations (fn-cfg-value (fn-owner-config state)))))

(definterface fn-pinv-host-owner-invitations
  :class ::program)

(defun fn-pinv-host-owner-reconfigure (id delta fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (fn-owner-reconfigure-deltas id (list delta) fn-arena state))

; PRF-124: the confirm's plan over both documents and the live peers table,
; and its record's deltas (the consumption and the peer, one record).
(defun fn-pinv-host-confirm-record-plan (received invitation observed-ml ed ml
                                                  invitations snapshots peers)
  (declare (xargs :mode :program))
  (fn-pinv-confirm-record-plan received invitation observed-ml ed ml
                               invitations snapshots peers))

(definterface fn-pinv-host-confirm-record-plan
  :class ::program)

(defun fn-pinv-host-owner-peers (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-cfg-peers (fn-cfg-value (fn-owner-config state)))))

(definterface fn-pinv-host-owner-peers
  :class ::program)

(defun fn-pinv-host-owner-reconfigure-deltas (id deltas fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (fn-owner-reconfigure-deltas id deltas fn-arena state))

(defun fn-pinv-host-confirm-request-encode (acceptance invitation)
  (declare (xargs :mode :program))
  (fn-pinv-confirm-request-encode acceptance invitation))

(definterface fn-pinv-host-confirm-request-encode
  :class ::program)

(defun fn-pinv-host-confirm-request-decode (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-pinv-confirm-request-decode octets))

(definterface fn-pinv-host-confirm-request-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(defun fn-native-operator-host-result-peering-words (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-peering-words result))

(definterface fn-native-operator-host-result-peering-words
  :class ::program)

(defun fn-native-operator-host-result-peering-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-peering-control-path-octets result))

(definterface fn-native-operator-host-result-peering-control-path-octets
  :class ::program)

;; PKT-221: the login-binding reload (kind 14).
(defun fn-pinv-host-bindings-request-encode ()
  (declare (xargs :mode :program))
  (fn-pinv-bindings-request-encode))

(definterface fn-pinv-host-bindings-request-encode
  :class ::program)

(defun fn-pinv-host-bindings-request-decode (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-pinv-bindings-request-decode octets))

(definterface fn-pinv-host-bindings-request-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

;; PRF-166 (PKT-325): `keys redecide MSGID' (kind 12) and its operator words.
(defun fn-pinv-host-redecide-request-encode (msgid)
  (declare (xargs :mode :program))
  (fn-pinv-redecide-request-encode msgid))

(definterface fn-pinv-host-redecide-request-encode
  :class ::program)

(defun fn-pinv-host-redecide-request-decode (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-pinv-redecide-request-decode octets))

(definterface fn-pinv-host-redecide-request-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(defun fn-native-operator-host-result-keys-msgid-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-keys-msgid-octets result))

(definterface fn-native-operator-host-result-keys-msgid-octets
  :class ::program)

(defun fn-native-operator-host-result-keys-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-keys-control-path-octets result))

(definterface fn-native-operator-host-result-keys-control-path-octets
  :class ::program)
