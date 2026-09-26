; ACL2-facing boundary for the peering verbs (PRF-097, books/peer-invite.lisp).
; Every decision is the book's; these wrappers only name it for the image.
(in-package "ACL2")
(include-book "../books/peer-invite")

(defun fn-pinv-host-observation-subject (received)
  (declare (xargs :mode :program))
  (fn-pinv-observation-subject received))

(defun fn-pinv-host-issue-plan (received observed-ml ed ml invitations)
  (declare (xargs :mode :program))
  (fn-pinv-issue-plan received observed-ml ed ml invitations))

(defun fn-pinv-host-accept-step (sequence txid generation received observed-ml
                                          ed ml snapshots)
  (declare (xargs :mode :program))
  (fn-pinv-accept-step sequence txid generation received observed-ml ed ml
                       snapshots))

(defun fn-pinv-host-accept-plan (received observed-ml ed ml)
  (declare (xargs :mode :program))
  (fn-pinv-accept-plan received observed-ml ed ml))

(defun fn-pinv-host-confirm-plan (received observed-ml ed ml invitations
                                           snapshots)
  (declare (xargs :mode :program))
  (fn-pinv-confirm-plan received observed-ml ed ml invitations snapshots))

(defun fn-pinv-host-confirm-step (sequence txid generation received observed-ml
                                           ed ml invitations snapshots)
  (declare (xargs :mode :program))
  (fn-pinv-confirm-step sequence txid generation received observed-ml ed ml
                        invitations snapshots))

(defun fn-pinv-host-invitation-source (date-ms nonce principal token keys name
                                               path groups host port
                                               inviter-host inviter-port)
  (declare (xargs :mode :program))
  (fn-pinv-invitation-source date-ms nonce principal token keys name path
                             groups host port inviter-host inviter-port))

; PRF-160: the accept's plan over the invitation and the live peers table:
; (:configure DELTAS) configures the inviter as a peer before the enrolment.
(defun fn-pinv-host-accept-record-plan (received observed-ml ed ml snapshots
                                                 peers)
  (declare (xargs :mode :program))
  (fn-pinv-accept-record-plan received observed-ml ed ml snapshots peers))

(defun fn-pinv-host-acceptance-source (date-ms received observed-ml ed ml
                                               principal token keys path
                                               reachable)
  (declare (xargs :mode :program))
  (fn-pinv-acceptance-source date-ms received observed-ml ed ml principal token
                             keys path reachable))

(defun fn-pinv-host-genesis-principal (ed ml token)
  (declare (xargs :mode :program))
  (fn-pinv-genesis-principal ed ml token))

(defun fn-pinv-host-request-encode (kind received)
  (declare (xargs :mode :program))
  (fn-pinv-request-encode kind received))

(defun fn-pinv-host-request-decode (kind octets)
  (declare (xargs :mode :program))
  (fn-pinv-request-decode kind octets))

(defun fn-pinv-host-kind (verb)
  (declare (xargs :mode :program))
  (cond ((equal verb :issue) *fn-pinv-issue-kind*)
        ((equal verb :accept) *fn-pinv-accept-kind*)
        ((equal verb :confirm) *fn-pinv-confirm-kind*)
        (t nil)))

; The live owner's invitations slot and its staging step for one delta.
(defun fn-pinv-host-owner-invitations (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-cfg-invitations (fn-cfg-value (fn-owner-config state)))))

(defun fn-pinv-host-owner-reconfigure (id delta state)
  (declare (xargs :stobjs state :mode :program))
  (fn-owner-reconfigure-deltas id (list delta) state))

; PRF-124: the confirm's plan over both documents and the live peers table,
; and its record's deltas (the consumption and the peer, one record).
(defun fn-pinv-host-confirm-record-plan (received invitation observed-ml ed ml
                                                  invitations snapshots peers)
  (declare (xargs :mode :program))
  (fn-pinv-confirm-record-plan received invitation observed-ml ed ml
                               invitations snapshots peers))

(defun fn-pinv-host-owner-peers (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-cfg-peers (fn-cfg-value (fn-owner-config state)))))

(defun fn-pinv-host-owner-reconfigure-deltas (id deltas state)
  (declare (xargs :stobjs state :mode :program))
  (fn-owner-reconfigure-deltas id deltas state))

(defun fn-pinv-host-confirm-request-encode (acceptance invitation)
  (declare (xargs :mode :program))
  (fn-pinv-confirm-request-encode acceptance invitation))

(defun fn-pinv-host-confirm-request-decode (octets)
  (declare (xargs :mode :program))
  (fn-pinv-confirm-request-decode octets))

(defun fn-native-operator-host-result-peering-words (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-peering-words result))

(defun fn-native-operator-host-result-peering-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-peering-control-path-octets result))

;; PRF-166 (PKT-325): `keys redecide MSGID' (kind 12) and its operator words.
(defun fn-pinv-host-redecide-request-encode (msgid)
  (declare (xargs :mode :program))
  (fn-pinv-redecide-request-encode msgid))

(defun fn-pinv-host-redecide-request-decode (octets)
  (declare (xargs :mode :program))
  (fn-pinv-redecide-request-decode octets))

(defun fn-native-operator-host-result-keys-msgid-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-keys-msgid-octets result))

(defun fn-native-operator-host-result-keys-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-keys-control-path-octets result))
