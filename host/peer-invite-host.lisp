; ACL2-facing boundary for the peering verbs (PRF-097, books/peer-invite.lisp).
; Every decision is the book's; these wrappers only name it for the image.
(in-package "ACL2")
(include-book "../books/peer-invite")
(include-book "../books/peer-invite-retry")
(include-book "../books/definterface")
(include-book "owner-host")

(include-book "../books/entries-peer-invite-host")

(definterface fn-pinv-host-observation-subject
  :class ::program)

(definterface fn-pinv-host-issue-plan
  :class ::program)

(definterface fn-pinv-host-accept-step
  :class ::program)

(definterface fn-pinv-host-confirm-step
  :class ::program)

(definterface fn-pinv-host-invitation-source
  :class ::program)

 ; PKT497: committed adoption receipt decides a crash retry in ACL2.

(definterface fn-par-host-accept-record-plan
  :class :common-lisp-compliant
  :delegates fn-par-accept-record-plan)

(definterface fn-pinv-host-acceptance-source
  :class ::program)

(definterface fn-pinv-host-genesis-principal
  :class ::program)

(definterface fn-pinv-host-request-encode
  :class ::program)

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

(definterface fn-pinv-host-confirm-request-encode
  :class ::program)

(definterface fn-pinv-host-confirm-request-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-native-operator-host-result-peering-words
  :class ::program)

(definterface fn-native-operator-host-result-peering-control-path-octets
  :class ::program)

;; PKT-221: the login-binding reload (kind 14).

(definterface fn-pinv-host-bindings-request-encode
  :class ::program)

(definterface fn-pinv-host-bindings-request-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

;; PRF-166 (PKT-325): `keys redecide MSGID' (kind 12) and its operator words.

(definterface fn-pinv-host-redecide-request-encode
  :class ::program)

(definterface fn-pinv-host-redecide-request-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-native-operator-host-result-keys-msgid-octets
  :class ::program)

(definterface fn-native-operator-host-result-keys-control-path-octets
  :class ::program)
