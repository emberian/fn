; ACL2-facing boundary for native hybrid signing and verification.
(in-package "ACL2")
(include-book "../books/hybrid-store")
(include-book "../books/hybrid-carrier")

(defun fn-hsig-host-received-carrier-plan (received)
  (declare (xargs :mode :program))
  (fn-hc-received-plan received))

(defun fn-hsig-host-render-carrier (source principal keys signatures)
  (declare (xargs :mode :program))
  (fn-hc-render-at-most *fn-article-max-octets*
                        source principal keys signatures))

(defun fn-hsig-host-preimage (principal keys source)
  (declare (xargs :mode :program))
  (if (fn-hsig-subject-p principal keys source)
      (fn-hsig-signed-preimage principal keys source)
    nil))

(defun fn-hsig-host-max-source-octets ()
  (declare (xargs :mode :program))
  *fn-article-max-octets*)

(defun fn-hsig-host-max-received-octets ()
  (declare (xargs :mode :program))
  *fn-article-max-octets*)

(defun fn-hsig-host-authorize
    (principal keys source signatures observed-ml-key ed ml)
  (declare (xargs :mode :program))
  (fn-hsig-authorize principal keys source signatures observed-ml-key ed ml))

(defun fn-hsig-host-keyring-event
    (sequence txid generation keyring-generation principal keys)
  (declare (xargs :mode :program))
  (fn-hsig-keyring-event sequence txid generation keyring-generation
                         principal keys))

(defun fn-hsig-host-keyring-snapshot-value (snapshot)
  (declare (xargs :mode :program))
  (fn-hsig-keyring-snapshot-value snapshot))

(defun fn-hsig-host-keyring-snapshot-octets (snapshot)
  (declare (xargs :mode :program))
  (if (fn-stxk-p snapshot) (fn-stxk-snapshot snapshot) nil))

(defun fn-hsig-host-authored-source-fields (source)
  (declare (xargs :mode :program))
  (fn-hsig-authored-source-fields source))

(defun fn-hsig-host-authorized-article-event
    (sequence txid generation keyring-generation enrolled-snapshot
              msgid content-subject
              article-record principal keys source signatures observed-ml-key
              ed ml)
  (declare (xargs :mode :program))
  (fn-hsig-authorized-article-event
   sequence txid generation keyring-generation enrolled-snapshot
   msgid content-subject
   article-record principal keys source signatures observed-ml-key ed ml))

(defun fn-hsig-host-authorized-submission-event
    (sequence txid generation keyring-generation enrolled-snapshot
              msgid source groups obligation-id content-subject
              release-evidence charge principal keys signatures observed-ml-key
              ed ml observation)
  (declare (xargs :mode :program))
  (fn-hsig-authorized-submission-event
   sequence txid generation keyring-generation enrolled-snapshot
   msgid source groups obligation-id content-subject release-evidence charge
   principal keys signatures observed-ml-key ed ml observation))
