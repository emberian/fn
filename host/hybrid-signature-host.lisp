; ACL2-facing boundary for native hybrid signing and verification.
(in-package "ACL2")
(include-book "../books/hybrid-store")
(include-book "../books/hybrid-lifecycle")
(include-book "../books/hybrid-carrier")

(defun fn-hsig-host-received-carrier-plan (received)
  (declare (xargs :mode :program))
  (fn-hc-received-plan received))

(defun fn-hsig-host-render-carrier (source principal keys signatures)
  (declare (xargs :mode :program))
  (fn-hc-render-at-most *fn-article-max-octets*
                        source principal keys signatures))

; The carrier version is ACL2's (`fn-hsig-source-version'): v1 up to the
; u16's 65535 source octets, v2 above.  A received carrier was decoded at
; that same version (`fn-hc-received-plan'), so the host never classifies.
(defun fn-hsig-host-preimage (principal keys source)
  (declare (xargs :mode :program))
  (let ((version (fn-hsig-source-version source)))
    (if (fn-hsig-subject-at-p version principal keys source)
        (fn-hsig-signed-preimage-at version principal keys source)
      nil)))

; The widest authored source a signer or author request may hand ACL2: the
; v2 carrier's u32 length (a codec width, D27).  Whether a node accepts the
; article is the store profile's article bound, decided at injection.
(defun fn-hsig-host-max-source-octets ()
  (declare (xargs :mode :program))
  *fn-hsig-v2-max-source*)

(defun fn-hsig-host-max-received-octets ()
  (declare (xargs :mode :program))
  *fn-article-max-octets*)

(defun fn-hsig-host-authored-source-id (source)
  (declare (xargs :mode :program))
  (fn-hsig-authored-source-id source))

(defun fn-hsig-host-authorize
    (principal keys source signatures observed-ml-key ed ml)
  (declare (xargs :mode :program))
  (fn-hsig-authorize-at (fn-hsig-source-version source)
                        principal keys source signatures observed-ml-key ed ml))

(defun fn-hsig-host-keyring-event
    (sequence txid generation keyring-generation principal keys)
  (declare (xargs :mode :program))
  (fn-hsig-keyring-event sequence txid generation keyring-generation
                         principal keys))

(defun fn-hl-host-enroll-event
    (sequence txid generation keyring-generation principal keys snapshots)
  (declare (xargs :mode :program))
  (fn-hl-enroll-event sequence txid generation keyring-generation
                      principal keys snapshots))

(defun fn-hl-host-revoke-event
    (sequence txid generation keyring-generation principal snapshots)
  (declare (xargs :mode :program))
  (fn-hl-revoke-event sequence txid generation keyring-generation
                      principal snapshots))

(defun fn-hl-host-store-history (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((snapshots
         (fn-sn-keyring-snapshots (f-get-global 'fn-store-sn state))))
    (value (fn-hl-history-rows snapshots snapshots))))

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

(defun fn-hsig-host-authorized-carried-submission-event
    (sequence txid generation keyring-generation enrolled-snapshot
              msgid source received groups obligation-id content-subject
              release-evidence charge principal keys signatures observed-ml-key
              ed ml observation)
  (declare (xargs :mode :program))
  (fn-hsig-authorized-carried-submission-event
   sequence txid generation keyring-generation enrolled-snapshot
   msgid source received groups obligation-id content-subject
   release-evidence charge principal keys signatures observed-ml-key
   ed ml observation))
