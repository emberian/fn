;;; Peering invitations: `peer genesis|invite|accept|confirm' (PRF-097).
;;;
;;; I/O only.  This file reads key files and documents, draws the nonce from
;;; the OS CSPRNG, reads the wall clock, makes the two primitive signature
;;; observations and moves octets over the control socket.  What a document
;;; says, whether it binds its keys, which configuration row it writes and
;;; which enrolment follows are books/peer-invite.lisp's, through
;;; host/peer-invite-host.lisp.  The owner's three handlers wrap the hybrid
;;; control handler (host/native/hybrid-control.lisp) instead of editing it.
;;;
;;; A key directory holds principal.bin (32 octets, written by `peer
;;; genesis'), token.bin (the genesis token, at most 64 octets),
;;; ed-public.bin (32), ed-secret.bin (seed || public, 64), ml-public.pem and
;;; ml-private.pem.

(in-package "ACL2")

(defconstant +fnn-pinv-nonce-octets+ 16)
(defconstant +fnn-pinv-token-octets+ 16)
(defconstant +fnn-pinv-max-token-octets+ 64)

(defun fnn-pinv-path (directory name) (fnn-join directory name))

(defun fnn-pinv-read-document (path)
  (fnn-octet-list
   (fnn-read-regular-bounded path (fnn-core 'fn-hsig-host-max-received-octets))))

(defun fnn-pinv-public-keys (directory)
  "The key set (Ed25519 and ML-DSA-65 public keys) a key directory holds."
  (list (cons :ed25519 (fnn-hsig-command-read-exact
                        (fnn-pinv-path directory "ed-public.bin") 32
                        "Ed25519 public key"))
        (cons :ml-dsa-65 (coerce (fnn-hsig-ml-dsa-65-public-key
                                  (fnn-pinv-path directory "ml-public.pem"))
                                 'list))))

(defun fnn-pinv-token (directory)
  (fnn-octet-list (fnn-read-regular-bounded
                   (fnn-pinv-path directory "token.bin")
                   +fnn-pinv-max-token-octets+)))

(defun fnn-pinv-principal (directory)
  (fnn-hsig-command-read-exact (fnn-pinv-path directory "principal.bin") 32
                               "principal"))

(defun fnn-pinv-write-new (path octets)
  (with-open-file (stream path :direction :output
                               :element-type '(unsigned-byte 8)
                               :if-exists :error :if-does-not-exist :create)
    (write-sequence (fnn-octets octets) stream)
    (finish-output stream)))

(defun fnn-pinv-sign (directory source principal keys)
  "Sign SOURCE with DIRECTORY's secret halves; ACL2 builds the preimage and
renders the carrier, and the result is checked like any received carrier."
  (let ((preimage (fnn-core 'fn-hsig-host-preimage principal keys source)))
    (unless (and preimage (consp preimage))
      (fnn-refuse "the document is outside the hybrid signing profile"))
    (let* ((ed-secret (fnn-hsig-command-read-exact
                       (fnn-pinv-path directory "ed-secret.bin") 64
                       "Ed25519 secret key"))
           (ed-signature (fnn-hsig-ed25519-sign (fnn-octets ed-secret) preimage))
           (ml-signature (fnn-hsig-ml-dsa-65-sign
                          (fnn-pinv-path directory "ml-private.pem") preimage))
           (signatures (list (cons :ed25519 (fnn-octet-list ed-signature))
                             (cons :ml-dsa-65 (fnn-octet-list ml-signature))))
           (rendered (fnn-core 'fn-hsig-host-render-carrier
                               source principal keys signatures)))
      (unless (and (fnn-octet-list-p rendered) (consp rendered))
        (fnn-refuse "the document is outside the portable FN-Authorship profile"))
      rendered)))

(defun fnn-pinv-observe (received)
  "The two primitive observations over the carrier's own key set, as
(observed-ml-key ed-observation ml-observation), or NIL when ACL2 finds no
carrier to observe."
  (let ((subject (fnn-core 'fn-pinv-host-observation-subject received)))
    (when (eq (first subject) :observe)
      (destructuring-bind (tag principal keys preimage signatures) subject
        (declare (ignore tag principal))
        (let* ((observations (fnn-hsig-observe-raw (cdr (first keys))
                                                   (cdr (second keys))
                                                   preimage signatures))
               (ml (second observations))
               (observed (and (consp ml) (second ml))))
          (list (and observed (coerce observed 'list))
                (first observations)
                (if (consp ml) (first ml) ml)))))))

;;; ---------------------------------------------------------------------
;;; The owner's handlers: each runs under the owner mutex.

(defun fnn-pinv-refused (verb plan)
  (fnn-err "peer ~(~a~) refused: ~(~a~)" verb (second plan))
  :refused)

(defun fnn-pinv-owner-issue (service received)
  (fnn-owner-serialized
   service nil
   (lambda ()
     (let ((observed (fnn-pinv-observe received)))
       (unless observed
         (return-from fnn-pinv-owner-issue
           (fnn-pinv-refused :invite '(:refused :carrier))))
       (let ((plan (apply #'fnn-core 'fn-pinv-host-issue-plan received
                          (append observed
                                  (list (fnn-owner-core
                                         'fn-pinv-host-owner-invitations))))))
         (if (not (eq (first plan) :issue))
             (fnn-pinv-refused :invite plan)
           (fnn-owner-live-reconfigure-locked
            service
            (lambda (cid)
              (fnn-owner-action 'fn-pinv-host-owner-reconfigure cid
                                (second plan))))))))))

(defun fnn-pinv-owner-accept (service received)
  "PRF-160: an invitation that names the inviter's address configures the
inviter as a peer in one configuration record (books/peer-invite.lisp
fn-pinv-accept-record-plan); the enrolment follows it."
  (fnn-owner-serialized
   service nil
   (lambda ()
     (let ((observed (fnn-pinv-observe received)))
       (unless observed
         (return-from fnn-pinv-owner-accept
           (fnn-pinv-refused :accept '(:refused :carrier))))
       (let ((plan (apply #'fnn-core 'fn-pinv-host-accept-record-plan received
                          (append observed
                                  (list (fnn-owner-core
                                         'fn-owner-hybrid-snapshots)
                                        (fnn-owner-core
                                         'fn-pinv-host-owner-peers))))))
         (case (first plan)
           (:configure
            (let ((published
                    (fnn-owner-live-reconfigure-locked
                     service
                     (lambda (cid)
                       (fnn-owner-action 'fn-pinv-host-owner-reconfigure-deltas
                                         cid (second plan))))))
              (unless (eq published :accepted)
                (return-from fnn-pinv-owner-accept published))
              ;; The model's crash point between the configuration record and
              ;; the kind-3 record (fn-pinv-accept-record-fold-configures-the-
              ;; inviter); a developer image dies here on request.
              (when (fnn-developer-selector "FN_PEER_TEST_STOP_AFTER_CONFIGURE")
                (fnn-err "peer accept: developer stop after the peer record")
                (sb-ext:exit :code 137 :abort t))))
           (:enrol nil)
           (t (return-from fnn-pinv-owner-accept
                (fnn-pinv-refused :accept plan)))))
       (destructuring-bind (sequence txid generation)
           (fnn-owner-core 'fn-owner-next-store-coordinates)
         (let ((step (apply #'fnn-core 'fn-pinv-host-accept-step
                            sequence txid generation received
                            (append observed
                                    (list (fnn-owner-core
                                           'fn-owner-hybrid-snapshots))))))
           (if (not (eq (first step) :enrol))
               (fnn-pinv-refused :accept step)
             (progn (fnn-owner-identity-commit service (second step))
                    :accepted))))))))

(defun fnn-pinv-owner-enrol-confirmed (service received observed)
  "The enrolment the configuration now permits: ACL2 asks the invitations
slot again, so only a row consumed by exactly this acceptance yields one."
  (destructuring-bind (sequence txid generation)
      (fnn-owner-core 'fn-owner-next-store-coordinates)
    (let ((step (apply #'fnn-core 'fn-pinv-host-confirm-step
                       sequence txid generation received
                       (append observed
                               (list (fnn-owner-core
                                      'fn-pinv-host-owner-invitations)
                                     (fnn-owner-core
                                      'fn-owner-hybrid-snapshots))))))
      (if (not (eq (first step) :enrol))
          (fnn-pinv-refused :confirm step)
        (progn (fnn-owner-identity-commit service (second step))
               :accepted)))))

(defun fnn-pinv-owner-confirm (service received invitation)
  "PRF-124: one configuration record consumes the invitation and configures
the invitee as a peer (books/peer-invite.lisp fn-pinv-confirm-record-plan);
the enrolment follows it."
  (fnn-owner-serialized
   service nil
   (lambda ()
     (let ((observed (fnn-pinv-observe received)))
       (unless observed
         (return-from fnn-pinv-owner-confirm
           (fnn-pinv-refused :confirm '(:refused :carrier))))
       (let ((plan (apply #'fnn-core 'fn-pinv-host-confirm-record-plan
                          received invitation
                          (append observed
                                  (list (fnn-owner-core
                                         'fn-pinv-host-owner-invitations)
                                        (fnn-owner-core
                                         'fn-owner-hybrid-snapshots)
                                        (fnn-owner-core
                                         'fn-pinv-host-owner-peers))))))
         (case (first plan)
           (:configure
            (let ((published
                    (fnn-owner-live-reconfigure-locked
                     service
                     (lambda (cid)
                       (fnn-owner-action 'fn-pinv-host-owner-reconfigure-deltas
                                         cid (second plan))))))
              (unless (eq published :accepted)
                (return-from fnn-pinv-owner-confirm published))
              ;; The model's crash point between the configuration record
              ;; and the kind-3 record (fn-pinv-confirm-record-fold-consumes-
              ;; and-configures); a developer image dies here on request.
              (when (fnn-developer-selector "FN_PEER_TEST_STOP_AFTER_CONSUME")
                (fnn-err "peer confirm: developer stop after consumption")
                (sb-ext:exit :code 137 :abort t))
              (fnn-pinv-owner-enrol-confirmed service received observed)))
           (:enrol (fnn-pinv-owner-enrol-confirmed service received observed))
           (t (fnn-pinv-refused :confirm plan))))))))

(defvar *fnn-pinv-next-handler* *fnn-hybrid-control-handler*)

(defun fnn-pinv-control-handle (service frame)
  (let* ((octets (and (typep frame 'fnn-octets) (fnn-octet-list frame)))
         (issue (and octets (fnn-core 'fn-pinv-host-request-decode
                                      (fnn-core 'fn-pinv-host-kind :issue)
                                      octets)))
         (accept (and octets (not issue)
                      (fnn-core 'fn-pinv-host-request-decode
                                (fnn-core 'fn-pinv-host-kind :accept) octets)))
         (confirm (and octets (not issue) (not accept)
                       (fnn-core 'fn-pinv-host-confirm-request-decode
                                 octets))))
    (cond (issue (fnn-pinv-owner-issue service issue))
          (accept (fnn-pinv-owner-accept service accept))
          (confirm (fnn-pinv-owner-confirm service (first confirm)
                                           (second confirm)))
          (*fnn-pinv-next-handler*
           (funcall *fnn-pinv-next-handler* service frame))
          (t nil))))

(setq *fnn-hybrid-control-handler* #'fnn-pinv-control-handle)

;;; ---------------------------------------------------------------------
;;; The operator's side.

(defun fnn-pinv-send (control-path verb received)
  (let ((request (fnn-core 'fn-pinv-host-request-encode
                           (fnn-core 'fn-pinv-host-kind verb) received)))
    (fnn-hybrid-control-send control-path request)))

(defun fnn-pinv-status-code (status)
  (fnn-core 'fn-native-control-host-status-exit-code status))

(defun fnn-pinv-text (word) (fnn-ascii-octet-list word))

(defun fnn-pinv-genesis (directory)
  "Write principal.bin: ACL2's genesis identity of the directory's two public
keys and its token (a fresh CSPRNG token when token.bin is absent)."
  (let ((token-path (fnn-pinv-path directory "token.bin"))
        (principal-path (fnn-pinv-path directory "principal.bin")))
    (unless (probe-file token-path)
      (fnn-pinv-write-new token-path
                          (fnn-octet-list
                           (fnn-anchor-csprng-nonce +fnn-pinv-token-octets+))))
    (let* ((keys (fnn-pinv-public-keys directory))
           (principal (fnn-core 'fn-pinv-host-genesis-principal
                                (cdr (first keys)) (cdr (second keys))
                                (fnn-pinv-token directory))))
      (unless (and (fnn-octet-list-p principal) (= (length principal) 32))
        (fnn-refuse "ACL2 derived no genesis principal from these keys"))
      (fnn-pinv-write-new principal-path principal)
      (fnn-out "principal ~a" (fnn-hex principal))
      +fnn-exit-ok+)))

(defun fnn-pinv-invite (control-path words)
  (destructuring-bind (name groups host port path directory out inviter-host
                       inviter-port) words
    (let* ((keys (fnn-pinv-public-keys directory))
           (principal (fnn-pinv-principal directory))
           (nonce (fnn-octet-list
                   (fnn-anchor-csprng-nonce +fnn-pinv-nonce-octets+)))
           (source (fnn-core 'fn-pinv-host-invitation-source
                             (fnn-owner-wall-milliseconds) nonce principal
                             (fnn-pinv-token directory) keys
                             (fnn-pinv-text name) (fnn-pinv-text path)
                             (fnn-pinv-text groups) (fnn-pinv-text host)
                             (fnn-pinv-text port) (fnn-pinv-text inviter-host)
                             (fnn-pinv-text inviter-port))))
      (unless (and (fnn-octet-list-p source) (consp source))
        (fnn-refuse "ACL2 refused the invitation's words"))
      (let* ((signed (fnn-pinv-sign directory source principal keys))
             (code (fnn-pinv-status-code
                    (fnn-pinv-send control-path :issue signed))))
        ;; The invitation is recorded before it exists anywhere else.
        (when (= code +fnn-exit-ok+)
          (fnn-pinv-write-new out signed)
          (fnn-out "invitation nonce=~a out=~a" (fnn-hex nonce) out))
        code))))

(defun fnn-pinv-accept (control-path words)
  (destructuring-bind (file directory path reachable out) words
    (let* ((received (fnn-pinv-read-document file))
           (code (fnn-pinv-status-code
                  (fnn-pinv-send control-path :accept received))))
      (if (/= code +fnn-exit-ok+)
          code
        (let* ((observed (fnn-pinv-observe received))
               (source (and observed
                            (apply #'fnn-core 'fn-pinv-host-acceptance-source
                                   (fnn-owner-wall-milliseconds) received
                                   (append observed
                                           (list (fnn-pinv-principal directory)
                                                 (fnn-pinv-token directory)
                                                 (fnn-pinv-public-keys directory)
                                                 (fnn-pinv-text path)
                                                 (fnn-pinv-text reachable)))))))
          (unless (and (fnn-octet-list-p source) (consp source))
            (fnn-refuse "ACL2 refused the acceptance's words"))
          (let ((signed (fnn-pinv-sign directory source
                                       (fnn-pinv-principal directory)
                                       (fnn-pinv-public-keys directory))))
            (fnn-pinv-write-new out signed)
            (fnn-out "acceptance out=~a" out)
            +fnn-exit-ok+))))))

(defun fnn-pinv-confirm (control-path words)
  "`peer confirm ACCEPTANCE INVITATION': both documents go to the owner."
  (let ((request (fnn-core 'fn-pinv-host-confirm-request-encode
                           (fnn-pinv-read-document (first words))
                           (fnn-pinv-read-document (second words)))))
    (when (eq request :bad)
      (fnn-refuse "ACL2 refused the confirm request's documents"))
    (fnn-pinv-status-code (fnn-hybrid-control-send control-path request))))

(defun fnn-pinv-execute (result)
  "Execute an accepted `peer genesis|invite|accept|confirm' plan."
  (let* ((words (fnn-core 'fn-native-operator-host-result-peering-words result))
         (verb (first words))
         (control (fnn-core
                   'fn-native-operator-host-result-peering-control-path-octets
                   result))
         (control-path (and (fnn-octet-list-p control) (consp control)
                            (fnn-octets-string (fnn-octets control)))))
    (handler-case
        (let ((code
                (cond ((equal verb "genesis") (fnn-pinv-genesis (second words)))
                      ((null control-path)
                       (fnn-refuse "the configuration names no control socket"))
                      ((equal verb "invite")
                       (fnn-pinv-invite control-path (rest words)))
                      ((equal verb "accept")
                       (fnn-pinv-accept control-path (rest words)))
                      ((equal verb "confirm")
                       (fnn-pinv-confirm control-path (rest words)))
                      (t (fnn-fault "ACL2 returned an unknown peering verb")))))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code) "peer")
          code)
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                    "peer" condition)
          code)))))
