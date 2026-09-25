;;; Native primitive boundary for D09's mandatory Ed25519 + ML-DSA-65 profile.
;;; ACL2 supplies the canonical preimage and makes the final conjunction.
;;; Callers supply independent Ed25519 and ML-DSA key material; this file owns
;;; no key derivation, custody, recovery, or authorization policy.

(in-package "ACL2")

(defconstant +fnn-hsig-ed-secret-key-octets+ 64)
(defconstant +fnn-hsig-ed-public-key-octets+ 32)
(defconstant +fnn-hsig-ed-signature-octets+ 64)
(defconstant +fnn-hsig-ml-public-key-octets+ 1952)
(defconstant +fnn-hsig-ml-signature-octets+ 3309)
(defconstant +fnn-hsig-openssl-3-5+ #x30500000)

;;; The preimage bound is ACL2's (fn-hsig-host-max-preimage-octets): the v2
;;; layout over the widest v2 source.  Every message here is an ACL2-produced
;;; preimage, so this refuses only a caller outside that contract.
(defun fnn-hsig-max-message-octets ()
  (fnn-core 'fn-hsig-host-max-preimage-octets))

(define-condition fnn-hsig-error (error)
  ((detail :initarg :detail :reader fnn-hsig-error-detail))
  (:report (lambda (condition stream)
             (format stream "native hybrid signature: ~a"
                     (fnn-hsig-error-detail condition)))))
(define-condition fnn-hsig-unsupported (fnn-hsig-error) ())
(define-condition fnn-hsig-fault (fnn-hsig-error) ())

(defvar *fnn-hsig-openssl-state* :uninitialized)
(defvar *fnn-hsig-openssl-library* nil)
(defvar *fnn-hsig-openssl-version* nil)
(defvar *fnn-hsig-openssl-lock*
  (sb-thread:make-mutex :name "fn ML-DSA provider initialization"))

(sb-alien:define-alien-routine
    ("crypto_sign_detached" fnn-%hsig-ed-sign-detached) sb-alien:int
  (signature (* sb-alien:unsigned-char))
  (signature-length (* sb-alien:unsigned-long-long))
  (message (* sb-alien:unsigned-char))
  (message-length sb-alien:unsigned-long-long)
  (secret-key (* sb-alien:unsigned-char)))
(sb-alien:define-alien-routine ("OpenSSL_version_num" fnn-%hsig-version-num)
    sb-alien:unsigned-long)
(sb-alien:define-alien-routine ("OpenSSL_version" fnn-%hsig-version)
    sb-alien:c-string (selector sb-alien:int))
(sb-alien:define-alien-routine ("BIO_new_file" fnn-%hsig-bio-new-file)
    (* t) (filename sb-alien:c-string) (mode sb-alien:c-string))
(sb-alien:define-alien-routine ("BIO_free" fnn-%hsig-bio-free)
    sb-alien:int (bio (* t)))
(sb-alien:define-alien-routine
    ("PEM_read_bio_PrivateKey" fnn-%hsig-read-private-key) (* t)
  (bio (* t)) (key (* t)) (password-callback (* t)) (userdata (* t)))
(sb-alien:define-alien-routine
    ("PEM_read_bio_PUBKEY" fnn-%hsig-read-public-key) (* t)
  (bio (* t)) (key (* t)) (password-callback (* t)) (userdata (* t)))
(sb-alien:define-alien-routine ("EVP_PKEY_free" fnn-%hsig-pkey-free)
    sb-alien:void (key (* t)))
(sb-alien:define-alien-routine
    ("EVP_PKEY_new_raw_public_key_ex" fnn-%hsig-new-raw-public-key) (* t)
  (library-context (* t)) (keytype sb-alien:c-string)
  (properties sb-alien:c-string) (key (* sb-alien:unsigned-char))
  (key-length sb-alien:unsigned-long))
(sb-alien:define-alien-routine
    ("EVP_PKEY_get_raw_public_key" fnn-%hsig-get-raw-public-key) sb-alien:int
  (key (* t)) (output (* sb-alien:unsigned-char))
  (output-length (* sb-alien:unsigned-long)))
(sb-alien:define-alien-routine
    ("EVP_PKEY_CTX_new_from_pkey" fnn-%hsig-context-new) (* t)
  (library-context (* t)) (key (* t)) (properties sb-alien:c-string))
(sb-alien:define-alien-routine ("EVP_PKEY_CTX_free" fnn-%hsig-context-free)
    sb-alien:void (context (* t)))
(sb-alien:define-alien-routine ("EVP_SIGNATURE_fetch" fnn-%hsig-fetch)
    (* t) (library-context (* t)) (algorithm sb-alien:c-string)
    (properties sb-alien:c-string))
(sb-alien:define-alien-routine ("EVP_SIGNATURE_free" fnn-%hsig-signature-free)
    sb-alien:void (signature (* t)))
(sb-alien:define-alien-routine
    ("EVP_PKEY_sign_message_init" fnn-%hsig-sign-init) sb-alien:int
  (context (* t)) (algorithm (* t)) (parameters (* t)))
(sb-alien:define-alien-routine
    ("EVP_PKEY_verify_message_init" fnn-%hsig-verify-init) sb-alien:int
  (context (* t)) (algorithm (* t)) (parameters (* t)))
(sb-alien:define-alien-routine ("EVP_PKEY_sign" fnn-%hsig-sign) sb-alien:int
  (context (* t)) (signature (* sb-alien:unsigned-char))
  (signature-length (* sb-alien:unsigned-long))
  (message (* sb-alien:unsigned-char)) (message-length sb-alien:unsigned-long))
(sb-alien:define-alien-routine ("EVP_PKEY_verify" fnn-%hsig-verify) sb-alien:int
  (context (* t)) (signature (* sb-alien:unsigned-char))
  (signature-length sb-alien:unsigned-long)
  (message (* sb-alien:unsigned-char)) (message-length sb-alien:unsigned-long))

(defun fnn-hsig-null () (sb-alien:sap-alien (sb-sys:int-sap 0) (* t)))
(defun fnn-hsig-null-p (pointer) (sb-alien:null-alien pointer))
(defun fnn-hsig-pointer (vector)
  (sb-alien:sap-alien (sb-sys:vector-sap vector) (* sb-alien:unsigned-char)))

(defun fnn-hsig-initialize ()
  "Require the process-wide TLS OpenSSL pair to be >= 3.5 with ML-DSA-65."
  (fnn-crypto-initialize)
  (sb-thread:with-mutex (*fnn-hsig-openssl-lock*)
    (case *fnn-hsig-openssl-state*
      (:ready t)
      (:unsupported
       (error 'fnn-hsig-unsupported :detail "ML-DSA-65 is unavailable"))
      (t
       (handler-case
             (progn
               ;; One loader owns libcrypto/libssl.  This prevents TLS binding
               ;; OpenSSL 3.0 while the signature FFI resolves into a later
               ;; independently loaded library with the same global symbols.
               (unless (fboundp 'fnn-tls-initialize)
                 (error 'fnn-hsig-unsupported
                        :detail "the shared OpenSSL TLS facility is not loaded"))
               (fnn-tls-initialize)
               (unless (>= (fnn-%hsig-version-num) +fnn-hsig-openssl-3-5+)
                 (error 'fnn-hsig-unsupported
                        :detail "OpenSSL 3.5 or newer is required for ML-DSA"))
               (let ((algorithm (fnn-%hsig-fetch (fnn-hsig-null)
                                                  "ML-DSA-65" nil)))
                 (when (fnn-hsig-null-p algorithm)
                   (error 'fnn-hsig-unsupported
                          :detail "the active OpenSSL providers lack ML-DSA-65"))
                 (fnn-%hsig-signature-free algorithm))
               (setq *fnn-hsig-openssl-library* *fnn-tls-libraries*
                     *fnn-hsig-openssl-version* (fnn-%hsig-version 0)
                     *fnn-hsig-openssl-state* :ready)
               t)
           (fnn-hsig-unsupported (condition)
             (setq *fnn-hsig-openssl-state* :unsupported)
             (error condition)))))))

(defun fnn-hsig-reset ()
  (setq *fnn-hsig-openssl-state* :uninitialized
        *fnn-hsig-openssl-library* nil *fnn-hsig-openssl-version* nil)
  t)

(defun fnn-hsig-read-key (path privatep)
  (unless (and (stringp path) (> (length path) 0)
               (not (find (code-char 0) path)))
    (error 'fnn-hsig-fault :detail "a PEM key path is required"))
  (let ((bio (fnn-%hsig-bio-new-file path "rb")))
    (when (fnn-hsig-null-p bio)
      (error 'fnn-hsig-fault :detail (format nil "cannot open key ~a" path)))
    (unwind-protect
           (let* ((callback (sb-alien:cast
                             (sb-alien:alien-callable-function
                              'fnn-%tls-no-password) (* t)))
                  (key (if privatep
                        (fnn-%hsig-read-private-key bio (fnn-hsig-null)
                                                    callback (fnn-hsig-null))
                      (fnn-%hsig-read-public-key bio (fnn-hsig-null)
                                                callback (fnn-hsig-null)))))
           (when (fnn-hsig-null-p key)
             (error 'fnn-hsig-fault
                    :detail (format nil "cannot read unencrypted key ~a" path)))
           key)
      (fnn-%hsig-bio-free bio))))

(defun fnn-hsig-ed25519-sign (secret-key message)
  (fnn-crypto-initialize)
  (let ((key (fnn-crypto-octets secret-key +fnn-hsig-ed-secret-key-octets+
                                "Ed25519 secret key"))
        (text (fnn-crypto-octets message (fnn-hsig-max-message-octets)
                                 "hybrid signed preimage"))
        (signature (make-array +fnn-hsig-ed-signature-octets+
                               :element-type '(unsigned-byte 8))))
    (unless (= (length key) +fnn-hsig-ed-secret-key-octets+)
      (error 'fnn-hsig-fault :detail "Ed25519 secret key is not 64 octets"))
    (sb-alien:with-alien ((actual sb-alien:unsigned-long-long))
      (sb-sys:with-pinned-objects (key text signature)
        (unless (zerop (fnn-%hsig-ed-sign-detached
                        (fnn-hsig-pointer signature) (sb-alien:addr actual)
                        (fnn-hsig-pointer text) (length text)
                        (fnn-hsig-pointer key)))
          (error 'fnn-hsig-fault :detail "Ed25519 signing failed")))
      (unless (= actual +fnn-hsig-ed-signature-octets+)
        (error 'fnn-hsig-fault :detail "unexpected Ed25519 signature width")))
    signature))

(defun fnn-hsig-ml-public-key-from-handle (key)
  (let ((output (make-array +fnn-hsig-ml-public-key-octets+
                            :element-type '(unsigned-byte 8))))
    (sb-alien:with-alien ((actual sb-alien:unsigned-long))
             (setf actual +fnn-hsig-ml-public-key-octets+)
             (sb-sys:with-pinned-objects (output)
               (unless (= (fnn-%hsig-get-raw-public-key
                           key (fnn-hsig-pointer output)
                           (sb-alien:addr actual)) 1)
                 (error 'fnn-hsig-fault
                        :detail "ML-DSA-65 public-key export failed")))
             (unless (= actual +fnn-hsig-ml-public-key-octets+)
               (error 'fnn-hsig-fault
                      :detail "unexpected ML-DSA-65 public-key width")))
    output))

(defun fnn-hsig-ml-dsa-65-public-key (public-key-path)
  "Return and width-check the raw FIPS 204 public key from a supplied PEM."
  (fnn-hsig-initialize)
  (let ((key nil))
    (unwind-protect
         (progn (setq key (fnn-hsig-read-key public-key-path nil))
                (fnn-hsig-ml-public-key-from-handle key))
      (when key (fnn-%hsig-pkey-free key)))))

(defun fnn-hsig-ml-dsa-65-sign (private-key-path message)
  (fnn-hsig-initialize)
  (let ((text (fnn-crypto-octets message (fnn-hsig-max-message-octets)
                                 "hybrid signed preimage"))
        (key nil) (context nil) (algorithm nil)
        (signature (make-array +fnn-hsig-ml-signature-octets+
                               :element-type '(unsigned-byte 8))))
    (unwind-protect
         (progn
           (setq key (fnn-hsig-read-key private-key-path t)
                 context (fnn-%hsig-context-new (fnn-hsig-null) key nil)
                 algorithm (fnn-%hsig-fetch (fnn-hsig-null) "ML-DSA-65" nil))
           (when (or (fnn-hsig-null-p context) (fnn-hsig-null-p algorithm))
             (error 'fnn-hsig-unsupported :detail "ML-DSA-65 context unavailable"))
           (unless (= (fnn-%hsig-sign-init context algorithm (fnn-hsig-null)) 1)
             (error 'fnn-hsig-fault :detail "ML-DSA-65 signing initialization failed"))
           (sb-alien:with-alien ((actual sb-alien:unsigned-long))
             (setf actual +fnn-hsig-ml-signature-octets+)
             (sb-sys:with-pinned-objects (text signature)
               (unless (= (fnn-%hsig-sign context (fnn-hsig-pointer signature)
                                            (sb-alien:addr actual)
                                            (fnn-hsig-pointer text) (length text)) 1)
                 (error 'fnn-hsig-fault :detail "ML-DSA-65 signing failed")))
             (unless (= actual +fnn-hsig-ml-signature-octets+)
               (error 'fnn-hsig-fault :detail "unexpected ML-DSA-65 signature width"))))
      (when algorithm (fnn-%hsig-signature-free algorithm))
      (when context (fnn-%hsig-context-free context))
      (when key (fnn-%hsig-pkey-free key)))
    signature))

(defun fnn-hsig-ml-dsa-65-verify-key (key message signature)
  "Verify with an already imported public key and report its actual raw bytes."
  (let ((text (fnn-crypto-octets message (fnn-hsig-max-message-octets)
                                 "hybrid signed preimage"))
        (sig (fnn-crypto-octets signature +fnn-hsig-ml-signature-octets+
                                "ML-DSA-65 signature"))
        (context nil) (algorithm nil) (observed-key nil))
    (unless (= (length sig) +fnn-hsig-ml-signature-octets+)
      (return-from fnn-hsig-ml-dsa-65-verify-key nil))
    (unwind-protect
         (progn
           (setq context (fnn-%hsig-context-new (fnn-hsig-null) key nil)
                 algorithm (fnn-%hsig-fetch (fnn-hsig-null) "ML-DSA-65" nil))
           (setq observed-key (fnn-hsig-ml-public-key-from-handle key))
           (when (or (fnn-hsig-null-p context) (fnn-hsig-null-p algorithm))
             (error 'fnn-hsig-unsupported :detail "ML-DSA-65 context unavailable"))
           (unless (= (fnn-%hsig-verify-init context algorithm (fnn-hsig-null)) 1)
             (error 'fnn-hsig-fault :detail "ML-DSA-65 verification initialization failed"))
           (sb-sys:with-pinned-objects (text sig)
             (let ((result (fnn-%hsig-verify context (fnn-hsig-pointer sig)
                                              (length sig) (fnn-hsig-pointer text)
                                              (length text))))
               (cond ((= result 1) (values t observed-key))
                     ((= result 0) (values nil observed-key))
                     (t (error 'fnn-hsig-fault
                               :detail "ML-DSA-65 verification fault"))))))
      (when algorithm (fnn-%hsig-signature-free algorithm))
      (when context (fnn-%hsig-context-free context)))))

(defun fnn-hsig-ml-dsa-65-verify (public-key-path message signature)
  (fnn-hsig-initialize)
  (let ((key nil))
    (unwind-protect
         (progn
           (setq key (fnn-hsig-read-key public-key-path nil))
           (fnn-hsig-ml-dsa-65-verify-key key message signature))
      (when key (fnn-%hsig-pkey-free key)))))

(defun fnn-hsig-ml-dsa-65-verify-raw (public-key message signature)
  "Import the exact bounded enrolled key bytes; no PEM file or key choice."
  (fnn-hsig-initialize)
  (let ((raw (fnn-crypto-octets public-key +fnn-hsig-ml-public-key-octets+
                                 "ML-DSA-65 public key"))
        (key nil))
    (unless (= (length raw) +fnn-hsig-ml-public-key-octets+)
      (return-from fnn-hsig-ml-dsa-65-verify-raw nil))
    (unwind-protect
         (progn
           (sb-sys:with-pinned-objects (raw)
             (setq key (fnn-%hsig-new-raw-public-key
                        (fnn-hsig-null) "ML-DSA-65" nil
                        (fnn-hsig-pointer raw) (length raw))))
           (when (fnn-hsig-null-p key)
             (error 'fnn-hsig-fault
                    :detail "cannot import ML-DSA-65 enrolled public key"))
           (fnn-hsig-ml-dsa-65-verify-key key message signature))
      (when key (fnn-%hsig-pkey-free key)))))

(defun fnn-hsig-observe
    (ed-public-key ml-public-key-path message signatures)
  "Return two distinct primitive observations.  No component can stand in for
the other, and unsupported ML-DSA is never mapped to :VERIFIED."
  (let ((ed-signature (and (consp signatures) (cdr (car signatures))))
        (ml-signature (and (consp (cdr signatures))
                           (cdr (car (cdr signatures))))))
    (list (fnn-crypto-ed25519-observe
           ed-public-key message ed-signature (fnn-hsig-max-message-octets))
          (handler-case
              (multiple-value-bind (verified observed-key)
                  (fnn-hsig-ml-dsa-65-verify
                   ml-public-key-path message ml-signature)
                (list (if verified :verified :refused) observed-key))
            (fnn-hsig-unsupported () :unsupported)
            (error () :fault)))))

(defun fnn-hsig-observe-raw
    (ed-public-key ml-public-key message signatures)
  "Two independent observations against the exact ACL2-selected key bytes."
  (let ((ed-signature (and (consp signatures) (cdr (car signatures))))
        (ml-signature (and (consp (cdr signatures))
                           (cdr (car (cdr signatures))))))
    (list (fnn-crypto-ed25519-observe
           ed-public-key message ed-signature (fnn-hsig-max-message-octets))
          (handler-case
              (multiple-value-bind (verified observed-key)
                  (fnn-hsig-ml-dsa-65-verify-raw
                   ml-public-key message ml-signature)
                (list (if verified :verified :refused) observed-key))
            (fnn-hsig-unsupported () :unsupported)
            (error () :fault)))))

(defun fnn-hsig-authorize-profile
    (principal keys source signatures ml-public-key-path)
  "Verify and ask ACL2's selected-profile conjunction for the final verdict."
  (let ((preimage (fnn-core 'fn-hsig-host-preimage principal keys source)))
    (unless (and preimage (plusp (length preimage)))
      (return-from fnn-hsig-authorize-profile nil))
    (let* ((ed-public-key (cdr (first keys)))
           (observations (fnn-hsig-observe ed-public-key ml-public-key-path
                                           preimage signatures))
           (ml-observation (second observations))
           (observed-ml-key (and (consp ml-observation)
                                 (second ml-observation))))
      (fnn-core 'fn-hsig-host-authorize principal keys source signatures
                (and observed-ml-key (coerce observed-ml-key 'list))
                (first observations)
                (if (consp ml-observation) (first ml-observation)
                  ml-observation)))))

(defun fnn-hsig-verify-received-carrier (received ml-public-key-path)
  "Decode a bounded portable carrier in ACL2, then verify both native suites.
The caller supplies an independently configured ML-DSA public-key file; ACL2's
authorization check binds its observed key bytes to the carrier's key set."
  (let ((plan (fnn-core 'fn-hsig-host-received-carrier-plan received)))
    (if (not (eq (first plan) :ok))
        plan
      (let* ((value (second plan))
             (source (first value))
             (carrier (second value))
             (principal (first carrier))
             (keys (second carrier))
             (signatures (third carrier)))
        (if (fnn-hsig-authorize-profile principal keys source signatures
                                        ml-public-key-path)
            (list :verified source principal keys)
          (list :unverified :signature received))))))

(defun fnn-hsig-authorized-article-event
    (sequence txid generation keyring-generation enrolled-snapshot
              msgid content-subject
              article-record principal keys source signatures
              ml-public-key-path)
  "Verify once, then ask ACL2 to construct the complete durable kind-4 event.
The caller may pass the returned object unchanged to the identity owner."
  (let ((preimage (fnn-core 'fn-hsig-host-preimage principal keys source)))
    (unless (and preimage (plusp (length preimage)))
      (return-from fnn-hsig-authorized-article-event nil))
    (let* ((observations
            (fnn-hsig-observe (cdr (first keys)) ml-public-key-path
                              preimage signatures))
           (ml-observation (second observations))
           (observed-ml-key (and (consp ml-observation)
                                 (second ml-observation))))
      (fnn-core
       'fn-hsig-host-authorized-article-event
       sequence txid generation keyring-generation enrolled-snapshot
       msgid content-subject
       article-record principal keys source signatures
       (and observed-ml-key (coerce observed-ml-key 'list))
       (first observations)
       (if (consp ml-observation) (first ml-observation) ml-observation)))))

(defun fnn-hsig-authorized-submission-event
    (coordinates keyring-generation enrolled-snapshot msgid source groups
                 obligation-id content-subject release-evidence charge
                 principal keys signatures ml-public-key-path observation)
  "Verify once and ask ACL2 to construct the complete fn-r plus kind-4 event."
  (destructuring-bind (sequence txid generation) coordinates
    (let ((preimage (fnn-core 'fn-hsig-host-preimage principal keys source)))
      (unless (and preimage (plusp (length preimage)))
        (return-from fnn-hsig-authorized-submission-event nil))
      (let* ((observations
              (fnn-hsig-observe (cdr (first keys)) ml-public-key-path
                                preimage signatures))
             (ml-observation (second observations))
             (observed-ml-key (and (consp ml-observation)
                                   (second ml-observation))))
        (fnn-core
         'fn-hsig-host-authorized-submission-event
         sequence txid generation keyring-generation enrolled-snapshot
         msgid source groups obligation-id content-subject release-evidence
         charge principal keys signatures
         (and observed-ml-key (coerce observed-ml-key 'list))
         (first observations)
         (if (consp ml-observation) (first ml-observation)
           ml-observation)
         observation)))))

(defun fnn-hsig-authorized-carried-submission-event
    (coordinates keyring-generation enrolled-snapshot msgid source received groups
                 obligation-id content-subject release-evidence charge
                 principal keys signatures ml-public-key-path config observation)
  "Verify both native signatures, then ask ACL2 for the bound received carrier event."
  (destructuring-bind (sequence txid generation) coordinates
    (let ((preimage (fnn-core 'fn-hsig-host-preimage principal keys source)))
      (unless (and preimage (plusp (length preimage)))
        (return-from fnn-hsig-authorized-carried-submission-event nil))
      (let* ((observations
              (fnn-hsig-observe (cdr (first keys)) ml-public-key-path
                                preimage signatures))
             (ml-observation (second observations))
             (observed-ml-key (and (consp ml-observation)
                                   (second ml-observation))))
        (fnn-core
         'fn-hsig-authorized-injected-carried-submission-event
         sequence txid generation keyring-generation enrolled-snapshot
         msgid source received groups obligation-id content-subject
         release-evidence charge principal keys signatures
         (and observed-ml-key (coerce observed-ml-key 'list))
         (first observations)
         (if (consp ml-observation) (first ml-observation) ml-observation)
         config observation)))))
