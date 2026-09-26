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

;;; ML-DSA-65 is the vendored PQClean implementation (FIPS 204 final, pure,
;;; empty context) behind host/native/fn-mldsa65.c, built by
;;; tools/build_mldsa65.sh into lib/ beside the image's core (HST-016).  It
;;; reads and writes the key files OpenSSL 3.5 wrote (PKCS#8 and
;;; SubjectPublicKeyInfo PEM), byte for byte; tests/mldsa65_interop.py checks
;;; that and every committed OpenSSL-made signature.  Nothing here depends on
;;; the TLS library.
(defvar *fnn-hsig-mldsa-state* :uninitialized)
(defvar *fnn-hsig-mldsa-library* nil)
(defvar *fnn-hsig-mldsa-version* nil)
(defvar *fnn-hsig-mldsa-lock*
  (sb-thread:make-mutex :name "fn ML-DSA-65 initialization"))

(defun fnn-hsig-mldsa-library-name ()
  (if (member :darwin *features*) "libfn-mldsa65.dylib" "libfn-mldsa65.so"))

(defun fnn-hsig-mldsa-library-candidates ()
  "FN_MLDSA_LIBRARY when the operator names one, else lib/ beside the core:
build/lib for a built image, the frozen or installed directory's lib/."
  (let ((named (sb-ext:posix-getenv "FN_MLDSA_LIBRARY"))
        (core sb-ext:*core-pathname*))
    (cond ((and named (plusp (length named)))
           (if (find (code-char 0) named)
               (error 'fnn-hsig-unsupported :detail "invalid FN_MLDSA_LIBRARY")
             (list named)))
          (core
           (list (namestring
                  (merge-pathnames (concatenate 'string "lib/"
                                                (fnn-hsig-mldsa-library-name))
                                   (make-pathname :name nil :type nil
                                                  :version nil
                                                  :defaults core)))))
          (t nil))))

(sb-alien:define-alien-routine
    ("crypto_sign_detached" fnn-%hsig-ed-sign-detached) sb-alien:int
  (signature (* sb-alien:unsigned-char))
  (signature-length (* sb-alien:unsigned-long-long))
  (message (* sb-alien:unsigned-char))
  (message-length sb-alien:unsigned-long-long)
  (secret-key (* sb-alien:unsigned-char)))
(sb-alien:define-alien-routine
    ("fn_mldsa65_implementation" fnn-%hsig-ml-implementation) sb-alien:c-string)
(sb-alien:define-alien-routine ("fn_mldsa65_widths" fnn-%hsig-ml-widths)
    sb-alien:int (out (* sb-alien:unsigned-long)))
(sb-alien:define-alien-routine ("fn_mldsa65_strerror" fnn-%hsig-ml-strerror)
    sb-alien:c-string (code sb-alien:int))
(sb-alien:define-alien-routine
    ("fn_mldsa65_public_from_pem_file" fnn-%hsig-ml-public-from-file)
    sb-alien:int (path sb-alien:c-string) (public-key (* sb-alien:unsigned-char)))
(sb-alien:define-alien-routine
    ("fn_mldsa65_sign_pem_file" fnn-%hsig-ml-sign-file) sb-alien:int
  (path sb-alien:c-string) (message (* sb-alien:unsigned-char))
  (message-length sb-alien:unsigned-long) (signature (* sb-alien:unsigned-char)))
(sb-alien:define-alien-routine ("fn_mldsa65_verify" fnn-%hsig-ml-verify)
    sb-alien:int
  (signature (* sb-alien:unsigned-char)) (signature-length sb-alien:unsigned-long)
  (message (* sb-alien:unsigned-char)) (message-length sb-alien:unsigned-long)
  (public-key (* sb-alien:unsigned-char)))

(defun fnn-hsig-pointer (vector)
  (sb-alien:sap-alien (sb-sys:vector-sap vector) (* sb-alien:unsigned-char)))

(defun fnn-hsig-mldsa-load ()
  (let ((last-error nil))
    (dolist (candidate (fnn-hsig-mldsa-library-candidates))
      (handler-case
          (progn
            ;; Not serialized into the core: startup re-loads from the
            ;; restarted image's own lib/ (fnn-hsig-reset clears readiness).
            (sb-alien:load-shared-object candidate :dont-save t)
            (return-from fnn-hsig-mldsa-load candidate))
        (error (condition) (setq last-error condition))))
    (error 'fnn-hsig-unsupported
           :detail (if last-error
                       (format nil "the ML-DSA-65 library cannot be loaded: ~a"
                               last-error)
                     "no ML-DSA-65 library candidate (lib/ beside the core)"))))

(defun fnn-hsig-mldsa-check-abi ()
  (let ((widths (make-array 3 :element-type '(unsigned-byte 64))))
    (sb-sys:with-pinned-objects (widths)
      (unless (zerop (fnn-%hsig-ml-widths
                      (sb-alien:sap-alien (sb-sys:vector-sap widths)
                                          (* sb-alien:unsigned-long))))
        (error 'fnn-hsig-unsupported :detail "ML-DSA-65 widths unavailable")))
    (unless (and (= (aref widths 0) +fnn-hsig-ml-public-key-octets+)
                 (= (aref widths 1) +fnn-hsig-ml-signature-octets+))
      (error 'fnn-hsig-unsupported
             :detail "the ML-DSA-65 library was built for other widths")))
  (fnn-%hsig-ml-implementation))

(defun fnn-hsig-initialize ()
  "Load libsodium (Ed25519) and the ML-DSA-65 library once; check their ABI."
  (fnn-crypto-initialize)
  (sb-thread:with-mutex (*fnn-hsig-mldsa-lock*)
    (case *fnn-hsig-mldsa-state*
      (:ready t)
      (:unsupported
       (error 'fnn-hsig-unsupported :detail "ML-DSA-65 is unavailable"))
      (t
       (handler-case
           (let* ((library (fnn-hsig-mldsa-load))
                  (version (fnn-hsig-mldsa-check-abi)))
             (setq *fnn-hsig-mldsa-library* library
                   *fnn-hsig-mldsa-version* version
                   *fnn-hsig-mldsa-state* :ready)
             t)
         (fnn-hsig-unsupported (condition)
           (setq *fnn-hsig-mldsa-state* :unsupported)
           (error condition))
         (error (condition)
           (setq *fnn-hsig-mldsa-state* :unsupported)
           (error 'fnn-hsig-unsupported
                  :detail (format nil "ML-DSA-65 ABI cannot initialize: ~a"
                                  condition))))))))

(defun fnn-hsig-reset ()
  (sb-thread:with-mutex (*fnn-hsig-mldsa-lock*)
    (setq *fnn-hsig-mldsa-state* :uninitialized
          *fnn-hsig-mldsa-library* nil *fnn-hsig-mldsa-version* nil))
  t)

(defun fnn-hsig-version ()
  (fnn-hsig-initialize)
  (list *fnn-hsig-mldsa-library* *fnn-hsig-mldsa-version*))

(defun fnn-hsig-ml-fault (code what)
  (error 'fnn-hsig-fault
         :detail (format nil "~a: ~a" what (fnn-%hsig-ml-strerror code))))

(defun fnn-hsig-key-path (path)
  (unless (and (stringp path) (> (length path) 0)
               (not (find (code-char 0) path)))
    (error 'fnn-hsig-fault :detail "a PEM key path is required"))
  path)

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

(defun fnn-hsig-ml-dsa-65-public-key (public-key-path)
  "Return the raw FIPS 204 public key from a SubjectPublicKeyInfo PEM file."
  (fnn-hsig-initialize)
  (let ((path (fnn-hsig-key-path public-key-path))
        (output (make-array +fnn-hsig-ml-public-key-octets+
                            :element-type '(unsigned-byte 8))))
    (sb-sys:with-pinned-objects (output)
      (let ((code (fnn-%hsig-ml-public-from-file path (fnn-hsig-pointer output))))
        (unless (zerop code)
          (fnn-hsig-ml-fault code (format nil "ML-DSA-65 public key ~a" path)))))
    output))

(defun fnn-hsig-ml-dsa-65-sign (private-key-path message)
  "Pure ML-DSA-65 (empty context, hedged) with the key in a PKCS#8 PEM file.
The secret key is read, expanded and wiped inside the library; it never
enters the Lisp heap."
  (fnn-hsig-initialize)
  (let ((path (fnn-hsig-key-path private-key-path))
        (text (fnn-crypto-octets message (fnn-hsig-max-message-octets)
                                 "hybrid signed preimage"))
        (signature (make-array +fnn-hsig-ml-signature-octets+
                               :element-type '(unsigned-byte 8))))
    (sb-sys:with-pinned-objects (text signature)
      (let ((code (fnn-%hsig-ml-sign-file path (fnn-hsig-pointer text)
                                          (length text)
                                          (fnn-hsig-pointer signature))))
        (unless (zerop code)
          (fnn-hsig-ml-fault code "ML-DSA-65 signing"))))
    signature))

(defun fnn-hsig-ml-dsa-65-verify-key (key message signature)
  "Verify under the exact raw public KEY; the second value is the key
observed (the octets verification used)."
  (let ((text (fnn-crypto-octets message (fnn-hsig-max-message-octets)
                                 "hybrid signed preimage"))
        (sig (fnn-crypto-octets signature +fnn-hsig-ml-signature-octets+
                                "ML-DSA-65 signature"))
        (raw (fnn-crypto-octets key +fnn-hsig-ml-public-key-octets+
                                "ML-DSA-65 public key")))
    (unless (and (= (length sig) +fnn-hsig-ml-signature-octets+)
                 (= (length raw) +fnn-hsig-ml-public-key-octets+))
      (return-from fnn-hsig-ml-dsa-65-verify-key nil))
    (sb-sys:with-pinned-objects (text sig raw)
      (let ((code (fnn-%hsig-ml-verify (fnn-hsig-pointer sig) (length sig)
                                       (fnn-hsig-pointer text) (length text)
                                       (fnn-hsig-pointer raw))))
        (cond ((= code 0) (values t raw))
              ((= code 1) (values nil raw))
              (t (fnn-hsig-ml-fault code "ML-DSA-65 verification")))))))

(defun fnn-hsig-ml-dsa-65-verify (public-key-path message signature)
  (fnn-hsig-ml-dsa-65-verify-key (fnn-hsig-ml-dsa-65-public-key public-key-path)
                                 message signature))

(defun fnn-hsig-ml-dsa-65-verify-raw (public-key message signature)
  "Verify under the exact bounded enrolled key bytes; no PEM file or key choice."
  (fnn-hsig-initialize)
  (let ((raw (fnn-crypto-octets public-key +fnn-hsig-ml-public-key-octets+
                                "ML-DSA-65 public key")))
    (unless (= (length raw) +fnn-hsig-ml-public-key-octets+)
      (return-from fnn-hsig-ml-dsa-65-verify-raw nil))
    (fnn-hsig-ml-dsa-65-verify-key raw message signature)))

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
