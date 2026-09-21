;;; Native cryptographic primitive observations.
;;;
;;; This raw-Lisp file is part of HST-004's trust boundary.  It deliberately
;;; owns no signed grammar or key policy.  Callers must obtain the exact
;;; message octets from ACL2 (for the freshness anchor these are
;;; fn-anchor-host-delegation-octets and fn-anchor-host-signed-octets), and
;;; ACL2 continues to decide pinned-key membership, delegation windows,
;;; one-nonce/Merkle policy, acceptance and persistence.
;;;
;;; The implementation uses the stable libsodium C ABI already present on the
;;; supported development hosts.  Library absence and primitive faults are
;;; conditions, never a successful or refused signature verdict.

(in-package "ACL2")

(defconstant +fnn-crypto-ed25519-public-key-octets+ 32)
(defconstant +fnn-crypto-ed25519-signature-octets+ 64)
(defconstant +fnn-crypto-sha512-octets+ 64)
(defconstant +fnn-crypto-max-message-octets+ 4096)

(define-condition fnn-crypto-error (error)
  ((detail :initarg :detail :reader fnn-crypto-error-detail))
  (:report (lambda (condition stream)
             (format stream "native crypto: ~a"
                     (fnn-crypto-error-detail condition)))))

(define-condition fnn-crypto-unavailable (fnn-crypto-error) ())
(define-condition fnn-crypto-fault (fnn-crypto-error) ())

(defvar *fnn-crypto-state* :uninitialized)
(defvar *fnn-crypto-library* nil)
(defvar *fnn-crypto-version* nil)
(defvar *fnn-crypto-initialize-lock*
  (sb-thread:make-mutex :name "fn native crypto initialization"))

(defun fnn-crypto-library-candidates ()
  (cond
    ((member :darwin *features*)
     '("/opt/homebrew/opt/libsodium/lib/libsodium.dylib"
       "/usr/local/opt/libsodium/lib/libsodium.dylib"
       "libsodium.dylib"))
    ((member :linux *features*) '("libsodium.so.23" "libsodium.so"))
    (t nil)))

(sb-alien:define-alien-routine ("sodium_init" fnn-%sodium-init)
    sb-alien:int)
(sb-alien:define-alien-routine
    ("sodium_version_string" fnn-%sodium-version-string)
    sb-alien:c-string)
(sb-alien:define-alien-routine
    ("crypto_sign_publickeybytes" fnn-%crypto-sign-publickeybytes)
    sb-alien:unsigned-long)
(sb-alien:define-alien-routine
    ("crypto_sign_bytes" fnn-%crypto-sign-bytes)
    sb-alien:unsigned-long)
(sb-alien:define-alien-routine
    ("crypto_hash_sha512_bytes" fnn-%crypto-hash-sha512-bytes)
    sb-alien:unsigned-long)
(sb-alien:define-alien-routine
    ("crypto_sign_verify_detached" fnn-%crypto-sign-verify-detached)
    sb-alien:int
  (signature (* sb-alien:unsigned-char))
  (message (* sb-alien:unsigned-char))
  (message-length sb-alien:unsigned-long-long)
  (public-key (* sb-alien:unsigned-char)))
(sb-alien:define-alien-routine
    ("crypto_hash_sha512" fnn-%crypto-hash-sha512)
    sb-alien:int
  (output (* sb-alien:unsigned-char))
  (input (* sb-alien:unsigned-char))
  (input-length sb-alien:unsigned-long-long))

(defun fnn-crypto-load-library ()
  (let ((last-error nil))
    (dolist (candidate (fnn-crypto-library-candidates))
      (handler-case
          (progn
            (sb-alien:load-shared-object candidate)
            (return-from fnn-crypto-load-library candidate))
        (error (condition) (setq last-error condition))))
    (error 'fnn-crypto-unavailable
           :detail (if last-error
                       (format nil "libsodium cannot be loaded: ~a" last-error)
                     "libsodium has no loader candidate on this platform"))))

(defun fnn-crypto-check-abi ()
  (unless (member (fnn-%sodium-init) '(0 1))
    (error 'fnn-crypto-fault :detail "sodium_init failed"))
  (unless (= (fnn-%crypto-sign-publickeybytes)
             +fnn-crypto-ed25519-public-key-octets+)
    (error 'fnn-crypto-fault :detail "unexpected Ed25519 public-key width"))
  (unless (= (fnn-%crypto-sign-bytes)
             +fnn-crypto-ed25519-signature-octets+)
    (error 'fnn-crypto-fault :detail "unexpected Ed25519 signature width"))
  (unless (= (fnn-%crypto-hash-sha512-bytes) +fnn-crypto-sha512-octets+)
    (error 'fnn-crypto-fault :detail "unexpected SHA-512 output width"))
  (setq *fnn-crypto-version* (fnn-%sodium-version-string)))

(defun fnn-crypto-initialize ()
  "Load libsodium once and validate every ABI width used by this seam."
  (sb-thread:with-mutex (*fnn-crypto-initialize-lock*)
    (case *fnn-crypto-state*
      (:ready t)
      (:unavailable
       (error 'fnn-crypto-unavailable
              :detail "libsodium was unavailable during initialization"))
      (t
       (handler-case
           (progn
             (setq *fnn-crypto-library* (fnn-crypto-load-library))
             (fnn-crypto-check-abi)
             (setq *fnn-crypto-state* :ready)
             t)
         (fnn-crypto-error (condition)
           (setq *fnn-crypto-state* :unavailable)
           (error condition))
         (error (condition)
           (setq *fnn-crypto-state* :unavailable)
           (error 'fnn-crypto-unavailable
                  :detail (format nil "libsodium ABI cannot initialize: ~a"
                                  condition))))))))

(defun fnn-crypto-version ()
  (fnn-crypto-initialize)
  (list *fnn-crypto-library* *fnn-crypto-version*))

(defun fnn-crypto-octets (value limit name)
  "Copy VALUE to a bounded simple (unsigned-byte 8) vector."
  (let ((length (handler-case (length value) (type-error () nil))))
    (unless (and (integerp length) (<= 0 length) (<= length limit))
      (error 'fnn-crypto-fault
             :detail (format nil "~a is not bounded to ~d octets" name limit)))
    (let ((answer (make-array length :element-type '(unsigned-byte 8))))
      (dotimes (index length answer)
        (let ((octet (elt value index)))
          (unless (typep octet '(unsigned-byte 8))
            (error 'fnn-crypto-fault
                   :detail (format nil "~a contains a non-octet" name)))
          (setf (aref answer index) octet))))))

(defun fnn-crypto-pointer (vector)
  (sb-alien:sap-alien (sb-sys:vector-sap vector)
                      (* sb-alien:unsigned-char)))

(defun fnn-crypto-ed25519-verify (public-key message signature)
  "Return T or NIL for one bounded detached signature; signal facility faults."
  (fnn-crypto-initialize)
  (let ((key (fnn-crypto-octets public-key
                                +fnn-crypto-ed25519-public-key-octets+
                                "Ed25519 public key"))
        (text (fnn-crypto-octets message +fnn-crypto-max-message-octets+
                                 "Ed25519 message"))
        (sig (fnn-crypto-octets signature
                                +fnn-crypto-ed25519-signature-octets+
                                "Ed25519 signature")))
    ;; Wrong widths are a negative verification verdict, matching the ACL2
    ;; seam's constraints; malformed/non-octet values above are host faults.
    (if (or (/= (length key) +fnn-crypto-ed25519-public-key-octets+)
            (/= (length sig) +fnn-crypto-ed25519-signature-octets+))
        nil
      (sb-sys:with-pinned-objects (key text sig)
        (let ((result (fnn-%crypto-sign-verify-detached
                       (fnn-crypto-pointer sig) (fnn-crypto-pointer text)
                       (length text) (fnn-crypto-pointer key))))
          (cond ((zerop result) t)
                ((= result -1) nil)
                (t (error 'fnn-crypto-fault
                          :detail (format nil
                                          "Ed25519 verifier returned ~d"
                                          result)))))))))

(defun fnn-crypto-ed25519-observe (public-key message signature)
  "Three-way host observation.  :UNAVAILABLE/:FAULT are not signature verdicts."
  (handler-case
      (if (fnn-crypto-ed25519-verify public-key message signature)
          :verified
        :refused)
    (fnn-crypto-unavailable () :unavailable)
    (fnn-crypto-fault () :fault)
    ;; Foreign symbol/call failures are host faults.  They are deliberately
    ;; caught only by the observation API; the lower primitive keeps the
    ;; diagnostic condition for callers that need to report it.
    (error () :fault)))

(defun fnn-crypto-sha512 (octets)
  "Return the 64 SHA-512 octets for one bounded input; signal facility faults."
  (fnn-crypto-initialize)
  (let ((input (fnn-crypto-octets octets +fnn-crypto-max-message-octets+
                                  "SHA-512 input"))
        (output (make-array +fnn-crypto-sha512-octets+
                            :element-type '(unsigned-byte 8))))
    (sb-sys:with-pinned-objects (input output)
      (let ((result (fnn-%crypto-hash-sha512
                     (fnn-crypto-pointer output) (fnn-crypto-pointer input)
                     (length input))))
        (unless (zerop result)
          (error 'fnn-crypto-fault
                 :detail (format nil "SHA-512 returned ~d" result)))))
    output))

(defun fnn-crypto-anchor-leaf (nonce)
  "SHA-512(0x00 || NONCE), the host realiser of fn-anchor-leaf-digest."
  (let ((value (fnn-crypto-octets nonce 32 "Roughtime nonce")))
    (unless (= (length value) 32)
      (error 'fnn-crypto-fault :detail "Roughtime nonce is not 32 octets"))
    (let ((preimage (make-array 33 :element-type '(unsigned-byte 8)
                                :initial-element 0)))
      (replace preimage value :start1 1)
      (fnn-crypto-sha512 preimage))))
