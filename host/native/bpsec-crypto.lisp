;;; Receiver-only BPSec primitive I/O, inside HST-004's native trust boundary.
;;; Depends on crypto.lisp conditions/pointers and tls.lisp's pinned OpenSSL
;;; pair. ACL2 owns suite/key/profile decisions, canonical input, charged
;;; span bounds, HMAC comparison and completion. This module does NOT issue
;;; references, grant a descriptor, create a completion or admit a bundle.
;;; The caller must hold the issued descriptor and exact immutable source/key
;;; spans through every call. A descriptor retained here is provenance data,
;;; never evidence that a caller actually held that authority.
;;;
;;; Each update borrows one bounded simple octet vector window. No input is
;;; concatenated. This is the FIRST, authentication-only GCM pass: each
;;; speculative plaintext window is cleansed immediately, never retained or
;;; returned. Final reports authentication of the exact issued input. A
;;; SECOND decryption pass needs the SAME retained immutable ciphertext pin
;;; and a current ACL2 replay grant; that caller/API is not installed here.
;;; Cancel/fault destroys the single transient window and frees the context.
;;; Primitive observations are NOT application accepted/refused decisions.
(in-package "ACL2")

(define-condition fnn-bps-unsupported (fnn-crypto-error) ())

(defparameter *fnn-bps-required-symbols*
  '("HMAC_CTX_new" "HMAC_CTX_free" "HMAC_Init_ex" "HMAC_Update" "HMAC_Final"
    "EVP_sha256" "EVP_sha384" "EVP_sha512" "EVP_aes_128_gcm" "EVP_aes_256_gcm"
    "EVP_CIPHER_CTX_new" "EVP_CIPHER_CTX_free" "EVP_CIPHER_CTX_ctrl"
    "EVP_DecryptInit_ex" "EVP_DecryptUpdate" "EVP_DecryptFinal_ex"
    "OPENSSL_cleanse"))

(sb-alien:define-alien-routine ("HMAC_CTX_new" fnn-bps-%hmac-new) (* t))
(sb-alien:define-alien-routine ("HMAC_CTX_free" fnn-bps-%hmac-free) sb-alien:void
  (ctx (* t)))
(sb-alien:define-alien-routine ("HMAC_Init_ex" fnn-bps-%hmac-init) sb-alien:int
  (ctx (* t)) (key (* sb-alien:unsigned-char)) (count sb-alien:int)
  (md (* t)) (engine (* t)))
(sb-alien:define-alien-routine ("HMAC_Update" fnn-bps-%hmac-update) sb-alien:int
  (ctx (* t)) (input (* sb-alien:unsigned-char)) (count sb-alien:unsigned-long))
(sb-alien:define-alien-routine ("HMAC_Final" fnn-bps-%hmac-final) sb-alien:int
  (ctx (* t)) (output (* sb-alien:unsigned-char)) (count (* sb-alien:unsigned-int)))
(sb-alien:define-alien-routine ("EVP_sha256" fnn-bps-%sha256) (* t))
(sb-alien:define-alien-routine ("EVP_sha384" fnn-bps-%sha384) (* t))
(sb-alien:define-alien-routine ("EVP_sha512" fnn-bps-%sha512) (* t))
(sb-alien:define-alien-routine ("EVP_aes_128_gcm" fnn-bps-%aes128) (* t))
(sb-alien:define-alien-routine ("EVP_aes_256_gcm" fnn-bps-%aes256) (* t))
(sb-alien:define-alien-routine ("EVP_CIPHER_CTX_new" fnn-bps-%cipher-new) (* t))
(sb-alien:define-alien-routine ("EVP_CIPHER_CTX_free" fnn-bps-%cipher-free) sb-alien:void
  (ctx (* t)))
(sb-alien:define-alien-routine ("EVP_CIPHER_CTX_ctrl" fnn-bps-%cipher-ctrl) sb-alien:int
  (ctx (* t)) (command sb-alien:int) (arg sb-alien:int) (ptr (* t)))
(sb-alien:define-alien-routine ("EVP_DecryptInit_ex" fnn-bps-%decrypt-init) sb-alien:int
  (ctx (* t)) (cipher (* t)) (engine (* t))
  (key (* sb-alien:unsigned-char)) (iv (* sb-alien:unsigned-char)))
(sb-alien:define-alien-routine ("EVP_DecryptUpdate" fnn-bps-%decrypt-update) sb-alien:int
  (ctx (* t)) (output (* sb-alien:unsigned-char)) (written (* sb-alien:int))
  (input (* sb-alien:unsigned-char)) (count sb-alien:int))
(sb-alien:define-alien-routine ("EVP_DecryptFinal_ex" fnn-bps-%decrypt-final) sb-alien:int
  (ctx (* t)) (output (* sb-alien:unsigned-char)) (written (* sb-alien:int)))
(sb-alien:define-alien-routine ("OPENSSL_cleanse" fnn-bps-%cleanse) sb-alien:void
  (bytes (* sb-alien:unsigned-char)) (count sb-alien:unsigned-long))

(defstruct (fnn-bps-primitive (:constructor fnn-bps-%make-primitive))
  descriptor kind context (phase :active) transient
  ;; This is a caller-selected per-call allocation/work bound, not a total
  ;; message ceiling. Its charge/representability is an ACL2 caller premise.
  window-limit)

(defun fnn-bps-initialize ()
  "Use the already selected TLS libcrypto pair; never load another version."
  (handler-case (fnn-tls-initialize)
    (fnn-tls-error (condition)
      (error 'fnn-crypto-unavailable :detail (fnn-tls-error-detail condition))))
  (let ((missing (remove-if #'sb-sys:find-foreign-symbol-address
                            *fnn-bps-required-symbols*)))
    (when missing
      (error 'fnn-crypto-unavailable :detail
             (format nil "BPSec primitive ABI lacks ~{~a~^, ~}" missing))))
  t)

(defun fnn-bps-ffi-fault (name)
  (error 'fnn-crypto-fault :detail
         (format nil "~a: ~a" name (fnn-tls-error-stack))))

(defun fnn-bps-check-one (result name)
  (unless (= result 1) (fnn-bps-ffi-fault name)))

(defun fnn-bps-null-bytes ()
  (sb-alien:sap-alien (sb-sys:int-sap 0) (* sb-alien:unsigned-char)))

(defun fnn-bps-byte-count (bytes)
  (unless (typep bytes '(simple-array (unsigned-byte 8) (*)))
    (error 'fnn-crypto-fault :detail "primitive byte buffer is not a simple octet vector"))
  (length bytes))

(defun fnn-bps-window-check (bytes start count limit)
  ;; Raw FFI memory safety only. No list traversal/copy of an unbounded input.
  ;; The actual provider must establish immutable byte/span provenance.
  (unless (and (typep bytes '(simple-array (unsigned-byte 8) (*)))
               (typep start '(integer 0 *)) (typep count '(integer 0 *))
               (typep limit '(integer 1 2147483631))
               (<= count limit) (<= (+ start count) (length bytes)))
    (error 'fnn-crypto-fault :detail "invalid or unbounded primitive window")))

(defun fnn-bps-window-pointer (bytes start)
  (sb-alien:sap-alien (sb-sys:sap+ (sb-sys:vector-sap bytes) start)
                      (* sb-alien:unsigned-char)))

(defun fnn-bps-cleanse (bytes)
  (when (plusp (length bytes))
    (sb-sys:with-pinned-objects (bytes)
      (fnn-bps-%cleanse (fnn-crypto-pointer bytes) (length bytes))))
  nil)

(defun fnn-bps-cancel (handle)
  "Idempotent disposal. No charge refund or logical token retirement inferred."
  (let ((window (fnn-bps-primitive-transient handle)))
    (when window (fnn-bps-cleanse window))
    (setf (fnn-bps-primitive-transient handle) nil))
  (let ((ctx (fnn-bps-primitive-context handle)))
    (when ctx
      ;; Clear the Lisp pointer before free so an unwind cannot double-free.
      (setf (fnn-bps-primitive-context handle) nil)
      (if (eq (fnn-bps-primitive-kind handle) :hmac)
          (fnn-bps-%hmac-free ctx)
        (fnn-bps-%cipher-free ctx))))
  (setf (fnn-bps-primitive-phase handle) :closed)
  nil)

(defmacro fnn-bps-with-operation ((handle) &body body)
  ;; A failed allocation/FFI call is as terminal as an explicit cancel. Do not
  ;; leave an active context or speculative plaintext after a nonlocal exit.
  `(let ((completed nil))
     (unwind-protect
          (multiple-value-prog1 (progn ,@body) (setf completed t))
       (unless completed (fnn-bps-cancel ,handle)))))

(defun fnn-bps-active (handle kind)
  (unless (and (fnn-bps-primitive-p handle)
               (eq (fnn-bps-primitive-kind handle) kind)
               (eq (fnn-bps-primitive-phase handle) :active)
               (fnn-bps-primitive-context handle))
    (error 'fnn-crypto-fault :detail "primitive is closed or of another kind")))

(defun fnn-bps-hmac-start (descriptor digest key window-limit)
  "Initialize exactly the primitive ACL2 selected. DIGEST is a primitive name.
General primitive diagnostics may use RFC keys shorter than BPSec permits;
production key/profile admission MUST be done by ACL2 before this call."
  (let* ((getter (case digest (:sha256 #'fnn-bps-%sha256)
                               (:sha384 #'fnn-bps-%sha384) (:sha512 #'fnn-bps-%sha512)
                  (otherwise (error 'fnn-bps-unsupported :detail "unknown HMAC primitive"))))
         (md (progn (fnn-bps-initialize) (funcall getter)))
         (handle (fnn-bps-%make-primitive :descriptor descriptor :kind :hmac
                                         :window-limit window-limit)))
    (when (fnn-tls-null-pointer-p md)
      (error 'fnn-crypto-unavailable :detail "selected HMAC digest unavailable"))
    (fnn-bps-with-operation (handle)
      (fnn-bps-window-check key 0 (fnn-bps-byte-count key) window-limit)
      (let ((ctx (fnn-bps-%hmac-new)))
        (when (fnn-tls-null-pointer-p ctx) (fnn-bps-ffi-fault "HMAC_CTX_new"))
        (setf (fnn-bps-primitive-context handle) ctx)
        (fnn-%err-clear-error)
        (sb-sys:with-pinned-objects (key)
          (fnn-bps-check-one
           (fnn-bps-%hmac-init ctx (fnn-crypto-pointer key) (fnn-bps-byte-count key) md
                              (fnn-tls-null-pointer)) "HMAC_Init_ex")))
      handle)))

(defun fnn-bps-hmac-update (handle bytes start count)
  (fnn-bps-with-operation (handle)
    (fnn-bps-active handle :hmac)
    (fnn-bps-window-check bytes start count (fnn-bps-primitive-window-limit handle))
    (fnn-%err-clear-error)
    (sb-sys:with-pinned-objects (bytes)
      (fnn-bps-check-one
       (fnn-bps-%hmac-update (fnn-bps-primitive-context handle)
                            (fnn-bps-window-pointer bytes start) count) "HMAC_Update"))
    ;; No comparison with expected HMAC is performed in the host.
    nil))

(defun fnn-bps-hmac-final (handle)
  "Return (descriptor :hmac-bytes actual-vector actual-width), never :verified."
  (fnn-bps-with-operation (handle)
    (fnn-bps-active handle :hmac)
    (let ((output (make-array 64 :element-type '(unsigned-byte 8) :initial-element 0))
          (transferred nil))
      (unwind-protect
           (sb-alien:with-alien ((written sb-alien:unsigned-int 0))
             (fnn-%err-clear-error)
             (sb-sys:with-pinned-objects (output)
               (fnn-bps-check-one
                (fnn-bps-%hmac-final (fnn-bps-primitive-context handle)
                                    (fnn-crypto-pointer output) (sb-alien:addr written))
                "HMAC_Final"))
             (unless (member written '(32 48 64)) (fnn-bps-ffi-fault "HMAC width"))
             (fnn-bps-cancel handle)
             (prog1 (list (fnn-bps-primitive-descriptor handle) :hmac-bytes output written)
               (setf transferred t)))
        (unless transferred (fnn-bps-cleanse output))))))

(defun fnn-bps-gcm-start (descriptor cipher key iv window-limit)
  "Start a receiver. CIPHER is :aes128-gcm or :aes256-gcm selected by ACL2."
  (let* ((key-width (case cipher (:aes128-gcm 16) (:aes256-gcm 32)
                      (otherwise (error 'fnn-bps-unsupported :detail "unknown GCM primitive"))))
         (method (progn (fnn-bps-initialize)
                        (if (= key-width 16) (fnn-bps-%aes128) (fnn-bps-%aes256))))
         (handle (fnn-bps-%make-primitive :descriptor descriptor :kind :gcm
                                         :window-limit window-limit)))
    (when (fnn-tls-null-pointer-p method)
      (error 'fnn-crypto-unavailable :detail "selected GCM cipher unavailable"))
    (fnn-bps-with-operation (handle)
      (fnn-bps-window-check key 0 (fnn-bps-byte-count key) key-width)
      (unless (= (fnn-bps-byte-count key) key-width)
        (error 'fnn-crypto-fault :detail "unsafe GCM key buffer width"))
      (fnn-bps-window-check iv 0 (fnn-bps-byte-count iv) 16)
      (unless (<= 8 (fnn-bps-byte-count iv) 16)
        (error 'fnn-crypto-fault :detail "unsafe GCM IV buffer width"))
      (fnn-bps-window-check iv 0 0 window-limit)
      (let ((ctx (fnn-bps-%cipher-new)))
        (when (fnn-tls-null-pointer-p ctx) (fnn-bps-ffi-fault "EVP_CIPHER_CTX_new"))
        (setf (fnn-bps-primitive-context handle) ctx)
        (fnn-%err-clear-error)
        (fnn-bps-check-one
         (fnn-bps-%decrypt-init ctx method (fnn-tls-null-pointer)
                               (fnn-bps-null-bytes) (fnn-bps-null-bytes)) "GCM select")
        ;; EVP_CTRL_AEAD_SET_IVLEN = 9, SET_TAG = 17 (stable EVP ABI).
        (fnn-bps-check-one
         (fnn-bps-%cipher-ctrl ctx 9 (fnn-bps-byte-count iv) (fnn-tls-null-pointer)) "GCM IV length")
        (sb-sys:with-pinned-objects (key iv)
          (fnn-bps-check-one
           (fnn-bps-%decrypt-init ctx (fnn-tls-null-pointer) (fnn-tls-null-pointer)
                                 (fnn-crypto-pointer key) (fnn-crypto-pointer iv)) "GCM key/IV")))
      handle)))

(defun fnn-bps-gcm-aad (handle bytes start count)
  (fnn-bps-with-operation (handle)
    (fnn-bps-active handle :gcm)
    (fnn-bps-window-check bytes start count (fnn-bps-primitive-window-limit handle))
    (fnn-%err-clear-error)
    (sb-alien:with-alien ((written sb-alien:int 0))
      (sb-sys:with-pinned-objects (bytes)
        (fnn-bps-check-one
         (fnn-bps-%decrypt-update (fnn-bps-primitive-context handle)
                                 (fnn-bps-null-bytes) (sb-alien:addr written)
                                 (fnn-bps-window-pointer bytes start) count) "GCM AAD")))
    nil))

(defun fnn-bps-gcm-update (handle bytes start count)
  "Authenticate one ciphertext window; discard all speculative plaintext."
  (fnn-bps-with-operation (handle)
    (fnn-bps-active handle :gcm)
    (fnn-bps-window-check bytes start count (fnn-bps-primitive-window-limit handle))
    (let ((output (make-array (+ count 16) :element-type '(unsigned-byte 8) :initial-element 0)))
      (setf (fnn-bps-primitive-transient handle) output)
      (unwind-protect
           (sb-alien:with-alien ((written sb-alien:int 0))
             (fnn-%err-clear-error)
             (sb-sys:with-pinned-objects (bytes output)
               (fnn-bps-check-one
                (fnn-bps-%decrypt-update (fnn-bps-primitive-context handle)
                                        (fnn-crypto-pointer output) (sb-alien:addr written)
                                        (fnn-bps-window-pointer bytes start) count) "GCM ciphertext"))
             (unless (<= 0 written (+ count 16)) (fnn-bps-ffi-fault "GCM update width"))
             nil)
        (fnn-bps-cleanse output)
        (setf (fnn-bps-primitive-transient handle) nil)))))

(defun fnn-bps-gcm-final (handle tag)
  "Return (descriptor :authenticated nil) or (descriptor :bad-tag nil).
This authenticates only; no plaintext or BCB completion is published here."
  (fnn-bps-with-operation (handle)
    (fnn-bps-active handle :gcm)
    (fnn-bps-window-check tag 0 (fnn-bps-byte-count tag) 16)
    (unless (= (fnn-bps-byte-count tag) 16)
      (error 'fnn-crypto-fault :detail "unsafe GCM tag buffer width"))
    (let ((output (make-array 16 :element-type '(unsigned-byte 8) :initial-element 0)))
      (setf (fnn-bps-primitive-transient handle) output)
      (unwind-protect
           (sb-alien:with-alien ((written sb-alien:int 0))
             (fnn-%err-clear-error)
             (sb-sys:with-pinned-objects (tag)
               (fnn-bps-check-one
                (fnn-bps-%cipher-ctrl (fnn-bps-primitive-context handle) 17 16
                                     (sb-alien:cast (fnn-crypto-pointer tag) (* t))) "GCM set tag"))
             (fnn-%err-clear-error)
             (let ((result (sb-sys:with-pinned-objects (output)
                             (fnn-bps-%decrypt-final (fnn-bps-primitive-context handle)
                                                    (fnn-crypto-pointer output) (sb-alien:addr written)))))
               (cond
                ((= result 1)
                 ;; GCM produces all bytes at Update; unexpected Final output
                 ;; is an ABI fault. Never silently truncate such a tail.
                 (unless (zerop written) (fnn-bps-ffi-fault "GCM unexpected final bytes"))
                 (fnn-bps-cancel handle)
                 (list (fnn-bps-primitive-descriptor handle) :authenticated nil))
                ((and (zerop result) (zerop (fnn-%err-get-error)))
                 (fnn-bps-cancel handle)
                 (list (fnn-bps-primitive-descriptor handle) :bad-tag nil))
                (t (fnn-bps-ffi-fault "GCM final")))))
        (fnn-bps-cleanse output)
        (setf (fnn-bps-primitive-transient handle) nil)))))
