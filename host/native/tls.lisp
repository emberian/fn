;;; Native TLS transport boundary.
;;;
;;; TLS protocol, record protection, certificate parsing and cryptography are
;;; delegated to the system's libssl C ABI: OpenSSL 3.0 or later, or
;;; LibreSSL 3 or later (HST-016).  Only functions both provide are called,
;;; and every one is checked to resolve when the facility initializes (at
;;; image build and at each start), so a library lacking one is refused by
;;; name rather than failing at first use.  Signatures do not use this
;;; library (host/native/crypto.lisp, host/native/signatures.lisp).  This file supplies bounded
;;; nonblocking transport and diagnostics; it owns no NNTP or authentication
;;; decision.  A caller may mark an ACL2 connection protected only after
;;; FNN-TLS-ACCEPT returns a live channel.
;;;
;;; Trust and scheduling premises:
;;;   * the loaded libssl/libcrypto and platform dynamic loader are trusted;
;;;   * OpenSSL's C ABI and socket BIO behavior are trusted;
;;;   * one client worker is the sole reader and writer of a channel;
;;;   * MSG_PEEK followed by exact consume sees the same prefix under that
;;;     ownership.  FNN-TLS-CONSUME-PLAINTEXT checks the bytes and faults the
;;;     connection on short, changed, or failed consumption.

(in-package "ACL2")

(defconstant +fnn-tls-filetype-pem+ 1)
(defconstant +fnn-tls-error-ssl+ 1)
(defconstant +fnn-tls-error-want-read+ 2)
(defconstant +fnn-tls-error-want-write+ 3)
(defconstant +fnn-tls-error-syscall+ 5)
(defconstant +fnn-tls-error-zero-return+ 6)
(defconstant +fnn-tls-ctrl-set-min-proto-version+ 123)
(defconstant +fnn-tls-version-1-2+ #x0303)
(defconstant +fnn-tls-verify-peer+ 1)
(defconstant +fnn-tls-ctrl-set-tlsext-hostname+ 55)
(defconstant +fnn-tls-tlsext-nametype-host-name+ 0)

(define-condition fnn-tls-error (error)
  ((detail :initarg :detail :reader fnn-tls-error-detail))
  (:report (lambda (condition stream)
             (format stream "native TLS: ~a" (fnn-tls-error-detail condition)))))

(define-condition fnn-tls-unavailable (fnn-tls-error) ())
(define-condition fnn-tls-config-error (fnn-tls-error) ())
(define-condition fnn-tls-handshake-error (fnn-tls-error) ())
(define-condition fnn-tls-io-error (fnn-tls-error) ())
;;; PKT-613: the chain or the name did not verify.  OUTCOME is the host's
;;; classification of SSL_get_verify_result: :name-mismatch for
;;; X509_V_ERR_HOSTNAME_MISMATCH (62) or X509_V_ERR_IP_ADDRESS_MISMATCH (64),
;;; :certificate for any other nonzero result.  An observation, not a decision.
(define-condition fnn-tls-verify-error (fnn-tls-handshake-error)
  ((outcome :initarg :outcome :reader fnn-tls-verify-error-outcome)))

;;; A server context's POINTER is replaced only by `tls reload'
;;; (FNN-TLS-CONTEXT-SWAP, PRF-212), under LOCK, which FNN-TLS-ACCEPT also
;;; holds across SSL_new: SSL_new takes its own reference to the SSL_CTX (in
;;; OpenSSL 3 and LibreSSL alike), so once the swap releases the lock no
;;; new session can start on the old pointer and the sessions already open
;;; keep it alive until each is freed.  SERVED is ACL2's accepted decision
;;; for the material in POINTER (books/tls-reload.lisp fn-tlsr-decide), the
;;; source of the `tls names=... not-after=...' line; NIL when no decision was
;;; taken (a client context).
(defstruct (fnn-tls-context (:constructor fnn-tls-context-make))
  pointer certificate-path private-key-path
  (lock (sb-thread:make-mutex :name "fn native TLS context"))
  served)

(defstruct (fnn-tls-channel (:constructor fnn-tls-channel-make))
  pointer fd)

(defvar *fnn-tls-state* :uninitialized)
(defvar *fnn-tls-libraries* nil)
(defvar *fnn-tls-pinned-libraries* nil)
(defvar *fnn-tls-version* nil)
(defvar *fnn-tls-initialize-lock*
  (sb-thread:make-mutex :name "fn native TLS initialization"))

(defun fnn-tls-configured-library-pair ()
  "Return the operator-selected matched libcrypto/libssl pair, if any.
FN_OPENSSL_PREFIX is optional: unset, the system's pair is used."
  (let ((prefix (sb-ext:posix-getenv "FN_OPENSSL_PREFIX")))
    (when prefix
      (when (or (zerop (length prefix)) (find (code-char 0) prefix))
        (error 'fnn-tls-unavailable :detail "invalid FN_OPENSSL_PREFIX"))
      (let ((directory (string-right-trim "/" prefix)))
        (if (member :darwin *features*)
            (list (format nil "~a/lib/libcrypto.3.dylib" directory)
                  (format nil "~a/lib/libssl.3.dylib" directory))
          (let ((lib (list (format nil "~a/lib/libcrypto.so.3" directory)
                           (format nil "~a/lib/libssl.so.3" directory)))
                (lib64 (list (format nil "~a/lib64/libcrypto.so.3" directory)
                             (format nil "~a/lib64/libssl.so.3" directory))))
            (if (and (probe-file (first lib64)) (probe-file (second lib64)))
                lib64 lib)))))))

(defun fnn-tls-library-candidates ()
  (let ((configured (fnn-tls-configured-library-pair)))
    (if configured
        (list configured)
      ;; Read-time, as fnn-crypto-library-candidates: the core carries only
      ;; its platform's names (PKT-723).
      #+darwin
      '(("/opt/homebrew/opt/openssl@3/lib/libcrypto.3.dylib"
         "/opt/homebrew/opt/openssl@3/lib/libssl.3.dylib")
        ("/usr/local/opt/openssl@3/lib/libcrypto.3.dylib"
         "/usr/local/opt/openssl@3/lib/libssl.3.dylib")
        ("libcrypto.3.dylib" "libssl.3.dylib"))
      #+linux '(("libcrypto.so.3" "libssl.so.3"))
      ;; LibreSSL in the base system; ld.so resolves an unversioned
      ;; name to the installed major.
      #+openbsd '(("libcrypto.so" "libssl.so"))
      #-(or darwin linux openbsd) nil)))

;;; Every libssl/libcrypto function this file calls.  OpenSSL 3.0 to 3.5 and
;;; LibreSSL 3+ export all of them; SSL_CTX_set_min_proto_version and
;;; SSL_set_tlsext_host_name are reached through SSL_CTX_ctrl/SSL_ctrl, which
;;; both libraries implement for these command numbers.
(defparameter *fnn-tls-required-symbols*
  '("OpenSSL_version_num" "OpenSSL_version" "ERR_clear_error" "ERR_get_error"
    "ERR_reason_error_string" "TLS_server_method" "TLS_client_method"
    "SSL_CTX_new" "SSL_CTX_free" "SSL_CTX_ctrl"
    "SSL_CTX_use_certificate_chain_file" "SSL_CTX_use_PrivateKey_file"
    "SSL_CTX_set_default_passwd_cb" "SSL_CTX_check_private_key"
    "SSL_CTX_set_verify" "SSL_CTX_load_verify_locations"
    ;; PKT-613: a named peer anchored on the system's public roots.
    "SSL_CTX_set_default_verify_paths" "SSL_new" "SSL_free"
    "SSL_set_fd" "SSL_accept" "SSL_connect" "SSL_set1_host" "SSL_ctrl"
    "SSL_get_verify_result" "SSL_get_error" "SSL_pending" "SSL_read"
    "SSL_write" "SSL_shutdown"
    ;; `tls reload' and the served line (PRF-212): the leaf and its facts.
    ;; OpenSSL 1.1+ and LibreSSL 2.7+ (OpenBSD 6.3) export all of them.
    "SSL_CTX_get0_certificate" "X509_get0_notBefore" "X509_get0_notAfter"
    "ASN1_STRING_get0_data" "ASN1_STRING_length" "X509_get_ext_by_NID"
    "X509_get_ext" "X509_EXTENSION_get_data"))

(defun fnn-tls-missing-symbols ()
  (remove-if #'sb-sys:find-foreign-symbol-address *fnn-tls-required-symbols*))

(defun fnn-tls-supported-version-p (number text)
  "OpenSSL 3.0 or later, or LibreSSL 3 or later (which reports 0x20000000
through OpenSSL_version_num and names itself in OpenSSL_version)."
  (or (>= number #x30000000)
      (and (stringp text)
           (> (length text) 9)
           (string= "LibreSSL " text :end2 9)
           (let ((major (parse-integer text :start 9 :junk-allowed t)))
             (and major (>= major 3))))))

(sb-alien:define-alien-routine ("OpenSSL_version_num" fnn-%openssl-version-num)
    sb-alien:unsigned-long)
(sb-alien:define-alien-routine ("OpenSSL_version" fnn-%openssl-version)
    sb-alien:c-string
  (selector sb-alien:int))
(sb-alien:define-alien-routine ("ERR_clear_error" fnn-%err-clear-error)
    sb-alien:void)
(sb-alien:define-alien-routine ("ERR_get_error" fnn-%err-get-error)
    sb-alien:unsigned-long)
(sb-alien:define-alien-routine ("ERR_reason_error_string" fnn-%err-reason-string)
    sb-alien:c-string
  (code sb-alien:unsigned-long))
(sb-alien:define-alien-routine ("TLS_server_method" fnn-%tls-server-method)
    (* t))
(sb-alien:define-alien-routine ("TLS_client_method" fnn-%tls-client-method) (* t))
(sb-alien:define-alien-routine ("SSL_CTX_new" fnn-%ssl-ctx-new)
    (* t)
  (method (* t)))
(sb-alien:define-alien-routine ("SSL_CTX_free" fnn-%ssl-ctx-free)
    sb-alien:void
  (context (* t)))
(sb-alien:define-alien-routine ("SSL_CTX_ctrl" fnn-%ssl-ctx-ctrl)
    sb-alien:long
  (context (* t)) (command sb-alien:int) (larg sb-alien:long) (parg (* t)))
(sb-alien:define-alien-routine
    ("SSL_CTX_use_certificate_chain_file" fnn-%ssl-ctx-use-chain-file)
    sb-alien:int
  (context (* t)) (path sb-alien:c-string))
(sb-alien:define-alien-routine
    ("SSL_CTX_use_PrivateKey_file" fnn-%ssl-ctx-use-private-key-file)
    sb-alien:int
  (context (* t)) (path sb-alien:c-string) (filetype sb-alien:int))
(sb-alien:define-alien-routine
    ("SSL_CTX_set_default_passwd_cb" fnn-%ssl-ctx-set-default-passwd-cb)
    sb-alien:void
  (context (* t)) (callback (* t)))
(sb-alien:define-alien-routine
    ("SSL_CTX_check_private_key" fnn-%ssl-ctx-check-private-key)
    sb-alien:int
  (context (* t)))
(sb-alien:define-alien-routine ("SSL_CTX_set_verify" fnn-%ssl-ctx-set-verify)
    sb-alien:void (context (* t)) (mode sb-alien:int) (callback (* t)))
(sb-alien:define-alien-routine ("SSL_CTX_load_verify_locations" fnn-%ssl-ctx-load-verify-locations)
    sb-alien:int (context (* t)) (cafile sb-alien:c-string) (capath sb-alien:c-string))
(sb-alien:define-alien-routine ("SSL_CTX_set_default_verify_paths"
                                fnn-%ssl-ctx-set-default-verify-paths)
    sb-alien:int (context (* t)))
(sb-alien:define-alien-routine ("SSL_new" fnn-%ssl-new)
    (* t)
  (context (* t)))
(sb-alien:define-alien-routine ("SSL_free" fnn-%ssl-free)
    sb-alien:void
  (ssl (* t)))
(sb-alien:define-alien-routine ("SSL_set_fd" fnn-%ssl-set-fd)
    sb-alien:int
  (ssl (* t)) (fd sb-alien:int))
(sb-alien:define-alien-routine ("SSL_accept" fnn-%ssl-accept)
    sb-alien:int
  (ssl (* t)))
(sb-alien:define-alien-routine ("SSL_connect" fnn-%ssl-connect) sb-alien:int (ssl (* t)))
(sb-alien:define-alien-routine ("SSL_set1_host" fnn-%ssl-set1-host)
    sb-alien:int (ssl (* t)) (hostname sb-alien:c-string))
(sb-alien:define-alien-routine ("SSL_ctrl" fnn-%ssl-ctrl)
    sb-alien:long (ssl (* t)) (command sb-alien:int) (larg sb-alien:long) (parg (* t)))
(sb-alien:define-alien-routine ("SSL_get_verify_result" fnn-%ssl-get-verify-result)
    sb-alien:long (ssl (* t)))
(sb-alien:define-alien-routine ("SSL_get_error" fnn-%ssl-get-error)
    sb-alien:int
  (ssl (* t)) (result sb-alien:int))
(sb-alien:define-alien-routine ("SSL_pending" fnn-%ssl-pending)
    sb-alien:int
  (ssl (* t)))
(sb-alien:define-alien-routine ("SSL_read" fnn-%ssl-read)
    sb-alien:int
  (ssl (* t)) (buffer (* sb-alien:unsigned-char)) (count sb-alien:int))
(sb-alien:define-alien-routine ("SSL_write" fnn-%ssl-write)
    sb-alien:int
  (ssl (* t)) (buffer (* sb-alien:unsigned-char)) (count sb-alien:int))
(sb-alien:define-alien-routine ("SSL_shutdown" fnn-%ssl-shutdown)
    sb-alien:int
  (ssl (* t)))
(sb-alien:define-alien-routine ("SSL_CTX_get0_certificate" fnn-%ssl-ctx-get0-certificate)
    (* t) (context (* t)))
(sb-alien:define-alien-routine ("X509_get0_notBefore" fnn-%x509-get0-not-before)
    (* t) (x509 (* t)))
(sb-alien:define-alien-routine ("X509_get0_notAfter" fnn-%x509-get0-not-after)
    (* t) (x509 (* t)))
(sb-alien:define-alien-routine ("ASN1_STRING_get0_data" fnn-%asn1-string-get0-data)
    (* sb-alien:unsigned-char) (string (* t)))
(sb-alien:define-alien-routine ("ASN1_STRING_length" fnn-%asn1-string-length)
    sb-alien:int (string (* t)))
(sb-alien:define-alien-routine ("X509_get_ext_by_NID" fnn-%x509-get-ext-by-nid)
    sb-alien:int (x509 (* t)) (nid sb-alien:int) (lastpos sb-alien:int))
(sb-alien:define-alien-routine ("X509_get_ext" fnn-%x509-get-ext)
    (* t) (x509 (* t)) (location sb-alien:int))
(sb-alien:define-alien-routine ("X509_EXTENSION_get_data" fnn-%x509-extension-get-data)
    (* t) (extension (* t)))
(sb-alien:define-alien-routine ("recv" fnn-%recv-peek)
    sb-alien:long
  (fd sb-alien:int) (buffer (* sb-alien:unsigned-char))
  (count sb-alien:unsigned-long) (flags sb-alien:int))

; Encrypted private keys are outside the native v0 configuration profile.
; Returning zero makes OpenSSL refuse them without consulting a terminal or
; consuming the operator's stdin through its default password callback.
(sb-alien:define-alien-callable fnn-%tls-no-password sb-alien:int
  ((buffer (* sb-alien:unsigned-char)) (size sb-alien:int)
   (rwflag sb-alien:int) (userdata (* t)))
  (declare (ignore buffer size rwflag userdata))
  0)

(defun fnn-tls-pointer (vector &optional (offset 0))
  (sb-alien:sap-alien (sb-sys:sap+ (sb-sys:vector-sap vector) offset)
                      (* sb-alien:unsigned-char)))

(defun fnn-tls-null-pointer-p (pointer)
  (sb-alien:null-alien pointer))

(defun fnn-tls-null-pointer ()
  (sb-alien:sap-alien (sb-sys:int-sap 0) (* t)))

(defun fnn-tls-error-stack ()
  (let ((reasons nil))
    (loop for code = (fnn-%err-get-error) until (zerop code) do
      (let ((reason (fnn-%err-reason-string code)))
        (push (if reason reason (format nil "OpenSSL error 0x~x" code)) reasons)))
    (if reasons
        (format nil "~{~a~^; ~}" (nreverse reasons))
      "OpenSSL reported no queued detail")))

(defun fnn-tls-load-libraries ()
  "Select one complete pair before loading either member; never mix fallback."
  (let* ((candidates (fnn-tls-library-candidates))
         (pair (or *fnn-tls-pinned-libraries*
                   (find-if (lambda (candidate)
                              (and (probe-file (first candidate))
                                   (probe-file (second candidate))))
                            candidates)
                   (find-if (lambda (candidate)
                              (and (not (char= (char (first candidate) 0) #\/))
                                   (not (char= (char (second candidate) 0) #\/))))
                            candidates))))
    (unless pair
      (error 'fnn-tls-unavailable
             :detail "no complete OpenSSL libcrypto/libssl pair exists"))
    ;; Pin one pair for this process incarnation.  The foreign objects are
    ;; omitted from saved cores, so restart can select the frozen bundle's
    ;; paths without mixing two OpenSSL versions in one process.
    (setq *fnn-tls-pinned-libraries* pair)
    (handler-case
        (progn
          (sb-alien:load-shared-object (first pair) :dont-save t)
          (sb-alien:load-shared-object (second pair) :dont-save t)
          pair)
      (error (condition)
        (error 'fnn-tls-unavailable
               :detail (format nil "pinned OpenSSL pair cannot be loaded: ~a"
                               condition))))))

(defun fnn-tls-initialize ()
  "Load the system libssl pair once and check its version and symbols.  This establishes facility availability, not a
configured server context and never a protected client session."
  (sb-thread:with-mutex (*fnn-tls-initialize-lock*)
    (case *fnn-tls-state*
      (:ready t)
      (:unavailable
       (error 'fnn-tls-unavailable
              :detail "OpenSSL was unavailable during initialization"))
      (t
       (handler-case
           (progn
             (setq *fnn-tls-libraries* (fnn-tls-load-libraries))
             (let ((missing (fnn-tls-missing-symbols)))
               (when missing
                 (error 'fnn-tls-unavailable
                        :detail (format nil "the TLS library lacks ~{~a~^, ~}"
                                        missing))))
             (let ((number (fnn-%openssl-version-num))
                   (text (fnn-%openssl-version 0)))
               (unless (fnn-tls-supported-version-p number text)
                 (error 'fnn-tls-unavailable
                        :detail (format nil "OpenSSL 3.0+ or LibreSSL 3+ required; found ~a (0x~x)"
                                        text number))))
             (setq *fnn-tls-version* (fnn-%openssl-version 0)
                   *fnn-tls-state* :ready)
             t)
         (fnn-tls-error (condition)
           (setq *fnn-tls-state* :unavailable)
           (error condition))
         (error (condition)
           (setq *fnn-tls-state* :unavailable)
           (error 'fnn-tls-unavailable
                  :detail (format nil "OpenSSL ABI cannot initialize: ~a"
                                  condition))))))))

(defun fnn-tls-reset ()
  "Forget serialized loader readiness and pair before saved-image service."
  (sb-thread:with-mutex (*fnn-tls-initialize-lock*)
    (setq *fnn-tls-state* :uninitialized
          *fnn-tls-libraries* nil
          *fnn-tls-pinned-libraries* nil
          *fnn-tls-version* nil))
  t)

;; test-only (tools/host_callers.py): tests/native_tls_transport.lisp
(defun fnn-tls-version ()
  (fnn-tls-initialize)
  (list *fnn-tls-libraries* *fnn-tls-version*))

(defconstant +fnn-tls-nid-subject-alt-name+ 85)
;; A certificate's times and its subjectAltName extension are a few dozen
;; to a few thousand octets; this is a work bound on one copy, far above
;; any certificate a CA issues, and a larger one is reported absent (so ACL2
;; refuses it by name) rather than copied.
(defconstant +fnn-tls-max-fact-octets+ 65536)

(defun fnn-tls-asn1-octets (string)
  "The contents octets of one ASN1_STRING, as a list, or NIL."
  (if (fnn-tls-null-pointer-p string)
      nil
    (let ((count (fnn-%asn1-string-length string))
          (data (fnn-%asn1-string-get0-data string)))
      (if (or (not (integerp count)) (<= count 0) (> count +fnn-tls-max-fact-octets+)
              (sb-alien:null-alien data))
          nil
        (loop for i below count collect (sb-alien:deref data i))))))

(defun fnn-tls-leaf-facts (pointer)
  "The loaded leaf's notBefore and notAfter contents octets and its
subjectAltName extension value (NIL without one), for ACL2
(books/tls-reload.lisp fn-tlsr-facts).  The library parsed the certificate;
this copies three of its fields and decides nothing."
  (let ((leaf (fnn-%ssl-ctx-get0-certificate pointer)))
    (if (fnn-tls-null-pointer-p leaf)
        (values nil nil nil)
      (let* ((location (fnn-%x509-get-ext-by-nid
                        leaf +fnn-tls-nid-subject-alt-name+ -1))
             (extension (and (>= location 0) (fnn-%x509-get-ext leaf location)))
             (san (and extension (not (fnn-tls-null-pointer-p extension))
                       (fnn-tls-asn1-octets
                        (fnn-%x509-extension-get-data extension)))))
        (values (fnn-tls-asn1-octets (fnn-%x509-get0-not-before leaf))
                (fnn-tls-asn1-octets (fnn-%x509-get0-not-after leaf))
                san)))))

(defun fnn-tls-server-candidate (certificate-path private-key-path)
  "Build one server SSL_CTX from the pair and report what the library
observed.  Returns (values POINTER CHAIN KEY MATCH DETAIL): POINTER is the
context (the caller owns it and frees it), CHAIN, KEY and MATCH whether
SSL_CTX_use_certificate_chain_file, SSL_CTX_use_PrivateKey_file and
SSL_CTX_check_private_key returned 1 (the key and the chain are each
attempted; the match only when both loaded), and DETAIL the first failure's
text, the chain's before the key's.  A context the
library cannot create at all is a config error."
  (fnn-tls-initialize)
  (unless (and (stringp certificate-path) (> (length certificate-path) 0)
               (stringp private-key-path) (> (length private-key-path) 0))
    (error 'fnn-tls-config-error :detail "certificate and private-key paths are required"))
  (fnn-%err-clear-error)
  (let* ((method (fnn-%tls-server-method))
         (pointer (and (not (fnn-tls-null-pointer-p method))
                       (fnn-%ssl-ctx-new method))))
    (when (or (fnn-tls-null-pointer-p method)
              (fnn-tls-null-pointer-p pointer))
      (error 'fnn-tls-config-error
             :detail (format nil "server context creation failed: ~a"
                             (fnn-tls-error-stack))))
    (handler-case
        (progn
          ;; SSL_CTX_set_min_proto_version is a public macro over SSL_CTX_ctrl.
          (unless (= (fnn-%ssl-ctx-ctrl pointer
                                      +fnn-tls-ctrl-set-min-proto-version+
                                      +fnn-tls-version-1-2+
                                      (fnn-tls-null-pointer))
                     1)
            (error 'fnn-tls-config-error
                   :detail (format nil "cannot require TLS 1.2+: ~a"
                                   (fnn-tls-error-stack))))
          ;; The key first, then the chain.  SSL_CTX_use_PrivateKey_file
          ;; after a certificate refuses a key that does not match it, which
          ;; would report a readable key as unloadable; loaded before the
          ;; chain, a key that does not belong to the leaf is dropped when the
          ;; leaf is set (OpenSSL 3 and LibreSSL ssl_set_cert), so the three
          ;; observations stay distinct: key readable, chain readable, match.
          (fnn-%ssl-ctx-set-default-passwd-cb
           pointer
           (sb-alien:cast
            (sb-alien:alien-callable-function 'fnn-%tls-no-password) (* t)))
          (fnn-%err-clear-error)
          (let* ((key (= (fnn-%ssl-ctx-use-private-key-file
                          pointer private-key-path +fnn-tls-filetype-pem+) 1))
                 ;; friend-path-2: a missing key file said "encrypted keys
                 ;; are unsupported" (OpenSSL's error 0x80000002 is ENOENT);
                 ;; the observation names which it is.
                 (key-detail
                   (unless key
                     (if (null (ignore-errors (sb-posix:stat private-key-path)))
                         (format nil "private key ~a does not exist or cannot be read: ~a"
                                 private-key-path (fnn-tls-error-stack))
                       (format nil "private key ~a cannot be loaded; encrypted keys are unsupported (fn takes an unencrypted PEM key): ~a"
                               private-key-path (fnn-tls-error-stack)))))
                 (chain (progn (fnn-%err-clear-error)
                               (= (fnn-%ssl-ctx-use-chain-file pointer certificate-path) 1)))
                 (chain-detail
                   (unless chain
                     (format nil "certificate chain ~a cannot be loaded: ~a"
                             certificate-path (fnn-tls-error-stack)))))
            (unless (and chain key)
              (return-from fnn-tls-server-candidate
                (values pointer chain key nil (or chain-detail key-detail))))
            (fnn-%err-clear-error)
            (unless (= (fnn-%ssl-ctx-check-private-key pointer) 1)
              (return-from fnn-tls-server-candidate
                (values pointer t t nil
                        (format nil "certificate/private-key mismatch: ~a"
                                (fnn-tls-error-stack))))))
          (values pointer t t t nil))
      (error (condition)
        (fnn-%ssl-ctx-free pointer)
        (error condition)))))

(defun fnn-tls-open-context (certificate-path private-key-path)
  "Load and validate one server certificate chain/private-key pair."
  (multiple-value-bind (pointer chain key match detail)
      (fnn-tls-server-candidate certificate-path private-key-path)
    (unless (and chain key match)
      (fnn-%ssl-ctx-free pointer)
      (error 'fnn-tls-config-error :detail detail))
    (fnn-tls-context-make :pointer pointer
                          :certificate-path certificate-path
                          :private-key-path private-key-path)))

(defun fnn-tls-context-swap (context pointer served)
  "Serve POINTER (and SERVED, ACL2's accepted decision) to every session
that starts after this returns; free the pointer it replaces.  A session
already open holds its own reference to the old SSL_CTX (SSL_new took it),
so freeing here only drops the context's reference."
  (let ((old nil))
    (sb-thread:with-mutex ((fnn-tls-context-lock context))
      (setq old (fnn-tls-context-pointer context))
      (setf (fnn-tls-context-pointer context) pointer
            (fnn-tls-context-served context) served))
    (when old (fnn-%ssl-ctx-free old))
    t))

(defun fnn-tls-open-client-context (trust)
  "Create a peer-verifying client context rooted in TRUST.

TRUST is the fourth element of ACL2's `fn-peer-tls-verification' answer:
(:PINNED PATH) roots the chain only in the certificates of PATH, and
(:SYSTEM-ROOTS) in the library's default store (SSL_CTX_set_default_verify_paths:
the system bundle, or SSL_CERT_FILE/SSL_CERT_DIR where the library honours
them).  Nothing else opens a client context."
  (fnn-tls-initialize)
  (let ((pinned (and (consp trust) (eq (first trust) :pinned) (second trust)))
        (system (equal trust '(:system-roots))))
    (unless (or system
                (and (stringp pinned) (> (length pinned) 0)
                     (null (position (code-char 0) pinned))))
      (error 'fnn-tls-config-error :detail "a trust-anchor path or the system roots is required"))
    (let* ((method (fnn-%tls-client-method))
           (pointer (and (not (fnn-tls-null-pointer-p method)) (fnn-%ssl-ctx-new method))))
      (when (or (fnn-tls-null-pointer-p method) (fnn-tls-null-pointer-p pointer))
        (error 'fnn-tls-config-error :detail "client context creation failed"))
      (handler-case
          (progn
            (unless (= (fnn-%ssl-ctx-ctrl pointer +fnn-tls-ctrl-set-min-proto-version+
                                          +fnn-tls-version-1-2+ (fnn-tls-null-pointer)) 1)
              (error 'fnn-tls-config-error :detail "cannot require TLS 1.2+"))
            (fnn-%ssl-ctx-set-verify pointer +fnn-tls-verify-peer+ (fnn-tls-null-pointer))
            (if system
                (unless (= (fnn-%ssl-ctx-set-default-verify-paths pointer) 1)
                  (error 'fnn-tls-config-error
                         :detail (format nil "the system trust roots cannot be loaded: ~a"
                                         (fnn-tls-error-stack))))
              (unless (= (fnn-%ssl-ctx-load-verify-locations pointer pinned nil) 1)
                (error 'fnn-tls-config-error
                       :detail (format nil "trust anchor ~a cannot be loaded: ~a"
                                       pinned (fnn-tls-error-stack)))))
            (fnn-tls-context-make :pointer pointer
                                  :certificate-path (or pinned "system-roots")))
        (error (condition) (fnn-%ssl-ctx-free pointer) (error condition))))))

(defun fnn-tls-verify-failure (ssl)
  "The verification outcome of a failed client handshake, or NIL."
  (let ((result (fnn-%ssl-get-verify-result ssl)))
    (cond ((zerop result) nil)
          ((member result '(62 64)) (values :name-mismatch result))
          (t (values :certificate result)))))

(defun fnn-tls-connect (context fd server-name seconds &key (sni t))
  "Complete an authenticated client handshake with chain and hostname checks.

SERVER-NAME is always the SSL_set1_host name; it is sent as SNI only when SNI
is true (ACL2 decides: a DNS name, never an address literal, RFC 6066 s3)."
  (unless (and (stringp server-name) (> (length server-name) 0)
               (null (position (code-char 0) server-name)))
    (error 'fnn-tls-config-error :detail "a TLS server name is required"))
  (let ((ssl (fnn-%ssl-new (fnn-tls-context-pointer context)))
        (deadline (fnn-tls-deadline seconds))
        (sni-octets (fnn-octets (append (map 'list #'char-code server-name) '(0)))))
    (when (fnn-tls-null-pointer-p ssl)
      (error 'fnn-tls-handshake-error :detail "SSL_new failed"))
    (handler-case
        (progn
          (unless (and (= (fnn-%ssl-set-fd ssl fd) 1)
                       (= (fnn-%ssl-set1-host ssl server-name) 1)
                       (or (not sni)
                           (sb-sys:with-pinned-objects (sni-octets)
                             (= (fnn-%ssl-ctrl ssl +fnn-tls-ctrl-set-tlsext-hostname+
                                               +fnn-tls-tlsext-nametype-host-name+
                                               (sb-alien:cast (fnn-tls-pointer sni-octets) (* t)))
                                1))))
            (error 'fnn-tls-handshake-error :detail "client TLS parameters failed"))
          (loop
            (let ((result (fnn-%ssl-connect ssl)))
              (when (= result 1)
                (multiple-value-bind (outcome code) (fnn-tls-verify-failure ssl)
                  (when outcome
                    (error 'fnn-tls-verify-error :outcome outcome
                           :detail (format nil "certificate verification failed for ~a (~a, ~d)"
                                           server-name outcome code))))
                (return (fnn-tls-channel-make :pointer ssl :fd fd)))
              (let ((disposition (fnn-tls-retry-direction ssl result)))
                (if (member disposition '(:input :output))
                    (fnn-tls-wait fd disposition deadline 'fnn-tls-handshake-error)
                  (multiple-value-bind (outcome code) (fnn-tls-verify-failure ssl)
                    (if outcome
                        (error 'fnn-tls-verify-error :outcome outcome
                               :detail (format nil "certificate refused for ~a (~a, ~d)"
                                               server-name outcome code))
                      (fnn-tls-operation-error 'fnn-tls-handshake-error "client handshake"
                                               disposition))))))))
      (error (condition) (fnn-%ssl-free ssl) (error condition)))))

(defun fnn-tls-close-context (context)
  (when context
    (let ((pointer nil))
      (sb-thread:with-mutex ((fnn-tls-context-lock context))
        (setq pointer (fnn-tls-context-pointer context))
        (setf (fnn-tls-context-pointer context) nil))
      (when pointer (fnn-%ssl-ctx-free pointer))))
  nil)

(defun fnn-tls-deadline (seconds)
  (when (< seconds 0) (error 'fnn-tls-io-error :detail "negative TLS timeout"))
  (+ (fnn-now) (* seconds internal-time-units-per-second)))

(defun fnn-tls-wait (fd direction deadline kind)
  (let ((remaining (fnn-seconds-to-deadline deadline)))
    (when (or (<= remaining 0)
              (not (funcall *fnn-fd-waiter* fd direction remaining)))
      (error kind :detail "operation timed out"))))

(defun fnn-tls-retry-direction (ssl result)
  "Call SSL_get_error immediately after RESULT, before another OpenSSL call."
  (let ((code (fnn-%ssl-get-error ssl result)))
    (cond ((= code +fnn-tls-error-want-read+) :input)
          ((= code +fnn-tls-error-want-write+) :output)
          ((= code +fnn-tls-error-zero-return+) :closed)
          ((= code +fnn-tls-error-syscall+) :syscall)
          (t (list :ssl code)))))

(defun fnn-tls-operation-error (kind operation disposition)
  (error kind :detail
         (case disposition
           (:closed (format nil "~a: peer closed TLS" operation))
           (:syscall (format nil "~a: transport syscall failed: ~a"
                             operation (fnn-tls-error-stack)))
           (otherwise
            (format nil "~a failed (~s): ~a"
                    operation disposition (fnn-tls-error-stack))))))

(defun fnn-tls-accept (context fd seconds)
  "Complete a nonblocking server handshake and return a live TLS channel."
  (let ((ssl nil) (deadline (fnn-tls-deadline seconds)))
    (fnn-%err-clear-error)
    ;; Under the context's lock: `tls reload' swaps the pointer (PRF-212).
    (sb-thread:with-mutex ((fnn-tls-context-lock context))
      (let ((pointer (fnn-tls-context-pointer context)))
        (unless pointer
          (error 'fnn-tls-handshake-error :detail "the TLS context is closed"))
        (setq ssl (fnn-%ssl-new pointer))))
    (when (fnn-tls-null-pointer-p ssl)
      (error 'fnn-tls-handshake-error
             :detail (format nil "SSL_new failed: ~a" (fnn-tls-error-stack))))
    (handler-case
        (progn
          (unless (= (fnn-%ssl-set-fd ssl fd) 1)
            (error 'fnn-tls-handshake-error
                   :detail (format nil "SSL_set_fd failed: ~a"
                                   (fnn-tls-error-stack))))
          (loop
            (fnn-%err-clear-error)
            (let ((result (fnn-%ssl-accept ssl)))
              (when (= result 1)
                (return (fnn-tls-channel-make :pointer ssl :fd fd)))
              (let ((disposition (fnn-tls-retry-direction ssl result)))
                (if (member disposition '(:input :output))
                    (fnn-tls-wait fd disposition deadline 'fnn-tls-handshake-error)
                  (fnn-tls-operation-error 'fnn-tls-handshake-error
                                           "handshake" disposition))))))
      (error (condition)
        (fnn-%ssl-free ssl)
        (error condition)))))

(defun fnn-tls-read (channel seconds &optional (limit +fnn-max-read+))
  "Read decrypted bytes, an empty vector at close_notify, or :timeout.
SSL_pending is checked before fd readiness so plaintext already buffered
inside OpenSSL cannot be stranded.  A zero-second call still performs one
nonblocking readiness poll, as FNN-RECV does.

An SSL_read that answers WANT_READ or WANT_WRITE has made no application data
available yet: it consumed a record that carries none (a TLS 1.3
NewSessionTicket or KeyUpdate), or part of a record.  That is FNN-RECV's
EAGAIN, not a failure: the call waits for the direction OpenSSL names until
its deadline and then answers :timeout, exactly as an idle socket does.  The
record layer keeps what it consumed, so the next call resumes it (defect M3:
the feed's zero-second read met the tickets fn's own TLS 1.3 server sends
after the handshake, signalled an I/O error, and dropped every link)."
  (let* ((ssl (fnn-tls-channel-pointer channel))
         (fd (fnn-tls-channel-fd channel))
         (deadline (fnn-tls-deadline seconds))
         (buffer (fnn-make-octets limit))
         (initialp t)
         (zero-poll-p (zerop seconds)))
    ;; Within one call, SSL_read retries keep the identical pinned
    ;; pointer/count, including WANT_READ changing to WANT_WRITE.  A later
    ;; call may use a fresh buffer: SSL_read keeps no reference to it across
    ;; a WANT_* return (fnn-tls-read-now relies on the same).
    (sb-sys:with-pinned-objects (buffer)
      (loop
        (when (and initialp (zerop (fnn-%ssl-pending ssl)))
          ;; Match the plaintext receive contract while no TLS operation has
          ;; begun: an idle deadline is not a connection failure.  Once
          ;; SSL_read has returned WANT_*, its retry stays inside this call.
          (let ((remaining (fnn-seconds-to-deadline deadline)))
            (when (and (<= remaining 0) (not zero-poll-p))
              (return :timeout))
            (unless (funcall *fnn-fd-waiter* fd :input remaining)
              (return :timeout))
            (setq zero-poll-p nil)))
        (setq initialp nil)
        (fnn-%err-clear-error)
        (let ((result
                (fnn-%ssl-read ssl (fnn-tls-pointer buffer) (length buffer))))
          (when (> result 0) (return (subseq buffer 0 result)))
          (let ((disposition (fnn-tls-retry-direction ssl result)))
            (cond ((eq disposition :closed) (return (fnn-make-octets 0)))
                  ((member disposition '(:input :output))
                   (let ((remaining (fnn-seconds-to-deadline deadline)))
                     (unless (and (> remaining 0)
                                  (funcall *fnn-fd-waiter* fd disposition
                                           remaining))
                       (return :timeout))))
                  (t (fnn-tls-operation-error 'fnn-tls-io-error
                                              "read" disposition)))))))))

(defun fnn-tls-send-all (channel octets seconds)
  "Write all bytes under one deadline.  A WANT retry uses the identical
pointer and length required by SSL_write's retry contract."
  (let* ((ssl (fnn-tls-channel-pointer channel))
         (fd (fnn-tls-channel-fd channel))
         (data (fnn-octets octets))
         (offset 0)
         (deadline (fnn-tls-deadline seconds)))
    (sb-sys:with-pinned-objects (data)
      (loop while (< offset (length data)) do
        (let ((count (- (length data) offset)))
          (loop
            (fnn-%err-clear-error)
            (let ((result (fnn-%ssl-write ssl (fnn-tls-pointer data offset) count)))
              (when (> result 0)
                (incf offset result)
                (return))
              (let ((disposition (fnn-tls-retry-direction ssl result)))
                (if (member disposition '(:input :output))
                    (fnn-tls-wait fd disposition deadline 'fnn-tls-io-error)
                  (fnn-tls-operation-error 'fnn-tls-io-error
                                           "write" disposition))))))))
    nil))

;;; The multiplexed served path (host/native/mux.lisp; lane
;;; connection-multiplexing, PKT-605).  The loop never waits inside OpenSSL:
;;; each operation below makes one attempt and answers what the descriptor
;;; must become ready for (:input or :output), and the loop polls for that.
;;; SSL_MODE_ENABLE_PARTIAL_WRITE (1) and SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER
;;; (2) let a write that returned WANT_* be retried from a vector the
;;; collector may have moved, with the remaining count; SSL_MODE_RELEASE_BUFFERS
;;; (16) frees an idle session's record buffers (the per-connection figure,
;;; books/connection-budget.lisp *fn-cbud-tls-octets*).  SSL_CTRL_MODE is 33.
(defconstant +fnn-tls-ctrl-mode+ 33)
(defconstant +fnn-tls-mux-modes+ (logior 1 2 16))

(defun fnn-tls-accept-begin (context fd)
  "A server session on FD for the loop's handshake, not yet started."
  (let ((ssl nil))
    (fnn-%err-clear-error)
    ;; Under the context's lock: `tls reload' swaps the pointer (PRF-212).
    (sb-thread:with-mutex ((fnn-tls-context-lock context))
      (let ((pointer (fnn-tls-context-pointer context)))
        (unless pointer
          (error 'fnn-tls-handshake-error :detail "the TLS context is closed"))
        (setq ssl (fnn-%ssl-new pointer))))
    (when (fnn-tls-null-pointer-p ssl)
      (error 'fnn-tls-handshake-error
             :detail (format nil "SSL_new failed: ~a" (fnn-tls-error-stack))))
    (unless (= (fnn-%ssl-set-fd ssl fd) 1)
      (fnn-%ssl-free ssl)
      (error 'fnn-tls-handshake-error
             :detail (format nil "SSL_set_fd failed: ~a" (fnn-tls-error-stack))))
    (fnn-%ssl-ctrl ssl +fnn-tls-ctrl-mode+ +fnn-tls-mux-modes+ (fnn-tls-null-pointer))
    ssl))

(defun fnn-tls-accept-step (ssl)
  "One SSL_accept attempt: :done, or :input/:output to wait for.  A failure
signals FNN-TLS-HANDSHAKE-ERROR; the caller frees SSL."
  (fnn-%err-clear-error)
  (let ((result (fnn-%ssl-accept ssl)))
    (if (= result 1)
        :done
      (let ((disposition (fnn-tls-retry-direction ssl result)))
        (if (member disposition '(:input :output))
            disposition
          (fnn-tls-operation-error 'fnn-tls-handshake-error "handshake"
                                   disposition))))))

(defun fnn-tls-channel-of (ssl fd)
  (fnn-tls-channel-make :pointer ssl :fd fd))

(defun fnn-tls-pending-p (channel)
  (and (fnn-tls-channel-pointer channel)
       (> (fnn-%ssl-pending (fnn-tls-channel-pointer channel)) 0)))

(defun fnn-tls-read-now (channel &optional (limit +fnn-max-read+) buffer)
  "One SSL_read attempt of at most LIMIT octets, into BUFFER when given (at
least LIMIT long; the caller's reused buffer), else a fresh one: decrypted
octets (empty at close_notify), or :input/:output when the session must
wait."
  (let ((ssl (fnn-tls-channel-pointer channel))
        (buffer (or buffer (fnn-make-octets limit))))
    (unless (<= limit (length buffer))
      (fnn-fault "TLS read buffer shorter than its limit"))
    (sb-sys:with-pinned-objects (buffer)
      (fnn-%err-clear-error)
      (let ((result (fnn-%ssl-read ssl (fnn-tls-pointer buffer) limit)))
        (if (> result 0)
            (subseq buffer 0 result)
          (let ((disposition (fnn-tls-retry-direction ssl result)))
            (cond ((eq disposition :closed) (fnn-make-octets 0))
                  ((member disposition '(:input :output)) disposition)
                  (t (fnn-tls-operation-error 'fnn-tls-io-error "read"
                                              disposition)))))))))

(defun fnn-tls-write-now (channel data offset)
  "One SSL_write attempt of DATA from OFFSET: the octets written, or
:input/:output when the session must wait."
  (let ((ssl (fnn-tls-channel-pointer channel))
        (count (- (length data) offset)))
    (sb-sys:with-pinned-objects (data)
      (fnn-%err-clear-error)
      (let ((result (fnn-%ssl-write ssl (fnn-tls-pointer data offset) count)))
        (if (> result 0)
            result
          (let ((disposition (fnn-tls-retry-direction ssl result)))
            (if (member disposition '(:input :output))
                disposition
              (fnn-tls-operation-error 'fnn-tls-io-error "write" disposition))))))))

(defun fnn-tls-close-channel (channel)
  "Fast shutdown is intentional: NNTP has already ended and the underlying
socket is closed immediately, so this channel is never reused."
  (when (and channel (fnn-tls-channel-pointer channel))
    (ignore-errors (fnn-%ssl-shutdown (fnn-tls-channel-pointer channel)))
    (fnn-%ssl-free (fnn-tls-channel-pointer channel))
    (setf (fnn-tls-channel-pointer channel) nil))
  nil)

(defvar *fnn-tls-peek-syscall*
  (lambda (fd buffer)
    (sb-sys:with-pinned-objects (buffer)
      (let ((result (fnn-%recv-peek fd (fnn-tls-pointer buffer)
                                    (length buffer) 2))) ; MSG_PEEK
        (if (< result 0)
            (values nil (sb-alien:get-errno))
          (values result nil)))))
  "Raw MSG_PEEK seam.  Tests bind it; production calls recv(2).")

(defun fnn-tls-peek-plaintext (fd seconds)
  "Observe, but do not consume, at most +fnn-max-read+ plaintext octets.
Return :TIMEOUT with no observation, matching FNN-RECV's idle behavior."
  (let ((deadline (fnn-tls-deadline seconds))
        (buffer (fnn-make-octets +fnn-max-read+)))
    (loop
      (let ((remaining (fnn-seconds-to-deadline deadline)))
        (when (or (<= remaining 0)
                  (not (funcall *fnn-fd-waiter* fd :input remaining)))
          (return :timeout)))
      (multiple-value-bind (count errno)
          (funcall *fnn-tls-peek-syscall* fd buffer)
        (cond ((and (null count) (fnn-eintr-p errno)) nil)
              ((and (null count) (fnn-would-block-p errno)) nil)
              ((null count) (fnn-os-fail errno))
              (t (return (subseq buffer 0 count))))))))

(defun fnn-tls-consume-plaintext (fd expected seconds)
  "Consume exactly EXPECTED after a peek.  Return EXPECTED or signal; a
short/error/mismatched consume must close the connection and must not cause
the caller to replay the already-applied ACL2 transition."
  (let* ((wanted (fnn-octets expected))
         (actual (fnn-make-octets (length wanted)))
         (offset 0)
         (deadline (fnn-tls-deadline seconds)))
    (loop while (< offset (length actual)) do
      (fnn-tls-wait fd :input deadline 'fnn-tls-io-error)
      (let* ((remaining (- (length actual) offset))
             (piece (fnn-make-octets remaining))
             (count (fnn-read-fd fd piece deadline t)))
        (cond ((eq count :would-block) nil)
              ((zerop count)
               (error 'fnn-tls-io-error
                      :detail "plaintext consume ended before the modeled prefix"))
              (t
               (replace actual piece :start1 offset :end2 count)
               (incf offset count)))))
    (unless (equalp actual wanted)
      (error 'fnn-tls-io-error
             :detail "plaintext bytes changed between peek and exact consume"))
    actual))
