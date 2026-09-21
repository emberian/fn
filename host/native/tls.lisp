;;; Native TLS transport boundary.
;;;
;;; TLS protocol, record protection, certificate parsing and cryptography are
;;; delegated to the OpenSSL 3 libssl C ABI.  This file supplies bounded
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

(defstruct (fnn-tls-context (:constructor fnn-tls-context-make))
  pointer certificate-path private-key-path)

(defstruct (fnn-tls-channel (:constructor fnn-tls-channel-make))
  pointer fd)

(defvar *fnn-tls-state* :uninitialized)
(defvar *fnn-tls-libraries* nil)
(defvar *fnn-tls-version* nil)
(defvar *fnn-tls-initialize-lock*
  (sb-thread:make-mutex :name "fn native TLS initialization"))

(defun fnn-tls-library-candidates ()
  (cond
    ((member :darwin *features*)
     '(("/opt/homebrew/opt/openssl@3/lib/libcrypto.3.dylib"
        "/opt/homebrew/opt/openssl@3/lib/libssl.3.dylib")
       ("/usr/local/opt/openssl@3/lib/libcrypto.3.dylib"
        "/usr/local/opt/openssl@3/lib/libssl.3.dylib")
       ("libcrypto.3.dylib" "libssl.3.dylib")))
    ((member :linux *features*)
     '(("libcrypto.so.3" "libssl.so.3")))
    (t nil)))

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
  (let ((last-error nil))
    (dolist (pair (fnn-tls-library-candidates))
      (handler-case
          (progn
            ;; libssl depends on libcrypto.  Loading the dependency first is
            ;; required on platforms whose loader does not make it global.
            (sb-alien:load-shared-object (first pair))
            (sb-alien:load-shared-object (second pair))
            (return-from fnn-tls-load-libraries pair))
        (error (condition) (setq last-error condition))))
    (error 'fnn-tls-unavailable
           :detail (if last-error
                       (format nil "OpenSSL 3 cannot be loaded: ~a" last-error)
                     "OpenSSL 3 has no loader candidate on this platform"))))

(defun fnn-tls-initialize ()
  "Load OpenSSL 3 once.  This establishes facility availability, not a
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
             (let ((number (fnn-%openssl-version-num)))
               (unless (>= number #x30000000)
                 (error 'fnn-tls-unavailable
                        :detail (format nil "OpenSSL 3 required; ABI is 0x~x" number))))
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
  "Forget serialized loader readiness before a saved image enters service."
  (sb-thread:with-mutex (*fnn-tls-initialize-lock*)
    (setq *fnn-tls-state* :uninitialized
          *fnn-tls-libraries* nil
          *fnn-tls-version* nil))
  t)

(defun fnn-tls-version ()
  (fnn-tls-initialize)
  (list *fnn-tls-libraries* *fnn-tls-version*))

(defun fnn-tls-open-context (certificate-path private-key-path)
  "Load and validate one server certificate chain/private-key pair."
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
          (fnn-%err-clear-error)
          (unless (= (fnn-%ssl-ctx-use-chain-file pointer certificate-path) 1)
            (error 'fnn-tls-config-error
                   :detail (format nil "certificate chain ~a cannot be loaded: ~a"
                                   certificate-path (fnn-tls-error-stack))))
          (fnn-%ssl-ctx-set-default-passwd-cb
           pointer
           (sb-alien:cast
            (sb-alien:alien-callable-function 'fnn-%tls-no-password) (* t)))
          (fnn-%err-clear-error)
          (unless (= (fnn-%ssl-ctx-use-private-key-file
                      pointer private-key-path +fnn-tls-filetype-pem+) 1)
            (error 'fnn-tls-config-error
                   :detail (format nil "private key ~a cannot be loaded; encrypted keys are unsupported: ~a"
                                   private-key-path (fnn-tls-error-stack))))
          (fnn-%err-clear-error)
          (unless (= (fnn-%ssl-ctx-check-private-key pointer) 1)
            (error 'fnn-tls-config-error
                   :detail (format nil "certificate/private-key mismatch: ~a"
                                   (fnn-tls-error-stack))))
          (fnn-tls-context-make :pointer pointer
                                :certificate-path certificate-path
                                :private-key-path private-key-path))
      (error (condition)
        (fnn-%ssl-ctx-free pointer)
        (error condition)))))

(defun fnn-tls-open-client-context (trust-anchor-path)
  "Create a peer-verifying client context rooted only in TRUST-ANCHOR-PATH."
  (fnn-tls-initialize)
  (unless (and (stringp trust-anchor-path) (> (length trust-anchor-path) 0))
    (error 'fnn-tls-config-error :detail "a trust-anchor path is required"))
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
          (unless (= (fnn-%ssl-ctx-load-verify-locations pointer trust-anchor-path nil) 1)
            (error 'fnn-tls-config-error
                   :detail (format nil "trust anchor ~a cannot be loaded: ~a"
                                   trust-anchor-path (fnn-tls-error-stack))))
          (fnn-tls-context-make :pointer pointer :certificate-path trust-anchor-path))
      (error (condition) (fnn-%ssl-ctx-free pointer) (error condition)))))

(defun fnn-tls-connect (context fd server-name seconds)
  "Complete an authenticated client handshake with chain and hostname checks."
  (unless (and (stringp server-name) (> (length server-name) 0))
    (error 'fnn-tls-config-error :detail "a TLS server name is required"))
  (let ((ssl (fnn-%ssl-new (fnn-tls-context-pointer context)))
        (deadline (fnn-tls-deadline seconds))
        (sni (fnn-octets (append (map 'list #'char-code server-name) '(0)))))
    (when (fnn-tls-null-pointer-p ssl)
      (error 'fnn-tls-handshake-error :detail "SSL_new failed"))
    (handler-case
        (progn
          (unless (and (= (fnn-%ssl-set-fd ssl fd) 1)
                       (= (fnn-%ssl-set1-host ssl server-name) 1)
                       (sb-sys:with-pinned-objects (sni)
                         (= (fnn-%ssl-ctrl ssl +fnn-tls-ctrl-set-tlsext-hostname+
                                           +fnn-tls-tlsext-nametype-host-name+
                                           (sb-alien:cast (fnn-tls-pointer sni) (* t))) 1)))
            (error 'fnn-tls-handshake-error :detail "client TLS parameters failed"))
          (loop
            (let ((result (fnn-%ssl-connect ssl)))
              (when (= result 1)
                (unless (zerop (fnn-%ssl-get-verify-result ssl))
                  (error 'fnn-tls-handshake-error :detail "certificate verification failed"))
                (return (fnn-tls-channel-make :pointer ssl :fd fd)))
              (let ((disposition (fnn-tls-retry-direction ssl result)))
                (if (member disposition '(:input :output))
                    (fnn-tls-wait fd disposition deadline 'fnn-tls-handshake-error)
                  (fnn-tls-operation-error 'fnn-tls-handshake-error "client handshake"
                                           disposition))))))
      (error (condition) (fnn-%ssl-free ssl) (error condition)))))

(defun fnn-tls-close-context (context)
  (when (and context (fnn-tls-context-pointer context))
    (fnn-%ssl-ctx-free (fnn-tls-context-pointer context))
    (setf (fnn-tls-context-pointer context) nil))
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
    (setq ssl (fnn-%ssl-new (fnn-tls-context-pointer context)))
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
  "Read decrypted bytes.  SSL_pending is checked before fd readiness so
plaintext already buffered inside OpenSSL cannot be stranded."
  (let* ((ssl (fnn-tls-channel-pointer channel))
         (fd (fnn-tls-channel-fd channel))
         (deadline (fnn-tls-deadline seconds))
         (buffer (fnn-make-octets limit))
         (initialp t))
    ;; SSL_read retries keep the identical pinned pointer/count for the whole
    ;; operation, including WANT_READ changing to WANT_WRITE.
    (sb-sys:with-pinned-objects (buffer)
      (loop
        (when (and initialp (zerop (fnn-%ssl-pending ssl)))
          ;; Match the plaintext receive contract while no TLS operation has
          ;; begun: an idle deadline is not a connection failure.  Once
          ;; SSL_read has returned WANT_*, its retry stays inside this call.
          (let ((remaining (fnn-seconds-to-deadline deadline)))
            (when (or (<= remaining 0)
                      (not (funcall *fnn-fd-waiter* fd :input remaining)))
              (return :timeout))))
        (setq initialp nil)
        (fnn-%err-clear-error)
        (let ((result
                (fnn-%ssl-read ssl (fnn-tls-pointer buffer) (length buffer))))
          (when (> result 0) (return (subseq buffer 0 result)))
          (let ((disposition (fnn-tls-retry-direction ssl result)))
            (cond ((eq disposition :closed) (return (fnn-make-octets 0)))
                  ((member disposition '(:input :output))
                   (fnn-tls-wait fd disposition deadline 'fnn-tls-io-error))
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
