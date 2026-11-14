;;; Physical OpenSSL state only. ACL2 supplies configuration and byte bounds;
;;; the adapter owns each handle for exactly one capability incarnation.
(in-package "ACL2")

(sb-alien:define-alien-routine ("fn2_tls_config" fn2-tls-%config) sb-sys:system-area-pointer
 (certificate sb-alien:c-string) (key sb-alien:c-string) (minimum sb-alien:int))
(sb-alien:define-alien-routine ("fn2_tls_config_free" fn2-tls-%config-free) sb-alien:void
 (config sb-sys:system-area-pointer))
(sb-alien:define-alien-routine ("fn2_tls_new" fn2-tls-%new) sb-sys:system-area-pointer
 (config sb-sys:system-area-pointer) (capacity sb-alien:unsigned-long))
(sb-alien:define-alien-routine ("fn2_tls_free" fn2-tls-%free) sb-alien:void
 (handle sb-sys:system-area-pointer))
(sb-alien:define-alien-routine ("fn2_tls_handshake" fn2-tls-%handshake) sb-alien:int
 (handle sb-sys:system-area-pointer))
(sb-alien:define-alien-routine ("fn2_tls_feed" fn2-tls-%feed) sb-alien:int
 (handle sb-sys:system-area-pointer) (bytes sb-sys:system-area-pointer) (length sb-alien:unsigned-long))
(sb-alien:define-alien-routine ("fn2_tls_drain" fn2-tls-%drain) sb-alien:int
 (handle sb-sys:system-area-pointer) (bytes sb-sys:system-area-pointer) (length sb-alien:unsigned-long))
(sb-alien:define-alien-routine ("fn2_tls_input_room" fn2-tls-%input-room) sb-alien:unsigned-long
 (handle sb-sys:system-area-pointer))
(sb-alien:define-alien-routine ("fn2_tls_output_pending" fn2-tls-%output-pending) sb-alien:unsigned-long
 (handle sb-sys:system-area-pointer))
(sb-alien:define-alien-routine ("fn2_tls_read" fn2-tls-%read) sb-alien:int
 (handle sb-sys:system-area-pointer) (bytes sb-sys:system-area-pointer)
 (length sb-alien:unsigned-long) (count (* sb-alien:unsigned-long)))
(sb-alien:define-alien-routine ("fn2_tls_write" fn2-tls-%write) sb-alien:int
 (handle sb-sys:system-area-pointer) (bytes sb-sys:system-area-pointer)
 (length sb-alien:unsigned-long) (count (* sb-alien:unsigned-long)))

(defstruct fn2-native-tls
 input output seed transport (input-length 0) (input-offset 0) (seed-length 0) (seed-offset 0) (output-offset 0) (output-length 0)
 ;; The external library's requested readiness; KICK schedules a bounded
 ;; first call or a call that can consume already-buffered transport data.
 (interest 1) (kick t))

(defun fn2-native-tls-open (quantum seed-capacity)
 ;; No SSL allocation here: the logical controller selects that action.
 (make-fn2-native-tls :transport (create-fn2-tls-transport)
   :seed (make-array seed-capacity :element-type '(unsigned-byte 8) :initial-element 0)
   :input (make-array quantum :element-type '(unsigned-byte 8) :initial-element 0)
   :output (make-array quantum :element-type '(unsigned-byte 8) :initial-element 0)))

(defun fn2-native-tls-handle (tls)
 ;; The physical pointer conversion has no independent ownership decision.
 (sb-sys:int-sap (fn2-tls-transport-handle (fn2-native-tls-transport tls))))

(defun fn2-native-tls-close (tls cap-index nonce host)
 "Retire the matching capability and consume its reserved free action once."
 (when tls
  (multiple-value-bind (status ledger)
      (fn2-tls-transport-retire cap-index nonce (fn2-native-tls-transport tls))
   (setf (fn2-native-tls-transport tls) ledger)
   (case status
    (:done nil)
    (:closing
     (multiple-value-bind (selected action offset count serial updated)
         (fn2-tls-transport-next 0 0 ledger)
      (setf ledger updated (fn2-native-tls-transport tls) updated)
      (unless (eq selected :cleanup) (error "fn2 TLS: cleanup ownership refused"))
      (multiple-value-bind (raw errno)
          (fn2-native-tls-perform tls action offset count -1 host nil 0)
       (multiple-value-bind (observed kick updated)
           (fn2-tls-transport-observe cap-index nonce
             (fn2-tls-transport-slot 0 ledger) (fn2-tls-transport-generation 0 ledger)
             serial raw 0 errno ledger)
        (declare (ignore kick))
        (setf (fn2-native-tls-transport tls) updated)
        (unless (eq observed :ok) (error "fn2 TLS: free observation refused"))
        (multiple-value-bind (closed updated)
            (fn2-tls-transport-retire cap-index nonce updated)
         (setf (fn2-native-tls-transport tls) updated)
         (unless (eq closed :done) (error "fn2 TLS: handle remained live after free")))))))
    (otherwise (error "fn2 TLS: retiring a stale or pending capability refused"))))))

(defun fn2-native-tls-span (total offset room quantum)
 (multiple-value-bind (code count) (fn2-host-tls-span total offset room quantum)
  (unless (eq code :ok) (error "fn2 TLS: transport span observation refused"))
  count))

(defun fn2-native-tls-stage-span (total offset capacity quantum)
 (multiple-value-bind (code count) (fn2-host-tls-stage-span total offset capacity quantum)
  (unless (eq code :ok) (error "fn2 TLS: staging span observation refused"))
  count))

(defun fn2-native-tls-record (tls writep address length)
 (sb-alien:with-alien ((count sb-alien:unsigned-long))
  (setf count 0)
  (let ((code (if writep
                 (fn2-tls-%write (fn2-native-tls-handle tls) address length (sb-alien:addr count))
               (fn2-tls-%read (fn2-native-tls-handle tls) address length (sb-alien:addr count)))))
   (values code count))))

(defun fn2-native-tls-output-empty-p (tls)
 (and (= (fn2-native-tls-output-offset tls) (fn2-native-tls-output-length tls))
      (zerop (fn2-tls-%output-pending (fn2-native-tls-handle tls)))))

(defun fn2-native-tls-flush (tls fd host)
 "At most one bounded BIO drain and one nonblocking send. Retain short writes."
 (let ((buffer (fn2-native-tls-output tls)))
  (sb-sys:with-pinned-objects (buffer)
   (when (= (fn2-native-tls-output-offset tls) (fn2-native-tls-output-length tls))
    (let ((n (fn2-tls-%drain (fn2-native-tls-handle tls) (sb-sys:vector-sap buffer) (length buffer))))
     (when (minusp n) (return-from fn2-native-tls-flush :failed))
     (setf (fn2-native-tls-output-offset tls) 0 (fn2-native-tls-output-length tls) n)))
   (let* ((off (fn2-native-tls-output-offset tls))
          (remaining (fn2-native-tls-span (fn2-native-tls-output-length tls) off (length buffer) (length buffer))))
    (when (zerop remaining) (return-from fn2-native-tls-flush :empty))
    (fn2-n-boundary host "tls-send")
    (multiple-value-bind (n errno) (fn2-native-send fd (sb-sys:sap+ (sb-sys:vector-sap buffer) off) remaining)
     (cond ((and (minusp n) (fn2-n-again-p errno)) :blocked)
           ((<= n 0) :failed)
           (t (incf (fn2-native-tls-output-offset tls) n) :progress)))))))

(defun fn2-native-tls-fill (tls fd host)
 "Retain ciphertext until BIO accepts it; never overwrite pending input."
 (let* ((buffer (fn2-native-tls-input tls))
        (room (fn2-native-tls-span (length buffer) 0
                 (fn2-tls-%input-room (fn2-native-tls-handle tls)) (length buffer))))
  (when (zerop room) (return-from fn2-native-tls-fill :blocked))
  (sb-sys:with-pinned-objects (buffer)
   (when (= (fn2-native-tls-input-offset tls) (fn2-native-tls-input-length tls))
    (fn2-n-boundary host "tls-receive")
    (multiple-value-bind (n errno) (fn2-native-recv fd (sb-sys:vector-sap buffer) room)
     (cond ((and (minusp n) (fn2-n-again-p errno)) (return-from fn2-native-tls-fill :blocked))
           ((<= n 0) (return-from fn2-native-tls-fill :failed))
           (t (setf (fn2-native-tls-input-length tls) n (fn2-native-tls-input-offset tls) 0)))))
   (let* ((off (fn2-native-tls-input-offset tls))
          (n (fn2-native-tls-span (fn2-native-tls-input-length tls) off room (length buffer)))
          (fed (fn2-tls-%feed (fn2-native-tls-handle tls)
                 (sb-sys:sap+ (sb-sys:vector-sap buffer) off) n)))
    (unless (and (<= 0 fed) (<= fed n))
     (error "fn2 TLS: physical BIO input count contract failed"))
    (incf (fn2-native-tls-input-offset tls) fed)
    (if (plusp fed) :progress :blocked)))))

(defun fn2-native-tls-perform (tls action offset count fd host bytes address)
 "One physical action; its tag and bounded arguments came from ACL2."
 (let ((handle (fn2-native-tls-handle tls))
       (seed (fn2-native-tls-seed tls)) (input (fn2-native-tls-input tls))
       (output (fn2-native-tls-output tls)))
  (sb-sys:with-pinned-objects (bytes seed input output)
   (case action
    (1 (replace seed bytes :start1 offset :end1 (+ offset count)
                :start2 (+ address offset) :end2 (+ address offset count))
       (values count 0))
    (2 (values (fn2-tls-%feed handle (sb-sys:sap+ (sb-sys:vector-sap seed) offset) count) 0))
    (3 (values (fn2-tls-%feed handle (sb-sys:sap+ (sb-sys:vector-sap input) offset) count) 0))
    (4 (values (fn2-tls-%drain handle (sb-sys:vector-sap output) count) 0))
    (5 (fn2-n-boundary host "tls-send")
       (fn2-native-send fd (sb-sys:sap+ (sb-sys:vector-sap output) offset) count))
    (6 (fn2-n-boundary host "tls-receive")
       (fn2-native-recv fd (sb-sys:vector-sap input) count))
    (7 (fn2-n-boundary host "tls-handshake")
       (values (fn2-tls-%handshake handle) 0))
    (8 (fn2-n-boundary host "tls-start")
       (let ((allocated (fn2-tls-%new (fn2-nhost-tls-config host) offset)))
        (values (sb-sys:sap-int allocated) 0)))
    (9 (fn2-n-boundary host "tls-free")
       (fn2-tls-%free handle)
       (values 0 0))
    (otherwise (error "fn2 TLS: unknown logical physical action"))))))

(defun fn2-native-tls-handshake-step (tls fd host bytes address cap-index nonce slot generation)
 "Execute exactly the action selected by the concrete ACL2 transport ledger."
 (let ((ledger (fn2-native-tls-transport tls))
       (handle (fn2-native-tls-handle tls)))
  (multiple-value-bind (status action offset count serial updated)
      (fn2-tls-transport-next (fn2-tls-%input-room handle)
                              (fn2-tls-%output-pending handle) ledger)
   (setf ledger updated (fn2-native-tls-transport tls) updated)
   (unless (member status '(:act :cleanup))
    (return-from fn2-native-tls-handshake-step
      (values status (fn2-tls-transport-status-kick status) 1)))
   (multiple-value-bind (raw errno)
       (fn2-native-tls-perform tls action offset count fd host bytes address)
    (multiple-value-bind (observed kick updated)
        (fn2-tls-transport-observe cap-index nonce slot generation serial raw 0 errno ledger)
     (setf (fn2-native-tls-transport tls) updated)
     (values observed kick (fn2-tls-transport-action-interest action)))))))
