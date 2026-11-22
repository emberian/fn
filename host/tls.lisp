;;; Physical OpenSSL state only. ACL2 supplies configuration and byte bounds;
;;; the adapter owns each handle for exactly one capability incarnation.
(in-package "ACL2")

(sb-alien:define-alien-routine ("fn2_tls_config" fn2-tls-%config) sb-sys:system-area-pointer
 (certificate sb-alien:c-string) (key sb-alien:c-string) (minimum sb-alien:int))
(sb-alien:define-alien-routine ("fn2_tls_client_config" fn2-tls-%client-config) sb-sys:system-area-pointer
 (trust-file sb-alien:c-string) (peer sb-alien:c-string) (minimum sb-alien:int))
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
 input output seed transport config
 ;; The external library's requested readiness; KICK schedules a bounded
 ;; first call or a call that can consume already-buffered transport data.
 (interest 1) (kick t))

(defun fn2-native-tls-open (config quantum seed-capacity)
 ;; No SSL allocation here: the logical controller selects that action.
 (make-fn2-native-tls :config config :transport (create-fn2-tls-transport)
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





(defun fn2-native-tls-record (tls writep address length)
 (sb-alien:with-alien ((count sb-alien:unsigned-long))
  (setf count 0)
  (let ((code (if writep
                 (fn2-tls-%write (fn2-native-tls-handle tls) address length (sb-alien:addr count))
               (fn2-tls-%read (fn2-native-tls-handle tls) address length (sb-alien:addr count)))))
   (values code count))))









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
       (let ((allocated (fn2-tls-%new (fn2-native-tls-config tls) offset)))
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

(defun fn2-native-tls-record-perform (host tls fd action bytes address offset count)
 ;; BYTES and ADDRESS are the selected pool or private window, never a guessed loan.
 (sb-sys:with-pinned-objects (bytes)
  (case action
   ((12 13)
    (fn2-n-boundary host "tls-record")
    (multiple-value-bind (raw moved)
        (fn2-native-tls-record tls (= action 13)
         (sb-sys:sap+ (sb-sys:vector-sap bytes) address) count)
     (values raw moved 0)))
   (otherwise
    (multiple-value-bind (raw errno)
        (fn2-native-tls-perform tls action offset count fd host bytes address)
     (values raw 0 errno))))))

(defun fn2-native-tls-record-step (host slot tls fd)
 (let* ((op (aref (fn2-nhost-ops host) slot)) (bytes (fn2-nhost-bytes host))
        (handle (fn2-native-tls-handle tls)))
  (multiple-value-bind (status action address offset count serial transport record)
      (fn2-host-tls-record-next slot (fn2-nop-gen op)
       (fn2-tls-%input-room handle) (fn2-tls-%output-pending handle)
       (fn2-native-tls-transport tls) (fn2-nop-tls-record op) (fn2-nhost-core host))
   (setf (fn2-native-tls-transport tls) transport (fn2-nop-tls-record op) record)
   (unless (eq status :act) (return-from fn2-native-tls-record-step (values status count address)))
   (multiple-value-bind (raw moved errno)
       (fn2-native-tls-record-perform host tls fd action bytes address offset count)
    (multiple-value-bind (observed next-transport next-record)
        (fn2-tls-record-step-observe serial raw moved errno transport record)
     (setf (fn2-native-tls-transport tls) next-transport (fn2-nop-tls-record op) next-record)
     (unless (member observed '(:ok :blocked))
      (error "fn2 TLS: selected record observation refused: ~S" observed))
     (multiple-value-bind (effect relative-offset effect-count)
         (fn2-tls-record-public-input-prefix serial action offset moved next-record)
      (case effect
       (:input-prefix
        (fn2-n-record host (list :input-prefix slot (fn2-nop-gen op)
          relative-offset effect-count (fn2-n-octets host address effect-count))))
       (:none nil)
       (otherwise (error "fn2 TLS: accepted input effect refused: ~S" effect))))
     (values :progress 0 0))))))

(defun fn2-native-tls-child-step (host slot tls fd upper input output)
 ;; Upper remains pending until this child returns its logical terminal result.
 (let* ((op (aref (fn2-nhost-ops host) slot)) (handle (fn2-native-tls-handle tls)))
  (multiple-value-bind (status action channel offset count serial transport record)
      (fn2-host-tls-child-next slot (fn2-nop-gen op)
       (fn2-tls-%input-room handle) (fn2-tls-%output-pending handle)
       upper (fn2-native-tls-transport tls) (fn2-nop-tls-record op) (fn2-nhost-core host))
   (setf (fn2-native-tls-transport tls) transport (fn2-nop-tls-record op) record)
   (unless (eq status :act) (return-from fn2-native-tls-child-step (values status count)))
   (let ((bytes (case channel (2 input) (3 output) (0 (fn2-nhost-bytes host))
                 (otherwise (error "fn2 TLS: refused private channel")))))
    (multiple-value-bind (raw moved errno)
        (fn2-native-tls-record-perform host tls fd action bytes offset offset count)
     (multiple-value-bind (observed next-transport next-record)
         (fn2-tls-record-step-observe serial raw moved errno transport record)
      (setf (fn2-native-tls-transport tls) next-transport (fn2-nop-tls-record op) next-record)
      (unless (member observed '(:ok :blocked))
       (error "fn2 TLS: selected child observation refused: ~S" observed))
      (values :progress 0)))))))


(defun fn2-native-tls-mark-closed (host slot tls)
 ;; Core authorization binds even a never-started sibling before the carrier
 ;; disappears; a private child is settled by its upper codec instead.
 (let ((op (aref (fn2-nhost-ops host) slot)))
  (multiple-value-bind (code record)
      (fn2-host-tls-mark-closed slot (fn2-nop-gen op)
       (fn2-native-tls-transport tls) (fn2-nop-tls-record op) (fn2-nhost-core host))
   (setf (fn2-nop-tls-record op) record)
   (unless (member code '(:ok :kind :child :too-late))
    (error "fn2 TLS: closed carrier loan authorization refused: ~S" code)))))

(defun fn2-native-tls-cancel-result (host slot other)
 ;; Works for closed-waiting operations without looking up a live capability.
 (let ((cancel (aref (fn2-nhost-ops host) slot)))
  (multiple-value-bind (decision target code count won address record)
      (fn2-host-tls-cancel-result slot (fn2-nop-gen cancel)
       (fn2-nop-tls-record other) (fn2-nhost-core host))
   (setf (fn2-nop-tls-record other) record)
   (case decision
    ((:productive :cancelled)
     ;; Only productive input carries pool effects. Cancelled Send retains
     ;; accepted application count, not evidence of ciphertext delivery.
     (fn2-n-complete host target code count 0 nil
      (and (eq decision :productive) (fn2-n-octets host address count)))
     (fn2-n-complete host slot :ok 0 0 won)
     t)
    ((:unbound :kind) nil)
    (:too-late (fn2-n-complete host slot :ok 0 0 nil) t)
    (otherwise (error "fn2 TLS: cancellation authorization refused: ~S" decision))))))
