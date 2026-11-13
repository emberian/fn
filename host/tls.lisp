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
 handle input output (output-offset 0) (output-length 0)
 ;; The external library's requested readiness; KICK schedules a bounded
 ;; first call or a call that can consume already-buffered transport data.
 (interest 1) (kick t))

(defun fn2-native-tls-open (config capacity quantum)
 (let ((handle (fn2-tls-%new config capacity)))
  (unless (zerop (sb-sys:sap-int handle))
   (make-fn2-native-tls :handle handle
     :input (make-array quantum :element-type '(unsigned-byte 8) :initial-element 0)
     :output (make-array quantum :element-type '(unsigned-byte 8) :initial-element 0)))))
(defun fn2-native-tls-close (tls)
 (when (and tls (fn2-native-tls-handle tls))
  (fn2-tls-%free (fn2-native-tls-handle tls))
  (setf (fn2-native-tls-handle tls) nil)))

(defun fn2-native-tls-record (tls writep address length)
 (sb-alien:with-alien ((count sb-alien:unsigned-long))
  (setf count 0)
  (let ((code (if writep
                 (fn2-tls-%write (fn2-native-tls-handle tls) address length (sb-alien:addr count))
               (fn2-tls-%read (fn2-native-tls-handle tls) address length (sb-alien:addr count)))))
   (values code count))))
