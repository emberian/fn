; ACL2-facing boundary for the operator's status report
; (books/native-live-status.lisp).  Every wrapper here returns one value and
; no `state': the offline report reads the Store the command just replayed,
; the owner's reply reads the Store, configuration and pins the owner
; carries, and neither can update what it reads.  Raw Lisp transports the
; octets and prints them; it renders no field.
(in-package "ACL2")
(include-book "../books/native-live-status")

(defun fn-native-live-status-host-offline (kind profile obs state)
  ; `status', `pins', `obligations' and `peer list' with no owner running:
  ; the Store and configuration this process replayed, no connection.
  (declare (xargs :stobjs state :mode :program))
  (fn-nls-offline-report kind profile
                         (f-get-global 'fn-store-sn state)
                         (f-get-global 'fn-store-cfg state)
                         obs))

(defun fn-native-live-status-host-answer (request cached obs state)
  ; The running owner's page for one FNLS request, under its mutex
  ; (host/native/control.lisp `fnn-control-live-status-answer'): (REPLY
  ; CACHED').  A request from offset 0 renders the report once into a
  ; buffer (`fn-nls-buffer'); a later page of the same kind is a substring
  ; of the buffer its first page stored (`fn-nls-cached-buffer',
  ; `fn-nls-page-of-buffer-is-reply').  CACHED is carried by the host and
  ; chosen here.  The carried octet sum is read, not extended in place:
  ; `fn-owner-headroom' stores its extension, this does not.
  (declare (xargs :stobjs state :mode :program))
  (let ((decoded (fn-nls-request-decode request)))
    (if (not (equal (car decoded) :live-status))
        (list (fn-nls-reply-encode :refused 0 nil nil) cached)
      (let* ((kind (cadr decoded))
             (offset (caddr decoded))
             (stored (fn-nls-cached-buffer kind offset cached))
             (buffer
              (or stored
                  (fn-nls-buffer
                   (fn-nls-live-report kind
                                       (fn-owner-store-profile state)
                                       (fn-owner-ocfg state)
                                       (if (boundp-global 'fn-owner-record-octets state)
                                           (f-get-global 'fn-owner-record-octets state)
                                         nil)
                                       obs)))))
        (list (fn-nls-page buffer offset)
              (if stored cached (fn-nls-cache-put kind buffer cached)))))))

(defun fn-native-live-status-host-requestp (octets)
  (declare (xargs :mode :program))
  (equal (car (fn-nls-request-decode octets)) :live-status))

(defun fn-native-live-status-host-request-encode (kind offset)
  (declare (xargs :mode :program))
  (fn-nls-request-encode kind offset))

(defun fn-native-live-status-host-client-step (acc total digest reply)
  (declare (xargs :mode :program))
  (fn-nls-client-step acc total digest reply))

(defun fn-native-live-status-host-route (socket-present outcome)
  (declare (xargs :mode :program))
  (fn-nls-route socket-present outcome))

(defun fn-native-live-status-host-max-frame ()
  (declare (xargs :mode :program))
  *fn-nls-max-frame*)

(defun fn-native-live-status-host-max-restarts ()
  (declare (xargs :mode :program))
  *fn-nls-max-restarts*)
