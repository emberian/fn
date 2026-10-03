;;; `operator CONFIG tls reload' and the served certificate line `status'
;;; prints (PRF-212, HST-020; control requests of FNCT kind 19, replies of
;;; kind 20, books/tls-reload.lisp).
;;;
;;; I/O only.  The owner's handler builds a candidate SSL_CTX from the paths
;;; `run' loaded (host/native/tls.lisp fnn-tls-server-candidate), copies the
;;; primitive facts the library observed (chain, key and match as booleans;
;;; the leaf's validity times and subjectAltName octets; the host clock), and
;;; asks ACL2 (fn-tlsr-decide) whether to take it.  On :accept it swaps the
;;; context's pointer under the context's lock (fnn-tls-context-swap): every
;;; handshake that starts after the swap uses the new pair, and a session
;;; already open keeps the SSL_CTX it was created from (SSL_new took a
;;; reference).  On a refusal it frees the candidate and the served context
;;; is untouched.  The log line and the reply's line are ACL2's octets.

(in-package "ACL2")

(defvar *fnn-tls-reload-mutex* (sb-thread:make-mutex :name "fn tls reload")
  "One reload at a time: two concurrent requests would each build a
candidate and the second would decide against stale served facts.")

(defun fnn-tls-unix-now ()
  "The host clock in seconds since 1970-01-01T00:00:00Z (a primitive
observation ACL2 compares with the validity window)."
  (- (get-universal-time) 2208988800))

(defun fnn-tls-facts-of (pointer chain key match)
  (multiple-value-bind (not-before not-after san)
      (if (and pointer chain) (fnn-tls-leaf-facts pointer) (values nil nil nil))
    (fnn-core 'fn-tlsr-host-facts (and chain t) (and key t) (and match t)
              not-before not-after san (fnn-tls-unix-now))))

(defun fnn-tls-start-context (certificate-path private-key-path)
  "PRF-387 (PKT-606): the server context `run' serves from.  The candidate is
built and observed exactly as a reload's (fnn-tls-server-candidate,
fnn-tls-facts-of), and ACL2 decides it (fn-tlsr-start-decide, the reload's
decision against no served material).  On :accept the context records those
facts as the material it serves, which establishes the relation
fnn-tls-context-swap preserves; on a refusal the candidate is freed and the
start is refused (exit 1) by ACL2's word, the library's text after it."
  (multiple-value-bind (pointer chain key match detail)
      (fnn-tls-server-candidate certificate-path private-key-path)
    (let* ((facts (fnn-tls-facts-of pointer chain key match))
           (decision (fnn-core 'fn-tlsr-host-start-decide facts)))
      (if (fnn-core 'fn-tlsr-host-acceptp decision)
          (fnn-tls-context-make :pointer pointer
                                :certificate-path certificate-path
                                :private-key-path private-key-path
                                :served facts)
        (progn
          (when pointer (fnn-%ssl-ctx-free pointer))
          (error 'fnn-store-error
                 :message (format nil "~a~@[ (~a)~]"
                                  (fnn-octets-string
                                   (fnn-octets
                                    (fnn-core 'fn-tlsr-host-start-refusal-line
                                              decision)))
                                  detail)))))))

(defun fnn-tls-served-facts (context)
  "The facts of the material CONTEXT serves: recorded by fnn-tls-start-context
when `run' opened it and replaced only by fnn-tls-context-swap, both under
the context's lock."
  (sb-thread:with-mutex ((fnn-tls-context-lock context))
    (fnn-tls-context-served context)))

(defun fnn-tls-owner-reload (service)
  (let ((context (fnn-owner-service-tls-context service)))
    (if (null context)
        (list :tls-reply :refused :no-tls-context
              (fnn-core 'fn-tlsr-host-reply-line nil))
      (sb-thread:with-mutex (*fnn-tls-reload-mutex*)
        (let ((served (fnn-tls-served-facts context)))
          (multiple-value-bind (pointer chain key match detail)
              (handler-case
                  (fnn-tls-server-candidate
                   (fnn-tls-context-certificate-path context)
                   (fnn-tls-context-private-key-path context))
                ;; No context could be created at all: nothing loaded.
                (fnn-tls-error (condition)
                  (values nil nil nil nil (fnn-tls-error-detail condition))))
            (let* ((facts (fnn-tls-facts-of pointer chain key match))
                   (decision (fnn-core 'fn-tlsr-host-decide facts served)))
              (when detail (fnn-err "tls reload: ~a" detail))
              (fnn-log-line (fnn-core 'fn-tlsr-host-log-line decision facts))
              (if (fnn-core 'fn-tlsr-host-acceptp decision)
                  (progn
                    (fnn-tls-context-swap context pointer facts)
                    (list :tls-reply :accepted nil
                          (fnn-core 'fn-tlsr-host-reply-line facts)))
                (progn
                  (when pointer (fnn-%ssl-ctx-free pointer))
                  (list :tls-reply :refused
                        (fnn-core 'fn-tlsr-host-refusal decision)
                        (fnn-core 'fn-tlsr-host-reply-line served)))))))))))

(defun fnn-tls-owner-status (service)
  (let ((context (fnn-owner-service-tls-context service)))
    (list :tls-reply :accepted nil
          (fnn-core 'fn-tlsr-host-reply-line
                    (and context (fnn-tls-served-facts context))))))

(defvar *fnn-tls-reload-next-handler* *fnn-hybrid-control-handler*)

(defun fnn-tls-control-handle (service frame)
  (let ((verb (and (typep frame 'fnn-octets)
                   (fnn-core 'fn-tlsr-host-request-decode
                             (fnn-control-frame-octet-list frame)))))
    (case verb
      (:reload (fnn-tls-owner-reload service))
      (:status (fnn-tls-owner-status service))
      (t (and *fnn-tls-reload-next-handler*
              (funcall *fnn-tls-reload-next-handler* service frame))))))

(setq *fnn-hybrid-control-handler* #'fnn-tls-control-handle)

(defun fnn-tls-request (control-path verb)
  "Ask the owner at CONTROL-PATH; answers ACL2's read of the reply,
(STATUS WORD LINE), or (values NIL STAGE) when no reply frame came."
  (multiple-value-bind (frame stage)
      (fnn-control-exchange control-path
                            (fnn-core 'fn-tlsr-host-request-encode verb))
    (let ((read (and frame (fnn-core 'fn-tlsr-host-reply-read
                                     (fnn-octet-list frame)))))
      (if (consp read)
          (values read stage)
        (values nil stage)))))

(defun fnn-tls-status-line (control-path-octets)
  "The line `status' prints after its report while an owner runs: the
served certificate's names and notAfter, or ACL2's `tls unknown REASON'."
  (let ((read (handler-case (fnn-tls-request (fnn-octets-string control-path-octets)
                                             :status)
                (error () nil))))
    (fnn-out "~a" (fnn-octets-string
                   (fnn-octets (fnn-core 'fn-tlsr-host-status-client-line read))))))

(defun fnn-tls-execute (result)
  "Execute an accepted `tls reload' plan over the control socket."
  (let* ((control (fnn-core
                   'fn-native-operator-host-result-tls-control-path-octets result))
         (control-path (and (fnn-octet-list-p control) (consp control)
                            (fnn-octets-string (fnn-octets control)))))
    (handler-case
        (if (null control-path)
            (progn (fnn-operator-emit-status :refused "tls"
                                             "the configuration names no control socket")
                   +fnn-exit-refused+)
          (multiple-value-bind (read stage) (fnn-tls-request control-path :reload)
            (if (null read)
                (let* ((status (fnn-control-transport-outcome stage))
                       (code (fnn-core 'fn-native-control-host-status-exit-code status)))
                  (fnn-operator-emit-status (fnn-operator-status-of-exit-code code) "tls")
                  code)
              (destructuring-bind (status word line) read
                (when (and (fnn-octet-list-p line) (consp line))
                  (fnn-out "~a" (fnn-octets-string (fnn-octets line))))
                (let ((code (fnn-core 'fn-native-control-host-status-exit-code status)))
                  (fnn-operator-emit-status
                   (fnn-operator-status-of-exit-code code) "tls"
                   (let ((detail (and (fnn-octet-list-p word)
                                      (fnn-core 'fn-native-control-host-reply-detail
                                                status word))))
                     (and (fnn-octet-list-p detail) (consp detail)
                          (fnn-octets-string (fnn-octets detail)))))
                  code)))))
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                    "tls" condition)
          code)))))
