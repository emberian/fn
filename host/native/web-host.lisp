;;; The node's own web face (lane web-native, PRF-340, WEB-005): an HTTP/1.1
;;; listener in the native image.  I/O only.
;;;
;;; ACL2 decides every value (books/web-request.lisp, web-render.lisp,
;;; web-session.lisp, web-config.lisp through host/web-host.lisp): where the
;;; head ends, what the request is, which route it names and whether its
;;; capability holds, the browser's address, the session a token names, every
;;; NNTP command a page needs, every reply's meaning, every page's octets and
;;; every response head.  This file accepts a connection, moves its octets
;;; into `fn-web-in', calls `fn-web-host-step' for each event, performs the
;;; action ACL2 answers against the owner, and writes `fn-web-out'.
;;;
;;; A browser session is a LOGICAL READER CONNECTION of the owner, opened
;;; through the owner's own exposure admission for the browser's address
;;; (fn-owner-exposure-open, as host/native/mux.lisp fnn-mux-admit opens a
;;; socket's), fed through the owner's served step (fnn-owner-handle-chunk,
;;; class :reader, no socket: the pull feed's logical connection,
;;; host/native/pull-service.lisp), and closed as a socket's is
;;; (fn-owner-close, fn-owner-exposure-release).  So a web reader meets the
;;; same authentication, the same `account access' narrowing, the same
;;; exposure limits (login pacing included) and the same POST path as an
;;; NNTP reader: there is no second implementation of any of them.
;;;
;;; Work per connection is bounded: one request per connection (ACL2's head
;;; says Connection: close), the head within the profile's head limit and the
;;; body within the body limit ACL2 derived from the article limit (both
;;; checked by ACL2 before the octets are read), the whole request within
;;; fn-web-host-request-seconds, and at most fn-web-host-max-events events.
;;; One thread serves the face, one connection at a time: the two buffers
;;; are that thread's alone (a known limit: a friends' node, not a portal).

(in-package "ACL2")

(defstruct (fnn-web-face (:constructor %make-fnn-web-face))
  plan config limits listener thread tls-context service
  (stop nil))

(defvar *fnn-web-face* nil)

(defun fnn-web-live (sym)
  (or (cdr (assoc sym (user-stobj-alist *the-live-state*)))
      (fnn-fault "the ~(~a~) buffer is not in this image" sym)))

(defun fnn-web-fill (st vector)
  "Make VECTOR's bytes ST's contents (the same boundary as fnn-octets-fill)."
  (let ((n (length vector)))
    (fn-octets$c-reserve n st)
    (replace (the fnn-octets (svref st 0)) vector)
    (setf (svref st 1) n)
    st))

(defun fnn-web-append (st vector)
  (let ((fill (svref st 1)) (n (length vector)))
    (fn-octets$c-reserve (+ fill n) st)
    (replace (the fnn-octets (svref st 0)) vector :start1 fill)
    (setf (svref st 1) (+ fill n))
    st))

(defun fnn-web-len (st) (svref st 1))

(defun fnn-web-slice (st start end)
  (unless (and (integerp start) (integerp end) (<= 0 start end (svref st 1)))
    (fnn-fault "ACL2 named a range outside the web buffer"))
  (subseq (the fnn-octets (svref st 0)) start end))

(defun fnn-web-seconds ()
  (floor (fnn-now) internal-time-units-per-second))

;;; ---------------------------------------------------------------------------
;;; The owner side of a session: open, feed, close.

(defun fnn-web-open (service family address protected)
  "A logical reader connection for the browser at FAMILY/ADDRESS: the owner's
exposure admission decides (the id, or NIL when it refused)."
  (let* ((seed (fnn-owner-sasl-seed))
         (custody nil)
         (opened
          (fnn-owner-serialized
           service nil
           (lambda ()
             (fnn-owner-advance-clock)
             (multiple-value-bind (id node)
                 (fnn-owner-connection-open-locked service :exposure family address nil)
               (setq custody node)
               (when id (fnn-owner-log))
               ;; The session's SASL context (books/nntp-auth.lisp): a fresh
               ;; seed and no channel binding (the browser's TLS layer is not
               ;; one an NNTP client can bind to).  (:tls-established) below
               ;; keeps it.
               (when (integerp id) (fnn-owner-sasl-context id seed nil))
               id))
           :reader)))
    (when (and opened (not (and (integerp opened) (>= opened 0))))
      (fnn-fault "owner returned a malformed connection id"))
    (when (and opened protected)
      ;; ACL2 decided the browser's channel is protected (TLS here, or a
      ;; loopback peer: fn-wss-ctx); the owner's session is told as a
      ;; completed handshake tells it (host/native/mux.lisp).
      (fnn-owner-serialized
       service opened
       (lambda ()
         (unless (eq (fnn-owner-action 'fn-owner-tls-established opened) :ok)
           (fnn-fault "owner rejected the web connection's protection")))
       :reader))
    (values opened custody)))

(defun fnn-web-feed (service cid octets)
  "Feed OCTETS to CID through the owner's served step; the whole reply, or
:GONE when the owner no longer knows CID."
  (handler-case
      (let ((pending (fnn-octets octets)) (reply (fnn-make-octets 0)) (closing nil))
        (loop while (and (> (length pending) 0) (not closing)) do
          (let ((results (multiple-value-list
                          (fnn-owner-handle-chunk service cid pending nil :reader))))
            (if (eq (first results) :defer)
                (sleep (/ (min (second results) 1000) 1000))
              (destructuring-bind (plan close starttls consumed &rest more) results
                (declare (ignore starttls more))
                (unwind-protect
                     (loop
                       (multiple-value-bind (part rest donep)
                           (fnn-owner-render-next-quantum service cid plan :reader)
                         (setq reply (concatenate 'fnn-octets reply part))
                         (when donep (return))
                         (setq plan rest)))
                  (fnn-owner-response-unpin service cid))
                (setq closing close)
                (when (and (zerop consumed) (not close))
                  (fnn-fault "owner consumed no octets of a web command"))
                (setq pending (subseq pending consumed))))))
        reply)
    (fnn-store-error () :gone)))

(defun fnn-web-close (service cid &optional custody)
  (fnn-owner-response-unpin service cid)
  (ignore-errors
    (fnn-owner-serialized service cid (lambda () (fnn-owner-connection-close-locked service cid custody nil)) :reader))
  (ignore-errors
    (fnn-owner-serialized service nil
                          (lambda () (fnn-owner-action 'fn-owner-exposure-release cid))
                          :reader)))

;;; ---------------------------------------------------------------------------
;;; One connection.

(defun fnn-web-receive (fd channel seconds)
  (if channel (fnn-tls-read channel seconds) (fnn-recv fd seconds)))

(defun fnn-web-send (fd channel octets seconds)
  (if channel (fnn-tls-send-all channel octets seconds) (fnn-send-all fd octets seconds)))

(defun fnn-web-respond (face fd channel code fields body bodyp)
  (let ((head (fnn-core 'fn-web-host-head code fields (length body)
                        (fnn-web-face-config face) (and (fnn-web-face-tls-context face) t))))
    (unless (fnn-octet-list-p head)
      (fnn-fault "ACL2 returned a malformed response head"))
    (fnn-web-send fd channel (fnn-octets head) 10)
    (when (and bodyp (> (length body) 0))
      (fnn-web-send fd channel body 10))))

(defun fnn-web-refuse (face fd channel code)
  (let ((body (fnn-core 'fn-web-host-refusal-body code)))
    (fnn-web-respond face fd channel code (fnn-core 'fn-web-host-refusal-fields)
                     (fnn-octets body) t)))

(defun fnn-web-peer (socket)
  (multiple-value-bind (address port) (sb-bsd-sockets:socket-peername socket)
    (declare (ignore port))
    (unless (and (vectorp address) (member (length address) '(4 16)))
      (fnn-fault "socket returned a malformed peer address"))
    (values (if (= (length address) 4) :inet :inet6) (coerce address 'list))))

(defun fnn-web-read-request (face fd channel in deadline)
  "Read the head (ACL2 frames and parses it) and the body ACL2 admitted:
(values REQUEST END), or (values :refused CODE), or NIL (the client left)."
  (let ((limits (fnn-web-face-limits face)) (from 0))
    (fnn-web-fill in (fnn-make-octets 0))
    (loop
      (let ((frame (first (fnn-call 'fn-web-host-frame from limits in))))
        (case (first frame)
          (:head
           (let* ((end (second frame))
                  (parsed (first (fnn-call 'fn-web-host-parse end limits in))))
             (case (first parsed)
               (:refused (return (values :refused (second parsed))))
               (:request
                (let* ((request (second parsed))
                       (need (+ end (fnn-core 'fn-web-req-clen request))))
                  (loop while (< (fnn-web-len in) need) do
                    (let ((more (fnn-web-receive fd channel
                                                 (max 0 (- deadline (fnn-web-seconds))))))
                      (when (or (eq more :timeout) (zerop (length more)))
                        (return-from fnn-web-read-request nil))
                      (fnn-web-append in more)))
                  (return (values request end))))
               (otherwise (fnn-fault "ACL2 returned a malformed parse")))))
          (:need
           (setq from (second frame))
           (let ((more (fnn-web-receive fd channel (max 0 (- deadline (fnn-web-seconds))))))
             (when (or (eq more :timeout) (zerop (length more)))
               (return nil))
             (fnn-web-append in more)))
          (:refused (return (values :refused (second frame))))
          (otherwise (fnn-fault "ACL2 returned a malformed frame")))))))

(defun fnn-web-request (face socket fd channel)
  (let* ((in (fnn-web-live 'fn-web-in))
         (out (fnn-web-live 'fn-web-out))
         (service (fnn-web-face-service face))
         (deadline (+ (fnn-web-seconds) (fnn-core 'fn-web-host-request-seconds))))
    (multiple-value-bind (request end) (fnn-web-read-request face fd channel in deadline)
      (cond
        ((null request) nil)
        ((eq request :refused) (fnn-web-refuse face fd channel end))
        (t
         (multiple-value-bind (family address) (fnn-web-peer socket)
           (let ((event (list :begin request end
                              (+ end (fnn-core 'fn-web-req-clen request))
                              (fnn-web-seconds)
                              (fnn-octet-list (fnn-anchor-csprng-nonce 32))
                              (fnn-octet-list (fnn-anchor-csprng-nonce 32))
                              (and (fnn-web-face-tls-context face) t)
                              family address))
                 (flow nil) (custody nil) (opened-cid nil))
             (unwind-protect
             (dotimes (i (fnn-core 'fn-web-host-max-events)
                         (fnn-fault "a web request took more events than ACL2 allows"))
               (declare (ignorable i))
               (destructuring-bind (action out-st state)
                   (fnn-call 'fn-web-host-step (fnn-web-face-config face) flow event
                             in out *the-live-state*)
                 (declare (ignore out-st state))
                 (case (fnn-core 'fn-web-host-action-kind action)
                   (:respond
                    (destructuring-bind (code fields bodyp) (rest action)
                      (fnn-web-respond face fd channel code fields
                                       (fnn-web-slice out 0 (fnn-web-len out)) bodyp))
                    (return))
                   (:open
                    (destructuring-bind (fam addr protected next) (rest action)
                      (multiple-value-bind (id node) (fnn-web-open service fam addr protected)
                        (setq custody node opened-cid id flow next
                              event (list :opened id)))))
                   (:send
                    (destructuring-bind (cid start stop next) (rest action)
                      (let ((reply (fnn-web-feed service cid (fnn-web-slice out start stop))))
                        (setq flow next)
                        (if (eq reply :gone)
                            (setq event (list :gone))
                          (progn (fnn-web-fill in reply)
                                 (setq event (list :reply)))))))
                   (:close
                    (destructuring-bind (cid next) (rest action)
                      (fnn-web-close service cid custody)
                      (setq opened-cid nil custody nil)
                      (setq flow next event (list :closed))))
                   (otherwise (fnn-fault "ACL2 returned a malformed web action")))))
               (when opened-cid (fnn-web-close service opened-cid custody))))))))))

(defun fnn-web-serve (face socket)
  (let ((fd (fnn-socket-fd socket)) (channel nil))
    (unwind-protect
         (handler-case
             (progn
               (when (fnn-web-face-tls-context face)
                 (setq channel (fnn-tls-accept (fnn-web-face-tls-context face) fd 10)))
               (fnn-web-request face socket fd channel))
           ;; A browser that went away or a handshake that failed ends this
           ;; connection only; an ACL2 fault is the owner's (it stopped).
           (fnn-os-error () nil)
           (sb-bsd-sockets:socket-error () nil)
           (error (condition)
             (if (and (find-class 'fnn-tls-error nil) (typep condition 'fnn-tls-error))
                 nil
               (error condition))))
      (when channel (ignore-errors (fnn-tls-close-channel channel)))
      (fnn-socket-shut socket))))

;;; ---------------------------------------------------------------------------
;;; The listener: an owner start hook binds it, a stop hook ends it.

(defun fnn-web-start (service plan tls-context)
  (let* ((port (fnn-core 'fn-web-host-plan-port plan))
         (family (fnn-core 'fn-web-host-plan-family plan))
         (address (fnn-core 'fn-web-host-plan-address plan))
         (tls (fnn-core 'fn-web-host-plan-tls plan))
         (limits (fnn-core 'fn-web-host-limits
                           (first (fnn-call 'fn-web-host-article-limit *the-live-state*)))))
    (unless (and (integerp port) (< 0 port 65536) (member family '(:inet :inet6))
                 (fnn-octet-list-p address))
      (fnn-fault "ACL2 returned a malformed web plan"))
    (when (and tls (null tls-context))
      (fnn-fault "the web face's TLS needs [listener]'s certificate"))
    (fnn-call 'fn-web-host-reset *the-live-state*)
    (multiple-value-bind (listener bound-port)
        (fnn-listen port :address (coerce address '(simple-array (unsigned-byte 8) (*)))
                         :family family :backlog 64)
      (let ((face (%make-fnn-web-face :plan plan
                                      :config (fnn-core 'fn-web-host-plan-config plan)
                                      :limits limits :listener listener
                                      :tls-context (and tls tls-context)
                                      :service service)))
        ;; A worker of the service, as the owner's TLS accept thread is:
        ;; the stop joins it; it ends when the service stops.
        (fnn-with-roster (service)
          (let ((thread
                  (sb-thread:make-thread
                   (lambda ()
                     (unwind-protect
                          (handler-case
                              (loop
                                (when (or *fnn-sigterm-requested* (fnn-web-face-stop face)
                                          (fnn-owner-service-stopping service))
                                  (return))
                                (let ((socket (fnn-accept-observe listener 1)))
                                  (unless (eq socket :timeout)
                                    (fnn-web-serve face socket))))
                            (sb-bsd-sockets:socket-error (condition)
                              (unless (or *fnn-sigterm-requested*
                                          (fnn-owner-service-stopping service))
                                (fnn-err "web face listener: ~a" condition))))
                       (fnn-with-roster (service)
                         (setf (fnn-owner-service-workers service)
                               (delete sb-thread:*current-thread*
                                       (fnn-owner-service-workers service) :test #'eq)))))
                   :name "fn web face")))
            (push thread (fnn-owner-service-workers service))
            (setf (fnn-web-face-thread face) thread)))
        (setq *fnn-web-face* face)
        (fnn-out "LISTENING-WEB ~d" bound-port)
        face))))

(defun fnn-web-close-face (service)
  "After the workers are joined (the owner's close hooks run then)."
  (declare (ignore service))
  (let ((face *fnn-web-face*))
    (when face
      (setf (fnn-web-face-stop face) t)
      (fnn-socket-shut (fnn-web-face-listener face))
      (setq *fnn-web-face* nil))))

;;; The operator's `run': the plan ACL2 made of the profile's [web] table
;;; (books/web-config.lisp), the hooks that start and stop the face.
(defun fnn-web-run-hooks (listener-port tls-port certp)
  "(values START STOP CLOSE) hooks for the owner, or NIL when the profile
has no [web] port.  A refused [web] table stops the run by its reason."
  (when *fnn-operator-config-octets*
    (let ((plan (fnn-core 'fn-web-host-plan (fnn-octet-list *fnn-operator-config-octets*)
                          listener-port tls-port certp)))
      (cond ((fnn-core 'fn-web-host-plan-web-p plan)
             (values plan))
            ((fnn-core 'fn-web-host-plan-refusal plan)
             (fnn-refuse "the [web] table is refused: ~(~a~)"
                         (fnn-core 'fn-web-host-plan-refusal plan)))
            (t nil)))))
