;;; The remote consumer (D48 / PKT-673; specs/applications.md "Remote consumer").
;;;
;;; A separate TLS listener, `[remote_consumer]' (books/consumer-remote-config.lisp).
;;; Each accepted socket first draws the FNCR connection vector from the
;;; class's private resource ledger (books/consumer-remote-operation-source.lisp
;;; fn-crf-open); a socket the ledger cannot fund is closed before the
;;; handshake.  A funded session then does one exchange:
;;;   TLS handshake (deadline) -> FNCR header and frame reads, each admitted
;;;   by fn-owner-remote-operation-preflight against the live draw ->
;;;   fn-cr-request-decode -> fn-owner-consumer-remote-route (the account's
;;;   bound consumer, books/consumer-remote-bound.lisp) -> the SAME local
;;;   consumer entry the control socket calls -> the reasoned consumer reply
;;;   (FNCT) a local client reads -> close.
;;; The session's thread ends, its socket is closed, and only then the accept
;;; thread joins it and settles its draw (fn-crf-close): physical close, never
;;; logical.  No FNCT request is forwarded to owner control; operator
;;; controls are refused by the route.
(in-package "ACL2")

(defconstant +fnn-remote-io-seconds+ 10)

(defstruct (fnn-remote-face (:constructor %make-fnn-remote-face))
  service tls-context listener accept-thread
  (lock (sb-thread:make-mutex :name "fn remote consumer"))
  ledger (sessions nil) (finished nil) (stopping nil))

(defvar *fnn-remote-face* nil)

;;; -- reads -------------------------------------------------------------------

(defun fnn-remote-read-exact (channel count seconds)
  "Move exactly COUNT plaintext octets under one TLS I/O deadline.
The caller holds the admitted read for this exact extent."
  (let ((result (fnn-make-octets count)) (offset 0)
        (deadline (+ (fnn-now) (* seconds internal-time-units-per-second))))
    (loop while (< offset count) do
      (let ((remaining (fnn-seconds-to-deadline deadline)))
        (when (<= remaining 0) (return-from fnn-remote-read-exact :timeout))
        (let ((chunk (fnn-tls-read channel remaining
                                  (min +fnn-max-read+ (- count offset)))))
          (when (eq chunk :timeout) (return-from fnn-remote-read-exact :timeout))
          (when (zerop (length chunk)) (return-from fnn-remote-read-exact :closed))
          (replace result chunk :start1 offset)
          (incf offset (length chunk)))))
    result))

(defun fnn-remote-admit (face token kind count)
  "ACL2's admission of one read on this session's draw: (:admitted) or a refusal."
  (sb-thread:with-mutex ((fnn-remote-face-lock face))
    (fnn-core 'fn-owner-remote-operation-preflight kind count token
              (fnn-remote-face-ledger face))))

(defun fnn-remote-receive (face token channel g seconds)
  "Read one FNCR frame: the octets of header and frame, or ACL2's refusal.
Each read is admitted before its first octet; a refused one reads nothing."
  (let* ((header-count (fnn-core 'fn-cre-header-octets))
         (admitted (fnn-remote-admit face token :remote-header header-count)))
    (unless (equal admitted '(:admitted))
      (return-from fnn-remote-receive admitted))
    (let ((header (fnn-remote-read-exact channel header-count seconds)))
      (unless (vectorp header)
        (return-from fnn-remote-receive (fnn-core 'fn-cre-receive-failure header)))
      (let ((plan (fnn-core 'fn-cre-header-plan (fnn-octet-list header) t g)))
        (unless (eq (car plan) :receive) (return-from fnn-remote-receive plan))
        (let ((admitted (fnn-remote-admit face token :remote-frame (second plan))))
          (unless (equal admitted '(:admitted))
            (return-from fnn-remote-receive admitted)))
        (let ((suffix (fnn-remote-read-exact channel (second plan) seconds)))
          (unless (vectorp suffix)
            (return-from fnn-remote-receive (fnn-core 'fn-cre-receive-failure suffix)))
          (concatenate '(simple-array (unsigned-byte 8) (*)) header suffix))))))

;;; -- one exchange ------------------------------------------------------------

(defun fnn-remote-refusal (operation reason)
  "A refusal in the reply shape OPERATION's local client reads."
  (list :reason
        (case operation
          ((:bound-poll :bound-wait) (list :consumer-poll-reply :refused nil nil))
          (:status (list :consumer-status-reply :refused nil nil nil))
          (otherwise (list :consumer-reply :refused nil)))
        reason))

(defun fnn-remote-answer (service request)
  "The owner's answer to a decoded FNCR request, as host/native/control.lisp's
consumer dispatch answers the local request it routes to."
  (let* ((op (second request))
         (local (fnn-core 'fn-crc-local-operation op))
         (route (fnn-owner-serialized
                 service nil
                 (lambda () (fnn-owner-core 'fn-owner-consumer-remote-route request)))))
    (case (and (consp route) (first route))
      (:refused (fnn-remote-refusal local (second route)))
      (:bound-poll
       (fnn-owner-consumer-local-serialized service :bound-poll (second route) (third route)))
      (:bound-ack
       (fnn-owner-consumer-local-serialized service :bound-ack (second route) (third route)))
      (:bound-wait
       (fnn-owner-consumer-local-wait service :bound-wait (second route) (third route)))
      ((:position :status)
       ;; The gate and the read in one owner turn.
       (fnn-owner-consumer-local-serialized
        service (if (eq (first route) :position) :remote-position :remote-status)
        request nil))
      (otherwise (fnn-fault "ACL2 returned a malformed remote route")))))

(defun fnn-remote-reply-octets (status)
  "The reasoned consumer reply (PKT-709) host/native/control.lisp sends a
reasoned consumer request: the consumer reply of an acceptance, else the
status and ACL2's reason."
  (let ((reason nil))
    (when (and (consp status) (eq (first status) :reason))
      (setq reason (third status) status (second status)))
    (when (keywordp status)
      (setq status (list :reasoned-reply status reason nil)))
    (when (and (consp status)
               (member (first status) '(:consumer-reply :consumer-poll-reply
                                        :consumer-status-reply))
               (not (eq (second status) :accepted)))
      (setq status (list :reasoned-reply (second status) reason nil)))
    (fnn-control-reply-octets status)))

(defun fnn-remote-exchange (face token channel)
  (let* ((service (fnn-remote-face-service face))
         (g (fnn-core 'fn-crf-groups))
         (frame (fnn-remote-receive face token channel g +fnn-remote-io-seconds+))
         (request (if (vectorp frame)
                      (fnn-core 'fn-cr-request-decode (fnn-octet-list frame) t g)
                    frame))
         (status
           (if (not (eq (first request) :remote-consumer))
               ;; Nothing was decoded: no operation is known, so the plain
               ;; reasoned reply carries the refusal.
               (list :reason (if (eq (first request) :unavailable) :busy :refused)
                     (second request))
             (handler-case (fnn-remote-answer service request)
               (fnn-store-indeterminate (condition)
                 (fnn-err "remote consumer request uncertain; owner fenced: ~a" condition)
                 :uncertain)
               (fnn-store-fault (condition)
                 (fnn-err "remote consumer request fault; owner stopped: ~a" condition)
                 :fault)
               (fnn-store-error (condition)
                 (fnn-err "remote consumer request refused (store-error): ~a" condition)
                 (list :reason :refused
                       (fnn-core 'fn-native-control-host-refusal-reason :store-error)))))))
    (fnn-tls-send-all channel (fnn-remote-reply-octets status) +fnn-remote-io-seconds+)))

(defun fnn-remote-session (face token socket)
  "One funded session, on its own thread.  It never settles its own draw."
  (unwind-protect
       (handler-case
           (let ((channel (fnn-tls-accept (fnn-remote-face-tls-context face)
                                          (fnn-socket-fd socket) +fnn-remote-io-seconds+)))
             (unwind-protect (fnn-remote-exchange face token channel)
               (fnn-tls-close-channel channel)))
         (error (condition)
           (fnn-err "remote consumer session ended: ~a" condition)))
    (fnn-socket-shut socket)
    (sb-thread:with-mutex ((fnn-remote-face-lock face))
      (push sb-thread:*current-thread* (fnn-remote-face-finished face)))))

;;; -- physical close and settlement ------------------------------------------

(defun fnn-remote-settle (face thread)
  "Join THREAD (its socket already closed) and settle its draw."
  (sb-thread:join-thread thread :default nil)
  (sb-thread:with-mutex ((fnn-remote-face-lock face))
    (let ((entry (assoc thread (fnn-remote-face-sessions face))))
      (when entry
        (destructuring-bind (word returned)
            (fnn-call 'fn-crf-close (cdr entry) (fnn-remote-face-ledger face))
          (setf (fnn-remote-face-ledger face) returned)
          (unless (eq word :settled)
            (fnn-fault "remote consumer settlement refused ~a" word)))
        (setf (fnn-remote-face-sessions face)
              (remove thread (fnn-remote-face-sessions face) :key #'car))))))

(defun fnn-remote-reap (face)
  (let ((finished (sb-thread:with-mutex ((fnn-remote-face-lock face))
                    (shiftf (fnn-remote-face-finished face) nil))))
    (dolist (thread finished) (fnn-remote-settle face thread))))

(defun fnn-remote-launch (face socket)
  (let ((token nil))
    (sb-thread:with-mutex ((fnn-remote-face-lock face))
      (unless (fnn-remote-face-stopping face)
        (destructuring-bind (word drawn returned)
            (fnn-call 'fn-crf-open (fnn-remote-face-ledger face))
          (setf (fnn-remote-face-ledger face) returned)
          (if (eq word :drawn)
              (setq token drawn)
            (fnn-err "remote consumer connection refused: ~(~a~)" word)))))
    (if (null token)
        ;; Unfunded: closed before any handshake (nothing can be said in clear).
        (fnn-socket-shut socket)
      (let ((spawned nil))
        (unwind-protect
             ;; The session records itself as finished only under this lock,
             ;; so its entry exists before it can be reaped.
             (sb-thread:with-mutex ((fnn-remote-face-lock face))
               (let ((thread (sb-thread:make-thread
                              (lambda () (fnn-remote-session face token socket))
                              :name "fn remote consumer session")))
                 (push (cons thread token) (fnn-remote-face-sessions face))
                 (setq spawned t)))
          (unless spawned
            ;; No thread was created: the socket's close is the physical
            ;; close, and the draw settles here.
            (fnn-socket-shut socket)
            (sb-thread:with-mutex ((fnn-remote-face-lock face))
              (destructuring-bind (word returned)
                  (fnn-call 'fn-crf-close token (fnn-remote-face-ledger face))
                (setf (fnn-remote-face-ledger face) returned)
                (unless (eq word :settled)
                  (fnn-fault "remote consumer settlement refused ~a" word))))))))))

(defun fnn-remote-accept-loop (face)
  (let ((listener (fnn-remote-face-listener face)))
    (loop
      (fnn-remote-reap face)
      (when (sb-thread:with-mutex ((fnn-remote-face-lock face))
              (fnn-remote-face-stopping face))
        (return))
      (handler-case
          (let ((socket (fnn-accept-observe listener 1)))
            (unless (eq socket :timeout) (fnn-remote-launch face socket)))
        (error (condition)
          (unless (sb-thread:with-mutex ((fnn-remote-face-lock face))
                    (fnn-remote-face-stopping face))
            (fnn-err "remote consumer listener failed: ~a" condition))
          (return))))))

;;; -- lifecycle (host/native/operator-live.lisp's run hooks) ------------------

(defun fnn-remote-run-hooks (config-octets listener-port tls-port certp)
  "ACL2's plan of the profile's [remote_consumer] table, or NIL for none.
CONFIG-OCTETS are the octets the operator's profile was loaded from."
  (when config-octets
    (let ((plan (fnn-core 'fn-crc-config-plan (fnn-octet-list config-octets)
                          listener-port tls-port certp)))
      (case (first plan)
        (:remote plan)
        (:refused (fnn-refuse "the [remote_consumer] table is refused: ~(~a~)" (second plan)))
        (t nil)))))

(defun fnn-remote-start (service plan tls-context)
  (destructuring-bind (tag port family address sessions) plan
    (declare (ignore tag))
    (unless (and tls-context (integerp port) (member family '(:inet :inet6))
                 (fnn-octet-list-p address))
      (fnn-fault "malformed remote consumer plan"))
    (let ((face (%make-fnn-remote-face :service service :tls-context tls-context)))
      (destructuring-bind (word returned)
          (fnn-call 'fn-crf-install sessions (fnn-mux-thread-stack-octets)
                    (fnn-core 'create-fn-resource-ledger))
        (setf (fnn-remote-face-ledger face) returned)
        (unless (eq word :installed)
          (fnn-refuse "remote consumer funding refused: ~(~a~)" word)))
      (multiple-value-bind (listener bound-port)
          (fnn-listen port :address (coerce address '(simple-array (unsigned-byte 8) (*)))
                           :family family :backlog 16)
        (setf (fnn-remote-face-listener face) listener)
        (setq *fnn-remote-face* face)
        (setf (fnn-remote-face-accept-thread face)
              (sb-thread:make-thread (lambda () (fnn-remote-accept-loop face))
                                     :name "fn remote consumer accept"))
        (fnn-out "LISTENING-REMOTE-CONSUMER ~d" bound-port)
        face))))

(defun fnn-remote-close (&rest ignored)
  "Stop accepting, join every session, settle every draw; the class must drain."
  (declare (ignore ignored))
  (let ((face *fnn-remote-face*))
    (when face
      (sb-thread:with-mutex ((fnn-remote-face-lock face))
        (setf (fnn-remote-face-stopping face) t))
      (ignore-errors (sb-bsd-sockets:socket-shutdown (fnn-remote-face-listener face)
                                                     :direction :io))
      (when (fnn-remote-face-accept-thread face)
        (sb-thread:join-thread (fnn-remote-face-accept-thread face) :default nil))
      (dolist (entry (sb-thread:with-mutex ((fnn-remote-face-lock face))
                       (copy-list (fnn-remote-face-sessions face))))
        (fnn-remote-settle face (car entry)))
      (fnn-socket-shut (fnn-remote-face-listener face))
      (unless (fnn-core 'fn-crf-drainedp (fnn-remote-face-ledger face))
        (fnn-fault "remote consumer sessions remain drawn after close"))
      (setq *fnn-remote-face* nil))))

;;; -- the client: `fn consumer-remote OP HOST PORT TRUST LOGIN SECRET-FILE ...' --

(defun fnn-remote-client-exchange (host port trust request operation seconds)
  "Send one FNCR frame over TLS and answer (values REPLY WORD) as the local
consumer client does (host/native/control.lisp fnn-control-consumer-answer)."
  (let ((frame (fnn-core 'fn-cr-request-encode request (fnn-core 'fn-crf-groups)))
        (socket nil) (context nil) (channel nil) (stage :before-submission))
    (unless (fnn-octet-list-p frame) (fnn-fault "ACL2 refused the FNCR request"))
    (unwind-protect
         (handler-case
             (progn
               (setq socket (fnn-connect host port :timeout +fnn-remote-io-seconds+))
               (setq context (fnn-tls-open-client-context (list :pinned trust))
                     channel (fnn-tls-connect context (fnn-socket-fd socket) host
                                              +fnn-remote-io-seconds+ :sni nil))
               (setq stage :after-submission)
               (fnn-tls-send-all channel (fnn-octets frame) +fnn-remote-io-seconds+)
               (let* ((maximum (fnn-control-consumer-maximum operation))
                      (deadline (+ (fnn-now) (* (+ +fnn-remote-io-seconds+ seconds)
                                                internal-time-units-per-second)))
                      (got (make-array 0 :element-type '(unsigned-byte 8)
                                         :adjustable t :fill-pointer 0)))
                                  (loop
                   (let* ((remaining (fnn-seconds-to-deadline deadline))
                          (chunk (if (<= remaining 0) :timeout
                                   (fnn-tls-read channel remaining
                                                 (min +fnn-max-read+
                                                      (max 1 (- maximum (length got))))))))
                     (when (or (eq chunk :timeout) (zerop (length chunk))) (return))
                     (loop for octet across chunk do (vector-push-extend octet got))
                     (when (>= (length got) maximum) (return))))
                 (fnn-control-consumer-answer
                  operation (and (plusp (length got)) (coerce got '(simple-array (unsigned-byte 8) (*))))
                  :after-submission)))
           (error (condition)
             (fnn-err "remote consumer: ~a" condition)
             (fnn-control-consumer-answer
              operation nil stage)))
      (when channel (ignore-errors (fnn-tls-close-channel channel)))
      (when context (ignore-errors (fnn-tls-close-context context)))
      (when socket (fnn-socket-shut socket)))))

(defun fnn-command-consumer-remote (args)
  (let* ((argv (mapcar #'fnn-ascii-octet-list args))
         (plan (fnn-core 'fn-crc-cli-plan argv)))
    (unless (eq (first plan) :run)
      (fnn-err "usage: fn consumer-remote OP HOST PORT TRUST LOGIN SECRET-FILE ...")
      (return-from fnn-command-consumer-remote +fnn-exit-usage+))
    (destructuring-bind (ignored op host port trust login secret-file arg out1 out2 seconds) plan
      (declare (ignore ignored))
      (let* ((path (lambda (octets) (fnn-octets-string (fnn-octets octets))))
             (secret (fnn-core 'fn-native-control-host-consumer-secret-of-file
                               (fnn-octet-list (fnn-read-regular-bounded
                                                (funcall path secret-file) 498))))
             (cursor (and (eq op :ack)
                          (fnn-octet-list (fnn-read-regular-bounded (funcall path arg) 512))))
             (consumer (if (eq op :ack) (fnn-core 'fn-cbind-cursor-consumer cursor) arg))
             (request (list :remote-consumer op login secret consumer nil cursor seconds))
             (operation (fnn-core 'fn-crc-local-operation op)))
        (multiple-value-bind (reply word)
            (fnn-remote-client-exchange (funcall path host) port (funcall path trust)
                                        request operation seconds)
          (let ((status (and (consp reply) (second reply))))
            (when (eq status :accepted)
              (handler-case
                  (case op
                    ((:poll :wait)
                     ;; Report first, cursor last, as the local client writes them.
                     (fnn-write-staged (funcall path out2) (fnn-octets (fourth reply)))
                     (fnn-write-staged (funcall path out1) (fnn-octets (third reply))))
                    (:position
                     (fnn-write-staged (funcall path out1) (fnn-octets (third reply)))))
                (error () (setq status :fault))))
            (if (and (eq op :status) (eq status :accepted))
                (fnn-out "consumer status accepted committed-ack=~d committed-journal-frontier=~d journal-event-distance=~d"
                         (third reply) (fourth reply) (fifth reply))
              (fnn-consumer-say nil operation status word))
            (fnn-core 'fn-native-control-host-status-exit-code status)))))))

(fnn-register-verb "consumer-remote"
                   (lambda (first rest)
                     (fnn-command-consumer-remote (cons first rest))))
