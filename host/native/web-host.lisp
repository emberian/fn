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
;;; A registered I/O actor multiplexes bounded connection records. One fixed
;;; semantic actor runs the owner operations that can await publication. Each record
;;; retains its input/output stobjs, socket offset and semantic continuation.
;;; No socket, commit receipt or cold read is awaited on that actor's stack.

(in-package "ACL2")

(defstruct (fnn-web-face (:constructor %make-fnn-web-face))
  plan config limits listener thread tls-context service capacity semantic-thread
  (lock (sb-thread:make-mutex :name "fn web completions"))
  (jobs nil) (jobs-closed nil)
  (job-ready (sb-thread:make-waitqueue :name "fn web semantic work"))
  (conns nil) wake-read wake-write (wake-closed nil) (cleanup-debts nil) (stop nil))

(defstruct (fnn-web-conn (:constructor %make-fnn-web-conn))
  socket fd ssl channel in out deadline job (closedp nil) (semantic-ended nil) (semantic-disposal :idle)
  (phase :head) (want :input) (from 0) request end
  flow event private-begin (events 0) (opened nil) (answered nil)
  cid leased (cmd-at 0) (cmd-end 0) pending plan closing await completion
  cold cold-word (line-since nil) (resume-at 0)
  wire (wire-at 0) (body-at 0) (body-end 0)
  page-segs page-cursor page-response (pagep nil) (page-count 0) (page-done nil)
  reply-scan captured-plans replay-plans replay-plan replay-need replay-return
  replay-tail replay-tail-base replay-use-tail
  (replay-at 0) (window-base 0)
  (cleanup-attempts nil))

(defvar *fnn-web-face* nil)

(defun fnn-web-fill (st vector)
  "Make VECTOR's bytes ST's contents (the same boundary as fnn-octets-fill)."
  (let ((n (length vector)))
    (fn-octets$c-reserve n st)
    (replace (the fnn-octets (svref st 0)) vector)
    (setf (svref st 1) n)
    st))

(defun fnn-web-append (st vector)
  (let ((fill (svref st 1)) (n (length vector)))
    (fn-octets$c-reserve (fnn-core 'fn-web-host-reserve-size
                                 (+ fill n) (length (svref st 0))) st)
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
         (opened
          (fnn-owner-serialized
           service nil
           (lambda ()
             (fnn-owner-advance-clock)
             (let ((id (fnn-owner-core 'fn-owner-exposure-open family address nil)))
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
    opened))

;;; HTTP continuations. Only this actor advances these records; the committer
;;; publishes a completion cell under FACE's lock and never runs a web step.

(def-section fnn-quantum-web-finish
  :actors (:web) :classes (:reader :control) :admits (:cleanup :finish)
  :doc "Web semantic custody after its exact job activation has returned.")

(defstruct (fnn-web-job (:constructor %make-fnn-web-job))
  conn kind (returned nil) (cancelled nil))

(defun fnn-web-cleanup (face conn key thunk)
  (let ((claimed nil))
    (sb-thread:with-mutex ((fnn-web-face-lock face))
      (unless (member key (fnn-web-conn-cleanup-attempts conn) :test #'equal)
        (push key (fnn-web-conn-cleanup-attempts conn)) (setq claimed t)))
    (when claimed
      (handler-case (funcall thunk)
        (serious-condition (condition)
          (sb-thread:with-mutex ((fnn-web-face-lock face))
            (push (list conn key condition) (fnn-web-face-cleanup-debts face)))
          (handler-case
              (fnn-owner-thread-escape (fnn-web-face-service face) condition "web cleanup")
            (serious-condition () nil)))))))

(defun fnn-web-dispose-semantic (face conn)
  ;; Claim the whole disposal, not just each effect. Concurrent shutdown or
  ;; job-return observers cannot manufacture a receipt while its sole
  ;; claimant is still inside a callback.
  (let ((claimed nil))
    (sb-thread:with-mutex ((fnn-web-face-lock face))
      (when (and (eq (fnn-web-conn-semantic-disposal conn) :idle)
                 (or (null (fnn-web-conn-job conn))
                     (fnn-web-job-returned (fnn-web-conn-job conn))))
        (setf (fnn-web-conn-semantic-disposal conn) :running)
        (setq claimed t)))
    (unless claimed (return-from fnn-web-dispose-semantic nil)))
  ;; A cancelled operation may still pin/issue/await while its activation
  ;; runs. This cleanup is eligible only after that activation has returned.
  (let ((service (fnn-web-face-service face)) (cid (fnn-web-conn-cid conn)))
    (when (fnn-web-conn-await conn)
      (fnn-web-cleanup face conn :await (lambda () (fnn-owner-await-abandon service cid))))
    (when (fnn-web-conn-cold conn)
      (fnn-web-cleanup face conn :cold
        (lambda () (fnn-owner-cold-abandon (first (fnn-web-conn-cold conn))))))
    (when cid
      (fnn-web-cleanup face conn :response (lambda () (fnn-owner-response-unpin service cid))))
    (unless (fnn-web-conn-answered conn)
      (dolist (opened (remove-duplicates (append (fnn-web-conn-opened conn)
                         (and (fnn-web-conn-leased conn) cid (list cid)))))
        (fnn-web-cleanup face conn (list :close opened)
          (lambda () (fnn-quantum-web-finish service opened
            (lambda () (fnn-owner-action 'fn-owner-close opened)) :reader)))
        (fnn-web-cleanup face conn (list :release opened)
          (lambda () (fnn-quantum-web-finish service nil
            (lambda () (fnn-owner-action 'fn-owner-exposure-release opened)) :reader)))))
    (sb-thread:with-mutex ((fnn-web-face-lock face))
      (unless (find conn (fnn-web-face-cleanup-debts face) :key #'first :test #'eq)
        (setf (fnn-web-conn-leased conn) nil (fnn-web-conn-semantic-ended conn) t
              (fnn-web-conn-semantic-disposal conn) :returned)))))

(defun fnn-web-finish (face conn)
  (let ((first nil) (eligible nil))
    (sb-thread:with-mutex ((fnn-web-face-lock face))
      (unless (fnn-web-conn-closedp conn)
        (setf (fnn-web-conn-closedp conn) t (fnn-web-conn-phase conn) :done)
        (setq first t))
      (let ((job (fnn-web-conn-job conn)))
        (when job (setf (fnn-web-job-cancelled job) t))
        (setq eligible (or (null job) (fnn-web-job-returned job)))))
    (when eligible (fnn-web-dispose-semantic face conn))
    ;; Physical transport cleanup is independent of semantic/job custody.
    (when first
      (when (fnn-web-conn-channel conn)
        (fnn-web-cleanup face conn :tls
          (lambda () (fnn-tls-close-channel (fnn-web-conn-channel conn)))))
      (when (fnn-web-conn-ssl conn)
        (fnn-web-cleanup face conn :ssl
          (lambda () (fnn-%ssl-free (fnn-web-conn-ssl conn)))))
      (fnn-web-cleanup face conn :socket
        (lambda () (fnn-socket-shut (fnn-web-conn-socket conn)))))))

(defun fnn-web-wake-locked (face)
  (unless (fnn-web-face-wake-closed face)
    (let ((one (fnn-make-octets 1)))
      (sb-sys:with-pinned-objects (one)
        (sb-unix:unix-write (fnn-web-face-wake-write face) one 0 1)))))

(defun fnn-web-job-submit (face conn kind)
  ;; One outstanding job per admitted HTTP record: the mailbox cannot grow
  ;; beyond the profile's already captured slot count.
  (sb-thread:with-mutex ((fnn-web-face-lock face))
    (when (and (not (fnn-web-conn-job conn))
               (eq (fn-fs-inbox-admit (fnn-web-face-jobs-closed face)) :admitted))
      (let ((job (%make-fnn-web-job :conn conn :kind kind)))
        (setf (fnn-web-conn-job conn) job
              (fnn-web-face-jobs face) (nconc (fnn-web-face-jobs face) (list job)))
        (sb-thread:condition-notify (fnn-web-face-job-ready face))
        t))))

(defun fnn-web-job-consume (face conn)
  (sb-thread:with-mutex ((fnn-web-face-lock face))
    (let ((job (fnn-web-conn-job conn)))
      (when (and job (fnn-web-job-returned job))
        (setf (fnn-web-conn-job conn) nil)))))

(defun fnn-web-semantic-body (face)
  (loop
    (let ((job nil))
      (loop until job do
        (sb-thread:with-mutex ((fnn-web-face-lock face))
          (cond ((fnn-web-face-jobs face) (setq job (pop (fnn-web-face-jobs face))))
                ((fnn-web-face-jobs-closed face) (return-from fnn-web-semantic-body nil))
                (t (sb-thread:condition-wait (fnn-web-face-job-ready face)
                                            (fnn-web-face-lock face) :timeout 1)))))
      (let ((conn (fnn-web-job-conn job)))
        (unwind-protect
             (handler-case
                 (unless (fnn-web-job-cancelled job)
                   (ecase (fnn-web-job-kind job)
                     (:feed (fnn-web-feed-step face conn))
                     (:render (fnn-web-render-step face conn))
                     (:replay (fnn-web-replay-step face conn))
                     (:cold (fnn-web-cold-step face conn))
                     ((:page-count :page-emit) (fnn-web-page-step face conn))
                     (:private-reply (fnn-web-private-reply face conn))
                     (:private-begin (fnn-web-private-begin face conn))))
               (serious-condition (condition)
                 (unwind-protect
                     (fnn-owner-thread-escape (fnn-web-face-service face) condition "web semantic job")
                   (fnn-web-finish face conn))))
          ;; Returning from this activation is the no-future-publisher
          ;; receipt for its buffers/plan. The worker actor itself remains
          ;; registered until its independent physical join.
          (sb-thread:with-mutex ((fnn-web-face-lock face))
            (setf (fnn-web-job-returned job) t)
            (when (fnn-web-job-cancelled job) (setf (fnn-web-conn-phase conn) :done))
            (fnn-web-wake-locked face))
          (when (fnn-web-job-cancelled job) (fnn-web-dispose-semantic face conn)))))))

(defun fnn-web-peer (socket)
  (multiple-value-bind (address port) (sb-bsd-sockets:socket-peername socket)
    (declare (ignore port))
    (unless (and (vectorp address) (member (length address) '(4 16)))
      (fnn-fault "socket returned a malformed peer address"))
    (values (if (= (length address) 4) :inet :inet6) (coerce address 'list))))

(defun fnn-web-response (face conn code fields bodyp &optional (length (fnn-web-len (fnn-web-conn-out conn))))
  (let* ((head (fnn-core 'fn-web-host-head code fields length
                        (fnn-web-face-config face) (and (fnn-web-face-tls-context face) t))))
    (unless (fnn-octet-list-p head) (fnn-fault "malformed web response head"))
    (setf (fnn-web-conn-wire conn) (fnn-octets head)
          (fnn-web-conn-wire-at conn) 0
          (fnn-web-conn-body-at conn) 0
          (fnn-web-conn-body-end conn) (if bodyp length 0)
          (fnn-web-conn-phase conn) :write
          (fnn-web-conn-want conn) :output)))

(defun fnn-web-refusal (face conn code)
  (fnn-web-fill (fnn-web-conn-out conn) (fnn-octets (fnn-core 'fn-web-host-refusal-body code)))
  (fnn-web-response face conn code (fnn-core 'fn-web-host-refusal-fields) t))

(defun fnn-web-begin (face conn)
  (multiple-value-bind (family address) (fnn-web-peer (fnn-web-conn-socket conn))
    (setf (fnn-web-conn-event conn)
          (list :begin (fnn-web-conn-request conn) (fnn-web-conn-end conn)
                (fnn-core 'fn-web-host-request-end (fnn-web-conn-end conn)
                          (fnn-web-conn-request conn))
                (fnn-web-seconds)
                (fnn-octet-list (fnn-anchor-csprng-nonce 32))
                (fnn-octet-list (fnn-anchor-csprng-nonce 32))
                (and (fnn-web-face-tls-context face) t) family address)
          (fnn-web-conn-phase conn) :event (fnn-web-conn-want conn) nil)))

(defun fnn-web-frame (face conn)
  (let ((in (fnn-web-conn-in conn)) (limits (fnn-web-face-limits face)))
    (when (eq (fnn-web-conn-phase conn) :head)
      (let ((frame (first (fnn-call 'fn-web-host-frame (fnn-web-conn-from conn) limits in))))
        (case (first frame)
          (:need (setf (fnn-web-conn-from conn) (second frame)))
          (:refused (fnn-web-refusal face conn (second frame)))
          (:head
           (let ((parsed (first (fnn-call 'fn-web-host-parse (second frame) limits in))))
             (case (first parsed)
               (:refused (fnn-web-refusal face conn (second parsed)))
               (:request
                (setf (fnn-web-conn-request conn) (second parsed)
                      (fnn-web-conn-end conn) (second frame)
                      (fnn-web-conn-phase conn) :body))
               (t (fnn-fault "malformed web parse")))))
          (t (fnn-fault "malformed web frame")))))
    (when (and (eq (fnn-web-conn-phase conn) :body)
               (zerop (fnn-core 'fn-web-host-read-size (fnn-web-len in) limits
                               (fnn-web-conn-end conn) (fnn-web-conn-request conn))))
      (fnn-web-begin face conn))))

(defun fnn-web-read-ready (face conn)
  (let* ((size (fnn-core 'fn-web-host-read-size (fnn-web-len (fnn-web-conn-in conn))
                         (fnn-web-face-limits face) (fnn-web-conn-end conn)
                         (fnn-web-conn-request conn)))
         (buffer (fnn-make-octets size))
         (got (if (fnn-web-conn-channel conn)
                  (fnn-tls-read-now (fnn-web-conn-channel conn) size buffer)
                (fnn-mux-read-plain (fnn-web-conn-fd conn) buffer))))
    (cond ((member got '(:input :output)) (setf (fnn-web-conn-want conn) got))
          ((zerop (length got)) (fnn-web-finish face conn))
          (t (fnn-web-append (fnn-web-conn-in conn) got)
             (setf (fnn-web-conn-want conn) :input)
             (fnn-web-frame face conn)))))

(defun fnn-web-event (face conn)
  (when (>= (fnn-web-conn-events conn) (fnn-core 'fn-web-host-max-events))
    (fnn-fault "web flow exceeded its event allowance"))
  (let* ((service (fnn-web-face-service face))
         (cid (fnn-owner-serialized service nil (lambda ()
                (first (fnn-call 'fn-web-host-event-cid (fnn-web-face-config face)
                  (fnn-web-conn-flow conn) (fnn-web-conn-event conn) *the-live-state*))) :reader)))
    (when cid
      (setf (fnn-web-conn-cid conn) cid)
      (unless (fnn-web-feed-owned-p face conn)
        (setf (fnn-web-conn-resume-at conn) (fnn-mux-ms-ticks 2))
        (return-from fnn-web-event nil))))
  (incf (fnn-web-conn-events conn))
  (let* ((service (fnn-web-face-service face))
         (action (first (fnn-owner-serialized service nil
                   (lambda () (fnn-call 'fn-web-host-step (fnn-web-face-config face)
                     (fnn-web-conn-flow conn) (fnn-web-conn-event conn)
                     (fnn-web-conn-in conn) (fnn-web-conn-out conn) *the-live-state*)) :reader))))
    (fnn-web-apply-action face conn action)))

(defun fnn-web-private-reply (face conn)
  (when (>= (fnn-web-conn-events conn) (fnn-core 'fn-web-host-max-events))
    (fnn-fault "web flow exceeded its event allowance"))
  (incf (fnn-web-conn-events conn))
  (fnn-web-apply-action face conn
    (first (fnn-call 'fn-web-host-private-reply-step (fnn-web-face-config face)
                    (fnn-web-conn-flow conn) (fnn-web-conn-event conn)
                    (fnn-web-conn-in conn) (fnn-web-conn-out conn)))))

(defun fnn-web-private-begin (face conn)
  (when (>= (fnn-web-conn-events conn) (fnn-core 'fn-web-host-max-events))
    (fnn-fault "web flow exceeded its event allowance"))
  (incf (fnn-web-conn-events conn))
  (let ((action (first (fnn-call 'fn-web-host-private-begin-step (fnn-web-face-config face)
                               (fnn-web-conn-private-begin conn)
                               (fnn-web-conn-in conn) (fnn-web-conn-out conn)))))
    (setf (fnn-web-conn-private-begin conn) nil)
    (fnn-web-apply-action face conn action)))

(defun fnn-web-apply-action (face conn action)
  (let ((service (fnn-web-face-service face)))
    (case (fnn-core 'fn-web-host-action-kind action)
      (:private-begin (setf (fnn-web-conn-private-begin conn) action
                            (fnn-web-conn-phase conn) :private-begin))
      (:respond (destructuring-bind (code fields bodyp &optional page-kind segs) (rest action)
                  (when (fnn-web-conn-reply-scan conn)
                    (fnn-web-fill (fnn-web-conn-in conn) (fnn-make-octets 0))
                    (setf (fnn-web-conn-window-base conn) 0))
                  (if (eq page-kind :page-plan)
                      (setf (fnn-web-conn-pagep conn) t
                            (fnn-web-conn-page-segs conn) segs
                            (fnn-web-conn-page-cursor conn) (fnn-core 'fn-web-host-page-cursor segs)
                            (fnn-web-conn-page-response conn) (list code fields bodyp)
                            (fnn-web-conn-phase conn) :page-count)
                    (fnn-web-response face conn code fields bodyp))))
      (:health
       (fnn-owner-space-preobserve service t)
       (setf (fnn-web-conn-flow conn) (second action)
             (fnn-web-conn-event conn) (list :health-observation
               (fnn-owner-serialized service nil (lambda ()
                 (fnn-owner-core 'fn-web-host-health-observe (fnn-owner-sched-snapshot service))) :reader))))
      (:open (destructuring-bind (family address protected next) (rest action)
               (let ((cid (fnn-web-open service family address protected)))
                 (when cid (push cid (fnn-web-conn-opened conn)))
                 (setf (fnn-web-conn-flow conn) next (fnn-web-conn-event conn) (list :opened cid)))))
      (:send (destructuring-bind (cid start end next) (rest action)
               (setf (fnn-web-conn-cid conn) cid (fnn-web-conn-cmd-at conn) start
                     (fnn-web-conn-cmd-end conn) end (fnn-web-conn-flow conn) next
                     (fnn-web-conn-phase conn) :feed)
               (setf (fnn-web-conn-reply-scan conn)
                     (and (fnn-core 'fn-web-host-stream-p next)
                          (fnn-core 'fn-web-host-stream-start next))
                     (fnn-web-conn-captured-plans conn) nil)
               (fnn-web-fill (fnn-web-conn-in conn) (fnn-make-octets 0))))
      (:close (destructuring-bind (cid next) (rest action)
                (fnn-web-cleanup face conn (list :close cid)
                  (lambda () (fnn-owner-serialized service cid
                    (lambda () (fnn-owner-action 'fn-owner-close cid)) :reader)))
                (fnn-web-cleanup face conn (list :release cid)
                  (lambda () (fnn-owner-serialized service nil
                    (lambda () (fnn-owner-action 'fn-owner-exposure-release cid)) :reader)))
                (setf (fnn-web-conn-opened conn) (remove cid (fnn-web-conn-opened conn))
                      (fnn-web-conn-flow conn) next (fnn-web-conn-event conn) (list :closed)
                      (fnn-web-conn-leased conn) nil)))
      (t (fnn-fault "malformed web action")))))

(defun fnn-web-feed-owned-p (face conn)
  ;; One logical reader connection has one response pin and one await slot.
  ;; Acquire through the complete HTTP semantic flow, not just one command.
  (or (fnn-web-conn-leased conn)
      (unless (some (lambda (other)
                      (and (not (eq conn other)) (fnn-web-conn-leased other)
                           (eql (fnn-web-conn-cid conn) (fnn-web-conn-cid other))))
                    (fnn-web-face-conns face))
        (setf (fnn-web-conn-leased conn) t))))

(defun fnn-web-await-publish (face conn completion)
  (sb-thread:with-mutex ((fnn-web-face-lock face))
    (unless (fnn-web-conn-closedp conn)
      (setf (fnn-web-conn-completion conn) (list completion))
      (fnn-web-wake-locked face))))

(defun fnn-web-cold-start (conn read mode)
  (let ((since (fnn-owner-monotonic-ms)))
    (setf (fnn-web-conn-line-since conn) (or (fnn-web-conn-line-since conn) since)
          (fnn-web-conn-cold conn) (list read mode since)
          (fnn-web-conn-phase conn) :cold
          (fnn-web-conn-resume-at conn) (fnn-mux-ms-ticks 2))))

(defun fnn-web-feed-step (face conn)
  (unless (fnn-web-feed-owned-p face conn) (return-from fnn-web-feed-step nil))
  (let* ((service (fnn-web-face-service face)) (cid (fnn-web-conn-cid conn))
         (pending (fnn-web-conn-pending conn)))
    (unless pending
      (when (= (fnn-web-conn-cmd-at conn) (fnn-web-conn-cmd-end conn))
        (if (fnn-web-conn-reply-scan conn)
            (fnn-web-apply-action face conn
              (fnn-core 'fn-web-host-stream-page (fnn-web-face-config face)
                        (fnn-web-conn-flow conn) (fnn-web-conn-reply-scan conn)))
          (setf (fnn-web-conn-phase conn) :event (fnn-web-conn-event conn) '(:reply)))
        (return-from fnn-web-feed-step nil))
      (let ((end (fnn-core 'fn-web-host-window-end (fnn-web-conn-cmd-at conn)
                           (fnn-web-conn-cmd-end conn))))
        (setq pending (fnn-web-slice (fnn-web-conn-out conn) (fnn-web-conn-cmd-at conn) end))
        (setf (fnn-web-conn-pending conn) pending)))
    (let* ((word (fnn-web-conn-cold-word conn))
           (results (multiple-value-list
                     (destructuring-bind (&optional w since now limit line-since) word
                       (fnn-owner-handle-chunk-step service cid pending nil :reader nil
                                                   w line-since since now limit)))))
      (setf (fnn-web-conn-cold-word conn) nil)
      (case (first results)
        (:cold (fnn-web-cold-start conn (second results) :feed))
        (:defer (setf (fnn-web-conn-resume-at conn) (fnn-mux-ms-ticks (min (second results) 1000))))
        (otherwise
         (let ((plan nil) (used nil) (closing nil))
           (if (eq (first results) :await)
               (destructuring-bind (tag step redeem close starttls consumed) results
                 (declare (ignore tag starttls))
                 (setq used consumed closing close)
                 (setf (fnn-web-conn-await conn) (list step redeem)
                       (fnn-web-conn-phase conn) :await)
                 (let ((early (fnn-owner-await-register service cid
                                (lambda (completion) (fnn-web-await-publish face conn completion))
                                (fnn-web-conn-socket conn))))
                   (when early (fnn-web-await-publish face conn early))))
             (destructuring-bind (step-plan close starttls consumed &rest more) results
               (declare (ignore more))
               (when starttls (fnn-fault "web logical connection requested a transport change"))
               (setq plan step-plan used consumed closing close)
               (when (fnn-web-conn-reply-scan conn)
                 (push plan (fnn-web-conn-captured-plans conn)))
               (setf (fnn-web-conn-plan conn) plan (fnn-web-conn-phase conn) :render)))
           (unless (and (integerp used) (<= 0 used (length pending))
                        (or (> used 0) closing))
             (fnn-fault "logical web feed consumed no input"))
           (incf (fnn-web-conn-cmd-at conn) used)
           (setf (fnn-web-conn-pending conn) (and (< used (length pending)) (subseq pending used))
                 (fnn-web-conn-closing conn) closing
                 (fnn-web-conn-line-since conn) nil)))))))

(defun fnn-web-await-step (face conn)
  (let ((cell nil))
    (sb-thread:with-mutex ((fnn-web-face-lock face))
      (setq cell (fnn-web-conn-completion conn))
      (setf (fnn-web-conn-completion conn) nil))
    (when cell
      (let ((completion (first cell)))
        (if (eq completion :uncertain)
            (fnn-web-finish face conn)
          (progn
            (when (and (consp completion) (eq (car completion) :close))
              (setq completion (cdr completion))
              (setf (fnn-web-conn-closing conn) t))
            (destructuring-bind (step redeem) (fnn-web-conn-await conn)
              (setf (fnn-web-conn-plan conn) (fnn-core 'fn-splan-step-plan step completion redeem)
                    (fnn-web-conn-phase conn) :render
                    (fnn-web-conn-await conn) nil)
              (when (fnn-web-conn-reply-scan conn)
                (push (fnn-web-conn-plan conn) (fnn-web-conn-captured-plans conn))))))))))

(defun fnn-web-render-step (face conn)
  (let ((service (fnn-web-face-service face)) (cid (fnn-web-conn-cid conn))
        (plan (fnn-web-conn-plan conn)))
    (if plan
        (multiple-value-bind (part rest donep yieldedp read)
            (fnn-owner-render-next-quantum service cid plan :reader)
          (cond (read (fnn-web-cold-start conn read :render))
                (t (if (fnn-web-conn-reply-scan conn)
                       (progn
                         (fnn-web-fill (fnn-web-conn-in conn) part)
                         (setf (fnn-web-conn-reply-scan conn)
                               (fnn-core 'fn-web-host-stream-scan
                                         (fnn-web-conn-reply-scan conn) (fnn-web-conn-in conn))))
                     (fnn-web-append (fnn-web-conn-in conn) part))
                   (setf (fnn-web-conn-plan conn) (if donep nil rest))
                   (when (and (not donep) yieldedp)
                     (setf (fnn-web-conn-resume-at conn)
                           (fnn-mux-ms-ticks (fnn-core 'fn-splan-cursor-resume-ms)))))))
      (progn
        ;; The final article plan remains pinned through both HTML passes
        ;; and the final socket suffix. Earlier GROUP plans are immutable
        ;; status lists, and settle before the next command acquires its pin.
        (unless (and (fnn-web-conn-reply-scan conn)
                     (or (fnn-web-conn-closing conn)
                         (= (fnn-web-conn-cmd-at conn) (fnn-web-conn-cmd-end conn))))
          (fnn-owner-response-unpin service cid))
        (if (fnn-web-conn-closing conn)
            (setf (fnn-web-conn-phase conn) (if (fnn-web-conn-reply-scan conn) :feed :event)
                  (fnn-web-conn-event conn) '(:reply) (fnn-web-conn-pending conn) nil
                  (fnn-web-conn-cmd-at conn) (fnn-web-conn-cmd-end conn))
          (setf (fnn-web-conn-phase conn) :feed))))))

(defun fnn-web-cold-step (face conn)
  (destructuring-bind (read mode issued) (fnn-web-conn-cold conn)
    (multiple-value-bind (word since now limit)
        (fnn-owner-cold-poll (fnn-web-face-service face) read (fnn-web-conn-line-since conn) issued)
      (cond ((and (consp word) (eq (first word) :wait))
             (setf (fnn-web-conn-resume-at conn) (fnn-mux-ms-ticks (min (second word) 2))))
            ((and (member mode '(:render :replay)) (not (eq word :serve)))
             ;; No substitute reply or fabricated terminator after a partial
             ;; semantic reply. The browser receives no HTTP outcome.
             (fnn-web-finish face conn))
            (t (setf (fnn-web-conn-cold conn) nil (fnn-web-conn-phase conn) mode
                     (fnn-web-conn-cold-word conn)
                     (and (eq mode :feed) (list word since now limit (fnn-web-conn-line-since conn)))))))))

(defun fnn-web-replay-start (conn need return-phase)
  (let ((forward (and (fnn-web-conn-replay-tail conn)
                      (fnn-core 'fn-web-host-replay-forward-p need
                                (fnn-web-conn-replay-tail-base conn) (fnn-web-conn-replay-at conn)))))
    (unless forward
      (setf (fnn-web-conn-replay-plans conn) (reverse (fnn-web-conn-captured-plans conn))
            (fnn-web-conn-replay-plan conn) nil (fnn-web-conn-replay-at conn) 0
            (fnn-web-conn-replay-tail conn) nil))
    (setf (fnn-web-conn-replay-use-tail conn) forward
          (fnn-web-conn-replay-need conn) need
          (fnn-web-conn-replay-return conn) return-phase
          (fnn-web-conn-window-base conn) (car need) (fnn-web-conn-phase conn) :replay)
    (fnn-web-fill (fnn-web-conn-in conn) (fnn-make-octets 0))))

(defun fnn-web-replay-part (conn part base)
  (destructuring-bind (start end next complete)
      (fnn-core 'fn-web-host-replay-slice base (length part) (fnn-web-conn-replay-need conn))
    (when (< start end)
      (fnn-web-append (fnn-web-conn-in conn) (subseq part start end)))
    (when complete
      (setf (fnn-web-conn-phase conn) (fnn-web-conn-replay-return conn)
            (fnn-web-conn-replay-need conn) nil))
    next))

(defun fnn-web-replay-step (face conn)
  ;; One retained tail prevents a monotone body from rescanning its prefix
  ;; at every window boundary. Backward header/link seeks restart the same
  ;; immutable plan, without rerunning a semantic command.
  (when (fnn-web-conn-replay-use-tail conn)
    (setf (fnn-web-conn-replay-use-tail conn) nil)
    (fnn-web-replay-part conn (fnn-web-conn-replay-tail conn) (fnn-web-conn-replay-tail-base conn))
    (return-from fnn-web-replay-step nil))
  (unless (fnn-web-conn-replay-plan conn)
    (let ((plans (fnn-web-conn-replay-plans conn)))
      (unless plans (fnn-fault "captured web reply ended before its requested span"))
      (setf (fnn-web-conn-replay-plan conn) (car plans)
            (fnn-web-conn-replay-plans conn) (cdr plans))
      (unless (fnn-web-conn-replay-plan conn) (return-from fnn-web-replay-step nil))))
  (multiple-value-bind (part rest done yielded read)
      (fnn-owner-render-next-quantum (fnn-web-face-service face) (fnn-web-conn-cid conn)
                                   (fnn-web-conn-replay-plan conn) :reader)
    (cond (read (fnn-web-cold-start conn read :replay))
          (t
           (let ((base (fnn-web-conn-replay-at conn)))
             (setf (fnn-web-conn-replay-tail conn) part (fnn-web-conn-replay-tail-base conn) base
                   (fnn-web-conn-replay-at conn) (fnn-web-replay-part conn part base)
                   (fnn-web-conn-replay-plan conn) (unless done rest)))
           (when (and yielded (not done))
             (setf (fnn-web-conn-resume-at conn)
                   (fnn-mux-ms-ticks (fnn-core 'fn-splan-cursor-resume-ms))))))))

(defun fnn-web-page-step (face conn)
  ;; The retained reply and immutable segment plan belong to this exact
  ;; job; neither is read under O or copied into a whole HTML buffer.
  (let ((emitp (eq (fnn-web-conn-phase conn) :page-emit)))
    (destructuring-bind (octets next count done &optional need)
        (if (fnn-web-conn-reply-scan conn)
            (fnn-call 'fn-web-host-window-page-step (fnn-web-conn-page-cursor conn)
                      (fnn-web-conn-window-base conn) (fnn-web-conn-page-count conn)
                      emitp (fnn-web-conn-in conn))
          (fnn-call 'fn-web-host-page-step (fnn-web-conn-page-cursor conn)
                    (fnn-web-conn-page-count conn) emitp (fnn-web-conn-in conn)))
      (setf (fnn-web-conn-page-cursor conn) next
            (fnn-web-conn-page-count conn) count)
      (when (and need (null octets))
        (fnn-web-replay-start conn need (if emitp :page-emit :page-count))
        (return-from fnn-web-page-step nil))
      (if emitp
          (progn
            (setf (fnn-web-conn-page-done conn) done)
            (when octets
              (unless (fnn-octet-list-p octets) (fnn-fault "malformed web page window"))
              (setf (fnn-web-conn-wire conn) (fnn-octets octets)
                    (fnn-web-conn-wire-at conn) 0 (fnn-web-conn-phase conn) :write
                    (fnn-web-conn-want conn) :output))
            (when (and done (null octets))
              (setf (fnn-web-conn-answered conn) t)
              (fnn-web-finish face conn)))
        (when done
          (destructuring-bind (code fields bodyp) (fnn-web-conn-page-response conn)
            (setf (fnn-web-conn-page-cursor conn)
                  (fnn-core 'fn-web-host-page-cursor (fnn-web-conn-page-segs conn))
                  (fnn-web-conn-page-count conn) 0
                  (fnn-web-conn-page-done conn) (not bodyp))
            (fnn-web-response face conn code fields bodyp count)))))))

(defun fnn-web-write-ready (face conn)
  (let* ((data (fnn-web-conn-wire conn))
         (progress (fnn-transport-write-now (fnn-web-conn-fd conn) (fnn-web-conn-channel conn)
                                         data (fnn-web-conn-wire-at conn))))
    (cond ((member progress '(:input :output)) (setf (fnn-web-conn-want conn) progress))
          (t
           (incf (fnn-web-conn-wire-at conn) progress)
           (when (= (fnn-web-conn-wire-at conn) (length data))
             (if (fnn-web-conn-pagep conn)
                 (if (fnn-web-conn-page-done conn)
                     (progn (setf (fnn-web-conn-answered conn) t)
                            (fnn-web-finish face conn))
                   (setf (fnn-web-conn-phase conn) :page-emit
                         (fnn-web-conn-want conn) nil))
               (let ((at (fnn-web-conn-body-at conn)) (end (fnn-web-conn-body-end conn)))
               (if (= at end)
                   (progn (setf (fnn-web-conn-answered conn) t)
                          (fnn-web-finish face conn))
                 (let ((next (fnn-core 'fn-web-host-window-end at end)))
                   (setf (fnn-web-conn-wire conn) (fnn-web-slice (fnn-web-conn-out conn) at next)
                         (fnn-web-conn-wire-at conn) 0 (fnn-web-conn-body-at conn) next
                         (fnn-web-conn-want conn) :output))))))))))

(defun fnn-web-handshake-ready (conn)
  (let ((result (fnn-tls-accept-step (fnn-web-conn-ssl conn))))
    (if (eq result :done)
        (setf (fnn-web-conn-channel conn) (fnn-tls-channel-of (fnn-web-conn-ssl conn) (fnn-web-conn-fd conn))
              (fnn-web-conn-ssl conn) nil (fnn-web-conn-phase conn) :head
              (fnn-web-conn-want conn) :input)
      (setf (fnn-web-conn-want conn) result))))

(defun fnn-web-advance (face conn &optional ready)
  (fnn-web-job-consume face conn)
  (handler-case
      (cond ((fnn-web-conn-closedp conn) nil)
            ((>= (fnn-web-seconds) (fnn-web-conn-deadline conn)) (fnn-web-finish face conn))
            ((fnn-web-conn-job conn) nil)
            ((< (fnn-now) (fnn-web-conn-resume-at conn)) nil)
            (t
             (case (fnn-web-conn-phase conn)
               (:event (if (fnn-core 'fn-web-host-private-reply-p
                                    (fnn-web-conn-flow conn) (fnn-web-conn-event conn))
                           (fnn-web-job-submit face conn :private-reply)
                         (fnn-web-event face conn)))
               (:private-begin (fnn-web-job-submit face conn :private-begin))
               (:feed (when (fnn-web-feed-owned-p face conn) (fnn-web-job-submit face conn :feed)))
               (:await (fnn-web-await-step face conn))
               (:render (fnn-web-job-submit face conn :render))
               (:replay (fnn-web-job-submit face conn :replay))
               ((:page-count :page-emit) (fnn-web-job-submit face conn (fnn-web-conn-phase conn)))
               (:cold (fnn-web-job-submit face conn :cold))
               (:handshake (when ready (fnn-web-handshake-ready conn)))
               ((:head :body) (when (or ready (and (fnn-web-conn-channel conn)
                                                   (fnn-tls-pending-p (fnn-web-conn-channel conn))))
                                (fnn-web-read-ready face conn)))
               (:write (when ready (fnn-web-write-ready face conn))))))
    ((or fnn-os-error sb-bsd-sockets:socket-error fnn-tls-error) () (fnn-web-finish face conn))
    (serious-condition (condition)
      (unwind-protect
           (fnn-owner-thread-escape (fnn-web-face-service face) condition "web request")
        (fnn-web-finish face conn)))))

(defun fnn-web-adopt (face socket)
  (let ((conn (%make-fnn-web-conn :socket socket :deadline (+ (fnn-web-seconds) (fnn-core 'fn-web-host-request-seconds)))))
    ;; Publish custody before any fallible TLS setup. Terminal cleanup can
    ;; then always find an accepted descriptor.
    (push conn (fnn-web-face-conns face))
    (setf (fnn-web-conn-fd conn) (fnn-socket-fd socket)
          (fnn-web-conn-in conn) (create-fn-octets$c)
          (fnn-web-conn-out conn) (create-fn-octets$c))
    (when (fnn-web-face-tls-context face)
      (setf (fnn-web-conn-phase conn) :handshake
            (fnn-web-conn-ssl conn) (fnn-tls-accept-begin (fnn-web-face-tls-context face) (fnn-web-conn-fd conn))))
    conn))

(defun fnn-web-iterate (face)
  ;; Each live record receives one semantic or readiness quantum per pass.
  ;; Socket readiness and asynchronous completions do not block this actor.
  ;; Stateful event/session owner admission still runs under O. Captured
  ;; reply plan construction is private worker work, but is not yet a
  ;; bounded semantic quantum; this is not full semantic-event fairness.
  (dolist (conn (fnn-web-face-conns face)) (fnn-web-advance face conn))
  (setf (fnn-web-face-conns face)
        (remove-if (lambda (conn) (and (fnn-web-conn-closedp conn) (fnn-web-conn-semantic-ended conn)
                                       (null (fnn-web-conn-job conn))))
                   (fnn-web-face-conns face)))
  (let* ((conns (fnn-web-face-conns face)) (listener (fnn-web-face-listener face))
         (capacity (< (length conns) (fnn-web-face-capacity face)))
         (fds (coerce (list* (fnn-web-face-wake-read face)
                                  (if capacity (fnn-socket-fd listener) -1)
                                  (mapcar (lambda (conn) (if (fnn-web-conn-closedp conn) -1 (fnn-web-conn-fd conn))) conns)) 'vector))
         (events (coerce (list* +fnn-mux-pollin+ +fnn-mux-pollin+
                       (mapcar (lambda (conn) (case (and (not (fnn-web-conn-job conn)) (not (fnn-web-conn-closedp conn)) (fnn-web-conn-want conn))
                                 (:input +fnn-mux-pollin+) (:output +fnn-mux-pollout+) (t 0))) conns)) 'vector))
         ;; Pending semantic work receives another pass immediately; only
         ;; readiness/dependency/completion waits permit the bounded poll.
         (work (some (lambda (conn) (and (not (fnn-web-conn-job conn)) (not (fnn-web-conn-closedp conn)) (member (fnn-web-conn-phase conn) '(:event :private-begin :render :replay :feed :page-count :page-emit))
                                        (or (not (eq (fnn-web-conn-phase conn) :feed))
                                            (fnn-web-feed-owned-p face conn))
                                        (>= (fnn-now) (fnn-web-conn-resume-at conn)))) conns))
         (cold (some (lambda (conn) (eq (fnn-web-conn-phase conn) :cold)) conns))
         (timeout (if work 0
                    (loop with ms = (if cold 2 250) for conn in conns
                          for left = (- (fnn-web-conn-resume-at conn) (fnn-now))
                          when (> left 0) do (setf ms (min ms (max 1 (ceiling (* left 1000) internal-time-units-per-second))))
                          finally (return ms))))
         (ready (fnn-mux-poll fds events timeout)))
    (when (not (zerop (aref ready 0)))
      (let ((buffer (fnn-make-octets 64)))
        (fnn-mux-read-plain (fnn-web-face-wake-read face) buffer)))
    (when (and capacity (not (zerop (logand (aref ready 1) +fnn-mux-pollin+))))
      (let ((socket (fnn-accept-observe listener 0)))
        (unless (eq socket :timeout) (fnn-web-adopt face socket))))
    (loop for conn in conns for i from 2 do
      (let ((event (aref ready i)))
        (when (not (zerop event))
          (if (and (not (zerop (logand event +fnn-mux-poll-trouble+)))
                   (or (fnn-web-conn-job conn)
                       (member (fnn-web-conn-phase conn) '(:await :cold))))
              (fnn-web-finish face conn)
            (fnn-web-advance face conn t)))))))

(defun fnn-web-actor-body (face)
  (unwind-protect
       (loop until (or *fnn-sigterm-requested* (fnn-web-face-stop face)
                       (fnn-owner-service-stopping (fnn-web-face-service face)))
             do (fnn-web-iterate face))
    (dolist (conn (fnn-web-face-conns face)) (fnn-web-finish face conn))
    ;; Close publication under its lock before freeing either pipe fd.
    (sb-thread:with-mutex ((fnn-web-face-lock face))
      (setf (fnn-web-face-wake-closed face) t (fnn-web-face-jobs-closed face) t)
      (sb-thread:condition-broadcast (fnn-web-face-job-ready face))
      (sb-posix:close (fnn-web-face-wake-read face))
      (sb-posix:close (fnn-web-face-wake-write face)))))

(def-actor fnn-web-spawn :thread-name "fn web face" :roster t)
(def-actor fnn-web-spawn-semantic :thread-name "fn web semantic" :roster t)

(defun fnn-web-start (service plan tls-context)
  (let* ((port (fnn-core 'fn-web-host-plan-port plan))
         (family (fnn-core 'fn-web-host-plan-family plan))
         (address (fnn-core 'fn-web-host-plan-address plan))
         (tls (fnn-core 'fn-web-host-plan-tls plan))
         (config (fnn-core 'fn-web-host-plan-config plan))
         (limits (fnn-owner-serialized service nil (lambda ()
                   (fnn-core 'fn-web-host-limits
                     (first (fnn-call 'fn-web-host-article-limit *the-live-state*)))) :reader)))
    (unless (and (integerp port) (< 0 port 65536) (member family '(:inet :inet6))
                 (fnn-octet-list-p address)) (fnn-fault "malformed web plan"))
    (when (and tls (null tls-context)) (fnn-fault "web TLS needs the listener certificate"))
    (fnn-owner-serialized service nil (lambda () (fnn-call 'fn-web-host-reset *the-live-state*)) :reader)
    (multiple-value-bind (listener bound-port)
        (fnn-listen port :address (coerce address '(simple-array (unsigned-byte 8) (*))) :family family :backlog 64)
      (let ((face (%make-fnn-web-face :plan plan :config config :limits limits :listener listener
                                    :capacity (fnn-core 'fn-web-host-connection-limit config)
                                    :tls-context (and tls tls-context) :service service)))
        (setq *fnn-web-face* face)
        (let ((started nil))
          (unwind-protect
               (progn
                 (multiple-value-bind (r w) (sb-posix:pipe)
                   (setf (fnn-web-face-wake-read face) r (fnn-web-face-wake-write face) w)
                   (fnn-set-nonblocking r) (fnn-set-nonblocking w))
                 (setf (fnn-web-face-semantic-thread face)
                       (fnn-web-spawn-semantic service (list face) (lambda () (fnn-web-semantic-body face))
                         (lambda (condition) (fnn-owner-thread-escape service condition "web semantic actor"))))
                 (setf (fnn-web-face-thread face)
                       (fnn-web-spawn service (list face) (lambda () (fnn-web-actor-body face))
                         (lambda (condition) (fnn-owner-thread-escape service condition "web actor"))))
                 (setq started t)
                 (fnn-out "LISTENING-WEB ~d" bound-port)
                 face)
            (unless started
              ;; A second actor's failed maker must not strand the first
              ;; actor on its empty mailbox during service shutdown.
              (sb-thread:with-mutex ((fnn-web-face-lock face))
                (setf (fnn-web-face-stop face) t (fnn-web-face-jobs-closed face) t)
                (sb-thread:condition-broadcast (fnn-web-face-job-ready face)))
              (when (fnn-web-face-semantic-thread face)
                (fnn-owner-actor-join service (fnn-web-face-semantic-thread face)))
              (unless (fnn-web-face-thread face)
                (sb-thread:with-mutex ((fnn-web-face-lock face))
                  (setf (fnn-web-face-wake-closed face) t)
                  (when (fnn-web-face-wake-read face) (sb-posix:close (fnn-web-face-wake-read face)))
                  (when (fnn-web-face-wake-write face) (sb-posix:close (fnn-web-face-wake-write face)))))
              (fnn-socket-shut listener))))))))

(defun fnn-web-close-face (service)
  "The owner's close hook follows physical actor drain."
  (declare (ignore service))
  (when *fnn-web-face*
    (setf (fnn-web-face-stop *fnn-web-face*) t)
    (fnn-socket-shut (fnn-web-face-listener *fnn-web-face*))
    (setq *fnn-web-face* nil)))

(defun fnn-web-run-hooks (listener-port tls-port certp)
  (when *fnn-operator-config-octets*
    (let ((plan (fnn-core 'fn-web-host-plan (fnn-octet-list *fnn-operator-config-octets*) listener-port tls-port certp)))
      (cond ((fnn-core 'fn-web-host-plan-web-p plan) (values plan))
            ((fnn-core 'fn-web-host-plan-refusal plan)
             (fnn-refuse "the [web] table is refused: ~(~a~)" (fnn-core 'fn-web-host-plan-refusal plan)))
            (t nil)))))
