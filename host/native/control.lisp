;;; Native bounded local-control transport for exact article submission.
;;;
;;; ACL2 owns the FNCT request/reply grammar, bounds, status vocabulary and
;;; exit projection in books/native-control.lisp.  This raw module only moves
;;; those octets over one AF_UNIX stream and invokes the serialized owner
;;; callback.  It never opens the Store and has no direct-store fallback.

(in-package "ACL2")


(defvar *fnn-hybrid-control-handler* nil)

























(defun fnn-control-reply-octets (status)
  (let ((reply
          (cond
            ;; The owner's FNLS page, already sealed by ACL2
            ;; (`fn-native-live-status-host-answer').
            ((and (consp status) (eq (first status) :live-status-reply))
             (second status))
            ;; A reply with no line seals kind 18 as before
            ;; (fn-ncline-read-of-a-lineless-encode).
            ((and (consp status) (eq (first status) :reasoned-reply))
             (fnn-core 'fn-native-control-host-lined-reply-encode
                       (second status) (third status) (fourth status)))
            ;; `tls reload' / the served line (PRF-212): FNCT kind 20,
            ;; sealed by ACL2 (host/native/tls-reload.lisp).
            ((and (consp status) (eq (first status) :tls-reply))
             (fnn-core 'fn-tlsr-host-reply-encode
                       (second status) (third status) (fourth status)))
            ((and (consp status) (eq (first status) :topic-reply))
             (fnn-core 'fn-native-control-host-topic-reply-encode
                       (second status)))
            ((and (consp status) (eq (first status) :consumer-poll-reply))
             (fnn-core 'fn-native-control-host-consumer-poll-reply-encode
                       (second status) (third status) (fourth status)))
            ((and (consp status) (eq (first status) :consumer-status-reply))
             (fnn-core 'fn-native-control-host-consumer-status-reply-encode
                       (second status) (third status) (fourth status)
                       (fifth status)))
            ((and (consp status) (eq (first status) :consumer-reply))
             (fnn-core 'fn-native-control-host-consumer-reply-encode
                       (second status) (third status)))
            (t (fnn-core 'fn-native-control-host-reply-encode status)))))
    (unless (fnn-octet-list-p reply)
      (fnn-fault "ACL2 refused a local-control reply status"))
    (fnn-octets reply)))



(defun fnn-control-stop-cut-armed-p ()
  "Whether FN_NATIVE_CONTROL_TEST_STOP arms the developer stop cut.

The variable is read only through `fnn-developer-selector', which answers NIL
on a production image; a production image never gets this far with it set,
because `fnn-developer-selector-gate' refuses to start (host/native/io.lisp).
So this function has no production branch, and the reply below has no
production conversion: an earlier version faulted here, after the owner had
already made the article durable, and the caller got exit 4 for an accepted
article (campaign dabebb84, F4)."
  (let ((raw (fnn-developer-selector "FN_NATIVE_CONTROL_TEST_STOP")))
    (when raw
      (unless (string= raw "after-submit")
        (fnn-fault "unknown FN_NATIVE_CONTROL_TEST_STOP cut: ~a" raw))
      t)))

(defun fnn-control-stop-calling-thread ()
  "Stop the process with a SIGSTOP directed at the calling thread.

A process-directed kill(getpid(), SIGSTOP) is delivered to whichever thread
the kernel picks (the main thread first, when it can take it), and the group
stop reaches this worker only asynchronously: the worker could return and
send its reply before it stopped (campaign dabebb84, F3; 2 of 5 clients got
ACCEPTED by hand).  pthread_kill(pthread_self(), SIGSTOP) queues the signal
on this thread, which dequeues it on its return from the syscall and starts
the group stop itself, so no instruction after this call runs until SIGCONT."
  (let ((code (sb-alien:alien-funcall
               (sb-alien:extern-alien "pthread_kill"
                                      (function sb-alien:int sb-alien:unsigned-long
                                                sb-alien:int))
               (sb-alien:alien-funcall
                (sb-alien:extern-alien "pthread_self"
                                       (function sb-alien:unsigned-long)))
               sb-posix:sigstop)))
    ;; This runs on a client worker after the owner answered; a failed stop
    ;; is reported and the reply goes out with the owner's own status.
    (unless (zerop code)
      (fnn-err "developer stop cut: pthread_kill returned ~d" code))))

(defun fnn-control-test-after-submit (status)
  "Developer-only process-stop cut after owner completion, before the reply."
  (when (and (fnn-control-stop-cut-armed-p)
             (member status '(:accepted :duplicate :refused :clock-unusable
                              :article-exceeds-profile-bound)))
    (fnn-out "CONTROL-SUBMITTED")
    (fnn-control-stop-calling-thread)))

(defun fnn-control-send-reply (socket status)
  "Transport ACL2's sealed status; the caller retains socket ownership."
  (handler-case
      (let ((fd (fnn-socket-fd socket)))
        (fnn-send-all fd (fnn-control-reply-octets status)
                      +fnn-control-io-seconds+)
        (fnn-graceful-close fd))
    (error () nil)))

(defun fnn-control-answering (control socket)
  "Withdraw SOCKET from the set a stop wakes, once its whole frame is read.

`fnn-control-stop' shuts every socket in that set so that a worker blocked in
its read returns.  A worker that has read its frame is no longer blocked on
the socket; it is computing the reply, and the request it is answering may be
the very one whose fault or uncertain observation stops the owner.  Shutting
its socket then threw away the owner's own terminal word: on the dabebb84
image a live `group create' that faulted the owner before publishing anything
reached the operator as a closed connection, which the client can only call
uncertain (exit 3), not the fault (exit 4) the owner had classified.  The
worker still ends its I/O under the reply deadline and `fnn-control-close'
joins it before the process exits."
  (fnn-with-control (control)
    (setf (fnn-control-state-clients control)
          (delete socket (fnn-control-state-clients control) :test #'eq))))

;; The running owner's [alerts] headroom_min_percent: ACL2's projection of
;; its run plan (fn-native-operator-host-result-health-min-percent), carried
;; for the health report the owner renders (books/native-health.lisp).
(defvar *fnn-health-min-percent* 0)

(defvar *fnn-live-status-buffers* nil
  "The owner's rendered status reports, one per kind, as ACL2 chose them
(`fn-native-live-status-host-answer'); read and replaced under the owner
mutex only.")

(defun fnn-control-live-status-legacy-answer (service request)
  "The running owner's page of its status report, under the owner mutex.

ACL2 decodes the request, renders the report from the Store, the
configuration and the connection pins the owner carries once per request
(offset 0), and pages from that rendered buffer
(`fn-native-live-status-host-answer').  The wrapper returns no `state', so
answering changes nothing the owner holds; the host keeps the buffers ACL2
returns.  The mutex keeps a render from observing a half-applied
transition.  The free space health reports is observed first, off the
mutex (HST-033: statvfs never runs inside the owner's critical section)."
  (fnn-owner-space-preobserve service t)
  (fnn-owner-serialized
   service nil
   (lambda ()
     (let ((answer (fnn-core 'fn-native-live-status-host-answer request
                             *fnn-live-status-buffers*
                             (fnn-store-observation
                              (fnn-owner-service-store service))
                             *fnn-health-min-percent*
                             ;; PKT-508: the log sink's counts for `health'.
                             (fnn-log-sink-snapshot)
                             ;; HST-023: the scheduler's hold and wait fold
                             ;; (books/owner-scheduler.lisp fn-osch-health-lines).
                             (fnn-owner-sched-snapshot service)
                             ;; the owner's arena: the reclaim line reads each
                             ;; article's stored length through it.
                             (fnn-live-arena)
                             ;; lane scale-reads: and each article's tombstone
                             ;; flag from the catalog's column.
                             (fnn-live-cat)
                             *the-live-state*)))
       (unless (and (consp answer) (consp (cdr answer))
                    (fnn-octet-list-p (first answer)))
         (fnn-fault "ACL2 returned a malformed live status page"))
       (setf *fnn-live-status-buffers* (second answer))
       (first answer)))
   :inspect))

; Fixed result publication runs within the owner wrapper, after its returned
; stobjs are retained and before scheduler cleanup. It constructs no frame.
(defun fnn-control-publish-inspect-answer (word answer)
 (unless (eq word :yield)
  (unless (and (consp answer) (consp (cdr answer))
               (fnn-octet-list-p (first answer)))
   (fnn-fault "ACL2 returned a malformed installed inspect page"))
  (setf *fnn-live-status-buffers* (second answer)))
 (values word answer))

; The installed closure owns capture, incremental preparation and paging.
; Each yield reenters with a fresh actual control turn. Its core report job
; retains the original source; the ticket itself never escapes a quantum.
(defun fnn-control-live-status-answer (service request)
 (let ((binding (fnn-owner-service-inspector-binding service)) (job-token nil)
       (cached nil) (cache-captured nil))
  (if (not binding) (fnn-control-live-status-legacy-answer service request)
   (loop
    (multiple-value-bind (word answer)
        (fnn-owner-serialized-with-control-turn
         service nil
         (lambda (slot nonce slots pool)
          ;; Capture under the first owner gate; later turns keep this exact
          ;; lexical cache even if another request publishes a new one.
          (unless cache-captured
           (setf cached *fnn-live-status-buffers* cache-captured t))
          (funcall binding request cached job-token slot nonce slots pool))
         :inspect nil #'fnn-control-publish-inspect-answer)
     (if (eq word :yield)
         (progn
          (unless (and (consp answer) (eq (first answer) :report-continuation)
                       (consp (cdr answer)) (second answer) (null (cddr answer)))
           (fnn-fault "ACL2 returned a malformed inspect continuation"))
          ;; Core checks this real reservation identity on the next turn.
          (setf job-token (second answer)))
       (return (first answer))))))))

(defvar *fnn-live-pages-cache* nil
  "The owner's paged-report cursors, as ACL2 chose them
(`fn-native-live-pages-host-answer'); read and replaced under the owner
mutex only.  A cursor holds the rest of the retention ledger its report
started from (an applicative value, shared with the Store, not copied).")

(defun fnn-control-live-pages-answer (service request)
  "The running owner's page of a paged report, under the owner mutex.

ACL2 decodes the request and answers one page of at most
`*fn-nls-chunk-octets*' octets from the cursor its version names, or starts
a report (version 0) from the retention the owner holds now, or answers
version-gone by name (`fn-nlp-answer').  Work and allocation per request are
one page; the report is never rendered whole.  The host keeps the cursors
ACL2 returns."
  (fnn-owner-serialized
   service nil
   (lambda ()
     (let ((answer (fnn-core 'fn-native-live-pages-host-answer request
                             *fnn-live-pages-cache* *the-live-state*)))
       (unless (and (consp answer) (consp (cdr answer))
                    (fnn-octet-list-p (first answer)))
         (fnn-fault "ACL2 returned a malformed live report page"))
       (setf *fnn-live-pages-cache* (second answer))
       (first answer)))
   :inspect))

(defun fnn-control-handle-client (control socket)
  (let* ((*fnn-owner-measure-label* :control)
         (service (fnn-control-state-service control))
         (maximum (fnn-control-state-read-maximum control))
         ;; PKT-453 (a): a frame of the reasoned kinds (13, 17) is answered
         ;; with the reasoned reply however its handling ends; ACL2 says
         ;; which (fn-native-control-reasoned-framep).
         (reasoned nil)
         (status
           (handler-case
               (let* ((frame (prog1 (fnn-control-read-frame socket maximum)
                               (fnn-control-answering control socket)))
                      ;; D27 (books/native-live-buffer.lisp, PRF-960): the
                      ;; frame is decoded in place from the control buffer,
                      ;; once, from one digest, under the control buffer lock;
                      ;; ACL2 owns the dispatch (fn-frb-site-decode-is-reference)
                      ;; and the host destructures (REASONED REQUEST ADMIN
                      ;; MODERATION TOPIC CONSUMER LIVE PAGES).  No list of
                      ;; the frame is built.
                      (decoded
                        (and (typep frame 'fnn-octets)
                             (let ((d (fnn-with-control-buffer ()
                                        (fnn-core 'fn-native-control-host-decode-frame
                                                  (fnn-octets-ctl-fill frame)))))
                               (setq reasoned (first d))
                               d)))
                      (request (and decoded (second decoded)))
                      (admin (and decoded (third decoded)))
                      ;; PKT-657, PKT-575: the moderation request (kind 21).
                      (moderation (and decoded (fourth decoded)))
                      (topic (and decoded (fifth decoded)))
                      ;; PKT-709: the plain request (kind 4) or the reasoned
                      ;; one (kind 22, the same payload), decided alike.
                      (consumer (and decoded (sixth decoded)))
                      ;; The FNLS requests: a live status request, else
                      ;; (lane obligations-paged) a paged report's request
                      ;; (FNLS frame kind 4, books/native-live-pages.lisp).
                      (live (and decoded (seventh decoded)))
                      (pages (and decoded (eighth decoded))))
                 (cond
                   (live
                    (list :live-status-reply
                          (fnn-control-live-status-answer
                           service (fnn-octet-list frame))))
                   (pages
                    (list :live-status-reply
                          (fnn-control-live-pages-answer
                           service (fnn-octet-list frame))))
                   ((and *fnn-hybrid-control-handler*
                         (funcall *fnn-hybrid-control-handler* service frame)))
                   ((and (consp topic) (eq (first topic) :topic))
                    (multiple-value-bind (owner-p uid)
                        (fnn-control-peer-is-owner-p socket)
                      (if owner-p
                          (list :topic-reply
                                (fnn-owner-topic-local-serialized
                                 service (second topic) (third topic)
                                 (fourth topic) uid))
                        (list :topic-reply :refused))))
                   ((and (consp consumer) (eq (car consumer) :consumer))
                      (if (fnn-control-peer-is-owner-p socket)
                        (if (member (second consumer) '(:wait :bound-wait))
                            ;; PRF-252: a wait sleeps outside the owner
                            ;; mutex and answers a poll's reply.
                            (fnn-owner-consumer-local-wait
                             service (second consumer) (third consumer)
                             (fourth consumer))
                          (fnn-owner-consumer-local-serialized
                           service (second consumer) (third consumer)
                           (fourth consumer)))
                      (list
                       :reason
                       (case (second consumer)
                         ((:poll :bound-poll :wait :bound-wait)
                          (list :consumer-poll-reply :refused nil nil))
                         (:status (list :consumer-status-reply :refused nil nil nil))
                         (otherwise (list :consumer-reply :refused nil)))
                       :not-owner)))
                   ;; Lane time-model-2 (PRF-311): a mutating request --
                   ;; an operator post, a live configuration change, a
                   ;; moderation decision -- while the disk is slow or
                   ;; stalled is answered BUSY (try later: nothing stored,
                   ;; nothing staged) at once, decided by ACL2 at a clock
                   ;; event appended now (fn-otm-admit-post), before it
                   ;; waits for the gate that the barrier in flight holds.
                   ((and (or (and (consp request) (eq (car request) :request))
                             (and (consp admin) (eq (car admin) :admin))
                             (and (consp moderation) (eq (car moderation) :moderation)))
                         (eq (fnn-owner-disk-admit service) :shed))
                    :busy)
                   ((and (consp request) (eq (car request) :request))
                    (let ((msgid (second request))
                         (groups (third request))
                         (article (fourth request)))
                     (unless (and (fnn-octet-list-p msgid)
                                  (listp groups)
                                  (every #'fnn-octet-list-p groups)
                                  (fnn-octet-list-p article))
                       (fnn-fault "ACL2 returned a malformed control request"))
                     (fnn-owner-control-submit-serialized
                      service (fnn-octets msgid)
                      (mapcar #'fnn-octets groups) (fnn-octets article))))
                   ((and (consp admin) (eq (car admin) :admin))
                    (fnn-owner-live-admin-serialized service (second admin)))
                   ((and (consp moderation) (eq (car moderation) :moderation))
                    (fnn-owner-moderation-serialized
                     service (second moderation) (third moderation)
                     (fourth moderation) (fifth moderation)))
                   (t :refused)))
             ;; The owner has already fenced itself on these two (exit 3 and
             ;; exit 4, `fnn-owner-shared-action-locked'); the reason goes to
             ;; the owner's log, and the caller gets the status word.
             (fnn-store-indeterminate (condition)
               (fnn-err "control request uncertain; owner fenced: ~a" condition)
               :uncertain)
             (fnn-store-fault (condition)
               (fnn-err "control request fault; owner stopped: ~a" condition)
               :fault)
             ;; PKT-264 (2): a refusal is no longer silent in the owner's
             ;; log; the line names the condition's class and its message
             ;; (the operator's reply word is still :refused).
             (fnn-store-error (condition)
               (fnn-err "control request refused (store-error): ~a" condition)
               ;; PKT-472 (e): ACL2 names the class as the refusal's reason.
               (list :reason :refused
                     (fnn-core 'fn-native-control-host-refusal-reason :store-error)))
             (fnn-os-error (condition)
               (fnn-err "control request refused (os-error): ~a" condition)
               ;; PKT-472 (e): ACL2 names the class as the refusal's reason.
               (list :reason :refused
                     (fnn-core 'fn-native-control-host-refusal-reason :os-error)))
             (sb-bsd-sockets:socket-error (condition)
               (fnn-err "control request refused (socket-error): ~a" condition)
               ;; PKT-472 (e): ACL2 names the class as the refusal's reason.
               (list :reason :refused
                     (fnn-core 'fn-native-control-host-refusal-reason :socket-error)))
             (error (condition)
               (fnn-owner-fault-service service nil condition)
               :fault))))
    ;; A peer that disappears here creates no uncertainty for the owner: the
    ;; status already records its durable observation.  The client, which did
    ;; not receive it, conservatively reports :uncertain.
    ;; An owner decision that named its reason answers (:reason STATUS
    ;; REASON) (host/native/owner.lisp fnn-owner-control-submit-serialized,
    ;; host/native/admin.lisp fnn-owner-live-admin-serialized); a reasoned
    ;; frame gets the reasoned reply (reason nil is ACL2's NONE), any other
    ;; frame the plain status an old client parses.
    ;; A limit decision also names its sentence, (:reason STATUS REASON
    ;; LINE): the reply carries ACL2's line (books/native-control-line.lisp,
    ;; kind 23).
    (let ((reason nil) (line nil))
      (when (and (consp status) (eq (first status) :reason))
        (setq reason (third status) line (fourth status) status (second status)))
      (fnn-control-test-after-submit
       (if (and (consp status) (eq (first status) :live-status-reply))
           nil
       (if (and (consp status)
                (member (first status)
                        '(:topic-reply :consumer-reply :consumer-poll-reply
                          :consumer-status-reply)))
           (second status) status)))
      (when (and reasoned (keywordp status))
        (setq status (list :reasoned-reply status reason line)))
      ;; PKT-709: a reasoned consumer request's refusal answers the reasoned
      ;; reply (its status and ACL2's reason); an acceptance answers the
      ;; consumer reply it always did.
      (when (and reasoned (consp status)
                 (member (first status) '(:consumer-reply :consumer-poll-reply
                                          :consumer-status-reply))
                 (not (eq (second status) :accepted)))
        (setq status (list :reasoned-reply (second status) reason)))
      (fnn-control-send-reply socket status))))

(defun fnn-control-client-done (control socket)
  (fnn-with-control (control)
    (setf (fnn-control-state-clients control)
          (delete socket (fnn-control-state-clients control) :test #'eq)
          (fnn-control-state-workers control)
          (delete sb-thread:*current-thread*
                  (fnn-control-state-workers control) :test #'eq))))

(defun fnn-control-launch-client (control socket)
  (let ((disposition nil))
    (fnn-with-control (control)
      ;; ACL2's disposition over the stop flag, the live worker count and
      ;; the profile of the store the owner opened, whose field 16 is the
      ;; ceiling (books/native-control-launch.lisp fn-ncla-launch-disposition,
      ;; PKT-700): the ceiling comparison is not the host's.  The accept loop
      ;; runs only after fnn-control-start, after the open.
      (setq disposition
            (fnn-core 'fn-native-control-host-launch-disposition
                      (and (fnn-control-state-stopping control) t)
                      (length (fnn-control-state-workers control))
                      (fnn-store-config
                       (fnn-owner-service-store
                        (fnn-control-state-service control)))))
      (case disposition
            ((:stopping :busy) nil)
            (:launch
             (push socket (fnn-control-state-clients control))
             (let ((worker
                     (sb-thread:make-thread
                      (lambda ()
                        (unwind-protect
                             (fnn-control-handle-client control socket)
                          (fnn-socket-shut socket)
                          (fnn-control-client-done control socket)))
                      :name "fn local control client")))
               (push worker (fnn-control-state-workers control))
               (setq disposition :launched)))
            (t (fnn-fault "ACL2 returned an invalid control launch disposition"))))
    (case disposition
      (:stopping (fnn-socket-shut socket))
      (:busy
       ;; The accept thread owns an over-ceiling socket and can return ACL2's
       ;; bounded BUSY frame without spawning an untracked worker.
       (unwind-protect (fnn-control-send-reply socket :busy)
         (fnn-socket-shut socket))))))

(defun fnn-control-accept-loop (control)
  (let ((listener (fnn-control-state-listener control)))
    (loop
      (when (fnn-with-control (control)
              (fnn-control-state-stopping control))
        (return))
      (handler-case
          (let ((socket (fnn-accept-observe listener 1)))
            (unless (eq socket :timeout)
              (fnn-control-launch-client control socket)))
          (sb-bsd-sockets:socket-error (condition)
            (unless (fnn-with-control (control)
                      (fnn-control-state-stopping control))
              (fnn-owner-fault-service
               (fnn-control-state-service control) nil condition))
            (return))
          (error (condition)
            (fnn-owner-fault-service
             (fnn-control-state-service control) nil condition)
            (return))))))

(defun fnn-control-start (control service posting-enabledp)
  (let ((configured
          (fnn-owner-serialized
           service nil
           (lambda ()
             (fnn-owner-action 'fn-owner-posting-configure posting-enabledp)))))
    (unless (eq configured :configured)
      (fnn-fault "owner refused ACL2 posting policy")))
  ;; The read bound of one control connection, from the profile the owner
  ;; carries (fixed while it runs): ACL2's `fn-nctrl-read-bound-for' of the
  ;; profile's article and group bounds, or its hybrid twin when hybrid
  ;; control is built in.
  (let* ((bounds (fnn-owner-serialized
                  service nil
                  (lambda () (fnn-owner-core 'fn-owner-control-profile-bounds))))
         (a (first bounds)) (g (second bounds))
         (maximum (if (fboundp 'fn-native-hybrid-control-host-read-bound)
                      (fnn-core 'fn-native-hybrid-control-host-read-bound a g)
                    (fnn-core 'fn-native-control-host-read-bound a g))))
    (unless (and (integerp maximum) (> maximum 0))
      (fnn-fault "ACL2 returned no control read bound"))
    (setf (fnn-control-state-read-maximum control) maximum))
  (fnn-control-acquire-lease control)
  (let* ((path (fnn-control-state-path control))
         (listener (fnn-control-listen path))
         (info (fnn-lstat path)))
    (unless (fnn-control-socket-path-p info)
      (fnn-socket-shut listener)
      (fnn-fault "control socket did not appear at configured path"))
    (setf (fnn-control-state-service control) service
          (fnn-control-state-listener control) listener
          (fnn-control-state-device control) (sb-posix:stat-dev info)
          (fnn-control-state-inode control) (sb-posix:stat-ino info)
          (fnn-control-state-accept-thread control)
          (sb-thread:make-thread
           (lambda () (fnn-control-accept-loop control))
           :name "fn local control accept"))
    (fnn-out "CONTROL ~a" path)))

(defun fnn-control-stop (control service)
  (declare (ignore service))
  (let ((listener nil) (clients nil) (first nil))
    (fnn-with-control (control)
      (unless (fnn-control-state-stopping control)
        (setf (fnn-control-state-stopping control) t
              listener (fnn-control-state-listener control)
              clients (copy-list (fnn-control-state-clients control))
              first t)))
    (when first
      (when listener
        (ignore-errors
          (sb-bsd-sockets:socket-shutdown listener :direction :io)))
      (dolist (socket clients)
        ;; Shutdown wakes the blocked read without releasing the descriptor;
        ;; the owning worker performs the sole final close after its I/O ends.
        (ignore-errors
          (sb-bsd-sockets:socket-shutdown socket :direction :io))))))

(defun fnn-control-close (control service)
  (declare (ignore service))
  (unwind-protect
       (progn
         (let ((accept-thread (fnn-control-state-accept-thread control)))
           (when accept-thread (sb-thread:join-thread accept-thread)))
         (loop
           (let ((workers
                   (fnn-with-control (control)
                     (copy-list (fnn-control-state-workers control)))))
             (when (null workers) (return))
             (dolist (worker workers) (sb-thread:join-thread worker))))
         (let ((listener (fnn-control-state-listener control)))
           (when listener
             (setf (fnn-control-state-listener control) nil)
             (fnn-socket-shut listener)))
         (let* ((path (fnn-control-state-path control))
                (info (fnn-lstat path)))
           (when (and (fnn-control-socket-path-p info)
                      (= (sb-posix:stat-dev info)
                         (fnn-control-state-device control))
                      (= (sb-posix:stat-ino info)
                         (fnn-control-state-inode control)))
             (fnn-unlink path))))
    (fnn-control-release-lease control)))

(defun fnn-control-owner-run-normalized
    (store-octets listener-host-octets listener-port oncep max-connections
     control-path-octets posting-enabledp &optional tls-context tls-port)
  "Add composable lifecycle hooks while leaving owner normalization intact."
  (unless (and (typep control-path-octets 'fnn-octets)
               (> (length control-path-octets) 0)
               (member posting-enabledp '(t nil)))
    (fnn-fault "malformed ACL2 control run plan"))
  (let* ((lease-octets
           (fnn-core 'fn-native-control-host-lease-path
                     (fnn-octet-list control-path-octets)))
         (lease-path
           (and (fnn-octet-list-p lease-octets)
                (fnn-octets-string (fnn-octets lease-octets))))
         (control (%make-fnn-control-state
                   :path (fnn-octets-string control-path-octets)
                   :lease-path lease-path))
         (*fnn-owner-start-hooks*
           (append *fnn-owner-start-hooks*
                   (list (lambda (service)
                           (fnn-control-start control service posting-enabledp)))))
         (*fnn-owner-stop-hooks*
           (append *fnn-owner-stop-hooks*
                   (list (lambda (service)
                           (fnn-control-stop control service)))))
         (*fnn-owner-close-hooks*
           (append *fnn-owner-close-hooks*
                   (list (lambda (service)
                           (fnn-control-close control service))))))
    (unless lease-path
      (fnn-fault "ACL2 refused the control lease path"))
    ;; A developer image validates its control stop selector here, before
    ;; the store opens, so a malformed value never surfaces on a worker after
    ;; a durable submission.
    (fnn-control-stop-cut-armed-p)
    ;; PKT-605: the connection budget counts these clients' threads, the
    ;; store profile's ceiling (PKT-700: fnn-mux-thread-count reads it after
    ;; the open).
    (fnn-owner-run-normalized store-octets listener-host-octets listener-port
                              oncep max-connections tls-context tls-port)))















(defun fnn-control-topic-local (path-octets operation sequence quota)
  "Send an ACL2-framed local topic operation to the authenticated owner."
  (let ((request-list
          (fnn-core 'fn-native-control-host-topic-request-encode
                    operation sequence quota))
        (socket nil) (stage :before-submission))
    (unless (fnn-octet-list-p request-list)
      (fnn-fault "ACL2 refused local topic request"))
    (unwind-protect
         (handler-case
             (progn
               (setq socket (fnn-control-connect
                             (fnn-octets-string path-octets)))
               (let ((fd (fnn-socket-fd socket)))
                 (setq stage :after-submission)
                 (fnn-control-send-request socket fd (fnn-octets request-list))
                 (let* ((frame (fnn-control-read-frame
                                socket (fnn-core
                                        'fn-native-control-host-max-frame)))
                        (reply (and (typep frame 'fnn-octets)
                                    (fnn-core
                                     'fn-native-control-host-topic-reply-decode
                                     (fnn-octet-list frame))))
                        (ordinary
                          (and (typep frame 'fnn-octets)
                               (fnn-core 'fn-native-control-host-reply-decode
                                         (fnn-octet-list frame)))))
                   (cond
                    ((and (consp reply) (eq (first reply) :topic-reply)
                          (member (second reply)
                                  '(:accepted :replayed-historical
                                    :refused :uncertain :fault)))
                     (second reply))
                    ((member ordinary '(:refused :uncertain :fault :busy))
                     (if (eq ordinary :busy) :refused ordinary))
                    (t (fnn-control-transport-outcome stage))))))
           (error () (fnn-control-transport-outcome stage)))
      (when socket (fnn-socket-shut socket)))))

;; The reply kind a consumer OPERATION answers on, as the client reports it.
(defun fnn-control-consumer-reply-tag (operation)
  (case operation
    ((:poll :bound-poll :wait :bound-wait) :consumer-poll-reply)
    (:status :consumer-status-reply)
    (otherwise :consumer-reply)))

(defun fnn-control-consumer-bare-reply (operation status)
  "The reply list for an outcome that carries no cursor, report or counts."
  (list (fnn-control-consumer-reply-tag operation) status nil nil nil))

(defun fnn-control-consumer-reply-okp (operation reply)
  "Whether REPLY, ACL2's decoded consumer reply, has the shape OPERATION's
client prints from (the checks the host made before PKT-709)."
  (and (consp reply)
       (eq (first reply) (fnn-control-consumer-reply-tag operation))
       (member (second reply) '(:accepted :refused :uncertain :fault))
       (if (eq operation :status)
           (or (and (eq (second reply) :accepted)
                    (every (lambda (value)
                             (and (integerp value) (not (minusp value))))
                           (cddr reply)))
               (and (not (eq (second reply) :accepted))
                    (null (third reply))
                    (null (fourth reply))
                    (null (fifth reply))))
         (and (fnn-octet-list-p (third reply))
              (or (not (member operation '(:poll :bound-poll :wait :bound-wait)))
                  (fnn-octet-list-p (fourth reply)))))))

(defun fnn-control-consumer-deadline (operation second)
  ;; PRF-252: a wait answers after its timeout.
  (+ +fnn-control-io-seconds+
     (case operation
       (:wait second)
       (:bound-wait (first second))
       (otherwise 0))))

(defun fnn-control-consumer-maximum (operation)
  "The reply bound: the operation's consumer reply, or the reasoned reply a
refusal comes as (PKT-709), whichever is larger (a status reply is 13
payload octets; a reason word is not)."
  (max (fnn-core (case operation
                   ((:poll :bound-poll :wait :bound-wait)
                    'fn-native-control-host-consumer-poll-max-frame)
                   (:status 'fn-native-control-host-consumer-status-max-frame)
                   (otherwise 'fn-native-control-host-max-frame)))
       (fnn-core 'fn-native-control-host-max-frame)))

(defun fnn-control-consumer-plain (path operation first second)
  "The kind-4 exchange (an old owner's, after it refused kind 22 unread):
answers the reply list, as before PKT-709."
  (let ((request-list
          (fnn-core 'fn-native-control-host-consumer-request-encode
                    operation first second)))
    (unless (fnn-octet-list-p request-list)
      (fnn-fault "ACL2 refused local consumer request"))
    (multiple-value-bind (frame stage)
        (fnn-control-exchange path request-list
                              (fnn-control-consumer-maximum operation)
                              (fnn-control-consumer-deadline operation second))
      (let* ((octets (and frame (fnn-octet-list frame)))
             (reply (and octets
                         (fnn-core (case operation
                                     ((:poll :bound-poll :wait :bound-wait)
                                      'fn-native-control-host-consumer-poll-reply-decode)
                                     (:status
                                      'fn-native-control-host-consumer-status-reply-decode)
                                     (otherwise
                                      'fn-native-control-host-consumer-reply-decode))
                                   octets)))
             (ordinary (and octets
                            (fnn-core 'fn-native-control-host-reply-decode octets))))
        (cond ((fnn-control-consumer-reply-okp operation reply) reply)
              ((member ordinary '(:refused :uncertain :fault :busy))
               (fnn-control-consumer-bare-reply
                operation (if (eq ordinary :busy) :refused ordinary)))
              (t (fnn-control-consumer-bare-reply
                  operation (fnn-control-transport-outcome stage))))))))

(defun fnn-control-consumer-local (path-octets operation first second)
  "Exchange one ACL2-framed consumer command with the 0600 owner socket.
Answers (values REPLY WORD): REPLY the consumer reply list the command
prints from, WORD ACL2's reason word (octets) or NIL.

PKT-709: the request goes as the reasoned consumer request (FNCT kind 22,
books/consumer-reason.lisp); ACL2 reads the answer
(fn-native-control-host-consumer-client-read): the consumer reply of an
acceptance, the owner's status and reason word, a resend of the plain
request once (an old owner refused kind 22 before acting on anything), or
the transport outcome of the stage reached."
  (let ((path (fnn-octets-string path-octets))
        (reasoned (fnn-core 'fn-native-control-host-consumer-reasoned-request-encode
                            operation first second)))
    (unless (fnn-octet-list-p reasoned)
      (fnn-fault "ACL2 refused local consumer request"))
    (multiple-value-bind (frame stage)
        (fnn-control-exchange path reasoned
                              (fnn-control-consumer-maximum operation)
                              (fnn-control-consumer-deadline operation second))
      (let ((step (if frame
                      (fnn-core 'fn-native-control-host-consumer-client-read
                                operation (fnn-octet-list frame))
                    '(:transport))))
        (case (first step)
          (:reply
           (values (if (fnn-control-consumer-reply-okp operation (second step))
                       (second step)
                     (fnn-control-consumer-bare-reply
                      operation (fnn-control-transport-outcome stage)))
                   nil))
          (:status
           (let ((status (second step)))
             (values (fnn-control-consumer-bare-reply
                      operation
                      (cond ((member status '(:refused :uncertain :fault)) status)
                            ((eq status :busy) :refused)
                            ;; An acceptance never comes as a reasoned reply.
                            (t (fnn-control-transport-outcome stage))))
                     (third step))))
          (:resend
           (values (fnn-control-consumer-plain path operation first second) nil))
          (otherwise
           (values (fnn-control-consumer-bare-reply
                    operation (fnn-control-transport-outcome stage))
                   nil)))))))

(defun fnn-control-submit (path-octets msgid-octets group-octets payload-path-octets)
  "Submit one exact bounded file; answer (values STATUS WORD), ACL2's status
keyword and its reason word (PKT-453 (a))."
  (let* ((path (fnn-octets-string path-octets))
         (payload-path (fnn-octets-string payload-path-octets))
         (maximum-article (fnn-core 'fn-native-control-host-max-article))
         (article (fnn-read-regular-bounded payload-path maximum-article))
         (fields (list (fnn-octet-list msgid-octets)
                       (mapcar #'fnn-octet-list group-octets)
                       (fnn-octet-list article)))
         (reasoned (apply #'fnn-core
                          'fn-native-control-host-reasoned-request-encode fields)))
    (unless (fnn-octet-list-p reasoned)
      (fnn-fault "ACL2 refused normalized control submission"))
    (fnn-control-reasoned-exchange
     path reasoned
     (lambda () (apply #'fnn-core 'fn-native-control-host-request-encode fields)))))

(defun fnn-control-live-request-exchange (path-octets request)
  "Send one sealed live-report REQUEST to the owner and read its reply.

The reply octets, or the stage at which the exchange failed
(:before-submission, :after-submission), or :refused when the owner answered
an ordinary refusal (it is stopping)."
  (let ((socket nil) (stage :before-submission))
    (unless (fnn-octet-list-p request)
      (fnn-fault "ACL2 refused a live status request"))
    (unwind-protect
         (handler-case
             (progn
               (setq socket (fnn-control-connect (fnn-octets-string path-octets)))
               (let ((fd (fnn-socket-fd socket)))
                 (setq stage :after-submission)
                 (fnn-control-send-request socket fd (fnn-octets request))
                 (let ((frame (fnn-control-read-frame
                               socket (fnn-core 'fn-native-live-status-host-max-frame))))
                   (if (typep frame 'fnn-octets)
                       (let ((octets (fnn-octet-list frame)))
                         (if (member (fnn-core 'fn-native-control-host-reply-decode octets)
                                     '(:refused :busy))
                             :refused
                           octets))
                     stage))))
           (error () stage))
      (when socket (fnn-socket-shut socket)))))

(defun fnn-control-live-status-page (path-octets kind offset)
  "Ask the owner for one page of report KIND from OFFSET (the whole-report
exchange, FNLS kind 1 or 3)."
  (fnn-control-live-request-exchange
   path-octets (fnn-core 'fn-native-live-status-host-request-encode kind offset)))

(defun fnn-control-live-pages (path-octets kind)
  "Read the owner's paged report KIND page by page (books/native-live-pages.lisp).

(:done-pages VECTORS): the pages in order, each an octet vector, which joined
are the report of one version (KEYSTONE fn-nlp-pages-join-to-the-report);
or an outcome keyword for `fn-nls-route'.  A version the owner no longer
holds is answered version-gone by name: the client restarts from page 0, at
most `fn-native-live-status-host-max-restarts' times, then answers
uncertain (:after-submission)."
  (let ((pages nil) (version 0) (page 0) (restarts 0) (count 0)
        (started (get-internal-real-time)) (first-page nil)
        (limit (fnn-core 'fn-native-live-status-host-max-restarts)))
    (loop
      (let ((reply (fnn-control-live-request-exchange
                    path-octets
                    (fnn-core 'fn-native-live-pages-host-request-encode
                              kind version page))))
        (when (keywordp reply)
          (return (if (and (eq reply :before-submission)
                           (or pages (plusp restarts)))
                      :after-submission
                    reply)))
        (incf count)
        (unless first-page (setq first-page (get-internal-real-time)))
        (let ((step (fnn-core 'fn-native-live-pages-host-client-step
                              version page reply)))
          (case (first step)
            (:done (push (fnn-octets (second step)) pages)
             ;; A measurement line on request (FN_REPORT_TIMING), never a
             ;; value the report carries.
             (when (sb-posix:getenv "FN_REPORT_TIMING")
               (format *error-output* "report-pages requests=~d restarts=~d first-page-seconds=~,3f seconds=~,3f~%"
                       count restarts
                       (/ (- first-page started) internal-time-units-per-second)
                       (/ (- (get-internal-real-time) started)
                          internal-time-units-per-second))
               (finish-output *error-output*))
             (return (list :done-pages (nreverse pages))))
            (:next (push (fnn-octets (second step)) pages)
             (setq version (third step) page (fourth step)))
            (:restart
             (when (>= (incf restarts) limit) (return :after-submission))
             (setq pages nil version 0 page 0))
            (:refused (return :refused))
            (t (return :after-submission))))))))

(defun fnn-control-live-status (path-octets kind)
  "Join the owner's pages of report KIND through `fn-nls-client-step'.

(:done OCTETS), or an outcome keyword for `fn-nls-route'.  A page that fails
after the first was answered is :after-submission: the owner was there.
A paged kind (`fn-nlp-pagedp') is read by `fnn-control-live-pages' instead:
(:done-pages VECTORS)."
  (when (fnn-core 'fn-native-live-pages-host-pagedp kind)
    (return-from fnn-control-live-status (fnn-control-live-pages path-octets kind)))
  ;; CHUNKS: the pages so far, newest first; N their joined length, which
  ;; ACL2 carries (fn-nsc-client-step-carries-its-length) and the next
  ;; page's offset.
  (let ((chunks nil) (n 0) (total nil) (digest nil) (restarts 0)
        (limit (fnn-core 'fn-native-live-status-host-max-restarts)))
    (loop
      (let ((page (fnn-control-live-status-page path-octets kind n)))
        (when (keywordp page)
          (return (if (and (eq page :before-submission)
                           (or chunks (plusp restarts)))
                      :after-submission
                    page)))
        (let ((step (fnn-core 'fn-native-live-status-host-client-step-chunks
                              chunks n total digest page)))
          (case (first step)
            (:done (return step))
            (:next (setq chunks (second step) n (third step)
                         total (fourth step) digest (fifth step)))
            (:restart
             (when (>= (incf restarts) limit) (return :after-submission))
             (setq chunks nil n 0 total nil digest nil))
            ;; ACL2's named refusal, (:refused WORD), is carried to the
            ;; caller as it came (fn-nls-page-refuses-exactly-past-the-
            ;; total-width); a bare refusal stays :refused.
            (:refused (return (if (rest step) step :refused)))
            (t (return :after-submission))))))))
