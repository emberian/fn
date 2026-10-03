;;; host/native/tcpcl.lisp -- the native host's TCPCLv4 convergence layer.
;;;
;;; TRUST BOUNDARY.  Raw Common Lisp, loaded under the same :fn-native-host
;;; trust tag as host/native/io.lisp and after it, so every socket call here
;;; is one of io.lisp's eight named entry points (`fnn-listen', `fnn-connect',
;;; `fnn-accept-loop', `fnn-socket-fd', `fnn-socket-shut', `fnn-recv',
;;; `fnn-send-all', `fnn-graceful-close') and this file opens no socket and
;;; makes no syscall of its own beyond the durability barrier below.
;;;
;;; THIS FILE OWNS NO PROTOCOL DECISION.  It holds three things the books do
;;; not have: a file descriptor, one monotonic millisecond reading per wakeup,
;;; and the durability barrier under a received bundle.  Every octet on the
;;; wire is `fn-tcl-encode' of a message the session machine emitted; every
;;; message consumed is one `fn-tcl-drive' made of the carry and the chunk;
;;; every length, MRU, refusal reason, termination reason and transfer outcome
;;; is read out of an ACL2 result through host/tcpcl-host.lisp.  The one
;;; ordering rule this file adds is stated at `fnn-tcl-act': outbound octets
;;; are buffered across an event list and released after the barrier, because
;;; `fn-tcl-complete' emits the XFER_ACK before the `:bundle-received' whose
;;; data the ack promises (specs/bp-design.md section 2.4).
;;;
;;; THREE OUTCOMES.  A session log line is `accepted', `refused' or
;;; `uncertain' and they never merge: a bundle whose staging barrier did not
;;; complete is uncertain, its acknowledgement is never released, the session
;;; is terminated and the process exits 3.

(in-package "ACL2")

;;; The one dependency.  Every socket, filesystem and core call below is
;;; host/native/io.lisp's, so this file loads it rather than leave the order
;;; to a loader: `load' is the raw-mode edge that `ld' is for the interpreted
;;; host files.  The guard keeps host/native/build.lisp, which loads io.lisp
;;; first, from re-evaluating it.  The path is repository-relative, as every
;;; other load of this pair is.
(eval-when (:load-toplevel :execute)
  (unless (fboundp 'fnn-core)
    (load "host/native/io.lisp")))

;;; ---------------------------------------------------------------------------
;;; Defaults.  Operator configuration, not protocol: each one is handed to
;;; `fn-tcl-host-params' and the machine decides what it means.

(defconstant +fnn-tcl-keepalive+ 10)          ; seconds, RFC 9174 section 4.3
(defconstant +fnn-tcl-segment-mru+ 1024)
(defconstant +fnn-tcl-transfer-mru+ 1048576)
(defconstant +fnn-tcl-accept-timeout+ 30)     ; seconds waiting for a session
(defconstant +fnn-tcl-write-timeout+ 30)

(defstruct (fnn-tcl-conn (:conc-name fnn-tclc-))
  fd tag spool session (carry nil) (held nil) (closing nil) (broken nil)
  (pending nil) (trace nil) (inbound 0)
  ;; Exact received transfer remains borrowed until actual joined disposition.
  (source-pending nil) (source-token nil) (source-id nil)
  (source-root nil) (source-count nil) (source-held nil) (source-more nil)
  ;; PKT-873: T when an accepted transfer's custody awaits the session's
  ;; progress hook (ACL2's fn-tcl-delivery-plan-progress-p named it).
  (progress nil)
  (accepted 0) (refused 0) (uncertain 0) (outcome nil)
  ;; T when a Store or FNBS publication inside the delivery callback was
  ;; uncertain: a fence, not the connection's own loss (ACL2 reads both,
  ;; fn-bprc-session-evidence, books/bp-run-class.lisp).
  (fenced nil)
  ;; The Reason Code of the peer's XFER_REFUSE for the outbound transfer, as
  ;; ACL2's :outbound-refused event carried it; nil when none arrived.
  (refusal nil)
  ;; T for a session this node opened to send (bp-service, bp-node
  ;; forwarding): it takes no inbound custody.  A transfer the peer offers
  ;; on it is refused by name, (:refused :outbound-session), which ACL2
  ;; answers with XFER_REFUSE No Resources (fn-tcl-delivery-refuse-reason),
  ;; and OUTCOME keeps meaning the outbound transfer's (inspection sweep
  ;; 2026-10-03 S024: such a transfer was ACKed into a plain spool file in
  ;; the FNBS root, never admitted, and renamed over by the next session).
  (refuse-inbound nil)
  ;; Retained driver state. Held protocol messages remain custody-gated;
  ;; only released messages enter TX-MESSAGES, in the machine's order.
  (retained nil) (tx-messages nil) (tx-data nil) (tx-offset 0) (tx-deadline nil)
  (input-due t) (pump-pending nil) role bundlep (expect 0) on-ready
  (ready-called nil) (finished nil)
  ;; Private concrete octet buffer, one incomplete frame only. The incoming
  ;; socket vector survives cursor turns; no list carry is appended/reparsed.
  input-buffer input-cursor input-vector (input-offset 0))

;;; ---------------------------------------------------------------------------
;;; The clock.  One monotonic reading per wakeup, in milliseconds, handed to
;;; ACL2, which builds the observation (`fn-tcl-host-tick') and decides what
;;; keepalive and idle timeout mean.

(defun fnn-tcl-now ()
  (fnn-monotonic-ms))

;;; The read timeout: below half the negotiated interval so that a keepalive
;;; is never missed by the wakeup granularity.  The interval is the machine's;
;;; this divides it.
(defun fnn-tcl-read-timeout (conn)
  (let ((seconds (fnn-core 'fn-tcl-host-keepalive (fnn-tclc-session conn))))
    (if (and (integerp seconds) (> seconds 1))
        (max 1 (floor seconds 4))
        1)))

;;; ---------------------------------------------------------------------------
;;; The session log.  Every digest is ACL2's (`fn-tcl-host-event-digests'), so
;;; the loop and the replay differential print the same object.

(defun fnn-tcl-log (conn kind control &rest args)
  (fnn-out "TCPCL ~a ~a ~a" (fnn-tclc-tag conn) kind (apply #'format nil control args)))

;;; `source' is "event" for the events of a `fn-tcl-drive' over received
;;; octets and "aux" for those of an open, a tick, a send, a pump, a peer
;;; close or a terminate.  tools/tcpcl_lab.py replays the trace
;;; through `fn-tcl-drive' alone, so only the "event" lines are its subject.
(defun fnn-tcl-log-events (conn source digests)
  (dolist (digest digests)
    (fnn-out "TCPCL ~a ~a ~s" (fnn-tclc-tag conn) source digest)))

;;; ---------------------------------------------------------------------------
;;; The FNBS barrier.  A received bundle is a regular file whose data and whose
;;; name are both durable before its acknowledgement is released.  An ambiguous
;;; failure is not a refusal: it is uncertain, and the caller never acks.

(defvar *fnn-tcl-progress* nil
  "One service scheduling turn after the session has flushed its held ACKs.
Invoked at each input/timeout turn, including keepalives; the hook must retain
unfinished jobs and return after one quantum.")
(defvar *fnn-tcl-work-pending* nil
  "Optional (conn)->boolean wakeup hint for already retained service work.
While true the session polls input without waiting, and still yields each turn.")

(defvar *fnn-tcl-deliver* nil
  "When non-nil, a function (conn xfer-id octets) that takes custody of one
completed inbound transfer in place of the plain spool file.  It returns
(:accepted path-or-nil), (:refused reason), or (:uncertain reason).  The
XFER_ACK for that transfer is already held; fn-tcl-delivery-plan decides
which message, if any, may be released after this callback.

host/native/bp.lisp installs `fn-bpn-receive' here, which is what makes the
`bp' verb a BPv7 node rather than a spool: the octets become a decoded
bundle, its lifetime and hop count are decided, and its ADU is what lands in
the journal.  Nothing else binds this.")

(defvar *fnn-tcl-deliver-counted* nil
  "Dormant received-source callback (conn xfer-id octets cumulative-count).
Only the qualified BP received-source installer may bind it. Callback presence
is not a resource grant. ACL2 selects count from the held final END ACK; no
host byte count or complete-source scan occurs. Old callback remains separate.")

(define-condition fnn-tcl-source-indeterminate (fnn-store-indeterminate)
  ((connection :initarg :connection :reader fnn-tcl-source-failure-connection)
   (cause :initarg :cause :reader fnn-tcl-source-failure-cause)))
(defun fnn-tcl-source-escape (conn condition)
  ;; The condition retains this same mutable I/O record across outer session
  ;; unwind. It conveys uncertainty, not a new authoritative source snapshot.
  (setf (fnn-tclc-fenced conn) t (fnn-tclc-outcome conn) :uncertain)
  (if (typep condition 'fnn-tcl-source-indeterminate) (error condition)
    (error 'fnn-tcl-source-indeterminate
           :message "TCPCL received source continuation is indeterminate"
           :connection conn :cause condition)))

(defvar *fnn-tcl-source-start* nil
  "Qualified registered source entry (conn id reversed-segments count).
Returns (:source-yield token) or a durable delivery disposition. Initially
NIL: no constructor, source issuer, policy or operation authority installed.")
(defvar *fnn-tcl-source-turn* nil
  "Qualified token-only continuation (conn token). One bounded action per
call; retains source and END ACK on yield. Never receives an authority row.")

(defun fnn-tcl-deliver-transfer (conn xfer-id octets)
  (cond
    ((fnn-tclc-refuse-inbound conn) (list :refused :outbound-session))
    (*fnn-tcl-deliver-counted*
     (let ((counted (fnn-core 'fn-tcl-final-held-count (fnn-tclc-held conn) xfer-id)))
       (unless (eq (fnn-core 'fn-tcl-final-count-ready-p counted) t)
         (fnn-fault "TCPCL received-source count lacks its held final ACK"))
       (funcall *fnn-tcl-deliver-counted* conn xfer-id octets
                (fnn-core 'fn-tcl-final-count-value counted))))
    (*fnn-tcl-deliver* (funcall *fnn-tcl-deliver* conn xfer-id octets))
    (t (fnn-tcl-stage conn xfer-id octets))))

(defconstant +fnn-tcl-spool-lock+ ".spool.lock")

(defun fnn-tcl-spool-entry-kind (path)
  (let ((st (fnn-lstat path)))
    (if (and st (fnn-regular-p st) (not (fnn-symlink-p st))) :regular :other)))

(defun fnn-tcl-spool-recover (root)
  "Remove only ACL2-selected private staging files, then barrier the removal.

The complete plan is obtained before the first unlink.  A symlink, directory,
or malformed name in the reserved namespace therefore preserves all evidence
and faults without following or deleting anything."
  (let* ((names (handler-case (fnn-list-directory root)
                  (fnn-os-error (e)
                    (fnn-indeterminate "tcpcl: spool cannot be enumerated: ~a" e))))
         (entries (mapcar (lambda (name)
                            (cons (fnn-octet-list (fnn-string-octets name))
                                  (fnn-tcl-spool-entry-kind (fnn-join root name))))
                          names))
         (plan (fnn-core 'fn-tcl-host-spool-recovery-plan entries))
         (status (and (consp plan) (first plan)))
         (actions (and (consp (cdr plan)) (second plan))))
    (unless (and (member status '(:ok :fault))
                 (or (eq status :fault)
                     (and (listp actions) (= (length actions) (length names)))))
      (fnn-fault "tcpcl: ACL2 returned an invalid spool recovery plan"))
    (when (eq status :fault)
      (fnn-fault "tcpcl: unexplained entry in the private staging namespace"))
    (let ((removed nil))
      (loop for name in names for action in actions do
        (case action
          (:keep nil)
          (:remove
           (when (string= (or (fnn-developer-selector "FN_TCPCL_TEST_FAIL_STAGING_UNLINK") "") "1")
             (fnn-indeterminate "tcpcl: injected staging cleanup unlink failure"))
           (handler-case (fnn-unlink (fnn-join root name))
             (fnn-os-error (e)
               (fnn-indeterminate "tcpcl: staging cleanup is uncertain: ~a" e)))
           (setq removed t))
          (t (fnn-fault "tcpcl: ACL2 returned an invalid spool recovery action"))))
      (when removed
        (when (string= (or (fnn-developer-selector "FN_TCPCL_TEST_FAIL_STAGING_BARRIER") "") "1")
          (fnn-indeterminate "tcpcl: injected staging cleanup barrier failure"))
        (handler-case (fnn-fsync-dir root)
          (fnn-os-error (e)
            (fnn-indeterminate "tcpcl: staging cleanup barrier is uncertain: ~a" e)))))))

(defun fnn-tcl-spool-acquire (root)
  "Establish one process as ROOT's owner, then recover its private staging."
  (handler-case
      (progn
        (fnn-safe-directory root t)
        ; Repeat the parent barrier on every recovery.  An earlier mkdir may
        ; have returned before its parent publication became authoritative.
        (fnn-fsync-dir (fnn-parent root)))
    (fnn-os-error (e)
      (fnn-indeterminate "tcpcl: spool namespace recovery is uncertain: ~a" e)))
  (let ((lock nil) (owned nil))
    (unwind-protect
         (progn
           (handler-case
               (setq lock (fnn-open (fnn-join root +fnn-tcl-spool-lock+)
                                    (logior sb-posix:o-rdwr sb-posix:o-creat
                                            +fnn-o-nofollow+)
                                    #o600))
             (fnn-os-error (e)
               (fnn-fault "tcpcl: cannot open spool ownership lock: ~a" e)))
           (unless (fnn-regular-p (fnn-fstat lock))
             (fnn-fault "tcpcl: refusing non-regular spool ownership lock"))
           (handler-case (fnn-flock lock (logior +fnn-lock-ex+ +fnn-lock-nb+))
             (fnn-os-error (e)
               (if (= (fnn-os-errno e) sb-posix:eagain)
                   (fnn-refuse "tcpcl: spool is already owned")
                 (fnn-fault "tcpcl: cannot establish spool ownership: ~a" e))))
           (fnn-tcl-spool-recover root)
           (setq owned t)
           lock)
      (unless owned
        (when lock
          (ignore-errors (fnn-flock lock +fnn-lock-un+))
          (ignore-errors (fnn-close lock)))))))

(defun fnn-tcl-spool-release (lock)
  (when lock
    (ignore-errors (fnn-flock lock +fnn-lock-un+))
    (ignore-errors (fnn-close lock))))

(defun fnn-tcl-test-pause-after-stage-data (stage)
  ; An explicit native process-death cut for the recovery regression.  It is
  ; disabled unless the test-only environment variable is exactly "1".
  (when (string= (or (fnn-developer-selector "FN_TCPCL_TEST_PAUSE_AFTER_STAGE_DATA") "")
                 "1")
    (fnn-out "TCPCL TEST STAGE-DATA ~a" stage)
    (sleep 60)))

(defun fnn-tcl-stage (conn xfer-id octets)
  (let* ((dir (fnn-tclc-spool conn))
         (final (fnn-join dir (format nil "~a-~d.bundle" (fnn-tclc-tag conn) xfer-id)))
         (stage (fnn-join dir (format nil ".incoming-~d-~a"
                                      (sb-posix:getpid) (fnn-random-hex 12)))))
    (handler-case
        (progn
          (fnn-write-staged stage (fnn-octets octets))
          (fnn-tcl-test-pause-after-stage-data stage)
          (fnn-replace stage final)
          (fnn-fsync-dir dir)
          (list :accepted final))
      (fnn-os-error (e)
        (ignore-errors (fnn-unlink stage))
        (fnn-indeterminate "inbound transfer ~d: staging did not complete: ~a"
                           xfer-id e)))))

;;; ---------------------------------------------------------------------------
;;; Writing.  Outbound octets are buffered for the length of one event list and
;;; released either after a barrier or at its end, so the order the machine
;;; chose is the order on the wire and no acknowledgement precedes the durable
;;; record of what it acknowledges.

(defun fnn-tcl-flush (conn)
  (let ((queued (nreverse (fnn-tclc-held conn))))
    (setf (fnn-tclc-held conn) nil)
    (unless (fnn-tclc-broken conn)
      (when (fnn-tclc-retained conn)
        (setf (fnn-tclc-tx-messages conn)
              (nconc (fnn-tclc-tx-messages conn) queued))
        (return-from fnn-tcl-flush))
      (handler-case
          (dolist (message queued)
            (fnn-send-all (fnn-tclc-fd conn)
                          (fnn-octets (fnn-core 'fn-tcl-host-encode message))
                          +fnn-tcl-write-timeout+))
        ((or fnn-os-error sb-bsd-sockets:socket-error) (e)
          ;; The peer has gone (EPIPE or ECONNRESET on this session's own
          ;; socket; dtn7-rs closes straight after its SESS_TERM).  What
          ;; that means for each transfer is ACL2's: fnn-tcl-session hands
          ;; the machine fn-tcl-host-tcp-closed and returns.
          (setf (fnn-tclc-broken conn) t (fnn-tclc-closing conn) t)
          (fnn-tcl-log conn "event" "peer gone before send: ~a" e))))))

(defun fnn-tcl-drop (conn)
  "Discard unreleased octets: an acknowledgement whose bundle is not durable."
  (setf (fnn-tclc-held conn) nil))

(defun fnn-tcl-record-trace (conn now chunk)
  (let ((stream (fnn-tclc-trace conn)))
    (when stream
      (write-sequence (fnn-string-octets (format nil "~d ~d~%" now (length chunk))) stream)
      (write-sequence (fnn-octets chunk) stream)
      (finish-output stream))))

;;; ---------------------------------------------------------------------------
(defun fnn-tcl-source-disposition (conn result)
  (case (fnn-core 'fn-tcl-source-result-action result)
    (:retain
     (setf (fnn-tclc-source-token conn)
           (fnn-core 'fn-tcl-source-result-token result)))
    (:settle
     (fnn-tcl-settle-delivery conn (fnn-tclc-source-id conn) result)
     ;; A throwing/uncertain settlement retains all source and token debt.
     (setf (fnn-tclc-source-pending conn) nil
           (fnn-tclc-source-token conn) nil (fnn-tclc-source-root conn) nil
           (fnn-tclc-source-id conn) nil (fnn-tclc-source-count conn) nil
           (fnn-tclc-source-held conn) nil))
    (otherwise (fnn-fault "TCPCL source continuation result unavailable"))))
(defun fnn-tcl-input-initialize (conn)
  (unless (fnn-tclc-input-buffer conn)
    (let ((buffer (create-fn-octets$c)))
      ;; Reserve the codec's supported message span once per context. The
      ;; BP bank already prepaid its captured wire/segment resident tariff.
      ;; Allocation/GC time of this initial reserve remains an explicit cost.
      (fn-octets$c-reserve
       (fnn-core 'fn-tcl-max-message
         (fnn-core 'fn-tcl-host-segment-mru (fnn-tclc-session conn))) buffer)
      (setf (fnn-tclc-input-buffer conn) buffer)))
  (unless (fnn-tclc-input-cursor conn)
    (setf (fnn-tclc-input-cursor conn)
      (fnn-core 'fn-tcf-begin
       (fnn-core 'fn-tcf-contactp
        (fnn-core 'fn-tcl-host-phase (fnn-tclc-session conn)))))))

(defun fnn-tcl-input-decode (conn now probe)
  (let* ((buffer (fnn-tclc-input-buffer conn))
         ;; Existing decoder/publication still consumes a complete logical
         ;; frame once. Full-frame conversion/decode is the remaining frontier.
         (octets (fnn-octet-list
                   (subseq (svref buffer 0) 0 (svref buffer 1)))))
    (unless (and probe (fnn-core 'fn-tcl-host-input-probe (fnn-tclc-session conn) octets))
      (let ((triple (fnn-core
                     (if *fnn-tcl-source-start* 'fn-tcl-host-source-drive 'fn-tcl-host-drive)
                     (fnn-tclc-session conn) octets now)))
        (setf (fnn-tclc-carry conn) (third triple))
        (fnn-tcl-apply conn triple "event")
        (setf (svref buffer 1) 0 (fnn-tclc-input-cursor conn) nil)))))

(defun fnn-tcl-input-turn (conn incoming now)
  "One scalar framing action and at most4096 byte copies. Retain unread input."
  (when incoming
    (when (fnn-tclc-input-vector conn) (fnn-fault "TCPCL input vector still borrowed"))
    (setf (fnn-tclc-input-vector conn) incoming (fnn-tclc-input-offset conn) 0))
  (fnn-tcl-input-initialize conn)
  (let* ((vector (fnn-tclc-input-vector conn))
         (offset (fnn-tclc-input-offset conn))
         (available (if vector (- (length vector) offset) 0))
         (plan (fnn-core 'fn-tcf-span (fnn-tclc-input-cursor conn) available))
         (action (first plan)) (used (third plan))
         (buffer (fnn-tclc-input-buffer conn)) (fill (svref buffer 1)))
    (setf (fnn-tclc-input-cursor conn) (second plan))
    (when (plusp used)
      (replace (svref buffer 0) vector :start1 fill :start2 offset :end2 (+ offset used))
      (setf (svref buffer 1) (+ fill used))
      (incf (fnn-tclc-input-offset conn) used)
      (when (eq action :byte)
        (setf (fnn-tclc-input-cursor conn)
          (fnn-core 'fn-tcf-byte (fnn-tclc-input-cursor conn) (aref vector offset)
                    (fnn-core 'fn-tcl-host-segment-mru (fnn-tclc-session conn))))))
    (when (and vector (= (fnn-tclc-input-offset conn) (length vector)))
      (setf (fnn-tclc-input-vector conn) nil (fnn-tclc-input-offset conn) 0))
    (case action
      (:decode (fnn-tcl-input-decode conn now nil))
      (:probe (fnn-tcl-input-decode conn now t)))
    (setf (fnn-tclc-source-more conn)
      (or (and (fnn-tclc-input-vector conn) t)
          (member (first (fnn-tclc-input-cursor conn)) '(:complete :probe))
          ;; Zero-length skips must advance without another socket read.
          (and (fnn-tclc-input-cursor conn)
               (zerop (second (fnn-tclc-input-cursor conn))) t)))))

(defun fnn-tcl-source-input-turn (conn chunk now)
  (unless (and *fnn-tcl-source-start* *fnn-tcl-source-turn*)
    (fnn-fault "TCPCL registered source driver unavailable"))
  (when (fnn-tclc-source-pending conn)
    (fnn-fault "TCPCL source owns input turn until settlement"))
  (let ((result (fnn-core 'fn-tcl-host-source-drive (fnn-tclc-session conn)
                           (append (fnn-tclc-carry conn) chunk) now)))
    (setf (fnn-tclc-carry conn) (third result)
          (fnn-tclc-source-more conn) (fnn-core 'fn-tcl-host-source-more-p result))
    (fnn-tcl-apply conn result "source-event")))

(defun fnn-tcl-source-tick (conn)
  (handler-case
      (progn
        (unless (and (fnn-tclc-source-pending conn)
                     (fnn-tclc-source-token conn) *fnn-tcl-source-turn*)
          (fnn-fault "TCPCL source continuation cannot resume"))
        (when (fnn-tclc-fenced conn)
          (fnn-fault "TCPCL source continuation is fenced"))
        (fnn-tcl-source-disposition
         conn (funcall *fnn-tcl-source-turn* conn (fnn-tclc-source-token conn))))
    (error (condition) (fnn-tcl-source-escape conn condition))))

(defun fnn-tcl-settle-delivery (conn xfer-id result)
  (let* ((plan (fnn-core 'fn-tcl-delivery-plan
                                (reverse (fnn-tclc-held conn))
                                xfer-id result))
                (status (fnn-core 'fn-tcl-delivery-plan-status plan)))
           (setf (fnn-tclc-held conn)
                 (reverse (fnn-core 'fn-tcl-delivery-plan-messages plan)))
           (case status
             (:accepted
              (incf (fnn-tclc-accepted conn))
              (incf (fnn-tclc-inbound conn))
              (when (fnn-core 'fn-tcl-delivery-plan-progress-p plan)
                (setf (fnn-tclc-progress conn) t))
              (fnn-tcl-log conn "accepted" "xfer=~d path=~a"
                           xfer-id
                           (fnn-core 'fn-tcl-delivery-plan-detail plan))
              (fnn-tcl-flush conn))
             (:refused
              (incf (fnn-tclc-refused conn))
              (unless (fnn-tclc-refuse-inbound conn)
                (setf (fnn-tclc-outcome conn) :refused))
              (fnn-tcl-log conn "refused" "inbound xfer=~d reason=~a"
                           xfer-id
                           (fnn-core 'fn-tcl-delivery-plan-detail plan))
              (fnn-tcl-flush conn))
             (:uncertain
              (incf (fnn-tclc-uncertain conn))
              (setf (fnn-tclc-outcome conn) :uncertain
                    (fnn-tclc-fenced conn) t)
              (fnn-tcl-log conn "uncertain" "inbound xfer=~d reason=~a"
                           xfer-id
                           (fnn-core 'fn-tcl-delivery-plan-detail plan))
              (fnn-indeterminate "inbound transfer ~d: durable disposition uncertain"
                                 xfer-id))
             (otherwise
              (fnn-tcl-drop conn)
              (fnn-fault "TCPCL delivery result did not match held final ACK")))))

;;; Acting on an event list, in order.

(defun fnn-tcl-act (conn events)
  (dolist (event events)
    (let ((tag (and (consp event) (first event))))
      (case tag
        (:send
         (push (second event) (fnn-tclc-held conn)))
        (:bundle-received
         ;; The held list ends with fn-tcl-complete's final END ACK and may
         ;; contain earlier machine output from the same drive batch. ACL2
         ;; selects the entire outbound message list after the callback.
         (let ((result (handler-case
                            (fnn-tcl-deliver-transfer conn (second event) (third event))
                          (fnn-store-indeterminate (e)
                            (fnn-tcl-drop conn)
                            (incf (fnn-tclc-uncertain conn))
                            (setf (fnn-tclc-outcome conn) :uncertain
                                  (fnn-tclc-fenced conn) t)
                            (fnn-tcl-log conn "uncertain" "~a" e)
                            (error e)))))
           (fnn-tcl-settle-delivery conn (second event) result)))
        (:bundle-segments-received
         (unless (and *fnn-tcl-source-start* *fnn-tcl-source-turn*)
           (fnn-fault "TCPCL registered source runtime unavailable"))
         (when (fnn-tclc-source-pending conn)
           (fnn-fault "TCPCL source continuation already owns END ACK"))
         ;; Persist native borrow before callback escape; registry owns authority.
         (setf (fnn-tclc-source-pending conn) t
               (fnn-tclc-source-id conn) (second event)
               (fnn-tclc-source-root conn) (third event)
               (fnn-tclc-source-count conn) (fourth event)
               (fnn-tclc-source-held conn) (fnn-tclc-held conn))
         (handler-case
             (fnn-tcl-source-disposition
              conn (funcall *fnn-tcl-source-start* conn (second event)
                            (third event) (fourth event)))
           (error (condition)
             (fnn-tcl-source-escape conn condition))))
        (:inbound-refused
         (incf (fnn-tclc-refused conn))
         (fnn-tcl-log conn "refused" "inbound xfer=~d reason=~a" (second event) (third event)))
        (:outbound-refused
         (incf (fnn-tclc-refused conn))
         (setf (fnn-tclc-outcome conn) :refused (fnn-tclc-pending conn) nil
               (fnn-tclc-refusal conn) (fourth event))
         (fnn-tcl-log conn "refused" "outbound xfer=~d reason=~a" (second event) (fourth event)))
        (:outbound-sent
         (incf (fnn-tclc-accepted conn))
         (setf (fnn-tclc-outcome conn) :accepted (fnn-tclc-pending conn) nil)
         (fnn-tcl-log conn "accepted" "outbound xfer=~d" (second event)))
        ((:inbound-failed :outbound-failed)
         (incf (fnn-tclc-uncertain conn))
         (when (eq tag :outbound-failed)
           (setf (fnn-tclc-outcome conn) :uncertain (fnn-tclc-pending conn) nil))
         (fnn-tcl-log conn "uncertain" "~(~a~) xfer=~d" tag (second event)))
        (:send-refused
         ;; :busy and :not-established are the machine telling the host to try
         ;; again; only a decided refusal clears the pending transfer.
         (unless (member (third event) '(:busy :not-established))
           (incf (fnn-tclc-refused conn))
           (setf (fnn-tclc-outcome conn) :refused (fnn-tclc-pending conn) nil)
           (fnn-tcl-log conn "refused" "outbound reason=~(~a~)" (third event))))
        (:close (setf (fnn-tclc-closing conn) t))
        (t nil))))
  (unless (fnn-tclc-source-pending conn) (fnn-tcl-flush conn)))

;;; One ACL2 result: adopt the session, log the digests, act on the events.
(defun fnn-tcl-apply (conn triple &optional (source "aux"))
  (setf (fnn-tclc-session conn) (first triple))
  (when (second triple)
    (fnn-tcl-log-events conn source (fnn-core 'fn-tcl-host-event-digests (second triple))))
  (fnn-tcl-act conn (second triple))
  triple)

;;; ---------------------------------------------------------------------------
;;; Sending a bundle the node offered.  `fn-tcl-send' decides whether it fits;
;;; `fn-tcl-pump' decides every segment boundary.  The host only repeats the
;;; pump until the machine stops emitting.

(defun fnn-tcl-pump-out (conn now)
  (when (fnn-tclc-retained conn)
    (setf (fnn-tclc-pump-pending conn) t)
    (return-from fnn-tcl-pump-out))
  (loop
    (let ((triple (fnn-core 'fn-tcl-host-pump (fnn-tclc-session conn) now)))
      (fnn-tcl-apply conn triple)
      (unless (second triple) (return)))))

(defun fnn-tcl-offer (conn now)
  (let ((pending (fnn-tclc-pending conn)))
    (when (and pending
               (eq (fnn-core 'fn-tcl-host-phase (fnn-tclc-session conn)) :established))
      (fnn-tcl-apply conn (fnn-core 'fn-tcl-host-send (fnn-tclc-session conn)
                                    (car pending) (cdr pending) now))
      (fnn-tcl-pump-out conn now))))

;;; ---------------------------------------------------------------------------
;;; The loop.  One `fn-tcl-drive' per chunk, with the carry prepended; a tick
;;; on every wakeup; `fn-tcl-tcp-closed' when the peer goes away.

(defun fnn-tcl-begin (fd role params tag spool &key bundle trace (expect 0) on-ready refuse-inbound retain)
  "Retain a session. Opening emits messages but performs no socket write."
  (let* ((now (fnn-tcl-now))
         (session (fnn-core 'fn-tcl-host-initial role params now))
         (conn (make-fnn-tcl-conn :fd fd :tag tag :spool spool :session session
                :trace trace :refuse-inbound refuse-inbound :retained t
                :role role :bundlep (and bundle t) :expect expect :on-ready on-ready
                :pending (and bundle (cons tag bundle)))))
    (when retain (funcall retain conn))
    (unless session (fnn-refuse "tcpcl: the session machine refused these parameters"))
    (fnn-tcl-apply conn (fnn-core 'fn-tcl-host-open session now))
    conn))

(defun fnn-tcl-turn-lost (conn)
  ;; This is protocol loss, never a delivery settlement or physical receipt.
  (setf (fnn-tclc-broken conn) t (fnn-tclc-closing conn) t
        (fnn-tclc-tx-data conn) nil (fnn-tclc-tx-messages conn) nil)
  (fnn-tcl-apply conn (fnn-core 'fn-tcl-host-tcp-closed (fnn-tclc-session conn))))

(defun fnn-tcl-turn-local (conn now)
  ;; The progress callback follows actual released ACK writes, not merely
  ;; enqueueing them. A retained received-source borrow also excludes it.
  (when (and *fnn-tcl-progress* (not (fnn-tclc-source-pending conn)))
    (funcall *fnn-tcl-progress* conn)
    (setf (fnn-tclc-progress conn) nil))
  (when (and (fnn-tclc-on-ready conn) (not (fnn-tclc-ready-called conn))
             (eq (fnn-core 'fn-tcl-host-phase (fnn-tclc-session conn)) :established))
    (setf (fnn-tclc-ready-called conn) t)
    (funcall (fnn-tclc-on-ready conn) conn))
  (unless (fnn-tclc-pump-pending conn) (fnn-tcl-offer conn now))
  (when (and (eq (fnn-tclc-role conn) :active)
             (eq (fnn-core 'fn-tcl-host-active-closep
                   (fnn-tclc-session conn) (fnn-tclc-bundlep conn)
                   (and (fnn-tclc-pending conn) t) (fnn-tclc-outcome conn)
                   (fnn-tclc-inbound conn) (fnn-tclc-expect conn)) t))
    (fnn-tcl-apply conn (fnn-core 'fn-tcl-host-terminate (fnn-tclc-session conn) now))))

(defun fnn-tcl-physical-attempt (conn operation)
  ;; Only the named socket call is connection-scoped. Publication and core
  ;; failures outside this thunk must escape to their existing fault fence.
  (handler-case (funcall operation)
    ((or fnn-os-error sb-bsd-sockets:socket-error) (condition)
      (fnn-tcl-log conn "event" "peer lost during retained attempt: ~a" condition)
      (fnn-tcl-turn-lost conn)
      :lost)))

(defun fnn-tcl-turn (conn)
  "One retained action; at most one bounded socket attempt. Returns work/wait/done.
The caller keeps this connection and its socket until actual physical close."
  (when (fnn-tclc-finished conn) (return-from fnn-tcl-turn :done))
  (let* ((now (fnn-tcl-now))
         (action (fnn-core 'fn-tcrt-action
                  (fnn-tclc-source-pending conn) (fnn-tclc-source-more conn)
                  (and (fnn-tclc-tx-data conn) t) (and (fnn-tclc-tx-messages conn) t)
                  (fnn-tclc-input-due conn) (fnn-tclc-pump-pending conn)
                  (fnn-tclc-closing conn)
                  (fnn-core 'fn-tcl-host-phase (fnn-tclc-session conn))
                  now (fnn-tclc-tx-deadline conn)))
         (result :work))
    (case action
        (:done (setf (fnn-tclc-finished conn) t) (setq result :done))
        (:lost (fnn-tcl-turn-lost conn))
        (:encode
         (setf (fnn-tclc-tx-data conn)
               (fnn-octets (fnn-core 'fn-tcl-host-encode (pop (fnn-tclc-tx-messages conn))))
               (fnn-tclc-tx-offset conn) 0
               (fnn-tclc-tx-deadline conn) (fnn-core 'fn-tcrt-write-deadline now)))
        (:write
         (let* ((data (fnn-tclc-tx-data conn)) (offset (fnn-tclc-tx-offset conn))
                (end (fnn-core 'fn-tcrt-write-end offset (length data)))
                (written (fnn-tcl-physical-attempt conn
                          (lambda () (fnn-socket-write-now (fnn-tclc-fd conn) data offset end)))))
           (cond ((eq written :lost) nil)
                 ((eq written :wait) (setq result :wait))
                 (t (progn
               (incf (fnn-tclc-tx-offset conn) written)
               (when (= (fnn-tclc-tx-offset conn) (length data))
                 (setf (fnn-tclc-tx-data conn) nil (fnn-tclc-tx-deadline conn) nil)))))))
        (:source (fnn-tcl-source-tick conn))
        (:buffer (fnn-tcl-input-turn conn nil now))
        (:pump
         (fnn-tcl-turn-local conn now)
         (let ((triple (fnn-core 'fn-tcl-host-pump (fnn-tclc-session conn) now)))
           (fnn-tcl-apply conn triple)
           (setf (fnn-tclc-pump-pending conn) (and (second triple) t)
                 (fnn-tclc-input-due conn) t)))
        (:local
         (fnn-tcl-turn-local conn now)
         (setf (fnn-tclc-input-due conn) t))
        (:read
         (let ((incoming (fnn-tcl-physical-attempt conn
                           (lambda () (fnn-socket-read-now (fnn-tclc-fd conn)
                                        (fnn-core 'fn-tcrt-read-limit))))))
           (setf (fnn-tclc-input-due conn) nil)
           (cond
             ((eq incoming :lost) nil)
             ((eq incoming :wait)
              (setq result :wait)
              (fnn-tcl-apply conn (fnn-core 'fn-tcl-host-tick (fnn-tclc-session conn) now)))
             ((zerop (length incoming)) (fnn-tcl-turn-lost conn))
             (t
              (fnn-tcl-record-trace conn now incoming)
              (fnn-tcl-input-turn conn incoming now)
              (unless (fnn-tclc-source-pending conn)
                (fnn-tcl-apply conn (fnn-core 'fn-tcl-host-tick (fnn-tclc-session conn) now)))))))
        (otherwise (fnn-fault "TCPCL retained turn action unavailable")))
    result))

(defun fnn-tcl-session (fd role params tag spool &key bundle trace (expect 0) on-ready refuse-inbound)
  "Compatibility consumer of the retained session driver."
  (let ((conn (fnn-tcl-begin fd role params tag spool :bundle bundle :trace trace
                :expect expect :on-ready on-ready :refuse-inbound refuse-inbound)))
    (loop for result = (fnn-tcl-turn conn) until (eq result :done) do
      (sb-thread:thread-yield)
      (when (eq result :wait) (sleep 0.01)))
    (when (fnn-tclc-closing conn) (ignore-errors (fnn-graceful-close fd)))
    conn))

;;; ---------------------------------------------------------------------------
;;; Listening and connecting.  Thin: io.lisp owns the sockets.

(defun fnn-tcl-listen (port)
  (fnn-listen port :backlog 4))

(defun fnn-tcl-connect (host port)
  (fnn-connect host port))

;;; ---------------------------------------------------------------------------
;;; Parameters from the command line.  Numbers and octets in; the params record
;;; is ACL2's.

(defun fnn-tcl-params (node-id peer keepalive segment-mru transfer-mru)
  (let ((params (fnn-core 'fn-tcl-host-params keepalive segment-mru transfer-mru
                          (fnn-octet-list (fnn-string-octets node-id))
                          nil
                          (and peer (fnn-octet-list (fnn-string-octets peer))))))
    (unless (eq (fnn-core 'fn-tcl-host-paramsp params) t)
      (fnn-refuse "tcpcl: parameters are not fn-tcl-paramsp"))
    params))

(defun fnn-tcl-arg (args index &optional default)
  "The INDEXth positional argument, or DEFAULT when it is absent or `-'."
  (let ((text (nth index args)))
    (if (or (null text) (string= text "-")) default text)))

(defun fnn-tcl-number (text default)
  (if (null text) default (parse-integer text)))

(defun fnn-tcl-bundle (path)
  (and path (fnn-octet-list (fnn-read-regular-bounded path (ash 1 24)))))

(defun fnn-tcl-trace-stream (path)
  (and path (sb-sys:make-fd-stream
             (fnn-open path (logior sb-posix:o-wronly sb-posix:o-creat sb-posix:o-trunc))
             :output t :element-type '(unsigned-byte 8) :buffering :full)))

(defun fnn-tcl-exit-code (conn)
  "ACL2's code for the session (books/bp-run-class.lisp, PRF-131/PRF-143): a
transfer lost after the session was established is connection-local,
:interrupted (6), never the fence; a fenced delivery callback is 3."
  (fnn-core 'fn-bprc-run-exit-code
            (fnn-core 'fn-bprc-note (fnn-core 'fn-bprc-empty)
                      (fnn-core 'fn-bprc-session-evidence
                                (fnn-tclc-outcome conn) (fnn-tclc-fenced conn)))))

(defun fnn-tcl-summary (conn)
  (fnn-out "TCPCL ~a summary accepted=~d refused=~d uncertain=~d phase=~(~a~)"
           (fnn-tclc-tag conn) (fnn-tclc-accepted conn) (fnn-tclc-refused conn)
           (fnn-tclc-uncertain conn)
           (fnn-core 'fn-tcl-host-phase (fnn-tclc-session conn))))

;;; ---------------------------------------------------------------------------
;;; The two verbs.

(defun fnn-command-tcpcl-listen (port once spool node-id peer keepalive segment-mru
                                 transfer-mru reply trace-path)
  (let ((listener nil) (code +fnn-exit-ok+) (trace (fnn-tcl-trace-stream trace-path))
        (spool-lock (fnn-tcl-spool-acquire spool)))
    (unwind-protect
         (let ((params (fnn-tcl-params node-id peer keepalive segment-mru transfer-mru))
               (bundle (fnn-tcl-bundle reply)))
           (multiple-value-bind (bound bound-port) (fnn-tcl-listen port)
             (setq listener bound)
             (fnn-out "TCPCL LISTENING ~d" bound-port))
           (fnn-accept-loop
            listener
            (lambda (socket)
              (let ((fd (fnn-socket-fd socket)))
                (unwind-protect
                     (handler-case
                         (let ((conn (fnn-tcl-session fd :passive params "passive" spool
                                                      :bundle bundle :trace trace)))
                           (fnn-tcl-summary conn)
                           (setq code (fnn-tcl-exit-code conn)))
                       ;; GEN: def-actor tcpcl-listen :end-connection -- ACL2
                       ;; decides the kind from the concrete class
                       ;; (books/failure-scope.lisp fn-fs-classify).  A
                       ;; journal ambiguity or a core fault is the verb's
                       ;; outcome, never one session's: re-signalled out of
                       ;; the accept loop, as `bp receive' does, so
                       ;; unwind-protect closes the listener and no later
                       ;; peer stages into the spool after an uncertain
                       ;; barrier (sweep S023; before, a fault was this
                       ;; session's refusal and the loop went on).  A known
                       ;; refusal is this session's refused code; a lost
                       ;; connection (an OS or socket failure before any
                       ;; durable step) this session's uncertain code.
                       (serious-condition (e)
                         (let ((kind (fn-fs-classify (fnn-condition-class e)
                                                     *fnn-section-step*)))
                           (cond ((and (eq kind :fault)
                                       (typep e '(or fnn-os-error
                                                     sb-bsd-sockets:socket-error)))
                                  (fnn-err "tcpcl: ~a" e)
                                  (setq code +fnn-exit-uncertain+))
                                 ((member kind '(:refusal :usage))
                                  (fnn-err "tcpcl: ~a" e)
                                  (setq code +fnn-exit-refused+))
                                 (t (error e))))))
                  (fnn-socket-shut socket))))
            once)
           code)
      (when listener (fnn-socket-shut listener))
      (fnn-tcl-spool-release spool-lock)
      (when trace (close trace)))))

(defun fnn-command-tcpcl-send (host port bundle-path spool node-id peer keepalive
                               segment-mru transfer-mru expect trace-path)
  (let ((socket nil) (trace (fnn-tcl-trace-stream trace-path))
        (spool-lock (fnn-tcl-spool-acquire spool)))
    (unwind-protect
         (let ((params (fnn-tcl-params node-id peer keepalive segment-mru transfer-mru))
               (bundle (fnn-tcl-bundle bundle-path)))
           (setq socket (fnn-tcl-connect host port))
           (let ((conn (fnn-tcl-session (fnn-socket-fd socket) :active params "active" spool
                                        :bundle bundle :trace trace :expect expect)))
             (fnn-tcl-summary conn)
             (fnn-tcl-exit-code conn)))
      (when socket (fnn-socket-shut socket))
      (fnn-tcl-spool-release spool-lock)
      (when trace (close trace)))))

;;; ---------------------------------------------------------------------------
;;; The differential.  `replay' folds `fn-tcl-drive' over the trace the loop
;;; wrote -- the same octets, the same clock readings, the same carry -- in one
;;; ACL2 call with no socket in it, and prints the digests in the loop's
;;; spelling.  tools/tcpcl_lab.py compares the two streams.

(defun fnn-tcl-trace-steps (path)
  "The (now octets) steps of a trace file: a decimal now, a space, a decimal
count, LF, that many octets, repeated.  Parsed digit by digit; a peer's octets
never reach the Lisp reader."
  (let ((data (fnn-read-regular-bounded path (ash 1 24)))
        (at 0) (steps nil))
    (flet ((number-until (stop)
             (let ((value 0) (digits 0))
               (loop while (and (< at (length data)) (/= (aref data at) stop)) do
                 (let ((digit (- (aref data at) 48)))
                   (unless (<= 0 digit 9) (fnn-refuse "trace: non-decimal field"))
                   (setq value (+ (* value 10) digit))
                   (incf digits) (incf at)))
               (when (zerop digits) (fnn-refuse "trace: empty field"))
               (unless (< at (length data)) (fnn-refuse "trace: unterminated field"))
               (incf at)
               value)))
      (loop while (< at (length data)) do
        (let* ((now (number-until 32))
               (count (number-until 10)))
          (when (> (+ at count) (length data)) (fnn-refuse "trace: truncated chunk"))
          (push (list now (fnn-octet-list (subseq data at (+ at count)))) steps)
          (incf at count))))
    (nreverse steps)))

(defun fnn-command-tcpcl-replay (trace-path role node-id peer keepalive segment-mru
                                 transfer-mru)
  (let* ((params (fnn-tcl-params node-id peer keepalive segment-mru transfer-mru))
         (steps (fnn-tcl-trace-steps trace-path))
         (start (if (consp steps) (first (first steps)) 0))
         (out (fnn-core 'fn-tcl-host-replay role params start steps)))
    (unless out (fnn-refuse "tcpcl: the session machine refused these parameters"))
    (dolist (digest (second out))
      (fnn-out "TCPCL replay event ~s" digest))
    (fnn-out "TCPCL replay summary phase=~(~a~) unconsumed=~d" (first out) (third out))
    +fnn-exit-ok+))

;;; ---------------------------------------------------------------------------
;;; The positional protocol behind `--fn tcpcl'.  Everything after the first
;;; required argument is optional and `-' selects the default; a session's
;;; parameters are operator configuration and the machine judges them.
;;;
;;;   tcpcl listen PORT [ONCE SPOOL NODE-ID PEER KEEPALIVE SEGMENT-MRU
;;;                      TRANSFER-MRU REPLY-FILE TRACE]
;;;   tcpcl send HOST PORT BUNDLE-FILE [SPOOL NODE-ID PEER KEEPALIVE
;;;                      SEGMENT-MRU TRANSFER-MRU EXPECT TRACE]
;;;   tcpcl replay TRACE-FILE [ROLE NODE-ID PEER KEEPALIVE SEGMENT-MRU
;;;                      TRANSFER-MRU]

(defun fnn-dispatch-tcpcl (command args)
  (flet ((need (n)
           (when (< (length args) n)
             (error 'fnn-usage-error :message "tcpcl: missing arguments")))
         (number (index default)
           (fnn-tcl-number (fnn-tcl-arg args index) default)))
    (cond
      ((string= command "listen")
       (need 1)
       (fnn-command-tcpcl-listen
        (parse-integer (first args))
        (string= (fnn-tcl-arg args 1 "1") "1")
        (fnn-tcl-arg args 2 "tcpcl-spool")
        (fnn-tcl-arg args 3 "dtn://fn-passive/")
        (fnn-tcl-arg args 4)
        (number 5 +fnn-tcl-keepalive+)
        (number 6 +fnn-tcl-segment-mru+)
        (number 7 +fnn-tcl-transfer-mru+)
        (fnn-tcl-arg args 8)
        (fnn-tcl-arg args 9)))
      ((string= command "send")
       (need 3)
       (fnn-command-tcpcl-send
        (first args)
        (parse-integer (second args))
        ;; `-' is a node with nothing to send: it opens the session, waits for
        ;; what the peer offers, and terminates when EXPECT transfers arrived.
        (fnn-tcl-arg args 2)
        (fnn-tcl-arg args 3 "tcpcl-spool")
        (fnn-tcl-arg args 4 "dtn://fn-active/")
        (fnn-tcl-arg args 5)
        (number 6 +fnn-tcl-keepalive+)
        (number 7 +fnn-tcl-segment-mru+)
        (number 8 +fnn-tcl-transfer-mru+)
        (number 9 0)
        (fnn-tcl-arg args 10)))
      ((string= command "replay")
       (need 1)
       (fnn-command-tcpcl-replay
        (first args)
        (if (string= (fnn-tcl-arg args 1 "passive") "active") :active :passive)
        (fnn-tcl-arg args 2 "dtn://fn-passive/")
        (fnn-tcl-arg args 3)
        (number 4 +fnn-tcl-keepalive+)
        (number 5 +fnn-tcl-segment-mru+)
        (number 6 +fnn-tcl-transfer-mru+)))
      (t (error 'fnn-usage-error
                :message (format nil "unknown tcpcl command ~a" command))))))

;;; The verb this file owns, registered with host/native/io.lisp's dispatcher
;;; (`fnn-dispatch'): io.lisp names nothing here.
(fnn-register-verb "tcpcl" #'fnn-dispatch-tcpcl)
