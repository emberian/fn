;;; host/native/bp.lisp -- the `bp' verb: fn as a BPv7 node over its own
;;; TCPCLv4 convergence layer.
;;;
;;; The distinction this file exists to keep.  `tcpcl send' hands the peer a
;;; file of octets fn did not author and cannot name.  `bp send' builds a
;;; complete BPv7 bundle -- this node's ID as the source, the clock
;;; observation as the creation timestamp, the configured lifetime, a hop
;;; count and a bundle age block, the ADU as the payload block -- by calling
;;; `fn-bpn-send' in ACL2, and hands the convergence layer THAT.  `bp receive'
;;; replaces the plain spool file with `fn-bpn-receive': the transfer's octets
;;; are decoded as a bundle, its lifetime and hop count are decided, and the
;;; ADU is what lands in the journal.
;;;
;;; Nothing here computes a protocol value.  The endpoint IDs, the
;;; configuration, the clock observation, the bundle octets, the receive
;;; outcome and the ADU all come from host/bp-node-host.lisp through
;;; `fnn-core'.  This file owns the socket, the clock reading and the
;;; durability barrier, exactly as host/native/tcpcl.lisp does.
;;;
;;; The creation-timestamp sequence is a durable FNBS frontier.  ACL2 reserves
;;; it and frames `(:bpn-sequence next)' before this file writes the staged
;;; replacement and barriers its directory.  Only after that barrier returns
;;; does the host call fn-bpn-send with the reserved value.  A damaged or
;;; uncertain frontier is an uncertain recovery event; it never falls back to
;;; zero or an operator-supplied number.

(in-package "ACL2")

;;; ---------------------------------------------------------------------------
;;; Configuration from the command line, judged by ACL2.

(defconstant +fnn-bp-lifetime+ 3600000)       ; one hour, in milliseconds
(defconstant +fnn-bp-crc-type+ 2)             ; CRC32C
(defconstant +fnn-bp-hop-limit+ 32)

(defun fnn-bp-eid (text)
  "The endpoint ID named by TEXT, or a refusal.  ACL2 matches the scheme."
  (let ((e (fnn-core 'fn-bpn-host-eid (fnn-octet-list (fnn-string-octets text)))))
    (unless e (fnn-refuse "bp: ~a is not an endpoint ID this node can use" text))
    e))

(defun fnn-bp-config (node-id lifetime crc-type hop-limit transfer-mru)
  (let* ((eid (fnn-bp-eid node-id))
         (config (fnn-core 'fn-bpn-host-config eid lifetime crc-type hop-limit
                           transfer-mru)))
    (unless config
      (fnn-refuse "bp: these node parameters are not a node configuration"))
    (unless (eq (fnn-core 'fn-bpn-host-node-idp eid) t)
      (fnn-refuse "bp: ~a is not usable as a node ID (RFC 9171 4.2.5.2)" node-id))
    config))

(defun fnn-bp-observation (wall wall-error)
  "One observation per wakeup.  With no operator-supplied DTN time the
observation has no wall reading, and `fn-bpn-creation-time' then writes the
zero of RFC 9171 section 4.2.6 rather than a monotonic counter."
  (let ((obs (fnn-core 'fn-bpn-host-observation (fnn-tcl-now)
                       (or wall 0) (or wall-error 0) (and wall t))))
    (unless obs (fnn-refuse "bp: the clock reading is not an observation"))
    obs))

;;; ---------------------------------------------------------------------------
;;; The receive path.  Installed into host/native/tcpcl.lisp's
;;; `*fnn-tcl-deliver*', so a completed inbound transfer becomes a decoded
;;; bundle instead of an opaque spool file.
;;;
;;; The barrier is the one the convergence layer already keeps: the XFER_ACK
;;; for this transfer is held until this function returns, so nothing is
;;; acknowledged before the journal record under it is durable.  An ambiguous
;;; write is uncertain and the ack is never released.
;;;
;;; The three outcomes are three different records and three different exit
;;; codes.  A refused bundle is still an acknowledged TRANSFER -- RFC 9174's
;;; ack is about the transfer, not about the bundle -- so the refusal is
;;; recorded durably and the ack is released.

(defstruct fnn-bp-tally
  (accepted 0) (refused 0) (uncertain 0) (config nil) (wall nil) (wall-error nil)
  (journal nil) (last-adu nil) (last-reason nil))

(defun fnn-bp-journal-dir (root)
  ;; FNN-SAFE-DIRECTORY barriers the parent only when it creates ROOT.  The
  ;; explicit BP barrier below is also required when ROOT already exists: a
  ;; prior mkdir may have succeeded while its parent fsync failed.  Retrying
  ;; must re-establish that publication before a child FNBS record can make a
  ;; later disappearance of ROOT look like a fresh allocator.
  (handler-case
      (progn
        (fnn-safe-directory root t)
        (if (string= (or (sb-ext:posix-getenv "FN_BP_TEST_FAIL_ROOT_PARENT_BARRIER") "")
                     "1")
            ;; Test-only fault point for the existing-root recovery cut.  It
            ;; represents an error from the parent barrier; normal operation
            ;; always calls FNN-FSYNC-DIR below.
            (fnn-indeterminate "bp: injected journal root parent barrier failure")
          (fnn-fsync-dir (fnn-parent root)))
        root)
    (fnn-os-error (e)
      (fnn-indeterminate "bp: journal root parent publication failed: ~a" e))))

(defun fnn-bp-sequence-dir (tally)
  (let* ((dir (fnn-join (fnn-bp-tally-journal tally) "sequence"))
         (prior (fnn-lstat dir)))
    ;; The creation path fsyncs the journal directory; this explicit barrier
    ;; repeats it on recovery too.  An already existing namespace must have a
    ;; frontier and is never silently reinitialised.
    (handler-case
        (progn
          (fnn-safe-directory dir t)
          (fnn-fsync-dir (fnn-parent dir))
          (values dir (null prior)))
      (fnn-os-error (e)
        (fnn-indeterminate "bp: sequence namespace publication failed: ~a" e)))))

(defun fnn-bp-sequence-lock (dir)
  (let ((fd (fnn-open (fnn-join dir "frontier.lock")
                      (logior sb-posix:o-rdwr sb-posix:o-creat +fnn-o-nofollow+)
                      #o600)))
    (unless (fnn-regular-p (fnn-fstat fd))
      (fnn-close fd)
      (fnn-fault "bp: refusing non-regular sequence lock"))
    (handler-case (fnn-flock fd (logior +fnn-lock-ex+ +fnn-lock-nb+))
      (fnn-os-error ()
        (fnn-close fd)
        (fnn-refuse "bp: sequence frontier is already locked")))
    fd))

(defun fnn-bp-reserve-sequence (tally)
  "Reserve one ACL2-owned creation sequence and make its FNBS frame durable.

The exclusive lock covers recovery, reservation and the durable replace.  It
is released before socket I/O: a crash after this returns can leave an unused
sequence, but cannot reuse it."
  (multiple-value-bind (dir freshp) (fnn-bp-sequence-dir tally)
    (let* ((frontier (fnn-join dir "frontier.fnb"))
           (lock (fnn-bp-sequence-lock dir)))
      (unwind-protect
           (let* ((present (fnn-check-regular frontier))
                  (raw (if present
                           (fnn-read-regular-bounded
                            frontier (fnn-core 'fn-bpn-host-sequence-frame-limit))
                         (fnn-make-octets 0)))
                  (recovered (fnn-core 'fn-bpn-host-sequence-recover
                                       (fnn-octet-list raw) (and present t) freshp)))
           (unless (eq (fnn-core 'fn-bpn-host-sequence-ready-p recovered) t)
             (fnn-indeterminate "bp: sequence frontier cannot be recovered"))
           (let* ((reservation
                   (fnn-core 'fn-bpn-host-sequence-reserve
                             (fnn-core 'fn-bpn-host-sequence-frontier recovered))))
             (unless (eq (fnn-core 'fn-bpn-host-sequence-reservationp reservation) t)
               (fnn-refuse "bp: sequence frontier is exhausted"))
             (let ((frame (fnn-core 'fn-bpn-host-sequence-reservation-frame reservation))
                   (stage (fnn-join dir (format nil ".frontier-~d-~a"
                                                (sb-posix:getpid) (fnn-random-hex 12)))))
               (handler-case
                   (progn
                     (fnn-write-staged stage (fnn-octets frame))
                     (fnn-replace stage frontier)
                     (fnn-fsync-dir dir)
                     (fnn-core 'fn-bpn-host-sequence-reservation-sequence reservation))
                 (fnn-os-error (e)
                   (ignore-errors (fnn-unlink stage))
                   (fnn-indeterminate "bp: sequence reservation did not complete: ~a" e))))))
        (ignore-errors (fnn-flock lock +fnn-lock-un+))
        (fnn-close lock)))))

(defun fnn-bp-record (tally name octets)
  "Write one journal record: data durable, then the name durable."
  (let* ((dir (fnn-bp-tally-journal tally))
         (final (fnn-join dir name))
         (stage (fnn-join dir (format nil ".incoming-~d-~a"
                                      (sb-posix:getpid) (fnn-random-hex 12)))))
    (handler-case
        (progn (fnn-write-staged stage (fnn-octets octets))
               (fnn-replace stage final)
               (fnn-fsync-dir dir)
               final)
      (fnn-os-error (e)
        (ignore-errors (fnn-unlink stage))
        (fnn-indeterminate "bp: journal record ~a did not complete: ~a" name e)))))

(defun fnn-bp-deliver (tally conn xfer-id octets)
  "Decode one completed inbound transfer as a bundle and journal the outcome.

The transfer's octets are journalled AS THEY ARRIVED, under `.wire', before
the node is asked what it makes of them.  That ordering is deliberate: a
refusal is as much a thing to keep the evidence of as an acceptance, and an
interoperability vector is only a vector if the bytes another implementation
actually put on the wire are what was kept.  Nothing here interprets them --
the octets are copied, not parsed -- and a write that does not complete is
an indeterminate outcome, which is the truth about a transfer whose evidence
may or may not be durable."
  (let* ((obs (fnn-bp-observation (fnn-bp-tally-wall tally)
                                  (fnn-bp-tally-wall-error tally)))
         (result (fnn-core 'fn-bpn-host-receive (fnn-bp-tally-config tally)
                           octets obs))
         (outcome (fnn-core 'fn-bpn-host-receive-outcome result))
         (reason (fnn-core 'fn-bpn-host-receive-reason result))
         (adu (fnn-core 'fn-bpn-host-receive-adu result))
         (tag (fnn-tclc-tag conn)))
    (fnn-bp-record tally (format nil "~a-~d.wire" tag xfer-id) octets)
    (setf (fnn-bp-tally-last-reason tally) reason)
    (ecase outcome
      (:accepted
       (incf (fnn-bp-tally-accepted tally))
       (setf (fnn-bp-tally-last-adu tally) adu)
       (let ((path (fnn-bp-record tally (format nil "~a-~d.adu" tag xfer-id) adu)))
         (fnn-out "BP accepted xfer=~d adu=~d path=~a"
                  xfer-id (length adu) path)
         path))
      (:refused
       (incf (fnn-bp-tally-refused tally))
       (let ((path (fnn-bp-record tally (format nil "~a-~d.refused" tag xfer-id)
                                  (fnn-octet-list
                                   (fnn-string-octets
                                    (format nil "~(~a~)~%" reason))))))
         (fnn-out "BP refused xfer=~d reason=~(~a~)" xfer-id reason)
         path))
      (:uncertain
       (incf (fnn-bp-tally-uncertain tally))
       (let ((path (fnn-bp-record tally (format nil "~a-~d.uncertain" tag xfer-id)
                                  (fnn-octet-list
                                   (fnn-string-octets
                                    (format nil "~(~a~)~%" reason))))))
         (fnn-out "BP uncertain xfer=~d reason=~(~a~)" xfer-id reason)
         path)))))

(defun fnn-bp-exit-code (tally conn)
  "Three outcomes, three codes.  Uncertain dominates a refusal, and a refusal
dominates an acceptance: a run that saw one of each did not succeed."
  (cond ((plusp (fnn-bp-tally-uncertain tally)) +fnn-exit-uncertain+)
        ((plusp (fnn-bp-tally-refused tally)) +fnn-exit-refused+)
        ((and conn (eq (fnn-tclc-outcome conn) :uncertain)) +fnn-exit-uncertain+)
        ((and conn (eq (fnn-tclc-outcome conn) :refused)) +fnn-exit-refused+)
        (t +fnn-exit-ok+)))

(defun fnn-bp-summary (tally)
  (fnn-out "BP summary accepted=~d refused=~d uncertain=~d"
           (fnn-bp-tally-accepted tally) (fnn-bp-tally-refused tally)
           (fnn-bp-tally-uncertain tally)))

;;; ---------------------------------------------------------------------------
;;; `bp send'

(defun fnn-command-bp-send (host port adu-path journal node-id peer-eid
                            lifetime crc-type hop-limit transfer-mru
                            expect wall wall-error)
  (let* ((config (fnn-bp-config node-id lifetime crc-type hop-limit transfer-mru))
         (peer (fnn-bp-eid peer-eid))
         (adu (fnn-octet-list (fnn-read-regular-bounded adu-path transfer-mru)))
         (obs (fnn-bp-observation wall wall-error))
         (tally (make-fnn-bp-tally :config config :wall wall :wall-error wall-error
                                   :journal (fnn-bp-journal-dir journal)))
         (sequence (fnn-bp-reserve-sequence tally))
         (bundle (fnn-core 'fn-bpn-host-send config peer adu sequence obs))
         (summary (fnn-core 'fn-bpn-host-sent-summary config peer adu sequence obs))
         (socket nil))
    (unless bundle
      (fnn-refuse "bp: this ADU and configuration are not a bundle this node can author"))
    (fnn-out "BP authored creation=~d sequence=~d lifetime=~d payload=~d octets=~d"
             (first summary) (second summary) (third summary) (fourth summary)
             (length bundle))
    ;; The bundle this node authored, kept before it is put on a socket, for
    ;; the same reason the receive path keeps what arrives: an octet string
    ;; another implementation accepted is only a vector if it was recorded.
    (fnn-out "BP wire authored path=~a"
             (fnn-bp-record tally (format nil "authored-~d.wire" sequence)
                            bundle))
    (unwind-protect
         (let ((*fnn-tcl-deliver*
                 (lambda (conn xfer-id octets)
                   (fnn-bp-deliver tally conn xfer-id octets))))
           (setq socket (fnn-tcl-connect host port))
           (let ((conn (fnn-tcl-session
                        (fnn-socket-fd socket) :active
                        ;; The convergence layer's expected peer is a
                        ;; SESSION identity (RFC 9174 section 4.2), not the
                        ;; bundle's destination: a bundle for
                        ;; dtn://x/demux may travel over a session with any
                        ;; node.  Passing the destination here would refuse
                        ;; every correct session whose peer is not also the
                        ;; final destination.
                        (fnn-tcl-params node-id nil +fnn-tcl-keepalive+
                                        +fnn-tcl-segment-mru+ transfer-mru)
                        "active" journal
                        :bundle bundle :expect expect)))
             (fnn-tcl-summary conn)
             (fnn-bp-summary tally)
             (fnn-bp-exit-code tally conn)))
      (when socket (fnn-socket-shut socket)))))

;;; ---------------------------------------------------------------------------
;;; `bp receive'

(defun fnn-command-bp-receive (port once journal node-id peer-eid lifetime
                               crc-type hop-limit transfer-mru reply-adu
                               reply-peer wall wall-error)
  (let* ((config (fnn-bp-config node-id lifetime crc-type hop-limit transfer-mru))
         (tally (make-fnn-bp-tally :config config :wall wall :wall-error wall-error
                                   :journal (fnn-bp-journal-dir journal)))
         (reply (when reply-adu
                  (let* ((peer (fnn-bp-eid (or reply-peer node-id)))
                         (adu (fnn-octet-list
                               (fnn-read-regular-bounded reply-adu transfer-mru)))
                         (obs (fnn-bp-observation wall wall-error))
                         (sequence (fnn-bp-reserve-sequence tally))
                         (octets (fnn-core 'fn-bpn-host-send config peer adu sequence obs)))
                    (unless octets
                      (fnn-refuse "bp: the reply ADU is not a bundle this node can author"))
                    octets)))
         (listener nil)
         (code +fnn-exit-ok+))
    (unwind-protect
         (let ((*fnn-tcl-deliver*
                 (lambda (conn xfer-id octets)
                   (fnn-bp-deliver tally conn xfer-id octets))))
           (multiple-value-bind (bound bound-port) (fnn-tcl-listen port)
             (setq listener bound)
             (fnn-out "BP LISTENING ~d" bound-port))
           (fnn-accept-loop
            listener
            (lambda (socket)
              (let ((fd (fnn-socket-fd socket)))
                (unwind-protect
                     (handler-case
                         (let ((conn (fnn-tcl-session
                                      fd :passive
                                      (fnn-tcl-params node-id peer-eid
                                                      +fnn-tcl-keepalive+
                                                      +fnn-tcl-segment-mru+
                                                      transfer-mru)
                                      "passive" journal :bundle reply)))
                           (fnn-tcl-summary conn)
                           (setq code (fnn-bp-exit-code tally conn)))
                       (fnn-store-indeterminate (e)
                         (fnn-err "bp: ~a" e)
                         (setq code +fnn-exit-uncertain+))
                       (fnn-store-error (e)
                         (fnn-err "bp: ~a" e)
                         (setq code +fnn-exit-refused+))
                       ((or fnn-os-error sb-bsd-sockets:socket-error) (e)
                         (fnn-err "bp: ~a" e)
                         (setq code +fnn-exit-uncertain+)))
                  (fnn-socket-shut socket))))
            once)
           (fnn-bp-summary tally)
           code)
      (when listener (fnn-socket-shut listener)))))

;;; ---------------------------------------------------------------------------
;;; `bp decode' -- a file of octets in, the node's verdict out, no socket.
;;; This is what the interoperability harness uses to say what fn made of a
;;; bundle another implementation authored.

(defun fnn-command-bp-decode (path node-id lifetime crc-type hop-limit
                              transfer-mru wall wall-error adu-out)
  (let* ((config (fnn-bp-config node-id lifetime crc-type hop-limit transfer-mru))
         (octets (fnn-octet-list (fnn-read-regular-bounded path transfer-mru)))
         (obs (fnn-bp-observation wall wall-error))
         (result (fnn-core 'fn-bpn-host-receive config octets obs))
         (outcome (fnn-core 'fn-bpn-host-receive-outcome result))
         (reason (fnn-core 'fn-bpn-host-receive-reason result))
         (adu (fnn-core 'fn-bpn-host-receive-adu result)))
    (fnn-out "BP decode outcome=~(~a~) reason=~(~a~) adu=~d"
             outcome reason (length adu))
    (when (and adu-out (eq outcome :accepted))
      (fnn-write-staged adu-out (fnn-octets adu)))
    (ecase outcome
      (:accepted +fnn-exit-ok+)
      (:refused +fnn-exit-refused+)
      (:uncertain +fnn-exit-uncertain+))))

;;; ---------------------------------------------------------------------------
;;; The positional protocol behind `--fn bp'.  `-' selects the default.
;;;
;;;   bp send HOST PORT ADU-FILE [JOURNAL NODE-ID PEER-EID LIFETIME CRC-TYPE
;;;                               HOP-LIMIT TRANSFER-MRU EXPECT
;;;                               WALL WALL-ERROR]
;;;   bp receive PORT [ONCE JOURNAL NODE-ID PEER-EID LIFETIME CRC-TYPE
;;;                    HOP-LIMIT TRANSFER-MRU REPLY-ADU REPLY-PEER
;;;                    WALL WALL-ERROR]
;;;   bp decode FILE [NODE-ID LIFETIME CRC-TYPE HOP-LIMIT TRANSFER-MRU
;;;                   WALL WALL-ERROR ADU-OUT]

(defun fnn-dispatch-bp (command args)
  (flet ((need (n)
           (when (< (length args) n)
             (error 'fnn-usage-error :message "bp: missing arguments")))
         (number (index default)
           (fnn-tcl-number (fnn-tcl-arg args index) default))
         (optional-number (index)
           (let ((text (fnn-tcl-arg args index)))
             (and text (parse-integer text)))))
    (cond
      ((string= command "send")
       (need 3)
       (fnn-command-bp-send
        (first args) (parse-integer (second args)) (third args)
        (fnn-tcl-arg args 3 "bp-journal")
        (fnn-tcl-arg args 4 "dtn://fn-a/")
        (fnn-tcl-arg args 5 "dtn://fn-b/")
        (number 6 +fnn-bp-lifetime+)
        (number 7 +fnn-bp-crc-type+)
        (number 8 +fnn-bp-hop-limit+)
        (number 9 +fnn-tcl-transfer-mru+)
        (number 10 0)
        (optional-number 11)
        (number 12 0)))
      ((string= command "receive")
       (need 1)
       (fnn-command-bp-receive
        (parse-integer (first args))
        (string= (fnn-tcl-arg args 1 "1") "1")
        (fnn-tcl-arg args 2 "bp-journal")
        (fnn-tcl-arg args 3 "dtn://fn-b/")
        (fnn-tcl-arg args 4)
        (number 5 +fnn-bp-lifetime+)
        (number 6 +fnn-bp-crc-type+)
        (number 7 +fnn-bp-hop-limit+)
        (number 8 +fnn-tcl-transfer-mru+)
        (fnn-tcl-arg args 9)
        (fnn-tcl-arg args 10)
        (optional-number 11)
        (number 12 0)))
      ((string= command "decode")
       (need 1)
       (fnn-command-bp-decode
        (first args)
        (fnn-tcl-arg args 1 "dtn://fn-b/")
        (number 2 +fnn-bp-lifetime+)
        (number 3 +fnn-bp-crc-type+)
        (number 4 +fnn-bp-hop-limit+)
        (number 5 +fnn-tcl-transfer-mru+)
        (optional-number 6)
        (number 7 0)
        (fnn-tcl-arg args 8)))
      (t (error 'fnn-usage-error
                :message (format nil "unknown bp command ~a" command))))))

(fnn-register-verb "bp" #'fnn-dispatch-bp)
