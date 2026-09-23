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

(defun fnn-bp-monotonic-now ()
  "Milliseconds on Linux CLOCK_BOOTTIME, whose origin survives process death.
This is host clock evidence, not an ACL2 expiry decision.  A reboot starts a
new origin and needs a separately identified recovery epoch."
  #+(and sbcl linux)
  (multiple-value-bind (seconds nanoseconds)
      (sb-unix::clock-gettime 7) ; Linux CLOCK_BOOTTIME includes suspend time.
    (+ (* 1000 seconds) (floor nanoseconds 1000000)))
  #-(and sbcl linux)
  (error "BP monotonic clock requires Linux CLOCK_BOOTTIME"))

(defun fnn-bp-boot-id-observation ()
  "Bounded Linux boot identifier; ACL2 validates its UUID syntax and domain."
  #+(and sbcl linux)
  (fnn-octet-list
   (fnn-read-regular-bounded "/proc/sys/kernel/random/boot_id" 37))
  #-(and sbcl linux)
  (error "BP clock domain requires Linux boot ID"))

(defun fnn-bp-observation (wall wall-error)
  "One observation per wakeup.  With no operator-supplied DTN time the
observation has no wall reading, and `fn-bpn-creation-time' then writes the
zero of RFC 9171 section 4.2.6 rather than a monotonic counter."
  (let ((obs (fnn-core 'fn-bpn-host-observation (fnn-bp-monotonic-now)
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
  (journal nil) (spool-lock nil) (evidence-dir nil) (evidence-state nil)
  (last-adu nil) (last-reason nil))

(defun fnn-bp-journal-dir (root)
  ;; FNN-SAFE-DIRECTORY barriers the parent only when it creates ROOT.  The
  ;; explicit BP barrier below is also required when ROOT already exists: a
  ;; prior mkdir may have succeeded while its parent fsync failed.  Retrying
  ;; must re-establish that publication before a child FNBS record can make a
  ;; later disappearance of ROOT look like a fresh allocator.
  (handler-case
      (progn
        (fnn-safe-directory root t)
        (if (string= (or (fnn-developer-selector "FN_BP_TEST_FAIL_ROOT_PARENT_BARRIER") "")
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
      (fnn-os-error (e)
        (ignore-errors (fnn-close fd))
        ;; Only nonblocking contention is an ordinary refusal.  A broken
        ;; descriptor, I/O failure, or another flock errno must remain a
        ;; fault; this host cannot say the reservation was merely busy.
        (if (eql (fnn-os-errno e) sb-posix:eagain)
            (fnn-refuse "bp: sequence frontier is already locked")
          (fnn-fault "bp: sequence frontier lock failed: ~a" e))))
    fd))

(defun fnn-bp-reserve-sequence (tally)
  "Reserve one ACL2-owned creation sequence and make its FNBS frame durable.

The exclusive lock covers recovery, reservation and the durable replace.  It
is released before socket I/O: a crash after this returns can leave an unused
sequence.  The ACL2 persistence-cut trace proof required to make an all-crash
nonreuse claim remains open."
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
                     (values
                      (fnn-core 'fn-bpn-host-sequence-reservation-sequence reservation)
                      reservation))
                 (fnn-os-error (e)
                   (ignore-errors (fnn-unlink stage))
                   (fnn-indeterminate "bp: sequence reservation did not complete: ~a" e))))))
        (ignore-errors (fnn-flock lock +fnn-lock-un+))
        (fnn-close lock)))))

(defun fnn-bp-authored-wire-publish (tally config peer adu reservation obs)
  "Publish the exact ACL2-authored bundle under its reserved immutable name."
  (let* ((dir (fnn-bp-tally-journal tally))
         ;; ACL2 derives this preview from the reservation token.  It exists
         ;; solely so the host can observe that exact pathname while holding
         ;; the shared spool lock; the operation below must return it unchanged.
         (preview (fnn-core 'fn-bpn-host-authored-wire-name reservation)))
    (unless (and (stringp preview) (> (length preview) 0)
                 (null (position #\/ preview)))
      (fnn-fault "bp: ACL2 returned an invalid authored-wire name"))
    (let* ((final (fnn-join dir preview))
           (final-absent (if (fnn-lstat final) nil t))
           (operation
            (fnn-core 'fn-bpn-host-authored-wire-authorize
                      config peer adu reservation obs
                      (if (fnn-bp-tally-spool-lock tally) t nil)
                      final-absent)))
      (unless (eq (fnn-core 'fn-bpn-host-authored-wire-operationp operation) t)
        (if final-absent
            (fnn-fault "bp: ACL2 refused its authored-wire reservation")
          ;; A durable sequence is never reused.  Any pre-existing exact next
          ;; name is conflicting recovery evidence, including equal bytes; it
          ;; is never replaced or silently accepted as this operation's write.
          (fnn-indeterminate
           "bp: reserved authored-wire name is already occupied: ~a" preview)))
      (let* ((name
              (fnn-core 'fn-bpn-host-authored-wire-operation-name operation))
             (wire
              (fnn-core 'fn-bpn-host-authored-wire-operation-wire operation))
             (publication
              (fnn-core
               'fn-bpn-host-authored-wire-operation-publication operation))
             (label
              (fnn-core 'fn-bpn-host-authored-wire-operation-label operation)))
        (unless (and (stringp name) (string= name preview)
                     (fnn-octet-list-p wire))
          (fnn-fault "bp: ACL2 changed its authored-wire publication echo"))
        (let* ((stage
                (fnn-join dir (format nil ".authored-~d-~a"
                                      (sb-posix:getpid) (fnn-random-hex 12))))
               (outcome
                (fnn-immutable-publish-effect
                 publication stage final dir (fnn-octets wire)
                 :cleanup-directory dir :operation-label label)))
          (case outcome
            (:durable (values final wire))
            (:refused
             (fnn-refuse "bp: authored-wire publication refused before link"))
            (otherwise
             (fnn-indeterminate
              "bp: authored-wire publication outcome is uncertain"))))))))

(defun fnn-bp-evidence-entry-kind (path)
  (let ((st (fnn-lstat path)))
    (if (and st (fnn-regular-p st) (not (fnn-symlink-p st)))
        :regular
      :other)))

(defun fnn-bp-evidence-name (value)
  (unless (and (stringp value) (> (length value) 0)
               (null (position #\/ value)))
    (fnn-fault "bp: ACL2 returned an invalid evidence name"))
  value)

(defun fnn-bp-evidence-open (tally)
  "Recover the ACL2-owned immutable receive-evidence namespace.

The shared spool lock is already held.  Legacy root-level passive-X files are
left untouched and are not allocation records in this namespace."
  (let* ((directory-name
          (fnn-bp-evidence-name
           (fnn-core 'fn-bpn-host-evidence-directory-name)))
         (dir (fnn-join (fnn-bp-tally-journal tally) directory-name)))
    (handler-case
        (progn
          (fnn-safe-directory dir t)
          ;; Repeat both barriers on reopen.  Allocation is based only on the
          ;; complete namespace after these authoritative recovery barriers.
          (fnn-fsync-dir (fnn-parent dir))
          (fnn-fsync-dir dir))
      (fnn-os-error (e)
        (fnn-indeterminate "bp: evidence namespace recovery failed: ~a" e)))
    (let ((limit (fnn-core 'fn-bpn-host-evidence-max-entries)))
      ;; Fetch and validate the ACL2-owned policy before opening the directory:
      ;; a hostile namespace must not allocate a complete host list before its
      ;; admission bound exists.
      (unless (and (integerp limit) (>= limit 0))
        (fnn-fault "bp: ACL2 returned an invalid evidence bound"))
      (let* ((names (handler-case
                        (fnn-list-directory-bounded
                         dir limit "bp: receive evidence namespace")
                      (fnn-os-error (e)
                        (fnn-indeterminate
                         "bp: evidence namespace cannot be enumerated: ~a" e))))
             (sorted (sort (copy-list names) #'string<))
             (entries
              (mapcar (lambda (name)
                        (cons name
                              (fnn-bp-evidence-entry-kind
                               (fnn-join dir name))))
                      sorted))
             (recovered (fnn-core 'fn-bpn-host-evidence-recover entries)))
        (unless (eq (fnn-core 'fn-bpn-host-evidence-readyp recovered) t)
          (fnn-fault "bp: receive evidence namespace is inconsistent"))
        (setf (fnn-bp-tally-evidence-dir tally) dir
              (fnn-bp-tally-evidence-state tally) recovered)
        tally))))

(defun fnn-bp-evidence-publish-one (tally publication final-name octets)
  (let* ((root (fnn-bp-tally-journal tally))
         (dir (fnn-bp-tally-evidence-dir tally))
         (stage (fnn-join root (format nil ".incoming-~d-~a"
                                       (sb-posix:getpid) (fnn-random-hex 12))))
         (final (fnn-join dir final-name)))
    (fnn-immutable-publish-effect publication stage final dir
                                  (fnn-octets octets)
                                  :cleanup-directory root)))

(defun fnn-bp-evidence-publish (tally outcome wire result-octets)
  "Publish exact wire bytes and their verdict under one ACL2 identity.

The successor is installed only after the wire allocation is durable.  Any
uncertain result raises fnn-store-indeterminate, which the command lets escape
the accept loop; no later connection can mutate the journal in this process."
  (let* ((st (fnn-bp-tally-evidence-state tally))
         (wire-name
          (fnn-bp-evidence-name
           (fnn-core 'fn-bpn-host-evidence-next-wire-name st)))
         (result-name
          (fnn-bp-evidence-name
           (fnn-core 'fn-bpn-host-evidence-next-result-name st outcome)))
         (dir (fnn-bp-tally-evidence-dir tally))
         (wire-absent (null (fnn-check-regular (fnn-join dir wire-name))))
         (result-absent (null (fnn-check-regular (fnn-join dir result-name))))
         (lock-owned (if (fnn-bp-tally-spool-lock tally) t nil))
         (operation
          (fnn-core 'fn-bpn-host-evidence-authorize
                    st outcome lock-owned wire-absent result-absent)))
    (unless (eq (fnn-core 'fn-bpn-host-evidence-operationp operation) t)
      (fnn-refuse "bp: receive evidence admission refused"))
    ;; Use the names carried by the authorization capability, not the preview.
    (setq wire-name
          (fnn-bp-evidence-name
           (fnn-core 'fn-bpn-host-evidence-operation-wire-name operation))
          result-name
          (fnn-bp-evidence-name
           (fnn-core 'fn-bpn-host-evidence-operation-result-name operation)))
    (case
        (fnn-bp-evidence-publish-one
         tally
         (fnn-core 'fn-bpn-host-evidence-operation-wire-publication operation)
         wire-name wire)
      (:durable
       ;; The exact bytes now own this identity, even if the sidecar fails.
       (setf (fnn-bp-tally-evidence-state tally)
             (fnn-core 'fn-bpn-host-evidence-operation-successor operation)))
      (:refused (fnn-refuse "bp: receive wire evidence publication refused"))
      (otherwise
       (fnn-indeterminate "bp: receive wire evidence publication uncertain")))
    (case
        (fnn-bp-evidence-publish-one
         tally
         (fnn-core 'fn-bpn-host-evidence-operation-result-publication operation)
         result-name result-octets)
      (:durable (fnn-join dir result-name))
      (:refused (fnn-refuse "bp: receive verdict evidence publication refused"))
      (otherwise
       (fnn-indeterminate "bp: receive verdict evidence publication uncertain")))))

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
  ; Test-only exact core/adapter fault.  This runs inside the receive callback
  ; and the command's production handler, so exit-code evidence exercises the
  ; real subtype ordering rather than a sibling classifier.
  (when (string= (or (fnn-developer-selector "FN_BP_TEST_DELIVER_FAULT") "") "1")
    (fnn-fault "bp: injected receive core fault"))
  (let* ((obs (fnn-bp-observation (fnn-bp-tally-wall tally)
                                  (fnn-bp-tally-wall-error tally)))
         (result (fnn-core 'fn-bpn-host-receive (fnn-bp-tally-config tally)
                           octets obs))
         (outcome (fnn-core 'fn-bpn-host-receive-outcome result))
         (reason (fnn-core 'fn-bpn-host-receive-reason result))
         (adu (fnn-core 'fn-bpn-host-receive-adu result)))
    (declare (ignore conn))
    (setf (fnn-bp-tally-last-reason tally) reason)
    (ecase outcome
      (:accepted
       (let ((path (fnn-bp-evidence-publish tally outcome octets adu)))
       (incf (fnn-bp-tally-accepted tally))
       (setf (fnn-bp-tally-last-adu tally) adu)
         (fnn-out "BP accepted xfer=~d adu=~d path=~a"
                  xfer-id (length adu) path)
         (list :accepted path)))
      (:refused
       (fnn-bp-evidence-publish
        tally outcome octets
        (fnn-octet-list
         (fnn-string-octets (format nil "~(~a~)~%" reason))))
       (incf (fnn-bp-tally-refused tally))
       (fnn-out "BP refused xfer=~d reason=~(~a~)" xfer-id reason)
       (list :refused reason))
      (:uncertain
       (fnn-bp-evidence-publish
        tally outcome octets
        (fnn-octet-list
         (fnn-string-octets (format nil "~(~a~)~%" reason))))
       (incf (fnn-bp-tally-uncertain tally))
       (fnn-out "BP uncertain xfer=~d reason=~(~a~)" xfer-id reason)
       (list :uncertain reason)))))

(defun fnn-bp-deliver-node
  (service conn session-counter xfer-id octets owner channel)
  "Complete one transfer through the single FNBS machine owner."
  (when (string= (or (fnn-developer-selector "FN_BP_TEST_DELIVER_FAULT") "") "1")
    (fnn-fault "bp: injected receive core fault"))
  (let* ((tally (fnn-bps-tally service))
         (ingress (fnn-bps-tcpcl-ingress
                   service conn session-counter xfer-id owner channel)))
    (multiple-value-bind (result adu)
        (fnn-bps-receive service ingress octets)
      (case (first result)
        (:accepted
         (incf (fnn-bp-tally-accepted tally))
         (setf (fnn-bp-tally-last-adu tally) adu
               (fnn-bp-tally-last-reason tally) :stored)
         (fnn-out "BP accepted xfer=~d adu=~d path=~a"
                  xfer-id (length adu) (second result)))
        (:refused
         ;; A refused transfer has no kind-5 custody record.  The separate
         ;; evidence namespace retains its exact wire and refusal reason.
         (let* ((reason (second result))
                (text (fnn-octet-list
                       (fnn-string-octets (format nil "~(~a~)~%" reason)))))
           (fnn-bp-evidence-publish tally :refused octets text)
           (incf (fnn-bp-tally-refused tally))
           (setf (fnn-bp-tally-last-reason tally) reason)
           (fnn-out "BP refused xfer=~d reason=~(~a~)" xfer-id reason)))
        (:uncertain
         ;; No new I/O follows an ambiguous FNBS publication.  TCPCL's
         ;; disposition mapper withholds the held ACK and stops this owner.
         (incf (fnn-bp-tally-uncertain tally))
         (setf (fnn-bp-tally-last-reason tally) (second result))
         (fnn-out "BP uncertain xfer=~d reason=~(~a~)"
                  xfer-id (second result)))
        (otherwise
         (fnn-indeterminate "bp: invalid foundation callback result")))
      result)))

(defun fnn-bp-exit-code (tally conn)
  "Three outcomes, three codes.  Uncertain dominates a refusal, and a refusal
dominates an acceptance: a run that saw one of each did not succeed."
  (case (fnn-core 'fn-bpn-host-run-outcome
                  (fnn-bp-tally-accepted tally)
                  (fnn-bp-tally-refused tally)
                  (fnn-bp-tally-uncertain tally)
                  (and conn (fnn-tclc-outcome conn)))
    (:accepted +fnn-exit-ok+)
    (:refused +fnn-exit-refused+)
    (t +fnn-exit-uncertain+)))

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
         ;; The standalone sender shares the FNBS owner and clock-domain gate
         ;; with bp-service, so it cannot create an unmarked sequence frontier.
         (service (fnn-bps-open journal config wall wall-error))
         (journal-root (fnn-bps-root service)))
    (unwind-protect
         (let* ((tally (fnn-bp-evidence-open (fnn-bps-tally service)))
                (socket nil))
           (multiple-value-bind (sequence reservation)
               (fnn-bp-reserve-sequence tally)
             (multiple-value-bind (path bundle)
                 (fnn-bp-authored-wire-publish
                  tally config peer adu reservation obs)
               (let ((summary
                      (fnn-core 'fn-bpn-host-sent-summary
                                config peer adu sequence obs)))
                 (fnn-out
                  "BP authored creation=~d sequence=~d lifetime=~d payload=~d octets=~d"
                  (first summary) (second summary) (third summary) (fourth summary)
                  (length bundle))
                 ;; The exact ACL2-authored bytes become durable evidence before
                 ;; the first socket operation.  A retry allocates a new sequence;
                 ;; it never treats this immutable name as a retransmit slot.
                 (fnn-out "BP wire authored path=~a" path)
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
                                     "active" journal-root
                                     :bundle bundle :expect expect)))
                          (fnn-tcl-summary conn)
                          (fnn-bp-summary tally)
                          (fnn-bp-exit-code tally conn)))
                   (when socket (fnn-socket-shut socket)))))))
      (fnn-bps-release service))))

;;; ---------------------------------------------------------------------------
;;; `bp receive'

(defun fnn-command-bp-receive (port once journal node-id peer-eid lifetime
                               crc-type hop-limit transfer-mru reply-adu
                               reply-peer wall wall-error)
  (let* ((config (fnn-bp-config node-id lifetime crc-type hop-limit transfer-mru))
         (journal-root (fnn-bp-journal-dir journal))
         (service (fnn-bps-open journal config wall wall-error)))
    (unwind-protect
         (let* ((tally (fnn-bp-evidence-open (fnn-bps-tally service)))
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
                (progn
                  (multiple-value-bind (bound bound-port) (fnn-tcl-listen port)
                    (setq listener bound)
                    (fnn-out "BP LISTENING ~d" bound-port))
                  (fnn-accept-loop
                   listener
                   (lambda (socket)
                     (let* ((fd (fnn-socket-fd socket))
                            (session-counter
                              (incf (fnn-bps-next-session service)))
                            (*fnn-tcl-deliver*
                              (lambda (conn xfer-id octets)
                                (fnn-bp-deliver-node
                                 service conn session-counter xfer-id octets
                                 nil nil))))
                       (unwind-protect
                            (handler-case
                                (let ((conn (fnn-tcl-session
                                             fd :passive
                                             (fnn-tcl-params node-id peer-eid
                                                             +fnn-tcl-keepalive+
                                                             +fnn-tcl-segment-mru+
                                                             transfer-mru)
                                             "passive" journal-root :bundle reply)))
                                  (fnn-tcl-summary conn)
                                  (setq code (fnn-bp-exit-code tally conn)))
                              ; A journal ambiguity or core fault is an owner
                              ; outcome, not a connection-local verdict.  Let
                              ; it escape the accept loop so unwind-protect
                              ; closes the listener and no later socket can
                              ; mutate this journal in the same process.
                              (fnn-store-indeterminate (e) (error e))
                              (fnn-store-fault (e) (error e))
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
             (when listener (fnn-socket-shut listener))))
      (fnn-bps-release service))))

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
