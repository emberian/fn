; ACL2 wrappers for the native host's TCPCLv4 convergence layer (RFC 9174).
;
; host/native/tcpcl.lisp calls exactly these, through `fnn-call', and opens no
; TCPCL record of its own.  Every protocol value -- the octets of a message,
; its kind, segment and transfer MRUs, the negotiated keepalive, refusal and
; termination reason codes, which transfer completed -- is computed here, by
; books/tcpcl-session.lisp and books/tcpcl-octets.lisp, and read out of the
; flat triple below.  The raw host contributes three things the books do not
; have: the socket, one monotonic clock reading per wakeup, and the durability
; barrier under a received bundle.
;
; Each driver returns (session events unconsumed) as a plain list, so the host
; never applies a record accessor and never sees a record's shape.

(in-package "ACL2")
(include-book "../books/tcpcl-session")
(include-book "../books/tcpcl-host-drive")
(include-book "../books/tcpcl-delivery")
(include-book "../books/tcpcl-received-count")
(include-book "../books/tcpcl-received-source")
(include-book "../books/tcpcl-source-continuation")
(include-book "../books/tcpcl-spool")

; Directory names and lstat kinds in; a complete recovery plan out.  The raw
; host validates the whole plan before unlinking anything, then performs only
; the :remove actions selected here.
(defun fn-tcl-host-spool-recovery-plan (entries)
  (fn-tcl-spool-recovery-plan entries))

; -----------------------------------------------------------------------------
; Opening a session.  The operator's configuration becomes params here; the
; host passes numbers and octets and never assembles the record.

(defun fn-tcl-host-params (keepalive segment-mru transfer-mru node-id can-tls
                                     expected-peer)
  (fn-tcl-make-params keepalive segment-mru transfer-mru node-id
                      (if can-tls t nil)
                      (if expected-peer expected-peer nil)))

(defun fn-tcl-host-paramsp (p)
  (fn-tcl-paramsp p))

; NIL when the host offered a role, params or clock reading the machine will
; not accept: a refusal, distinct from a session.
(defun fn-tcl-host-initial (role local now)
  (if (and (fn-tcl-rolep role) (fn-tcl-paramsp local) (fn-clock-timep now))
      (fn-tcl-initial-session role local now)
    nil))

; -----------------------------------------------------------------------------
; The transitions.  One per host wakeup cause.

(defun fn-tcl-host-open (s now)
  (fn-tcl-host-triple (fn-tcl-open s now)))

; The host has a monotonic millisecond reading and no trusted wall clock; the
; observation is built here so that its shape is the books' and not the host's.
(defun fn-tcl-host-tick (s monotonic)
  (fn-tcl-host-triple (fn-tcl-tick s (fn-clock-observation monotonic 0 0 nil))))

(defun fn-tcl-host-send (s ref octets now)
  (declare (xargs :guard (fn-cbor-octet-listp octets) :verify-guards nil))
  (fn-tcl-host-triple (fn-tcl-send s ref octets now)))

(defun fn-tcl-host-pump (s now)
  (fn-tcl-host-triple (fn-tcl-pump s now)))

(defun fn-tcl-host-tcp-closed (s)
  (fn-tcl-host-triple (fn-tcl-tcp-closed s)))

; A shutdown the operator asked for is not one of the RFC's named causes, so
; it carries Unknown (RFC 9174 section 6.1).  The code is the book's constant.
(defun fn-tcl-host-terminate (s now)
  (fn-tcl-host-triple (fn-tcl-terminate s *fn-tcl-term-unknown* now)))

; Whether the active entity ends the session now (RFC 9174 section 6.1: only
; it initiates SESS_TERM here).  The session machine has no effect that says
; "nothing more to send or await"; this is that decision, over facts the
; machine's own events set.  The transfer the host was given must have an
; outcome (:outbound-sent, :outbound-refused, :outbound-failed or a decided
; :send-refused cleared it), and then either the EXPECT inbound transfers
; have arrived, or that outcome is not an acceptance: a receipt answers an
; accepted bundle, so a refused or uncertain one is awaited for nothing
; (planning/evidence/stale-native-tests-2026-09-24.md, finding 3).
(defun fn-tcl-host-active-closep (s bundlep pendingp outcome inbound expect)
  (and (equal (fn-tcl-session-phase s) :established)
       (not pendingp)
       (or (not bundlep) (and outcome t))
       (or (and bundlep (member-equal outcome '(:refused :uncertain)) t)
           (>= (nfix inbound) (nfix expect)))))

; -----------------------------------------------------------------------------
; Reading a result out.  The host asks; it does not compute.

(defun fn-tcl-host-encode (m)
  (fn-tcl-encode m))

(defun fn-tcl-host-phase (s)
  (fn-tcl-session-phase s))

; The negotiated keepalive in seconds, 0 before SESS_INIT and when the peer
; asked for none.  The host divides it to choose a read timeout; the interval
; itself is the machine's.
(defun fn-tcl-host-keepalive (s)
  (let ((n (fn-tcl-session-negotiated s)))
    (if n (fn-tcl-negotiated-keepalive n) 0)))

; -----------------------------------------------------------------------------
; Event digests.  A session log line must be bounded, so the bulk octets of a
; message or a received bundle are replaced by their length -- computed here,
; like every other length in this protocol.  The digest is what the host logs
; and what the differential compares, so both sides compare the same object.

(defun fn-tcl-host-event-digest (e)
  (cond ((not (consp e)) e)
        ((equal (car e) :send)
         (list :send (fn-tcl-msg-kind (car (cdr e)))
               (len (fn-tcl-encode (car (cdr e))))))
        ((equal (car e) :bundle-received)
         (list :bundle-received (car (cdr e)) (len (car (cdr (cdr e))))))
        ((equal (car e) :session-up)
         (let ((n (car (cdr e))))
           (list :session-up (fn-tcl-negotiated-keepalive n)
                 (fn-tcl-negotiated-segment-mtu n)
                 (fn-tcl-negotiated-transfer-mtu n)
                 (fn-tcl-negotiated-tls n))))
        (t e)))

; Executes by a loop (lane depth-debt, PRF-919): one digest per event of a
; socket chunk's drive, as many as the chunk's messages.  ACC holds the
; digests so far, reversed.
(defun fn-tcl-host-event-digests-loop (events acc)
  (if (consp events)
      (fn-tcl-host-event-digests-loop
       (cdr events) (cons (fn-tcl-host-event-digest (car events)) acc))
    (fn-ag-rev-onto acc nil)))

(defun fn-tcl-host-event-digests (events)
  (fn-tcl-host-event-digests-loop events nil))

; -----------------------------------------------------------------------------
; The differential's model side.  STEPS is the trace the session loop wrote:
; one (now octets) pair per socket read, in order, with the octets exactly as
; they arrived.  Folding fn-tcl-drive over it with the carry reproduces the
; loop's whole event stream in one call, with no socket and no host in the way;
; tools/tcpcl_lab.py compares the two digests.

; Guard-verified (lane depth-debt-2, PRF-919): the carry and the events are
; octets and events of the whole trace, and an unverified function's *1*
; appended them one control-stack frame per element.  The :exec is the fold
; with the session's functions called through ec-call and the appends in
; constant stack (fn-ag-append).
(defun fn-tcl-host-fold (s carry steps acc)
  (declare (xargs :measure (len steps) :guard t :verify-guards nil))
  (mbe
   :logic
   (if (not (consp steps))
       (list s acc carry)
     (let ((r (fn-tcl-drive s (append carry (car (cdr (car steps))))
                            (car (car steps)))))
       (fn-tcl-host-fold (fn-tcl-result-session r)
                         (fn-tcl-result-unconsumed r)
                         (cdr steps)
                         (append acc (fn-tcl-result-events r)))))
   :exec
   (if (not (consp steps))
       (list s acc carry)
     (let ((r (ec-call (fn-tcl-drive s (fn-ag-append carry (fn-ag-car (fn-ag-cdr (fn-ag-car steps))))
                                     (fn-ag-car (fn-ag-car steps))))))
       (fn-tcl-host-fold (ec-call (fn-tcl-result-session r))
                         (ec-call (fn-tcl-result-unconsumed r))
                         (cdr steps)
                         (fn-ag-append acc (ec-call (fn-tcl-result-events r))))))))

(verify-guards fn-tcl-host-fold
  :hints (("Goal" :in-theory (disable fn-tcl-drive))))

(defun fn-tcl-host-replay (role local now steps)
  (let ((s (fn-tcl-host-initial role local now)))
    (if (null s)
        nil
      (let ((out (fn-tcl-host-fold s nil steps nil)))
        (list (fn-tcl-session-phase (car out))
              (fn-tcl-host-event-digests (car (cdr out)))
              (len (car (cdr (cdr out)))))))))
