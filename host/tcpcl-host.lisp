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
(include-book "../books/tcpcl-delivery")
(include-book "../books/tcpcl-spool")

; Directory names and lstat kinds in; a complete recovery plan out.  The raw
; host validates the whole plan before unlinking anything, then performs only
; the :remove actions selected here.
(defun fn-tcl-host-spool-recovery-plan (entries)
  (fn-tcl-spool-recovery-plan entries))

(defun fn-tcl-host-triple (r)
  (list (fn-tcl-result-session r)
        (fn-tcl-result-events r)
        (fn-tcl-result-unconsumed r)))

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

(defun fn-tcl-host-drive (s buf now)
  (fn-tcl-host-triple (fn-tcl-drive s buf now)))

; The host has a monotonic millisecond reading and no trusted wall clock; the
; observation is built here so that its shape is the books' and not the host's.
(defun fn-tcl-host-tick (s monotonic)
  (fn-tcl-host-triple (fn-tcl-tick s (fn-clock-observation monotonic 0 0 nil))))

(defun fn-tcl-host-send (s ref octets now)
  (fn-tcl-host-triple (fn-tcl-send s ref octets now)))

(defun fn-tcl-host-pump (s now)
  (fn-tcl-host-triple (fn-tcl-pump s now)))

(defun fn-tcl-host-tcp-closed (s)
  (fn-tcl-host-triple (fn-tcl-tcp-closed s)))

; A shutdown the operator asked for is not one of the RFC's named causes, so
; it carries Unknown (RFC 9174 section 6.1).  The code is the book's constant.
(defun fn-tcl-host-terminate (s now)
  (fn-tcl-host-triple (fn-tcl-terminate s *fn-tcl-term-unknown* now)))

; -----------------------------------------------------------------------------
; Reading a result out.  The host asks; it does not compute.

(defun fn-tcl-host-encode (m)
  (fn-tcl-encode m))

(defun fn-tcl-host-kind (m)
  (fn-tcl-msg-kind m))

(defun fn-tcl-host-phase (s)
  (fn-tcl-session-phase s))

; The negotiated keepalive in seconds, 0 before SESS_INIT and when the peer
; asked for none.  The host divides it to choose a read timeout; the interval
; itself is the machine's.
(defun fn-tcl-host-keepalive (s)
  (let ((n (fn-tcl-session-negotiated s)))
    (if n (fn-tcl-negotiated-keepalive n) 0)))

(defun fn-tcl-host-transfer-mtu (s)
  (let ((n (fn-tcl-session-negotiated s)))
    (if n (fn-tcl-negotiated-transfer-mtu n) 0)))

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

(defun fn-tcl-host-event-digests (events)
  (if (consp events)
      (cons (fn-tcl-host-event-digest (car events))
            (fn-tcl-host-event-digests (cdr events)))
    nil))

; -----------------------------------------------------------------------------
; The differential's model side.  STEPS is the trace the session loop wrote:
; one (now octets) pair per socket read, in order, with the octets exactly as
; they arrived.  Folding fn-tcl-drive over it with the carry reproduces the
; loop's whole event stream in one call, with no socket and no host in the way;
; tools/tcpcl_lab.py compares the two digests.

(defun fn-tcl-host-fold (s carry steps acc)
  (declare (xargs :measure (len steps)))
  (if (not (consp steps))
      (list s acc carry)
    (let ((r (fn-tcl-drive s (append carry (car (cdr (car steps))))
                           (car (car steps)))))
      (fn-tcl-host-fold (fn-tcl-result-session r)
                        (fn-tcl-result-unconsumed r)
                        (cdr steps)
                        (append acc (fn-tcl-result-events r))))))

(defun fn-tcl-host-replay (role local now steps)
  (let ((s (fn-tcl-host-initial role local now)))
    (if (null s)
        nil
      (let ((out (fn-tcl-host-fold s nil steps nil)))
        (list (fn-tcl-session-phase (car out))
              (fn-tcl-host-event-digests (car (cdr out)))
              (len (car (cdr (cdr out)))))))))
