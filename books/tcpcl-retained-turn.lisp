; Scheduling of retained TCPCL work, independent of protocol decisions.
; A quantum bounds one physical attempt; it is not a stored-data limit.
(in-package "ACL2")
(defun fn-tcrt-read-limit () (declare (xargs :guard t)) 4096)
(defun fn-tcrt-write-end (offset total)
 (declare (xargs :guard t))
 (min (nfix total) (+ (nfix offset) (fn-tcrt-read-limit))))
(defun fn-tcrt-write-deadline (now)
 (declare (xargs :guard t)) (+ (nfix now) 30000))
(defun fn-tcrt-action (source-pending source-more writep messagesp input-due pump closing phase now deadline)
 (declare (xargs :guard t))
 (cond
  (writep (if (and (natp deadline) (<= deadline (nfix now))) :lost :write))
  (messagesp :encode)
  (closing :done)
  ((equal phase :closed) :done)
  (source-pending :source)
  (source-more :buffer)
  (input-due :read)
  (pump :pump)
  (t :local)))
(defthm fn-tcrt-write-range-is-bounded
 (implies (and (natp offset) (integerp total) (<= offset total))
  (and (<= offset (fn-tcrt-write-end offset total))
       (<= (fn-tcrt-write-end offset total) total)
       (<= (- (fn-tcrt-write-end offset total) offset) (fn-tcrt-read-limit)))))
(defthm fn-tcrt-source-custody-excludes-input
 (implies (and source-pending (not writep) (not messagesp)
               (not closing) (not (equal phase :closed)))
  (equal (fn-tcrt-action source-pending source-more writep messagesp input-due pump closing phase now deadline) :source)))
(defthm fn-tcrt-ready-write-precedes-source-and-close
 (implies (and writep (not (and (natp deadline) (<= deadline (nfix now)))))
  (equal (fn-tcrt-action source-pending source-more writep messagesp input-due pump closing phase now deadline) :write)))

; RFC9174 section4.1: close a TCP connection whose peer Contact Header never
; completes. Sixty seconds is fn's reception policy (RFC SHOULD <=60s), not a
; bound on an established session, transfer, stored source or publication.
(defun fn-tcrt-contact-deadline (now)
 (declare (xargs :guard t)) (+ (nfix now) 60000))
(defun fn-tcrt-contact-timeout-p (phase now deadline buffered)
 (declare (xargs :guard t))
 (and (not buffered) (member-eq phase '(:tcp-connected :contact))
      (natp now) (natp deadline) (<= deadline now) t))
(defthm fn-tcrt-contact-timeout-only-before-header-by-definition
 (implies (fn-tcrt-contact-timeout-p phase now deadline buffered)
  (and (not buffered) (member-eq phase '(:tcp-connected :contact))
       (natp now) (natp deadline) (<= deadline now)))
 :rule-classes nil)
(defthm fn-tcrt-established-contact-is-never-expired-by-definition
 (not (fn-tcrt-contact-timeout-p :established now deadline buffered))
 :rule-classes nil)

; Local session setup policy. RFC9174 section4.6 precedes ready-to-transfer;
; section5.1.1's negotiated idle interval does not yet exist in :messaging.
; Capture this deadline once on entering messaging; partial input never renews.
(defun fn-tcrt-init-deadline (phase now prior)
 (declare (xargs :guard t))
 (and (equal phase :messaging)
      (if (natp prior) prior (+ (nfix now) 60000))))
(defun fn-tcrt-init-timeout-p (phase now deadline buffered)
 (declare (xargs :guard t))
 (and (not buffered) (equal phase :messaging)
      (natp now) (natp deadline) (<= deadline now) t))
(defthm fn-tcrt-init-deadline-does-not-renew
 (implies (and (equal phase :messaging) (natp prior))
  (equal (fn-tcrt-init-deadline phase now prior) prior)))
(defthm fn-tcrt-init-timeout-excludes-established
 (implies (fn-tcrt-init-timeout-p phase now deadline buffered)
  (equal phase :messaging))
 :rule-classes nil)

; S025 (coordinator ruling 2026-10-04, planning/design/bp-2026-10-04.md 2.6):
; the no-progress bounds of an ESTABLISHED session.  Progress is transfer
; advancement in either direction: a whole XFER_SEGMENT or XFER_ACK frame
; received, or written to the socket (RFC 9174 5.2.4, 5.2.5; message type
; octets 1 and 2).  An ACK merely queued does not count (the host notes only
; frames whose last octet was written), and neither do KEEPALIVE, SESS_TERM,
; XFER_REFUSE, MSG_REJECT or SESS_INIT.  The bounds are admission policy:
; fairness among inbound peers is not bounded, and a peer that advances one
; frame per window keeps its slot.
;   passive-ms  bounded only under contention (the incoming class is full and
;               another peer is waiting): SESS_TERM reason 5, Resource Exhaustion.
;   stall-ms    bounded always, for a session with a transfer in flight:
;               SESS_TERM reason 1, Idle timeout.
; The host acts only at the :local arm of fn-tcrt-action, so the SESS_TERM
; is queued behind complete messages and never inside an unfinished one.
(defun fn-tcrt-progress-frame-p (type)
 (declare (xargs :guard t))
 (and (member-equal type '(1 2)) t))
; Captured once on entering :established; the prior value is never renewed here.
(defun fn-tcrt-progress-clock (phase now prior)
 (declare (xargs :guard t))
 (and (equal phase :established)
      (if (natp prior) prior (nfix now))))
(defun fn-tcrt-note-frame (type now prior)
 (declare (xargs :guard t))
 (if (and (natp prior) (natp now) (<= prior now) (fn-tcrt-progress-frame-p type))
     now
   prior))
(defun fn-tcrt-passive-timeout-p (phase now progress-at passive-ms contended)
 (declare (xargs :guard t))
 (and contended (equal phase :established)
      (natp now) (natp progress-at) (posp passive-ms)
      (<= (+ progress-at passive-ms) now) t))
(defun fn-tcrt-stall-timeout-p (phase now progress-at stall-ms in-transfer)
 (declare (xargs :guard t))
 (and in-transfer (equal phase :established)
      (natp now) (natp progress-at) (posp stall-ms)
      (<= (+ progress-at stall-ms) now) t))
(defun fn-tcrt-expiry-reason (phase now progress-at passive-ms stall-ms in-transfer contended)
 (declare (xargs :guard t))
 (cond ((fn-tcrt-passive-timeout-p phase now progress-at passive-ms contended)
        5)  ; Resource Exhaustion
       ((fn-tcrt-stall-timeout-p phase now progress-at stall-ms in-transfer)
        1)  ; Idle timeout
       (t nil)))
; The one decision the host obeys: the SESS_TERM reason, or nil.  Only the
; :local action may end a session this way.
(defun fn-tcrt-expiry (action phase now progress-at passive-ms stall-ms in-transfer contended)
 (declare (xargs :guard t))
 (and (equal action :local)
      (fn-tcrt-expiry-reason phase now progress-at passive-ms stall-ms in-transfer contended)))

(defthm fn-tcrt-passive-timeout-only-under-contention-by-definition
 (implies (fn-tcrt-passive-timeout-p phase now progress-at passive-ms contended)
  (and contended (equal phase :established)
       (natp now) (natp progress-at) (posp passive-ms)
       (<= (+ progress-at passive-ms) now)))
 :rule-classes nil)
(defthm fn-tcrt-quiet-node-never-passive-timeout
 (not (fn-tcrt-passive-timeout-p phase now progress-at passive-ms nil)))
(defthm fn-tcrt-stall-timeout-needs-a-transfer-by-definition
 (implies (fn-tcrt-stall-timeout-p phase now progress-at stall-ms in-transfer)
  (and in-transfer (equal phase :established)
       (natp now) (natp progress-at) (posp stall-ms)
       (<= (+ progress-at stall-ms) now)))
 :rule-classes nil)
(defthm fn-tcrt-idle-session-never-stall-timeout
 (not (fn-tcrt-stall-timeout-p phase now progress-at stall-ms nil)))
(defthm fn-tcrt-no-expiry-before-established
 (implies (not (equal phase :established))
  (not (fn-tcrt-expiry-reason phase now progress-at passive-ms stall-ms in-transfer contended))))
(defthm fn-tcrt-progress-clock-does-not-renew
 (implies (natp prior)
  (equal (fn-tcrt-progress-clock :established now prior) prior)))
(defthm fn-tcrt-only-transfer-frames-renew-progress
 (implies (not (fn-tcrt-progress-frame-p type))
  (equal (fn-tcrt-note-frame type now prior) prior)))
(defthm fn-tcrt-transfer-frame-renews-progress
 (implies (and (fn-tcrt-progress-frame-p type) (natp prior) (natp now) (<= prior now)
               (posp passive-ms) (posp stall-ms))
  (and (not (fn-tcrt-passive-timeout-p :established now (fn-tcrt-note-frame type now prior)
                                        passive-ms t))
       (not (fn-tcrt-stall-timeout-p :established now (fn-tcrt-note-frame type now prior)
                                      stall-ms t)))))
(defthm fn-tcrt-contention-is-reason-five-by-definition
 (implies (fn-tcrt-passive-timeout-p phase now progress-at passive-ms t)
  (equal (fn-tcrt-expiry-reason phase now progress-at passive-ms stall-ms in-transfer t) 5))
 :rule-classes nil)
(defthm fn-tcrt-stall-bound-ignores-contention
 (implies (fn-tcrt-stall-timeout-p phase now progress-at stall-ms in-transfer)
  (and (fn-tcrt-expiry-reason phase now progress-at passive-ms stall-ms in-transfer nil)
       (fn-tcrt-expiry-reason phase now progress-at passive-ms stall-ms in-transfer t)))
 :rule-classes nil)
(defthm fn-tcrt-expiry-reason-is-idle-or-resource-exhaustion
 (implies (fn-tcrt-expiry-reason phase now progress-at passive-ms stall-ms in-transfer contended)
  (member-equal (fn-tcrt-expiry-reason phase now progress-at passive-ms stall-ms in-transfer contended)
                '(1 5)))
 :rule-classes nil)
; The same bounds stated over the decision the host calls, fn-tcrt-expiry.
(defthm fn-tcrt-expiry-resource-exhaustion-only-under-contention
 (implies (equal (fn-tcrt-expiry action phase now progress-at passive-ms stall-ms in-transfer contended) 5)
  contended)
 :rule-classes nil)
(defthm fn-tcrt-quiet-idle-session-is-never-expired
 (not (fn-tcrt-expiry action phase now progress-at passive-ms stall-ms nil nil)))
(defthm fn-tcrt-stall-expiry-needs-a-transfer
 (implies (equal (fn-tcrt-expiry action phase now progress-at passive-ms stall-ms in-transfer contended) 1)
  in-transfer)
 :rule-classes nil)
(defthm fn-tcrt-no-expiry-before-established-session
 (implies (not (equal phase :established))
  (not (fn-tcrt-expiry action phase now progress-at passive-ms stall-ms in-transfer contended))))
(defthm fn-tcrt-expiry-is-idle-or-resource-exhaustion
 (implies (fn-tcrt-expiry action phase now progress-at passive-ms stall-ms in-transfer contended)
  (member-equal (fn-tcrt-expiry action phase now progress-at passive-ms stall-ms in-transfer contended)
                '(1 5)))
 :rule-classes nil)
; The session is never ended inside an unfinished message or over held custody.
(defthm fn-tcrt-expiry-only-at-a-message-boundary
 (implies (fn-tcrt-expiry (fn-tcrt-action source-pending source-more writep messagesp input-due pump closing phase now1 deadline)
                          phase now progress-at passive-ms stall-ms in-transfer contended)
  (and (not writep) (not messagesp) (not source-pending) (not closing)))
 :rule-classes nil)
