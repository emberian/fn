; fn TCPCLv4 session machine (RFC 9174 section 3.3): contact exchange,
; SESS_INIT negotiation, one inbound and one outbound transfer with
; cumulative acknowledgement, refusal with Table 6 reasons, keepalive and idle
; timeout as clock observations, the SESS_TERM handshake, MSG_REJECT.
;
; The served path is fn-tcl-drive: the native host prepends its carry to a
; socket chunk and calls it (specs/tcpcl.md section 4).  Every other entry
; point is one event from the host: fn-tcl-open, fn-tcl-send, fn-tcl-pump,
; fn-tcl-tick, fn-tcl-terminate, fn-tcl-tcp-closed.  Each is total in the
; logic and returns (fn-tcl-make-result session events unconsumed).
;
; State is the opaque session record of tcpcl-records.  fn-tcl-sessionp is a
; carried invariant: it guards every entry point, is proved preserved by
; every transition (the keystones at the end of this book), and is never
; re-run per octet.  The inbound record carries the sum of its staged segment
; lengths and the recognizer requires that sum to be the measurement of the
; staged list, so the retained-input bound (transfer MRU) is a carried
; scalar, as in books/wire.lisp.
;
; Local policy, stated where it departs from or narrows the RFC: one
; outbound transfer at a time (transfer pipelining is a MAY, section 3.3;
; segment pipelining is what fn-tcl-pump gives); TLS is never negotiated
; up (CAN_TLS = 0 is sent and a negotiated Enable TLS of true is refused
; Contact Failure, section 4.3); no session extension types are known, so a
; CRITICAL one fails the session (section 4.8); a peer that announces a
; node ID other than the contact plan's configured peer is refused Contact
; Failure (section 4.6, unauthenticated node IDs drive nothing); a decode
; error after the contact exchange is answered with MSG_REJECT and a close,
; because TCPCL messages are not self-delimiting (section 8.5).

(in-package "ACL2")
(include-book "tcpcl-octets")
(include-book "clock")
; clock withdraws fn-clock-observationp under fn-clock-vocabulary and keeps
; its accessors opaque; fn-tcl-tick reads fn-clock-monotonic under that
; recognizer, so this book opens it locally (docs/proof-style.md section 2).
(local (in-theory (enable fn-clock-observationp)))

(local (in-theory (enable fn-tcl-has-is-len-bound)))

; Table 6 XFER_REFUSE reasons.
(defconst *fn-tcl-refuse-unknown* 0)
(defconst *fn-tcl-refuse-completed* 1)
(defconst *fn-tcl-refuse-no-resources* 2)
(defconst *fn-tcl-refuse-retransmit* 3)
(defconst *fn-tcl-refuse-not-acceptable* 4)
(defconst *fn-tcl-refuse-extension-failure* 5)
(defconst *fn-tcl-refuse-session-terminating* 6)
; Table 9 SESS_TERM reasons.
(defconst *fn-tcl-term-unknown* 0)
(defconst *fn-tcl-term-idle-timeout* 1)
(defconst *fn-tcl-term-version-mismatch* 2)
(defconst *fn-tcl-term-busy* 3)
(defconst *fn-tcl-term-contact-failure* 4)
(defconst *fn-tcl-term-resource-exhaustion* 5)
; Table 4 MSG_REJECT reasons.
(defconst *fn-tcl-reject-type-unknown* 1)
(defconst *fn-tcl-reject-unsupported* 2)
(defconst *fn-tcl-reject-unexpected* 3)
; Transfer Length Extension type (Table 13).
(defconst *fn-tcl-ext-transfer-length* 1)

; -----------------------------------------------------------------------------
; List vocabulary for the staged inbound segments (newest first).

(defun fn-tcl-octet-listsp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (fn-cbor-octet-listp (car x)) (fn-tcl-octet-listsp (cdr x)))
    (null x)))

(defun fn-tcl-lists-len (x)
  (declare (xargs :guard (fn-tcl-octet-listsp x)))
  (if (consp x)
      (+ (len (car x)) (fn-tcl-lists-len (cdr x)))
    0))

; The staged segments in arrival order, as one octet list.  Each segment is
; copied once, so completing a transfer costs its length.
(defun fn-tcl-concat-rev (x acc)
  (declare (xargs :guard (and (fn-tcl-octet-listsp x) (true-listp acc))))
  (if (consp x)
      (fn-tcl-concat-rev (cdr x) (append (car x) acc))
    acc))

(defthm fn-tcl-len-concat-rev
  (equal (len (fn-tcl-concat-rev x acc))
         (+ (fn-tcl-lists-len x) (len acc))))

(defthm fn-tcl-concat-rev-octet-listp
  (implies (and (fn-tcl-octet-listsp x) (fn-cbor-octet-listp acc))
           (fn-cbor-octet-listp (fn-tcl-concat-rev x acc))))

; append with a total guard: the same function in the logic, so every
; theorem below speaks of append.
(defun fn-tcl-app (a b)
  (declare (xargs :guard t))
  (if (consp a) (cons (car a) (fn-tcl-app (cdr a) b)) b))

(defthm fn-tcl-app-is-append
  (equal (fn-tcl-app a b) (append a b)))

; -----------------------------------------------------------------------------
; Recognizers.

(defun fn-tcl-paramsp (p)
  (declare (xargs :guard t))
  (and (fn-tcl-params-shapep p)
       (natp (fn-tcl-params-keepalive p))
       (<= (fn-tcl-params-keepalive p) *fn-tcl-max-u16*)
       (natp (fn-tcl-params-segment-mru p))
       (<= (fn-tcl-params-segment-mru p) *fn-tcl-max-u64*)
       (natp (fn-tcl-params-transfer-mru p))
       (<= (fn-tcl-params-transfer-mru p) *fn-tcl-max-u64*)
       (fn-cbor-octet-listp (fn-tcl-params-node-id p))
       (<= (len (fn-tcl-params-node-id p)) *fn-tcl-node-id-cap*)
       (booleanp (fn-tcl-params-can-tls p))
       (or (null (fn-tcl-params-expected-peer p))
           (fn-cbor-octet-listp (fn-tcl-params-expected-peer p)))))

; The peer's SESS_INIT as decoded; what fn-tcl-messagep says of a :sess-init.
(defun fn-tcl-peer-initp (m)
  (declare (xargs :guard t))
  (and (fn-tcl-sess-init-shapep m)
       (natp (fn-tcl-sess-init-keepalive m))
       (<= (fn-tcl-sess-init-keepalive m) *fn-tcl-max-u16*)
       (natp (fn-tcl-sess-init-segment-mru m))
       (<= (fn-tcl-sess-init-segment-mru m) *fn-tcl-max-u64*)
       (natp (fn-tcl-sess-init-transfer-mru m))
       (<= (fn-tcl-sess-init-transfer-mru m) *fn-tcl-max-u64*)
       (fn-cbor-octet-listp (fn-tcl-sess-init-node-id m))
       (fn-tcl-item-listp (fn-tcl-sess-init-ext m))))

(defthm fn-tcl-messagep-sess-init-is-peer-initp
  (implies (and (fn-tcl-messagep m mru)
                (equal (fn-tcl-msg-kind m) :sess-init))
           (fn-tcl-peer-initp m))
  :hints (("Goal" :in-theory (enable fn-tcl-messagep))))

(defun fn-tcl-negotiatedp (n)
  (declare (xargs :guard t))
  (and (fn-tcl-negotiated-shapep n)
       (natp (fn-tcl-negotiated-keepalive n))
       (<= (fn-tcl-negotiated-keepalive n) *fn-tcl-max-u16*)
       (posp (fn-tcl-negotiated-segment-mtu n))
       (<= (fn-tcl-negotiated-segment-mtu n) *fn-tcl-max-u64*)
       (posp (fn-tcl-negotiated-transfer-mtu n))
       (<= (fn-tcl-negotiated-transfer-mtu n) *fn-tcl-max-u64*)
       (booleanp (fn-tcl-negotiated-tls n))
       (fn-cbor-octet-listp (fn-tcl-negotiated-peer-node-id n))))

(defun fn-tcl-inboundp (i limit)
  (declare (xargs :guard (natp limit)))
  (and (fn-tcl-inbound-shapep i)
       (natp (fn-tcl-inbound-xfer-id i))
       (<= (fn-tcl-inbound-xfer-id i) *fn-tcl-max-u64*)
       (fn-tcl-octet-listsp (fn-tcl-inbound-staged i))
       (natp (fn-tcl-inbound-received-len i))
       (equal (fn-tcl-inbound-received-len i)
              (fn-tcl-lists-len (fn-tcl-inbound-staged i)))
       (<= (fn-tcl-inbound-received-len i) limit)
       (or (null (fn-tcl-inbound-total i))
           (and (natp (fn-tcl-inbound-total i))
                (<= (fn-tcl-inbound-total i) *fn-tcl-max-u64*)
                (<= (fn-tcl-inbound-received-len i) (fn-tcl-inbound-total i))))))

(defun fn-tcl-outboundp (o)
  (declare (xargs :guard t))
  (and (fn-tcl-outbound-shapep o)
       (natp (fn-tcl-outbound-xfer-id o))
       (<= (fn-tcl-outbound-xfer-id o) *fn-tcl-max-u64*)
       (fn-cbor-octet-listp (fn-tcl-outbound-remaining o))
       (natp (fn-tcl-outbound-total o))
       (<= (fn-tcl-outbound-total o) *fn-tcl-max-u64*)
       (natp (fn-tcl-outbound-sent-len o))
       (equal (+ (fn-tcl-outbound-sent-len o) (len (fn-tcl-outbound-remaining o)))
              (fn-tcl-outbound-total o))
       (natp (fn-tcl-outbound-acked-len o))
       (<= (fn-tcl-outbound-acked-len o) (fn-tcl-outbound-sent-len o))))

(defun fn-tcl-rolep (r)
  (declare (xargs :guard t))
  (or (equal r :active) (equal r :passive)))

(defun fn-tcl-phasep (p)
  (declare (xargs :guard t))
  (or (equal p :tcp-connected) (equal p :contact) (equal p :messaging)
      (equal p :established) (equal p :ending) (equal p :closed)))

(defun fn-tcl-pre-establishedp (p)
  (declare (xargs :guard t))
  (or (equal p :tcp-connected) (equal p :contact) (equal p :messaging)))

(defun fn-tcl-transferringp (p)
  (declare (xargs :guard t))
  (or (equal p :established) (equal p :ending)))

(defun fn-tcl-termp (x)
  (declare (xargs :guard t))
  (or (null x) (equal x :sent) (equal x :both)))

(defun fn-tcl-sessionp (s)
  (declare (xargs :guard t))
  (and (fn-tcl-session-shapep s)
       (fn-tcl-rolep (fn-tcl-session-role s))
       (fn-tcl-phasep (fn-tcl-session-phase s))
       (fn-tcl-paramsp (fn-tcl-session-local s))
       (booleanp (fn-tcl-session-tls s))
       (or (null (fn-tcl-session-peer s))
           (fn-tcl-peer-initp (fn-tcl-session-peer s)))
       (or (null (fn-tcl-session-negotiated s))
           (fn-tcl-negotiatedp (fn-tcl-session-negotiated s)))
       (or (null (fn-tcl-session-inbound s))
           (fn-tcl-inboundp (fn-tcl-session-inbound s)
                            (fn-tcl-params-transfer-mru (fn-tcl-session-local s))))
       (or (null (fn-tcl-session-outbound s))
           (fn-tcl-outboundp (fn-tcl-session-outbound s)))
       (natp (fn-tcl-session-next-xfer-id s))
       (fn-clock-timep (fn-tcl-session-last-rx s))
       (fn-clock-timep (fn-tcl-session-last-tx s))
       (fn-tcl-termp (fn-tcl-session-term s))
       ; phase consistency
       (implies (fn-tcl-pre-establishedp (fn-tcl-session-phase s))
                (and (null (fn-tcl-session-negotiated s))
                     (null (fn-tcl-session-term s))))
       (implies (equal (fn-tcl-session-phase s) :established)
                (and (fn-tcl-session-negotiated s)
                     (null (fn-tcl-session-term s))))
       (implies (equal (fn-tcl-session-phase s) :ending)
                (fn-tcl-session-term s))
       (implies (not (fn-tcl-transferringp (fn-tcl-session-phase s)))
                (and (null (fn-tcl-session-inbound s))
                     (null (fn-tcl-session-outbound s))))
       (implies (null (fn-tcl-session-negotiated s))
                (and (null (fn-tcl-session-inbound s))
                     (null (fn-tcl-session-outbound s))))))

(defun fn-tcl-initial-session (role local now)
  (declare (xargs :guard t))
  (fn-tcl-make-session role :tcp-connected local nil nil nil nil nil 0 now now nil))

(defthm fn-tcl-initial-session-is-session
  (implies (and (fn-tcl-rolep role) (fn-tcl-paramsp local) (fn-clock-timep now))
           (fn-tcl-sessionp (fn-tcl-initial-session role local now))))

; The one-call rebuild every transition uses: the fields a transition may
; change, the rest carried from s.
(defun fn-tcl-next (s phase inbound outbound term last-tx)
  (declare (xargs :guard t))
  (fn-tcl-make-session (fn-tcl-session-role s) phase (fn-tcl-session-local s)
                       (fn-tcl-session-tls s) (fn-tcl-session-peer s)
                       (fn-tcl-session-negotiated s) inbound outbound
                       (fn-tcl-session-next-xfer-id s) (fn-tcl-session-last-rx s)
                       last-tx term))

(defun fn-tcl-touch-rx (s now)
  (declare (xargs :guard t))
  (fn-tcl-make-session (fn-tcl-session-role s) (fn-tcl-session-phase s)
                       (fn-tcl-session-local s) (fn-tcl-session-tls s)
                       (fn-tcl-session-peer s) (fn-tcl-session-negotiated s)
                       (fn-tcl-session-inbound s) (fn-tcl-session-outbound s)
                       (fn-tcl-session-next-xfer-id s) now
                       (fn-tcl-session-last-tx s) (fn-tcl-session-term s)))

(defun fn-tcl-transfer-mru (s)
  (declare (xargs :guard t))
  (fn-tcl-params-transfer-mru (fn-tcl-session-local s)))

(defun fn-tcl-segment-mru (s)
  (declare (xargs :guard t))
  (fn-tcl-params-segment-mru (fn-tcl-session-local s)))

; Events named once.
(defun fn-tcl-send-event (m)
  (declare (xargs :guard t))
  (list :send m))

; The outcome events of the live transfers, for a close.
(defun fn-tcl-fail-live (s)
  (declare (xargs :guard t))
  (append (if (fn-tcl-session-inbound s)
              (list (list :inbound-failed
                          (fn-tcl-inbound-xfer-id (fn-tcl-session-inbound s))))
            nil)
          (if (fn-tcl-session-outbound s)
              (list (list :outbound-failed
                          (fn-tcl-outbound-xfer-id (fn-tcl-session-outbound s))
                          (fn-tcl-outbound-ref (fn-tcl-session-outbound s))))
            nil)))

; A session in Ending whose SESS_TERM handshake is complete and whose
; transfers are done closes (section 6.1: "Transfers Done").
(defun fn-tcl-settle (r)
  (declare (xargs :guard t))
  (let ((s (fn-tcl-result-session r)))
    (if (and (equal (fn-tcl-session-phase s) :ending)
             (equal (fn-tcl-session-term s) :both)
             (null (fn-tcl-session-inbound s))
             (null (fn-tcl-session-outbound s)))
        (fn-tcl-make-result (fn-tcl-next s :closed nil nil :both (fn-tcl-session-last-tx s))
                            (fn-tcl-app (fn-tcl-result-events r) (list (list :close)))
                            nil)
      r)))

; -----------------------------------------------------------------------------
; Contact exchange (sections 4.1 to 4.3).

(defun fn-tcl-own-contact (s)
  (declare (xargs :guard t))
  (fn-tcl-make-contact 4 (if (fn-tcl-params-can-tls (fn-tcl-session-local s)) 1 0)))

(defun fn-tcl-own-init (s)
  (declare (xargs :guard t))
  (fn-tcl-make-sess-init (fn-tcl-params-keepalive (fn-tcl-session-local s))
                         (fn-tcl-params-segment-mru (fn-tcl-session-local s))
                         (fn-tcl-params-transfer-mru (fn-tcl-session-local s))
                         (fn-tcl-params-node-id (fn-tcl-session-local s))
                         nil))

; The active entity sends its Contact Header immediately (section 4.1).
(defun fn-tcl-open (s now)
  (declare (xargs :guard t))
  (if (and (equal (fn-tcl-session-role s) :active)
           (equal (fn-tcl-session-phase s) :tcp-connected))
      (fn-tcl-make-result (fn-tcl-next s :contact nil nil nil now)
                          (list (fn-tcl-send-event (fn-tcl-own-contact s)))
                          nil)
    (fn-tcl-make-result s nil nil)))

(defun fn-tcl-recv-contact (s m now)
  (declare (xargs :guard (and (fn-tcl-contact-shapep m)
                              (fn-cbor-octetp (fn-tcl-contact-flags m)))))
  (let* ((version (fn-tcl-contact-version m))
         (tls (and (fn-tcl-params-can-tls (fn-tcl-session-local s))
                   (fn-tcl-flag-can-tls (fn-tcl-contact-flags m))
                   t))
         (own (if (equal (fn-tcl-session-phase s) :tcp-connected)
                  (list (fn-tcl-send-event (fn-tcl-own-contact s)))
                nil)))
    (cond ((not (equal version 4))
           (if (equal (fn-tcl-session-role s) :passive)
               ; section 4.3: send own header, then Version mismatch
               (fn-tcl-make-result
                (fn-tcl-make-session :passive :ending (fn-tcl-session-local s) tls nil nil
                                     nil nil (fn-tcl-session-next-xfer-id s)
                                     (fn-tcl-session-last-rx s) now :sent)
                (append own (list (fn-tcl-send-event
                                   (fn-tcl-make-sess-term 0 *fn-tcl-term-version-mismatch*))))
                nil)
             ; the active entity closes (section 4.3)
             (fn-tcl-make-result
              (fn-tcl-make-session :active :closed (fn-tcl-session-local s) tls nil nil
                                   nil nil (fn-tcl-session-next-xfer-id s)
                                   (fn-tcl-session-last-rx s) (fn-tcl-session-last-tx s) nil)
              (list (list :close))
              nil)))
          (tls
           ; Enable TLS negotiated true is unacceptable in wave 4: Contact Failure
           (fn-tcl-make-result
            (fn-tcl-make-session (fn-tcl-session-role s) :ending (fn-tcl-session-local s) tls
                                 nil nil nil nil (fn-tcl-session-next-xfer-id s)
                                 (fn-tcl-session-last-rx s) now :sent)
            (append own (list (fn-tcl-send-event
                               (fn-tcl-make-sess-term 0 *fn-tcl-term-contact-failure*))))
            nil))
          ((equal (fn-tcl-session-role s) :passive)
           (fn-tcl-make-result
            (fn-tcl-make-session :passive :messaging (fn-tcl-session-local s) tls nil nil
                                 nil nil (fn-tcl-session-next-xfer-id s)
                                 (fn-tcl-session-last-rx s)
                                 (if own now (fn-tcl-session-last-tx s)) nil)
            own
            nil))
          (t
           ; active: messaging is available, send SESS_INIT (section 4.4.3)
           (fn-tcl-make-result
            (fn-tcl-make-session :active :messaging (fn-tcl-session-local s) tls nil nil
                                 nil nil (fn-tcl-session-next-xfer-id s)
                                 (fn-tcl-session-last-rx s) now nil)
            (append own (list (fn-tcl-send-event (fn-tcl-own-init s))))
            nil)))))

; -----------------------------------------------------------------------------
; Session negotiation (sections 4.6 to 4.8).

(defun fn-tcl-no-critical-items (items)
  (declare (xargs :guard (fn-tcl-item-listp items)))
  (if (consp items)
      (and (not (fn-tcl-flag-critical (fn-tcl-item-flags (car items))))
           (fn-tcl-no-critical-items (cdr items)))
    t))

(defun fn-tcl-negotiate (local tls m)
  (declare (xargs :guard (and (fn-tcl-paramsp local) (fn-tcl-peer-initp m))))
  (fn-tcl-make-negotiated (min (fn-tcl-params-keepalive local)
                               (fn-tcl-sess-init-keepalive m))
                          (fn-tcl-sess-init-segment-mru m)
                          (fn-tcl-sess-init-transfer-mru m)
                          (if tls t nil)
                          (fn-tcl-sess-init-node-id m)))

(defun fn-tcl-init-acceptablep (local m)
  (declare (xargs :guard (and (fn-tcl-paramsp local) (fn-tcl-peer-initp m))))
  (and (posp (fn-tcl-sess-init-segment-mru m))
       (posp (fn-tcl-sess-init-transfer-mru m))
       (or (null (fn-tcl-params-expected-peer local))
           (equal (fn-tcl-params-expected-peer local) (fn-tcl-sess-init-node-id m)))
       (fn-tcl-no-critical-items (fn-tcl-sess-init-ext m))))

(defun fn-tcl-recv-init (s m now)
  (declare (xargs :guard (and (fn-tcl-paramsp (fn-tcl-session-local s))
                              (fn-tcl-peer-initp m))))
  (let ((own (if (equal (fn-tcl-session-role s) :passive)
                 (list (fn-tcl-send-event (fn-tcl-own-init s)))
               nil)))
    (if (fn-tcl-init-acceptablep (fn-tcl-session-local s) m)
        (let ((n (fn-tcl-negotiate (fn-tcl-session-local s) (fn-tcl-session-tls s) m)))
          (fn-tcl-make-result
           (fn-tcl-make-session (fn-tcl-session-role s) :established (fn-tcl-session-local s)
                                (fn-tcl-session-tls s) m n nil nil
                                (fn-tcl-session-next-xfer-id s) (fn-tcl-session-last-rx s)
                                (if own now (fn-tcl-session-last-tx s)) nil)
           (append own (list (list :session-up n)))
           nil))
      (fn-tcl-make-result
       (fn-tcl-make-session (fn-tcl-session-role s) :ending (fn-tcl-session-local s)
                            (fn-tcl-session-tls s) m nil nil nil
                            (fn-tcl-session-next-xfer-id s) (fn-tcl-session-last-rx s)
                            now :sent)
       (append own (list (fn-tcl-send-event
                          (fn-tcl-make-sess-term 0 *fn-tcl-term-contact-failure*))))
       nil))))

; -----------------------------------------------------------------------------
; Inbound transfer (sections 5.2.2 to 5.2.5).

(defun fn-tcl-count-tle (items)
  (declare (xargs :guard (fn-tcl-item-listp items)))
  (if (consp items)
      (+ (if (equal (fn-tcl-item-type (car items)) *fn-tcl-ext-transfer-length*) 1 0)
         (fn-tcl-count-tle (cdr items)))
    0))

(defun fn-tcl-find-tle (items)
  (declare (xargs :guard (fn-tcl-item-listp items)))
  (if (consp items)
      (if (equal (fn-tcl-item-type (car items)) *fn-tcl-ext-transfer-length*)
          (car items)
        (fn-tcl-find-tle (cdr items)))
    nil))

(defun fn-tcl-critical-unknown-items (items)
  (declare (xargs :guard (fn-tcl-item-listp items)))
  (if (consp items)
      (or (and (fn-tcl-flag-critical (fn-tcl-item-flags (car items)))
               (not (equal (fn-tcl-item-type (car items)) *fn-tcl-ext-transfer-length*)))
          (fn-tcl-critical-unknown-items (cdr items)))
    nil))

(defthm fn-tcl-find-tle-is-item
  (implies (and (fn-tcl-item-listp items) (fn-tcl-find-tle items))
           (and (fn-tcl-item-shapep (fn-tcl-find-tle items))
                (fn-cbor-octet-listp (fn-tcl-item-value (fn-tcl-find-tle items))))))

; The transfer extension decision at START: (:refuse reason) or (:ok total)
; with total the Transfer Length Extension value or nil.
(defun fn-tcl-ext-decision (items transfer-mru)
  (declare (xargs :guard (and (fn-tcl-item-listp items) (natp transfer-mru))))
  (let ((tle (fn-tcl-find-tle items)))
    (cond ((fn-tcl-critical-unknown-items items)
           (list :refuse *fn-tcl-refuse-extension-failure*))
          ((< 1 (fn-tcl-count-tle items))
           (list :refuse *fn-tcl-refuse-not-acceptable*))
          ((and tle (not (equal (len (fn-tcl-item-value tle)) 8)))
           (list :refuse *fn-tcl-refuse-extension-failure*))
          ((and tle (< transfer-mru (fn-tcl-be-from (fn-tcl-item-value tle))))
           (list :refuse *fn-tcl-refuse-not-acceptable*))
          (tle (list :ok (fn-tcl-be-from (fn-tcl-item-value tle))))
          (t (list :ok nil)))))

(defun fn-tcl-refuse (s xfer-id reason now)
  (declare (xargs :guard t))
  (fn-tcl-make-result
   (fn-tcl-next s (fn-tcl-session-phase s) nil (fn-tcl-session-outbound s)
                (fn-tcl-session-term s) now)
   (list (fn-tcl-send-event (fn-tcl-make-xfer-refuse reason xfer-id))
         (list :inbound-refused xfer-id reason))
   nil))

(defun fn-tcl-complete (s xfer-id flags len data now)
  (declare (xargs :guard t))
  (fn-tcl-make-result
   (fn-tcl-next s (fn-tcl-session-phase s) nil (fn-tcl-session-outbound s)
                (fn-tcl-session-term s) now)
   (list (fn-tcl-send-event (fn-tcl-make-xfer-ack flags xfer-id len))
         (list :bundle-received xfer-id data))
   nil))

(defun fn-tcl-stage (s inbound flags xfer-id len now)
  (declare (xargs :guard t))
  (fn-tcl-make-result
   (fn-tcl-next s (fn-tcl-session-phase s) inbound (fn-tcl-session-outbound s)
                (fn-tcl-session-term s) now)
   (list (fn-tcl-send-event (fn-tcl-make-xfer-ack flags xfer-id len)))
   nil))

; A segment that interleaves with the live transfer, repeats START, or
; continues a transfer that was never started: the stream is broken.  Reject
; the message, refuse the live transfer (Retransmit, it must come again in a
; new session), and terminate Contact Failure unless already terminating.
(defun fn-tcl-broken-stream (s live-id now)
  (declare (xargs :guard t))
  (fn-tcl-make-result
   (fn-tcl-next s :ending nil (fn-tcl-session-outbound s)
                (if (fn-tcl-session-term s) (fn-tcl-session-term s) :sent) now)
   (append (list (fn-tcl-send-event (fn-tcl-make-msg-reject *fn-tcl-reject-unexpected* 1)))
           (if live-id
               (list (fn-tcl-send-event
                      (fn-tcl-make-xfer-refuse *fn-tcl-refuse-retransmit* live-id))
                     (list :inbound-refused live-id *fn-tcl-refuse-retransmit*))
             nil)
           (if (fn-tcl-session-term s)
               nil
             (list (fn-tcl-send-event
                    (fn-tcl-make-sess-term 0 *fn-tcl-term-contact-failure*)))))
   nil))

(defun fn-tcl-recv-segment (s m now)
  (declare (xargs :guard (and (fn-tcl-sessionp s)
                              (fn-tcl-transferringp (fn-tcl-session-phase s))
                              (fn-tcl-session-negotiated s)
                              (fn-tcl-messagep m (fn-tcl-segment-mru s))
                              (equal (fn-tcl-msg-kind m) :xfer-segment))
                  :verify-guards nil))
  (let* ((flags (fn-tcl-xfer-segment-flags m))
         (xfer-id (fn-tcl-xfer-segment-xfer-id m))
         (ext (fn-tcl-xfer-segment-ext m))
         (data (fn-tcl-xfer-segment-data m))
         (dlen (len data))
         (inb (fn-tcl-session-inbound s))
         (mru (fn-tcl-transfer-mru s)))
    (cond
     ((and inb (or (not (equal xfer-id (fn-tcl-inbound-xfer-id inb)))
                   (fn-tcl-flag-start flags)))
      (fn-tcl-broken-stream s (fn-tcl-inbound-xfer-id inb) now))
     ((and (not inb) (not (fn-tcl-flag-start flags)))
      (fn-tcl-broken-stream s nil now))
     ((not inb)
      ; START of a new transfer
      (if (equal (fn-tcl-session-phase s) :ending)
          (fn-tcl-refuse s xfer-id *fn-tcl-refuse-session-terminating* now)
        (let ((d (fn-tcl-ext-decision ext mru)))
          (cond ((equal (car d) :refuse) (fn-tcl-refuse s xfer-id (car (cdr d)) now))
                ((< mru dlen) (fn-tcl-refuse s xfer-id *fn-tcl-refuse-no-resources* now))
                ((and (car (cdr d)) (< (car (cdr d)) dlen))
                 (fn-tcl-refuse s xfer-id *fn-tcl-refuse-not-acceptable* now))
                ((fn-tcl-flag-end flags)
                 (if (and (car (cdr d)) (not (equal (car (cdr d)) dlen)))
                     (fn-tcl-refuse s xfer-id *fn-tcl-refuse-not-acceptable* now)
                   (fn-tcl-complete s xfer-id flags dlen data now)))
                (t (fn-tcl-stage s (fn-tcl-make-inbound xfer-id (list data) dlen (car (cdr d)))
                                 flags xfer-id dlen now))))))
     (t
      ; continuation of the live transfer
      (let ((new-len (+ (fn-tcl-inbound-received-len inb) dlen))
            (total (fn-tcl-inbound-total inb)))
        (cond ((< mru new-len)
               (fn-tcl-refuse s xfer-id *fn-tcl-refuse-no-resources* now))
              ((and total (< total new-len))
               (fn-tcl-refuse s xfer-id *fn-tcl-refuse-not-acceptable* now))
              ((fn-tcl-flag-end flags)
               (if (and total (not (equal total new-len)))
                   (fn-tcl-refuse s xfer-id *fn-tcl-refuse-not-acceptable* now)
                 (fn-tcl-complete s xfer-id flags new-len
                                  (fn-tcl-concat-rev (cons data (fn-tcl-inbound-staged inb)) nil)
                                  now)))
              (t (fn-tcl-stage s (fn-tcl-make-inbound xfer-id
                                                      (cons data (fn-tcl-inbound-staged inb))
                                                      new-len total)
                               flags xfer-id new-len now))))))))

; -----------------------------------------------------------------------------
; Outbound transfer: acknowledgements and refusals from the peer.

(defun fn-tcl-unexpected (s header now)
  (declare (xargs :guard t))
  (fn-tcl-make-result
   (fn-tcl-next s (fn-tcl-session-phase s) (fn-tcl-session-inbound s)
                (fn-tcl-session-outbound s) (fn-tcl-session-term s) now)
   (list (fn-tcl-send-event (fn-tcl-make-msg-reject *fn-tcl-reject-unexpected* header)))
   nil))

(defun fn-tcl-recv-ack (s m now)
  (declare (xargs :guard (and (fn-tcl-sessionp s)
                              (fn-tcl-transferringp (fn-tcl-session-phase s))
                              (fn-tcl-session-negotiated s)
                              (fn-tcl-messagep m (fn-tcl-segment-mru s))
                              (equal (fn-tcl-msg-kind m) :xfer-ack))
                  :verify-guards nil))
  (let ((ob (fn-tcl-session-outbound s))
        (xfer-id (fn-tcl-xfer-ack-xfer-id m))
        (len (fn-tcl-xfer-ack-acked-len m))
        (flags (fn-tcl-xfer-ack-flags m)))
    (if (or (null ob)
            (not (equal xfer-id (fn-tcl-outbound-xfer-id ob)))
            (< (fn-tcl-outbound-sent-len ob) len)
            (< len (fn-tcl-outbound-acked-len ob)))
        ; an unknown transfer, an acknowledgement of unsent data, or a
        ; regressing one: Message Unexpected (section 5.1.2)
        (fn-tcl-unexpected s 2 now)
      (if (and (fn-tcl-flag-end flags) (equal len (fn-tcl-outbound-total ob)))
          (fn-tcl-make-result
           (fn-tcl-next s (fn-tcl-session-phase s) (fn-tcl-session-inbound s) nil
                        (fn-tcl-session-term s) (fn-tcl-session-last-tx s))
           (list (list :outbound-sent xfer-id (fn-tcl-outbound-ref ob)))
           nil)
        (fn-tcl-make-result
         (fn-tcl-next s (fn-tcl-session-phase s) (fn-tcl-session-inbound s)
                      (fn-tcl-make-outbound xfer-id (fn-tcl-outbound-ref ob)
                                            (fn-tcl-outbound-remaining ob)
                                            (fn-tcl-outbound-total ob)
                                            (fn-tcl-outbound-sent-len ob) len)
                      (fn-tcl-session-term s) (fn-tcl-session-last-tx s))
         nil
         nil)))))

(defun fn-tcl-recv-refuse (s m now)
  (declare (xargs :guard (and (fn-tcl-sessionp s)
                              (fn-tcl-transferringp (fn-tcl-session-phase s))
                              (fn-tcl-session-negotiated s)
                              (fn-tcl-messagep m (fn-tcl-segment-mru s))
                              (equal (fn-tcl-msg-kind m) :xfer-refuse))
                  :verify-guards nil))
  (declare (ignore now))
  (let ((ob (fn-tcl-session-outbound s))
        (xfer-id (fn-tcl-xfer-refuse-xfer-id m)))
    (if (and ob (equal xfer-id (fn-tcl-outbound-xfer-id ob)))
        (fn-tcl-make-result
         (fn-tcl-next s (fn-tcl-session-phase s) (fn-tcl-session-inbound s) nil
                      (fn-tcl-session-term s) (fn-tcl-session-last-tx s))
         (list (list :outbound-refused xfer-id (fn-tcl-outbound-ref ob)
                     (fn-tcl-xfer-refuse-reason m)))
         nil)
      ; a refusal that crossed the final acknowledgement on the wire
      ; (section 5.2.4): nothing to stop
      (fn-tcl-make-result s nil nil))))

; -----------------------------------------------------------------------------
; Termination (section 6.1).

(defun fn-tcl-recv-term (s m now)
  (declare (xargs :guard (and (fn-tcl-sess-term-shapep m)
                              (fn-cbor-octetp (fn-tcl-sess-term-flags m)))))
  (let ((reason (fn-tcl-sess-term-reason m)))
    (if (null (fn-tcl-session-term s))
        ; the peer initiated: acknowledge with identical content, REPLY set
        (fn-tcl-make-result
         (fn-tcl-next s :ending (fn-tcl-session-inbound s) (fn-tcl-session-outbound s)
                      :both now)
         (list (fn-tcl-send-event
                (fn-tcl-make-sess-term (logior 1 (fn-tcl-sess-term-flags m)) reason))
               (list :peer-terminating reason))
         nil)
      ; our own SESS_TERM was already sent: this is its reply, or a
      ; crossing initiation, and neither is acknowledged again
      (fn-tcl-make-result
       (fn-tcl-next s :ending (fn-tcl-session-inbound s) (fn-tcl-session-outbound s)
                    :both (fn-tcl-session-last-tx s))
       (list (list :peer-terminating reason))
       nil))))

(defun fn-tcl-terminate (s reason now)
  (declare (xargs :guard t))
  (cond ((fn-tcl-session-term s) (fn-tcl-make-result s nil nil))
        ((equal (fn-tcl-session-phase s) :closed) (fn-tcl-make-result s nil nil))
        ((equal (fn-tcl-session-phase s) :tcp-connected)
         ; no Contact Header has been sent, so no SESS_TERM may be (section 6.1)
         (fn-tcl-make-result (fn-tcl-next s :closed nil nil nil (fn-tcl-session-last-tx s))
                             (list (list :close))
                             nil))
        (t (fn-tcl-make-result
            (fn-tcl-next s :ending (fn-tcl-session-inbound s) (fn-tcl-session-outbound s)
                         :sent now)
            (list (fn-tcl-send-event (fn-tcl-make-sess-term 0 reason)))
            nil))))

(defun fn-tcl-tcp-closed (s)
  (declare (xargs :guard t))
  (if (equal (fn-tcl-session-phase s) :closed)
      (fn-tcl-make-result s nil nil)
    (fn-tcl-make-result (fn-tcl-next s :closed nil nil (fn-tcl-session-term s)
                                     (fn-tcl-session-last-tx s))
                        (append (fn-tcl-fail-live s) (list (list :session-down)))
                        nil)))

; Undecodable input.  Before the contact exchange: close silently (section
; 6.1).  After it: MSG_REJECT naming the offending header, then close,
; because the stream cannot be resynchronised (section 8.5).
(defun fn-tcl-input-error (s header reason now)
  (declare (xargs :guard t))
  (if (or (equal (fn-tcl-session-phase s) :tcp-connected)
          (equal (fn-tcl-session-phase s) :contact))
      (fn-tcl-make-result (fn-tcl-next s :closed nil nil (fn-tcl-session-term s)
                                       (fn-tcl-session-last-tx s))
                          (list (list :close))
                          nil)
    (fn-tcl-make-result
     (fn-tcl-next s :closed nil nil (fn-tcl-session-term s) now)
     (append (list (fn-tcl-send-event
                    (fn-tcl-make-msg-reject
                     (if (and (consp reason) (equal (car reason) :unknown-type))
                         *fn-tcl-reject-type-unknown*
                       *fn-tcl-reject-unsupported*)
                     header)))
             (fn-tcl-fail-live s)
             (list (list :close)))
     nil)))

; -----------------------------------------------------------------------------
; Node-initiated sending (sections 5.2.1, 5.2.2).

; The session with a new outbound transfer and the advanced ID frontier.
(defun fn-tcl-with-outbound (s outbound next-xfer-id)
  (declare (xargs :guard t))
  (fn-tcl-make-session (fn-tcl-session-role s) :established (fn-tcl-session-local s)
                       (fn-tcl-session-tls s) (fn-tcl-session-peer s)
                       (fn-tcl-session-negotiated s) (fn-tcl-session-inbound s)
                       outbound next-xfer-id (fn-tcl-session-last-rx s)
                       (fn-tcl-session-last-tx s) nil))

(defun fn-tcl-pump (s now)
  (declare (xargs :guard (fn-tcl-sessionp s) :verify-guards nil))
  (let ((ob (fn-tcl-session-outbound s)))
    (if (or (null ob)
            (equal (fn-tcl-outbound-sent-len ob) (fn-tcl-outbound-total ob)))
        (fn-tcl-make-result s nil nil)
      (let* ((mtu (fn-tcl-negotiated-segment-mtu (fn-tcl-session-negotiated s)))
             (sent (fn-tcl-outbound-sent-len ob))
             (total (fn-tcl-outbound-total ob))
             (left (- total sent))
             (k (if (< mtu left) mtu left))
             (start (equal sent 0))
             (end (equal k left))
             (flags (+ (if end 1 0) (if start 2 0)))
             (ext (if (and start (not end))
                      (list (fn-tcl-make-item 0 *fn-tcl-ext-transfer-length*
                                              (fn-tcl-be-bytes total 8)))
                    nil)))
        (fn-tcl-make-result
         (fn-tcl-next s (fn-tcl-session-phase s) (fn-tcl-session-inbound s)
                      (fn-tcl-make-outbound (fn-tcl-outbound-xfer-id ob)
                                            (fn-tcl-outbound-ref ob)
                                            (fn-tcl-drop k (fn-tcl-outbound-remaining ob))
                                            total (+ sent k)
                                            (fn-tcl-outbound-acked-len ob))
                      (fn-tcl-session-term s) now)
         (list (fn-tcl-send-event
                (fn-tcl-make-xfer-segment flags (fn-tcl-outbound-xfer-id ob) ext
                                          (fn-tcl-take k (fn-tcl-outbound-remaining ob)))))
         nil)))))

(defun fn-tcl-send (s ref octets now)
  (declare (xargs :guard (and (fn-tcl-sessionp s) (fn-cbor-octet-listp octets))
                  :verify-guards nil))
  (cond ((not (equal (fn-tcl-session-phase s) :established))
         (fn-tcl-make-result s (list (list :send-refused ref :not-established)) nil))
        ((fn-tcl-session-outbound s)
         (fn-tcl-make-result s (list (list :send-refused ref :busy)) nil))
        ((< (fn-tcl-negotiated-transfer-mtu (fn-tcl-session-negotiated s)) (len octets))
         (fn-tcl-make-result s (list (list :send-refused ref :exceeds-transfer-mtu)) nil))
        ((< *fn-tcl-max-u64* (fn-tcl-session-next-xfer-id s))
         ; section 5.2.1: Resource Exhaustion on ID space exhaustion
         (fn-tcl-make-result
          (fn-tcl-next s :ending (fn-tcl-session-inbound s) nil :sent now)
          (list (list :send-refused ref :ids-exhausted)
                (fn-tcl-send-event (fn-tcl-make-sess-term 0 *fn-tcl-term-resource-exhaustion*)))
          nil))
        (t (fn-tcl-pump
            (fn-tcl-with-outbound s (fn-tcl-make-outbound (fn-tcl-session-next-xfer-id s) ref
                                                          octets (len octets) 0 0)
                                  (+ 1 (fn-tcl-session-next-xfer-id s)))
            now))))

; -----------------------------------------------------------------------------
; Keepalive and idle timeout (sections 5.1.1, 6.2) as clock observations.

(defun fn-tcl-tick (s obs)
  (declare (xargs :guard (and (fn-tcl-sessionp s) (fn-clock-observationp obs))
                  :verify-guards nil))
  (let ((now (fn-clock-monotonic obs))
        (n (fn-tcl-session-negotiated s)))
    (if (or (null n)
            (not (fn-tcl-transferringp (fn-tcl-session-phase s)))
            (equal (fn-tcl-negotiated-keepalive n) 0))
        (fn-tcl-make-result s nil nil)
      (let ((interval (* 1000 (fn-tcl-negotiated-keepalive n))))
        (cond ((<= (* 2 interval) (- now (fn-tcl-session-last-rx s)))
               (if (fn-tcl-session-term s)
                   ; already terminating and the peer is silent: give up
                   (fn-tcl-make-result
                    (fn-tcl-next s :closed nil nil (fn-tcl-session-term s)
                                 (fn-tcl-session-last-tx s))
                    (append (fn-tcl-fail-live s) (list (list :close)))
                    nil)
                 (fn-tcl-make-result
                  (fn-tcl-next s :ending (fn-tcl-session-inbound s)
                               (fn-tcl-session-outbound s) :sent now)
                  (list (fn-tcl-send-event (fn-tcl-make-sess-term 0 *fn-tcl-term-idle-timeout*)))
                  nil)))
              ((<= interval (- now (fn-tcl-session-last-tx s)))
               (fn-tcl-make-result
                (fn-tcl-next s (fn-tcl-session-phase s) (fn-tcl-session-inbound s)
                             (fn-tcl-session-outbound s) (fn-tcl-session-term s) now)
                (list (fn-tcl-send-event (fn-tcl-make-keepalive)))
                nil))
              (t (fn-tcl-make-result s nil nil)))))))

; -----------------------------------------------------------------------------
; One decoded message.

(defun fn-tcl-step (s m now)
  (declare (xargs :guard (and (fn-tcl-sessionp s)
                              (fn-tcl-messagep m (fn-tcl-segment-mru s))
                              (fn-clock-timep now))
                  :verify-guards nil))
  (if (equal (fn-tcl-session-phase s) :closed)
      (fn-tcl-make-result s nil nil)
    (let* ((s1 (fn-tcl-touch-rx s now))
           (kind (fn-tcl-msg-kind m))
           (phase (fn-tcl-session-phase s1)))
      (fn-tcl-settle
       (cond ((equal kind :contact)
              (if (or (equal phase :tcp-connected) (equal phase :contact))
                  (fn-tcl-recv-contact s1 m now)
                (fn-tcl-make-result s1 nil nil)))
             ((equal kind :sess-init)
              (if (equal phase :messaging)
                  (fn-tcl-recv-init s1 m now)
                (fn-tcl-unexpected s1 7 now)))
             ((equal kind :xfer-segment)
              (if (and (fn-tcl-transferringp phase) (fn-tcl-session-negotiated s1))
                  (fn-tcl-recv-segment s1 m now)
                (fn-tcl-unexpected s1 1 now)))
             ((equal kind :xfer-ack)
              (if (and (fn-tcl-transferringp phase) (fn-tcl-session-negotiated s1))
                  (fn-tcl-recv-ack s1 m now)
                (fn-tcl-unexpected s1 2 now)))
             ((equal kind :xfer-refuse)
              (if (and (fn-tcl-transferringp phase) (fn-tcl-session-negotiated s1))
                  (fn-tcl-recv-refuse s1 m now)
                (fn-tcl-unexpected s1 3 now)))
             ((equal kind :keepalive) (fn-tcl-make-result s1 nil nil))
             ((equal kind :sess-term)
              (if (equal phase :tcp-connected)
                  (fn-tcl-make-result s1 nil nil)
                (fn-tcl-recv-term s1 m now)))
             ((equal kind :msg-reject)
              (fn-tcl-make-result s1 (list (list :peer-rejected (fn-tcl-msg-reject-reason m)
                                                 (fn-tcl-msg-reject-header m)))
                                  nil))
             (t (fn-tcl-make-result s1 nil nil)))))))

; -----------------------------------------------------------------------------
; The served path: consume every complete message in the buffer.  A trailing
; partial message is returned as `unconsumed`, never copied into the state;
; so is the buffer when the session is closed or a decode error closed it.

(defun fn-tcl-decode-for (s buf)
  (declare (xargs :guard (and (fn-tcl-sessionp s) (fn-cbor-octet-listp buf))
                  :verify-guards nil))
  (if (or (equal (fn-tcl-session-phase s) :tcp-connected)
          (equal (fn-tcl-session-phase s) :contact))
      (fn-tcl-decode-contact buf)
    (fn-tcl-decode-message buf (fn-tcl-segment-mru s))))

(defthm fn-tcl-decode-for-consumes
  (implies (fn-tcl-parse-okp (fn-tcl-decode-for s buf))
           (< (len (fn-tcl-parse-rest (fn-tcl-decode-for s buf))) (len buf)))
  :rule-classes (:rewrite :linear))

(defun fn-tcl-drive (s buf now)
  (declare (xargs :guard (and (fn-tcl-sessionp s) (fn-cbor-octet-listp buf)
                              (fn-clock-timep now))
                  :verify-guards nil
                  :measure (len buf)))
  (if (mbe :logic (not (and (fn-tcl-sessionp s) (fn-cbor-octet-listp buf)
                            (fn-clock-timep now)))
           :exec nil)
      (fn-tcl-make-result s nil buf)
    (if (or (equal (fn-tcl-session-phase s) :closed) (not (consp buf)))
        (fn-tcl-make-result s nil buf)
      (let ((d (fn-tcl-decode-for s buf)))
        (cond ((fn-tcl-parse-okp d)
               (let* ((r (fn-tcl-step s (fn-tcl-parse-msg d) now))
                      (tail (fn-tcl-drive (fn-tcl-result-session r) (fn-tcl-parse-rest d) now)))
                 (fn-tcl-make-result (fn-tcl-result-session tail)
                                     (fn-tcl-app (fn-tcl-result-events r)
                                                 (fn-tcl-result-events tail))
                                     (fn-tcl-result-unconsumed tail))))
              ((fn-tcl-parse-needp d) (fn-tcl-make-result s nil buf))
              (t (let ((r (fn-tcl-input-error s (car buf) (fn-tcl-parse-reason d) now)))
                   (fn-tcl-make-result (fn-tcl-result-session r)
                                       (fn-tcl-result-events r)
                                       buf))))))))

; -----------------------------------------------------------------------------
; Preservation keystones.  Each transition keeps fn-tcl-sessionp; the guard
; closure below is discharged from them.

(local (in-theory (enable fn-tcl-messagep)))

(defthm fn-tcl-touch-rx-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now))
           (fn-tcl-sessionp (fn-tcl-touch-rx s now))))

; fn-tcl-step dispatches on the touched session; what touch-rx carries.
(defthm fn-tcl-touch-rx-fields
  (and (equal (fn-tcl-session-role (fn-tcl-touch-rx s now)) (fn-tcl-session-role s))
       (equal (fn-tcl-session-phase (fn-tcl-touch-rx s now)) (fn-tcl-session-phase s))
       (equal (fn-tcl-session-local (fn-tcl-touch-rx s now)) (fn-tcl-session-local s))
       (equal (fn-tcl-session-negotiated (fn-tcl-touch-rx s now)) (fn-tcl-session-negotiated s))
       (equal (fn-tcl-session-inbound (fn-tcl-touch-rx s now)) (fn-tcl-session-inbound s))
       (equal (fn-tcl-session-outbound (fn-tcl-touch-rx s now)) (fn-tcl-session-outbound s))
       (equal (fn-tcl-session-term (fn-tcl-touch-rx s now)) (fn-tcl-session-term s))
       (equal (fn-tcl-segment-mru (fn-tcl-touch-rx s now)) (fn-tcl-segment-mru s))))

; What a session says about its fields, exported so an includer never
; opens fn-tcl-sessionp, and the one rebuild lemma every transition uses.
; The absent-field facts are stated with `not`, never `null`: ACL2 stores a
; `(not x)` conclusion as the rule x -> nil under iff, which fires on the
; bare literal `(fn-tcl-session-outbound s)` in a split case, while a
; `(null x)` conclusion is a rule on the term `(null x)` and never matches it.
(defthm fn-tcl-sessionp-facts
  (implies (fn-tcl-sessionp s)
           (and (fn-tcl-session-shapep s)
                (fn-tcl-rolep (fn-tcl-session-role s))
                (fn-tcl-phasep (fn-tcl-session-phase s))
                (fn-tcl-paramsp (fn-tcl-session-local s))
                (booleanp (fn-tcl-session-tls s))
                (fn-tcl-termp (fn-tcl-session-term s))
                (natp (fn-tcl-session-next-xfer-id s))
                (fn-clock-timep (fn-tcl-session-last-rx s))
                (fn-clock-timep (fn-tcl-session-last-tx s))
                (implies (fn-tcl-session-peer s) (fn-tcl-peer-initp (fn-tcl-session-peer s)))
                (implies (fn-tcl-session-negotiated s)
                         (fn-tcl-negotiatedp (fn-tcl-session-negotiated s)))
                (implies (fn-tcl-session-inbound s)
                         (fn-tcl-inboundp (fn-tcl-session-inbound s)
                                          (fn-tcl-params-transfer-mru (fn-tcl-session-local s))))
                (implies (fn-tcl-session-outbound s)
                         (fn-tcl-outboundp (fn-tcl-session-outbound s)))
                (implies (fn-tcl-pre-establishedp (fn-tcl-session-phase s))
                         (and (not (fn-tcl-session-negotiated s))
                              (not (fn-tcl-session-term s))))
                (implies (equal (fn-tcl-session-phase s) :established)
                         (and (fn-tcl-session-negotiated s)
                              (not (fn-tcl-session-term s))))
                (implies (equal (fn-tcl-session-phase s) :ending)
                         (fn-tcl-session-term s))
                (implies (not (fn-tcl-transferringp (fn-tcl-session-phase s)))
                         (and (not (fn-tcl-session-inbound s))
                              (not (fn-tcl-session-outbound s))))
                (implies (not (fn-tcl-session-negotiated s))
                         (and (not (fn-tcl-session-inbound s))
                              (not (fn-tcl-session-outbound s)))))))

; The field facts of the sub-recognizers and the conditional fields of a
; session, as forward-chaining rules only (docs/proof-style.md section 1):
; `(fn-tcl-sessionp s)` in a hypothesis puts into the context every fact a
; transition lemma relieves about the fields it carries, in the opened form
; the clause states them (`integerp` and bounds, never `natp`), so that no
; proof opens the recognizer to reach a field of a field.
(defthm fn-tcl-paramsp-forward-fields
  (implies (fn-tcl-paramsp p)
           (and (fn-tcl-params-shapep p)
                (integerp (fn-tcl-params-keepalive p))
                (<= 0 (fn-tcl-params-keepalive p))
                (<= (fn-tcl-params-keepalive p) *fn-tcl-max-u16*)
                (integerp (fn-tcl-params-segment-mru p))
                (<= 0 (fn-tcl-params-segment-mru p))
                (<= (fn-tcl-params-segment-mru p) *fn-tcl-max-u64*)
                (integerp (fn-tcl-params-transfer-mru p))
                (<= 0 (fn-tcl-params-transfer-mru p))
                (<= (fn-tcl-params-transfer-mru p) *fn-tcl-max-u64*)
                (fn-cbor-octet-listp (fn-tcl-params-node-id p))
                (<= (len (fn-tcl-params-node-id p)) *fn-tcl-node-id-cap*)
                (booleanp (fn-tcl-params-can-tls p))))
  :rule-classes :forward-chaining)

(defthm fn-tcl-negotiatedp-forward-fields
  (implies (fn-tcl-negotiatedp n)
           (and (fn-tcl-negotiated-shapep n)
                (integerp (fn-tcl-negotiated-keepalive n))
                (<= 0 (fn-tcl-negotiated-keepalive n))
                (<= (fn-tcl-negotiated-keepalive n) *fn-tcl-max-u16*)
                (integerp (fn-tcl-negotiated-segment-mtu n))
                (< 0 (fn-tcl-negotiated-segment-mtu n))
                (<= (fn-tcl-negotiated-segment-mtu n) *fn-tcl-max-u64*)
                (integerp (fn-tcl-negotiated-transfer-mtu n))
                (< 0 (fn-tcl-negotiated-transfer-mtu n))
                (<= (fn-tcl-negotiated-transfer-mtu n) *fn-tcl-max-u64*)
                (booleanp (fn-tcl-negotiated-tls n))
                (fn-cbor-octet-listp (fn-tcl-negotiated-peer-node-id n))))
  :rule-classes :forward-chaining)

(defthm fn-tcl-inboundp-forward-fields
  (implies (fn-tcl-inboundp i limit)
           (and (fn-tcl-inbound-shapep i)
                (integerp (fn-tcl-inbound-xfer-id i))
                (<= 0 (fn-tcl-inbound-xfer-id i))
                (<= (fn-tcl-inbound-xfer-id i) *fn-tcl-max-u64*)
                (fn-tcl-octet-listsp (fn-tcl-inbound-staged i))
                (integerp (fn-tcl-inbound-received-len i))
                (<= 0 (fn-tcl-inbound-received-len i))
                (equal (fn-tcl-inbound-received-len i)
                       (fn-tcl-lists-len (fn-tcl-inbound-staged i)))
                (<= (fn-tcl-inbound-received-len i) limit)))
  :rule-classes :forward-chaining)

(defthm fn-tcl-inboundp-forward-total
  (implies (and (fn-tcl-inboundp i limit) (fn-tcl-inbound-total i))
           (and (integerp (fn-tcl-inbound-total i))
                (<= 0 (fn-tcl-inbound-total i))
                (<= (fn-tcl-inbound-total i) *fn-tcl-max-u64*)
                (<= (fn-tcl-inbound-received-len i) (fn-tcl-inbound-total i))))
  :rule-classes ((:forward-chaining :trigger-terms ((fn-tcl-inbound-total i)))))

(defthm fn-tcl-outboundp-forward-fields
  (implies (fn-tcl-outboundp o)
           (and (fn-tcl-outbound-shapep o)
                (integerp (fn-tcl-outbound-xfer-id o))
                (<= 0 (fn-tcl-outbound-xfer-id o))
                (<= (fn-tcl-outbound-xfer-id o) *fn-tcl-max-u64*)
                (fn-cbor-octet-listp (fn-tcl-outbound-remaining o))
                (integerp (fn-tcl-outbound-total o))
                (<= 0 (fn-tcl-outbound-total o))
                (<= (fn-tcl-outbound-total o) *fn-tcl-max-u64*)
                (integerp (fn-tcl-outbound-sent-len o))
                (<= 0 (fn-tcl-outbound-sent-len o))
                (equal (+ (fn-tcl-outbound-sent-len o) (len (fn-tcl-outbound-remaining o)))
                       (fn-tcl-outbound-total o))
                (integerp (fn-tcl-outbound-acked-len o))
                (<= 0 (fn-tcl-outbound-acked-len o))
                (<= (fn-tcl-outbound-acked-len o) (fn-tcl-outbound-sent-len o))))
  :rule-classes :forward-chaining)

(defthm fn-tcl-sessionp-forward-fields
  (implies (fn-tcl-sessionp s)
           (and (fn-tcl-session-shapep s)
                (fn-tcl-paramsp (fn-tcl-session-local s))
                (booleanp (fn-tcl-session-tls s))
                (integerp (fn-tcl-session-next-xfer-id s))
                (<= 0 (fn-tcl-session-next-xfer-id s))
                (fn-clock-timep (fn-tcl-session-last-rx s))
                (fn-clock-timep (fn-tcl-session-last-tx s))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (disable fn-tcl-sessionp) :use fn-tcl-sessionp-facts)))

(defthm fn-tcl-sessionp-forward-peer
  (implies (and (fn-tcl-sessionp s) (fn-tcl-session-peer s))
           (fn-tcl-peer-initp (fn-tcl-session-peer s)))
  :rule-classes ((:forward-chaining :trigger-terms ((fn-tcl-session-peer s))))
  :hints (("Goal" :in-theory (disable fn-tcl-sessionp) :use fn-tcl-sessionp-facts)))

(defthm fn-tcl-sessionp-forward-negotiated
  (implies (and (fn-tcl-sessionp s) (fn-tcl-session-negotiated s))
           (fn-tcl-negotiatedp (fn-tcl-session-negotiated s)))
  :rule-classes ((:forward-chaining :trigger-terms ((fn-tcl-session-negotiated s))))
  :hints (("Goal" :in-theory (disable fn-tcl-sessionp) :use fn-tcl-sessionp-facts)))

(defthm fn-tcl-sessionp-forward-inbound
  (implies (and (fn-tcl-sessionp s) (fn-tcl-session-inbound s))
           (and (fn-tcl-inboundp (fn-tcl-session-inbound s)
                                 (fn-tcl-params-transfer-mru (fn-tcl-session-local s)))
                (fn-tcl-session-negotiated s)))
  :rule-classes ((:forward-chaining :trigger-terms ((fn-tcl-session-inbound s))))
  :hints (("Goal" :in-theory (disable fn-tcl-sessionp) :use fn-tcl-sessionp-facts)))

(defthm fn-tcl-sessionp-forward-established
  (implies (and (fn-tcl-sessionp s) (equal (fn-tcl-session-phase s) :established))
           (fn-tcl-session-negotiated s))
  :rule-classes ((:forward-chaining :trigger-terms ((fn-tcl-session-phase s))))
  :hints (("Goal" :in-theory (disable fn-tcl-sessionp) :use fn-tcl-sessionp-facts)))

(defthm fn-tcl-sessionp-forward-outbound
  (implies (and (fn-tcl-sessionp s) (fn-tcl-session-outbound s))
           (and (fn-tcl-outboundp (fn-tcl-session-outbound s))
                (fn-tcl-session-negotiated s)))
  :rule-classes ((:forward-chaining :trigger-terms ((fn-tcl-session-outbound s))))
  :hints (("Goal" :in-theory (disable fn-tcl-sessionp) :use fn-tcl-sessionp-facts)))

; The numeric fields, in the rule classes type-set and linear arithmetic read:
; `(+ 1 (fn-tcl-session-next-xfer-id s))` is an integer only if type-set
; knows the field is (a :type-prescription rule), and a Transfer Length is
; within the u64 only through the MRU (a :linear rule).
(defthm fn-tcl-sessionp-next-xfer-id-natp
  (implies (fn-tcl-sessionp s) (natp (fn-tcl-session-next-xfer-id s)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable fn-tcl-sessionp) :use fn-tcl-sessionp-facts)))

(defthm fn-tcl-sessionp-mru-natp
  (implies (fn-tcl-sessionp s)
           (and (natp (fn-tcl-params-segment-mru (fn-tcl-session-local s)))
                (natp (fn-tcl-params-transfer-mru (fn-tcl-session-local s)))))
  :rule-classes ((:type-prescription
                  :corollary (implies (fn-tcl-sessionp s)
                                      (natp (fn-tcl-params-segment-mru (fn-tcl-session-local s)))))
                 (:type-prescription
                  :corollary (implies (fn-tcl-sessionp s)
                                      (natp (fn-tcl-params-transfer-mru (fn-tcl-session-local s))))))
  :hints (("Goal" :in-theory (disable fn-tcl-sessionp) :use fn-tcl-sessionp-facts)))

; The two MRU glue functions are closed in the step and drive proofs (so
; that fn-tcl-decode-for-yields-message matches); their type stays known.
(defthm fn-tcl-segment-mru-natp
  (implies (fn-tcl-sessionp s) (natp (fn-tcl-segment-mru s)))
  :rule-classes :type-prescription)

(defthm fn-tcl-transfer-mru-natp
  (implies (fn-tcl-sessionp s) (natp (fn-tcl-transfer-mru s)))
  :rule-classes :type-prescription)

(defthm fn-tcl-sessionp-mru-bounds
  (implies (fn-tcl-sessionp s)
           (and (<= (fn-tcl-params-segment-mru (fn-tcl-session-local s)) *fn-tcl-max-u64*)
                (<= (fn-tcl-params-transfer-mru (fn-tcl-session-local s)) *fn-tcl-max-u64*)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-tcl-sessionp) :use fn-tcl-sessionp-facts)))

; The five phase-consistency hypotheses are conditionals whose antecedent is
; a glue predicate over the new phase.  When a transition carries the phase
; (`(fn-tcl-session-phase s)`), the antecedent opens to an undecided
; disjunction that the rewriter cannot assume while relieving a hypothesis,
; although fn-tcl-sessionp-facts decides each case at the clause level; so
; those five are `case-split`: the rule fires, and a case the rewriter could
; not relieve is split off and closed from the facts.  Logically identity.
(defthm fn-tcl-next-preserves-sessionp
  (implies (and (fn-tcl-sessionp s)
                (fn-tcl-phasep phase) (fn-tcl-termp term) (fn-clock-timep last-tx)
                (or (not inbound)
                    (fn-tcl-inboundp inbound (fn-tcl-params-transfer-mru (fn-tcl-session-local s))))
                (or (not outbound) (fn-tcl-outboundp outbound))
                (case-split
                 (implies (fn-tcl-pre-establishedp phase)
                          (and (not (fn-tcl-session-negotiated s)) (not term))))
                (case-split
                 (implies (equal phase :established)
                          (and (fn-tcl-session-negotiated s) (not term))))
                (case-split (implies (equal phase :ending) term))
                (case-split
                 (implies (not (fn-tcl-transferringp phase)) (and (not inbound) (not outbound))))
                (case-split
                 (implies (not (fn-tcl-session-negotiated s)) (and (not inbound) (not outbound)))))
           (fn-tcl-sessionp (fn-tcl-next s phase inbound outbound term last-tx)))
  :hints (("Goal" :in-theory (disable fn-tcl-inboundp fn-tcl-outboundp fn-tcl-paramsp
                                      fn-tcl-negotiatedp fn-tcl-peer-initp))))

(defthm fn-tcl-with-outbound-preserves-sessionp
  (implies (and (fn-tcl-sessionp s)
                (equal (fn-tcl-session-phase s) :established)
                (fn-tcl-outboundp outbound)
                (natp next-xfer-id))
           (fn-tcl-sessionp (fn-tcl-with-outbound s outbound next-xfer-id)))
  :hints (("Goal" :in-theory (disable fn-tcl-inboundp fn-tcl-outboundp fn-tcl-paramsp
                                      fn-tcl-negotiatedp fn-tcl-peer-initp))))

; fn-tcl-recv-contact and fn-tcl-recv-init build their session with
; fn-tcl-make-session directly (they set tls, peer and negotiated, which
; fn-tcl-next carries), so their lemmas conclude the recognizer of a
; constructor and open it in their hints; every other transition goes
; through fn-tcl-next and its lemma is fn-tcl-next-preserves-sessionp.
(local (in-theory (disable fn-tcl-sessionp fn-tcl-next fn-tcl-with-outbound)))

(defthm fn-tcl-settle-preserves-sessionp
  (implies (fn-tcl-sessionp (fn-tcl-result-session r))
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-settle r)))))

(defthm fn-tcl-open-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now))
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-open s now)))))

(defthm fn-tcl-recv-contact-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now)
                (fn-tcl-pre-establishedp (fn-tcl-session-phase s)))
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-recv-contact s m now))))
  :hints (("Goal" :in-theory (enable fn-tcl-sessionp))))

(defthm fn-tcl-negotiate-is-negotiated
  (implies (and (fn-tcl-paramsp local) (fn-tcl-peer-initp m)
                (fn-tcl-init-acceptablep local m))
           (fn-tcl-negotiatedp (fn-tcl-negotiate local tls m))))

(defthm fn-tcl-recv-init-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now)
                (fn-tcl-peer-initp m)
                (equal (fn-tcl-session-phase s) :messaging))
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-recv-init s m now))))
  :hints (("Goal" :in-theory (e/d (fn-tcl-sessionp) (fn-tcl-negotiate fn-tcl-init-acceptablep)))))

(defthm fn-tcl-refuse-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now))
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-refuse s xfer-id reason now)))))

(defthm fn-tcl-complete-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now))
           (fn-tcl-sessionp (fn-tcl-result-session
                             (fn-tcl-complete s xfer-id flags len data now)))))

(defthm fn-tcl-stage-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now)
                (fn-tcl-transferringp (fn-tcl-session-phase s))
                (fn-tcl-session-negotiated s)
                (fn-tcl-inboundp inbound (fn-tcl-transfer-mru s)))
           (fn-tcl-sessionp (fn-tcl-result-session
                             (fn-tcl-stage s inbound flags xfer-id len now)))))

(defthm fn-tcl-broken-stream-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now)
                (fn-tcl-transferringp (fn-tcl-session-phase s)))
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-broken-stream s live-id now)))))

; At START, an accepted decision's total is a Transfer Length within the MRU.
; `rationalp` is concluded beside `integerp` because the guard obligation of
; the `<` on the total is `rationalp`, and the total's type is not a
; :type-prescription (the typed term would occur in its own hypotheses).
(defthm fn-tcl-ext-decision-ok-total
  (implies (and (fn-tcl-item-listp items)
                (not (equal (car (fn-tcl-ext-decision items mru)) :refuse))
                (cadr (fn-tcl-ext-decision items mru)))
           (and (integerp (cadr (fn-tcl-ext-decision items mru)))
                (rationalp (cadr (fn-tcl-ext-decision items mru)))
                (<= 0 (cadr (fn-tcl-ext-decision items mru)))
                (<= (cadr (fn-tcl-ext-decision items mru)) mru)))
  :rule-classes ((:rewrite)
                 (:linear :corollary
                  (implies (and (fn-tcl-item-listp items)
                                (not (equal (car (fn-tcl-ext-decision items mru)) :refuse))
                                (cadr (fn-tcl-ext-decision items mru)))
                           (<= (cadr (fn-tcl-ext-decision items mru)) mru)))))

(defthm fn-tcl-ext-decision-ok-total-u64
  (implies (and (fn-tcl-item-listp items)
                (<= mru *fn-tcl-max-u64*)
                (not (equal (car (fn-tcl-ext-decision items mru)) :refuse))
                (cadr (fn-tcl-ext-decision items mru)))
           (<= (cadr (fn-tcl-ext-decision items mru)) *fn-tcl-max-u64*)))

(defthm fn-tcl-drop-octet-listp
  (implies (fn-cbor-octet-listp x)
           (fn-cbor-octet-listp (fn-tcl-drop n x)))
  :hints (("Goal" :in-theory (enable fn-tcl-drop))))

(defthm fn-tcl-recv-segment-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now)
                (fn-tcl-messagep m (fn-tcl-segment-mru s))
                (equal (fn-tcl-msg-kind m) :xfer-segment)
                (fn-tcl-transferringp (fn-tcl-session-phase s))
                (fn-tcl-session-negotiated s))
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-recv-segment s m now))))
  :hints (("Goal" :in-theory (e/d (fn-tcl-recv-segment)
                                  (fn-tcl-refuse fn-tcl-complete fn-tcl-stage
                                   fn-tcl-broken-stream fn-tcl-ext-decision
                                   fn-tcl-sessionp))
           ; the stage lemma cited for the two inbound records recv-segment
           ; builds (START, continuation); as a rewrite rule it is not
           ; relieved on either instance
           :use ((:instance fn-tcl-stage-preserves-sessionp
                            (inbound (fn-tcl-make-inbound
                                      (fn-tcl-xfer-segment-xfer-id m)
                                      (list (fn-tcl-xfer-segment-data m))
                                      (len (fn-tcl-xfer-segment-data m))
                                      (cadr (fn-tcl-ext-decision (fn-tcl-xfer-segment-ext m)
                                                                 (fn-tcl-transfer-mru s)))))
                            (flags (fn-tcl-xfer-segment-flags m))
                            (xfer-id (fn-tcl-xfer-segment-xfer-id m))
                            (len (len (fn-tcl-xfer-segment-data m))))
                 (:instance fn-tcl-stage-preserves-sessionp
                            (inbound (fn-tcl-make-inbound
                                      (fn-tcl-xfer-segment-xfer-id m)
                                      (cons (fn-tcl-xfer-segment-data m)
                                            (fn-tcl-inbound-staged (fn-tcl-session-inbound s)))
                                      (+ (fn-tcl-inbound-received-len (fn-tcl-session-inbound s))
                                         (len (fn-tcl-xfer-segment-data m)))
                                      (fn-tcl-inbound-total (fn-tcl-session-inbound s))))
                            (flags (fn-tcl-xfer-segment-flags m))
                            (xfer-id (fn-tcl-xfer-segment-xfer-id m))
                            (len (+ (fn-tcl-inbound-received-len (fn-tcl-session-inbound s))
                                    (len (fn-tcl-xfer-segment-data m)))))))))

(defthm fn-tcl-unexpected-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now))
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-unexpected s header now)))))

(defthm fn-tcl-recv-ack-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now)
                (fn-tcl-messagep m (fn-tcl-segment-mru s))
                (equal (fn-tcl-msg-kind m) :xfer-ack)
                (fn-tcl-transferringp (fn-tcl-session-phase s))
                (fn-tcl-session-negotiated s))
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-recv-ack s m now))))
  :hints (("Goal" :in-theory (disable fn-tcl-unexpected)
           ; the rebuild lemma cited for the acknowledged outbound; as a
           ; rewrite rule it is not relieved on this instance
           :use ((:instance fn-tcl-next-preserves-sessionp
                            (phase (fn-tcl-session-phase s)) (inbound (fn-tcl-session-inbound s))
                            (outbound (fn-tcl-make-outbound
                                       (fn-tcl-xfer-ack-xfer-id m)
                                       (fn-tcl-outbound-ref (fn-tcl-session-outbound s))
                                       (fn-tcl-outbound-remaining (fn-tcl-session-outbound s))
                                       (fn-tcl-outbound-total (fn-tcl-session-outbound s))
                                       (fn-tcl-outbound-sent-len (fn-tcl-session-outbound s))
                                       (fn-tcl-xfer-ack-acked-len m)))
                            (term (fn-tcl-session-term s)) (last-tx (fn-tcl-session-last-tx s)))))))

(defthm fn-tcl-recv-refuse-preserves-sessionp
  (implies (fn-tcl-sessionp s)
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-recv-refuse s m now)))))

(defthm fn-tcl-recv-term-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now)
                (not (equal (fn-tcl-session-phase s) :closed)))
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-recv-term s m now)))))

(defthm fn-tcl-terminate-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now))
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-terminate s reason now)))))

(defthm fn-tcl-tcp-closed-preserves-sessionp
  (implies (fn-tcl-sessionp s)
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-tcp-closed s)))))

(defthm fn-tcl-input-error-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now))
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-input-error s header reason now)))))

(defthm fn-tcl-pump-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now))
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-pump s now)))))

(defthm fn-tcl-send-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now) (fn-cbor-octet-listp octets))
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-send s ref octets now))))
  :hints (("Goal" :in-theory (disable fn-tcl-pump))))

(defthm fn-tcl-tick-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-observationp obs))
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-tick s obs)))))

(defthm fn-tcl-step-preserves-sessionp
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now)
                (fn-tcl-messagep m (fn-tcl-segment-mru s)))
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-step s m now))))
  :hints (("Goal" :in-theory (e/d (fn-tcl-step)
                                  (fn-tcl-messagep fn-tcl-touch-rx fn-tcl-segment-mru
                                   fn-tcl-settle fn-tcl-recv-contact fn-tcl-recv-init
                                   fn-tcl-recv-segment fn-tcl-recv-ack fn-tcl-recv-refuse
                                   fn-tcl-recv-term fn-tcl-unexpected))
           :use ((:instance fn-tcl-touch-rx-preserves-sessionp)))))

(defthm fn-tcl-decode-for-yields-message
  (implies (and (fn-tcl-sessionp s) (fn-cbor-octet-listp buf)
                (fn-tcl-parse-okp (fn-tcl-decode-for s buf)))
           (fn-tcl-messagep (fn-tcl-parse-msg (fn-tcl-decode-for s buf))
                            (fn-tcl-segment-mru s)))
  :hints (("Goal" :in-theory (e/d (fn-tcl-sessionp) (fn-tcl-messagep)))))

(defthm fn-tcl-decode-for-rest-octet-listp
  (implies (and (fn-cbor-octet-listp buf)
                (fn-tcl-parse-okp (fn-tcl-decode-for s buf)))
           (fn-cbor-octet-listp (fn-tcl-parse-rest (fn-tcl-decode-for s buf)))))

(defthm fn-tcl-drive-preserves-sessionp
  (implies (fn-tcl-sessionp s)
           (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-drive s buf now))))
  :hints (("Goal" :induct (fn-tcl-drive s buf now)
           :in-theory (e/d (fn-tcl-drive)
                           (fn-tcl-sessionp fn-tcl-messagep fn-tcl-step fn-tcl-decode-for
                            fn-tcl-input-error fn-tcl-segment-mru)))))

; -----------------------------------------------------------------------------
; Executable guard closure.

(local (in-theory (disable fn-tcl-messagep)))

(verify-guards fn-tcl-recv-segment
  :hints (("Goal" :in-theory (e/d (fn-tcl-messagep)
                                  (fn-tcl-refuse fn-tcl-complete fn-tcl-stage
                                   fn-tcl-broken-stream fn-tcl-ext-decision)))))
(verify-guards fn-tcl-recv-ack
  :hints (("Goal" :in-theory (enable fn-tcl-messagep))))
(verify-guards fn-tcl-recv-refuse
  :hints (("Goal" :in-theory (enable fn-tcl-messagep))))
(verify-guards fn-tcl-pump)
(verify-guards fn-tcl-send
  :hints (("Goal" :in-theory (disable fn-tcl-pump) :use fn-tcl-sessionp-facts)))
(verify-guards fn-tcl-tick)
(verify-guards fn-tcl-step
  :hints (("Goal" :in-theory (e/d (fn-tcl-messagep)
                                  (fn-tcl-recv-contact fn-tcl-recv-init fn-tcl-recv-segment
                                   fn-tcl-recv-ack fn-tcl-recv-refuse fn-tcl-recv-term
                                   fn-tcl-unexpected fn-tcl-settle
                                   fn-tcl-touch-rx fn-tcl-segment-mru))
           :use ((:instance fn-tcl-touch-rx-preserves-sessionp)))))
(verify-guards fn-tcl-decode-for)
(verify-guards fn-tcl-drive
  :hints (("Goal" :in-theory (disable fn-tcl-step fn-tcl-decode-for fn-tcl-input-error
                                      fn-tcl-messagep fn-tcl-segment-mru))))

; -----------------------------------------------------------------------------
; Export theory.  Keystones and the list vocabulary stay enabled; every
; recognizer, the initial state and every transition are withdrawn under one
; name, so an includer computes with them but never inherits their unfolding.

(deftheory fn-tcl-session-vocabulary
  '(fn-tcl-paramsp fn-tcl-peer-initp fn-tcl-negotiatedp fn-tcl-inboundp fn-tcl-outboundp
    fn-tcl-rolep fn-tcl-phasep fn-tcl-pre-establishedp fn-tcl-transferringp fn-tcl-termp
    fn-tcl-sessionp fn-tcl-initial-session fn-tcl-next fn-tcl-touch-rx
    fn-tcl-transfer-mru fn-tcl-segment-mru fn-tcl-send-event fn-tcl-fail-live
    fn-tcl-settle fn-tcl-own-contact fn-tcl-own-init fn-tcl-open fn-tcl-recv-contact
    fn-tcl-no-critical-items fn-tcl-negotiate fn-tcl-init-acceptablep fn-tcl-recv-init
    fn-tcl-count-tle fn-tcl-find-tle fn-tcl-critical-unknown-items fn-tcl-ext-decision
    fn-tcl-refuse fn-tcl-complete fn-tcl-stage fn-tcl-broken-stream fn-tcl-recv-segment
    fn-tcl-unexpected fn-tcl-recv-ack fn-tcl-recv-refuse fn-tcl-recv-term
    fn-tcl-terminate fn-tcl-tcp-closed fn-tcl-input-error fn-tcl-with-outbound
    fn-tcl-pump fn-tcl-send
    fn-tcl-tick fn-tcl-step fn-tcl-decode-for fn-tcl-drive
    fn-tcl-touch-rx-fields fn-tcl-ext-decision-ok-total fn-tcl-ext-decision-ok-total-u64
    fn-tcl-drop-octet-listp))

(in-theory (disable fn-tcl-session-vocabulary))
