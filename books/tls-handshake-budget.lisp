; fn: the TLS handshake as an admission decision (lane tls-handshake-budget,
; 2026-09-29; row W2a of COMPLETE-BEFORE-6.6.0; PKT-639; PRF-986).
;
; Ember's ruling (2026-09-29 06:35Z): "we should be modeling and bounding
; this in some way.  We shouldn't require being behind a proxy to be secure
; & resilient."  A TLS handshake on 563 (and a STARTTLS upgrade) costs the
; node CPU and native memory before any credential: this book decides,
; BEFORE the host runs SSL_accept, whether that work is started.
;
; THE LIMITS (HL), three rows of the operator's live configuration
; (`policy set NAME N', books/native-admin.lisp; an absent row is the
; profile's default, books/profile-limits.lisp):
;   N  tls-handshakes-per-source-per-minute  (default 30)
;   L  tls-handshakes-in-flight              (default 16)
;   D  tls-handshake-ms                      (default 5,000: the time model's D)
;
; THE SOURCE is the peer's address as the listener sees it: an IPv4
; address, or an IPv6 address's /64 (one subscriber's allocation, so
; rotating the low 64 bits buys nothing).  Every client behind one carrier
; NAT (CGNAT) or one reverse proxy is ONE source and shares one budget; the
; operator's lever is `policy set tls-handshakes-per-source-per-minute N',
; live.  A source in the trusted range (PRF-211) is exempt from the
; per-source budget and from nothing else.
;
; THE STATE (NEXT TICK STARTED FLIGHT WAITING BUCKETS):
;   NEXT     the next handshake id
;   TICK     the one-second tick of the latest decision (never decreases)
;   STARTED  the handshakes started in TICK
;   FLIGHT   the handshakes in progress: (ID . SOURCE), at most L
;   WAITING  the sockets waiting for a slot (no handshake work, no
;            admission yet), at most 32 x L
;   BUCKETS  per source (LEVEL . STAMP): a token bucket in token-milliseconds;
;            a full bucket holds N x 60,000, a handshake costs 60,000, and it
;            refills N per elapsed millisecond.  An absent source is full;
;            a source whose bucket refilled to full is dropped (so at most
;            the sources that started a handshake in the last minute are
;            rows: at most L x 61).
;
; THE DECISION (fn-hsb-admit), in this order:
;   1. the source's bucket holds less than one handshake  -> refused,
;      reason :handshake-budget (logged by name; never a silent drop);
;   2. L handshakes in flight, or L started this tick     -> :wait (the
;      socket waits unadmitted, at most D), or refused :busy when 32 x L
;      already wait;
;   3. otherwise                                          -> :admit ID: one
;      handshake is charged to the source and to the tick.
; A handshake's end (completed, failed, timed out, closed) releases its slot
; (fn-hsb-done); a waiting socket that leaves unadmitted releases its place
; (fn-hsb-leave).  Every attempt is charged when it starts, whatever its
; outcome: a failed handshake counts against its source (decisions.md item
; 12, PKT-639's remainder).
;
; THE BOUND, independent of the traffic offered:
;   KEYSTONE fn-hsb-steps-keep-the-bound: from a state within the bound,
;     every decision, release and leave keeps it: at most L in flight, at
;     most L started in the tick, at most 32 x L waiting.
;   KEYSTONE fn-hsb-admits-per-tick-are-bounded: over ANY sequence of
;     events (any sources, any order, any number) from ANY state, the
;     handshakes admitted in one tick are at most L (the largest L the
;     events were decided under, so a live change is covered).
;   KEYSTONE fn-hsb-source-admits-are-bounded: from ANY state, over any
;     sequence of events whose times are nondecreasing and within [T0, T1],
;     one untrusted source is admitted at most N + N x (T1 - T0) / 60,000
;     handshakes.
;   fn-hsb-scratch-within-the-reservation: the handshakes in flight hold at
;     most L x *fn-hsb-scratch-octets* of native crypto scratch.
;
; Host callers: host/owner-host.lisp fn-owner-handshake-admit,
; fn-owner-handshake-done, fn-owner-handshake-leave (called by
; host/native/mux.lisp fnn-mux-begin, fnn-mux-request-handshake,
; fnn-mux-start-waiting-handshake, fnn-mux-finish).

(in-package "ACL2")
(include-book "connection-budget") ; public-exposure (the trusted range), heap-figure, profile-limits

; -----------------------------------------------------------------------------
; The limits.

(defconst *fn-hsb-window-ms* 60000)
(defconst *fn-hsb-tick-ms* 1000)
(defconst *fn-hsb-queue-factor* 32)
(defconst *fn-hsb-default-per-source* (fn-profile-limit :tls-handshakes-per-source-per-minute))
(defconst *fn-hsb-default-in-flight* (fn-profile-limit :tls-handshakes-in-flight))
(defconst *fn-hsb-default-deadline-ms* (fn-profile-limit :tls-handshake-ms))

; The native memory a handshake in progress holds beyond its connection's
; established session (books/connection-budget.lisp *fn-cbud-tls-octets*):
; OpenSSL's or LibreSSL's two record buffers (16,709 octets each at their
; defaults) and the handshake's transcript, key exchange and certificate
; chain.  Stated, not measured: measure at convergence (the TLS native
; module's flood, the process's RSS against L).
(defconst *fn-hsb-scratch-octets* 131072)

(defun fn-hsb-pos-or (x default)
  (declare (xargs :guard t))
  (if (posp x) x (if (posp default) default 1)))

(defun fn-hsb-at (i x)
  (declare (xargs :guard t))
  (if (and (natp i) (true-listp x)) (nth i x) nil))

; The operator's rows as the host read them (nil when absent).
(defun fn-hsb-limits (per-source in-flight deadline-ms)
  (declare (xargs :guard t))
  (list (fn-hsb-pos-or per-source *fn-hsb-default-per-source*)
        (fn-hsb-pos-or in-flight *fn-hsb-default-in-flight*)
        (fn-hsb-pos-or deadline-ms *fn-hsb-default-deadline-ms*)))

(defun fn-hsb-lim-rate (hl)
  (declare (xargs :guard t))
  (fn-hsb-pos-or (fn-hsb-at 0 hl) *fn-hsb-default-per-source*))
(defun fn-hsb-lim-in-flight (hl)
  (declare (xargs :guard t))
  (fn-hsb-pos-or (fn-hsb-at 1 hl) *fn-hsb-default-in-flight*))
(defun fn-hsb-lim-deadline (hl)
  (declare (xargs :guard t))
  (fn-hsb-pos-or (fn-hsb-at 2 hl) *fn-hsb-default-deadline-ms*))
(defun fn-hsb-lim-queue (hl)
  (declare (xargs :guard t))
  (* *fn-hsb-queue-factor* (fn-hsb-lim-in-flight hl)))

(defthm fn-hsb-lim-rate-posp (posp (fn-hsb-lim-rate hl)) :rule-classes :type-prescription)
(defthm fn-hsb-lim-in-flight-posp (posp (fn-hsb-lim-in-flight hl)) :rule-classes :type-prescription)
(defthm fn-hsb-lim-deadline-posp (posp (fn-hsb-lim-deadline hl)) :rule-classes :type-prescription)

; -----------------------------------------------------------------------------
; The state.

(defun fn-hsb-make (next tick started flight waiting buckets)
  (declare (xargs :guard t))
  (list next tick started flight waiting buckets))

(defun fn-hsb-next (s) (declare (xargs :guard t)) (nfix (fn-hsb-at 0 s)))
(defun fn-hsb-tick (s) (declare (xargs :guard t)) (nfix (fn-hsb-at 1 s)))
(defun fn-hsb-started (s) (declare (xargs :guard t)) (nfix (fn-hsb-at 2 s)))
(defun fn-hsb-flight (s) (declare (xargs :guard t)) (fn-hsb-at 3 s))
(defun fn-hsb-waiting (s) (declare (xargs :guard t)) (nfix (fn-hsb-at 4 s)))
(defun fn-hsb-buckets (s) (declare (xargs :guard t)) (fn-hsb-at 5 s))

(defun fn-hsb-initial ()
  (declare (xargs :guard t))
  (fn-hsb-make 1 0 0 nil 0 nil))

(defthm fn-hsb-make-accessors
  (and (equal (fn-hsb-next (fn-hsb-make n tk st f w b)) (nfix n))
       (equal (fn-hsb-tick (fn-hsb-make n tk st f w b)) (nfix tk))
       (equal (fn-hsb-started (fn-hsb-make n tk st f w b)) (nfix st))
       (equal (fn-hsb-flight (fn-hsb-make n tk st f w b)) f)
       (equal (fn-hsb-waiting (fn-hsb-make n tk st f w b)) (nfix w))
       (equal (fn-hsb-buckets (fn-hsb-make n tk st f w b)) b)))

; The source: an IPv6 address's /64, any other address itself.
(defun fn-hsb-source-key (address)
  (declare (xargs :guard t))
  (if (and (consp address)
           (equal (car address) :inet6)
           (true-listp (cdr address))
           (<= 8 (len (cdr address))))
      (cons :inet6 (take 8 (cdr address)))
    address))

; -----------------------------------------------------------------------------
; The buckets: an alist SOURCE -> (LEVEL . STAMP).

(defun fn-hsb-lookup (key rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (consp (car rows)) (equal (car (car rows)) key))
          (cdr (car rows))
        (fn-hsb-lookup key (cdr rows)))
    nil))

(defun fn-hsb-cap (rate)
  (declare (xargs :guard t))
  (* (nfix rate) *fn-hsb-window-ms*))

; A row's level at NOW (an absent row is full).  A stamp later than NOW
; refills nothing.
(defun fn-hsb-level (row rate now)
  (declare (xargs :guard t))
  (if (consp row)
      (let* ((stamp (nfix (cdr row)))
             (dt (if (< stamp (nfix now)) (- (nfix now) stamp) 0)))
        (min (fn-hsb-cap rate) (+ (nfix (car row)) (* (nfix rate) dt))))
    (fn-hsb-cap rate)))

(defun fn-hsb-fullp (row rate now)
  (declare (xargs :guard t))
  (<= (fn-hsb-cap rate) (fn-hsb-level row rate now)))

; Drop the rows that refilled to full by NOW (they are the absent row).
(defun fn-hsb-prune (rows rate now)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (consp (car rows))
               (not (fn-hsb-fullp (cdr (car rows)) rate now)))
          (cons (car rows) (fn-hsb-prune (cdr rows) rate now))
        (fn-hsb-prune (cdr rows) rate now))
    nil))

(defun fn-hsb-drop (key rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (consp (car rows)) (equal (car (car rows)) key))
          (fn-hsb-drop key (cdr rows))
        (cons (car rows) (fn-hsb-drop key (cdr rows))))
    nil))

(defun fn-hsb-put (key level stamp rows)
  (declare (xargs :guard t))
  (cons (cons key (cons level stamp)) (fn-hsb-drop key rows)))

; -----------------------------------------------------------------------------
; The flight: (ID . SOURCE) pairs.

(defun fn-hsb-remove (id flight)
  (declare (xargs :guard t))
  (if (consp flight)
      (if (and (consp (car flight)) (equal (car (car flight)) id))
          (fn-hsb-remove id (cdr flight))
        (cons (car flight) (fn-hsb-remove id (cdr flight))))
    nil))

(defthm fn-hsb-len-of-remove
  (<= (len (fn-hsb-remove id flight)) (len flight))
  :rule-classes :linear)

; -----------------------------------------------------------------------------
; THE DECISION THE HOST CALLS (through host/owner-host.lisp
; fn-owner-handshake-admit).  S the state, HL the limits, TRUSTEDP whether
; the source is in the trusted range, ADDRESS the kernel's (FAMILY . OCTETS),
; NOW the recorded milliseconds, QUEUEDP whether the socket is one that
; waited (it leaves the waiting count unless it waits again).
; The result is (VERDICT S' X): (:admit S' ID), (:wait S' nil) or
; (:refuse S' REASON), REASON :handshake-budget or :busy.

(defun fn-hsb-now-tick (now)
  (declare (xargs :guard t))
  (floor (nfix now) *fn-hsb-tick-ms*))

(defthm fn-hsb-now-tick-natp
  (natp (fn-hsb-now-tick now))
  :rule-classes :type-prescription)

(in-theory (disable fn-hsb-now-tick))

(defun fn-hsb-admit (s hl trustedp address now queuedp)
  (declare (xargs :guard t))
  (let* ((rate (fn-hsb-lim-rate hl))
         (lmax (fn-hsb-lim-in-flight hl))
         (key (fn-hsb-source-key address))
         (now-tick (fn-hsb-now-tick now))
         (tick (max (fn-hsb-tick s) now-tick))
         (started (if (< (fn-hsb-tick s) now-tick) 0 (fn-hsb-started s)))
         (next (fn-hsb-next s))
         (flight (fn-hsb-flight s))
         (rows (fn-hsb-buckets s))
         (level (fn-hsb-level (fn-hsb-lookup key rows) rate now))
         (waiting (fn-hsb-waiting s))
         (left (if queuedp (nfix (- waiting 1)) waiting)))
    (cond ((and (not trustedp) (< level *fn-hsb-window-ms*))
           (list :refuse (fn-hsb-make next tick started flight left rows)
                 :handshake-budget))
          ((or (<= lmax (len flight)) (<= lmax started))
           (cond (queuedp
                  (list :wait (fn-hsb-make next tick started flight waiting rows) nil))
                 ((< waiting (fn-hsb-lim-queue hl))
                  (list :wait (fn-hsb-make next tick started flight (+ 1 waiting) rows) nil))
                 (t (list :refuse (fn-hsb-make next tick started flight waiting rows)
                          :busy))))
          (t (list :admit
                   (fn-hsb-make (+ 1 next) tick (+ 1 started)
                                (cons (cons next key) flight) left
                                (if trustedp
                                    rows
                                  (fn-hsb-put key (- level *fn-hsb-window-ms*) (nfix now)
                                              (fn-hsb-prune rows rate now))))
                   next)))))

(defun fn-hsb-verdict (r) (declare (xargs :guard t)) (fn-hsb-at 0 r))
(defun fn-hsb-state (r) (declare (xargs :guard t)) (fn-hsb-at 1 r))
(defun fn-hsb-detail (r) (declare (xargs :guard t)) (fn-hsb-at 2 r))

; A handshake ended (completed, failed, timed out or closed): its slot.
(defun fn-hsb-done (s id)
  (declare (xargs :guard t))
  (fn-hsb-make (fn-hsb-next s) (fn-hsb-tick s) (fn-hsb-started s)
               (fn-hsb-remove id (fn-hsb-flight s))
               (fn-hsb-waiting s) (fn-hsb-buckets s)))

; A waiting socket left without a decision (its deadline, its peer's close).
(defun fn-hsb-leave (s)
  (declare (xargs :guard t))
  (fn-hsb-make (fn-hsb-next s) (fn-hsb-tick s) (fn-hsb-started s)
               (fn-hsb-flight s)
               (nfix (- (fn-hsb-waiting s) 1)) (fn-hsb-buckets s)))

; -----------------------------------------------------------------------------
; The service log's line for a refusal (PKT-640's line, with the source).

(defun fn-hsb-hex-digit (d)
  (declare (xargs :guard t))
  (let ((d (nfix d)))
    (if (< d 10) (code-char (+ 48 d)) (code-char (+ 87 (min d 15))))))

;; Octets as text: decimal joined by SEP (IPv4), or 16-bit hex groups
;; joined by ":" (an IPv6 /64).  Built as characters, then one string.
(defun fn-hsb-decimal-chars (n)
  (declare (xargs :guard t))
  (explode-nonnegative-integer (nfix n) 10 nil))

(defun fn-hsb-octets-chars (octets sep)
  (declare (xargs :guard (characterp sep)))
  (if (consp octets)
      (append (fn-hsb-decimal-chars (car octets))
              (if (consp (cdr octets))
                  (cons sep (fn-hsb-octets-chars (cdr octets) sep))
                nil))
    nil))

(defun fn-hsb-hex4-chars (hi lo)
  (declare (xargs :guard t))
  (let ((v (+ (* 256 (mod (nfix hi) 256)) (mod (nfix lo) 256))))
    (list (fn-hsb-hex-digit (floor v 4096))
          (fn-hsb-hex-digit (mod (floor v 256) 16))
          (fn-hsb-hex-digit (mod (floor v 16) 16))
          (fn-hsb-hex-digit (mod v 16)))))

(defun fn-hsb-hex-chars (octets)
  (declare (xargs :guard t :measure (len octets)))
  (if (and (consp octets) (consp (cdr octets)))
      (append (fn-hsb-hex4-chars (car octets) (cadr octets))
              (if (consp (cddr octets))
                  (cons #\: (fn-hsb-hex-chars (cddr octets)))
                nil))
    nil))

(local
 (defthm fn-hsb-character-listp-of-append
   (implies (and (character-listp a) (character-listp b))
            (character-listp (append a b)))))

(defthm fn-hsb-hex-digit-characterp
  (characterp (fn-hsb-hex-digit d))
  :rule-classes :type-prescription)

(defthm fn-hsb-decimal-chars-character-listp
  (character-listp (fn-hsb-decimal-chars n)))

(defthm fn-hsb-hex4-chars-character-listp
  (character-listp (fn-hsb-hex4-chars hi lo))
  :hints (("Goal" :in-theory (disable fn-hsb-hex-digit floor mod))))

(in-theory (disable fn-hsb-hex-digit fn-hsb-decimal-chars fn-hsb-hex4-chars))

(defthm fn-hsb-octets-chars-character-listp
  (implies (characterp sep) (character-listp (fn-hsb-octets-chars octets sep))))

(defthm fn-hsb-hex-chars-character-listp
  (character-listp (fn-hsb-hex-chars octets)))

(defun fn-hsb-source-text (key)
  (declare (xargs :guard t))
  (cond ((and (consp key) (equal (car key) :inet))
         (coerce (fn-hsb-octets-chars (cdr key) #\.) 'string))
        ((and (consp key) (equal (car key) :inet6))
         (coerce (append (fn-hsb-hex-chars (cdr key)) (coerce "::/64" 'list)) 'string))
        (t "unknown")))

(defconst *fn-hsb-reasons*
  '((:handshake-budget . "handshake-budget") (:busy . "busy")))

(defthm fn-hsb-source-text-stringp
  (stringp (fn-hsb-source-text key))
  :rule-classes :type-prescription)

(in-theory (disable fn-hsb-source-text fn-hsb-source-key))

(defun fn-hsb-refusal-line (reason address)
  (declare (xargs :guard t))
  (let ((word (cdr (assoc-equal reason *fn-hsb-reasons*))))
    (concatenate 'string "tls refused reason=" (if (stringp word) word "other")
                 " source=" (fn-hsb-source-text (fn-hsb-source-key address)))))

; -----------------------------------------------------------------------------
; The bound.

(defun fn-hsb-okp (s hl)
  (declare (xargs :guard t))
  (and (<= (len (fn-hsb-flight s)) (fn-hsb-lim-in-flight hl))
       (<= (fn-hsb-started s) (fn-hsb-lim-in-flight hl))
       (<= (fn-hsb-waiting s) (fn-hsb-lim-queue hl))))

(in-theory (disable fn-hsb-make fn-hsb-next fn-hsb-tick fn-hsb-started fn-hsb-flight
                    fn-hsb-waiting fn-hsb-buckets fn-hsb-lim-rate fn-hsb-lim-in-flight
                    fn-hsb-lim-deadline fn-hsb-level fn-hsb-lookup fn-hsb-prune fn-hsb-put))

; What one decision does, component by component (the admit opened once
; per component, under a small theory).
(defthm fn-hsb-result-accessors
  (and (equal (fn-hsb-verdict (list v x d)) v)
       (equal (fn-hsb-state (list v x d)) x)
       (equal (fn-hsb-detail (list v x d)) d)))


(defthm fn-hsb-admit-tick
  (equal (fn-hsb-tick (fn-hsb-state (fn-hsb-admit s hl trustedp address now queuedp)))
         (max (fn-hsb-tick s) (fn-hsb-now-tick now)))
  :hints (("Goal" :in-theory (e/d (fn-hsb-admit) (fn-hsb-level fn-hsb-lookup fn-hsb-put fn-hsb-prune fn-hsb-cap)))))

(defthm fn-hsb-admit-started
  (equal (fn-hsb-started (fn-hsb-state (fn-hsb-admit s hl trustedp address now queuedp)))
         (+ (if (< (fn-hsb-tick s) (fn-hsb-now-tick now)) 0 (fn-hsb-started s))
            (if (equal (fn-hsb-verdict (fn-hsb-admit s hl trustedp address now queuedp)) :admit)
                1 0)))
  :hints (("Goal" :in-theory (e/d (fn-hsb-admit) (fn-hsb-level fn-hsb-lookup fn-hsb-put fn-hsb-prune fn-hsb-cap)))))

(defthm fn-hsb-admit-flight
  (equal (fn-hsb-flight (fn-hsb-state (fn-hsb-admit s hl trustedp address now queuedp)))
         (if (equal (fn-hsb-verdict (fn-hsb-admit s hl trustedp address now queuedp)) :admit)
             (cons (cons (fn-hsb-next s) (fn-hsb-source-key address)) (fn-hsb-flight s))
           (fn-hsb-flight s)))
  :hints (("Goal" :in-theory (e/d (fn-hsb-admit) (fn-hsb-level fn-hsb-lookup fn-hsb-put fn-hsb-prune fn-hsb-cap)))))

(defthm fn-hsb-admit-admits-under-the-limits
  (implies (equal (fn-hsb-verdict (fn-hsb-admit s hl trustedp address now queuedp)) :admit)
           (and (< (len (fn-hsb-flight s)) (fn-hsb-lim-in-flight hl))
                (< (if (< (fn-hsb-tick s) (fn-hsb-now-tick now)) 0 (fn-hsb-started s))
                   (fn-hsb-lim-in-flight hl))
                (equal (fn-hsb-detail (fn-hsb-admit s hl trustedp address now queuedp))
                       (fn-hsb-next s))))
  :hints (("Goal" :in-theory (e/d (fn-hsb-admit) (fn-hsb-level fn-hsb-lookup fn-hsb-put fn-hsb-prune fn-hsb-cap))))
  :rule-classes nil)

(defthm fn-hsb-admit-waiting
  (implies (<= (fn-hsb-waiting s) (fn-hsb-lim-queue hl))
           (<= (fn-hsb-waiting (fn-hsb-state (fn-hsb-admit s hl trustedp address now queuedp)))
               (fn-hsb-lim-queue hl)))
  :hints (("Goal" :in-theory (e/d (fn-hsb-admit) (fn-hsb-level fn-hsb-lookup fn-hsb-put fn-hsb-prune fn-hsb-cap))))
  :rule-classes :linear)

(defthm fn-hsb-tick-natp (natp (fn-hsb-tick s)) :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-hsb-tick))))
(defthm fn-hsb-started-natp (natp (fn-hsb-started s)) :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-hsb-started))))
(defthm fn-hsb-waiting-natp (natp (fn-hsb-waiting s)) :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-hsb-waiting))))

(in-theory (disable fn-hsb-admit fn-hsb-state fn-hsb-verdict fn-hsb-detail))

(defthm fn-hsb-admit-keeps-the-bound
  (implies (fn-hsb-okp s hl)
           (fn-hsb-okp (fn-hsb-state (fn-hsb-admit s hl trustedp address now queuedp)) hl))
  :hints (("Goal" :use fn-hsb-admit-admits-under-the-limits)))

(defthm fn-hsb-done-keeps-the-bound
  (implies (fn-hsb-okp s hl) (fn-hsb-okp (fn-hsb-done s id) hl)))

(defthm fn-hsb-leave-keeps-the-bound
  (implies (fn-hsb-okp s hl) (fn-hsb-okp (fn-hsb-leave s) hl)))

(defthm fn-hsb-initial-within-the-bound
  (fn-hsb-okp (fn-hsb-initial) hl)
  :hints (("Goal" :in-theory (enable fn-hsb-lim-in-flight))))

; KEYSTONE for host/owner-host.lisp fn-owner-handshake-admit,
; fn-owner-handshake-done and fn-owner-handshake-leave.
(defthm fn-hsb-steps-keep-the-bound
  (implies (fn-hsb-okp s hl)
           (and (fn-hsb-okp (fn-hsb-state (fn-hsb-admit s hl trustedp address now queuedp)) hl)
                (fn-hsb-okp (fn-hsb-done s id) hl)
                (fn-hsb-okp (fn-hsb-leave s) hl)))
  :hints (("Goal" :in-theory (disable fn-hsb-okp fn-hsb-admit fn-hsb-done fn-hsb-leave
                                      fn-hsb-state))))

; An admission is charged: the flight grows by one and holds the id.
(defthm fn-hsb-admit-charges-the-flight
  (implies (equal (fn-hsb-verdict (fn-hsb-admit s hl trustedp address now queuedp)) :admit)
           (and (< (len (fn-hsb-flight s)) (fn-hsb-lim-in-flight hl))
                (equal (fn-hsb-flight (fn-hsb-state (fn-hsb-admit s hl trustedp address now queuedp)))
                       (cons (cons (fn-hsb-next s) (fn-hsb-source-key address))
                             (fn-hsb-flight s)))
                (equal (fn-hsb-detail (fn-hsb-admit s hl trustedp address now queuedp))
                       (fn-hsb-next s))))
  :hints (("Goal" :use fn-hsb-admit-admits-under-the-limits)))

; The native memory: the flight holds at most L handshakes' scratch.
(defthm fn-hsb-scratch-within-the-reservation
  (implies (fn-hsb-okp s hl)
           (<= (* (len (fn-hsb-flight s)) *fn-hsb-scratch-octets*)
               (* (fn-hsb-lim-in-flight hl) *fn-hsb-scratch-octets*)))
  :rule-classes :linear)

; -----------------------------------------------------------------------------
; The events the host's calls make, and the bound over any sequence of them.
;   (:admit HL TRUSTEDP ADDRESS NOW QUEUEDP)   fn-owner-handshake-admit
;   (:done ID)                                 fn-owner-handshake-done
;   (:leave)                                   fn-owner-handshake-leave

(defun fn-hsb-event (s e)
  (declare (xargs :guard t))
  (cond ((and (consp e) (equal (car e) :admit))
         (fn-hsb-state (fn-hsb-admit s (fn-hsb-at 1 e) (fn-hsb-at 2 e) (fn-hsb-at 3 e)
                                     (fn-hsb-at 4 e) (fn-hsb-at 5 e))))
        ((and (consp e) (equal (car e) :done)) (fn-hsb-done s (fn-hsb-at 1 e)))
        ((and (consp e) (equal (car e) :leave)) (fn-hsb-leave s))
        (t s)))

(defun fn-hsb-admittedp (s e)
  (declare (xargs :guard t))
  (and (consp e) (equal (car e) :admit)
       (equal (fn-hsb-verdict (fn-hsb-admit s (fn-hsb-at 1 e) (fn-hsb-at 2 e) (fn-hsb-at 3 e)
                                            (fn-hsb-at 4 e) (fn-hsb-at 5 e)))
              :admit)))

; The handshakes admitted in tick K over the events ES from S.
(defun fn-hsb-admits-in-tick (k s es)
  (declare (xargs :guard t))
  (if (consp es)
      (+ (if (and (fn-hsb-admittedp s (car es))
                  (equal (fn-hsb-tick (fn-hsb-event s (car es))) (nfix k)))
             1 0)
         (fn-hsb-admits-in-tick k (fn-hsb-event s (car es)) (cdr es)))
    0))

; Every admission event decided under an in-flight limit at most LMAX.
(defun fn-hsb-events-under (lmax es)
  (declare (xargs :guard t))
  (if (consp es)
      (and (or (not (and (consp (car es)) (equal (car (car es)) :admit)))
               (<= (fn-hsb-lim-in-flight (fn-hsb-at 1 (car es))) (nfix lmax)))
           (fn-hsb-events-under lmax (cdr es)))
    t))

(defthm fn-hsb-event-tick-monotone
  (<= (fn-hsb-tick s) (fn-hsb-tick (fn-hsb-event s e)))
  :rule-classes :linear)

(defthm fn-hsb-event-started-in-tick
  (implies (and (consp e) (equal (car e) :admit)
                (equal (fn-hsb-tick (fn-hsb-event s e)) (fn-hsb-tick s)))
           (equal (fn-hsb-started (fn-hsb-event s e))
                  (+ (fn-hsb-started s) (if (fn-hsb-admittedp s e) 1 0)))))

(defthm fn-hsb-event-started-in-a-new-tick
  (implies (< (fn-hsb-tick s) (fn-hsb-tick (fn-hsb-event s e)))
           (equal (fn-hsb-started (fn-hsb-event s e))
                  (if (fn-hsb-admittedp s e) 1 0))))

(defthm fn-hsb-event-started-unchanged-otherwise
  (implies (not (and (consp e) (equal (car e) :admit)))
           (and (equal (fn-hsb-started (fn-hsb-event s e)) (fn-hsb-started s))
                (equal (fn-hsb-tick (fn-hsb-event s e)) (fn-hsb-tick s))
                (not (fn-hsb-admittedp s e)))))

(defthm fn-hsb-admitted-under-the-limit
  (implies (fn-hsb-admittedp s e)
           (< (if (equal (fn-hsb-tick (fn-hsb-event s e)) (fn-hsb-tick s))
                  (fn-hsb-started s)
                0)
              (fn-hsb-lim-in-flight (fn-hsb-at 1 e))))
  :hints (("Goal" :use ((:instance fn-hsb-admit-admits-under-the-limits
                                   (hl (fn-hsb-at 1 e)) (trustedp (fn-hsb-at 2 e))
                                   (address (fn-hsb-at 3 e)) (now (fn-hsb-at 4 e))
                                   (queuedp (fn-hsb-at 5 e)))))))

(in-theory (disable fn-hsb-event fn-hsb-admittedp))

;; The room left in tick K from S: what S already started in it (0 before
;; K; the whole limit once K is past, when nothing more is admitted in it).
(defun fn-hsb-used (k s lmax)
  (declare (xargs :guard t))
  (cond ((equal (fn-hsb-tick s) (nfix k)) (min (fn-hsb-started s) (nfix lmax)))
        ((< (fn-hsb-tick s) (nfix k)) 0)
        (t (nfix lmax))))

(defun fn-hsb-event-under (lmax e)
  (declare (xargs :guard t))
  (or (not (and (consp e) (equal (car e) :admit)))
      (<= (fn-hsb-lim-in-flight (fn-hsb-at 1 e)) (nfix lmax))))

(local
 (defthm fn-hsb-event-step
   (implies (fn-hsb-event-under lmax e)
            (<= (+ (if (and (fn-hsb-admittedp s e)
                            (equal (fn-hsb-tick (fn-hsb-event s e)) (nfix k)))
                       1 0)
                   (fn-hsb-used k s lmax))
                (fn-hsb-used k (fn-hsb-event s e) lmax)))
   :hints (("Goal" :use ((:instance fn-hsb-admitted-under-the-limit)
                         (:instance fn-hsb-event-started-in-tick)
                         (:instance fn-hsb-event-started-in-a-new-tick)
                         (:instance fn-hsb-event-started-unchanged-otherwise)
                         (:instance fn-hsb-event-tick-monotone))))
   :rule-classes nil))

(local
 (defthm fn-hsb-used-bounded
   (<= (fn-hsb-used k s lmax) (nfix lmax))
   :rule-classes :linear))

(defthm fn-hsb-events-under-opens
  (equal (fn-hsb-events-under lmax es)
         (if (consp es)
             (and (fn-hsb-event-under lmax (car es))
                  (fn-hsb-events-under lmax (cdr es)))
           t))
  :rule-classes :definition)

(local
 (defthm fn-hsb-admits-in-tick-general
   (implies (fn-hsb-events-under lmax es)
            (<= (+ (fn-hsb-admits-in-tick k s es) (fn-hsb-used k s lmax))
                (nfix lmax)))
   :hints (("Goal" :induct (fn-hsb-admits-in-tick k s es)
                   :in-theory (disable fn-hsb-used fn-hsb-event-under))
           ("Subgoal *1/1" :use ((:instance fn-hsb-event-step (e (car es))))))
   :rule-classes nil))

; KEYSTONE: the handshakes admitted in any one tick, over any sequence of
; events from any state, are at most L (the largest in-flight limit the
; admissions were decided under).
(defthm fn-hsb-admits-per-tick-are-bounded
  (implies (fn-hsb-events-under lmax es)
           (<= (fn-hsb-admits-in-tick k s es) (nfix lmax)))
  :hints (("Goal" :use fn-hsb-admits-in-tick-general
                  :in-theory (disable fn-hsb-admits-in-tick fn-hsb-events-under)))
  :rule-classes :linear)

; -----------------------------------------------------------------------------
; The per-source bound.  Over events whose times are nondecreasing within
; [T0, T1], decided at one rate N, a source is admitted at most
; N + N x (T1 - T0) / 60,000 handshakes (the bucket's burst and its
; refill), whatever else is offered, from ANY state: a bucket never holds
; more than N x 60,000.  The invariant: 60,000 x (the source's admissions
; from now on) <= (its bucket's level now) + N x (T1 - now).

; The source's bucket level at NOW in the rows.
(defun fn-hsb-eff (rows key rate now)
  (declare (xargs :guard t))
  (fn-hsb-level (fn-hsb-lookup key rows) rate now))

(local (in-theory (enable fn-hsb-lookup fn-hsb-prune fn-hsb-put fn-hsb-drop)))

(local
 (defthm fn-hsb-lookup-of-drop
   (equal (fn-hsb-lookup key (fn-hsb-drop k2 rows))
          (if (equal key k2) nil (fn-hsb-lookup key rows)))))

(local
 (defthm fn-hsb-lookup-of-put
   (equal (fn-hsb-lookup key (fn-hsb-put k2 lv st rows))
          (if (equal key k2) (cons lv st) (fn-hsb-lookup key rows)))))

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-hsb-times-monotone
   (implies (and (natp n) (natp a) (natp b) (<= a b))
            (<= (* n a) (* n b)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes :linear))

(local
 (defthm fn-hsb-level-at-most-cap
   (<= (fn-hsb-level row rate now) (fn-hsb-cap rate))
   :hints (("Goal" :in-theory (enable fn-hsb-level)))
   :rule-classes :linear))

(local
 (defthm fn-hsb-level-natp
   (natp (fn-hsb-level row rate now))
   :hints (("Goal" :in-theory (enable fn-hsb-level fn-hsb-cap)))
   :rule-classes :type-prescription))

(local
 (defthm fn-hsb-eff-at-most-cap
   (<= (fn-hsb-eff rows key rate now) (fn-hsb-cap rate))
   :rule-classes :linear))

(local
 (defthm fn-hsb-eff-natp
   (natp (fn-hsb-eff rows key rate now))
   :rule-classes :type-prescription))

; Refill: from TT to NOW >= TT any row's level rises by at most N x (NOW - TT).
(local
 (defun fn-hsb-dt (stamp now)
   (if (< (nfix stamp) (nfix now)) (- (nfix now) (nfix stamp)) 0)))

(local
 (defthm fn-hsb-dt-grows
   (implies (and (natp tt) (natp now) (<= tt now))
            (and (natp (fn-hsb-dt st now))
                 (natp (fn-hsb-dt st tt))
                 (<= (fn-hsb-dt st now) (+ (fn-hsb-dt st tt) (- now tt)))))
   :rule-classes nil))

(local
 (defthm fn-hsb-level-by-dt
   (equal (fn-hsb-level row rate now)
          (if (consp row)
              (min (fn-hsb-cap rate)
                   (+ (nfix (car row)) (* (nfix rate) (fn-hsb-dt (cdr row) now))))
            (fn-hsb-cap rate)))
   :hints (("Goal" :in-theory (enable fn-hsb-level)))))

(local
 (defthm fn-hsb-dt-self
   (implies (<= (nfix now) (nfix st)) (equal (fn-hsb-dt st now) 0))
   :hints (("Goal" :in-theory (enable fn-hsb-dt)))))

(local (in-theory (disable fn-hsb-dt)))

(local
 (defthm fn-hsb-level-refill
   (implies (and (natp tt) (natp now) (<= tt now) (natp rate))
            (<= (fn-hsb-level row rate now)
                (+ (fn-hsb-level row rate tt) (* rate (- now tt)))))
   :hints (("Goal" :in-theory (disable fn-hsb-cap)
                   :use ((:instance fn-hsb-dt-grows (st (cdr row)))
                         (:instance fn-hsb-times-monotone (n rate)
                                    (a (fn-hsb-dt (cdr row) now))
                                    (b (+ (fn-hsb-dt (cdr row) tt) (- now tt))))
                         (:instance fn-hsb-times-monotone (n rate) (a tt) (b now)))))
   :rule-classes nil))

(local
 (defthm fn-hsb-eff-refill
   (implies (and (natp tt) (natp now) (<= tt now) (natp rate))
            (<= (fn-hsb-eff rows key rate now)
                (+ (fn-hsb-eff rows key rate tt) (* rate (- now tt)))))
   :hints (("Goal" :use ((:instance fn-hsb-level-refill (row (fn-hsb-lookup key rows))))))
   :rule-classes nil))

; Pruning never raises a level: a dropped row was full.
(local
 (defthm fn-hsb-eff-of-prune
   (<= (fn-hsb-eff (fn-hsb-prune rows rate now) key rate now)
       (fn-hsb-eff rows key rate now))
   :hints (("Goal" :induct (fn-hsb-prune rows rate now)
                   :in-theory (e/d (fn-hsb-fullp) (fn-hsb-level fn-hsb-level-by-dt fn-hsb-cap))))
   :rule-classes :linear))

(local
 (defthm fn-hsb-level-of-fresh
   (implies (and (natp lv) (natp now) (<= lv (fn-hsb-cap rate)))
            (equal (fn-hsb-level (cons lv now) rate now) lv))))

(local
 (defthm fn-hsb-eff-of-put
   (implies (and (natp lv) (natp now) (<= lv (fn-hsb-cap rate)))
            (equal (fn-hsb-eff (fn-hsb-put k2 lv now rows) key rate now)
                   (if (equal key k2) lv (fn-hsb-eff rows key rate now))))
   :hints (("Goal" :in-theory (disable fn-hsb-put fn-hsb-cap)))))

(in-theory (disable fn-hsb-eff))

; What an admission does to the buckets.
(defthm fn-hsb-buckets-of-admit
  (equal (fn-hsb-buckets (fn-hsb-state (fn-hsb-admit s hl trustedp address now queuedp)))
         (if (and (equal (fn-hsb-verdict (fn-hsb-admit s hl trustedp address now queuedp)) :admit)
                  (not trustedp))
             (fn-hsb-put (fn-hsb-source-key address)
                         (- (fn-hsb-eff (fn-hsb-buckets s) (fn-hsb-source-key address)
                                        (fn-hsb-lim-rate hl) now)
                            *fn-hsb-window-ms*)
                         (nfix now)
                         (fn-hsb-prune (fn-hsb-buckets s) (fn-hsb-lim-rate hl) now))
           (fn-hsb-buckets s)))
  :hints (("Goal" :in-theory (e/d (fn-hsb-admit fn-hsb-eff) (fn-hsb-level fn-hsb-level-by-dt fn-hsb-lookup fn-hsb-put fn-hsb-prune fn-hsb-cap)))))

(defthm fn-hsb-admit-needs-a-handshake-of-level
  (implies (and (equal (fn-hsb-verdict (fn-hsb-admit s hl trustedp address now queuedp)) :admit)
                (not trustedp))
           (<= *fn-hsb-window-ms*
               (fn-hsb-eff (fn-hsb-buckets s) (fn-hsb-source-key address) (fn-hsb-lim-rate hl) now)))
  :hints (("Goal" :in-theory (e/d (fn-hsb-admit fn-hsb-eff) (fn-hsb-level fn-hsb-level-by-dt fn-hsb-lookup fn-hsb-put fn-hsb-prune fn-hsb-cap))))
  :rule-classes :linear)

(defthm fn-hsb-buckets-of-done-leave
  (and (equal (fn-hsb-buckets (fn-hsb-done s id)) (fn-hsb-buckets s))
       (equal (fn-hsb-buckets (fn-hsb-leave s)) (fn-hsb-buckets s))))

(in-theory (disable fn-hsb-admit fn-hsb-state fn-hsb-verdict fn-hsb-detail))

; The handshakes admitted from untrusted source KEY over the events ES.
(defun fn-hsb-source-admits (key s es)
  (declare (xargs :guard t))
  (if (consp es)
      (+ (if (and (fn-hsb-admittedp s (car es))
                  (not (fn-hsb-at 2 (car es)))
                  (equal (fn-hsb-source-key (fn-hsb-at 3 (car es))) key))
             1 0)
         (fn-hsb-source-admits key (fn-hsb-event s (car es)) (cdr es)))
    0))

; Every admission event decided at rate N, at a time within [PREV, T1] and
; no earlier than the one before it.
(defun fn-hsb-events-timed (es prev t1 n)
  (declare (xargs :guard t))
  (if (consp es)
      (if (and (consp (car es)) (equal (car (car es)) :admit))
          (and (natp (fn-hsb-at 4 (car es)))
               (<= (nfix prev) (fn-hsb-at 4 (car es)))
               (<= (fn-hsb-at 4 (car es)) (nfix t1))
               (equal (fn-hsb-lim-rate (fn-hsb-at 1 (car es))) n)
               (fn-hsb-events-timed (cdr es) (fn-hsb-at 4 (car es)) t1 n))
        (fn-hsb-events-timed (cdr es) prev t1 n))
    t))

; One admission event, for source KEY: its admission is paid from the level.
(local
 (defthm fn-hsb-event-source-step
   (implies (and (consp e) (equal (car e) :admit)
                 (equal (fn-hsb-at 4 e) now) (natp now)
                 (equal (fn-hsb-lim-rate (fn-hsb-at 1 e)) n))
            (<= (+ (if (and (fn-hsb-admittedp s e)
                            (not (fn-hsb-at 2 e))
                            (equal (fn-hsb-source-key (fn-hsb-at 3 e)) key))
                       *fn-hsb-window-ms* 0)
                   (fn-hsb-eff (fn-hsb-buckets (fn-hsb-event s e)) key n now))
                (fn-hsb-eff (fn-hsb-buckets s) key n now)))
   :hints (("Goal" :in-theory (e/d (fn-hsb-event fn-hsb-admittedp)
                                   (fn-hsb-put fn-hsb-prune fn-hsb-lookup fn-hsb-level fn-hsb-cap))
                   :use ((:instance fn-hsb-admit-needs-a-handshake-of-level
                                    (hl (fn-hsb-at 1 e)) (trustedp (fn-hsb-at 2 e))
                                    (address (fn-hsb-at 3 e)) (now (fn-hsb-at 4 e))
                                    (queuedp (fn-hsb-at 5 e)))
                         (:instance fn-hsb-eff-at-most-cap (rows (fn-hsb-buckets s))
                                    (key (fn-hsb-source-key (fn-hsb-at 3 e))) (rate n)))))
   :rule-classes nil))

(local
 (defthm fn-hsb-event-other-step
   (implies (not (and (consp e) (equal (car e) :admit)))
            (and (equal (fn-hsb-buckets (fn-hsb-event s e)) (fn-hsb-buckets s))
                 (not (fn-hsb-admittedp s e))))
   :hints (("Goal" :in-theory (enable fn-hsb-event fn-hsb-admittedp)))))

(local
 (defthm fn-hsb-source-admit-case
   (implies (and (natp tt) (consp e) (equal (car e) :admit)
                 (natp now) (equal (fn-hsb-at 4 e) now) (<= tt now)
                 (equal (fn-hsb-lim-rate (fn-hsb-at 1 e)) n) (natp n)
                 (<= (* *fn-hsb-window-ms* c)
                     (+ (fn-hsb-eff (fn-hsb-buckets (fn-hsb-event s e)) key n now)
                        (* n (- t1 now)))))
            (<= (* *fn-hsb-window-ms*
                   (+ (if (and (fn-hsb-admittedp s e)
                               (not (fn-hsb-at 2 e))
                               (equal (fn-hsb-source-key (fn-hsb-at 3 e)) key))
                          1 0)
                      c))
                (+ (fn-hsb-eff (fn-hsb-buckets s) key n tt) (* n (- t1 tt)))))
   :hints (("Goal" :in-theory (disable fn-hsb-event fn-hsb-admittedp)
                   :use ((:instance fn-hsb-event-source-step)
                         (:instance fn-hsb-eff-refill (rows (fn-hsb-buckets s)) (rate n)))))
   :rule-classes nil))

(local
 (defun fn-hsb-source-induct (s es tt)
   (declare (xargs :verify-guards nil))
   (if (consp es)
       (if (and (consp (car es)) (equal (car (car es)) :admit))
           (fn-hsb-source-induct (fn-hsb-event s (car es)) (cdr es) (fn-hsb-at 4 (car es)))
         (fn-hsb-source-induct (fn-hsb-event s (car es)) (cdr es) tt))
     (list s tt))))

(local
 (defthm fn-hsb-source-admits-general
   (implies (and (natp tt) (fn-hsb-events-timed es tt t1 n) (natp t1) (<= tt t1) (natp n))
            (<= (* *fn-hsb-window-ms* (fn-hsb-source-admits key s es))
                (+ (fn-hsb-eff (fn-hsb-buckets s) key n tt) (* n (- t1 tt)))))
   :hints (("Goal" :induct (fn-hsb-source-induct s es tt)
                   :in-theory (disable fn-hsb-event fn-hsb-admittedp))
           ("Subgoal *1/1" :use ((:instance fn-hsb-source-admit-case (e (car es))
                                            (now (fn-hsb-at 4 (car es)))
                                            (c (fn-hsb-source-admits key (fn-hsb-event s (car es))
                                                                     (cdr es))))))
           ("Subgoal *1/2" :use ((:instance fn-hsb-event-other-step (e (car es)))))
           ("Subgoal *1/3" :use ((:instance fn-hsb-times-monotone (n n) (a tt) (b t1)))))
   :rule-classes nil))

(local
 (defthm fn-hsb-events-timed-of-nfix
   (equal (fn-hsb-events-timed es (nfix t0) (nfix t1) n)
          (fn-hsb-events-timed es t0 t1 n))))

; KEYSTONE: from ANY state, over any events whose times are nondecreasing
; within [T0, T1], decided at rate N, one untrusted source is admitted at
; most N + N x (T1 - T0) / 60,000 handshakes (stated in token-milliseconds;
; the times are the recorded clock's naturals, as fn-hsb-events-timed reads
; them).
(defthm fn-hsb-source-admits-are-bounded
  (implies (and (fn-hsb-events-timed es t0 t1 n) (<= (nfix t0) (nfix t1)) (natp n))
           (<= (* *fn-hsb-window-ms* (fn-hsb-source-admits key s es))
               (+ (* n *fn-hsb-window-ms*) (* n (- (nfix t1) (nfix t0))))))
  :hints (("Goal" :in-theory (disable fn-hsb-source-admits fn-hsb-events-timed)
                  :use ((:instance fn-hsb-source-admits-general (tt (nfix t0)) (t1 (nfix t1)))
                        (:instance fn-hsb-events-timed-of-nfix)
                        (:instance fn-hsb-eff-at-most-cap (rows (fn-hsb-buckets s)) (rate n)
                                   (now (nfix t0)))))
          ("Goal'" :in-theory (enable fn-hsb-cap))))
