; fn: the limits of a public reader port (PRF-161, NNT-031).
;
; A node whose listener faces strangers must answer them within limits that
; ACL2 decides: how many connections it holds, how many from one address,
; how much work one address may start per quantum, how long a silent or
; trickling connection may hold a slot, how many failed logins one address
; may try, how fast one principal may post, and what an unauthenticated
; session may do at all.  This book owns every one of those decisions.  The
; host counts nothing: it hands this book the connection's source address,
; its connection id, the owner's monotonic clock and the octets the served
; step already rendered, and does what the answer says (send the 400, wait,
; close).  The design, the threat model and the operator's packet are
; planning/evidence/public-exposure-2026-09-26.md section 1.
;
; THE LIMITS ARE CONFIGURATION ROWS.  Each is a `:set-limit' row of the typed
; configuration value (books/config), keyed by its slot and "" exactly as
; books/reclaim-rule.lisp keys the retention rule, written by the ordinary
; reconfiguration record, replayed by the ordinary fold and applied live by
; the ordinary owner path (`fn operator CONFIG policy set SLOT N',
; books/native-admin.lisp).  The anonymous policy is the `:set-policy' row
; `anonymous'.  A row that is absent takes the default of the listener's
; exposure: a loopback listener keeps the behaviour every store had before
; this book (no per-address limit beyond the total, no rate, no idle close,
; anonymous as `[auth] required' says); a listener off loopback takes the
; public defaults below.  `fn-exp-limits' is the one reader.
;
;   exposure-connections        connections held at once (never above one
;                               fewer than the run's max_connections, which
;                               fn-own-open still enforces: the last is the
;                               operator's, `fn-exp-socket-cap')
;   exposure-per-address       connections held at once from one address
;   exposure-steps-per-second  served steps one address may start per
;                               1000 ms quantum; a step is one fn-owner-chunk
;                               over at most one host read (D27: work, not
;                               data).  Exhausted, the connection WAITS for
;                               the next quantum: backpressure, never a
;                               refusal and never a truncation
;   exposure-idle-seconds       RFC 3977 section 3.1's autologout timer after
;                               the first answered command
;   exposure-first-seconds      the shorter wait section 3.1 permits for the
;                               first command
;   exposure-auth-failures      481 answers one address may collect per
;                               minute before its connections close with 400
;                               and new ones are refused 400
;   exposure-posts-per-minute   submissions one authenticated principal may
;                               make per minute; past it the principal's
;                               connections wait for the next minute
;   policy `anonymous'          `none' (an unauthenticated session is gated
;                               480 on every reader and posting command) or
;                               `open' (as `[auth] required' says).  It only
;                               ever tightens: `[auth] required' is never
;                               weakened by `open'.
;
; The subjects the host calls (host/owner-host.lisp):
;   fn-exp-open      fn-owner-exposure-open (host/native/owner.lisp
;                    fnn-owner-serve-client, at accept)
;   fn-exp-charge    fn-owner-exposure-charge (fnn-owner-serve-client, before
;                    every served step)
;   fn-exp-observe   fn-owner-exposure-observe (fnn-owner-handle-chunk, after
;                    every served step, under the owner mutex)
;   fn-exp-idle      fn-owner-exposure-idle (fnn-owner-serve-client, on every
;                    receive timeout)
;   fn-exp-release   fn-owner-exposure-release (fnn-owner-serve-client's
;                    unwind, beside fn-owner-close)
;   fn-exp-health-lines  host/native-live-status-host.lisp
;                    fn-native-live-status-host-answer (the `health' verb)
;
; Keystones: fn-exp-open-admits-within-the-limits-in-force,
; fn-exp-charge-bounds-steps-per-quantum,
; fn-exp-anonymous-none-gates-every-restricted-command,
; fn-exp-limits-never-drop-a-connection, fn-exp-idle-closes-only-silence.
; Teeth: tests/acl2/public-exposure-tests.lisp.
;
; This book owns the prefix `fn-exp-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "public-exposure-rows")
(include-book "owner-config")
(include-book "native-config")

; -----------------------------------------------------------------------------
; Slots and defaults

; The public defaults: what a listener off loopback gets with no row.  They
; are the packet's recommendation, not ceilings on anything stored.  RFC 3977
; section 3.1 asks for an autologout of at least three minutes; ten is used.
(defconst *fn-exp-public-per-address* 8)
(defconst *fn-exp-public-steps* 64)
(defconst *fn-exp-public-idle* 600)
(defconst *fn-exp-public-first* 60)
(defconst *fn-exp-public-auth-failures* 10)
(defconst *fn-exp-public-posts* 60)

(defconst *fn-exp-quantum-ms* 1000)
(defconst *fn-exp-window-ms* 60000)
; RFC 3977 section 3.1: "the receipt of any significant amount of data from a
; client that is sending a multi-line data block SHOULD suffice to reset the
; autologout timer".  Significant is one initial line's worth, accumulated.
(defconst *fn-exp-significant-octets* 512)

; -----------------------------------------------------------------------------
; Total list access

(defun fn-exp-at (i x)
  (declare (xargs :guard t :measure (acl2-count x)))
  (if (consp x)
      (if (or (not (integerp i)) (<= i 0)) (car x) (fn-exp-at (1- i) (cdr x)))
    nil))

(defun fn-exp-nat (i x)
  (declare (xargs :guard t))
  (nfix (fn-exp-at i x)))

; -----------------------------------------------------------------------------
; The limits in force

(defun fn-exp-row (v slot)
  ; The limit row `:set-limit' writes for SLOT, as a natural, or nil.
  (declare (xargs :guard t))
  (let ((row (fn-cfg-row-lookup (fn-cfg-limits v) slot)))
    (if (and (consp row) (equal (fn-cfg-row-b row) ""))
        (nfix (fn-cfg-limit-value row))
      nil)))

(defun fn-exp-or (row public publicp legacy)
  (declare (xargs :guard t))
  (cond ((natp row) row)
        (publicp public)
        (t legacy)))

(defun fn-exp-anonymous-word (v)
  (declare (xargs :guard t))
  (let ((row (fn-cfg-row-lookup (fn-cfg-policies v) *fn-exp-policy-slot*)))
    (if (consp row) (fn-cfg-policy-id row) nil)))

; Only ever tightens: `[auth] required' or a public listener with no row is
; :none; `open' is honoured only where neither holds; any other word is :none.
(defun fn-exp-anonymous (v publicp auth-required)
  (declare (xargs :guard t))
  (let ((word (fn-exp-anonymous-word v)))
    (cond (auth-required :none)
          ((equal word "open") :open)
          ((equal word "none") :none)
          ((null word) (if publicp :none :open))
          (t :none))))

(defun fn-exp-lim-make (total per-address steps idle first auth-failures posts
                              anonymous)
  (declare (xargs :guard t))
  (list :fn-exp-limits total per-address steps idle first auth-failures posts
        anonymous))

(defun fn-exp-lim-total (l) (declare (xargs :guard t)) (fn-exp-nat 1 l))
(defun fn-exp-lim-per-address (l) (declare (xargs :guard t)) (fn-exp-nat 2 l))
(defun fn-exp-lim-steps (l) (declare (xargs :guard t)) (fn-exp-nat 3 l))
(defun fn-exp-lim-idle (l) (declare (xargs :guard t)) (fn-exp-nat 4 l))
(defun fn-exp-lim-first (l) (declare (xargs :guard t)) (fn-exp-nat 5 l))
(defun fn-exp-lim-auth-failures (l) (declare (xargs :guard t)) (fn-exp-nat 6 l))
(defun fn-exp-lim-posts (l) (declare (xargs :guard t)) (fn-exp-nat 7 l))
(defun fn-exp-lim-anonymous (l)
  (declare (xargs :guard t))
  (if (equal (fn-exp-at 8 l) :open) :open :none))

; The connections sockets may hold: one fewer than the owner's bound, so
; the operator's live reconfiguration, which stages through a private
; logical connection of its own (host/native/admin.lisp
; fnn-owner-live-reconfigure-locked), always finds one.  Found on hbox: with
; the reader port full, `policy set' was refused :no-such-connection, so a
; flood locked the operator out of the very limits that answer it
; (planning/evidence/public-exposure-2026-09-26.md section 4).  A bound of
; one keeps its one connection for sockets, as before.
(defun fn-exp-socket-cap (max-conns)
  (declare (xargs :guard t))
  (if (< 1 (nfix max-conns)) (1- (nfix max-conns)) (nfix max-conns)))

; The one reader of the rows.  V is the live configuration value, MAX-CONNS
; the run's max_connections, PUBLICP ACL2's reading of the listener
; (`fn-exp-address-publicp'), AUTH-REQUIRED the `[auth] required' bit.
(defun fn-exp-limits (v max-conns publicp auth-required)
  (declare (xargs :guard t))
  (let* ((cap (fn-exp-socket-cap max-conns))
         (row (fn-exp-row v *fn-exp-slot-connections*))
         (total (if (natp row) (min row cap) cap)))
    (fn-exp-lim-make
     total
     (fn-exp-or (fn-exp-row v *fn-exp-slot-per-address*)
                *fn-exp-public-per-address* publicp total)
     (fn-exp-or (fn-exp-row v *fn-exp-slot-steps*) *fn-exp-public-steps* publicp 0)
     (fn-exp-or (fn-exp-row v *fn-exp-slot-idle*) *fn-exp-public-idle* publicp 0)
     (fn-exp-or (fn-exp-row v *fn-exp-slot-first*) *fn-exp-public-first* publicp 0)
     (fn-exp-or (fn-exp-row v *fn-exp-slot-auth-failures*)
                *fn-exp-public-auth-failures* publicp 0)
     (fn-exp-or (fn-exp-row v *fn-exp-slot-posts*) *fn-exp-public-posts* publicp 0)
     (fn-exp-anonymous v publicp auth-required))))

; Whether the listener faces anything but this host: FAMILY and ADDRESS are
; ACL2's projection of the configured listener host (books/native-config.lisp
; fn-native-config-listener-address), which the owner run bound.  Anything
; outside 127.0.0.0/8 and ::1 is public.  No address (the low-level test
; entry, which binds loopback by default) is loopback.  A reverse proxy on
; loopback makes every client one loopback address: the packet says what
; that costs.
(defun fn-exp-address-publicp (family address)
  (declare (xargs :guard t))
  (cond ((null address) nil)
        ((and (equal family :inet) (consp address) (equal (car address) 127)) nil)
        ((and (equal family :inet6)
              (equal address *fn-ncfg-listener-ipv6-loopback*))
         nil)
        (t t)))

; -----------------------------------------------------------------------------
; The anonymous policy, as the AUTHINFO configuration pinned at open
;
; Under :none the configuration a connection pins requires authentication,
; so books/nntp-auth.lisp's gate answers 480 to every reader and posting
; command (fn-auth-restricted-keywordp) of an unauthenticated session; the
; credentials, the protected-only bit and TLS availability are the
; operator's.  A malformed operator configuration pins a well-formed one
; that requires authentication and offers nothing: fn-auth-open-session
; would otherwise replace it with the open profile, which requires nothing.
(defun fn-exp-pinned-acfg (acfg lim)
  (declare (xargs :guard t))
  (cond ((not (equal (fn-exp-lim-anonymous lim) :none)) acfg)
        ((fn-auth-configp acfg)
         (fn-auth-make-config t (fn-auth-config-protected-onlyp acfg)
                              (fn-auth-config-tls-availablep acfg)
                              (fn-auth-config-creds acfg)))
        (t (fn-auth-make-config t nil nil nil))))

; -----------------------------------------------------------------------------
; The exposure state
;
; (:fn-exp CONNS RATES FAILS POSTS COUNTERS)
;   CONNS     one entry per connection the owner opened through fn-exp-open:
;             (ID ADDRESS LAST ANSWERED PRINCIPAL PENDING) -- LAST the
;             monotonic ms of the last progress, ANSWERED whether a command
;             has been answered, PRINCIPAL the session's subject after the
;             last step, PENDING the octets consumed since the last progress
;   RATES     (ADDRESS QUANTUM STEPS), only for addresses with a connection
;   FAILS     (ADDRESS WINDOW COUNT), the current minute's 481 answers
;   POSTS     (PRINCIPAL WINDOW COUNT), the current minute's submissions
;   COUNTERS  (ADMITTED BUSY PER-ADDRESS AUTH DEFERRED IDLE AUTH-CLOSED
;              RECENT-WINDOW RECENT)
; Every list is pruned to the current window when it is touched, so none
; holds more than one entry per address or principal active in it.

(defun fn-exp-make (conns rates fails posts counters)
  (declare (xargs :guard t))
  (list :fn-exp conns rates fails posts counters))

(defun fn-exp-conns (xs) (declare (xargs :guard t)) (fn-exp-at 1 xs))
(defun fn-exp-rates (xs) (declare (xargs :guard t)) (fn-exp-at 2 xs))
(defun fn-exp-fails (xs) (declare (xargs :guard t)) (fn-exp-at 3 xs))
(defun fn-exp-posts (xs) (declare (xargs :guard t)) (fn-exp-at 4 xs))
(defun fn-exp-counters (xs) (declare (xargs :guard t)) (fn-exp-at 5 xs))

(defun fn-exp-initial ()
  (declare (xargs :guard t))
  (fn-exp-make nil nil nil nil (list 0 0 0 0 0 0 0 0 0)))

(defun fn-exp-entry (id address last answered principal pending)
  (declare (xargs :guard t))
  (list id address last answered principal pending))

(defun fn-exp-entry-id (e) (declare (xargs :guard t)) (fn-exp-at 0 e))
(defun fn-exp-entry-address (e) (declare (xargs :guard t)) (fn-exp-at 1 e))
(defun fn-exp-entry-last (e) (declare (xargs :guard t)) (fn-exp-nat 2 e))
(defun fn-exp-entry-answered (e) (declare (xargs :guard t)) (fn-exp-at 3 e))
(defun fn-exp-entry-principal (e) (declare (xargs :guard t)) (fn-exp-at 4 e))
(defun fn-exp-entry-pending (e) (declare (xargs :guard t)) (fn-exp-nat 5 e))

(defun fn-exp-find (id conns)
  (declare (xargs :guard t))
  (if (consp conns)
      (if (equal (fn-exp-entry-id (car conns)) id)
          (car conns)
        (fn-exp-find id (cdr conns)))
    nil))

(defun fn-exp-remove (id conns)
  (declare (xargs :guard t))
  (if (consp conns)
      (if (equal (fn-exp-entry-id (car conns)) id)
          (fn-exp-remove id (cdr conns))
        (cons (car conns) (fn-exp-remove id (cdr conns))))
    nil))

(defun fn-exp-replace (e conns)
  (declare (xargs :guard t))
  (if (consp conns)
      (if (equal (fn-exp-entry-id (car conns)) (fn-exp-entry-id e))
          (cons e (cdr conns))
        (cons (car conns) (fn-exp-replace e (cdr conns))))
    nil))

(defun fn-exp-count-address (address conns)
  (declare (xargs :guard t))
  (if (consp conns)
      (+ (if (equal (fn-exp-entry-address (car conns)) address) 1 0)
         (fn-exp-count-address address (cdr conns)))
    0))

(defun fn-exp-ids (conns)
  (declare (xargs :guard t))
  (if (consp conns)
      (cons (fn-exp-entry-id (car conns)) (fn-exp-ids (cdr conns)))
    nil))

; Keyed triples (KEY STAMP COUNT): RATES, FAILS and POSTS.
(defun fn-exp-lookup (key rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (consp (car rows)) (equal (car (car rows)) key))
          (car rows)
        (fn-exp-lookup key (cdr rows)))
    nil))

(defun fn-exp-drop (key rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (consp (car rows)) (equal (car (car rows)) key))
          (fn-exp-drop key (cdr rows))
        (cons (car rows) (fn-exp-drop key (cdr rows))))
    nil))

(defun fn-exp-put (key stamp count rows)
  (declare (xargs :guard t))
  (cons (list key stamp count) (fn-exp-drop key rows)))

(defun fn-exp-prune (stamp rows)
  ; Keep only the triples of this window.
  (declare (xargs :guard t))
  (if (consp rows)
      (if (equal (fn-exp-at 1 (car rows)) stamp)
          (cons (car rows) (fn-exp-prune stamp (cdr rows)))
        (fn-exp-prune stamp (cdr rows)))
    nil))

(defun fn-exp-count-in (key stamp rows)
  ; KEY's count in window STAMP; a stale or absent triple counts 0.
  (declare (xargs :guard t))
  (let ((row (fn-exp-lookup key rows)))
    (if (equal (fn-exp-at 1 row) stamp) (fn-exp-nat 2 row) 0)))

(defun fn-exp-quantum (now)
  (declare (xargs :guard t))
  (floor (nfix now) *fn-exp-quantum-ms*))

(defun fn-exp-window (now)
  (declare (xargs :guard t))
  (floor (nfix now) *fn-exp-window-ms*))

; COUNTERS.  Index 0 admitted, 1 refused busy, 2 refused per-address, 3
; refused auth, 4 deferred, 5 idle-closed, 6 auth-closed, 7 the recent
; window, 8 pressure events in it.
(defun fn-exp-plus (i k c)
  (declare (xargs :guard t))
  (+ (fn-exp-nat k c) (if (equal i k) 1 0)))

(defun fn-exp-counters-bump (i now c)
  ; Counter I, and for every pressure event (I > 0) the recent window too.
  (declare (xargs :guard t))
  (let* ((w (fn-exp-window now))
         (recent (if (equal (fn-exp-at 7 c) w) (fn-exp-nat 8 c) 0)))
    (list (fn-exp-plus i 0 c) (fn-exp-plus i 1 c) (fn-exp-plus i 2 c)
          (fn-exp-plus i 3 c) (fn-exp-plus i 4 c) (fn-exp-plus i 5 c)
          (fn-exp-plus i 6 c)
          (if (equal i 0) (fn-exp-at 7 c) w)
          (if (equal i 0) (fn-exp-nat 8 c) (1+ recent)))))

(defun fn-exp-with (xs conns rates fails posts counters)
  (declare (ignore xs) (xargs :guard t))
  (fn-exp-make conns rates fails posts counters))

; -----------------------------------------------------------------------------
; Admission (RFC 3977 section 5.1.1: 400 at the greeting, then close)

(defconst *fn-exp-busy-line* "400 too many connections; try again later")
(defconst *fn-exp-address-line*
  "400 too many connections from this address; try again later")
(defconst *fn-exp-auth-line*
  "400 too many authentication failures from this address; try again later")
(defconst *fn-exp-auth-close-line*
  "400 too many authentication failures; closing connection")

(defun fn-exp-line (text)
  (declare (xargs :guard t))
  (append (fn-record-string-octets text) (list 13 10)))

; The decision before the owner opens anything: :admit, or (:refuse TEXT).
(defun fn-exp-admit-decision (xs lim nconns address now)
  (declare (xargs :guard t))
  (let ((failed (fn-exp-count-in address (fn-exp-window now) (fn-exp-fails xs))))
    (cond ((and (posp (fn-exp-lim-auth-failures lim))
                (<= (fn-exp-lim-auth-failures lim) failed))
           (list :refuse *fn-exp-auth-line* 3))
          ((<= (fn-exp-lim-total lim) (nfix nconns))
           (list :refuse *fn-exp-busy-line* 1))
          ((<= (fn-exp-lim-per-address lim)
               (fn-exp-count-address address (fn-exp-conns xs)))
           (list :refuse *fn-exp-address-line* 2))
          (t (list :admit)))))

(defun fn-exp-register (xs id address now)
  (declare (xargs :guard t))
  (fn-exp-make (cons (fn-exp-entry id address (nfix now) nil nil 0)
                     (fn-exp-remove id (fn-exp-conns xs)))
               (fn-exp-rates xs) (fn-exp-fails xs) (fn-exp-posts xs)
               (fn-exp-counters-bump 0 now (fn-exp-counters xs))))

; THE HOST-CALLED OPEN.  OC is the configured owner, ACFG the operator's
; AUTHINFO configuration, PEER the configured peer the host resolved the
; source to (or nil), ADDRESS the kernel's (FAMILY . OCTETS).  The result is
; (EFFECTS OC' XS' ID REFUSAL): the served greeting and the owner with the
; connection installed, or no effects, the owner unchanged and REFUSAL the
; 400 line the host sends before it closes.  ID is nil when nothing opened.
(defun fn-exp-open (oc xs lim acfg peer address now)
  (declare (xargs :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (decision (fn-exp-admit-decision xs lim (len (fn-own-conns o))
                                          address now)))
    (if (equal (car decision) :admit)
        (let* ((id (fn-own-next-id o))
               (pinned (fn-exp-pinned-acfg acfg lim))
               (opened (if peer
                           (fn-ocfg-open-peer oc peer pinned)
                         (fn-ocfg-open oc pinned)))
               (oc2 (cdr opened))
               (openedp (and (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc2)))
                             t)))
          (list (car opened) oc2
                (if openedp (fn-exp-register xs id address now) xs)
                (if openedp id nil)
                nil))
      (list nil oc
            (fn-exp-with xs (fn-exp-conns xs) (fn-exp-rates xs)
                         (fn-exp-fails xs) (fn-exp-posts xs)
                         (fn-exp-counters-bump (nfix (fn-exp-at 2 decision)) now
                                               (fn-exp-counters xs)))
            nil
            (fn-exp-line (fn-exp-at 1 decision))))))

(defun fn-exp-open-effects (r) (declare (xargs :guard t)) (fn-exp-at 0 r))
(defun fn-exp-open-ocfg (r) (declare (xargs :guard t)) (fn-exp-at 1 r))
(defun fn-exp-open-state (r) (declare (xargs :guard t)) (fn-exp-at 2 r))
(defun fn-exp-open-id (r) (declare (xargs :guard t)) (fn-exp-at 3 r))
(defun fn-exp-open-refusal (r) (declare (xargs :guard t)) (fn-exp-at 4 r))

; Release: the host closed the connection (fn-owner-close ran).  The rate
; triple of an address with no connection left goes with it.
(defun fn-exp-release (xs id)
  (declare (xargs :guard t))
  (let* ((e (fn-exp-find id (fn-exp-conns xs)))
         (conns (fn-exp-remove id (fn-exp-conns xs)))
         (address (fn-exp-entry-address e)))
    (fn-exp-make conns
                 (if (and e (zp (fn-exp-count-address address conns)))
                     (fn-exp-drop address (fn-exp-rates xs))
                   (fn-exp-rates xs))
                 (fn-exp-fails xs) (fn-exp-posts xs) (fn-exp-counters xs))))

; -----------------------------------------------------------------------------
; The work budget (D27): before every served step

; The milliseconds to the start of the next PERIOD.  PERIOD minus the
; position in it is already in 1..PERIOD; the `posp' test states the range
; to the prover without an arithmetic library.
(defun fn-exp-ms-to-next (now period)
  (declare (xargs :guard (posp period)))
  (let ((ms (- period (mod (nfix now) period))))
    (if (posp ms) ms period)))

; :proceed, or (:defer MS): wait MS and ask again.  Never a close.
(defun fn-exp-charge (xs lim id now)
  (declare (xargs :guard t))
  (let ((e (fn-exp-find id (fn-exp-conns xs))))
    (if (not e)
        (cons :proceed xs)
      (let* ((address (fn-exp-entry-address e))
             (principal (fn-exp-entry-principal e))
             (q (fn-exp-quantum now))
             (steps (fn-exp-count-in address q (fn-exp-rates xs))))
        (cond
         ((and principal (posp (fn-exp-lim-posts lim))
               (<= (fn-exp-lim-posts lim)
                   (fn-exp-count-in principal (fn-exp-window now) (fn-exp-posts xs))))
          (cons (list :defer (fn-exp-ms-to-next now *fn-exp-window-ms*))
                (fn-exp-with xs (fn-exp-conns xs) (fn-exp-rates xs)
                             (fn-exp-fails xs) (fn-exp-posts xs)
                             (fn-exp-counters-bump 4 now (fn-exp-counters xs)))))
         ((not (posp (fn-exp-lim-steps lim))) (cons :proceed xs))
         ((<= (fn-exp-lim-steps lim) steps)
          (cons (list :defer (fn-exp-ms-to-next now *fn-exp-quantum-ms*))
                (fn-exp-with xs (fn-exp-conns xs) (fn-exp-rates xs)
                             (fn-exp-fails xs) (fn-exp-posts xs)
                             (fn-exp-counters-bump 4 now (fn-exp-counters xs)))))
         (t (cons :proceed
                  (fn-exp-with xs (fn-exp-conns xs)
                               (fn-exp-put address q (1+ steps) (fn-exp-rates xs))
                               (fn-exp-fails xs) (fn-exp-posts xs)
                               (fn-exp-counters xs)))))))))

; -----------------------------------------------------------------------------
; After every served step: progress, failed logins, submissions

(defun fn-exp-481-count (octets at-line-start)
  ; The replies in OCTETS that begin "481 ": the RFC 4643 section 2.3.2
  ; authentication-failed answer, as the served step rendered it.
  (declare (xargs :guard t))
  (if (consp octets)
      (+ (if (and at-line-start
                  (equal (fn-exp-at 0 octets) 52)
                  (equal (fn-exp-at 1 octets) 56)
                  (equal (fn-exp-at 2 octets) 49)
                  (equal (fn-exp-at 3 octets) 32))
             1 0)
         (fn-exp-481-count (cdr octets) (equal (car octets) 10)))
    0))

; The observation reads two facts of the step's reply and nothing else:
; ANSWERED, whether it sent any octet, and FAILURES, how many of its replies
; are a 481 (fn-exp-481-count).  CONSUMED is the octets the step consumed,
; SUBJECT the session's subject after it, SUBMITTED whether it produced a
; submission.  The result is (DECISION . XS'): :continue, or (:close LINE)
; after this address reached its failed-login limit in this step.
(defun fn-exp-observe-facts (xs lim id now answered failures consumed subject
                                submitted)
  (declare (xargs :guard t))
  (let ((e (fn-exp-find id (fn-exp-conns xs)))
        (failures (nfix failures)))
    (if (not e)
        (cons :continue xs)
      (let* ((address (fn-exp-entry-address e))
             (w (fn-exp-window now))
             (pending (+ (fn-exp-entry-pending e) (nfix consumed)))
             (progress (or answered
                           (<= *fn-exp-significant-octets* pending)))
             (entry (fn-exp-entry id address
                                  (if progress (nfix now) (fn-exp-entry-last e))
                                  (or (fn-exp-entry-answered e) answered)
                                  subject
                                  (if progress 0 pending)))
             (fails0 (fn-exp-prune w (fn-exp-fails xs)))
             (failed (+ failures (fn-exp-count-in address w fails0)))
             (fails (if (posp failures) (fn-exp-put address w failed fails0) fails0))
             (posts0 (fn-exp-prune w (fn-exp-posts xs)))
             (posts (if (and submitted subject)
                        (fn-exp-put subject w
                                    (1+ (fn-exp-count-in subject w posts0)) posts0)
                      posts0))
             (closep (and (posp failures)
                          (posp (fn-exp-lim-auth-failures lim))
                          (<= (fn-exp-lim-auth-failures lim) failed)))
             (next (fn-exp-make (fn-exp-replace entry (fn-exp-conns xs))
                                (fn-exp-rates xs) fails posts
                                (if closep
                                    (fn-exp-counters-bump 6 now (fn-exp-counters xs))
                                  (fn-exp-counters xs)))))
        (cons (if closep (list :close (fn-exp-line *fn-exp-auth-close-line*)) :continue)
              next)))))

; OUTPUT is the reply octets of the step (fn-served-reply-octets of its
; effects).  The served path does not build this list for the observation:
; host/owner-host.lisp fn-owner-exposure-observe calls
; fn-exp-observe-effects (books/public-exposure-reply.lisp), which is this
; function of the effects' reply octets and computes the two facts by one
; scan of the effects (exposure-reply-size, 2026-09-26: the recursion of
; fn-exp-481-count over a 2 MiB reply exhausted the control stack).
(defun fn-exp-observe (xs lim id now output consumed subject submitted)
  (declare (xargs :guard t))
  (fn-exp-observe-facts xs lim id now (consp output) (fn-exp-481-count output t)
                        consumed subject submitted))

; -----------------------------------------------------------------------------
; On a receive timeout: RFC 3977 section 3.1's autologout
;
; :keep, or :close -- and the close sends nothing: "When the timer expires,
; the server SHOULD close the connection without sending any response".

(defun fn-exp-idle-limit (lim e)
  (declare (xargs :guard t))
  (if (fn-exp-entry-answered e) (fn-exp-lim-idle lim) (fn-exp-lim-first lim)))

(defun fn-exp-idle (xs lim id now)
  (declare (xargs :guard t))
  (let* ((e (fn-exp-find id (fn-exp-conns xs)))
         (limit (fn-exp-idle-limit lim e)))
    (if (and e (posp limit)
             (<= (+ (fn-exp-entry-last e) (* 1000 limit)) (nfix now)))
        (cons :close
              (fn-exp-with xs (fn-exp-conns xs) (fn-exp-rates xs)
                           (fn-exp-fails xs) (fn-exp-posts xs)
                           (fn-exp-counters-bump 5 now (fn-exp-counters xs))))
      (cons :keep xs))))

; -----------------------------------------------------------------------------
; The operator's lines (appended to `health')

(defun fn-exp-decimal (n)
  (declare (xargs :guard t))
  (fn-record-string-octets
   (coerce (explode-nonnegative-integer (nfix n) 10 nil) 'string)))

(defun fn-exp-text (s)
  (declare (xargs :guard t))
  (fn-record-string-octets s))

(defun fn-exp-field (name n)
  (declare (xargs :guard t))
  (append (fn-exp-text " ") (fn-exp-text name) (fn-exp-text "=") (fn-exp-decimal n)))

; Pressure is held while the connections in use reach nine tenths of the
; total, or while this minute has seen a refusal, a deferral or a close.
(defun fn-exp-pressure-heldp (xs lim nconns now)
  (declare (xargs :guard t))
  (let ((c (fn-exp-counters xs)))
    (or (and (posp (fn-exp-lim-total lim))
             (<= (* 9 (fn-exp-lim-total lim)) (* 10 (nfix nconns))))
        (and (equal (fn-exp-at 7 c) (fn-exp-window now))
             (posp (fn-exp-nat 8 c))))))

(defun fn-exp-health-lines (xs lim nconns now)
  (declare (xargs :guard t))
  (let ((c (fn-exp-counters xs)))
    (append
     (fn-exp-text "exposure pressure ")
     (fn-exp-text (if (fn-exp-pressure-heldp xs lim nconns now) "held" "clear"))
     (fn-exp-field "connections" nconns)
     (fn-exp-field "total" (fn-exp-lim-total lim))
     (fn-exp-field "per-address" (fn-exp-lim-per-address lim))
     (fn-exp-field "recent" (if (equal (fn-exp-at 7 c) (fn-exp-window now))
                                (fn-exp-nat 8 c) 0))
     (list 10)
     (fn-exp-text "exposure counts")
     (fn-exp-field "admitted" (fn-exp-nat 0 c))
     (fn-exp-field "refused-busy" (fn-exp-nat 1 c))
     (fn-exp-field "refused-address" (fn-exp-nat 2 c))
     (fn-exp-field "refused-auth" (fn-exp-nat 3 c))
     (fn-exp-field "deferred" (fn-exp-nat 4 c))
     (fn-exp-field "idle-closed" (fn-exp-nat 5 c))
     (fn-exp-field "auth-closed" (fn-exp-nat 6 c))
     (list 10)
     (fn-exp-text "exposure limits")
     (fn-exp-field "steps-per-second" (fn-exp-lim-steps lim))
     (fn-exp-field "idle-seconds" (fn-exp-lim-idle lim))
     (fn-exp-field "first-seconds" (fn-exp-lim-first lim))
     (fn-exp-field "auth-failures" (fn-exp-lim-auth-failures lim))
     (fn-exp-field "posts-per-minute" (fn-exp-lim-posts lim))
     (fn-exp-text " anonymous=")
     (fn-exp-text (if (equal (fn-exp-lim-anonymous lim) :open) "open" "none"))
     (list 10))))

; =============================================================================
; Theorems

(local (in-theory (disable fn-ocfg-open fn-ocfg-open-peer fn-own-conns
                           fn-own-next-id fn-own-find-conn fn-ocfg-owner
                           fn-exp-pinned-acfg)))

(defthm fn-exp-at-of-cons
  (and (equal (fn-exp-at 0 (cons a b)) a)
       (implies (posp i)
                (equal (fn-exp-at i (cons a b)) (fn-exp-at (1- i) b)))))

(local (defthm fn-exp-make-fields
  (and (equal (fn-exp-conns (fn-exp-make c r f p k)) c)
       (equal (fn-exp-rates (fn-exp-make c r f p k)) r)
       (equal (fn-exp-fails (fn-exp-make c r f p k)) f)
       (equal (fn-exp-posts (fn-exp-make c r f p k)) p)
       (equal (fn-exp-counters (fn-exp-make c r f p k)) k))))

(local (defthm fn-exp-lim-fields
  (and (equal (fn-exp-lim-total (fn-exp-lim-make a b c d e f g h)) (nfix a))
       (equal (fn-exp-lim-per-address (fn-exp-lim-make a b c d e f g h)) (nfix b))
       (equal (fn-exp-lim-steps (fn-exp-lim-make a b c d e f g h)) (nfix c)))))

(local (in-theory (disable fn-exp-make fn-exp-conns fn-exp-rates fn-exp-fails
                           fn-exp-posts fn-exp-counters fn-exp-with
                           fn-exp-counters-bump)))

(local (defthm fn-exp-with-conns
  (equal (fn-exp-conns (fn-exp-with xs c r f p k)) c)
  :hints (("Goal" :in-theory (enable fn-exp-with)))))

(local (defthm fn-exp-count-address-of-remove
  (<= (fn-exp-count-address a (fn-exp-remove id conns))
      (fn-exp-count-address a conns))
  :rule-classes :linear))

(local (defthm fn-exp-ids-of-remove-other
  (implies (and (member-equal x (fn-exp-ids conns)) (not (equal x id)))
           (member-equal x (fn-exp-ids (fn-exp-remove id conns))))))

(local (defthm fn-exp-ids-of-replace
  (equal (fn-exp-ids (fn-exp-replace e conns)) (fn-exp-ids conns))
  :hints (("Goal" :in-theory (enable fn-exp-replace)))))

; -----------------------------------------------------------------------------
; KEYSTONE (a limit row in force bounds the accepted connections).
;
; The subject is fn-exp-open, which the host calls at every accept.  A
; connection opens only when, under the limits in force at that moment, the
; owner held fewer connections than the total and this address fewer than
; its per-address limit; afterwards the address holds exactly one more.  No
; open ever carries an address past the larger of what it held and the limit
; in force: so a limit lowered by reconfiguration closes nothing and admits
; nothing more from an address until it is back under the new limit.

(defthm fn-exp-open-admits-within-the-limits-in-force
  (let* ((r (fn-exp-open oc xs lim acfg peer address now))
         (before (fn-exp-count-address address (fn-exp-conns xs)))
         (after (fn-exp-count-address address
                                      (fn-exp-conns (fn-exp-open-state r)))))
    (implies (fn-exp-open-id r)
             (and (< (len (fn-own-conns (fn-ocfg-owner oc))) (fn-exp-lim-total lim))
                  (< before (fn-exp-lim-per-address lim))
                  (<= after (+ 1 before))
                  (<= after (fn-exp-lim-per-address lim)))))
  :hints (("Goal" :in-theory (enable fn-exp-open fn-exp-admit-decision
                                     fn-exp-register fn-exp-open-id
                                     fn-exp-open-state))))

(defthm fn-exp-open-never-exceeds-a-limit-in-force
  (let* ((r (fn-exp-open oc xs lim acfg peer address now))
         (before (fn-exp-count-address address (fn-exp-conns xs)))
         (after (fn-exp-count-address address
                                      (fn-exp-conns (fn-exp-open-state r)))))
    (<= after (max before (fn-exp-lim-per-address lim))))
  :hints (("Goal" :in-theory (enable fn-exp-open fn-exp-admit-decision
                                     fn-exp-register fn-exp-open-state))))

; A refused open answers the 400 and changes neither the owner nor the
; connections: the host sends REFUSAL and closes (RFC 3977 5.1.1 note [2]).
(defthm fn-exp-open-refusal-is-a-400-and-opens-nothing
  (let ((r (fn-exp-open oc xs lim acfg peer address now)))
    (implies (not (equal (car (fn-exp-admit-decision
                               xs lim (len (fn-own-conns (fn-ocfg-owner oc)))
                               address now))
                         :admit))
             (and (null (fn-exp-open-id r))
                  (equal (fn-exp-open-ocfg r) oc)
                  (equal (fn-exp-conns (fn-exp-open-state r)) (fn-exp-conns xs))
                  (equal (take 4 (fn-exp-open-refusal r))
                         (fn-record-string-octets "400 ")))))
  :hints (("Goal" :in-theory (enable fn-exp-open fn-exp-admit-decision
                                     fn-exp-open-id fn-exp-open-ocfg
                                     fn-exp-open-state fn-exp-open-refusal
                                     fn-exp-line))))

(defthm fn-exp-release-never-raises-a-count
  (<= (fn-exp-count-address a (fn-exp-conns (fn-exp-release xs id)))
      (fn-exp-count-address a (fn-exp-conns xs)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-exp-release))))

; -----------------------------------------------------------------------------
; KEYSTONE (the work budget per quantum).
;
; The subject is fn-exp-charge, which the host calls before every served
; step.  Under a positive steps-per-second row, a step proceeds only while
; its address has started fewer than the budget in this quantum, and after
; it the address's count for the quantum is at most the budget.  An
; exhausted budget is a wait for the next quantum, never a refusal.

(local (defthm fn-exp-count-in-of-put-same
  (equal (fn-exp-count-in key stamp (fn-exp-put key stamp n rows)) (nfix n))
  :hints (("Goal" :in-theory (enable fn-exp-count-in fn-exp-put fn-exp-lookup)))))

(defthm fn-exp-charge-bounds-steps-per-quantum
  (let* ((r (fn-exp-charge xs lim id now))
         (e (fn-exp-find id (fn-exp-conns xs)))
         (address (fn-exp-entry-address e))
         (q (fn-exp-quantum now)))
    (implies (and e
                  (posp (fn-exp-lim-steps lim))
                  (equal (car r) :proceed))
             (and (< (fn-exp-count-in address q (fn-exp-rates xs))
                     (fn-exp-lim-steps lim))
                  (<= (fn-exp-count-in address q (fn-exp-rates (cdr r)))
                      (fn-exp-lim-steps lim)))))
  :hints (("Goal" :in-theory (enable fn-exp-charge fn-exp-with))))

(defthm fn-exp-charge-waits-and-never-closes
  (let ((r (fn-exp-charge xs lim id now)))
    (or (equal (car r) :proceed)
        (and (equal (car (car r)) :defer)
             (posp (cadr (car r))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-exp-charge fn-exp-ms-to-next))))

; -----------------------------------------------------------------------------
; KEYSTONE (an anonymous session never reaches a mutating command).
;
; The subject is the configuration fn-exp-open pins (fn-exp-pinned-acfg):
; fn-auth-open-session makes it the session's (books/nntp-auth.lisp; the
; pin is `fn-served-peer-and-reader-open-under-the-same-policy' for both
; roles), and every command of an unauthenticated session under the :none
; policy is then books/nntp-auth.lisp's keystone
; fn-auth-gated-command-is-refused-and-not-performed: 480, no submission, no
; article mode, the session unchanged.  POST is one of the restricted
; commands; IHAVE, CHECK and TAKETHIS are peer policy, decided by the
; source-role record in fn-peer-step and refused to a non-peer there.

(defthm fn-exp-pinned-acfg-requires-authentication
  (implies (equal (fn-exp-lim-anonymous lim) :none)
           (and (fn-auth-configp (fn-exp-pinned-acfg acfg lim))
                (fn-auth-config-requiredp (fn-exp-pinned-acfg acfg lim))))
  :hints (("Goal" :in-theory (enable fn-exp-pinned-acfg fn-auth-configp
                                     fn-auth-cred-listp))))

(defthm fn-exp-pinned-acfg-keeps-the-operators-credentials
  (implies (fn-auth-configp acfg)
           (and (equal (fn-auth-config-creds (fn-exp-pinned-acfg acfg lim))
                       (fn-auth-config-creds acfg))
                (equal (fn-auth-config-protected-onlyp (fn-exp-pinned-acfg acfg lim))
                       (fn-auth-config-protected-onlyp acfg))
                (equal (fn-auth-config-tls-availablep (fn-exp-pinned-acfg acfg lim))
                       (fn-auth-config-tls-availablep acfg))))
  :hints (("Goal" :in-theory (enable fn-exp-pinned-acfg))))

(defthm fn-exp-anonymous-none-gates-every-restricted-command
  (implies (and (equal (fn-exp-lim-anonymous lim) :none)
                (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (equal (fn-auth-session-config as) (fn-exp-pinned-acfg acfg lim))
                (not (fn-auth-session-subject as))
                (fn-nntp-command-inputp line)
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (fn-auth-restricted-keywordp (car (fn-nntp-tokenize line))))
           (and (null (fn-post-result-submission
                       (fn-auth-step as archive config observation injection
                                     (list :command line))))
                (equal (fn-post-result-session
                        (fn-auth-step as archive config observation injection
                                      (list :command line)))
                       as)
                (equal (fn-post-result-effects
                        (fn-auth-step as archive config observation injection
                                      (list :command line)))
                       (fn-auth-single as "480 authentication required"))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-auth-gated-command-is-refused-and-not-performed)
                 (:instance fn-exp-pinned-acfg-requires-authentication))
           :in-theory (disable fn-auth-gated-command-is-refused-and-not-performed
                               fn-exp-pinned-acfg-requires-authentication
                               fn-auth-step fn-auth-single fn-auth-sessionp
                               fn-auth-restricted-keywordp fn-nntp-tokenize
                               fn-nntp-command-inputp
                               fn-nntp-command-arguments-at-mostp))))

; The mutating reader command is among them (ground).
(defthm fn-exp-post-is-restricted
  (fn-auth-restricted-keywordp (fn-nntp-string-octets "POST"))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; KEYSTONE (limits and reconfiguration never drop a connection).
;
; Nothing in this book removes a connection except fn-exp-release, which the
; host calls when the connection has already closed.  Whatever the limits
; (a reconfiguration hands the next call new ones), fn-exp-open adds at most
; one entry, fn-exp-charge and fn-exp-idle change none, and fn-exp-observe
; replaces one in place.  The only closes the book asks for are
; fn-exp-idle's (the connection was silent for the configured timer:
; fn-exp-idle-closes-only-silence) and fn-exp-observe's (the step itself
; answered 481 and reached the failed-login limit).

(defthm fn-exp-charge-keeps-the-connections
  (equal (fn-exp-conns (cdr (fn-exp-charge xs lim id now))) (fn-exp-conns xs))
  :hints (("Goal" :in-theory (e/d (fn-exp-charge fn-exp-with)
                                  (fn-exp-put fn-exp-count-in fn-exp-find
                                   fn-exp-counters-bump fn-exp-ms-to-next
                                   fn-exp-quantum fn-exp-window)))))

(defthm fn-exp-idle-keeps-the-connections
  (equal (fn-exp-conns (cdr (fn-exp-idle xs lim id now))) (fn-exp-conns xs))
  :hints (("Goal" :in-theory (e/d (fn-exp-idle fn-exp-with)
                                  (fn-exp-find fn-exp-counters-bump
                                   fn-exp-idle-limit)))))

(defthm fn-exp-observe-keeps-the-connection-ids
  (equal (fn-exp-ids (fn-exp-conns (cdr (fn-exp-observe xs lim id now output
                                                        consumed subject
                                                        submitted))))
         (fn-exp-ids (fn-exp-conns xs)))
  :hints (("Goal" :in-theory (e/d (fn-exp-observe)
                                  (fn-exp-put fn-exp-count-in fn-exp-find
                                   fn-exp-prune fn-exp-counters-bump
                                   fn-exp-481-count fn-exp-line fn-exp-replace
                                   fn-exp-entry fn-exp-window)))))

(local (defthm fn-exp-register-keeps-members
  (implies (member-equal x (fn-exp-ids (fn-exp-conns xs)))
           (member-equal x (fn-exp-ids (fn-exp-conns
                                        (fn-exp-register xs id address now)))))
  :hints (("Goal" :in-theory (enable fn-exp-register)))))

(defthm fn-exp-limits-never-drop-a-connection
  (implies (member-equal x (fn-exp-ids (fn-exp-conns xs)))
           (and (member-equal x (fn-exp-ids (fn-exp-conns (cdr (fn-exp-charge xs lim id now)))))
                (member-equal x (fn-exp-ids (fn-exp-conns (cdr (fn-exp-idle xs lim id now)))))
                (member-equal x (fn-exp-ids (fn-exp-conns
                                             (cdr (fn-exp-observe xs lim id now output
                                                                  consumed subject
                                                                  submitted)))))
                (member-equal x (fn-exp-ids (fn-exp-conns
                                             (fn-exp-open-state
                                              (fn-exp-open oc xs lim acfg peer
                                                           address now)))))))
  :hints (("Goal" :in-theory (e/d (fn-exp-open fn-exp-open-state fn-exp-with)
                                  (fn-exp-register fn-exp-admit-decision
                                   fn-exp-counters-bump fn-exp-line
                                   fn-exp-charge fn-exp-idle fn-exp-observe)))))

(defthm fn-exp-observe-closes-only-on-a-failed-login
  (implies (consp (car (fn-exp-observe xs lim id now output consumed subject
                                       submitted)))
           (and (posp (fn-exp-481-count output t))
                (posp (fn-exp-lim-auth-failures lim))))
  :hints (("Goal" :in-theory (e/d (fn-exp-observe)
                                  (fn-exp-put fn-exp-count-in fn-exp-find
                                   fn-exp-prune fn-exp-counters-bump
                                   fn-exp-481-count fn-exp-line fn-exp-replace
                                   fn-exp-entry fn-exp-window fn-exp-make)))))

(defthm fn-exp-idle-closes-only-silence
  (let ((e (fn-exp-find id (fn-exp-conns xs))))
    (implies (equal (car (fn-exp-idle xs lim id now)) :close)
             (and e
                  (posp (fn-exp-idle-limit lim e))
                  (<= (+ (fn-exp-entry-last e) (* 1000 (fn-exp-idle-limit lim e)))
                      (nfix now)))))
  :hints (("Goal" :in-theory (enable fn-exp-idle))))
