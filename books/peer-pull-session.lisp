; fn: the pull session -- the feed's protected preamble, then the NEWNEWS
; round (PRF-125; RFC 4642, RFC 4643, RFC 3977 section 7.4).
;
; A pull is a client connection this node opens.  Before the round of
; books/peer-pull.lisp may send DATE, the connection runs the feed's proved
; session machine (books/feed-connection.lisp `fn-fc-step' and
; `fn-fc-after-tls', streaming off): greeting, STARTTLS and its 382, a TLS
; handshake the host performs against the peer's server name and trust
; anchor, AUTHINFO USER/PASS from the peer's outbound credential profile,
; 281, and :ready.  The round then begins in phase :date
; (`fn-pull-begin-ready'), and every later event is the round's
; (`fn-pull-step').
;
; Whether a peer may be pulled with the transport and credential the
; configuration names is decided here, before any connection
; (`fn-pull-plan-verdict'):
;
;   :tls        a STARTTLS or implicit-TLS transport, with or without a
;               credential;
;   :clear      a clear transport and no credential (anonymous reading, the
;               PRF-100 pull; nothing private is sent);
;   :clear-lab  a clear transport with a credential whose profile carries the
;               explicit clear-text permission AND a loopback host literal:
;               the loopback-lab exception (specs/peering.md), never a
;               general claim;
;   otherwise   refused: the round is failed at its beginning, no :dial is
;               emitted, the profile file is not read.
;
; The host (host/native/pull-service.lisp) performs the effects: (:journal
; . cursor), (:dial), (:tls SERVER-NAME TRUST-ANCHOR), (:remote . octets),
; (:open-local), (:local . octets), (:close); it reports (:remote . octets),
; (:tls-up) only after a verified handshake, (:local . octets) and (:lost).
(in-package "ACL2")
(include-book "peer-pull")
(include-book "feed-connection-invariants")

; -----------------------------------------------------------------------------
; The verdict on a plan

; Local policy: the loopback-lab exception names the two loopback literals.
; A name ("localhost") is resolved outside ACL2 and is not one of them.
(defun fn-pull-loopback-hostp (host)
  (declare (xargs :guard t))
  (or (equal host (fn-record-string-octets "127.0.0.1"))
      (equal host (fn-record-string-octets "::1"))))

(defun fn-pull-auth-path (auth) (declare (xargs :guard t)) (fn-pull-at 1 auth))
(defun fn-pull-auth-allow-clear (auth) (declare (xargs :guard t)) (fn-pull-at 2 auth))

(defun fn-pull-tls-securityp (security)
  (declare (xargs :guard t))
  (and (true-listp security) (equal (len security) 4)
       (equal (car security) :tls)
       (member-equal (cadr security) '(:starttls :implicit))
       (stringp (caddr security)) (stringp (cadddr security))
       t))

; KEYSTONE SUBJECT.  host/native/pull-service.lisp `fnn-pull-round' calls it
; through `fn-pull-plan-profile-path' and `fn-pull-session-begin'.
(defun fn-pull-plan-verdict (plan)
  (declare (xargs :guard t))
  (let ((security (fn-pull-plan-security plan))
        (auth (fn-pull-plan-auth plan)))
    (cond ((fn-pull-tls-securityp security) :tls)
          ((not (equal security '(:clear))) :refused-security)
          ((null auth) :clear)
          ((and (equal (fn-pull-auth-allow-clear auth) t)
                (fn-pull-loopback-hostp (fn-pull-plan-host plan)))
           :clear-lab)
          (t :refused-clear-credential))))

; The profile file the host reads for this plan, or nil: ACL2 decides whether
; a secret is read at all.
(defun fn-pull-plan-profile-path (plan)
  (declare (xargs :guard t))
  (let ((auth (fn-pull-plan-auth plan)))
    (if (and auth (member-equal (fn-pull-plan-verdict plan) '(:tls :clear-lab))
             (stringp (fn-pull-auth-path auth)))
        (fn-pull-auth-path auth)
      nil)))

; -----------------------------------------------------------------------------
; The session: (fc round refusal security)

(defun fn-pull-session (fc round refusal security)
  (declare (xargs :guard t))
  (list fc round refusal security))
(defun fn-pull-s-fc (s) (declare (xargs :guard t)) (fn-pull-at 0 s))
(defun fn-pull-s-round (s) (declare (xargs :guard t)) (fn-pull-at 1 s))
(defun fn-pull-s-refusal (s) (declare (xargs :guard t)) (fn-pull-at 2 s))
(defun fn-pull-s-security (s) (declare (xargs :guard t)) (fn-pull-at 3 s))

(defthm fn-pull-s-of-session
  (and (equal (fn-pull-s-fc (fn-pull-session fc round refusal security)) fc)
       (equal (fn-pull-s-round (fn-pull-session fc round refusal security)) round)
       (equal (fn-pull-s-refusal (fn-pull-session fc round refusal security)) refusal)
       (equal (fn-pull-s-security (fn-pull-session fc round refusal security))
              security)))

(in-theory (disable fn-pull-session fn-pull-s-fc fn-pull-s-round
                    fn-pull-s-refusal fn-pull-s-security))

(defun fn-pull-fc-mode (security)
  (declare (xargs :guard t))
  (if (fn-pull-tls-securityp security) (cadr security) :clear))

(defun fn-pull-credentialp (credential)
  (declare (xargs :guard t))
  (and (true-listp credential) (equal (len credential) 2)
       (fn-fap-tokenp (car credential)) (true-listp (car credential))
       (fn-fap-tokenp (cadr credential)) (true-listp (cadr credential))))

; Why a session is refused at its beginning, or nil.  CREDENTIAL is what the
; host read from `fn-pull-plan-profile-path' and ACL2 decoded (the pair
; `fn-fap-decode' yields), nil when there was nothing to read or reading
; failed.
(defun fn-pull-session-refusal (plan credential)
  (declare (xargs :guard t))
  (let ((verdict (fn-pull-plan-verdict plan)))
    (cond ((not (member-equal verdict '(:tls :clear :clear-lab))) verdict)
          ((and (fn-pull-plan-auth plan) (not (fn-pull-credentialp credential)))
           :refused-profile)
          (t nil))))

(defun fn-pull-session-fc0 (plan credential)
  (declare (xargs :guard t))
  (let ((mode (fn-pull-fc-mode (fn-pull-plan-security plan))))
    (if (fn-pull-plan-auth plan)
        (fn-fc-initial-auth-state nil 0 mode
                                  (fn-pull-at 0 credential) (fn-pull-at 1 credential)
                                  (equal (fn-pull-plan-verdict plan) :clear-lab))
      (fn-fc-initial-state nil 0 mode))))

(defun fn-pull-tls-effect (security)
  (declare (xargs :guard t))
  (list :tls (fn-pull-at 2 security) (fn-pull-at 3 security)))

; KEYSTONE SUBJECT.  Beginning a pull (host/native/pull-service.lisp
; `fnn-pull-round').  The cursor's first instant is journaled exactly as
; `fn-pull-begin-effects' says, before the dial, refused or not.
(defun fn-pull-session-begin (plan cursor now credential)
  (declare (xargs :guard t))
  (let* ((security (fn-pull-plan-security plan))
         (round (fn-pull-begin-ready cursor (fn-pull-plan-wildmat plan) now))
         (refusal (fn-pull-session-refusal plan credential))
         (fc (fn-pull-session-fc0 plan credential))
         (journal (fn-pull-begin-effects cursor now)))
    (if refusal
        (mv-let (r2 fail) (fn-pull-fail round)
          (mv (fn-pull-session fc r2 refusal security) (append journal fail)))
      (mv (fn-pull-session fc round nil security)
          (append journal
                  (list (list :dial))
                  (if (equal (fn-fc-phase fc) :tls)
                      (list (fn-pull-tls-effect security))
                    nil))))))

; -----------------------------------------------------------------------------
; The preamble

; The kinds after which a command was sent and the peer's reply may already
; be in the retained input: the host drains (feeds nil) after them.
(defun fn-pull-pre-continuep (kind)
  (declare (xargs :guard t))
  (and (member-equal kind '(:starttls :auth-user :auth-pass)) t))

; The feed-machine events one host event amounts to: EV, then nil (drain the
; retained input) while the machine just sent a command, at most FUEL more.
(defun fn-pull-pre-events (fc ev fuel)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (let ((r (fn-fc-event-result fc ev)))
    (if (and (not (zp fuel)) (fn-pull-pre-continuep (fn-fc-kind r)))
        (cons ev (fn-pull-pre-events (fn-fc-next-state r) nil (1- fuel)))
      (list ev))))

; What the host does for one observation of the machine.  The credential
; lines are the feed's own renderings (`fn-fc-auth-user-command',
; PRF-051 `fn-fc-decoded-profile-renders-verbatim-in-every-state').
(defun fn-pull-obs-effect (kind fc security)
  (declare (xargs :guard t))
  (cond ((equal kind :starttls) (list (cons :remote (fn-fc-starttls-command))))
        ((equal kind :tls) (list (fn-pull-tls-effect security)))
        ((equal kind :auth-user) (list (cons :remote (fn-fc-auth-user-command fc))))
        ((equal kind :auth-pass) (list (cons :remote (fn-fc-auth-pass-command fc))))
        ((equal kind :ready) (list (cons :remote (fn-pull-date-command))))
        (t nil)))

(defun fn-pull-obs-effects (obs fc security)
  (declare (xargs :guard t))
  (if (consp obs)
      (append (fn-pull-obs-effect (fn-fc-obs-kind (car obs)) fc security)
              (fn-pull-obs-effects (cdr obs) fc security))
    nil))

; Every observation is one the preamble goes on from.
(defun fn-pull-pre-okp (obs)
  (declare (xargs :guard t))
  (if (consp obs)
      (and (member-equal (fn-fc-obs-kind (car obs))
                         '(:need-input :starttls :tls :auth-user :auth-pass :ready))
           (fn-pull-pre-okp (cdr obs)))
    t))

(defun fn-pull-session-readyp (s)
  (declare (xargs :guard t))
  (equal (fn-fc-phase (fn-pull-s-fc s)) :ready))

; The feed-machine events a session step feeds.
(defun fn-pull-session-fc-events (s event)
  (declare (xargs :guard t))
  (let ((fc (fn-pull-s-fc s)))
    (cond ((or (fn-pull-done-p (fn-pull-s-round s)) (fn-pull-session-readyp s)) nil)
          ((equal event '(:tls-up)) (fn-pull-pre-events fc :tls-up 1))
          ((and (consp event) (equal (car event) :remote))
           (let ((octets (fn-pull-event-octets event)))
             (fn-pull-pre-events fc octets (+ 1 (len octets)))))
          (t nil))))

(defun fn-pull-s-with-round (s round)
  (declare (xargs :guard t))
  (fn-pull-session (fn-pull-s-fc s) round (fn-pull-s-refusal s) (fn-pull-s-security s)))

; KEYSTONE SUBJECT.  One event of a pull session: the function the host calls
; (host/native/pull-service.lisp `fnn-pull-round', through
; `fn-pull-session-step-pair').
(defun fn-pull-session-step (s event)
  (declare (xargs :guard t))
  (let ((fc (fn-pull-s-fc s))
        (round (fn-pull-s-round s))
        (security (fn-pull-s-security s)))
    (cond ((fn-pull-done-p round) (mv s nil))
          ((fn-pull-session-readyp s)
           (mv-let (r2 effects) (fn-pull-step round event)
             (mv (fn-pull-s-with-round s r2) effects)))
          ((or (equal event '(:tls-up))
               (and (consp event) (equal (car event) :remote)))
           (let* ((evs (fn-pull-session-fc-events s event))
                  (obs (fn-fc-drive fc evs))
                  (fc2 (fn-fc-drive-state fc evs))
                  (effects (fn-pull-obs-effects obs fc security)))
             (if (fn-pull-pre-okp obs)
                 (mv (fn-pull-session fc2 round (fn-pull-s-refusal s) security)
                     effects)
               (mv-let (r2 fail) (fn-pull-fail round)
                 (mv (fn-pull-session fc2 r2 (fn-pull-s-refusal s) security)
                     (append effects fail))))))
          (t (mv-let (r2 fail) (fn-pull-fail round)
               (mv (fn-pull-s-with-round s r2) fail))))))

(defun fn-pull-session-run (s events)
  (declare (xargs :guard t))
  (if (consp events)
      (mv-let (s2 effects) (fn-pull-session-step s (car events))
        (mv-let (s3 more) (fn-pull-session-run s2 (cdr events))
          (mv s3 (append (fn-pull-list effects) more))))
    (mv s nil)))

(defun fn-pull-session-next (s event)
  (declare (xargs :guard t))
  (mv-let (s2 effects) (fn-pull-session-step s event)
    (declare (ignore effects))
    s2))

; The feed-machine events and observations across a run.
(defun fn-pull-session-fc-trace (s events)
  (declare (xargs :guard t))
  (if (consp events)
      (append (fn-pull-session-fc-events s (car events))
              (fn-pull-session-fc-trace (fn-pull-session-next s (car events))
                                        (cdr events)))
    nil))

(defun fn-pull-session-obs (s events)
  (declare (xargs :guard t))
  (if (consp events)
      (append (fn-fc-drive (fn-pull-s-fc s) (fn-pull-session-fc-events s (car events)))
              (fn-pull-session-obs (fn-pull-session-next s (car events))
                                   (cdr events)))
    nil))

; -----------------------------------------------------------------------------
; The preamble is the feed machine

(defthm fn-fc-drive-of-append
  (equal (fn-fc-drive st (append a b))
         (append (fn-fc-drive st a) (fn-fc-drive (fn-fc-drive-state st a) b)))
  :hints (("Goal" :induct (fn-fc-drive-state st a)
           :in-theory (e/d (fn-fc-drive fn-fc-drive-state)
                           (fn-fc-event-result fn-fc-line-code)))))

(defthm fn-fc-drive-state-of-append
  (equal (fn-fc-drive-state st (append a b))
         (fn-fc-drive-state (fn-fc-drive-state st a) b))
  :hints (("Goal" :induct (fn-fc-drive-state st a)
           :in-theory (e/d (fn-fc-drive-state) (fn-fc-event-result)))))

(defthm fn-fc-drive-state-of-nil
  (equal (fn-fc-drive-state st nil) st)
  :hints (("Goal" :in-theory (enable fn-fc-drive-state))))

(defthm fn-fc-drive-of-nil
  (equal (fn-fc-drive st nil) nil)
  :hints (("Goal" :in-theory (enable fn-fc-drive))))

(defthm fn-pull-session-fc-events-quiet
  (implies (or (fn-pull-done-p (fn-pull-s-round s))
               (fn-pull-session-readyp s)
               (not (or (equal event '(:tls-up))
                        (and (consp event) (equal (car event) :remote)))))
           (equal (fn-pull-session-fc-events s event) nil))
  :hints (("Goal" :in-theory (e/d (fn-pull-session-fc-events)
                                  (fn-pull-done-p fn-pull-session-readyp
                                   fn-pull-pre-events)))))

; A session step leaves the machine exactly where the events it fed drive it.
(defthm fn-pull-session-step-fc
  (equal (fn-pull-s-fc (car (fn-pull-session-step s event)))
         (fn-fc-drive-state (fn-pull-s-fc s) (fn-pull-session-fc-events s event)))
  :hints (("Goal" :in-theory (e/d (fn-pull-session-step fn-pull-s-with-round)
                                  (fn-fc-drive-state fn-fc-drive fn-pull-step
                                   fn-pull-fail fn-pull-session-fc-events
                                   fn-pull-obs-effects fn-pull-pre-okp
                                   fn-pull-done-p fn-pull-session-readyp
                                   fn-pull-pre-events fn-pull-event-octets)))))

(defthm fn-pull-session-obs-is-the-machine-over-its-trace
  (equal (fn-pull-session-obs s events)
         (fn-fc-drive (fn-pull-s-fc s) (fn-pull-session-fc-trace s events)))
  :hints (("Goal" :induct (fn-pull-session-obs s events)
           :in-theory (e/d (fn-pull-session-obs fn-pull-session-fc-trace)
                           (fn-fc-drive fn-fc-drive-state fn-pull-session-step
                            fn-pull-session-fc-events)))))

(defthm fn-pull-session-fc0-opens
  (let ((fc (fn-pull-session-fc0 plan credential)))
    (and (fn-fc-opening-phasep fc)
         (implies (fn-pull-tls-securityp (fn-pull-plan-security plan))
                  (fn-fc-protected-profilep fc))))
  :hints (("Goal" :in-theory (enable fn-fc-initial-auth-state fn-fc-initial-state
                                     fn-fc-make-state fn-fc-opening-phasep
                                     fn-fc-protected-profilep fn-fc-phase
                                     fn-fc-security))))

(defthm fn-pull-s-fc-of-begin
  (equal (fn-pull-s-fc (car (fn-pull-session-begin plan cursor now credential)))
         (fn-pull-session-fc0 plan credential))
  :hints (("Goal" :in-theory (disable fn-pull-session-fc0 fn-pull-fail
                                      fn-pull-begin-ready))))

; KEYSTONE (PRF-125, instantiating PRF-051
; `fn-fc-offers-and-credentials-wait-for-tls-and-login').  A pull over a TLS
; transport, driven by ANY sequence of host events: the observations of its
; preamble obey the feed's gate -- no AUTHINFO line until the 382 was read
; and the host reported the TLS handshake up, and no :ready (so no DATE,
; NEWNEWS or ARTICLE, since the round steps only once the machine is
; :ready) until, with a credential, a 281 was read.  Each pre-ready step's
; effects are `fn-pull-obs-effects' of exactly these observations
; (`fn-pull-session-step'), so an AUTHINFO line leaves only on an
; :auth-user or :auth-pass observation.
(defthm fn-pull-session-credentials-wait-for-tls-and-login
  (implies (equal (fn-pull-plan-verdict plan) :tls)
           (let ((s0 (car (fn-pull-session-begin plan cursor now credential))))
             (fn-fc-gate-okp (fn-fc-gate-start (fn-fc-security (fn-pull-s-fc s0)))
                             (fn-fc-loginp (fn-pull-s-fc s0))
                             (fn-pull-session-obs s0 events))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-fc-offers-and-credentials-wait-for-tls-and-login
                            (st (fn-pull-session-fc0 plan credential))
                            (events (fn-pull-session-fc-trace
                                     (car (fn-pull-session-begin plan cursor now
                                                                 credential))
                                     events)))
                 (:instance fn-pull-session-fc0-opens))
           :in-theory (e/d (fn-pull-plan-verdict)
                           (fn-fc-offers-and-credentials-wait-for-tls-and-login
                            fn-pull-session-fc0-opens
                            fn-pull-session-fc0 fn-fc-gate-okp fn-fc-drive
                            fn-pull-session-begin fn-pull-session-fc-trace
                            fn-fc-protected-profilep fn-fc-opening-phasep
                            fn-fc-loginp fn-fc-gate-start fn-fc-security)))))

; -----------------------------------------------------------------------------
; A clear transport with a credential and no exception is refused

(defthm fn-pull-done-p-of-fail
  (fn-pull-done-p (car (fn-pull-fail r)))
  :hints (("Goal" :in-theory (enable fn-pull-fail))))

(defthm fn-pull-session-step-of-a-done-round
  (implies (fn-pull-done-p (fn-pull-s-round s))
           (equal (fn-pull-session-step s event) (mv s nil)))
  :hints (("Goal" :in-theory (e/d (fn-pull-session-step) (fn-pull-done-p)))))

(defthm fn-pull-session-run-of-a-done-round
  (implies (fn-pull-done-p (fn-pull-s-round s))
           (equal (fn-pull-session-run s events) (mv s nil)))
  :hints (("Goal" :induct (len events)
           :in-theory (e/d (fn-pull-session-run) (fn-pull-done-p
                                                  fn-pull-session-step)))))

(defthm fn-pull-fail-effects
  (equal (mv-nth 1 (fn-pull-fail r)) (list (list :close)))
  :hints (("Goal" :in-theory (enable fn-pull-fail))))

(defthm fn-pull-close-of-a-failed-round
  (equal (fn-pull-close (car (fn-pull-fail r))) (fn-pull-round-cursor r))
  :hints (("Goal" :in-theory (enable fn-pull-fail fn-pull-close fn-pull-advancesp
                                     fn-pull-round-cursor))))

; KEYSTONE (PRF-125).  A plan whose transport is clear and whose peer record
; carries a credential, without both the profile's explicit clear-text
; permission and a loopback host literal, is refused before anything leaves
; this node: the secret is not read, the beginning emits no :dial (only the
; cursor's journal record and the close), the session answers every later
; event with nothing, and the round closes with the cursor it began with.
(defthm fn-pull-session-refuses-a-clear-credential-without-the-lab-exception
  (implies (and (equal (fn-pull-plan-security plan) '(:clear))
                (fn-pull-plan-auth plan)
                (not (and (equal (fn-pull-auth-allow-clear (fn-pull-plan-auth plan)) t)
                          (fn-pull-loopback-hostp (fn-pull-plan-host plan)))))
           (let ((b (fn-pull-session-begin plan cursor now credential)))
             (and (equal (fn-pull-plan-verdict plan) :refused-clear-credential)
                  (null (fn-pull-plan-profile-path plan))
                  (equal (mv-nth 1 b)
                         (append (fn-pull-begin-effects cursor now)
                                 (list (list :close))))
                  (equal (fn-pull-session-run (car b) events) (mv (car b) nil))
                  (equal (fn-pull-close (fn-pull-s-round (car b)))
                         (fn-pull-round-cursor
                          (fn-pull-begin cursor (fn-pull-plan-wildmat plan) now))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d ()
                           (fn-pull-fail fn-pull-begin-ready fn-pull-begin-effects
                            fn-pull-session-fc0 fn-pull-loopback-hostp
                            fn-pull-session-run fn-pull-close
                            fn-pull-round-cursor fn-pull-begin)))))

; -----------------------------------------------------------------------------
; After :ready the round is PRF-100's round

; The round a session enters is the round `fn-pull-begin' reaches on the
; peer's greeting, and the session's :ready sends that transition's DATE.
(defthm fn-pull-begin-ready-is-the-round-after-the-greeting
  (implies (member-equal (fn-pull-code line) '(200 201))
           (equal (fn-pull-on-line (fn-pull-begin c w now) line)
                  (mv (fn-pull-begin-ready c w now)
                      (list (cons :remote (fn-pull-date-command)))
                      t)))
  :hints (("Goal" :in-theory (enable fn-pull-on-line))))

(defthm fn-pull-session-step-after-ready-unfolds
  (implies (and (not (fn-pull-done-p (fn-pull-s-round s)))
                (fn-pull-session-readyp s))
           (equal (fn-pull-session-step s event)
                  (mv (fn-pull-s-with-round s (car (fn-pull-step (fn-pull-s-round s) event)))
                      (mv-nth 1 (fn-pull-step (fn-pull-s-round s) event)))))
  :hints (("Goal" :in-theory (e/d (fn-pull-session-step)
                                  (fn-pull-step fn-pull-done-p fn-pull-session-readyp)))))

(defthm fn-pull-journal-effects-of-obs-effects
  (equal (fn-pull-journal-effects (fn-pull-obs-effects obs fc security)) nil)
  :hints (("Goal" :in-theory (enable fn-pull-obs-effects fn-pull-obs-effect))))

(defthm fn-pull-fail-keeps-roundp
  (implies (fn-pull-roundp r) (fn-pull-roundp (car (fn-pull-fail r))))
  :hints (("Goal" :in-theory (enable fn-pull-fail))))

(defthm fn-pull-step-keeps-roundp
  (implies (fn-pull-roundp r) (fn-pull-roundp (car (fn-pull-step r event))))
  :hints (("Goal" :in-theory (disable fn-pull-step))))

(defthm fn-pull-session-step-keeps-the-cursor-and-journals-nothing
  (and (equal (fn-pull-round-cursor (fn-pull-s-round (car (fn-pull-session-step s event))))
              (fn-pull-round-cursor (fn-pull-s-round s)))
       (implies (fn-pull-roundp (fn-pull-s-round s))
                (fn-pull-roundp (fn-pull-s-round (car (fn-pull-session-step s event)))))
       (equal (fn-pull-journal-effects (mv-nth 1 (fn-pull-session-step s event))) nil))
  :hints (("Goal" :in-theory (e/d (fn-pull-session-step fn-pull-s-with-round)
                                  (fn-pull-step fn-pull-fail fn-pull-roundp
                                   fn-pull-round-cursor fn-fc-drive
                                   fn-fc-drive-state fn-pull-obs-effects
                                   fn-pull-session-fc-events fn-pull-pre-okp)))))

(defthm fn-pull-session-run-keeps-the-cursor-and-journals-nothing
  (and (equal (fn-pull-round-cursor (fn-pull-s-round (car (fn-pull-session-run s events))))
              (fn-pull-round-cursor (fn-pull-s-round s)))
       (implies (fn-pull-roundp (fn-pull-s-round s))
                (fn-pull-roundp (fn-pull-s-round (car (fn-pull-session-run s events)))))
       (equal (fn-pull-journal-effects (mv-nth 1 (fn-pull-session-run s events))) nil))
  :hints (("Goal" :induct (fn-pull-session-run s events)
           :in-theory (e/d (fn-pull-session-run fn-pull-list)
                           (fn-pull-session-step fn-pull-roundp
                            fn-pull-round-cursor)))))

(defthm fn-pull-session-begin-round
  (and (equal (fn-pull-round-cursor
               (fn-pull-s-round (car (fn-pull-session-begin plan cursor now credential))))
              (fn-pull-round-cursor
               (fn-pull-begin cursor (fn-pull-plan-wildmat plan) now)))
       (implies (fn-pull-startable-cursorp cursor)
                (fn-pull-roundp
                 (fn-pull-s-round (car (fn-pull-session-begin plan cursor now
                                                              credential)))))
       (equal (fn-pull-journal-effects
               (mv-nth 1 (fn-pull-session-begin plan cursor now credential)))
              (fn-pull-journal-effects (fn-pull-begin-effects cursor now))))
  :hints (("Goal" :in-theory (e/d ()
                                  (fn-pull-fail fn-pull-begin-ready
                                   fn-pull-begin-effects fn-pull-session-fc0
                                   fn-pull-session-refusal fn-pull-round-cursor
                                   fn-pull-begin))
           :use ((:instance fn-pull-roundp-of-begin (c cursor)
                            (wildmat (fn-pull-plan-wildmat plan)))))))

; KEYSTONE (PRF-125, the transfer of PRF-100
; `fn-pull-journal-is-the-cursor-at-every-cut', whose statement does not
; move).  Suppose the FNPL journal replays to the owner's cursor.  Then
; after a session's beginning it replays to the cursor `fn-pull-begin'
; would have asked with; after any events of the session -- its preamble
; over TLS included -- still to the round's cursor; and after the round's
; close records to the closed cursor.  A kill at any cut of a TLS pull
; therefore recovers what a kill at the same cut of a clear pull does.
(defthm fn-pull-session-journal-is-the-cursor-at-every-cut
  (implies (and (fn-pull-startable-cursorp c)
                (equal (fn-pull-replay c0 j) c))
           (let* ((b (fn-pull-session-begin plan c now credential))
                  (j0 (append j (fn-pull-journal-effects (mv-nth 1 b))))
                  (run (fn-pull-session-run (car b) events))
                  (r (fn-pull-s-round (car run))))
             (and (equal (fn-pull-replay c0 j0)
                         (fn-pull-round-cursor
                          (fn-pull-begin c (fn-pull-plan-wildmat plan) now)))
                  (equal (fn-pull-replay
                          c0 (append j0 (fn-pull-journal-effects (mv-nth 1 run))))
                         (fn-pull-round-cursor r))
                  (equal (fn-pull-replay
                          c0 (append j0 (fn-pull-journal-effects
                                         (fn-pull-close-effects r))))
                         (fn-pull-close r)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-pull-session-begin fn-pull-session-run
                               fn-pull-close fn-pull-advancesp fn-pull-begin
                               fn-pull-round-cursor fn-pull-begin-effects
                               fn-pull-close-effects fn-pull-roundp
                               fn-pull-begin-journal-replays-to-the-round
                               fn-pull-close-journal-replays-to-the-close)
           :use ((:instance fn-pull-begin-journal-replays-to-the-round
                            (wildmat (fn-pull-plan-wildmat plan)))
                 (:instance fn-pull-close-journal-replays-to-the-close
                            (r (fn-pull-s-round
                                (car (fn-pull-session-run
                                      (car (fn-pull-session-begin plan c now credential))
                                      events))))
                            (j (append j (fn-pull-journal-effects
                                          (fn-pull-begin-effects c now)))))))))

; -----------------------------------------------------------------------------
; The host's entry points that return one value, and the log line.

(defun fn-pull-session-begin-pair (plan cursor now credential)
  (declare (xargs :guard t))
  (mv-let (s effects) (fn-pull-session-begin plan cursor now credential)
    (list s effects)))

(defun fn-pull-session-step-pair (s event)
  (declare (xargs :guard t))
  (mv-let (s2 effects) (fn-pull-session-step s event) (list s2 effects)))

(defun fn-pull-session-done-p (s)
  (declare (xargs :guard t))
  (fn-pull-done-p (fn-pull-s-round s)))

(defun fn-pull-session-close (s)
  (declare (xargs :guard t))
  (fn-pull-close (fn-pull-s-round s)))

(defun fn-pull-session-close-effects (s)
  (declare (xargs :guard t))
  (fn-pull-close-effects (fn-pull-s-round s)))

; How many octets the host may read from the peer for the next event: one
; feed-machine chunk before :ready (`fn-fwi-chunkp'), nil (the host's own
; read bound) after.
(defun fn-pull-session-read-limit (s)
  (declare (xargs :guard t))
  (if (fn-pull-session-readyp s) nil *fn-feed-wire-input-max-chunk-octets*))

(defun fn-pull-refusal-name (refusal)
  (declare (xargs :guard t))
  (cond ((equal refusal :refused-clear-credential) "clear-credential")
        ((equal refusal :refused-profile) "profile")
        ((equal refusal :refused-security) "security")
        (t "other")))

(defun fn-pull-session-log-line (s)
  (declare (xargs :guard t))
  (append (fn-pull-log-line (fn-pull-s-round s))
          (fn-record-string-octets
           (cond ((fn-pull-s-refusal s)
                  (concatenate 'string " refused="
                               (fn-pull-refusal-name (fn-pull-s-refusal s))))
                 ((not (fn-pull-session-readyp s)) " at=preamble")
                 ((fn-pull-tls-securityp (fn-pull-s-security s)) " transport=tls")
                 (t " transport=clear")))))
