; fn: the node's own web face -- the session keystones (lane web-native,
; PRF-339; split from books/web-session.lisp for the per-book time budget).
;
; The subject of every keystone is `fn-web-step', the function the host
; calls for each event of each request (host/web-host.lisp fn-web-host-step,
; from host/native/web-host.lisp fnn-web-serve).  See books/web-session.lisp
; for the design and the host protocol.

(in-package "ACL2")
(include-book "web-session")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-wr-pct-encode))))

; Octet-list and parser rules of the included world that these proofs try on
; every true-listp, octet and cdr goal and never use (accumulated-persistence
; over the whole book, 2026-09-28, lane d26-books).  None is cited below.
(local (in-theory (disable fn-cbor-octet-listp-implies-true-listp
                           fn-w47-octets-of-cdr
                           fn-ot-nat-parse-accepts-only-digits
                           fn-oct-octetp-is-unsigned-byte-p
                           fn-oct-bufp-cell-is-octet
                           fn-oct-nth-of-octet-listp-is-octet)))

; -----------------------------------------------------------------------------
; THE KEYSTONES (PRF-339).

; What the pages answer: a response, never a send or an open.
(defthm fn-wss-page-responds
  (and (consp (car (fn-wss-page code fields title main ctx config fn-web-in fn-web-out)))
       (equal (car (car (fn-wss-page code fields title main ctx config fn-web-in fn-web-out)))
              :respond))
  :hints (("Goal" :in-theory (e/d (fn-wss-page) (fn-wr-frame fn-wr-emit fn-wr-segsp fn-wr-segs-within fn-octets-clear fn-octets-append-list fn-octets-len fn-wrq-true)))))

(defthm fn-wss-redirect-responds
  (and (consp (car (fn-wss-redirect location fields ctx fn-web-out)))
       (equal (car (car (fn-wss-redirect location fields ctx fn-web-out))) :respond))
  :hints (("Goal" :in-theory (e/d (fn-wss-redirect) (fn-octets-clear)))))

(defthm fn-wss-outcome-responds
  (equal (car (car (fn-wss-outcome code kind title message detail back ctx config
                                        fn-web-in fn-web-out)))
         :respond)
  :hints (("Goal" :in-theory (enable fn-wss-outcome))))

(defthm fn-wss-trouble-responds
  (and (equal (car (car (fn-wss-trouble code title message ctx config sessions
                                             fn-web-in fn-web-out)))
              :respond)
       (equal (car (cdr (fn-wss-trouble code title message ctx config sessions
                                         fn-web-in fn-web-out)))
              sessions))
  :hints (("Goal" :in-theory (enable fn-wss-trouble))))

(defthm fn-wss-signin-page-responds
  (equal (car (car (fn-wss-signin-page code message user next ctx config fn-web-in fn-web-out)))
         :respond)
  :hints (("Goal" :in-theory (enable fn-wss-signin-page))))

(defthm fn-wss-redeem-page-responds
  (equal (car (car (fn-wss-redeem-page code message user ctx config fn-web-in fn-web-out)))
         :respond)
  :hints (("Goal" :in-theory (enable fn-wss-redeem-page))))

; The session a :begin EVENT's request names: the live session of its
; fnr_session token (what fn-wss-begin finds when nothing has expired).
(defun fn-web-begin-session (config sessions event)
  (declare (xargs :guard t))
  (let* ((request (fn-wrq-nth 1 event))
         (now (nfix (fn-wrq-nth 4 event)))
         (token (fn-web-cookie-get (fn-wrq-oct "fnr_session") (fn-web-req-cookie request))))
    (and (fn-wss-tokenp token) (fn-wss-find token sessions now (fn-wss-cfg-idle config)))))

(defun fn-web-begin-row (event)
  ; The route row a :begin EVENT's request names, or nil.
  (declare (xargs :guard t))
  (let* ((request (fn-wrq-nth 1 event))
         (r (fn-web-route (fn-web-req-method request) (fn-web-req-path request))))
    (and (equal (car r) :route) (cadr r))))

(defthm fn-wss-gate-without-session
  (implies (and (member (fn-web-row-capability row) '(:session :csrf)) (not session))
           (equal (car (car (fn-wss-gate row session sessions ctx config fn-web-in fn-web-out)))
                  :respond))
  :hints (("Goal" :in-theory (e/d (fn-wss-gate)
                                  (fn-wss-same-site fn-wss-form fn-wss-cookie-val fn-wss-tokenp
                                   fn-wss-start)))))

(defthm fn-wss-begin-without-session
  (implies (and (member (fn-web-row-capability (fn-web-begin-row event)) '(:session :csrf))
                (not (fn-web-begin-session config sessions event)))
           (member (car (car (fn-wss-begin config sessions event fn-web-in fn-web-out)))
                   '(:respond :close)))
  :hints (("Goal" :in-theory (e/d (fn-wss-begin)
                                  (fn-wss-gate fn-web-route fn-wss-expired fn-wss-ctx
                                   fn-wss-theme-of)))))

(defthm fn-web-session-route-needs-its-session
  ; KEYSTONE: a route that needs a session, begun without a live session
  ; for the request's token, sends nothing to any connection and opens
  ; none.
  (implies (and (equal (fn-wss-car event) :begin)
                (member (fn-web-row-capability (fn-web-begin-row event)) '(:session :csrf))
                (not (fn-web-begin-session config sessions event)))
           (not (member (car (car (fn-web-step config sessions flow event fn-web-in fn-web-out)))
                        '(:send :open))))
  :hints (("Goal" :in-theory (disable fn-wss-begin fn-web-begin-row fn-web-begin-session
                                      fn-web-row-capability fn-wss-begin-without-session)
           :use ((:instance fn-wss-begin-without-session))
           :expand ((fn-web-step config sessions flow event fn-web-in fn-web-out)))))

; Every send of a session route goes to its session's connection, and the
; flow it carries keeps that session.
(defun fn-web-sends-to (action cid session)
  ; ACTION is no send, or a send to CID whose flow's session is SESSION.
  (declare (xargs :guard t))
  (or (not (equal (fn-wss-car action) :send))
      (and (equal (fn-wrq-nth 1 action) cid)
           (equal (fn-wss-c-session (fn-wss-f-ctx (fn-wrq-nth 4 action))) session))))

(defthm fn-wss-send-session-sends-to
  (fn-web-sends-to (car (fn-wss-send-session route stage data octets session ctx sessions fn-web-out))
                   (fn-wss-s-cid session) (fn-wss-c-session ctx))
  :hints (("Goal" :in-theory (enable fn-wss-send-session fn-wss-flow fn-wss-f-ctx))))

(defthm fn-wss-trouble-sends-to
  (fn-web-sends-to (car (fn-wss-trouble code title message ctx config sessions fn-web-in fn-web-out))
                   cid session)
  :hints (("Goal" :in-theory (disable fn-wss-trouble))))

(defthm fn-wss-m-post-sends-to
  (fn-web-sends-to (car (fn-wss-m-post session sessions ctx config fn-web-in fn-web-out))
                   (fn-wss-s-cid session) (fn-wss-c-session ctx))
  :hints (("Goal" :in-theory (enable fn-wss-m-post fn-wss-flow fn-wss-f-ctx))))

(defthm fn-wss-m-remove-sends-to
  (fn-web-sends-to (car (fn-wss-m-remove session sessions ctx config fn-web-in fn-web-out))
                   (fn-wss-s-cid session) (fn-wss-c-session ctx))
  :hints (("Goal" :in-theory (enable fn-wss-m-remove fn-wss-flow fn-wss-f-ctx))))

(defthm fn-web-sends-to-when-not-send
  (implies (not (equal (fn-wss-car action) :send))
           (fn-web-sends-to action cid session))
  :hints (("Goal" :in-theory (enable fn-web-sends-to))))

(defthm fn-wss-car-of-cons-type
  (implies (consp x) (equal (fn-wss-car x) (car x))))

(defthm fn-web-sends-to-of-send
  (equal (fn-web-sends-to (list :send c a b f) cid session)
         (and (equal c cid) (equal (fn-wss-c-session (fn-wss-f-ctx f)) session)))
  :hints (("Goal" :in-theory (enable fn-web-sends-to))))

(defthm fn-wss-f-ctx-of-flow
  (equal (fn-wss-f-ctx (fn-wss-flow route stage ctx data)) ctx)
  :hints (("Goal" :in-theory (enable fn-wss-f-ctx fn-wss-flow))))

(in-theory (disable fn-web-sends-to fn-wss-m-post fn-wss-m-remove fn-wss-m-theme))

(defthm fn-wss-signin-page-sends-to
  (fn-web-sends-to (car (fn-wss-signin-page code message user next ctx config fn-web-in fn-web-out)) cid session)
  :hints (("Goal" :in-theory (enable fn-wss-signin-page))))

(defthm fn-wss-redeem-page-sends-to
  (fn-web-sends-to (car (fn-wss-redeem-page code message user ctx config fn-web-in fn-web-out)) cid session)
  :hints (("Goal" :in-theory (enable fn-wss-redeem-page))))

(defthm fn-wss-outcome-sends-to
  (fn-web-sends-to (car (fn-wss-outcome code kind title message detail back ctx config
                                        fn-web-in fn-web-out))
                   cid session)
  :hints (("Goal" :in-theory (enable fn-wss-outcome))))

(defthm fn-wss-m-theme-sends-to
  (fn-web-sends-to (car (fn-wss-m-theme sessions ctx fn-web-in fn-web-out)) cid session)
  :hints (("Goal" :in-theory (e/d (fn-wss-m-theme) (fn-wss-referer-path member-equal)))))

(defthm fn-wss-m-signin-sends-to
  (fn-web-sends-to (car (fn-wss-m-signin sessions ctx config fn-web-in fn-web-out)) cid session)
  :hints (("Goal" :in-theory (e/d (fn-wss-m-signin) (fn-wss-flow)))))

(defthm fn-wss-m-redeem-sends-to
  (fn-web-sends-to (car (fn-wss-m-redeem sessions ctx config fn-web-in fn-web-out)) cid session)
  :hints (("Goal" :in-theory (e/d (fn-wss-m-redeem) (fn-wss-flow)))))

(defthm fn-wss-start-sends-to
  (fn-web-sends-to (car (fn-wss-start name session sessions ctx config fn-web-in fn-web-out))
                   (fn-wss-s-cid session) (fn-wss-c-session ctx))
  :hints (("Goal" :in-theory (e/d (fn-wss-start) (fn-wss-car)))))

(defthm fn-wss-gate-sends-to
  (fn-web-sends-to (car (fn-wss-gate row session sessions ctx config fn-web-in fn-web-out))
                   (fn-wss-s-cid session) (fn-wss-c-session ctx))
  :hints (("Goal" :in-theory (e/d (fn-wss-gate)
                                  (fn-wss-same-site fn-wss-form fn-wss-cookie-val fn-wss-tokenp)))))

(defthm fn-wss-gate-sends-to-its-session
  (implies (and (equal (fn-wss-c-session ctx) session)
                (equal cid (fn-wss-s-cid session)))
           (fn-web-sends-to (car (fn-wss-gate row session sessions ctx config fn-web-in fn-web-out))
                            cid session))
  :hints (("Goal" :use fn-wss-gate-sends-to :in-theory (disable fn-wss-gate-sends-to))))

(in-theory (disable fn-wss-gate))

(defthm fn-wss-c-session-of-ctx
  (equal (fn-wss-c-session (fn-wss-ctx request bs be now n1 n2 tls family address session theme config))
         session)
  :hints (("Goal" :in-theory (enable fn-wss-ctx fn-wss-c-session))))

(defthm fn-wss-begin-sends-to
  (fn-web-sends-to (car (fn-wss-begin config sessions event fn-web-in fn-web-out))
                   (fn-wss-s-cid (fn-web-begin-session config sessions event))
                   (fn-web-begin-session config sessions event))
  :hints (("Goal" :in-theory (e/d (fn-wss-begin)
                                  (fn-wss-gate fn-web-route fn-wss-expired fn-wss-ctx
                                   fn-wss-theme-of)))))

(defthm fn-wss-k-groups-sends-to
  (fn-web-sends-to (car (fn-wss-k-groups sessions flow event config fn-web-in fn-web-out))
                   (fn-wss-s-cid (fn-wss-c-session (fn-wss-f-ctx flow)))
                   (fn-wss-c-session (fn-wss-f-ctx flow)))
  :hints (("Goal" :in-theory (e/d (fn-wss-k-groups)
                                  (fn-wss-reply fn-wss-status-fields fn-ot-decimal-octets fn-ot-decimal-parse
                                   fn-wss-reply-code fn-wss-flow)))))

(defthm fn-wss-k-group-sends-to
  (fn-web-sends-to (car (fn-wss-k-group sessions flow event config fn-web-in fn-web-out))
                   (fn-wss-s-cid (fn-wss-c-session (fn-wss-f-ctx flow)))
                   (fn-wss-c-session (fn-wss-f-ctx flow)))
  :hints (("Goal" :in-theory (e/d (fn-wss-k-group)
                                  (fn-wss-reply fn-wss-status-fields fn-ot-decimal-octets fn-ot-decimal-parse
                                   fn-wss-reply-code fn-wss-flow)))))

(defthm fn-wss-k-article-sends-to
  (fn-web-sends-to (car (fn-wss-k-article sessions flow event config fn-web-in fn-web-out))
                   (fn-wss-s-cid (fn-wss-c-session (fn-wss-f-ctx flow)))
                   (fn-wss-c-session (fn-wss-f-ctx flow)))
  :hints (("Goal" :in-theory (e/d (fn-wss-k-article)
                                  (fn-wss-reply fn-wss-status-fields fn-ot-decimal-octets fn-ot-decimal-parse
                                   fn-wss-reply-code fn-wss-flow)))))

(defthm fn-wss-k-submit-sends-to
  (fn-web-sends-to (car (fn-wss-k-submit sessions flow event config fn-web-in fn-web-out))
                   (fn-wss-s-cid (fn-wss-c-session (fn-wss-f-ctx flow)))
                   (fn-wss-c-session (fn-wss-f-ctx flow)))
  :hints (("Goal" :in-theory (e/d (fn-wss-k-submit)
                                  (fn-wss-reply fn-wss-status-fields fn-ot-decimal-octets fn-ot-decimal-parse
                                   fn-wss-reply-code fn-wss-flow)))))

(defthm fn-web-session-sends-only-to-its-connection
  ; KEYSTONE: at a request's first step, anything sent goes to the
  ; connection of the session the request's own token names, and the flow
  ; keeps that session; at a later step of a session route, to the flow's
  ; session's connection.  With fn-web-sessions-bound-by-281 below: what a
  ; session reads is what the node answers the connection its own AUTHINFO
  ; authenticated -- the same group access an NNTP reader with that login
  ; gets (books/group-access.lisp), by construction.
  (and (implies (equal (fn-wss-car event) :begin)
                (fn-web-sends-to (car (fn-web-step config sessions flow event fn-web-in fn-web-out))
                                 (fn-wss-s-cid (fn-web-begin-session config sessions event))
                                 (fn-web-begin-session config sessions event)))
       (implies (and (not (equal (fn-wss-car event) :begin))
                     (member (fn-wss-f-route flow) '(:groups :group :article :post :remove)))
                (fn-web-sends-to (car (fn-web-step config sessions flow event fn-web-in fn-web-out))
                                 (fn-wss-s-cid (fn-wss-c-session (fn-wss-f-ctx flow)))
                                 (fn-wss-c-session (fn-wss-f-ctx flow)))))
  :hints (("Goal" :in-theory (disable fn-wss-begin fn-web-begin-session fn-wss-k-groups
                                      fn-wss-k-group fn-wss-k-article fn-wss-k-submit)
           :expand ((fn-web-step config sessions flow event fn-web-in fn-web-out)))))

; --- Sessions come only from a 281.

(defun fn-wss-tokens (sessions)
  (declare (xargs :guard t))
  (if (consp sessions)
      (cons (fn-wss-s-token (car sessions)) (fn-wss-tokens (cdr sessions)))
    nil))

(defthm fn-wss-member-token
  (implies (member-equal s sessions)
           (member-equal (fn-wss-s-token s) (fn-wss-tokens sessions))))

(defthm fn-wss-tokens-drop
  (implies (member-equal x (fn-wss-tokens (fn-wss-drop tok sessions)))
           (member-equal x (fn-wss-tokens sessions)))
  :hints (("Goal" :in-theory (enable fn-wss-drop))))

(defthm fn-wss-tokens-touch
  (implies (member-equal x (fn-wss-tokens (fn-wss-touch tok sessions now)))
           (member-equal x (fn-wss-tokens sessions)))
  :hints (("Goal" :in-theory (enable fn-wss-touch fn-wss-s-token fn-wss-session))))

; The connection and login of the AUTHINFO a sign-in flow sent.
(defun fn-wss-flow-cid (flow)
  (declare (xargs :guard t))
  (if (equal (fn-wss-f-route flow) :signin)
      (fn-wrq-nth 2 (fn-wss-f-data flow))
    (fn-wrq-nth 1 (fn-wss-f-data flow))))

(defun fn-wss-flow-login (flow)
  (declare (xargs :guard t))
  (fn-wrq-nth 0 (fn-wss-f-data flow)))

(defun fn-wss-bound-by-281 (s flow event fn-web-in)
  ; S is the session an AUTHINFO answered 281 made: the flow is a sign-in
  ; waiting for AUTHINFO's replies, this event is those replies, the second
  ; (PASS's) is 281, and S is bound to the connection the flow sent them on,
  ; for the login the flow named.
  (declare (xargs :stobjs fn-web-in :guard t))
  (and (member (fn-wss-f-route flow) '(:signin :redeem))
       (equal (fn-wss-f-stage flow) :sent)
       (equal (fn-wss-car event) :reply)
       (equal (fn-wrq-nth 1 (fn-wss-reply-codes fn-web-in)) 281)
       (equal (fn-wss-s-cid s) (fn-wss-flow-cid flow))
       (equal (fn-wss-s-login s) (fn-wr-octets-only (fn-wss-flow-login flow)))))

(defthm fn-wss-session-fields
  (and (equal (fn-wss-s-token (fn-wss-session token cid login csrf used)) token)
       (equal (fn-wss-s-cid (fn-wss-session token cid login csrf used)) cid)
       (equal (fn-wss-s-login (fn-wss-session token cid login csrf used)) (fn-wr-octets-only login)))
  :hints (("Goal" :in-theory (enable fn-wss-session fn-wss-s-token fn-wss-s-cid fn-wss-s-login))))

(defthm fn-wss-after-authinfo-sessions
  (let ((new (car (cdr (fn-wss-after-authinfo route login next cid config sessions ctx
                                              fn-web-in fn-web-out)))))
    (implies (and (member-equal s new)
                  (not (member-equal (fn-wss-s-token s) (fn-wss-tokens sessions))))
             (and (equal (nth 1 (fn-wss-reply-codes fn-web-in)) 281)
                  (equal (fn-wss-s-cid s) cid)
                  (equal (fn-wss-s-login s) (fn-wr-octets-only login)))))
  :hints (("Goal" :in-theory (e/d (fn-wss-after-authinfo fn-wss-new-session)
                                  (fn-wss-redirect fn-wss-reply-codes fn-wss-session)))))

(defthm fn-wss-leaves-sessions
  (and (equal (car (cdr (fn-wss-send-session route stage data octets session ctx sessions fn-web-out))) sessions)
       (equal (car (cdr (fn-wss-m-post session sessions ctx config fn-web-in fn-web-out))) sessions)
       (equal (car (cdr (fn-wss-m-remove session sessions ctx config fn-web-in fn-web-out))) sessions)
       (equal (car (cdr (fn-wss-m-theme sessions ctx fn-web-in fn-web-out))) sessions)
       (equal (car (cdr (fn-wss-m-signin sessions ctx config fn-web-in fn-web-out))) sessions)
       (equal (car (cdr (fn-wss-m-redeem sessions ctx config fn-web-in fn-web-out))) sessions))
  :hints (("Goal" :in-theory (e/d (fn-wss-send-session fn-wss-m-post fn-wss-m-remove fn-wss-m-theme
                                   fn-wss-m-signin fn-wss-m-redeem)
                                  (fn-wss-referer-path member-equal fn-wss-flow)))))

(defthm fn-wss-start-leaves-sessions
  (equal (car (cdr (fn-wss-start name session sessions ctx config fn-web-in fn-web-out))) sessions)
  :hints (("Goal" :in-theory (enable fn-wss-start))))

(defthm fn-wss-gate-leaves-sessions
  (equal (car (cdr (fn-wss-gate row session sessions ctx config fn-web-in fn-web-out))) sessions)
  :hints (("Goal" :in-theory (e/d (fn-wss-gate)
                                  (fn-wss-same-site fn-wss-form fn-wss-cookie-val fn-wss-tokenp)))))

(defthm fn-wss-k-reads-leave-sessions
  (and (equal (car (cdr (fn-wss-k-groups sessions flow event config fn-web-in fn-web-out))) sessions)
       (equal (car (cdr (fn-wss-k-group sessions flow event config fn-web-in fn-web-out))) sessions)
       (equal (car (cdr (fn-wss-k-article sessions flow event config fn-web-in fn-web-out))) sessions)
       (equal (car (cdr (fn-wss-k-submit sessions flow event config fn-web-in fn-web-out))) sessions))
  :hints (("Goal" :in-theory (e/d (fn-wss-k-groups fn-wss-k-group fn-wss-k-article fn-wss-k-submit)
                                  (fn-wss-reply fn-wss-status-fields fn-ot-decimal-octets fn-ot-decimal-parse
                                   fn-wss-reply-code fn-wss-flow)))))

(defthm fn-wss-begin-sessions
  (implies (member-equal x (fn-wss-tokens (car (cdr (fn-wss-begin config sessions event
                                                                  fn-web-in fn-web-out)))))
           (member-equal x (fn-wss-tokens sessions)))
  :hints (("Goal" :in-theory (e/d (fn-wss-begin)
                                  (fn-wss-gate fn-web-route fn-wss-expired fn-wss-ctx
                                   fn-wss-theme-of)))))

(defthm fn-wss-begin-member-token
  (implies (member-equal s (car (cdr (fn-wss-begin config sessions event fn-web-in fn-web-out))))
           (member-equal (fn-wss-s-token s) (fn-wss-tokens sessions)))
  :hints (("Goal" :in-theory (disable fn-wss-begin-sessions fn-wss-member-token)
           :use ((:instance fn-wss-member-token
                  (sessions (car (cdr (fn-wss-begin config sessions event fn-web-in fn-web-out)))))
                 (:instance fn-wss-begin-sessions (x (fn-wss-s-token s)))))))

(defthm fn-wss-drop-member-token
  (implies (member-equal s (fn-wss-drop tok sessions))
           (member-equal (fn-wss-s-token s) (fn-wss-tokens sessions)))
  :hints (("Goal" :in-theory (enable fn-wss-drop))))

(defthm fn-wss-k-signin-sessions
  (let ((new (car (cdr (fn-wss-k-signin sessions flow event config fn-web-in fn-web-out)))))
    (implies (and (equal (fn-wss-f-route flow) :signin)
                  (member-equal s new)
                  (not (member-equal (fn-wss-s-token s) (fn-wss-tokens sessions))))
             (fn-wss-bound-by-281 s flow event fn-web-in)))
  :hints (("Goal" :in-theory (e/d (fn-wss-k-signin)
                                  (fn-wss-after-authinfo fn-wss-signin-refused fn-wss-write
                                   fn-wss-flow fn-wss-reply-codes)))))

(defthm fn-wss-k-redeem-sessions
  (let ((new (car (cdr (fn-wss-k-redeem sessions flow event config fn-web-in fn-web-out)))))
    (implies (and (equal (fn-wss-f-route flow) :redeem)
                  (member-equal s new)
                  (not (member-equal (fn-wss-s-token s) (fn-wss-tokens sessions))))
             (fn-wss-bound-by-281 s flow event fn-web-in)))
  :hints (("Goal" :in-theory (e/d (fn-wss-k-redeem)
                                  (fn-wss-after-authinfo fn-wss-signin-refused fn-wss-redeem-refused
                                   fn-wss-write fn-wss-flow fn-wss-reply-codes)))))

(defthm fn-web-sessions-bound-by-281
  ; KEYSTONE: a session the step's table holds whose token the table did
  ; not hold before was made by an AUTHINFO the node answered 281 (PASS's
  ; reply), and is bound to the connection that AUTHINFO was sent on, for
  ; the login it named.  Every other change drops or touches a session.
  (let ((new (car (cdr (fn-web-step config sessions flow event fn-web-in fn-web-out)))))
    (implies (and (member-equal s new)
                  (not (member-equal (fn-wss-s-token s) (fn-wss-tokens sessions))))
             (fn-wss-bound-by-281 s flow event fn-web-in)))
  :hints (("Goal" :in-theory (disable fn-wss-begin fn-wss-k-signin fn-wss-k-redeem fn-wss-k-groups
                                      fn-wss-k-group fn-wss-k-article fn-wss-k-submit
                                      fn-wss-bound-by-281 fn-wss-trouble fn-wss-redirect)
           :expand ((fn-web-step config sessions flow event fn-web-in fn-web-out)))))
