; Teeth for the outbound feed's protected channel (PRF-047, PRF-051; plan
; 2026-09-22 T9c).
;
;   fn-fc-offers-and-credentials-wait-for-tls-and-login
;   fn-fc-refused-login-closes-without-an-offer
;   fn-fc-starttls-refusal-closes-before-the-credential
;   fn-fc-auth-user-command-sends-the-configured-name-alone
;   fn-fc-auth-pass-command-sends-the-configured-secret-alone
;   fn-fc-decoded-profile-renders-verbatim-in-every-state
;                                    (all books/feed-connection-invariants)
;
; The subjects are `fn-fc-step' (host/owner-host.lisp:1374, in
; `fn-owner-feed-reply-chunk', which host/native/feed-service.lisp:256 calls),
; `fn-fc-after-tls' (owner-host.lisp:1279, in `fn-owner-feed-tls-established',
; feed-service.lisp:194), and the two AUTHINFO renderers the host calls on the
; step's next state (owner-host.lisp:1288, :1388, :1393).
;
; WHAT A TOOTH IS HERE (AGENTS.md, "Teeth ship with the theorem").  For each
; keystone: a reachable, non-degenerate witness -- a connection built by the
; constructor `fn-owner-feed-dial-open' uses, from a credential profile
; `fn-fap-decode' accepts, driven through the replies a real peer sends --
; and one `must-fail' per hypothesis, that hypothesis dropped and every other
; one and the original hints kept, with the concrete value that refutes the
; weakened statement evaluated beside it.  The must-fails are asked not to
; induct (store-files-teeth-tests has the reason: a false goal the prover
; inducts on may not come back).  The one keystone with no hypothesis has a
; `must-fail' for the nearby statement that is false: the same rendering
; claim over a credential that did NOT come through `fn-fap-decode'.
;
; Every expected observation list is written out here from RFC 3977, 4642
; and 4643's reply codes, never computed by the function under test.

(in-package "ACL2")
(include-book "../../books/feed-connection-invariants")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; The scenario.  A profile file `FNAUTH1\nnode\nsecret\n', the replies a peer
; sends, and the connections `fn-owner-feed-dial-open' installs for it.

(defconst *fct-profile*
  '(70 78 65 85 84 72 49 10 110 111 100 101 10 115 101 99 114 101 116 10))
(defconst *fct-user* '(110 111 100 101))            ; node
(defconst *fct-pass* '(115 101 99 114 101 116))     ; secret
(assert-event (equal (fn-fap-decode *fct-profile*)
                     (list :ok *fct-user* *fct-pass*)))

(defconst *fct-200* '(50 48 48 32 111 107 13 10))   ; 200 ok
(defconst *fct-382* '(51 56 50 13 10))
(defconst *fct-381* '(51 56 49 13 10))
(defconst *fct-281* '(50 56 49 13 10))
(defconst *fct-203* '(50 48 51 13 10))
(defconst *fct-238* '(50 51 56 13 10))
(defconst *fct-481* '(52 56 49 13 10))
(defconst *fct-502* '(53 48 50 13 10))
(defconst *fct-580* '(53 56 48 13 10))

; What `fn-owner-feed-dial-open' installs for a streaming STARTTLS peer with
; a credential, for an implicit-TLS one, for a STARTTLS one without a
; credential, and for a clear one whose profile did not permit clear text.
(defconst *fct-starttls*
  (fn-fc-initial-auth-state t 7 :starttls
                            (cadr (fn-fap-decode *fct-profile*))
                            (caddr (fn-fap-decode *fct-profile*)) nil))
(defconst *fct-implicit*
  (fn-fc-initial-auth-state t 8 :implicit *fct-user* *fct-pass* nil))
(defconst *fct-tls-anon* (fn-fc-initial-state t 9 :starttls))
(defconst *fct-clear-refused*
  (fn-fc-initial-auth-state t 10 :clear *fct-user* *fct-pass* nil))
(assert-event (and (fn-fc-statep *fct-starttls*) (fn-fc-statep *fct-implicit*)
                   (fn-fc-statep *fct-tls-anon*)
                   (fn-fc-statep *fct-clear-refused*)))
(assert-event (and (fn-fc-protected-profilep *fct-starttls*)
                   (fn-fc-opening-phasep *fct-starttls*)
                   (fn-fc-protected-profilep *fct-implicit*)
                   (fn-fc-opening-phasep *fct-implicit*)
                   (fn-fc-protected-profilep *fct-tls-anon*)
                   (fn-fc-opening-phasep *fct-tls-anon*)
                   (fn-fc-protected-profilep *fct-clear-refused*)
                   (fn-fc-opening-phasep *fct-clear-refused*)))

; -----------------------------------------------------------------------------
; Keystone 1: fn-fc-offers-and-credentials-wait-for-tls-and-login.
;
; The witness: greeting, STARTTLS answered 382, the handshake reported, USER
; answered 381, PASS answered 281, MODE STREAM answered 203, and a CHECK
; reply.  The whole observation list is written out: the kinds the host acts
; on, in order, with the code of the line each step consumed.
(defconst *fct-full-trace*
  (list *fct-200* *fct-382* :tls-up *fct-381* *fct-281* *fct-203* *fct-238*))
(assert-event
 (equal (fn-fc-drive *fct-starttls* *fct-full-trace*)
        '((:starttls 200 nil) (:tls 382 nil) (:auth-user nil t)
          (:auth-pass 381 nil) (:mode 281 nil) (:ready 203 nil)
          (:reply 238 nil))))
(assert-event (fn-fc-gate-okp 0 t (fn-fc-drive *fct-starttls* *fct-full-trace*)))
; The credential the host sends at :auth-user and :auth-pass on that trace is
; the profile's, one line each.
(assert-event
 (equal (fn-fc-auth-user-command
         (fn-fc-drive-state *fct-starttls* (list *fct-200* *fct-382* :tls-up)))
        '(65 85 84 72 73 78 70 79 32 85 83 69 82 32 110 111 100 101 13 10)))
(assert-event
 (equal (fn-fc-auth-pass-command
         (fn-fc-drive-state *fct-starttls*
                            (list *fct-200* *fct-382* :tls-up *fct-381*)))
        '(65 85 84 72 73 78 70 79 32 80 65 83 83 32
          115 101 99 114 101 116 13 10)))

; Implicit TLS: the handshake first, then the greeting, then the login.
(defconst *fct-implicit-trace*
  (list :tls-up *fct-200* *fct-281* *fct-203* *fct-238*))
(assert-event
 (equal (fn-fc-drive *fct-implicit* *fct-implicit-trace*)
        '((:need-input nil t) (:auth-user 200 nil) (:mode 281 nil)
          (:ready 203 nil) (:reply 238 nil))))
(assert-event (fn-fc-gate-okp 1 t (fn-fc-drive *fct-implicit* *fct-implicit-trace*)))

; A STARTTLS peer without a credential goes live after the handshake alone.
(assert-event
 (equal (fn-fc-drive *fct-tls-anon* (list *fct-200* *fct-382* :tls-up *fct-203*))
        '((:starttls 200 nil) (:tls 382 nil) (:mode nil t) (:ready 203 nil))))
(assert-event
 (fn-fc-gate-okp 0 nil (fn-fc-drive *fct-tls-anon*
                                    (list *fct-200* *fct-382* :tls-up *fct-203*))))

; A clear-text peer whose profile did not permit clear text: refused at the
; greeting, before any AUTHINFO line.
(assert-event
 (equal (fn-fc-drive *fct-clear-refused* (list *fct-200* :tls-up *fct-281*))
        '((:refused 200 nil) (:invalid nil t) (:closed 281 nil))))

; The property has teeth of its own: these hand-written observation lists,
; which no connection above produced, are the orders it rejects.  A ready
; before the 382; a credential before the TLS report; a 281 read before the
; TLS report does not count as the login; a TLS report the machine refused
; does not count as the handshake.
(assert-event (not (fn-fc-gate-okp 0 t '((:ready 200 nil)))))
(assert-event (not (fn-fc-gate-okp 0 t '((:starttls 200 nil) (:tls 382 nil)
                                         (:auth-user 381 nil)))))
(assert-event (not (fn-fc-gate-okp 0 t '((:tls 382 nil) (:mode 281 nil)
                                         (:auth-user nil t) (:ready 203 nil)))))
(assert-event (not (fn-fc-gate-okp 0 t '((:tls 382 nil) (:invalid nil t)
                                         (:auth-user nil nil)))))
(assert-event (not (fn-fc-gate-okp 0 nil '((:tls 382 nil) (:ready 203 nil)))))

; Each must-fail below is the keystone with one hypothesis dropped, under the
; keystone's own hints; `fct-gate-full', the keystone itself through the same
; macro, is admitted first so that a must-fail cannot pass on a hint that
; stopped working.
(defmacro fct-gate-thm (name hyps)
  `(defthm ,name
     (implies (and ,@hyps)
              (fn-fc-gate-okp (fn-fc-gate-start (fn-fc-security st))
                              (fn-fc-loginp st)
                              (fn-fc-drive st events)))
     :hints (("Goal" :do-not-induct t
              :use ((:instance fn-fc-gate-holds-above-the-floor
                               (k (fn-fc-gate-start (fn-fc-security st)))))
              :in-theory (e/d (fn-fc-opening-phasep fn-fc-gate-floor
                               fn-fc-gate-start)
                              (fn-fc-gate-holds-above-the-floor
                               fn-fc-protected-profilep fn-fc-loginp
                               fn-fc-drive fn-fc-gate-okp))))))
(fct-gate-thm fct-gate-full
  ((fn-fc-protected-profilep st) (fn-fc-opening-phasep st)))

; Teeth.  Without `fn-fc-protected-profilep': a clear peer with no credential
; goes live on the greeting, at stage 0; and a clear peer whose profile DID
; permit clear text sends USER at stage 0 -- which is what the credential
; disjunct's `(not (fn-fc-allow-clear st))' excludes.
(defconst *fct-clear-open* (fn-fc-initial-state t 11 :clear))
(assert-event (not (fn-fc-protected-profilep *fct-clear-open*)))
(assert-event (equal (fn-fc-drive *fct-clear-open* (list *fct-200*))
                     '((:mode 200 nil))))
(assert-event (not (fn-fc-gate-okp 0 nil (fn-fc-drive *fct-clear-open*
                                                      (list *fct-200*)))))
(defconst *fct-clear-permitted*
  (fn-fc-initial-auth-state t 12 :clear *fct-user* *fct-pass* t))
(assert-event (not (fn-fc-protected-profilep *fct-clear-permitted*)))
(assert-event (equal (fn-fc-drive *fct-clear-permitted* (list *fct-200*))
                     '((:auth-user 200 nil))))
(assert-event (not (fn-fc-gate-okp 0 t (fn-fc-drive *fct-clear-permitted*
                                                    (list *fct-200*)))))
(local
 (must-fail
  (fct-gate-thm fct-gate-without-protected-profile ((fn-fc-opening-phasep st)))))

; Without `fn-fc-opening-phasep': a STARTTLS connection with a credential
; that is already in the ready phase (never through 382, TLS or 281) hands
; the next reply to the feed port at stage 0.
(defconst *fct-ready-unopened*
  (fn-fc-make-state (fn-fwi-initial-state) t :ready 13 :starttls))
(assert-event (and (fn-fc-statep *fct-ready-unopened*)
                   (fn-fc-protected-profilep *fct-ready-unopened*)
                   (not (fn-fc-opening-phasep *fct-ready-unopened*))))
(assert-event (equal (fn-fc-drive *fct-ready-unopened* (list *fct-238*))
                     '((:reply 238 nil))))
(assert-event (not (fn-fc-gate-okp 0 nil (fn-fc-drive *fct-ready-unopened*
                                                      (list *fct-238*)))))
(local
 (must-fail
  (fct-gate-thm fct-gate-without-opening-phase ((fn-fc-protected-profilep st)))))

; -----------------------------------------------------------------------------
; Keystone 2: fn-fc-refused-login-closes-without-an-offer.
;
; The witness: the reachable :auth-pass state of the full trace, answered 481
; (RFC 4643 section 2.3.2, authentication failed).  Refused, closed, and a
; peer that then pretends the login succeeded gets nothing.
(defconst *fct-at-pass*
  (fn-fc-drive-state *fct-starttls* (list *fct-200* *fct-382* :tls-up *fct-381*)))
(defconst *fct-at-user*
  (fn-fc-drive-state *fct-starttls* (list *fct-200* *fct-382* :tls-up)))
(assert-event (equal (fn-fc-phase *fct-at-pass*) :auth-pass))
(assert-event (equal (fn-fc-phase *fct-at-user*) :auth-user))
(assert-event (equal (fn-fc-kind (fn-fc-step *fct-at-pass* *fct-481*)) :refused))
(assert-event (equal (fn-fc-phase (fn-fc-next-state (fn-fc-step *fct-at-pass* *fct-481*)))
                     :closed))
(assert-event
 (equal (fn-fc-drive (fn-fc-next-state (fn-fc-step *fct-at-pass* *fct-481*))
                     (list *fct-281* :tls-up *fct-203* *fct-238*))
        '((:closed 281 nil) (:invalid nil t) (:closed 203 nil) (:closed 238 nil))))
; And USER answered 481 (no PASS asked for) is refused the same way.
(assert-event (equal (fn-fc-kind (fn-fc-step *fct-at-user* *fct-481*)) :refused))

; The one conclusion keystones 2 and 3 share, and the hints both use: each
; must-fail below is this theorem with one hypothesis dropped.
(defmacro fct-closes-quietly-thm (name hyps)
  `(defthm ,name
     (implies (and ,@hyps)
              (let ((r (fn-fc-step st octets)))
                (and (equal (fn-fc-kind r) :refused)
                     (equal (fn-fc-phase (fn-fc-next-state r)) :closed)
                     (fn-fc-quiet-obsp (fn-fc-drive (fn-fc-next-state r) events)))))
     :hints (("Goal" :do-not-induct t
              :in-theory (e/d (fn-fc-step fn-fc-from-line fn-fc-result
                               fn-fc-kind fn-fc-next-state)
                              (fn-fc-statep fn-fwi-step fn-fwi-chunkp
                               fn-own-feed-response-code fn-fc-drive
                               fn-fc-with-input-phase fn-fc-phase
                               fn-fc-security fn-fc-user fn-fc-allow-clear
                               fn-fc-input fn-fc-streamingp fn-fc-conn
                               fn-fwi-kind fn-fwi-line fn-fwi-next-state))))))

(defconst *fct-hyp-statep* '(fn-fc-statep st))
(defconst *fct-hyp-login-phase*
  '(member-equal (fn-fc-phase st) '(:auth-user :auth-pass)))
(defconst *fct-hyp-starttls-phase* '(equal (fn-fc-phase st) :starttls))
(defconst *fct-hyp-line*
  '(equal (fn-fwi-kind (fn-fwi-step (fn-fc-input st) octets)) :line))
(defconst *fct-hyp-not-281*
  '(not (equal (fn-own-feed-response-code
                (fn-fwi-line (fn-fwi-step (fn-fc-input st) octets)))
               281)))
(defconst *fct-hyp-not-381*
  '(or (equal (fn-fc-phase st) :auth-pass)
       (not (equal (fn-own-feed-response-code
                    (fn-fwi-line (fn-fwi-step (fn-fc-input st) octets)))
                   381))))
(defconst *fct-hyp-not-382*
  '(not (equal (fn-own-feed-response-code
                (fn-fwi-line (fn-fwi-step (fn-fc-input st) octets)))
               382)))

; The keystones themselves, through the macro and its hints, are admitted
; first, so that no must-fail below can pass on a hint that stopped working.
(make-event
 `(fct-closes-quietly-thm fct-refused-login-full
    (,*fct-hyp-statep* ,*fct-hyp-login-phase* ,*fct-hyp-line*
     ,*fct-hyp-not-281* ,*fct-hyp-not-381*)))
(make-event
 `(fct-closes-quietly-thm fct-starttls-refusal-full
    (,*fct-hyp-statep* ,*fct-hyp-starttls-phase* ,*fct-hyp-line*
     ,*fct-hyp-not-382*)))

; Without `fn-fc-statep': a list in the :auth-pass phase whose security is no
; security the machine knows is not a connection, and the step refuses to
; interpret it at all (:invalid), which is not the :refused the host closes on.
(defconst *fct-not-a-state*
  (fn-fc-make-state (fn-fwi-initial-state) t :auth-pass 14 :bogus))
(assert-event (not (fn-fc-statep *fct-not-a-state*)))
(assert-event (equal (fn-fc-kind (fn-fc-step *fct-not-a-state* *fct-481*)) :invalid))
(local
 (must-fail
  (make-event
   `(fct-closes-quietly-thm fct-refused-login-without-statep
      (,*fct-hyp-login-phase* ,*fct-hyp-line* ,*fct-hyp-not-281* ,*fct-hyp-not-381*)))))

; Without the login-phase hypothesis: the same 481 line in the ready phase is
; a feed reply, not a refusal.
(assert-event (equal (fn-fc-kind (fn-fc-step *fct-ready-unopened* *fct-481*)) :reply))
(local
 (must-fail
  (make-event
   `(fct-closes-quietly-thm fct-refused-login-without-phase
      (,*fct-hyp-statep* ,*fct-hyp-line* ,*fct-hyp-not-281* ,*fct-hyp-not-381*)))))

; Without the complete-line hypothesis: half a reply is retained, not refused.
(defconst *fct-half* '(52 56))
(assert-event (not (equal (fn-fwi-kind (fn-fwi-step (fn-fc-input *fct-at-pass*)
                                                    *fct-half*))
                          :line)))
(assert-event (not (equal (fn-own-feed-response-code
                           (fn-fwi-line (fn-fwi-step (fn-fc-input *fct-at-pass*)
                                                     *fct-half*)))
                          281)))
(assert-event (equal (fn-fc-kind (fn-fc-step *fct-at-pass* *fct-half*)) :need-input))
(local
 (must-fail
  (make-event
   `(fct-closes-quietly-thm fct-refused-login-without-a-line
      (,*fct-hyp-statep* ,*fct-hyp-login-phase* ,*fct-hyp-not-281* ,*fct-hyp-not-381*)))))

; Without "not 281": 281 is the login, and the connection proceeds to MODE.
(assert-event (equal (fn-fc-kind (fn-fc-step *fct-at-pass* *fct-281*)) :mode))
(local
 (must-fail
  (make-event
   `(fct-closes-quietly-thm fct-refused-login-without-not-281
      (,*fct-hyp-statep* ,*fct-hyp-login-phase* ,*fct-hyp-line* ,*fct-hyp-not-381*)))))

; Without "USER not answered 381": 381 to USER asks for the password.
(assert-event (equal (fn-fc-kind (fn-fc-step *fct-at-user* *fct-381*)) :auth-pass))
(local
 (must-fail
  (make-event
   `(fct-closes-quietly-thm fct-refused-login-without-not-381
      (,*fct-hyp-statep* ,*fct-hyp-login-phase* ,*fct-hyp-line* ,*fct-hyp-not-281*)))))

; -----------------------------------------------------------------------------
; Keystone 3: fn-fc-starttls-refusal-closes-before-the-credential.
;
; The witness: the reachable :starttls state, answered 502 and 580 (RFC 4642
; section 2.2.1).  Refused, closed, and the credential never leaves: a later
; 382, TLS report and 281 all find a closed connection.
(defconst *fct-at-starttls*
  (fn-fc-drive-state *fct-starttls* (list *fct-200*)))
(assert-event (equal (fn-fc-phase *fct-at-starttls*) :starttls))
(assert-event (equal (fn-fc-kind (fn-fc-step *fct-at-starttls* *fct-502*)) :refused))
(assert-event (equal (fn-fc-kind (fn-fc-step *fct-at-starttls* *fct-580*)) :refused))
(assert-event
 (equal (fn-fc-drive *fct-starttls*
                     (list *fct-200* *fct-580* *fct-382* :tls-up *fct-281*))
        '((:starttls 200 nil) (:refused 580 nil) (:closed 382 nil)
          (:invalid nil t) (:closed 281 nil))))

(defconst *fct-not-a-state-starttls*
  (fn-fc-make-state (fn-fwi-initial-state) t :starttls 15 :bogus))
(assert-event (not (fn-fc-statep *fct-not-a-state-starttls*)))
(assert-event (equal (fn-fc-kind (fn-fc-step *fct-not-a-state-starttls* *fct-580*))
                     :invalid))
(local
 (must-fail
  (make-event
   `(fct-closes-quietly-thm fct-starttls-refusal-without-statep
      (,*fct-hyp-starttls-phase* ,*fct-hyp-line* ,*fct-hyp-not-382*)))))

; Without the phase: 580 in the ready phase is a feed reply.
(assert-event (equal (fn-fc-kind (fn-fc-step *fct-ready-unopened* *fct-580*)) :reply))
(local
 (must-fail
  (make-event
   `(fct-closes-quietly-thm fct-starttls-refusal-without-phase
      (,*fct-hyp-statep* ,*fct-hyp-line* ,*fct-hyp-not-382*)))))

; Without the complete-line hypothesis: half a reply waits.
(assert-event (equal (fn-fc-kind (fn-fc-step *fct-at-starttls* '(53 56))) :need-input))
(assert-event (not (equal (fn-own-feed-response-code
                           (fn-fwi-line (fn-fwi-step (fn-fc-input *fct-at-starttls*)
                                                     '(53 56))))
                          382)))
(local
 (must-fail
  (make-event
   `(fct-closes-quietly-thm fct-starttls-refusal-without-a-line
      (,*fct-hyp-statep* ,*fct-hyp-starttls-phase* ,*fct-hyp-not-382*)))))

; Without "not 382": 382 starts the handshake.
(assert-event (equal (fn-fc-kind (fn-fc-step *fct-at-starttls* *fct-382*)) :tls))
(local
 (must-fail
  (make-event
   `(fct-closes-quietly-thm fct-starttls-refusal-without-not-382
      (,*fct-hyp-statep* ,*fct-hyp-starttls-phase* ,*fct-hyp-line*)))))

; -----------------------------------------------------------------------------
; Keystones 4 and 5: the AUTHINFO renderers the host calls send the
; configured name and secret alone.
;
; The witness is the decoded profile's (above, on the reachable states).
; Without `fn-fap-tokenp': a name carrying CRLF and a second command renders
; only the first line, so the statement's one-line equation is false (and a
; profile with it is one `fn-fap-decode' refuses).  Without `true-listp': an
; improper token renders nothing.
(defconst *fct-smuggled* '(110 13 10 81 85 73 84))   ; n CR LF QUIT
(defconst *fct-improper* '(110 111 . 100))
(assert-event (not (fn-fap-tokenp *fct-smuggled*)))
(assert-event (and (fn-fap-tokenp *fct-improper*) (not (true-listp *fct-improper*))))
(defconst *fct-smuggling-state*
  (fn-fc-initial-auth-state t 16 :starttls *fct-smuggled* *fct-smuggled* nil))
(defconst *fct-improper-state*
  (fn-fc-initial-auth-state t 17 :starttls *fct-improper* *fct-improper* nil))
(assert-event
 (equal (fn-fc-auth-user-command *fct-smuggling-state*)
        '(65 85 84 72 73 78 70 79 32 85 83 69 82 32 110 13 10)))
(assert-event
 (not (equal (fn-fc-auth-user-command *fct-smuggling-state*)
             (append *fn-fc-auth-user-prefix* *fct-smuggled* '(13 10)))))
(assert-event
 (not (equal (fn-fc-auth-pass-command *fct-smuggling-state*)
             (append *fn-fc-auth-pass-prefix* *fct-smuggled* '(13 10)))))
(assert-event (equal (fn-fc-auth-user-command *fct-improper-state*) nil))
(assert-event (equal (fn-fc-auth-pass-command *fct-improper-state*) nil))
; As above: the keystones through the macro first, then one hypothesis
; dropped from each.
(defmacro fct-render-thm (name command field prefix hyps)
  `(defthm ,name
     (implies (and ,@hyps)
              (equal (,command st) (append ,prefix (,field st) '(13 10))))
     :hints (("Goal" :do-not-induct t
              :in-theory (e/d (,command) (fn-fc-auth-command fn-fap-tokenp))))))
(fct-render-thm fct-user-command-full fn-fc-auth-user-command fn-fc-user
  *fn-fc-auth-user-prefix*
  ((fn-fap-tokenp (fn-fc-user st)) (true-listp (fn-fc-user st))))
(fct-render-thm fct-pass-command-full fn-fc-auth-pass-command fn-fc-pass
  *fn-fc-auth-pass-prefix*
  ((fn-fap-tokenp (fn-fc-pass st)) (true-listp (fn-fc-pass st))))
(local
 (must-fail
  (fct-render-thm fct-user-command-without-tokenp fn-fc-auth-user-command
    fn-fc-user *fn-fc-auth-user-prefix* ((true-listp (fn-fc-user st))))))
(local
 (must-fail
  (fct-render-thm fct-user-command-without-true-listp fn-fc-auth-user-command
    fn-fc-user *fn-fc-auth-user-prefix* ((fn-fap-tokenp (fn-fc-user st))))))
(local
 (must-fail
  (fct-render-thm fct-pass-command-without-tokenp fn-fc-auth-pass-command
    fn-fc-pass *fn-fc-auth-pass-prefix* ((true-listp (fn-fc-pass st))))))
(local
 (must-fail
  (fct-render-thm fct-pass-command-without-true-listp fn-fc-auth-pass-command
    fn-fc-pass *fn-fc-auth-pass-prefix* ((fn-fap-tokenp (fn-fc-pass st))))))

; -----------------------------------------------------------------------------
; Keystone 6: fn-fc-decoded-profile-renders-verbatim-in-every-state.  No
; hypothesis.  The witness is the full trace's state; the refused-profile
; case is a profile whose secret line carries a CR, which `fn-fap-decode'
; refuses and which therefore installs no credential.  The false neighbour:
; the same claim over a name and secret that did not come through
; `fn-fap-decode' -- the smuggling credential above refutes it.
(assert-event
 (equal (fn-fc-auth-pass-command (fn-fc-drive-state *fct-starttls* *fct-full-trace*))
        (append *fn-fc-auth-pass-prefix* *fct-pass* '(13 10))))
(defconst *fct-bad-profile*
  '(70 78 65 85 84 72 49 10 110 111 100 101 10 115 13 10))
(assert-event (equal (fn-fap-decode *fct-bad-profile*) '(:bad nil nil)))
(defmacro fct-custody-thm (name user pass)
  `(defthm ,name
     (let ((st (fn-fc-drive-state
                (fn-fc-initial-auth-state streamingp conn security
                                          ,user ,pass allow-clear)
                events)))
       (and (equal (fn-fc-auth-user-command st)
                   (append *fn-fc-auth-user-prefix* ,user '(13 10)))
            (equal (fn-fc-auth-pass-command st)
                   (append *fn-fc-auth-pass-prefix* ,pass '(13 10)))))
     :hints (("Goal" :do-not-induct t
              :cases ((equal (car (fn-fap-decode profile)) :ok))
              :use ((:instance fn-fap-decode-yields-two-renderable-tokens
                               (octets profile)))
              :in-theory (e/d (fn-fc-initial-auth-state fn-fc-user fn-fc-pass)
                              (fn-fap-tokenp
                               fn-fap-decode-yields-two-renderable-tokens
                               fn-fc-drive-state fn-fc-auth-user-command
                               fn-fc-auth-pass-command))))))
(fct-custody-thm fct-decoded-credential-full
  (cadr (fn-fap-decode profile)) (caddr (fn-fap-decode profile)))
(local
 (must-fail
  (fct-custody-thm fct-undecoded-credential-renders-verbatim user pass)))
