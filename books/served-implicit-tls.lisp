; fn: the implicit-TLS listener runs the STARTTLS session machine (PRF-162).
;
; `[listener] tls_port' (books/native-config.lisp) opens a second listener
; whose connections begin TLS at connect, the separate-port practice RFC
; 4642 section 1 describes (port 563) and discourages in favour of STARTTLS.
; fn offers it as a local policy because deployed readers speak only that
; form: tin 2.6.2 parses the STARTTLS capability and never sends the
; command (planning/evidence/sanding-2026-09-26.md).
;
; There is no second session machine.  The host (host/native/owner.lisp
; fnn-owner-serve-client, implicit mode) completes SSL_accept first, then
; opens the connection with the same fn-owner-open every reader gets
; (books/owner.lisp fn-own-open -> fn-served-open-group-indexed) and at once
; delivers the (:tls-established) wire event through fn-owner-tls-established
; (books/owner.lisp fn-own-read-step -> fn-served-dispatch), the event the
; STARTTLS path delivers after its handshake.  The keystone below says the
; connection that results is EQUAL to the one a STARTTLS client reaches
; after 382 and its handshake, so every later octet is answered by one
; fn-served-step over one state: the capability list without STARTTLS, a
; second STARTTLS refused 502 (books/nntp-auth.lisp
; fn-auth-second-starttls-is-refused), AUTHINFO allowed where
; `protected_only' requires a protected channel.
;
; Nothing here is about the handshake, the certificate or confidentiality:
; TLS stays a host facility (books/nntp-auth.lisp, "WHAT IS AND IS NOT
; PROVED HERE").

(in-package "ACL2")
(include-book "served")

(defconst *fn-sit-starttls-event*
  (list :command (fn-nntp-string-octets "STARTTLS")))

(defconst *fn-sit-established-event* (list :tls-established))

; The connection a reader listener opens: fn-own-open's call, whatever the
; pinned view.
(defun fn-sit-opened (archive index buckets verdicts line-limit body-limit
                              config observation injection acfg)
  (declare (xargs :guard t))
  (fn-served-result-conn
   (fn-served-open-group-indexed archive index buckets verdicts line-limit
                                 body-limit config observation injection acfg)))

(in-theory (disable fn-sit-opened))

; Whether a session is well formed does not depend on the two TLS bits,
; as long as each is a boolean.
(local
 (defthm fn-sit-sessionp-of-tls-bits
   (implies (and (syntaxp (not (and (equal tlsp ''nil)
                                    (equal handshaking ''nil))))
                 (booleanp tlsp) (booleanp handshaking))
            (equal (fn-auth-sessionp
                    (fn-auth-make-session base config pending subject tlsp
                                          handshaking))
                   (fn-auth-sessionp
                    (fn-auth-make-session base config pending subject nil
                                          nil))))
   :hints (("Goal" :in-theory (enable fn-auth-sessionp)))))

; A reader's fresh session is well formed, in the shape the open leaves it.
(local
 (defthm fn-sit-fresh-session-is-a-session
   (implies (fn-auth-configp acfg)
            (fn-auth-sessionp
             (fn-auth-make-session
              (fn-peer-make-session (fn-post-open-session archive) nil nil 0 nil nil)
              acfg nil nil nil nil)))
   :hints (("Goal" :use ((:instance fn-auth-open-session-is-consistent
                                    (peer nil) (node nil) (cfg nil) (tlsp nil)))
            :in-theory (e/d (fn-auth-open-session fn-peer-open-session
                             fn-auth-session-consistentp)
                            (fn-auth-open-session-is-consistent))))))

(local
 (defthm fn-sit-fresh-open-session-is-a-session
   (fn-auth-sessionp
    (fn-auth-make-session
     (fn-peer-make-session (fn-post-open-session archive) nil nil 0 nil nil)
     (fn-auth-open-config) nil nil nil nil))
   :hints (("Goal" :use ((:instance fn-sit-fresh-session-is-a-session
                                    (acfg (fn-auth-open-config))))
            :in-theory (disable fn-sit-fresh-session-is-a-session
                                (:e fn-auth-open-config))))))

; KEYSTONE.  The implicit-TLS connection after its (:tls-established) event
; is the STARTTLS connection after 382 and its handshake, and STARTTLS on the
; opened connection does owe that handshake (the (:starttls) effect the host
; performs SSL_accept on).  The equality alone would hold without either
; hypothesis, because the event sets the layer whatever preceded it; what the
; hypotheses buy is that the STARTTLS path reaches the event at all (580
; otherwise, and the host delivers no event after a 580).  The subject is
; fn-served-dispatch, which books/owner.lisp fn-own-read-step calls for the
; host's fn-owner-tls-established (host/owner-host.lisp), on the connection
; fn-served-open-group-indexed made, which fn-own-open calls for the host's
; fn-owner-open.  Both hypotheses are the operator's: a well-formed policy
; whose TLS is available (a certificate and key are loaded).
(defthm fn-served-implicit-tls-is-the-starttls-session
  (implies (and (fn-auth-configp acfg)
                (fn-auth-config-tls-availablep acfg))
           (let ((c0 (fn-sit-opened archive index buckets verdicts line-limit
                                    body-limit config observation injection
                                    acfg)))
             (and (member-equal
                   (fn-auth-starttls-effect)
                   (fn-served-result-effects
                    (fn-served-dispatch c0 *fn-sit-starttls-event*)))
                  (equal (fn-served-result-conn
                          (fn-served-dispatch c0 *fn-sit-established-event*))
                         (fn-served-result-conn
                          (fn-served-dispatch
                           (fn-served-result-conn
                            (fn-served-dispatch c0 *fn-sit-starttls-event*))
                           *fn-sit-established-event*))))))
  :hints (("Goal" :in-theory (enable fn-sit-opened fn-served-dispatch
                                     fn-served-open-group-indexed
                                     fn-served-open-indexed
                                     fn-served-pin-group-index
                                     fn-auth-step-pinned fn-auth-command
                                     fn-auth-starttls fn-auth-tls-established
                                     fn-auth-open-session
                                     fn-auth-clear-principal-peer
                                     fn-auth-gatedp fn-auth-principal-rolep
                                     fn-peer-open-session fn-post-offeredp
                                     fn-auth-single fn-nntp-single fn-auth-starttls-effect))))

; The implicit-TLS connection is protected from its first command: the event
; emits nothing (the greeting fn-served-open-group-indexed made is the only
; reply before the client speaks), records the TLS layer, and leaves no
; handshake owed.  A STARTTLS on it is then answered 502 by
; fn-auth-second-starttls-is-refused (books/nntp-auth.lisp).
(defthm fn-served-implicit-tls-session-is-protected
  (let ((r (fn-served-dispatch
            (fn-sit-opened archive index buckets verdicts line-limit body-limit
                           config observation injection acfg)
            *fn-sit-established-event*)))
    (and (null (fn-served-result-effects r))
         (fn-auth-session-tlsp (fn-served-conn-session (fn-served-result-conn r)))
         (not (fn-auth-session-handshakingp
               (fn-served-conn-session (fn-served-result-conn r))))))
  :hints (("Goal" :in-theory (enable fn-sit-opened fn-served-dispatch
                                     fn-served-open-group-indexed
                                     fn-served-open-indexed
                                     fn-served-pin-group-index
                                     fn-auth-step-pinned
                                     fn-auth-tls-established
                                     fn-auth-open-session
                                     fn-peer-open-session fn-post-offeredp))))
