; tcpcl-session-carried.lisp -- the TCPCLv4 session invariant declared
; (lane def-carried, 2026-10-01: the def-carried pilot on a carried
; invariant whose closure certifies today).
;
; `fn-tcl-sessionp' (books/tcpcl-session.lisp) is the session record's
; invariant: established by `fn-tcl-initial-session' and preserved by every
; session transition the host drives through the `fn-tcl-host-*' wrappers
; (host/native/tcpcl.lisp).  books/tcpcl-session.lisp proves one
; `fn-tcl-X-preserves-sessionp' per transition, each in the closed theory
; `fn-tcl-session-closed' (fn-deftransition).  Here the carrying argument is
; one `def-carried' form: for each transition the generator writes the
; statement -- the session (:state 0) satisfying the invariant, the
; transition's guard and the declared :hyps, to the invariant of the
; declared :result over the call (the call itself, or `(fn-tcl-result-session
; _)' of it) -- and proves it from the named theorem as a hint; the
; establishing point; and the trace theorem `fn-tcl-session-carried-run-carries'
; -- along every sequence of the transitions from a session satisfying the
; invariant, the invariant holds -- by functional instantiation of
; fn-cd-run-carries.  A value row is a model-level claim: it backs no raw
; dispatch.

; `fn-tcl-settle-preserves-sessionp' is not a session transition: it carries
; the invariant from `(fn-tcl-result-session r)' to `(fn-tcl-result-session
; (fn-tcl-settle r))', a result's session to the settled result's, so it
; assumes the invariant of a projection, not of a session, and the form
; refuses it as a transition.  It stands alone, as it was.
;
; The session is a value the host threads through its calls, not a stobj,
; so the world cannot say which declared entries produce one; the form says
; so (:complete-by): the list is the enumeration of books/tcpcl-session.lisp's
; preservation theorems, and the host reaches a session only through the
; fn-tcl-host-* wrappers over these transitions.
;
; Nothing changes for dependents: the book adds a row and theorems over
; functions tcpcl-session already defines; it redefines nothing, and no
; existing book includes it.

(in-package "ACL2")
(include-book "def-carried")
(include-book "tcpcl-session")

(def-carried fn-tcl-session-carried
  :invariant fn-tcl-sessionp
  :established ((fn-tcl-initial-session fn-tcl-initial-session-is-session
                 :hyps ((fn-tcl-rolep role) (fn-tcl-paramsp local) (fn-clock-timep now))))
  :transitions ((fn-tcl-touch-rx fn-tcl-touch-rx-preserves-sessionp :state 0
                 :hyps ((fn-clock-timep now)))
                (fn-tcl-next fn-tcl-next-preserves-sessionp :state 0
                 :hyps ((fn-tcl-phasep phase) (fn-tcl-termp term) (fn-clock-timep last-tx)
                        (or (not inbound)
                            (fn-tcl-inboundp inbound (fn-tcl-params-transfer-mru
                                                      (fn-tcl-session-local s))))
                        (or (not outbound) (fn-tcl-outboundp outbound))
                        (case-split
                         (implies (fn-tcl-pre-establishedp phase)
                                  (and (not (fn-tcl-session-negotiated s)) (not term))))
                        (case-split
                         (implies (equal phase :established)
                                  (and (fn-tcl-session-negotiated s) (not term))))
                        (case-split (implies (equal phase :ending) term))
                        (case-split
                         (implies (not (fn-tcl-transferringp phase))
                                  (and (not inbound) (not outbound))))
                        (case-split
                         (implies (not (fn-tcl-session-negotiated s))
                                  (and (not inbound) (not outbound))))))
                (fn-tcl-with-outbound fn-tcl-with-outbound-preserves-sessionp :state 0
                 :hyps ((equal (fn-tcl-session-phase s) :established) (fn-tcl-outboundp outbound)
                        (natp next-xfer-id)))
                (fn-tcl-open fn-tcl-open-preserves-sessionp :state 0 :result (fn-tcl-result-session _)
                 :hyps ((fn-clock-timep now)))
                (fn-tcl-recv-contact fn-tcl-recv-contact-preserves-sessionp :state 0 :result (fn-tcl-result-session _)
                 :hyps ((fn-clock-timep now) (fn-tcl-pre-establishedp (fn-tcl-session-phase s))))
                (fn-tcl-recv-init fn-tcl-recv-init-preserves-sessionp :state 0 :result (fn-tcl-result-session _)
                 :hyps ((fn-clock-timep now) (fn-tcl-peer-initp m)
                        (equal (fn-tcl-session-phase s) :messaging)))
                (fn-tcl-refuse fn-tcl-refuse-preserves-sessionp :state 0 :result (fn-tcl-result-session _)
                 :hyps ((fn-clock-timep now)))
                (fn-tcl-complete fn-tcl-complete-preserves-sessionp :state 0 :result (fn-tcl-result-session _)
                 :hyps ((fn-clock-timep now)))
                (fn-tcl-stage fn-tcl-stage-preserves-sessionp :state 0 :result (fn-tcl-result-session _)
                 :hyps ((fn-clock-timep now) (fn-tcl-transferringp (fn-tcl-session-phase s))
                        (fn-tcl-session-negotiated s)
                        (fn-tcl-inboundp inbound (fn-tcl-transfer-mru s))))
                (fn-tcl-broken-stream fn-tcl-broken-stream-preserves-sessionp :state 0 :result (fn-tcl-result-session _)
                 :hyps ((fn-clock-timep now) (fn-tcl-transferringp (fn-tcl-session-phase s))))
                (fn-tcl-recv-segment fn-tcl-recv-segment-preserves-sessionp :state 0 :result (fn-tcl-result-session _)
                 :hyps ((fn-clock-timep now) (fn-tcl-messagep m (fn-tcl-segment-mru s))
                        (equal (fn-tcl-msg-kind m) :xfer-segment)
                        (fn-tcl-transferringp (fn-tcl-session-phase s))
                        (fn-tcl-session-negotiated s)))
                (fn-tcl-unexpected fn-tcl-unexpected-preserves-sessionp :state 0 :result (fn-tcl-result-session _)
                 :hyps ((fn-clock-timep now)))
                (fn-tcl-recv-ack fn-tcl-recv-ack-preserves-sessionp :state 0 :result (fn-tcl-result-session _)
                 :hyps ((fn-clock-timep now) (fn-tcl-messagep m (fn-tcl-segment-mru s))
                        (equal (fn-tcl-msg-kind m) :xfer-ack)
                        (fn-tcl-transferringp (fn-tcl-session-phase s))
                        (fn-tcl-session-negotiated s)))
                (fn-tcl-recv-refuse fn-tcl-recv-refuse-preserves-sessionp :state 0 :result (fn-tcl-result-session _))
                (fn-tcl-recv-term fn-tcl-recv-term-preserves-sessionp :state 0 :result (fn-tcl-result-session _)
                 :hyps ((fn-clock-timep now) (not (equal (fn-tcl-session-phase s) :closed))))
                (fn-tcl-terminate fn-tcl-terminate-preserves-sessionp :state 0 :result (fn-tcl-result-session _)
                 :hyps ((fn-clock-timep now)))
                (fn-tcl-tcp-closed fn-tcl-tcp-closed-preserves-sessionp :state 0 :result (fn-tcl-result-session _))
                (fn-tcl-input-error fn-tcl-input-error-preserves-sessionp :state 0 :result (fn-tcl-result-session _)
                 :hyps ((fn-clock-timep now)))
                (fn-tcl-pump fn-tcl-pump-preserves-sessionp :state 0 :result (fn-tcl-result-session _)
                 :hyps ((fn-clock-timep now)))
                (fn-tcl-send fn-tcl-send-preserves-sessionp :state 0 :result (fn-tcl-result-session _)
                 :hyps ((fn-clock-timep now) (fn-cbor-octet-listp octets)))
                (fn-tcl-tick fn-tcl-tick-preserves-sessionp :state 0 :result (fn-tcl-result-session _)
                 :hyps ((fn-clock-observationp obs)))
                (fn-tcl-step fn-tcl-step-preserves-sessionp :state 0 :result (fn-tcl-result-session _)
                 :hyps ((fn-clock-timep now) (fn-tcl-messagep m (fn-tcl-segment-mru s))))
                (fn-tcl-drive fn-tcl-drive-preserves-sessionp :state 0 :result (fn-tcl-result-session _)))
  :complete-by (:enumeration "the session is a value the host threads; every fn-tcl-X-preserves-sessionp of books/tcpcl-session.lisp is listed, and host/native/tcpcl.lisp reaches a session only through the fn-tcl-host-* wrappers over these transitions"))

; The trace theorem exists and has the generated statement.
(assert-event
 (equal (getpropc 'fn-tcl-session-carried-run-carries 'theorem nil (w state))
        '(implies (if (fn-tcl-sessionp s) (fn-tcl-session-carried-run-okp s es) 'nil)
                  (fn-tcl-sessionp (fn-tcl-session-carried-run s es)))))

; The generated statement for one transition: the declared result over the
; call, the session invariant and the declared hypotheses (the guard is t).
(assert-event
 (equal (getpropc 'fn-tcl-session-carried-fn-tcl-open-carries 'theorem nil (w state))
        '(implies (if (fn-tcl-sessionp s) (fn-clock-timep now) 'nil)
                  (fn-tcl-sessionp (fn-tcl-result-session (fn-tcl-open s now))))))

; A value row is a model-level claim: it backs no raw dispatch.
(assert-event
 (equal (fn-cd-raw-with 'fn-tcl-session-carried 'fn-tcl-open (w state))
        '(fn-tcl-session-carried-fn-tcl-open-carries)))
(assert-event
 (fn-cd-raw-problem 'fn-tcl-session-carried 'fn-tcl-open (w state)))

; Reachable positive teeth for the literal generated step/run theorems.
; The active peer opens (RFC 9174 section 4.1), then records receipt time.
; Events retain formal positions: nil occupies the replaced session slot.
; The generated functions are defun-nx: evaluate their logical definitions
; by ground reduction, with the generated preservation rules disabled.
; Check the constructor's premises, both complete theorem antecedents,
; their conclusions, and observable progress through the concrete trace.
(local
 (thm
  (let* ((params (fn-tcl-make-params 30 3 64 '(100 116 110 58 47 47 97 47) nil nil))
         (s (fn-tcl-initial-session :active params 0))
         (e '(fn-tcl-open nil 1))
         (es '((fn-tcl-open nil 1) (fn-tcl-touch-rx nil 2)))
         (after-step (fn-tcl-session-carried-step s e))
         (after-run (fn-tcl-session-carried-run s es)))
    (and (fn-tcl-rolep :active) (fn-tcl-paramsp params) (fn-clock-timep 0)
         (fn-tcl-sessionp s)
         (fn-tcl-session-carried-okp s e)
         (fn-tcl-sessionp after-step)
         (equal (fn-tcl-session-phase after-step) :contact)
         (fn-tcl-session-carried-run-okp s es)
         (fn-tcl-sessionp after-run)
         (equal (fn-tcl-session-phase after-run) :contact)
         (equal (fn-tcl-session-last-rx after-run) 2)))
  :hints (("Goal" :in-theory
           (e/d (fn-tcl-session-carried-step fn-tcl-session-carried-okp
                 fn-tcl-session-carried-run fn-tcl-session-carried-run-okp)
                (fn-tcl-session-carried-step-carries
                 fn-tcl-session-carried-run-carries))))))

; Single-hypothesis removal, CORRUPTED INPUT STATE, not a reachable state:
; omit only (fn-tcl-sessionp s).  The role is invalid; the retained okp and
; run-okp hypotheses hold.  A real, nonempty touch-rx trace preserves the
; bad role, so both generated conclusions fail.
(local
 (thm
  (let* ((params (fn-tcl-make-params 30 3 64 '(100 116 110 58 47 47 97 47) nil nil))
         (s (fn-tcl-initial-session :invalid-role params 0))
         (e '(fn-tcl-touch-rx nil 2))
         (es '((fn-tcl-touch-rx nil 2))))
    (and (not (fn-tcl-sessionp s))
         (fn-tcl-session-carried-okp s e)
         (not (fn-tcl-sessionp (fn-tcl-session-carried-step s e)))
         (fn-tcl-session-carried-run-okp s es)
         (not (fn-tcl-sessionp (fn-tcl-session-carried-run s es)))))
  :hints (("Goal" :in-theory
           (e/d (fn-tcl-session-carried-step fn-tcl-session-carried-okp
                 fn-tcl-session-carried-run fn-tcl-session-carried-run-okp)
                (fn-tcl-session-carried-step-carries
                 fn-tcl-session-carried-run-carries))))))

; MUTATION witness: an incorrect dispatcher corrupts the role after the
; actual generated step/run.  This is a mutant output, not a counterexample
; to either theorem: the actual outputs still satisfy their conclusions.
(local
 (thm
  (let* ((params (fn-tcl-make-params 30 3 64 '(100 116 110 58 47 47 97 47) nil nil))
         (s (fn-tcl-initial-session :active params 0))
         (e '(fn-tcl-open nil 1))
         (es '((fn-tcl-open nil 1) (fn-tcl-touch-rx nil 2)))
         (after-step (fn-tcl-session-carried-step s e))
         (after-run (fn-tcl-session-carried-run s es))
         (mutant-step (update-nth 1 :invalid-role after-step))
         (mutant-run (update-nth 1 :invalid-role after-run)))
    (and (fn-tcl-sessionp s)
         (fn-tcl-session-carried-okp s e)
         (fn-tcl-sessionp after-step)
         (equal (fn-tcl-session-role mutant-step) :invalid-role)
         (not (fn-tcl-sessionp mutant-step))
         (fn-tcl-session-carried-run-okp s es)
         (fn-tcl-sessionp after-run)
         (equal (fn-tcl-session-role mutant-run) :invalid-role)
         (not (fn-tcl-sessionp mutant-run))))
  :hints (("Goal" :in-theory
           (e/d (fn-tcl-session-carried-step fn-tcl-session-carried-okp
                 fn-tcl-session-carried-run fn-tcl-session-carried-run-okp)
                (fn-tcl-session-carried-step-carries
                 fn-tcl-session-carried-run-carries))))))

(in-theory (disable fn-tcl-session-carried-step fn-tcl-session-carried-okp
                    fn-tcl-session-carried-run fn-tcl-session-carried-run-okp))
