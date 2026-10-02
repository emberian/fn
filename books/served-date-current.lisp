; DATE's clock independence at the host-called served step.
; host/reader-host.lisp fn-reader-chunk calls fn-served-step directly.
; The native owner's fn-owner-chunk-span-at calls fn-mca-read-span; its
; catalog and restricted post arms both use fn-post-command-env. Native
; owner composition is separately qualified by the liaison.
(in-package "ACL2")
(include-book "served")

; A reachable idle reader on an empty archive.  The clock readings are
; arbitrary, including missing/malformed/no-wall observations.  No validity
; hypothesis may hide the required refusal after a current clock is lost.
(defun fn-date-test-conn (pinned current)
  (declare (xargs :guard t))
  (fn-served-result-conn
   (fn-served-open
    (fn-initial-state nil) 510 8192
    (fn-inj-make-config t '(102 110) nil 32768)
    pinned current (fn-auth-open-config))))

(defthm fn-served-step-date-uses-current-reading
  (equal
   (fn-served-result-effects
    (fn-served-step (fn-date-test-conn pinned current)
                    '(68 65 84 69 13 10) fn-arena))
   (fn-nntp-result-effects
    (fn-nntp-date-response nil (fn-nntp-env current nil t))))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-date-test-conn fn-served-open fn-served-open-indexed
              fn-served-make-result fn-served-result-conn fn-served-result-effects
              fn-served-make-conn-indexed fn-served-make-conn-group-indexed
              fn-served-make-conn-live fn-served-conn-wire
              fn-served-conn-session fn-served-conn-archive fn-served-conn-config
              fn-served-conn-observation fn-served-conn-injection
              fn-served-conn-verdicts fn-served-conn-index
              fn-served-conn-group-index fn-served-conn-control
              fn-served-conn-pinned fn-served-conn-live fn-served-conn-pinned-index
              fn-served-conn-with-wire fn-served-step fn-served-feed
              fn-served-feed-loop fn-served-feed-byte
              fn-served-dispatch-events fn-served-dispatch-events-loop
              fn-served-dispatch fn-served-dispatch-core
              fn-served-closed-wirep fn-served-haltedp fn-served-quitp
              fn-served-tls-handshakingp fn-served-advance-eventp
              fn-auth-step-pinned fn-auth-delegate-pinned
              fn-peer-step-pinned fn-peer-delegate-pinned
              fn-nntp-post-step-pinned fn-nntp-step-pinned
              fn-nntp-command-pinned fn-nntp-session-command
              fn-inj-nth fn-inj-car fn-inj-cdr
              fn-peer-with-base fn-peer-make-session
              fn-auth-with-base fn-auth-make-session
              fn-nntp-reply-effect
              fn-post-command-env fn-post-reader-env
              fn-nntp-date-response fn-nntp-env fn-nntp-env-full
              fn-nntp-env-observation fn-nntp-result-effects
              fn-nntp-make-result fn-nntp-single
              fn-initial-state fn-inj-make-config fn-auth-open-config
              fn-auth-open-session fn-wire-initial-state fn-midx-build
              fn-post-make-result fn-post-result-effects fn-post-result-session
              fn-post-result-submission fn-post-sessionp fn-post-session-awaiting
              fn-post-session-base fn-post-make-session fn-post-offeredp
              fn-nntp-result-session fn-nntp-sessionp fn-nntp-session-openp
              fn-wire-statep fn-wire-feed-byte fn-wire-result-state
              fn-wire-result-events fn-wire-state-mode
              fn-ag-car fn-ag-cdr append car-cons cdr-cons)
            (union-theories (executable-counterpart-theory :here)
                            (theory 'minimal-theory)))))
  :rule-classes nil)

(defthm fn-served-step-date-ignores-pinned-reading
  (equal
   (fn-served-result-effects
    (fn-served-step (fn-date-test-conn pinned current)
                    '(68 65 84 69 13 10) fn-arena))
   (fn-served-result-effects
    (fn-served-step (fn-date-test-conn other current)
                    '(68 65 84 69 13 10) fn-arena)))
  :hints (("Goal"
           :use (fn-served-step-date-uses-current-reading
                 (:instance fn-served-step-date-uses-current-reading (pinned other)))
           :in-theory nil))
  :rule-classes nil)

; Canonicalize only the framed-command boundary and its pinned observation;
; the session, archive, permission/configuration, current clock and indexes
; are arbitrary. This includes restricted, gated, closed and posting states.
(defun fn-date-command-conn (conn pinned)
  (declare (xargs :guard t))
  (fn-served-make-conn-live
   (fn-wire-initial-state 510 8192)
   (fn-served-conn-session conn) (fn-served-conn-archive conn)
   (fn-served-conn-config conn) pinned (fn-served-conn-injection conn)
   (fn-served-conn-verdicts conn) (fn-served-conn-index conn)
   (fn-served-conn-group-index conn) (fn-served-conn-control conn)
   (fn-served-conn-pinned conn) (fn-served-conn-live conn)))

(local
 (defthm fn-date-post-canonical-pinned
   (implies (syntaxp (not (equal pinned ''nil)))
    (equal
    (fn-nntp-post-step-pinned ps archive index verdicts config pinned current
                              '(:command (68 65 84 69)) fn-arena)
    (fn-nntp-post-step-pinned ps archive index verdicts config nil current
                              '(:command (68 65 84 69)) fn-arena)))
   :hints (("Goal" :use (:instance fn-post-date-result-independent-of-pinned-observation
                                  (other nil))
            :in-theory nil))))

(local
 (defthm fn-date-post-direct-canonical-pinned
   (implies (syntaxp (not (equal pinned ''nil)))
    (equal
     (fn-nntp-post-step ps archive config pinned current
                        '(:command (68 65 84 69)) fn-arena)
     (fn-nntp-post-step ps archive config nil current
                        '(:command (68 65 84 69)) fn-arena)))
   :hints (("Goal" :in-theory
            (e/d (fn-nntp-post-step fn-post-command-env)
                 (fn-nntp-step fn-post-reader-env fn-post-sessionp
                  fn-post-session-awaiting fn-post-offeredp))))))

(local
 (defthm fn-date-auth-canonical-pinned
   (implies (syntaxp (not (equal pinned ''nil)))
    (equal
     (fn-auth-step-pinned as archive index verdicts config pinned current
                          '(:command (68 65 84 69)) fn-arena)
     (fn-auth-step-pinned as archive index verdicts config nil current
                          '(:command (68 65 84 69)) fn-arena)))
   :hints (("Goal" :in-theory
            (union-theories
             '(fn-auth-step-pinned fn-auth-delegate-pinned
               fn-peer-step-pinned fn-peer-delegate-pinned
               fn-peer-step fn-peer-delegate
               fn-date-post-direct-canonical-pinned fn-date-post-canonical-pinned
               car-cons cdr-cons)
             (union-theories (executable-counterpart-theory :here)
                             (theory 'minimal-theory)))))))

(defthm fn-served-step-date-any-session-ignores-pinned-reading
  (equal
   (fn-served-result-effects
    (fn-served-step (fn-date-command-conn conn pinned)
                    '(68 65 84 69 13 10) fn-arena))
   (fn-served-result-effects
    (fn-served-step (fn-date-command-conn conn other)
                    '(68 65 84 69 13 10) fn-arena)))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-date-command-conn fn-date-auth-canonical-pinned fn-served-open fn-served-open-indexed
              fn-served-make-result fn-served-result-conn fn-served-result-effects
              fn-served-make-conn-indexed fn-served-make-conn-group-indexed
              fn-served-make-conn-live fn-served-conn-wire
              fn-served-conn-session fn-served-conn-archive fn-served-conn-config
              fn-served-conn-observation fn-served-conn-injection
              fn-served-conn-verdicts fn-served-conn-index
              fn-served-conn-group-index fn-served-conn-control
              fn-served-conn-pinned fn-served-conn-live fn-served-conn-pinned-index
              fn-served-conn-with-wire fn-served-step fn-served-feed
              fn-served-feed-loop fn-served-feed-byte
              fn-served-dispatch-events fn-served-dispatch-events-loop
              fn-served-dispatch fn-served-dispatch-core
              fn-served-closed-wirep fn-served-haltedp fn-served-quitp
              fn-served-tls-handshakingp fn-served-advance-eventp




              fn-inj-nth fn-inj-car fn-inj-cdr
              fn-peer-with-base fn-peer-make-session
              fn-auth-with-base fn-auth-make-session
              fn-nntp-reply-effect
              fn-post-command-env fn-post-reader-env
              fn-nntp-env fn-nntp-env-full
              fn-nntp-env-observation fn-nntp-result-effects
              fn-nntp-make-result fn-nntp-single
              fn-initial-state fn-inj-make-config fn-auth-open-config
              fn-auth-open-session fn-wire-initial-state fn-midx-build
              fn-post-make-result fn-post-result-effects fn-post-result-session
              fn-post-result-submission fn-post-sessionp fn-post-session-awaiting
              fn-post-session-base fn-post-make-session fn-post-offeredp
              fn-nntp-result-session fn-nntp-sessionp fn-nntp-session-openp
              fn-wire-statep fn-wire-feed-byte fn-wire-result-state
              fn-wire-result-events fn-wire-state-mode
              fn-ag-car fn-ag-cdr append car-cons cdr-cons)
            (union-theories (executable-counterpart-theory :here)
                            (theory 'minimal-theory)))))
  :rule-classes nil)
