; fn: the push feed's restart is a new clock domain (lane time-bars,
; 2026-09-28; PRF-385, HST-031; planning/design-time-model-2026-09-27.md
; section 4b).
;
; The feed's back-off deadline (`fn-feed-backoff-until') is a reading of the
; monotonic clock: fn-feed-back-off and fn-feed-lost set it to the
; observation's monotonic milliseconds plus the delay, and the replay of the
; feed journal rebuilds it from the :feed-retry and :feed-lost records'
; readings.  Those readings are the previous process's: SBCL's
; get-internal-real-time starts near zero in every process.  fn-feed-restart
; used to keep the deadline, and fn-feed-with-backoff never lowers it, so a
; peer that was backing off when the node stopped was not offered anything
; after the restart until the new process's clock reached the old one's
; deadline -- about the previous run's uptime.  fn-feed-restart
; (books/peer-feed.lisp) now forgets it; the entries' attempt counts (the
; semantic observation) are kept and set the next back-off.
(in-package "ACL2")
(include-book "peer-feed-invariants")

;; KEYSTONE (PRF-385).  A restart forgets the previous clock domain.  The
;; restarted feed does not depend on the back-off deadline the previous run
;; left (any natural gives the same feed), it has none, and so the back-off
;; admits the first observation of the new process whatever its reading.
;; The subject is fn-feed-restart, which the host reaches at every open:
;; host/owner-host.lisp fn-owner-feed-restart through
;; books/owner-feed-port.lisp fn-own-feed-port-restart-fold (the :restart
;; event of fn-feed-live-next, books/feed-events.lisp), and the model's
;; reopen, books/owner.lisp fn-own-reopen (fn-own-feed-restart-all).
(defthm fn-feed-restart-forgets-the-previous-clock-domain
  (implies (and (fn-feedp f) (natp b))
           (and (equal (fn-feed-restart
                        (fn-feed-make (fn-feed-peer f) (fn-feed-limits-of f) (fn-feed-queue f)
                                      (fn-feed-contact f) b (fn-feed-conn f)
                                      (fn-feed-next-attempt f)))
                       (fn-feed-restart f))
                (equal (fn-feed-backoff-until (fn-feed-restart f)) 0)
                (<= (nfix (fn-feed-backoff-until (fn-feed-restart f)))
                    (nfix (fn-clock-monotonic obs)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-feed-restart fn-feedp fn-feed-shapep))))
