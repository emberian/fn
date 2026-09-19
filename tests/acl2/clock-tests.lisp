; Witnesses and teeth for the bundle expiry decision.
;
; Every keystone in `books/clock-invariants.lisp` gets a reachable
; non-degenerate witness here and one `must-fail` case per hypothesis showing
; that the conclusion does not survive dropping it.

(in-package "ACL2")

(include-book "../../books/clock-invariants")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; A host observation with a real wall reading and a five-second error bound.
; DTN time 1600000000000 ms is 2050-09-13T12:26:40Z.

(defconst *clock-obs* (fn-clock-observation 1000 1600000000000 5000 t))
(defconst *clock-obs-later* (fn-clock-observation 9000 1600000008000 5000 t))
(defconst *clock-obs-blind* (fn-clock-observation 1000 0 0 nil))

(assert-event (fn-clock-observationp *clock-obs*))
(assert-event (fn-clock-observationp *clock-obs-later*))
(assert-event (fn-clock-observationp *clock-obs-blind*))
(assert-event (fn-clock-later-observationp *clock-obs* *clock-obs-later*))

(assert-event (equal (fn-clock-earliest-true *clock-obs*) 1599999995000))
(assert-event (equal (fn-clock-latest-true *clock-obs*) 1600000005000))

; -----------------------------------------------------------------------------
; The three outcomes are all reachable on the wall path, and the boundary
; between them is the error bound, not the wall reading.

; Created 995 seconds ago even on the most favourable admissible clock.
(assert-event
 (equal (fn-clock-expiry-decision 1599999000000 100000 nil *clock-obs*)
        :expired))

; Created now: live on every admissible clock, because the whole five-second
; error bound still fits inside the lifetime.
(assert-event
 (equal (fn-clock-expiry-decision 1600000000000 100000 nil *clock-obs*)
        :live))

; The same bundle with a two-second lifetime: the admissible interval straddles
; expiry, so the answer is `:uncertain` and nothing may be dropped.
(assert-event
 (equal (fn-clock-expiry-decision 1600000000000 2000 nil *clock-obs*)
        :uncertain))
(assert-event
 (not (fn-clock-may-drop-local-copyp
       (fn-clock-expiry-decision 1600000000000 2000 nil *clock-obs*))))

; No wall reading at all, and a zero creation timestamp, are both `:uncertain`.
(assert-event
 (equal (fn-clock-expiry-decision 1599999000000 100000 nil *clock-obs-blind*)
        :uncertain))
(assert-event
 (equal (fn-clock-expiry-decision 0 100000 nil *clock-obs*)
        :uncertain))

; -----------------------------------------------------------------------------
; The Bundle Age path decides without any wall clock at all (RFC 9171
; section 5.5).  The anchor says the age was 50000 ms when the monotonic
; counter read 900; it now reads 1000, so the estimate is 50100 ms.

(defconst *clock-anchor* (cons 50000 900))

(assert-event (fn-clock-age-anchorp *clock-anchor*))
(assert-event (equal (fn-clock-age-estimate *clock-anchor* *clock-obs*) 50100))
(assert-event
 (equal (fn-clock-expiry-decision 0 50000 *clock-anchor* *clock-obs-blind*)
        :expired))
(assert-event
 (equal (fn-clock-expiry-decision 0 60000 *clock-anchor* *clock-obs-blind*)
        :live))

; -----------------------------------------------------------------------------
; Monotone in local time: expired stays expired.

(assert-event
 (equal (fn-clock-expiry-decision 1599999000000 100000 nil *clock-obs-later*)
        :expired))

; A bundle that is `:uncertain` now becomes `:expired` under a later
; observation of the same clock; the reverse never happens.
(assert-event
 (equal (fn-clock-expiry-decision 1599999994000 4000 nil *clock-obs*)
        :uncertain))
(assert-event
 (equal (fn-clock-expiry-decision 1599999994000 4000 nil *clock-obs-later*)
        :expired))

; -----------------------------------------------------------------------------
; Two nodes that disagree about wall time.  Node B's clock is 200 seconds
; ahead of node A's, and their admissible intervals are disjoint, so at most
; one of them is honest.  They reach opposite confident verdicts on the same
; bundle -- and that is not unsoundness, because no theorem in this lane says
; two nodes must agree.  `fn-clock-expired-and-live-cannot-both-be-sound` says
; only that they cannot both be honest while doing so.

(defconst *clock-obs-b* (fn-clock-observation 1000 1600000200000 1000 t))

(assert-event (fn-clock-observationp *clock-obs-b*))
(assert-event
 (equal (fn-clock-expiry-decision 1599999900000 150000 nil *clock-obs*)
        :live))
(assert-event
 (equal (fn-clock-expiry-decision 1599999900000 150000 nil *clock-obs-b*)
        :expired))

; The two admissible intervals really are disjoint, so no single true time is
; admissible for both; the keystone's hypotheses are not jointly satisfiable
; here, which is exactly why the disagreement is permitted.
(assert-event
 (< (fn-clock-latest-true *clock-obs*) (fn-clock-earliest-true *clock-obs-b*)))

; And when the intervals do overlap, the keystone's hypotheses are inhabited:
; both nodes admit 1600000000500 as the true time, and they agree.
(defconst *clock-obs-c* (fn-clock-observation 1000 1600000001000 2000 t))
(assert-event (fn-clock-admissible-truep *clock-obs* 1600000000500))
(assert-event (fn-clock-admissible-truep *clock-obs-c* 1600000000500))
(assert-event
 (equal (fn-clock-expiry-decision 1599999000000 100000 nil *clock-obs-c*)
        :expired))

; -----------------------------------------------------------------------------
; Teeth.
;
; One `must-fail` per hypothesis of each keystone.  Each shows that ACL2
; cannot prove the conclusion once that hypothesis is removed.

; fn-clock-expired-requires-every-admissible-clock-to-agree
;   without `fn-clock-admissible-truep`: an arbitrary `now` says nothing.
(local
 (must-fail
  (thm (implies (and (fn-clock-observationp obs)
                     (fn-clock-timep creation-time)
                     (fn-clock-timep lifetime)
                     (null bundle-age)
                     (equal (fn-clock-expiry-decision creation-time lifetime
                                                      bundle-age obs)
                            :expired))
                (< lifetime (- now creation-time))))))

;   without `(null bundle-age)`: the age path can answer `:expired` while the
;   wall clock still admits liveness, and it is right to.
(local
 (must-fail
  (thm (implies (and (fn-clock-observationp obs)
                     (fn-clock-timep creation-time)
                     (fn-clock-timep lifetime)
                     (fn-clock-admissible-truep obs now)
                     (equal (fn-clock-expiry-decision creation-time lifetime
                                                      bundle-age obs)
                            :expired))
                (< lifetime (- now creation-time))))))

;   without `fn-clock-observationp`: a malformed observation has no meaning.
(local
 (must-fail
  (thm (implies (and (fn-clock-timep creation-time)
                     (fn-clock-timep lifetime)
                     (null bundle-age)
                     (fn-clock-admissible-truep obs now)
                     (equal (fn-clock-expiry-decision creation-time lifetime
                                                      bundle-age obs)
                            :expired))
                (< lifetime (- now creation-time))))))

;   without the `:expired` hypothesis: a live or uncertain verdict says
;   nothing about the true age.
(local
 (must-fail
  (thm (implies (and (fn-clock-observationp obs)
                     (fn-clock-timep creation-time)
                     (fn-clock-timep lifetime)
                     (null bundle-age)
                     (fn-clock-admissible-truep obs now))
                (< lifetime (- now creation-time))))))

; fn-clock-expiry-is-monotone-in-local-time
;   without `fn-clock-later-observationp`: an unrelated observation may put the
;   earliest admissible true time back before expiry.
(local
 (must-fail
  (thm (implies (and (fn-clock-observationp a)
                     (fn-clock-observationp b)
                     (fn-clock-age-anchorp bundle-age)
                     (fn-clock-timep creation-time)
                     (fn-clock-timep lifetime)
                     (equal (fn-clock-expiry-decision creation-time lifetime
                                                      bundle-age a)
                            :expired))
                (equal (fn-clock-expiry-decision creation-time lifetime
                                                 bundle-age b)
                       :expired)))))

;   without `fn-clock-observationp` on the later observation.
(local
 (must-fail
  (thm (implies (and (fn-clock-observationp a)
                     (fn-clock-age-anchorp bundle-age)
                     (fn-clock-timep creation-time)
                     (fn-clock-timep lifetime)
                     (fn-clock-later-observationp a b)
                     (equal (fn-clock-expiry-decision creation-time lifetime
                                                      bundle-age a)
                            :expired))
                (equal (fn-clock-expiry-decision creation-time lifetime
                                                 bundle-age b)
                       :expired)))))

; fn-clock-expired-and-live-cannot-both-be-sound
;   without node B's admissibility: B may simply be wrong.
(local
 (must-fail
  (thm (implies (and (fn-clock-observationp a)
                     (fn-clock-observationp b)
                     (fn-clock-timep creation-time)
                     (fn-clock-timep lifetime)
                     (fn-clock-admissible-truep a now)
                     (equal (fn-clock-expiry-decision creation-time lifetime
                                                      nil a)
                            :expired))
                (not (equal (fn-clock-expiry-decision creation-time lifetime
                                                      nil b)
                            :live))))))

;   without node A's admissibility.
(local
 (must-fail
  (thm (implies (and (fn-clock-observationp a)
                     (fn-clock-observationp b)
                     (fn-clock-timep creation-time)
                     (fn-clock-timep lifetime)
                     (fn-clock-admissible-truep b now)
                     (equal (fn-clock-expiry-decision creation-time lifetime
                                                      nil a)
                            :expired))
                (not (equal (fn-clock-expiry-decision creation-time lifetime
                                                      nil b)
                            :live))))))

; fn-clock-expired-by-age-requires-true-age-over-lifetime
;   without the lower-bound hypothesis on the true age: the Bundle Age block
;   is only ever a lower bound because it sums known intervals, and nothing
;   in the model forces a caller to respect that.
(local
 (must-fail
  (thm (implies (and (fn-clock-observationp obs)
                     (fn-clock-age-anchorp bundle-age)
                     (consp bundle-age)
                     (fn-clock-timep lifetime)
                     (equal (fn-clock-expiry-decision creation-time lifetime
                                                      bundle-age obs)
                            :expired))
                (< lifetime true-age)))))
