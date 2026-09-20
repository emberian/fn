; Witnesses and teeth for the bundle expiry decision.
;
; Every keystone in `books/clock-invariants.lisp` gets a reachable
; non-degenerate witness here and one concrete violating value per hypothesis
; showing that the conclusion does not survive dropping it.

(in-package "ACL2")

(include-book "../../books/clock-invariants")

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
; Teeth: one concrete violating value per hypothesis of each keystone
; (docs/proof-style.md, section 5).  Each assert-event checks that the other
; hypotheses hold on the value and that the conclusion fails.
(defconst *clock-teeth-wall-only*
  ; earliest = latest = 1599999000000: live at that creation time, admissible
  ; only at exactly that instant.
  (fn-clock-observation 1000 1599999000000 0 t))
(defconst *clock-teeth-anchor* (cons 200000 1000))

; fn-clock-expired-requires-every-admissible-clock-to-agree
; without (fn-clock-admissible-truep obs now): now before the bound.
(assert-event
 (and (not (fn-clock-admissible-truep *clock-obs* 1599999000000))
      (equal (fn-clock-expiry-decision 1599999000000 100000 nil *clock-obs*) :expired)
      (not (< 100000 (- 1599999000000 1599999000000)))))
; without (null bundle-age): expired by age while the wall clock says created now.
(assert-event
 (and (consp *clock-teeth-anchor*)
      (fn-clock-admissible-truep *clock-obs* 1600000000000)
      (equal (fn-clock-expiry-decision 1600000000000 100000 *clock-teeth-anchor* *clock-obs*)
             :expired)
      (not (< 100000 (- 1600000000000 1600000000000)))))
; without the :expired decision: a live bundle.
(assert-event
 (and (fn-clock-admissible-truep *clock-obs* 1600000000000)
      (equal (fn-clock-expiry-decision 1600000000000 100000 nil *clock-obs*) :live)
      (not (< 100000 (- 1600000000000 1600000000000)))))

; fn-clock-expired-and-live-cannot-both-be-sound
; without (fn-clock-admissible-truep b now).
(assert-event
 (and (fn-clock-observationp *clock-obs*) (fn-clock-observationp *clock-teeth-wall-only*)
      (fn-clock-admissible-truep *clock-obs* 1600000000000)
      (not (fn-clock-admissible-truep *clock-teeth-wall-only* 1600000000000))
      (equal (fn-clock-expiry-decision 1599999000000 100000 nil *clock-obs*) :expired)
      (equal (fn-clock-expiry-decision 1599999000000 100000 nil *clock-teeth-wall-only*) :live)))
; without (fn-clock-admissible-truep a now).
(assert-event
 (and (not (fn-clock-admissible-truep *clock-obs* 1599999000000))
      (fn-clock-admissible-truep *clock-teeth-wall-only* 1599999000000)
      (equal (fn-clock-expiry-decision 1599999000000 100000 nil *clock-obs*) :expired)
      (equal (fn-clock-expiry-decision 1599999000000 100000 nil *clock-teeth-wall-only*) :live)))

; fn-clock-expiry-is-monotone-in-local-time
; without (fn-clock-later-observationp a b): a blind later reading.
(assert-event
 (and (fn-clock-observationp *clock-obs*) (fn-clock-observationp *clock-obs-blind*)
      (not (fn-clock-later-observationp *clock-obs* *clock-obs-blind*))
      (equal (fn-clock-expiry-decision 1599999000000 100000 nil *clock-obs*) :expired)
      (not (equal (fn-clock-expiry-decision 1599999000000 100000 nil *clock-obs-blind*)
                  :expired))))
; without (fn-clock-observationp b): OPEN.  No violating value was found:
; fn-clock-later-observationp compares the readings b exposes and the decision
; reads b only through them, so a malformed b that is later than an expired a
; is expired too.  The hypothesis looks unnecessary; dropping it from the
; theorem is recorded open (bp deputy, 2026-09-19) until the proof is redone
; without it.

; fn-clock-expired-by-age-requires-true-age-over-lifetime
; without (<= (fn-clock-age-estimate bundle-age obs) true-age): true age 0.
(assert-event
 (and (fn-clock-observationp *clock-obs*) (fn-clock-age-anchorp *clock-teeth-anchor*)
      (not (<= (fn-clock-age-estimate *clock-teeth-anchor* *clock-obs*) 0))
      (equal (fn-clock-expiry-decision 0 100000 *clock-teeth-anchor* *clock-obs*) :expired)
      (not (< 100000 0))))
