; fn: certified properties of the bundle expiry decision.
;
; The safety half of FLR-004 is discharged here: an `:expired` verdict is
; sound against every clock reading the deciding node itself admits, two nodes
; whose declared error bounds are honest can never reach opposite confident
; verdicts, and a verdict once `:expired` stays `:expired` as local time
; advances.  No theorem in this book relates the wall clocks of two nodes.
;
; The liveness half is NOT discharged here and is not claimed: nothing bounds
; how long a node may answer `:uncertain`, because that depends on the host
; ever supplying a wall reading with a finite error bound.  See specs/time.md.

(in-package "ACL2")

(include-book "clock")

(local (include-book "arithmetic/top" :dir :system))

; `arithmetic/top`'s generalization rule for `mod` introduces fresh `mod`
; terms into case trees that never had one, and loops the waterfall on the
; bit-level recursions below.  Local, so nothing downstream inherits it.
(local (in-theory (disable mod-x-y-=-x+y-for-rationals)))

; -----------------------------------------------------------------------------
; Shape

(defthm fn-clock-decision-is-one-of-three
  (or (equal (fn-clock-expiry-decision creation-time lifetime bundle-age obs)
             :expired)
      (equal (fn-clock-expiry-decision creation-time lifetime bundle-age obs)
             :live)
      (equal (fn-clock-expiry-decision creation-time lifetime bundle-age obs)
             :uncertain))
  :rule-classes nil)

; A node with neither an accurate wall reading nor Bundle Age information can
; never decide.  This is why RFC 9171 section 4.4.2 requires a Bundle Age block
; whenever the creation time is zero.
(defthm fn-clock-no-wall-and-no-age-is-uncertain
  (implies (and (null bundle-age)
                (not (fn-clock-has-wall obs)))
           (equal (fn-clock-expiry-decision creation-time lifetime bundle-age obs)
                  :uncertain)))

(defthm fn-clock-zero-creation-time-without-age-is-uncertain
  (implies (and (null bundle-age)
                (equal creation-time 0))
           (equal (fn-clock-expiry-decision creation-time lifetime bundle-age obs)
                  :uncertain)))

; -----------------------------------------------------------------------------
; Keystone 1: an `:expired` verdict on the wall path is sound against every
; clock reading this node's own declared error bound admits.

(defthm fn-clock-expired-requires-every-admissible-clock-to-agree
  (implies (and (fn-clock-observationp obs)
                (fn-clock-timep creation-time)
                (fn-clock-timep lifetime)
                (null bundle-age)
                (fn-clock-admissible-truep obs now)
                (equal (fn-clock-expiry-decision creation-time lifetime
                                                 bundle-age obs)
                       :expired))
           (< lifetime (- now creation-time))))

; The contrapositive, in the form FLR-004 states it: the node never answers
; `:expired` while its own error bound still admits a live reading.
(defthm fn-clock-admissible-liveness-blocks-expired
  (implies (and (fn-clock-observationp obs)
                (fn-clock-timep creation-time)
                (fn-clock-timep lifetime)
                (null bundle-age)
                (fn-clock-admissible-truep obs now)
                (<= (- now creation-time) lifetime))
           (not (equal (fn-clock-expiry-decision creation-time lifetime
                                                 bundle-age obs)
                       :expired)))
  :hints (("Goal"
           :use fn-clock-expired-requires-every-admissible-clock-to-agree
           :in-theory (disable fn-clock-expiry-decision
                               fn-clock-admissible-truep))))

; -----------------------------------------------------------------------------
; Keystone 2: safety needs no agreement between nodes.
;
; Two nodes exchange no clock information.  Each declares its own error bound.
; If both declarations are honest -- that is, each node's interval really does
; contain the one true DTN time -- then one node answering `:expired` and the
; other answering `:live` is impossible.  Nothing in this statement relates
; the two nodes' wall readings or error bounds to each other.

(defthm fn-clock-expired-and-live-cannot-both-be-sound
  (implies (and (fn-clock-observationp a)
                (fn-clock-observationp b)
                (fn-clock-timep creation-time)
                (fn-clock-timep lifetime)
                (fn-clock-admissible-truep a now)
                (fn-clock-admissible-truep b now)
                (equal (fn-clock-expiry-decision creation-time lifetime nil a)
                       :expired))
           (not (equal (fn-clock-expiry-decision creation-time lifetime nil b)
                       :live))))

; -----------------------------------------------------------------------------
; Keystone 3: the age path is sound whenever the age estimate is a lower bound
; on the bundle's true age.  RFC 9171 section 4.4.2 makes the Bundle Age block
; a sum of known intervals, so it is a lower bound by construction; this book
; carries that as an explicit hypothesis rather than an axiom.

(defthm fn-clock-expired-by-age-requires-true-age-over-lifetime
  (implies (and (fn-clock-observationp obs)
                (fn-clock-age-anchorp bundle-age)
                (consp bundle-age)
                (fn-clock-timep lifetime)
                (<= (fn-clock-age-estimate bundle-age obs) true-age)
                (equal (fn-clock-expiry-decision creation-time lifetime
                                                 bundle-age obs)
                       :expired))
           (< lifetime true-age)))

; -----------------------------------------------------------------------------
; Keystone 4: monotone in local time.
;
; Once `:expired` under an observation, still `:expired` under any later
; observation of the same clock, where "later" means the monotonic counter has
; not gone backwards and the earliest admissible true time has not gone
; backwards.  Both the age path and the wall path are covered.

; The age estimate itself is the monotone quantity on the age path.
(defthm fn-clock-age-estimate-is-monotone
  (implies (and (fn-clock-observationp a)
                (fn-clock-observationp b)
                (fn-clock-age-anchorp bundle-age)
                (consp bundle-age)
                (fn-clock-later-observationp a b))
           (<= (fn-clock-age-estimate bundle-age a)
               (fn-clock-age-estimate bundle-age b))))

(defthm fn-clock-expiry-is-monotone-in-local-time
  (implies (and (fn-clock-observationp a)
                (fn-clock-observationp b)
                (fn-clock-age-anchorp bundle-age)
                (fn-clock-timep creation-time)
                (fn-clock-timep lifetime)
                (fn-clock-later-observationp a b)
                (equal (fn-clock-expiry-decision creation-time lifetime
                                                 bundle-age a)
                       :expired))
           (equal (fn-clock-expiry-decision creation-time lifetime
                                            bundle-age b)
                  :expired)))

; The age estimate itself is the monotone quantity on the age path.
; -----------------------------------------------------------------------------
; The carrier's only reading of the decision.  Named for what it is: the
; definition of `fn-clock-may-drop-local-copyp`, not a proof event.

(defthm fn-clock-drop-permission-is-exactly-expired-by-definition
  (equal (fn-clock-may-drop-local-copyp
          (fn-clock-expiry-decision creation-time lifetime bundle-age obs))
         (equal (fn-clock-expiry-decision creation-time lifetime bundle-age obs)
                :expired)))
