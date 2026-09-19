; fn: local clock observations and bundle expiry decisions.
;
; RFC 9171 section 4.2.8 makes bundle lifetime a duration measured from the
; creation timestamp, and section 5.5 says bundle age MAY be computed from the
; creation timestamp only when that timestamp is non-zero AND the local clock
; is known to be accurate; otherwise age MUST come from the Bundle Age
; extension block (section 4.4.2).  fn's failure model (FLR-004) additionally
; requires that safety never depend on a synchronized global clock.
;
; This book models the host-supplied observation and the expiry decision only.
; It performs no I/O, no deletion, and no retention release.  Its three
; outcomes are deliberately distinct: `:expired`, `:live`, `:uncertain`.  An
; `:uncertain` result is not permission to delete anything.
;
; The host supplies an observation
;   (monotonic wall wall-error-bound has-wall)
; where `monotonic` is a non-decreasing local counter in milliseconds with no
; epoch meaning, `wall` is the local estimate of DTN time (milliseconds since
; 2000-01-01T00:00:00Z, RFC 9171 section 4.2.6), `wall-error-bound` is the
; half-width of the interval the host is willing to certify contains the true
; DTN time, and `has-wall` says whether the host claims any wall reading at all.
;
; Bundle age reaches this book as an anchor (age . monotonic-at-anchor): the
; bundle's age in milliseconds as most recently established, together with the
; monotonic reading at which it was established.  The current age estimate is
; that age plus the monotonic time elapsed since.  This is the only shape that
; makes the age path monotone in local elapsed time without a wall clock.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; Domains

; DTN time and durations are CBOR unsigned integers of at most 64 bits
; (RFC 9171 sections 4.2.6 and 4.3.1).  The same bound applies to the modeled
; quantities so that a decision input is always representable in a bundle.
(defconst *fn-clock-max* 18446744073709551615)

(defun fn-clock-timep (x)
  (declare (xargs :guard t))
  (and (natp x) (<= x *fn-clock-max*)))

(defun fn-clock-observation-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 5)
       (equal (car x) :fn-clock-observation)))
(defun fn-clock-observation (monotonic wall wall-error has-wall)
  (declare (xargs :guard t))
  (list :fn-clock-observation monotonic wall wall-error (if has-wall t nil)))
; Accessors are total: the :logic branch is the positional reader, the :exec
; branch its guard-free substitute (docs/proof-style.md, section 1).
(defun fn-clock-monotonic (x)
  (declare (xargs :guard t))
  (mbe :logic (nth 1 x)
       :exec (and (consp x) (consp (cdr x)) (car (cdr x)))))
(defun fn-clock-wall (x)
  (declare (xargs :guard t))
  (mbe :logic (nth 2 x)
       :exec (and (consp x) (consp (cdr x)) (consp (cddr x)) (car (cddr x)))))
(defun fn-clock-wall-error (x)
  (declare (xargs :guard t))
  (mbe :logic (nth 3 x)
       :exec (and (consp x) (consp (cdr x)) (consp (cddr x)) (consp (cdddr x))
                  (car (cdddr x)))))
(defun fn-clock-has-wall (x)
  (declare (xargs :guard t))
  (mbe :logic (nth 4 x)
       :exec (and (consp x) (consp (cdr x)) (consp (cddr x)) (consp (cdddr x))
                  (consp (cddddr x)) (car (cddddr x)))))
(defun fn-clock-observationp (x)
  (declare (xargs :guard t))
  (and (fn-clock-observation-shapep x)
       (fn-clock-timep (fn-clock-monotonic x))
       (fn-clock-timep (fn-clock-wall x))
       (fn-clock-timep (fn-clock-wall-error x))
       (booleanp (fn-clock-has-wall x))))
(verify-guards fn-clock-timep)
(verify-guards fn-clock-observation-shapep)
(verify-guards fn-clock-observation)
(verify-guards fn-clock-monotonic)
(verify-guards fn-clock-wall)
(verify-guards fn-clock-wall-error)
(verify-guards fn-clock-has-wall)
(verify-guards fn-clock-observationp)

(defthm fn-clock-observation-shapep-of-fn-clock-observation
  (fn-clock-observation-shapep (fn-clock-observation monotonic wall wall-error has-wall)))
(defthm fn-clock-monotonic-of-fn-clock-observation
  (equal (fn-clock-monotonic (fn-clock-observation monotonic wall wall-error has-wall))
         monotonic))
(defthm fn-clock-wall-of-fn-clock-observation
  (equal (fn-clock-wall (fn-clock-observation monotonic wall wall-error has-wall))
         wall))
(defthm fn-clock-wall-error-of-fn-clock-observation
  (equal (fn-clock-wall-error (fn-clock-observation monotonic wall wall-error has-wall))
         wall-error))
(defthm fn-clock-has-wall-of-fn-clock-observation
  (equal (fn-clock-has-wall (fn-clock-observation monotonic wall wall-error has-wall))
         (if has-wall t nil)))
(defthm fn-clock-observation-shapep-forward-shape
  (implies (fn-clock-observation-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-clock-observation-accessors-forward-consp
  (and (implies (fn-clock-monotonic x) (consp x))
       (implies (fn-clock-wall x) (consp x))
       (implies (fn-clock-wall-error x) (consp x))
       (implies (fn-clock-has-wall x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-clock-monotonic x) (consp x))
                                    :trigger-terms ((fn-clock-monotonic x)))
                 (:forward-chaining :corollary (implies (fn-clock-wall x) (consp x))
                                    :trigger-terms ((fn-clock-wall x)))
                 (:forward-chaining :corollary (implies (fn-clock-wall-error x) (consp x))
                                    :trigger-terms ((fn-clock-wall-error x)))
                 (:forward-chaining :corollary (implies (fn-clock-has-wall x) (consp x))
                                    :trigger-terms ((fn-clock-has-wall x)))))
(defthm fn-clock-observationp-forward-shape
  (implies (fn-clock-observationp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-clock-observationp fn-clock-observation-shapep))))
(in-theory (disable (:d fn-clock-observation-shapep) (:d fn-clock-monotonic)
                    (:d fn-clock-wall) (:d fn-clock-wall-error) (:d fn-clock-has-wall)
                    (:d fn-clock-observation)))

(defun fn-clock-age-anchorp (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (consp x)
           (fn-clock-timep (car x))
           (fn-clock-timep (cdr x)))))

(defun fn-clock-anchor-age (x)
  (declare (xargs :guard (and (fn-clock-age-anchorp x) (consp x))))
  (car x))

(defun fn-clock-anchor-monotonic (x)
  (declare (xargs :guard (and (fn-clock-age-anchorp x) (consp x))))
  (cdr x))

(verify-guards fn-clock-age-anchorp)
(verify-guards fn-clock-anchor-age)
(verify-guards fn-clock-anchor-monotonic)

; -----------------------------------------------------------------------------
; The admissible-time interval of a single observation
;
; These two functions name what the host is asserting when it hands over a
; wall reading: the true DTN time lies in [earliest, latest].  Nothing here
; relates the interval of one node to the interval of any other node.

(defun fn-clock-earliest-true (obs)
  (declare (xargs :guard (fn-clock-observationp obs)))
  (nfix (- (fn-clock-wall obs) (fn-clock-wall-error obs))))

(defun fn-clock-latest-true (obs)
  (declare (xargs :guard (fn-clock-observationp obs)))
  (+ (fn-clock-wall obs) (fn-clock-wall-error obs)))

(defun fn-clock-admissible-truep (obs now)
  (declare (xargs :guard (fn-clock-observationp obs)))
  (and (fn-clock-timep now)
       (fn-clock-has-wall obs)
       (<= (fn-clock-earliest-true obs) now)
       (<= now (fn-clock-latest-true obs))))

(verify-guards fn-clock-earliest-true)
(verify-guards fn-clock-latest-true)
(verify-guards fn-clock-admissible-truep)

; -----------------------------------------------------------------------------
; Age estimate from an anchor
;
; The Bundle Age block (RFC 9171 section 4.4.2) carries the sum of the known
; intervals of the bundle's residence and transmission up to its most recent
; forwarding.  The local node adds its own residence measured monotonically.
; The result is a lower bound on the bundle's true age; it is never an upper
; bound, because intervals unknown to every forwarder are omitted.

(defun fn-clock-age-estimate (anchor obs)
  (declare (xargs :guard (and (fn-clock-age-anchorp anchor)
                              (fn-clock-observationp obs))))
  (if (not (consp anchor))
      nil
    (+ (fn-clock-anchor-age anchor)
       (nfix (- (fn-clock-monotonic obs) (fn-clock-anchor-monotonic anchor))))))

(verify-guards fn-clock-age-estimate)

(defthm fn-clock-age-estimate-is-natural
  (implies (and (fn-clock-age-anchorp anchor)
                (fn-clock-observationp obs)
                (consp anchor))
           (and (natp (fn-clock-age-estimate anchor obs))
                (integerp (fn-clock-age-estimate anchor obs))
                (<= 0 (fn-clock-age-estimate anchor obs)))))

; -----------------------------------------------------------------------------
; The decision
;
; Bundle age takes precedence over the wall clock exactly as RFC 9171
; section 5.5 requires: a node without an accurate wall clock MUST use the
; Bundle Age block.  fn goes further and prefers the age path whenever an
; anchor exists, because the age path needs no clock agreement at all.
;
; On the wall path the decision is taken over the whole admissible interval:
;   `:expired`   every admissible true time puts the age past the lifetime
;   `:live`      no admissible true time puts the age past the lifetime
;   `:uncertain` the interval straddles the lifetime, or there is no usable
;                wall reading, or the creation timestamp is zero ("unknown",
;                RFC 9171 section 4.2.6)

(defun fn-clock-expiry-decision (creation-time lifetime bundle-age observation)
  (declare (xargs :guard (and (fn-clock-timep creation-time)
                              (fn-clock-timep lifetime)
                              (fn-clock-age-anchorp bundle-age)
                              (fn-clock-observationp observation))))
  (if (consp bundle-age)
      (if (< lifetime (fn-clock-age-estimate bundle-age observation))
          :expired
        :live)
    (if (or (not (fn-clock-has-wall observation))
            (equal creation-time 0))
        :uncertain
      (let ((earliest (fn-clock-earliest-true observation))
            (latest (fn-clock-latest-true observation)))
        (cond ((< lifetime (nfix (- earliest creation-time))) :expired)
              ((<= (nfix (- latest creation-time)) lifetime) :live)
              (t :uncertain))))))

(verify-guards fn-clock-expiry-decision)

; -----------------------------------------------------------------------------
; Comparing two observations of one clock
;
; "Later" is not "a bigger number".  The contract a host must meet for the
; monotonicity theorem is that the local monotonic counter does not go
; backwards and that the earliest admissible true time does not go backwards.
; A resynchronization that widens the error bound enough to move the earliest
; admissible time backwards is therefore NOT a later observation of the same
; clock, and the monotonicity theorem does not apply to it.

(defun fn-clock-later-observationp (a b)
  (declare (xargs :guard (and (fn-clock-observationp a)
                              (fn-clock-observationp b))))
  (and (<= (fn-clock-monotonic a) (fn-clock-monotonic b))
       (equal (fn-clock-has-wall a) (fn-clock-has-wall b))
       (<= (fn-clock-earliest-true a) (fn-clock-earliest-true b))))

(verify-guards fn-clock-later-observationp)

; -----------------------------------------------------------------------------
; Retention coupling
;
; fn never releases an obligation on an expiry decision.  This function names
; the only reading of the decision that the carrier is allowed to make: may the
; local BPA drop its own copy of the bundle?  `:uncertain` is not permission.

(defun fn-clock-may-drop-local-copyp (decision)
  (declare (xargs :guard t))
  (equal decision :expired))

(verify-guards fn-clock-may-drop-local-copyp)

; Export theory.  The observation record is opaque above.  The recognizers,
; readings and the decision are proof vocabulary for clock-invariants, which
; opens them locally; fn-clock-timep stays enabled as glue.
(deftheory fn-clock-vocabulary
  '(fn-clock-observationp fn-clock-age-anchorp fn-clock-anchor-age
    fn-clock-anchor-monotonic fn-clock-earliest-true fn-clock-latest-true
    fn-clock-admissible-truep fn-clock-age-estimate fn-clock-expiry-decision
    fn-clock-later-observationp fn-clock-may-drop-local-copyp))
(in-theory (disable fn-clock-vocabulary))
