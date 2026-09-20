; fn: what RFC 5537 section 3.5 injection guarantees.
;
; books/injection.lisp is one function of three arguments.  This book says
; what that function preserves, what it generates, and exactly which of its
; outputs move when the clock moves.  Nothing here opens the configuration or
; the decision record: both are opaque and are read through their exported
; accessor-of-constructor lemmas.

(in-package "ACL2")
(include-book "injection")
(local (include-book "arithmetic/top" :dir :system))

; Nothing below opens the article parser, the field views or the clock: they
; are closed for every proof in this book, and only the fn-inj- definitions a
; given theorem is about are re-enabled, one theorem at a time.  Opening
; fn-inj-decide with its callees enabled exhausts four million prover steps on
; its first theorem; with them closed the whole book is a few seconds.
(local (in-theory (disable fn-article-parse fn-af-proto-article-check
                           fn-article-result-okp fn-article-result-article
                           fn-article-syntax-p fn-article-get-headers
                           fn-clock-observationp fn-clock-has-wall
                           fn-clock-wall fn-clock-monotonic)))

(local
 (deftheory fn-inj-decide-theory
   (quote (fn-inj-decide fn-inj-refuse fn-inj-injectedp))))

; -----------------------------------------------------------------------------
; A refused proto-article produces no octets, and an injected one carries its
; source verbatim.

(defun fn-inj-suffixp (tail x)
  (declare (xargs :guard t :measure (acl2-count x)))
  (or (equal tail x)
      (and (consp x) (fn-inj-suffixp tail (cdr x)))))

(defthm fn-inj-append-keeps-its-second-argument-as-a-suffix
  (fn-inj-suffixp b (fn-inj-append a b))
  :hints (("Goal" :in-theory (enable fn-inj-append))))

(defthm fn-inj-refusal-produces-no-octets
  (implies (not (fn-inj-injectedp (fn-inj-decide source config observation)))
           (equal (fn-inj-decision-octets
                   (fn-inj-decide source config observation))
                  nil))
  :hints (("Goal" :in-theory (enable fn-inj-decide-theory))))

(defthm fn-inj-refusal-names-a-reason
  (implies (not (fn-inj-injectedp (fn-inj-decide source config observation)))
           (and (equal (fn-inj-decision-status
                        (fn-inj-decide source config observation))
                       :refused)
                (fn-inj-decision-reason
                 (fn-inj-decide source config observation))))
  :hints (("Goal" :in-theory (enable fn-inj-decide-theory))))

(defthm fn-inj-injected-article-retains-the-source-octets
  (implies (fn-inj-injectedp (fn-inj-decide source config observation))
           (fn-inj-suffixp source
                           (fn-inj-decision-octets
                            (fn-inj-decide source config observation))))
  :hints (("Goal" :in-theory (enable fn-inj-decide-theory))))

(defthm fn-inj-injected-article-is-within-the-configured-bound
  (implies (fn-inj-injectedp (fn-inj-decide source config observation))
           (<= (len (fn-inj-decision-octets
                     (fn-inj-decide source config observation)))
               (fn-inj-config-max-octets config)))
  :hints (("Goal" :in-theory (enable fn-inj-decide-theory))))

; -----------------------------------------------------------------------------
; The decision is a function of the source, the configuration, and exactly two
; readings of the observation.  The error bound the host attaches to a wall
; reading is not consulted, so two hosts that disagree about their confidence
; and agree about the time inject the same octets.

(defthm fn-inj-decision-uses-only-the-two-clock-readings
  (implies (and (fn-clock-observationp a)
                (fn-clock-observationp b)
                (equal (fn-clock-wall a) (fn-clock-wall b))
                (equal (fn-clock-monotonic a) (fn-clock-monotonic b))
                (equal (fn-clock-has-wall a) (fn-clock-has-wall b)))
           (equal (fn-inj-decide source config a)
                  (fn-inj-decide source config b)))
  :hints (("Goal" :in-theory (enable fn-inj-decide-theory
                                     fn-clock-observationp fn-clock-has-wall
                                     fn-clock-wall fn-clock-monotonic
                                     fn-inj-generated-message-id)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Retry identity
;
; RFC 5537 section 3.5 item 6 forbids altering an existing Message-ID header
; field.  fn keeps it octet for octet, which is the whole of the retry
; identity a posting agent can rely on: the design does NOT make a generated
; Message-ID stable across clock readings, because the generator's only inputs
; are the clock and the configured identity.  A posting agent that wants an
; exact retry identity must supply a Message-ID; one that does not gets a new
; article on every retry.  Both halves are stated here.

(defthm fn-inj-supplied-message-id-is-retained-exactly
  (implies (and (fn-inj-injectedp (fn-inj-decide source config observation))
                (fn-inj-nth 1 (fn-af-proto-article-check
                               (fn-article-result-article
                                (fn-article-parse source)))))
           (equal (fn-inj-decision-msgid
                   (fn-inj-decide source config observation))
                  (fn-inj-nth 1 (fn-af-proto-article-check
                                 (fn-article-result-article
                                  (fn-article-parse source))))))
  :hints (("Goal" :in-theory (enable fn-inj-decide-theory))))

(defthm fn-inj-supplied-identity-survives-a-different-clock
  (implies (and (fn-inj-injectedp (fn-inj-decide source config a))
                (fn-inj-injectedp (fn-inj-decide source config b))
                (fn-inj-nth 1 (fn-af-proto-article-check
                               (fn-article-result-article
                                (fn-article-parse source)))))
           (equal (fn-inj-decision-msgid (fn-inj-decide source config a))
                  (fn-inj-decision-msgid (fn-inj-decide source config b))))
  :hints (("Goal" :use ((:instance fn-inj-supplied-message-id-is-retained-exactly
                                   (observation a))
                        (:instance fn-inj-supplied-message-id-is-retained-exactly
                                   (observation b)))
           :in-theory (disable fn-inj-supplied-message-id-is-retained-exactly)))
  :rule-classes nil)

(defthm fn-inj-generated-identity-is-the-clock-identity
  (implies (and (fn-inj-injectedp (fn-inj-decide source config observation))
                (not (fn-inj-nth 1 (fn-af-proto-article-check
                                    (fn-article-result-article
                                     (fn-article-parse source))))))
           (equal (fn-inj-decision-msgid
                   (fn-inj-decide source config observation))
                  (fn-inj-generated-message-id observation config)))
  :hints (("Goal" :in-theory (enable fn-inj-decide-theory))))

; -----------------------------------------------------------------------------
; The calendar has an exact left inverse
;
; Each walk stops in a unit; the offset of that unit plus the remainder it
; returns is the input.  Injectivity of the decomposition follows with no
; further arithmetic.

(defthm fn-inj-year-of-inverts
  (implies (and (natp y) (<= 2000 y))
           (equal (+ (fn-inj-days-before-year
                      (fn-inj-car (fn-inj-year-of days y fuel)))
                     (fn-inj-cdr (fn-inj-year-of days y fuel)))
                  (+ (fn-inj-days-before-year y) (nfix days))))
  :hints (("Goal" :induct (fn-inj-year-of days y fuel)
           :in-theory (enable fn-inj-year-of fn-inj-days-before-year
                              fn-inj-car fn-inj-cdr))))

(defthm fn-inj-year-of-is-injective
  (implies (and (natp a) (natp b)
                (equal (fn-inj-year-of a 2000 fuel)
                       (fn-inj-year-of b 2000 fuel)))
           (equal a b))
  :hints (("Goal" :use ((:instance fn-inj-year-of-inverts (days a) (y 2000))
                        (:instance fn-inj-year-of-inverts (days b) (y 2000)))
           :in-theory (disable fn-inj-year-of-inverts fn-inj-year-of)))
  :rule-classes nil)

(defthm fn-inj-month-of-inverts
  (implies (and (natp m) (<= 1 m))
           (equal (+ (fn-inj-days-before-month
                      (fn-inj-car (fn-inj-month-of doy m leap fuel)) leap)
                     (fn-inj-cdr (fn-inj-month-of doy m leap fuel)))
                  (+ (fn-inj-days-before-month m leap) (nfix doy))))
  :hints (("Goal" :induct (fn-inj-month-of doy m leap fuel)
           :in-theory (enable fn-inj-month-of fn-inj-days-before-month
                              fn-inj-car fn-inj-cdr))))

(defthm fn-inj-month-of-is-injective
  (implies (and (natp a) (natp b)
                (equal (fn-inj-month-of a 1 leap fuel)
                       (fn-inj-month-of b 1 leap fuel)))
           (equal a b))
  :hints (("Goal" :use ((:instance fn-inj-month-of-inverts (doy a) (m 1))
                        (:instance fn-inj-month-of-inverts (doy b) (m 1)))
           :in-theory (disable fn-inj-month-of-inverts fn-inj-month-of)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The rendering has an exact left inverse at fixed width, so two different
; instants render two different Injection-Date field bodies.

(defun fn-inj-instantp (x)
  (declare (xargs :guard t))
  (declare (xargs :normalize nil))
  (and (natp (fn-inj-instant-year x))
       (< (fn-inj-instant-year x) 10000)
       (natp (fn-inj-instant-month x))
       (<= 1 (fn-inj-instant-month x))
       (<= (fn-inj-instant-month x) 12)
       (natp (fn-inj-instant-day x))
       (< (fn-inj-instant-day x) 100)
       (natp (fn-inj-instant-hour x))
       (< (fn-inj-instant-hour x) 100)
       (natp (fn-inj-instant-minute x))
       (< (fn-inj-instant-minute x) 100)
       (natp (fn-inj-instant-second x))
       (< (fn-inj-instant-second x) 100)))

(defthm fn-inj-instantp-opens
  (implies (fn-inj-instantp x)
           (and (natp (fn-inj-instant-year x))
                (< (fn-inj-instant-year x) 10000)
                (natp (fn-inj-instant-month x))
                (<= 1 (fn-inj-instant-month x))
                (<= (fn-inj-instant-month x) 12)
                (natp (fn-inj-instant-day x))
                (< (fn-inj-instant-day x) 100)
                (natp (fn-inj-instant-hour x))
                (< (fn-inj-instant-hour x) 100)
                (natp (fn-inj-instant-minute x))
                (< (fn-inj-instant-minute x) 100)
                (natp (fn-inj-instant-second x))
                (< (fn-inj-instant-second x) 100)))
  :rule-classes nil)

(defthm fn-inj-month-index-inverts-the-month-name
  (implies (and (natp m) (<= 1 m) (<= m 12))
           (equal (fn-inj-month-index (fn-inj-month-c1 m) (fn-inj-month-c2 m)
                                      (fn-inj-month-c3 m))
                  m))
  :hints (("Goal" :in-theory (enable fn-inj-month-index fn-inj-month-c1
                                     fn-inj-month-c2 fn-inj-month-c3))))

(defthm fn-inj-un2-recombines-two-digits
  (equal (fn-inj-un2 (fn-inj-hi2 n) (fn-inj-lo2 n)) (nfix n))
  :hints (("Goal" :in-theory (e/d (fn-inj-un2 fn-inj-hi2 fn-inj-lo2)
                                  (floor mod)))))

(defthm fn-inj-un4-recombines-four-digits
  (equal (fn-inj-un4 (fn-inj-y-th n) (fn-inj-y-hu n)
                     (fn-inj-y-te n) (fn-inj-y-un n))
         (nfix n))
  :hints (("Goal" :in-theory (e/d (fn-inj-un4 fn-inj-y-th fn-inj-y-hu
                                   fn-inj-y-te fn-inj-y-un fn-inj-r1
                                   fn-inj-r2)
                                  (floor mod)))))

(defthm fn-inj-date-decode-inverts-the-rendering
  (implies (and (natp (fn-inj-instant-month inst))
                (<= 1 (fn-inj-instant-month inst))
                (<= (fn-inj-instant-month inst) 12))
           (equal (fn-inj-date-decode (fn-inj-date-octets inst))
                  (list (nfix (fn-inj-instant-year inst))
                        (fn-inj-instant-month inst)
                        (nfix (fn-inj-instant-day inst))
                        (nfix (fn-inj-instant-hour inst))
                        (nfix (fn-inj-instant-minute inst))
                        (nfix (fn-inj-instant-second inst)))))
  :hints (("Goal" :in-theory (e/d (fn-inj-date-decode fn-inj-date-octets
                                   fn-inj-nth fn-inj-car fn-inj-cdr)
                                  (floor mod fn-inj-un2 fn-inj-un4
                                   fn-inj-hi2 fn-inj-lo2 fn-inj-r1 fn-inj-r2
                                   fn-inj-y-th fn-inj-y-hu fn-inj-y-te
                                   fn-inj-y-un fn-inj-month-index
                                   fn-inj-month-c1 fn-inj-month-c2
                                   fn-inj-month-c3 fn-inj-dow-c1 fn-inj-dow-c2
                                   fn-inj-dow-c3 fn-inj-instant-year
                                   fn-inj-instant-month fn-inj-instant-day
                                   fn-inj-instant-hour fn-inj-instant-minute
                                   fn-inj-instant-second
                                   fn-inj-instant-dow)))))

(defthm fn-inj-date-octets-separate-different-instants
  (implies (and (fn-inj-instantp a) (fn-inj-instantp b)
                (equal (fn-inj-date-octets a) (fn-inj-date-octets b)))
           (and (equal (fn-inj-instant-year a) (fn-inj-instant-year b))
                (equal (fn-inj-instant-month a) (fn-inj-instant-month b))
                (equal (fn-inj-instant-day a) (fn-inj-instant-day b))
                (equal (fn-inj-instant-hour a) (fn-inj-instant-hour b))
                (equal (fn-inj-instant-minute a) (fn-inj-instant-minute b))
                (equal (fn-inj-instant-second a) (fn-inj-instant-second b))))
  :hints (("Goal" :use ((:instance fn-inj-instantp-opens (x a))
                        (:instance fn-inj-instantp-opens (x b))
                        (:instance fn-inj-date-decode-inverts-the-rendering
                                   (inst a))
                        (:instance fn-inj-date-decode-inverts-the-rendering
                                   (inst b)))
           :in-theory (disable fn-inj-date-decode fn-inj-date-octets
                               fn-inj-date-decode-inverts-the-rendering
                               fn-inj-instantp fn-inj-nth)))
  :rule-classes nil)
