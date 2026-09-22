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

; -----------------------------------------------------------------------------
; The generated identifier separates two clock readings
;
; A generated Message-ID is <wall.monotonic.fn@agent> with each number
; rendered at a fixed width of twenty decimal digits, and every
; fn-clock-timep value is below 10^20.  Fixed-width decimal has an exact
; left inverse, so two readings that differ in either number generate two
; different identifiers.  This is the fact the owner's POST seam rests on:
; an injection clock taken per submission gives each submission on a
; connection its own identity, where one reading pinned per connection gave
; every submission on it the identity of the first
; (fn-post-distinct-injection-clocks-give-distinct-identities,
; books/nntp-post.lisp).

(local
 (defthm fn-inj-append-is-associative
   (equal (fn-inj-append (fn-inj-append a b) c)
          (fn-inj-append a (fn-inj-append b c)))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm fn-inj-append-nil-right
   (implies (true-listp a) (equal (fn-inj-append a nil) a))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

; The non-tail-recursive reverse the accumulating one computes.  Stating the
; accumulator lemma against this shape is what makes the induction close.
(local
 (defun fn-inj-rv (xs)
   (declare (xargs :guard t))
   (if (consp xs)
       (fn-inj-append (fn-inj-rv (cdr xs)) (list (car xs)))
     nil)))

(local
 (defthm fn-inj-true-listp-of-rv
   (true-listp (fn-inj-rv xs))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm fn-inj-rev-append-is-rv
   (equal (fn-inj-rev-append xs acc)
          (fn-inj-append (fn-inj-rv xs) acc))
   :hints (("Goal" :in-theory (enable fn-inj-rev-append fn-inj-append)
            :induct (fn-inj-rev-append xs acc)))))

(local
 (defthm fn-inj-rv-of-append
   (equal (fn-inj-rv (fn-inj-append a b))
          (fn-inj-append (fn-inj-rv b) (fn-inj-rv a)))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm fn-inj-rv-of-rv
   (implies (true-listp xs) (equal (fn-inj-rv (fn-inj-rv xs)) xs))
   :hints (("Goal" :in-theory (enable fn-inj-append)
            :induct (fn-inj-rv xs)))))

(local
 (defthm fn-inj-true-listp-of-digits-rev
   (true-listp (fn-inj-digits-rev n w))
   :hints (("Goal" :in-theory (enable fn-inj-digits-rev)))))

(local
 (defthm fn-inj-digits-is-rv-of-digits-rev
   (equal (fn-inj-digits n w) (fn-inj-rv (fn-inj-digits-rev n w)))
   :hints (("Goal" :in-theory (enable fn-inj-digits)))))

; The exact left inverse of the least-significant-first rendering.  The
; floor/mod facts the induction needs (books/arithmetic/top.lisp states
; none) come from ihs, locally and only for the forms below.
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

(local
 (defun fn-inj-undigits-rev (xs)
   (declare (xargs :guard t))
   (if (consp xs)
       (+ (- (fix (car xs)) 48) (* 10 (fn-inj-undigits-rev (cdr xs))))
     0)))

(local
 (defthm fn-inj-expt-10-step
   (implies (and (integerp w) (< 0 w))
            (equal (expt 10 w) (* 10 (expt 10 (+ -1 w)))))
   :hints (("Goal" :expand ((expt 10 w))))
   :rule-classes nil))

(local
 (defthm fn-inj-floor-10-is-a-natural
   (implies (natp n) (and (integerp (floor n 10)) (<= 0 (floor n 10))))
   :rule-classes ((:type-prescription
                   :corollary (implies (natp n) (natp (floor n 10))))
                  (:rewrite
                   :corollary (implies (natp n) (natp (floor n 10)))))
   :hints (("Goal" :in-theory (enable floor)))))

(local
 (defthm fn-inj-undigits-rev-inverts-digits-rev
   (implies (and (natp n) (natp w) (< n (expt 10 w)))
            (equal (fn-inj-undigits-rev (fn-inj-digits-rev n w)) n))
   :hints (("Goal" :in-theory (e/d (fn-inj-digits-rev) (floor mod expt))
            :induct (fn-inj-digits-rev n w))
           ("Subgoal *1/1" :use ((:instance fn-inj-expt-10-step)))
           ("Subgoal *1/2" :use ((:instance fn-inj-expt-10-step))))))

(local
 (defthm fn-inj-digits-are-injective-below-the-width
   (implies (and (natp n) (natp m) (natp w)
                 (< n (expt 10 w)) (< m (expt 10 w))
                 (equal (fn-inj-digits n w) (fn-inj-digits m w)))
            (equal n m))
   :hints (("Goal"
            :use ((:instance fn-inj-undigits-rev-inverts-digits-rev)
                  (:instance fn-inj-undigits-rev-inverts-digits-rev (n m))
                  (:instance fn-inj-rv-of-rv (xs (fn-inj-digits-rev n w)))
                  (:instance fn-inj-rv-of-rv (xs (fn-inj-digits-rev m w))))
            :in-theory (disable fn-inj-undigits-rev-inverts-digits-rev
                                fn-inj-rv-of-rv fn-inj-undigits-rev
                                fn-inj-digits-rev)))
   :rule-classes nil))

(local
 (defthm fn-inj-len-of-append
   (equal (len (fn-inj-append a b)) (+ (len a) (len b)))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm fn-inj-len-of-rv
   (equal (len (fn-inj-rv xs)) (len xs))))

(local
 (defthm fn-inj-len-of-digits-rev
   (equal (len (fn-inj-digits-rev n w)) (nfix w))
   :hints (("Goal" :in-theory (enable fn-inj-digits-rev)))))

(local
 (defthm fn-inj-len-of-digits
   (equal (len (fn-inj-digits n w)) (nfix w))))

(local
 (defun fn-inj-two-list-induct (a b)
   (declare (xargs :guard t))
   (if (and (consp a) (consp b))
       (fn-inj-two-list-induct (cdr a) (cdr b))
     (list a b))))

(local
 (defthm fn-inj-append-cancels-at-equal-length
   (implies (and (equal (len a) (len b))
                 (true-listp a) (true-listp b)
                 (equal (fn-inj-append a u) (fn-inj-append b v)))
            (and (equal a b) (equal u v)))
   :hints (("Goal" :in-theory (enable fn-inj-append)
            :induct (fn-inj-two-list-induct a b)))
   :rule-classes nil))

(local
 (defthm fn-inj-true-listp-of-digits
   (true-listp (fn-inj-digits n w))
   :hints (("Goal" :in-theory (e/d (fn-inj-digits)
                                   (fn-inj-digits-is-rv-of-digits-rev))))))

(defthm fn-inj-generated-identity-separates-different-clock-readings
  (implies (and (fn-clock-observationp a) (fn-clock-observationp b)
                (equal (fn-inj-generated-message-id a config)
                       (fn-inj-generated-message-id b config)))
           (and (equal (fn-clock-wall a) (fn-clock-wall b))
                (equal (fn-clock-monotonic a) (fn-clock-monotonic b))))
  :hints (("Goal"
           :in-theory (e/d (fn-inj-generated-message-id fn-clock-observationp
                            fn-clock-timep)
                           (fn-inj-digits fn-inj-append
                            fn-inj-digits-is-rv-of-digits-rev))
           :use ((:instance fn-inj-append-cancels-at-equal-length (a '(60)) (b '(60))
                            (u (fn-inj-append (fn-inj-digits (fn-clock-wall a) 20) (fn-inj-append '(46) (fn-inj-append (fn-inj-digits (fn-clock-monotonic a) 20) (fn-inj-append *fn-inj-id-tail* (fn-inj-append (fn-inj-config-agent config) '(62))))))) (v (fn-inj-append (fn-inj-digits (fn-clock-wall b) 20) (fn-inj-append '(46) (fn-inj-append (fn-inj-digits (fn-clock-monotonic b) 20) (fn-inj-append *fn-inj-id-tail* (fn-inj-append (fn-inj-config-agent config) '(62))))))))
                 (:instance fn-inj-append-cancels-at-equal-length
                            (a (fn-inj-digits (fn-clock-wall a) 20))
                            (b (fn-inj-digits (fn-clock-wall b) 20))
                            (u (fn-inj-append '(46) (fn-inj-append (fn-inj-digits (fn-clock-monotonic a) 20) (fn-inj-append *fn-inj-id-tail* (fn-inj-append (fn-inj-config-agent config) '(62)))))) (v (fn-inj-append '(46) (fn-inj-append (fn-inj-digits (fn-clock-monotonic b) 20) (fn-inj-append *fn-inj-id-tail* (fn-inj-append (fn-inj-config-agent config) '(62)))))))
                 (:instance fn-inj-append-cancels-at-equal-length (a '(46)) (b '(46))
                            (u (fn-inj-append (fn-inj-digits (fn-clock-monotonic a) 20) (fn-inj-append *fn-inj-id-tail* (fn-inj-append (fn-inj-config-agent config) '(62))))) (v (fn-inj-append (fn-inj-digits (fn-clock-monotonic b) 20) (fn-inj-append *fn-inj-id-tail* (fn-inj-append (fn-inj-config-agent config) '(62))))))
                 (:instance fn-inj-append-cancels-at-equal-length
                            (a (fn-inj-digits (fn-clock-monotonic a) 20))
                            (b (fn-inj-digits (fn-clock-monotonic b) 20))
                            (u (fn-inj-append *fn-inj-id-tail* (fn-inj-append (fn-inj-config-agent config) '(62)))) (v (fn-inj-append *fn-inj-id-tail* (fn-inj-append (fn-inj-config-agent config) '(62)))))
                 (:instance fn-inj-digits-are-injective-below-the-width
                            (n (fn-clock-wall a)) (m (fn-clock-wall b)) (w 20))
                 (:instance fn-inj-digits-are-injective-below-the-width
                            (n (fn-clock-monotonic a))
                            (m (fn-clock-monotonic b)) (w 20)))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; RFC 5536 section 3.1.2: an injected proto-article's From is a mailbox-list
; (books/mailbox.lisp), and so names an address.  `From: yue' was injected
; and served until 2026-09-22 because only presence was checked; this is the
; property the node was missing, over the function the served POST
; (books/nntp-post.lisp `fn-nntp-post-step') and the operator's submission
; (books/owner.lisp `fn-own-operator-decision') both call.  The address half
; is books/mailbox.lisp's `fn-mbx-mailbox-list-names-an-address', which does
; the work; the arm of `fn-inj-mandatory-reason' only places it.

; An injection happened only where posting is allowed; the operator's retry
; keystone (books/owner-invariants.lisp) reads this.
(defthm fn-inj-injection-requires-posting-allowed
  (implies (fn-inj-injectedp (fn-inj-decide source config observation))
           (fn-inj-config-allow config))
  :hints (("Goal" :in-theory (enable fn-inj-decide-theory))))

(defthm fn-inj-injected-proto-article-has-a-mailbox-list-from
  (implies (fn-inj-injectedp (fn-inj-decide source config observation))
           (let* ((article (fn-article-result-article (fn-article-parse source)))
                  (value (fn-article-field-unfolded-value
                          (car (fn-article-get-headers article
                                                       *fn-inj-from-name*)))))
             (and (fn-mbx-mailbox-listp value)
                  (member-equal 64 value))))
  :hints (("Goal" :in-theory (e/d (fn-inj-decide-theory fn-inj-mandatory-reason
                                   fn-inj-from-validp)
                                  (fn-mbx-mailbox-listp)))))

; -----------------------------------------------------------------------------
; Every injected article is a re-injection of its source (books/injection.lisp
; `fn-inj-reinjectionp'): this agent's Path line, an Injection-Date line, this
; agent's Injection-Info line, then optionally the generated Message-ID and
; Date lines, then the source octet for octet.  It holds for every clock
; reading, which is why a stored injection is recognisable when the same
; proto-article is submitted again under a later clock
; (books/owner.lisp `fn-own-operator-decision').

(local
 (defthm fn-inj-strip-of-append-left
   (implies (true-listp a)
            (equal (fn-inj-strip a (fn-inj-append a b)) b))
   :hints (("Goal" :in-theory (enable fn-inj-strip fn-inj-append)))))

(local
 (defthm fn-inj-strip-by-an-append
   (implies (true-listp a)
            (equal (fn-inj-strip (fn-inj-append a b) x)
                   (fn-inj-strip b (fn-inj-strip a x))))
   :hints (("Goal" :in-theory (enable fn-inj-strip fn-inj-append)))))

(local
 (defthm fn-inj-drop-of-append
   (implies (and (true-listp a) (equal n (len a)))
            (equal (fn-inj-drop n (fn-inj-append a b)) b))
   :hints (("Goal" :in-theory (enable fn-inj-drop fn-inj-append)))))

(local
 (defthm fn-inj-take-of-append
   (implies (and (true-listp a) (equal n (len a)))
            (equal (fn-inj-take n (fn-inj-append a b)) a))
   :hints (("Goal" :in-theory (enable fn-inj-take fn-inj-append)))))

(local
 (defthm fn-inj-true-listp-of-append
   (equal (true-listp (fn-inj-append a b)) (true-listp b))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm fn-inj-date-octets-shape
   (and (true-listp (fn-inj-date-octets inst))
        (equal (len (fn-inj-date-octets inst)) 31))
   :hints (("Goal" :in-theory (enable fn-inj-date-octets)))))

(local
 (defthm fn-inj-append-of-nil
   (equal (fn-inj-append nil b) b)
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm fn-inj-append-of-a-cons-is-a-cons
   (implies (consp a) (consp (fn-inj-append a b)))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm fn-inj-true-listp-of-generated-message-id
   (true-listp (fn-inj-generated-message-id obs config))
   :hints (("Goal" :in-theory (enable fn-inj-generated-message-id)))))

(local
 (defthm fn-inj-strip-of-nil
   (equal (fn-inj-strip nil x) x)
   :hints (("Goal" :in-theory (enable fn-inj-strip)))))

(defthm fn-inj-injected-article-is-a-reinjection-of-its-source
  (implies (fn-inj-injectedp (fn-inj-decide source config observation))
           (fn-inj-reinjectionp
            (fn-inj-decision-octets (fn-inj-decide source config observation))
            source
            (fn-inj-config-agent config)
            (fn-inj-decision-msgid (fn-inj-decide source config observation))))
  :hints (("Goal" :in-theory (e/d (fn-inj-decide-theory fn-inj-reinjectionp
                                   fn-inj-tail-matchp fn-inj-prefix
                                   fn-inj-path-line fn-inj-injection-date-line
                                   fn-inj-injection-info-line fn-inj-date-line
                                   fn-inj-message-id-line fn-inj-configp)
                                  (fn-inj-date-octets fn-inj-instant-of
                                   fn-inj-generated-message-id
                                   fn-inj-mandatory-reason
                                   fn-af-proto-article-check)))))
