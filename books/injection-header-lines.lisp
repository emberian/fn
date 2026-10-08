; Injection-generated date lines satisfy the shared exact-line predicate.
(in-package "ACL2")
(include-book "injection")
(include-book "post-header-line")
(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-pb-weekday-line-textp
   (and (not (equal (fn-inj-dow-c1 n) 10))
        (not (equal (fn-inj-dow-c1 n) 13))
        (not (equal (fn-inj-dow-c2 n) 10))
        (not (equal (fn-inj-dow-c2 n) 13))
        (not (equal (fn-inj-dow-c3 n) 10))
        (not (equal (fn-inj-dow-c3 n) 13)))
   :hints (("Goal" :in-theory (enable fn-inj-dow-c1 fn-inj-dow-c2 fn-inj-dow-c3)))))

(local
 (defthm fn-pb-month-line-textp
   (and (not (equal (fn-inj-month-c1 n) 10))
        (not (equal (fn-inj-month-c1 n) 13))
        (not (equal (fn-inj-month-c2 n) 10))
        (not (equal (fn-inj-month-c2 n) 13))
        (not (equal (fn-inj-month-c3 n) 10))
        (not (equal (fn-inj-month-c3 n) 13)))
   :hints (("Goal" :in-theory (enable fn-inj-month-c1 fn-inj-month-c2 fn-inj-month-c3)))))

(local
 (defthm fn-pb-date-digit-line-textp
   (and (not (equal (fn-inj-hi2 n) 10))
        (not (equal (fn-inj-hi2 n) 13))
        (not (equal (fn-inj-lo2 n) 10))
        (not (equal (fn-inj-lo2 n) 13))
        (not (equal (fn-inj-y-th n) 10))
        (not (equal (fn-inj-y-th n) 13))
        (not (equal (fn-inj-y-hu n) 10))
        (not (equal (fn-inj-y-hu n) 13))
        (not (equal (fn-inj-y-te n) 10))
        (not (equal (fn-inj-y-te n) 13))
        (not (equal (fn-inj-y-un n) 10))
        (not (equal (fn-inj-y-un n) 13)))
   :hints (("Goal" :in-theory (enable fn-inj-hi2 fn-inj-lo2 fn-inj-y-th fn-inj-y-hu fn-inj-y-te fn-inj-y-un fn-inj-r1 fn-inj-r2)))))

(defthm fn-pb-date-octets-line-textp
  (fn-pb-line-textp (fn-inj-date-octets inst))
  :hints (("Goal" :in-theory (enable fn-pb-line-textp fn-inj-date-octets))))

(defthm fn-pb-dot-atom-line-textp
  (implies (and (true-listp bytes) (fn-af-dot-atom-text-aux bytes want))
           (fn-pb-line-textp bytes))
  :hints (("Goal" :in-theory (enable fn-af-dot-atom-text-aux fn-af-atextp
                                      fn-pb-line-textp))))

(defthm fn-pb-config-agent-line-textp
  (implies (fn-inj-configp cfg) (fn-pb-line-textp (fn-inj-config-agent cfg)))
  :hints (("Goal" :in-theory (enable fn-inj-configp fn-af-dot-atom-textp
                                      fn-cbor-octet-listp))))

(local
 (defthm fn-pb-inj-append-line-textp
   (equal (fn-pb-line-textp (fn-inj-append a b))
          (and (fn-pb-line-textp (true-list-fix a)) (fn-pb-line-textp b)))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm fn-pb-digits-rev-line-textp
   (fn-pb-line-textp (fn-inj-digits-rev n w))
   :hints (("Goal" :in-theory (enable fn-inj-digits-rev fn-pb-line-textp)))))

(local
 (defthm fn-pb-rev-append-line-textp
   (equal (fn-pb-line-textp (fn-inj-rev-append x a))
          (and (fn-pb-line-textp (true-list-fix x)) (fn-pb-line-textp a)))
   :hints (("Goal" :in-theory (enable fn-inj-rev-append fn-pb-line-textp)))))

(local
 (defthm fn-pb-digits-line-textp
   (fn-pb-line-textp (fn-inj-digits n w))
   :hints (("Goal" :in-theory (enable fn-inj-digits)))))

(defthm fn-pb-generated-id-line-textp
  (implies (fn-inj-configp cfg)
           (fn-pb-line-textp (fn-inj-generated-message-id obs cfg)))
  :hints (("Goal" :in-theory (e/d (fn-inj-generated-message-id)
                                  (fn-inj-digits fn-inj-rev-append
                                   fn-inj-digits-rev)))))

(local
 (defthm fn-pb-ihl-append
   (equal (fn-inj-append a b) (append a b))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))
(local
 (defthm fn-pb-ihl-assoc
   (equal (append (append a b) c) (append a (append b c)))
   :hints (("Goal" :in-theory
            (union-theories '(binary-append car-cons cdr-cons)
                            (theory 'minimal-theory))))))
(local
 (defthm fn-pb-ihl-len-append
   (equal (len (append a b)) (+ (len a) (len b)))
   :hints (("Goal" :in-theory
            (union-theories '(binary-append len car-cons cdr-cons)
                            (theory 'minimal-theory))))))
(local
 (defthm fn-pb-ihl-true-list-append
   (equal (true-listp (append a b)) (true-listp b))
   :hints (("Goal" :in-theory
            (union-theories '(binary-append true-listp car-cons cdr-cons)
                            (theory 'minimal-theory))))))

(defthm fn-pb-stamp-line-is-fixed
  (implies (and (fn-pb-line-textp date) (equal (len date) 31))
           (fn-pb-fixed-linep 49 (append (fn-inj-injection-date-line date) rest)))
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn-pb-fixed-linep-of-text
                     (text (append *fn-inj-injection-date-field* date)) (tail rest)))
    :in-theory (union-theories
                 '(fn-inj-injection-date-line fn-pb-ihl-append fn-pb-ihl-assoc
                   fn-pb-ihl-len-append binary-append len fn-pb-line-textp-of-append
                   fn-pb-line-text-fix fn-pb-line-textp car-cons cdr-cons)
                 (theory 'minimal-theory)))))

(defthm fn-pb-date-line-is-fixed
  (implies (and (fn-pb-line-textp date) (equal (len date) 31)) (fn-pb-fixed-linep 39 (append (fn-inj-date-line date) rest)))
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn-pb-fixed-linep-of-text
                     (text (append *fn-inj-date-field* date)) (tail rest)))
    :in-theory (union-theories '(fn-inj-date-line fn-pb-ihl-true-list-append fn-pb-ihl-append fn-pb-ihl-assoc fn-pb-ihl-len-append binary-append len fn-pb-line-textp-of-append fn-pb-line-text-fix fn-pb-line-textp car-cons cdr-cons true-listp fn-pb-line-textp-is-true-list (:type-prescription len) fold-consts-in-+ commutativity-of-+ associativity-of-+)
                               (theory 'minimal-theory)))))

(defthm fn-pb-info-line-is-fixed
  (implies (fn-pb-line-textp agent) (and (< 2 (len (fn-inj-injection-info-line agent))) (true-listp (fn-inj-injection-info-line agent)) (fn-pb-fixed-linep (len (fn-inj-injection-info-line agent)) (fn-inj-injection-info-line agent))))
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn-pb-fixed-linep-of-text
                     (text (append *fn-inj-injection-info-field* agent)) (tail nil)))
    :in-theory (union-theories '(fn-inj-injection-info-line fn-pb-ihl-true-list-append fn-pb-ihl-append fn-pb-ihl-assoc fn-pb-ihl-len-append binary-append len fn-pb-line-textp-of-append fn-pb-line-text-fix fn-pb-line-textp car-cons cdr-cons true-listp fn-pb-line-textp-is-true-list (:type-prescription len) fold-consts-in-+ commutativity-of-+ associativity-of-+)
                               (theory 'minimal-theory)))))

(defthm fn-pb-msgid-line-is-fixed
  (implies (fn-pb-line-textp mid) (and (< 2 (len (fn-inj-message-id-line mid))) (true-listp (fn-inj-message-id-line mid)) (fn-pb-fixed-linep (len (fn-inj-message-id-line mid)) (fn-inj-message-id-line mid))))
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn-pb-fixed-linep-of-text
                     (text (append *fn-inj-message-id-field* mid)) (tail nil)))
    :in-theory (union-theories '(fn-inj-message-id-line fn-pb-ihl-true-list-append fn-pb-ihl-append fn-pb-ihl-assoc fn-pb-ihl-len-append binary-append len fn-pb-line-textp-of-append fn-pb-line-text-fix fn-pb-line-textp car-cons cdr-cons true-listp fn-pb-line-textp-is-true-list (:type-prescription len) fold-consts-in-+ commutativity-of-+ associativity-of-+)
                               (theory 'minimal-theory)))))

(include-book "injection-invariants")

(local
 (defthm fn-pb-an-injection-configures
   (implies (fn-inj-injectedp (fn-inj-decide source config obs))
            (fn-inj-configp config))
   :hints (("Goal" :in-theory (e/d (fn-inj-decide fn-inj-injectedp fn-inj-refuse)
                                   (fn-inj-configp fn-inj-mandatory-reason
                                    fn-inj-groups-admissiblep fn-inj-absentp
                                    fn-inj-prefix fn-inj-date-octets
                                    fn-inj-instant-of fn-inj-generated-message-id
                                    fn-inj-append floor fn-article-parse
                                    fn-af-proto-article-check fn-article-result-okp
                                    fn-article-result-article fn-article-syntax-p
                                    fn-clock-observationp fn-clock-has-wall
                                    fn-clock-wall))))))

(defthm fn-pb-injected-generated-id-line-textp
  (implies
   (and (fn-inj-injectedp (fn-inj-decide source config observation))
        (not (fn-inj-nth 1
              (fn-af-proto-article-check
               (fn-article-result-article (fn-article-parse source))))))
   (fn-pb-line-textp
    (fn-inj-decision-msgid (fn-inj-decide source config observation))))
  :hints (("Goal"
           :use ((:instance fn-inj-generated-identity-is-the-clock-identity)
                 (:instance fn-pb-an-injection-configures (obs observation)))
           :in-theory (union-theories '(fn-pb-generated-id-line-textp)
                                     (theory 'minimal-theory)))))

(include-book "poster-bytes-source")

(defthm fn-pb-strip-header-line-no-match-by-definition
  (implies (equal (fn-inj-strip line x) :no)
           (equal (fn-pb-strip-header-line line x) :no))
  :hints (("Goal" :in-theory (enable fn-pb-strip-header-line))))

(defthm fn-pb-info-strip-is-old
  (implies (fn-pb-line-textp agent)
           (equal (fn-pb-strip-header-line (fn-inj-injection-info-line agent) x)
                  (fn-inj-strip (fn-inj-injection-info-line agent) x)))
  :hints (("Goal" :in-theory
           (union-theories '(fn-pb-strip-header-line fn-pb-info-line-is-fixed)
                           (theory 'minimal-theory)))))

(defthm fn-pb-msgid-strip-is-old
  (implies (fn-pb-line-textp mid)
           (equal (fn-pb-strip-header-line (fn-inj-message-id-line mid) x)
                  (fn-inj-strip (fn-inj-message-id-line mid) x)))
  :hints (("Goal" :in-theory
           (union-theories '(fn-pb-strip-header-line fn-pb-msgid-line-is-fixed)
                           (theory 'minimal-theory)))))

(defthm fn-pb-msgid-does-not-strip-other-fields
  (and (equal (fn-pb-strip-header-line (fn-inj-message-id-line msgid)
                                      (append (fn-inj-date-line date) rest)) :no)
       (equal (fn-pb-strip-header-line (fn-inj-message-id-line msgid)
                                      (append (fn-inj-injection-info-line agent) rest)) :no))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-pb-strip-header-line fn-inj-strip fn-inj-message-id-line
              fn-inj-date-line fn-inj-injection-info-line fn-inj-append
              binary-append car-cons cdr-cons)
            (theory 'minimal-theory)))))

(defthm fn-pb-msgid-only-strips-m-field
  (implies (and (consp x) (not (equal (car x) 77)))
           (equal (fn-pb-strip-header-line (fn-inj-message-id-line msgid) x) :no))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-pb-strip-header-line fn-inj-strip fn-inj-message-id-line
              fn-inj-append car-cons cdr-cons)
            (theory 'minimal-theory)))))
