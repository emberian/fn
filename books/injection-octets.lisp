; fn: injection admission produces octets, including generated field bytes.
; This is the producer fact for the queued-submission domain, not a runtime scan.
(in-package "ACL2")
(include-book "injection")
(include-book "packed-octets")
(include-book "acceptance-alloc")
(local (in-theory (union-theories '(natp nfix zp max car-cons cdr-cons)
                                  (theory 'minimal-theory))))
(local (include-book "arithmetic-5/top" :dir :system))

(defthm fn-io-octet-recognizers
 (and (equal (fn-bch-octetsp x) (fn-cbor-octet-listp x))
      (equal (fn-bch-octetsp x) (fn-octet-listp x)))
 :hints (("Goal" :in-theory (enable fn-bch-octetsp fn-bch-octetp fn-cbor-octet-listp fn-cbor-octetp fn-octet-listp fn-octetp))))

(local
 (defthm fn-io-year-of-bound
 (and (natp (car (fn-inj-year-of days y fuel)))
      (<= (car (fn-inj-year-of days y fuel)) (+ (nfix y) (nfix fuel)))
      (natp (cdr (fn-inj-year-of days y fuel)))
      (<= (cdr (fn-inj-year-of days y fuel))
          (max 365 (- (nfix days) (* 365 (nfix fuel))))))
 :hints (("Goal" :induct (fn-inj-year-of days y fuel)
          :in-theory (enable fn-inj-year-of fn-inj-year-days)))))
(local
 (defthm fn-io-month-of-bound
 (and (natp (cdr (fn-inj-month-of doy m leap fuel)))
      (<= (cdr (fn-inj-month-of doy m leap fuel)) (nfix doy)))
 :hints (("Goal" :induct (fn-inj-month-of doy m leap fuel)
          :in-theory (enable fn-inj-month-of fn-inj-month-days)))))


(local
 (defthm fn-io-date-names
 (and (fn-bch-octetp (fn-inj-dow-c1 n))
      (fn-bch-octetp (fn-inj-dow-c2 n))
      (fn-bch-octetp (fn-inj-dow-c3 n))
      (fn-bch-octetp (fn-inj-month-c1 n))
      (fn-bch-octetp (fn-inj-month-c2 n))
      (fn-bch-octetp (fn-inj-month-c3 n)))
 :hints (("Goal" :in-theory (enable fn-bch-octetp fn-inj-dow-c1 fn-inj-dow-c2 fn-inj-dow-c3 fn-inj-month-c1 fn-inj-month-c2 fn-inj-month-c3)))))
(local
 (defthm fn-io-date-digits
 (and (implies (< (nfix n) 2080) (fn-bch-octetp (fn-inj-hi2 n)))
      (fn-bch-octetp (fn-inj-lo2 n))
      (implies (< (nfix n) 208000) (fn-bch-octetp (fn-inj-y-th n)))
      (fn-bch-octetp (fn-inj-y-hu n))
      (fn-bch-octetp (fn-inj-y-te n))
      (fn-bch-octetp (fn-inj-y-un n)))
 :hints (("Goal" :in-theory (enable fn-bch-octetp fn-inj-hi2 fn-inj-lo2 fn-inj-y-th fn-inj-y-hu fn-inj-y-te fn-inj-y-un fn-inj-r1 fn-inj-r2)))))
(local
 (defthm fn-io-date-render-octets
 (implies (and (< (nfix (fn-inj-instant-year inst)) 208000)
               (< (nfix (fn-inj-instant-day inst)) 2080)
               (< (nfix (fn-inj-instant-hour inst)) 2080)
               (< (nfix (fn-inj-instant-minute inst)) 2080)
               (< (nfix (fn-inj-instant-second inst)) 2080))
  (fn-bch-octetsp (fn-inj-date-octets inst)))
 :hints (("Goal" :in-theory (union-theories
  '(fn-inj-date-octets fn-bch-octetsp car-cons cdr-cons fn-io-date-names fn-io-date-digits
    (:executable-counterpart fn-bch-octetp))
  (theory 'minimal-theory))))))


(local
 (defthm fn-io-calendar-bounds
 (implies (< (nfix days) 146097)
  (let* ((ym (fn-inj-year-of days 2000 400))
         (md (fn-inj-month-of (cdr ym) 1 (fn-inj-leapp (car ym)) 12)))
   (and (natp (car ym)) (< (car ym) 208000)
        (natp (cdr md)) (< (+ 1 (cdr md)) 2080))))
 :hints (("Goal"
  :use ((:instance fn-io-year-of-bound (y 2000) (fuel 400))
        (:instance fn-io-month-of-bound
         (doy (cdr (fn-inj-year-of days 2000 400))) (m 1)
         (leap (fn-inj-leapp (car (fn-inj-year-of days 2000 400)))) (fuel 12)))
  :in-theory (disable fn-io-year-of-bound fn-io-month-of-bound)))))
(local
 (defthm fn-io-seconds-bounds
 (implies (and (natp sec) (< sec 86400))
  (and (natp (floor sec 3600)) (< (floor sec 3600) 2080)
       (natp (floor (mod sec 3600) 60)) (< (floor (mod sec 3600) 60) 2080)
       (natp (mod sec 60)) (< (mod sec 60) 2080)))))
(local
 (defthm fn-io-clock-seconds-bound
 (and (natp (floor (mod (nfix ms) 86400000) 1000))
      (< (floor (mod (nfix ms) 86400000) 1000) 86400))))


(local
 (defthm fn-io-date-octets
 (implies (< (nfix (floor (nfix ms) 86400000)) 146097)
  (fn-bch-octetsp (fn-inj-date-octets (fn-inj-instant-of ms))))
 :hints (("Goal"
  :use ((:instance fn-io-calendar-bounds (days (floor (nfix ms) 86400000)))
        (:instance fn-io-clock-seconds-bound)
        (:instance fn-io-seconds-bounds (sec (floor (mod (nfix ms) 86400000) 1000)))
        (:instance fn-io-date-render-octets (inst (fn-inj-instant-of ms))))
  :in-theory (union-theories
   '(fn-inj-instant-of fn-inj-instant-year fn-inj-instant-month fn-inj-instant-day fn-inj-instant-hour fn-inj-instant-minute fn-inj-instant-second fn-inj-instant-dow fn-inj-nth fn-inj-car fn-inj-cdr
     nfix natp zp car-cons cdr-cons (:type-prescription fn-inj-year-of) (:type-prescription fn-inj-month-of))
   (theory 'minimal-theory))))))


(local
 (defthm fn-io-append-octets
 (implies (and (fn-bch-octetsp x) (fn-bch-octetsp y))
  (and (fn-bch-octetsp (fn-inj-append x y))
       (fn-bch-octetsp (append x y))))
 :hints (("Goal" :in-theory (union-theories
  '(fn-bch-octetsp fn-inj-append binary-append car-cons cdr-cons)
  (theory 'minimal-theory))))))
(local
 (defthm fn-io-rev-append-octets
 (implies (and (fn-bch-octetsp x) (fn-bch-octetsp y))
  (fn-bch-octetsp (fn-inj-rev-append x y)))
 :hints (("Goal" :in-theory (union-theories
  '(fn-bch-octetsp fn-inj-rev-append car-cons cdr-cons)
  (theory 'minimal-theory))))))
(local
 (defthm fn-io-digits-rev-octets
 (fn-bch-octetsp (fn-inj-digits-rev n w))
 :hints (("Goal" :in-theory (e/d (fn-inj-digits-rev fn-bch-octetsp fn-bch-octetp)
                                (fn-io-octet-recognizers))))))
(local
 (defthm fn-io-digits-octets
 (fn-bch-octetsp (fn-inj-digits n w))
 :hints (("Goal" :in-theory (union-theories
  '(fn-inj-digits fn-io-digits-rev-octets fn-io-rev-append-octets
    (:executable-counterpart fn-bch-octetsp)) (theory 'minimal-theory))))))
(local
 (defthm fn-io-config-agent-octets
 (implies (fn-inj-configp cfg) (fn-bch-octetsp (fn-inj-config-agent cfg)))
 :hints (("Goal" :use ((:instance fn-io-octet-recognizers (x (fn-inj-config-agent cfg))))
          :in-theory (union-theories '(fn-inj-configp) (theory 'minimal-theory))))))
(local
 (defthm fn-io-generated-id-octets
 (implies (fn-inj-configp cfg)
  (fn-bch-octetsp (fn-inj-generated-message-id obs cfg)))
 :hints (("Goal" :in-theory (union-theories
  '(fn-inj-generated-message-id fn-io-config-agent-octets fn-io-append-octets
    fn-io-digits-octets (:executable-counterpart fn-bch-octetsp))
  (theory 'minimal-theory))))))
(local
 (defthm fn-io-prefix-block-octets
 (implies (and (fn-bch-octetsp date) (fn-bch-octetsp agent)
               (or (not generate-id) (fn-bch-octetsp msgid)))
  (and (fn-bch-octetsp (fn-inj-prefix date msgid agent generate-id generate-date))
       (fn-bch-octetsp (fn-inj-block date msgid agent generate-id generate-date))))
 :hints (("Goal" :in-theory (union-theories
  '(fn-inj-prefix fn-inj-block fn-inj-path-line fn-inj-injection-date-line
    fn-inj-message-id-line fn-inj-date-line fn-inj-injection-info-line fn-io-append-octets
    (:executable-counterpart fn-bch-octetsp))
  (theory 'minimal-theory))))))


(local
 (defthm fn-io-octets-true-list-fix
 (implies (fn-bch-octetsp x) (equal (true-list-fix x) x))
 :hints (("Goal" :in-theory (union-theories '(fn-bch-octetsp true-list-fix car-cons cdr-cons)
                          (theory 'minimal-theory))))))
(local
 (defthm fn-io-take-drop-octets
 (implies (fn-bch-octetsp x)
  (and (fn-bch-octetsp (fn-inj-take-n n x))
       (fn-bch-octetsp (fn-inj-drop-n n x))))
 :hints (("Goal" :induct (fn-inj-drop-n n x)
          :in-theory (union-theories
            '(fn-bch-octetsp fn-inj-take-n fn-inj-drop-n car-cons cdr-cons)
            (theory 'minimal-theory))))))
(local
 (defthm fn-io-splice-octets
 (implies (and (fn-bch-octetsp source) (fn-bch-octetsp agent))
  (fn-bch-octetsp (fn-inj-splice source k (fn-inj-path-insert agent))))
 :hints (("Goal" :in-theory (union-theories
  '(fn-inj-splice fn-inj-path-insert fn-io-take-drop-octets fn-io-octets-true-list-fix
    fn-io-append-octets (:executable-counterpart fn-bch-octetsp))
  (theory 'minimal-theory))))))
(defthm fn-io-parsed-source-octets
 (implies (fn-article-result-okp (fn-article-parse source))
  (fn-bch-octetsp source))
 :hints (("Goal" :use ((:instance fn-io-octet-recognizers (x source)))
          :in-theory (union-theories
   '(fn-article-parse fn-article-parse-under fn-article-result-okp fn-article-error
     car-cons cdr-cons)
   (theory 'minimal-theory)))))
(local
 (defthm fn-io-clock-in-range
 (implies (and (fn-clock-observationp obs)
               (< (floor (fn-clock-wall obs) 86400000) 146097))
  (< (nfix (floor (nfix (fn-clock-wall obs)) 86400000)) 146097))
 :hints (("Goal" :in-theory (enable fn-clock-observationp fn-clock-timep)))))
(defthm fn-inj-decision-produces-octets
 (fn-bch-octetsp (fn-inj-decision-octets (fn-inj-decide source cfg obs)))
 :hints (("Goal"
  :use ((:instance fn-io-parsed-source-octets)
        (:instance fn-io-config-agent-octets)
        (:instance fn-io-generated-id-octets)
        (:instance fn-io-date-octets (ms (fn-clock-wall obs)))
        (:instance fn-io-clock-in-range))
  :in-theory (union-theories
   '(fn-inj-decide fn-inj-refuse fn-inj-make-decision fn-inj-decision-octets
     fn-inj-nth fn-inj-car fn-inj-cdr car-cons cdr-cons nfix zp
     fn-io-parsed-source-octets fn-io-clock-in-range fn-io-date-octets
     fn-io-config-agent-octets fn-io-generated-id-octets fn-io-prefix-block-octets
     fn-io-splice-octets fn-io-append-octets (:executable-counterpart fn-bch-octetsp))
   (theory 'minimal-theory)))))

