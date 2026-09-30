; Teeth for PRF-212 (books/tls-reload.lisp).  The keystone
; fn-tlsr-decide-accepts-exactly-loaded-matching-current-covering-material:
; a reachable witness asserting every conjunct and the acceptance, and per
; conjunct a witness where that conjunct alone fails and the decision refuses
; by its name, plus a `must-fail' of the acceptance with that conjunct
; omitted (AGENTS.md, "Teeth ship with each keystone").  The certificate
; facts are an EC P-256 self-signed certificate's, made by `openssl req
; -x509 ... -addext subjectAltName=DNS:fn.example.invalid,
; DNS:alt.example.invalid,IP:127.0.0.1': its UTCTime validity and its
; subjectAltName octets as X509_EXTENSION_get_data hands them over (the IP
; entry, tag 0x87, is skipped).
(in-package "ACL2")
(include-book "../../books/tls-reload")
(include-book "must-fail-checked")

(defconst *tlst-not-before* (fn-record-string-octets "260926222343Z"))
(defconst *tlst-not-after* (fn-record-string-octets "261225222343Z"))
(defconst *tlst-san*
  '(#x30 #x2f
    #x82 #x12 #x66 #x6e #x2e #x65 #x78 #x61 #x6d #x70 #x6c #x65 #x2e #x69
    #x6e #x76 #x61 #x6c #x69 #x64
    #x82 #x13 #x61 #x6c #x74 #x2e #x65 #x78 #x61 #x6d #x70 #x6c #x65 #x2e
    #x69 #x6e #x76 #x61 #x6c #x69 #x64
    #x87 #x04 #x7f #x00 #x00 #x01))
(defconst *tlst-fn* (fn-record-string-octets "fn.example.invalid"))
(defconst *tlst-alt* (fn-record-string-octets "alt.example.invalid"))
(defconst *tlst-other* (fn-record-string-octets "other.example.invalid"))
; 2026-09-26T22:23:43Z and 2026-12-25T22:23:43Z (calendar.timegm).
(defconst *tlst-nb-seconds* 1790461423)
(defconst *tlst-na-seconds* 1798237423)
(defconst *tlst-now* (+ *tlst-nb-seconds* 3600))

; The parsers, on the certificate's own octets.
(assert-event (equal (fn-tlsr-time-fields *tlst-not-before*) '(2026 9 26 22 23 43)))
(assert-event (equal (fn-tlsr-seconds (fn-tlsr-time-fields *tlst-not-before*))
                     *tlst-nb-seconds*))
(assert-event (equal (fn-tlsr-seconds (fn-tlsr-time-fields *tlst-not-after*))
                     *tlst-na-seconds*))
(assert-event (equal (fn-tlsr-seconds (fn-tlsr-time-fields
                                       (fn-record-string-octets "20500101000000Z")))
                     2524608000))
(assert-event (equal (fn-tlsr-seconds (fn-tlsr-time-fields
                                       (fn-record-string-octets "991231235959Z")))
                     946684799))
(assert-event (null (fn-tlsr-time-fields (fn-record-string-octets "260230000000Z"))))
(assert-event (null (fn-tlsr-time-fields (fn-record-string-octets "2609262223Z"))))
(assert-event (equal (fn-tlsr-san-names *tlst-san*) (list *tlst-fn* *tlst-alt*)))
(assert-event (equal (fn-tlsr-san-names nil) nil))
(assert-event (equal (fn-tlsr-san-names (butlast *tlst-san* 1)) :malformed))
(assert-event (equal (fn-tlsr-san-names '(#x30 #x02 #x82 #x05)) :malformed))

(defmacro tlst-facts (&key (chain 't) (key 't) (match 't)
                           (nb '*tlst-not-before*) (na '*tlst-not-after*)
                           (san '*tlst-san*) (now '*tlst-now*))
  `(fn-tlsr-facts ,chain ,key ,match ,nb ,na ,san ,now))

; A served context naming only fn.example.invalid (a renewal adds alt).
(defconst *tlst-served*
  (fn-tlsr-facts t t t *tlst-not-before* *tlst-not-after*
                 '(#x30 #x14 #x82 #x12 #x66 #x6e #x2e #x65 #x78 #x61 #x6d #x70
                   #x6c #x65 #x2e #x69 #x6e #x76 #x61 #x6c #x69 #x64)
                 0))

; Positive witness: every conjunct holds, and the decision accepts with the
; parsed names and notAfter.
(assert-event
 (let ((f (tlst-facts)))
   (and (fn-tlsr-chain-loadedp f) (fn-tlsr-key-loadedp f) (fn-tlsr-key-matchesp f)
        (fn-tlsr-currentp f)
        (not (equal (fn-tlsr-names f) :malformed))
        (subsetp-equal (fn-tlsr-served-names *tlst-served*) (fn-tlsr-names f))
        (equal (fn-tlsr-decide f *tlst-served*)
               (list :accept (list *tlst-fn* *tlst-alt*) '(2026 12 25 22 23 43))))))

; Hypothesis removal: each conjunct alone fails, every other holds, and the
; decision refuses by that conjunct's name.
(defmacro tlst-refuses (facts served reason)
  `(assert-event (equal (fn-tlsr-decide ,facts ,served) (list :refuse ,reason))))
(assert-event (fn-tlsr-key-loadedp (tlst-facts :chain nil)))
(tlst-refuses (tlst-facts :chain nil) *tlst-served* :chain-unreadable)
(tlst-refuses (tlst-facts :key nil) *tlst-served* :key-unreadable)
(tlst-refuses (tlst-facts :match nil) *tlst-served* :key-mismatch)
(assert-event (and (fn-tlsr-chain-loadedp (tlst-facts :match nil))
                   (fn-tlsr-key-loadedp (tlst-facts :match nil))
                   (fn-tlsr-currentp (tlst-facts :match nil))))
(tlst-refuses (tlst-facts :now (- *tlst-nb-seconds* 1)) *tlst-served* :not-yet-valid)
(tlst-refuses (tlst-facts :now *tlst-na-seconds*) *tlst-served* :expired)
(tlst-refuses (tlst-facts :na (fn-record-string-octets "261325222343Z")) *tlst-served*
              :validity-malformed)
(tlst-refuses (tlst-facts :now "soon") *tlst-served* :clock-unusable)
(tlst-refuses (tlst-facts :san (butlast *tlst-san* 1)) *tlst-served* :names-malformed)
; The window's ends: notBefore itself is inside, the second before notAfter
; is inside.
(assert-event (fn-tlsr-acceptp (fn-tlsr-decide (tlst-facts :now *tlst-nb-seconds*)
                                               *tlst-served*)))
(assert-event (fn-tlsr-acceptp (fn-tlsr-decide (tlst-facts :now (- *tlst-na-seconds* 1))
                                               *tlst-served*)))
; Covering: served names the new material drops refuse; a served context
; without names (CN only) is covered by anything, and no names is readable.
(assert-event (equal (fn-tlsr-served-names *tlst-served*) (list *tlst-fn*)))
(tlst-refuses (tlst-facts) (tlst-facts :san (append '(#x30 #x17 #x82 #x15) *tlst-other*))
              :names-dropped)
(assert-event (fn-tlsr-acceptp (fn-tlsr-decide (tlst-facts :san nil)
                                               (tlst-facts :san nil))))
(tlst-refuses (tlst-facts :san nil) *tlst-served* :names-dropped)
(assert-event (fn-tlsr-acceptp (fn-tlsr-decide (tlst-facts) nil)))

; Each conjunct is needed: acceptance without it is not a theorem.
(defmacro tlst-without (&rest conjuncts)
  `(must-fail-checked
    (with-prover-step-limit
     100000
     (defthm tlst-accept-without
       (implies (and ,@conjuncts)
                (fn-tlsr-acceptp (fn-tlsr-decide facts served)))
       :rule-classes nil))))
(tlst-without (fn-tlsr-key-loadedp facts) (fn-tlsr-key-matchesp facts)
              (fn-tlsr-currentp facts)
              (not (equal (fn-tlsr-names facts) :malformed))
              (subsetp-equal (fn-tlsr-served-names served) (fn-tlsr-names facts)))
(tlst-without (fn-tlsr-chain-loadedp facts) (fn-tlsr-key-matchesp facts)
              (fn-tlsr-currentp facts)
              (not (equal (fn-tlsr-names facts) :malformed))
              (subsetp-equal (fn-tlsr-served-names served) (fn-tlsr-names facts)))
(tlst-without (fn-tlsr-chain-loadedp facts) (fn-tlsr-key-loadedp facts)
              (fn-tlsr-currentp facts)
              (not (equal (fn-tlsr-names facts) :malformed))
              (subsetp-equal (fn-tlsr-served-names served) (fn-tlsr-names facts)))
(tlst-without (fn-tlsr-chain-loadedp facts) (fn-tlsr-key-loadedp facts)
              (fn-tlsr-key-matchesp facts)
              (not (equal (fn-tlsr-names facts) :malformed))
              (subsetp-equal (fn-tlsr-served-names served) (fn-tlsr-names facts)))
(tlst-without (fn-tlsr-chain-loadedp facts) (fn-tlsr-key-loadedp facts)
              (fn-tlsr-key-matchesp facts) (fn-tlsr-currentp facts)
              (subsetp-equal (fn-tlsr-served-names served) (fn-tlsr-names facts)))
(tlst-without (fn-tlsr-chain-loadedp facts) (fn-tlsr-key-loadedp facts)
              (fn-tlsr-key-matchesp facts) (fn-tlsr-currentp facts)
              (not (equal (fn-tlsr-names facts) :malformed)))

; The served line and the frames.
(assert-event
 (equal (fn-tlsr-reply-line (tlst-facts))
        (fn-record-string-octets
         "tls names=fn.example.invalid,alt.example.invalid not-after=2026-12-25T22:23:43Z")))
(assert-event (equal (fn-tlsr-reply-line (tlst-facts :san nil))
                     (fn-record-string-octets "tls names=none not-after=2026-12-25T22:23:43Z")))
(assert-event (equal (fn-tlsr-reply-line nil) (fn-record-string-octets "tls none")))
(assert-event (equal (fn-tlsr-request-decode (fn-tlsr-request-encode :reload)) :reload))
(assert-event (equal (fn-tlsr-request-decode (fn-tlsr-request-encode :status)) :status))
(assert-event (equal (fn-tlsr-request-encode :restart) :bad))
(assert-event (null (fn-tlsr-request-decode (fn-native-control-reply-encode :accepted))))
(assert-event
 (equal (fn-tlsr-reply-read (fn-tlsr-reply-encode :refused :key-mismatch
                                                  (fn-tlsr-reply-line (tlst-facts))))
        (list :refused (fn-record-string-octets "key-mismatch")
              (fn-tlsr-reply-line (tlst-facts)))))
(assert-event
 (equal (fn-tlsr-reply-read (fn-native-control-reply-encode :refused))
        (list :refused (fn-record-string-octets "owner-lacks-tls-reload") nil)))
(assert-event
 (equal (fn-tlsr-status-client-line
         (fn-tlsr-reply-read (fn-native-control-reply-encode :refused)))
        (fn-record-string-octets "tls unknown owner-lacks-tls-reload")))
(assert-event (equal (fn-tlsr-status-client-line :bad)
                     (fn-record-string-octets "tls unknown no-reply")))
(assert-event
 (equal (fn-tlsr-log-line (list :refuse :key-mismatch) (tlst-facts :match nil))
        (fn-record-string-octets
         "tls reload refused key-mismatch: the served certificate is unchanged")))

; -----------------------------------------------------------------------------
; PRF-387 (PKT-606): the start's decision.
;
; fn-tlsr-start-decide-accepts-exactly-loaded-matching-current-material:
; a positive witness asserting every conjunct and the acceptance, per
; conjunct a witness where it alone fails and the start refuses by its name,
; and a must-fail of the acceptance with each conjunct omitted.

(assert-event
 (let ((f (tlst-facts)))
   (and (fn-tlsr-chain-loadedp f) (fn-tlsr-key-loadedp f) (fn-tlsr-key-matchesp f)
        (fn-tlsr-currentp f)
        (not (equal (fn-tlsr-names f) :malformed))
        (fn-tlsr-acceptp (fn-tlsr-start-decide f))
        (equal (fn-tlsr-start-decide f)
               (list :accept (list *tlst-fn* *tlst-alt*) '(2026 12 25 22 23 43))))))

(defmacro tlst-start-refuses (facts reason)
  `(assert-event (equal (fn-tlsr-start-decide ,facts) (list :refuse ,reason))))
(tlst-start-refuses (tlst-facts :chain nil) :chain-unreadable)
(tlst-start-refuses (tlst-facts :key nil) :key-unreadable)
(tlst-start-refuses (tlst-facts :match nil) :key-mismatch)
(tlst-start-refuses (tlst-facts :now (- *tlst-nb-seconds* 1)) :not-yet-valid)
(tlst-start-refuses (tlst-facts :now *tlst-na-seconds*) :expired)
(tlst-start-refuses (tlst-facts :na (fn-record-string-octets "261325222343Z"))
                    :validity-malformed)
(tlst-start-refuses (tlst-facts :now "soon") :clock-unusable)
(tlst-start-refuses (tlst-facts :san (butlast *tlst-san* 1)) :names-malformed)
; In each, every other conjunct holds (the mismatch, the expiry and the
; unreadable names, the three a start used to take or leave to OpenSSL).
(assert-event (let ((f (tlst-facts :now *tlst-na-seconds*)))
                (and (fn-tlsr-chain-loadedp f) (fn-tlsr-key-loadedp f)
                     (fn-tlsr-key-matchesp f)
                     (not (equal (fn-tlsr-names f) :malformed))
                     (not (fn-tlsr-currentp f)))))
(assert-event (let ((f (tlst-facts :san (butlast *tlst-san* 1))))
                (and (fn-tlsr-chain-loadedp f) (fn-tlsr-key-loadedp f)
                     (fn-tlsr-key-matchesp f) (fn-tlsr-currentp f)
                     (equal (fn-tlsr-names f) :malformed))))
; A CN-only pair (no subjectAltName) starts: no names is readable.
(assert-event (fn-tlsr-acceptp (fn-tlsr-start-decide (tlst-facts :san nil))))

(defmacro tlst-start-without (&rest conjuncts)
  `(must-fail-checked
    (with-prover-step-limit
     100000
     (defthm tlst-start-accept-without
       (implies (and ,@conjuncts)
                (fn-tlsr-acceptp (fn-tlsr-start-decide facts)))
       :rule-classes nil))))
(tlst-start-without (fn-tlsr-key-loadedp facts) (fn-tlsr-key-matchesp facts)
                    (fn-tlsr-currentp facts)
                    (not (equal (fn-tlsr-names facts) :malformed)))
(tlst-start-without (fn-tlsr-chain-loadedp facts) (fn-tlsr-key-matchesp facts)
                    (fn-tlsr-currentp facts)
                    (not (equal (fn-tlsr-names facts) :malformed)))
(tlst-start-without (fn-tlsr-chain-loadedp facts) (fn-tlsr-key-loadedp facts)
                    (fn-tlsr-currentp facts)
                    (not (equal (fn-tlsr-names facts) :malformed)))
(tlst-start-without (fn-tlsr-chain-loadedp facts) (fn-tlsr-key-loadedp facts)
                    (fn-tlsr-key-matchesp facts)
                    (not (equal (fn-tlsr-names facts) :malformed)))
(tlst-start-without (fn-tlsr-chain-loadedp facts) (fn-tlsr-key-loadedp facts)
                    (fn-tlsr-key-matchesp facts) (fn-tlsr-currentp facts))

; fn-tlsr-decide-is-the-start-decision-unless-names-dropped.  Positive: a
; reload's acceptance and a reload's key-mismatch are the start's decisions.
(assert-event
 (and (not (equal (fn-tlsr-decide (tlst-facts) *tlst-served*)
                  (list :refuse :names-dropped)))
      (equal (fn-tlsr-decide (tlst-facts) *tlst-served*)
             (fn-tlsr-start-decide (tlst-facts)))
      (equal (fn-tlsr-decide (tlst-facts :match nil) *tlst-served*)
             (fn-tlsr-start-decide (tlst-facts :match nil)))
      (equal (fn-tlsr-start-decide (tlst-facts :match nil))
             (list :refuse :key-mismatch))))
; Hypothesis removal: material that drops a served name is refused by the
; reload and taken by the start, so the equation needs its hypothesis.
(assert-event
 (let ((f (tlst-facts :san (append '(#x30 #x17 #x82 #x15) *tlst-other*))))
   (and (equal (fn-tlsr-decide f *tlst-served*) (list :refuse :names-dropped))
        (fn-tlsr-acceptp (fn-tlsr-start-decide f))
        (not (equal (fn-tlsr-decide f *tlst-served*) (fn-tlsr-start-decide f))))))
(must-fail-checked
 (with-prover-step-limit
  100000
  (defthm tlst-start-equation-without-its-hypothesis
    (equal (fn-tlsr-decide facts served) (fn-tlsr-start-decide facts))
    :rule-classes nil)))

; The operator's line for a refused start.
(assert-event
 (equal (fn-tlsr-start-refusal-line (fn-tlsr-start-decide (tlst-facts :match nil)))
        (fn-record-string-octets "tls key-mismatch")))
(assert-event
 (equal (fn-tlsr-start-refusal-line (fn-tlsr-start-decide
                                     (tlst-facts :now *tlst-na-seconds*)))
        (fn-record-string-octets "tls expired")))

; KEYSTONE fn-tlsr-decide-carries-the-facts-or-a-named-refusal (PRF-212; no
; hypothesis), by name, one witness per arm of its `if': an acceptance is
; exactly (:accept NAMES NOT-AFTER) of the new facts, and a refusal is
; (:refuse R) with R among *fn-tlsr-refusals*.
(assert-event
 (let ((d (fn-tlsr-decide (tlst-facts) *tlst-served*)))
   (and (fn-tlsr-acceptp d)
        (equal d (list :accept (fn-tlsr-names (tlst-facts))
                       (fn-tlsr-not-after (tlst-facts)))))))
(assert-event
 (let ((d (fn-tlsr-decide (tlst-facts :key nil) *tlst-served*)))
   (and (not (fn-tlsr-acceptp d))
        (equal (car d) :refuse)
        (member-equal (cadr d) *fn-tlsr-refusals*))))
