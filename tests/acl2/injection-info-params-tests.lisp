; Teeth for the Injection-Info parameters (PKT-597):
; books/injection-info-params-invariants.lisp (the keystones),
; books/injection-info-params.lisp (fn-ipp-injected-octets-without-parameters),
; books/injection-info-policy.lisp (the complaints address, the operator's
; account hash), the admin arm and the operator verb (PKT-786:
; books/native-operator.lisp fn-nop-account-hash hashes LOGIN's account).
(in-package "ACL2")
(include-book "../../books/injection-info-params-invariants")
(include-book "../../books/native-operator")
(include-book "../../books/crypto-attach")
(include-book "must-fail-checked")

(defun ipt-codes (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (consp cs) (cons (char-code (car cs)) (ipt-codes (cdr cs))) nil))
(defmacro ipt-o (s) `(ipt-codes (coerce ,s 'list)))

(defun ipt-infixp (x y)
  (declare (xargs :guard t :measure (acl2-count y)))
  (or (not (equal (fn-inj-strip x y) :no))
      (and (consp y) (ipt-infixp x (cdr y)))))

; The injection fixture of tests/acl2/injection-tests.lisp.
(defconst *ipt-good* (ipt-o "From: poster@example.invalid
Subject: hello
Newsgroups: fn.letters

Hello, news.
"))
(defun ipt-crlf (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (equal (car x) 10) (list* 13 10 (ipt-crlf (cdr x))) (cons (car x) (ipt-crlf (cdr x))))
    nil))
(defconst *ipt-source* (ipt-crlf *ipt-good*))
(defconst *ipt-agent* (ipt-o "fn.example.invalid"))
(defconst *ipt-inj-cfg* (fn-inj-make-config t *ipt-agent* (list (ipt-o "fn.letters")) 32768))
(defconst *ipt-closed* (fn-inj-make-config nil *ipt-agent* (list (ipt-o "fn.letters")) 32768))
(defconst *ipt-obs* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *ipt-d* (fn-inj-decide *ipt-source* *ipt-inj-cfg* *ipt-obs*))
(defconst *ipt-refused* (fn-inj-decide *ipt-source* *ipt-closed* *ipt-obs*))

; A one-epoch key ring (books/node-secret.lisp): epoch 1, identity
; "local", a 32-octet root.
(defconst *ipt-secret* (list (fn-ns-make-entry 1 (ipt-o "local")
                                               (make-list 32 :initial-element 7))))
(assert-event (fn-ns-ringp *ipt-secret*))
(defconst *ipt-login* (ipt-o "alice"))
(defconst *ipt-stamp* (fn-clock-observation 5 1700000000 2 t))
(defconst *ipt-cfg0* (fn-cfg-initial))
(defconst *ipt-cfg1*
  (fn-cfg-make 1 (fn-cfg-apply-delta (fn-cfg-empty-value) 1 *ipt-stamp*
                                     (fn-cfg-set-policy "complaints-to"
                                                        (ipt-o "abuse@example.org")))))

(assert-event (fn-inj-injectedp *ipt-d*))
(assert-event (not (fn-inj-injectedp *ipt-refused*)))
(assert-event (equal (fn-ipp-complaints *ipt-cfg1*) (ipt-o "abuse@example.org")))
(assert-event (equal (fn-ipp-complaints *ipt-cfg0*) nil))

(defconst *ipt-stored* (fn-ipp-injected-octets *ipt-d* *ipt-secret* *ipt-login* *ipt-cfg1*))
(defconst *ipt-hex* (fn-pa-account-value *ipt-secret* *ipt-login*))

; -----------------------------------------------------------------------------
; fn-ipp-injected-octets-carry-the-parameters: positive witness.  The
; antecedent (an injection), both conclusions, and what they mean on the
; wire: one Injection-Info whose value is AGENT; posting-account="HEX";
; mail-complaints-to="abuse@example.org", and no octet run of the login.
(assert-event
 (let ((params (fn-ipp-params *ipt-secret* *ipt-login* (fn-ipp-complaints *ipt-cfg1*))))
   (and (fn-inj-injectedp *ipt-d*)
        (not (fn-inj-supplies-pathp *ipt-source*))
        (equal *ipt-stored*
               (append (fn-ipp-prefix-with
                        (fn-ipp-date *ipt-obs*) (fn-inj-decision-msgid *ipt-d*)
                        *ipt-agent* (fn-ipp-gid *ipt-source*) (fn-ipp-gdate *ipt-source*)
                        params)
                       *ipt-source*))
        (equal (fn-inj-source-of *ipt-stored* *ipt-agent* (fn-inj-decision-msgid *ipt-d*))
               (cons t *ipt-source*)))))
(assert-event
 (let* ((a (fn-article-result-article (fn-article-parse *ipt-stored*)))
        (fields (fn-article-get-headers a *fn-af-injection-info-name*)))
   (and (fn-article-result-okp (fn-article-parse *ipt-stored*))
        (equal (len fields) 1)
        (equal (fn-article-field-unfolded-value (car fields))
               (cons 32 (append *ipt-agent* (ipt-o "; posting-account=\"") *ipt-hex*
                                (ipt-o "\"; mail-complaints-to=\"abuse@example.org\"")))))))
(assert-event (not (ipt-infixp *ipt-login* *ipt-stored*)))
; The value of an account is the value an article posted under it carries.
(assert-event (equal (fn-ipp-account-hash *ipt-secret* *ipt-login*) *ipt-hex*))
; Omitted hypothesis (the only one, an injection): a refused decision has no
; octets, and the conclusion fails.
(assert-event
 (and (not (fn-inj-injectedp *ipt-refused*))
      (not (equal (fn-ipp-injected-octets *ipt-refused* *ipt-secret* *ipt-login* *ipt-cfg1*)
                  (append (fn-ipp-prefix-with
                           (fn-ipp-date *ipt-obs*) (fn-inj-decision-msgid *ipt-refused*)
                           *ipt-agent* (fn-ipp-gid *ipt-source*) (fn-ipp-gdate *ipt-source*)
                           (fn-ipp-params *ipt-secret* *ipt-login*
                                          (fn-ipp-complaints *ipt-cfg1*)))
                          *ipt-source*)))))
(must-fail-checked
 (defthm ipt-carry-without-an-injection
   (equal (fn-ipp-injected-octets (fn-inj-decide source config obs) secret login cfg)
          (append (fn-ipp-prefix-with
                   (fn-ipp-date obs) (fn-inj-decision-msgid (fn-inj-decide source config obs))
                   (fn-inj-config-agent config) (fn-ipp-gid source) (fn-ipp-gdate source)
                   (fn-ipp-params secret login (fn-ipp-complaints cfg)))
                  source))
   :hints (("Goal" :in-theory (theory 'minimal-theory)))))

; fn-ipp-with-params-of-an-injection: the same antecedent; its removal is
; the witness above with PARAMS the parameters.
(must-fail-checked
 (defthm ipt-with-params-without-an-injection
   (equal (fn-ipp-with-params (fn-inj-decision-octets (fn-inj-decide source config obs))
                              (fn-inj-decision-msgid (fn-inj-decide source config obs))
                              params)
          (append (fn-ipp-prefix-with
                   (fn-ipp-date obs) (fn-inj-decision-msgid (fn-inj-decide source config obs))
                   (fn-inj-config-agent config) (fn-ipp-gid source) (fn-ipp-gdate source)
                   params)
                  source))
   :hints (("Goal" :in-theory (theory 'minimal-theory)))))

; fn-ipp-with-params-keeps-the-source: an injection and a parameter run.
; Positive: "; x=1".  Omitted run hypothesis: a "parameter" with a CR LF
; inside (a second header line smuggled into the Injection-Info line): the
; injection holds, the run does not, and the source is not given back.
(defconst *ipt-run* (ipt-o "; x=1"))
(defconst *ipt-not-a-run* (list 59 32 13 10 88))
(assert-event
 (and (fn-inj-injectedp *ipt-d*) (fn-ipp-params-okp *ipt-run*)
      (equal (fn-inj-source-of (fn-ipp-with-params (fn-inj-decision-octets *ipt-d*)
                                                   (fn-inj-decision-msgid *ipt-d*) *ipt-run*)
                               *ipt-agent* (fn-inj-decision-msgid *ipt-d*))
             (cons t *ipt-source*))))
(assert-event
 (and (fn-inj-injectedp *ipt-d*) (not (fn-ipp-params-okp *ipt-not-a-run*))
      (not (equal (fn-inj-source-of (fn-ipp-with-params (fn-inj-decision-octets *ipt-d*)
                                                        (fn-inj-decision-msgid *ipt-d*)
                                                        *ipt-not-a-run*)
                                    *ipt-agent* (fn-inj-decision-msgid *ipt-d*))
                  (cons t *ipt-source*)))))
(must-fail-checked
 (defthm ipt-keeps-the-source-without-a-run
   (implies (fn-inj-injectedp (fn-inj-decide source config obs))
            (equal (fn-inj-source-of
                    (fn-ipp-with-params
                     (fn-inj-decision-octets (fn-inj-decide source config obs))
                     (fn-inj-decision-msgid (fn-inj-decide source config obs))
                     params)
                    (fn-inj-config-agent config)
                    (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                   (cons t source)))
   :hints (("Goal" :in-theory (theory 'minimal-theory)))))
(must-fail-checked
 (defthm ipt-keeps-the-source-without-an-injection
   (implies (fn-ipp-params-okp params)
            (equal (fn-inj-source-of
                    (fn-ipp-with-params
                     (fn-inj-decision-octets (fn-inj-decide source config obs))
                     (fn-inj-decision-msgid (fn-inj-decide source config obs))
                     params)
                    (fn-inj-config-agent config)
                    (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                   (cons t source)))
   :hints (("Goal" :in-theory (theory 'minimal-theory)))))

; fn-ipp-params-of-a-login / -without-a-login / fn-ipp-a-login-has-parameters.
(assert-event
 (and (fn-ipp-accountp *ipt-secret* *ipt-login*)
      (equal (fn-ipp-params *ipt-secret* *ipt-login* nil)
             (append (ipt-o "; posting-account=\"") *ipt-hex* (ipt-o "\"")))))
; No secret installed: no posting-account, whatever the login.
(assert-event
 (and (not (fn-ipp-accountp nil *ipt-login*))
      (equal (fn-ipp-params nil *ipt-login* nil) nil)
      (not (consp (fn-ipp-params nil *ipt-login* nil)))))
; No login: only the complaints address.
(assert-event
 (and (not (fn-ipp-accountp *ipt-secret* nil))
      (equal (fn-ipp-params *ipt-secret* nil (ipt-o "abuse@example.org"))
             (ipt-o "; mail-complaints-to=\"abuse@example.org\""))))
(must-fail-checked
 (defthm ipt-params-of-anyone
   (equal (fn-ipp-params secret login addr)
          (append *fn-ipp-account-open*
                  (fn-pa-account-value secret (fn-ipp-octets login))
                  *fn-ipp-quote*
                  (if (consp addr) (fn-ipp-complaints-param addr) nil)))
   :hints (("Goal" :in-theory (theory 'minimal-theory)))))
(must-fail-checked
 (defthm ipt-params-never-an-account
   (equal (fn-ipp-params secret login addr)
          (if (consp addr) (fn-ipp-complaints-param addr) nil))
   :hints (("Goal" :in-theory (theory 'minimal-theory)))))
(must-fail-checked
 (defthm ipt-everyone-has-parameters
   (consp (fn-ipp-params secret login addr))
   :hints (("Goal" :in-theory (theory 'minimal-theory)))))

; fn-ipp-params-are-a-parameter-run: without parameters there is no run.
(assert-event
 (and (not (consp (fn-ipp-params nil nil (fn-ipp-complaints *ipt-cfg0*))))
      (not (fn-ipp-params-okp (fn-ipp-params nil nil (fn-ipp-complaints *ipt-cfg0*))))))
(assert-event
 (fn-ipp-params-okp (fn-ipp-params *ipt-secret* *ipt-login* (fn-ipp-complaints *ipt-cfg1*))))
(must-fail-checked
 (defthm ipt-params-always-a-run
   (fn-ipp-params-okp (fn-ipp-params secret login (fn-ipp-complaints cfg)))
   :hints (("Goal" :in-theory (theory 'minimal-theory)))))

; fn-ipp-injected-octets-without-parameters: each hypothesis matters.
(assert-event
 (equal (fn-ipp-injected-octets *ipt-d* *ipt-secret* nil *ipt-cfg0*)
        (fn-inj-decision-octets *ipt-d*)))
(assert-event
 (and (fn-ipp-accountp *ipt-secret* *ipt-login*) (not (fn-ipp-complaints *ipt-cfg0*))
      (not (equal (fn-ipp-injected-octets *ipt-d* *ipt-secret* *ipt-login* *ipt-cfg0*)
                  (fn-inj-decision-octets *ipt-d*)))))
(assert-event
 (and (not (fn-ipp-accountp *ipt-secret* nil)) (fn-ipp-complaints *ipt-cfg1*)
      (not (equal (fn-ipp-injected-octets *ipt-d* *ipt-secret* nil *ipt-cfg1*)
                  (fn-inj-decision-octets *ipt-d*)))))
(must-fail-checked
 (defthm ipt-without-parameters-under-a-login
   (implies (not (fn-ipp-complaints cfg))
            (equal (fn-ipp-injected-octets d secret login cfg)
                   (fn-inj-decision-octets d)))
   :hints (("Goal" :in-theory (theory 'minimal-theory)))))
(must-fail-checked
 (defthm ipt-without-parameters-with-an-address
   (implies (not (fn-ipp-accountp secret login))
            (equal (fn-ipp-injected-octets d secret login cfg)
                   (fn-inj-decision-octets d)))
   :hints (("Goal" :in-theory (theory 'minimal-theory)))))

; The complaints address: an addr-spec has no DQUOTE, backslash, ";", CR,
; LF; a string with a DQUOTE is no addr-spec (so it never reaches the
; header), and the admin plan refuses it.
(assert-event (fn-ipp-addr-specp (ipt-o "abuse@example.org")))
(assert-event (not (fn-ipp-addr-specp (ipt-o "a\"b@example.org"))))
(assert-event (not (fn-ipp-addr-specp (ipt-o "abuse"))))
(must-fail-checked
 (defthm ipt-any-text-is-quote-free
   (not (member-equal 34 x))
   :hints (("Goal" :in-theory (theory 'minimal-theory)))))

(defun ipt-argv (words)
  (if (consp words)
      (cons (fn-record-string-octets (car words)) (ipt-argv (cdr words)))
    nil))
(assert-event
 (let ((plan (fn-native-admin-plan (ipt-argv '("policy" "set" "complaints-to"
                                               "abuse@example.org")))))
   (and (equal (fn-native-admin-result-status plan) :accepted)
        (equal (fn-native-admin-result-kind plan) :set-policy))))
(assert-event
 (not (equal (fn-native-admin-result-status
              (fn-native-admin-plan (ipt-argv '("policy" "set" "complaints-to"
                                                "not an address"))))
             :accepted)))

; The operator verb: `account hash LOGIN' plans (:account-hash LOGIN) and
; is dispatched to its own action, never to the admin executor.
(assert-event
 (let ((r (fn-nop-parse-account '("hash" "alice") nil nil)))
   (and (equal (fn-native-operator-result-status r) :accepted)
        (equal (fn-native-operator-result-account-hash-login r) "alice"))))
(assert-event
 (not (equal (fn-native-operator-result-status
              (fn-nop-parse-account '("hash") nil nil))
             :accepted)))

; D25 (gpt-6 wave-5 review §3): generated Injection-Info is node metadata,
; not authored source.  The same source with a supplied Message-ID, injected
; at two clock readings and stored under two logins' parameters, is one
; article for the Store's duplicate test (books/poster-bytes.lisp
; fn-pb-same-articlep, which the host's buffer twin equals): a same-source
; retry is a duplicate whatever the new header says.
(defconst *ipt-withid* (ipt-crlf (ipt-o "From: poster@example.invalid
Subject: hello
Newsgroups: fn.letters
Message-ID: <a.b@example.invalid>

Hello, news.
")))
(defconst *ipt-obs-next* (fn-clock-observation 1000001 843004801000 500 t))
(defconst *ipt-d1* (fn-inj-decide *ipt-withid* *ipt-inj-cfg* *ipt-obs*))
(defconst *ipt-d2* (fn-inj-decide *ipt-withid* *ipt-inj-cfg* *ipt-obs-next*))
(assert-event
 (let ((s1 (fn-ipp-injected-octets *ipt-d1* *ipt-secret* *ipt-login* *ipt-cfg1*))
       (s2 (fn-ipp-injected-octets *ipt-d2* *ipt-secret* (ipt-o "bob") *ipt-cfg1*)))
   (and (fn-inj-injectedp *ipt-d1*) (fn-inj-injectedp *ipt-d2*)
        (equal (fn-inj-decision-msgid *ipt-d1*) (fn-inj-decision-msgid *ipt-d2*))
        (not (equal s1 s2))
        (fn-pb-same-articlep (fn-inj-decision-msgid *ipt-d1*) s2 s1))))
; A different source under the same Message-ID is not.
(assert-event
 (let ((s1 (fn-ipp-injected-octets *ipt-d1* *ipt-secret* *ipt-login* *ipt-cfg1*))
       (s3 (fn-ipp-injected-octets
            (fn-inj-decide (append *ipt-withid* (ipt-o "more")) *ipt-inj-cfg* *ipt-obs-next*)
            *ipt-secret* *ipt-login* *ipt-cfg1*)))
   (not (fn-pb-same-articlep (fn-inj-decision-msgid *ipt-d1*) s3 s1))))

; fn-ipp-injected-octets-keep-the-d25-subject: positive on the alice post
; (both conclusions); the omitted injection: a refused decision's octets
; are no source.
(assert-event
 (and (fn-inj-injectedp *ipt-d*)
      (equal (fn-pb-subject *ipt-stored* *ipt-agent* (fn-inj-decision-msgid *ipt-d*))
             (cons :source *ipt-source*))
      (equal (fn-pb-subject (fn-inj-decision-octets *ipt-d*) *ipt-agent*
                            (fn-inj-decision-msgid *ipt-d*))
             (cons :source *ipt-source*))))
(assert-event
 (and (not (fn-inj-injectedp *ipt-refused*))
      (not (equal (fn-pb-subject (fn-ipp-injected-octets *ipt-refused* *ipt-secret*
                                                         *ipt-login* *ipt-cfg1*)
                                 *ipt-agent* (fn-inj-decision-msgid *ipt-refused*))
                  (cons :source *ipt-source*)))))
(must-fail-checked
 (defthm ipt-d25-subject-without-an-injection
   (equal (fn-pb-subject (fn-ipp-injected-octets (fn-inj-decide source config obs)
                                                 secret login cfg)
                         (fn-inj-config-agent config)
                         (fn-inj-decision-msgid (fn-inj-decide source config obs)))
          (cons :source source))
   :hints (("Goal" :in-theory (theory 'minimal-theory)))))

; fn-ipp-a-same-source-retry-is-the-same-article and
; fn-ipp-same-articlep-of-two-injections: the positive witnesses are the D25
; pair above (*ipt-d1*, *ipt-d2*, alice then bob) and the v3 pair below; the
; different-source witness above shows the iff's other side.  Omitted
; Message-ID equality: a generated Message-ID differs per clock reading, and
; the two injections of *ipt-source* are then two articles.  Omitted
; injection of the held one: a blind clock refuses it.
(defconst *ipt-g1* (fn-inj-decide *ipt-source* *ipt-inj-cfg* *ipt-obs*))
(defconst *ipt-g2* (fn-inj-decide *ipt-source* *ipt-inj-cfg* *ipt-obs-next*))
(assert-event
 (and (fn-inj-injectedp *ipt-g1*) (fn-inj-injectedp *ipt-g2*)
      (not (fn-inj-supplies-pathp *ipt-source*))
      (not (equal (fn-inj-decision-msgid *ipt-g1*) (fn-inj-decision-msgid *ipt-g2*)))
      (not (fn-pb-same-articlep
            (fn-inj-decision-msgid *ipt-g1*)
            (fn-ipp-injected-octets *ipt-g2* *ipt-secret* *ipt-login* *ipt-cfg1*)
            (fn-ipp-injected-octets *ipt-g1* *ipt-secret* *ipt-login* *ipt-cfg1*)))))
(defconst *ipt-blind* (fn-clock-observation 1000000 843004800000 500 nil))
(assert-event
 (let ((d0 (fn-inj-decide *ipt-withid* *ipt-inj-cfg* *ipt-blind*)))
   (and (not (fn-inj-injectedp d0)) (fn-inj-injectedp *ipt-d2*)
        (not (fn-pb-same-articlep
              (fn-inj-decision-msgid *ipt-d2*)
              (fn-ipp-injected-octets *ipt-d2* *ipt-secret* *ipt-login* *ipt-cfg1*)
              (fn-ipp-injected-octets d0 *ipt-secret* *ipt-login* *ipt-cfg1*))))))
(must-fail-checked
 (defthm ipt-retry-without-one-message-id
   (implies (and (fn-inj-injectedp (fn-inj-decide source config obs1))
                 (fn-inj-injectedp (fn-inj-decide source config obs2)))
            (fn-pb-same-articlep
             (fn-inj-decision-msgid (fn-inj-decide source config obs1))
             (fn-ipp-injected-octets (fn-inj-decide source config obs2) s2 l2 c2)
             (fn-ipp-injected-octets (fn-inj-decide source config obs1) s1 l1 c1)))
   :hints (("Goal" :in-theory (disable fn-ipp-injected-octets fn-pb-same-articlep
                                       fn-inj-decide fn-inj-injectedp)))))

; fn-ipp-an-injection-does-not-open-with-c: the alice post opens with "P";
; the omitted injection: a refused decision's octets are nil.
(assert-event (and (fn-inj-injectedp *ipt-d*) (equal (car *ipt-stored*) 80)))
(must-fail-checked
 (defthm ipt-never-opens-with-c
   (not (equal (car (fn-ipp-injected-octets d secret login cfg)) 67))
   :hints (("Goal" :in-theory (theory 'minimal-theory)))))

; The supplied-Path (recipe v3) retry, concretely (the general theorem,
; fn-ipp-a-same-source-retry-is-the-same-article, covers both recipes): one source with a Path and a Message-ID, injected at two
; clocks under alice's and bob's parameters, is one article for D25; the
; plain-line reading would have named "AGENT; posting-account=..." as the
; agent (fn-pb-info-line-agent refuses an agent holding ";").
(defconst *ipt-v3* (ipt-crlf (ipt-o "Path: poster.example!not-for-mail
From: poster@example.invalid
Subject: hello
Newsgroups: fn.letters
Message-ID: <v3.retry@example.invalid>

Hello, news.
")))
(defconst *ipt-v3-1* (fn-inj-decide *ipt-v3* *ipt-inj-cfg* *ipt-obs*))
(defconst *ipt-v3-2* (fn-inj-decide *ipt-v3* *ipt-inj-cfg* *ipt-obs-next*))
(assert-event
 (let ((s1 (fn-ipp-injected-octets *ipt-v3-1* *ipt-secret* *ipt-login* *ipt-cfg1*))
       (s2 (fn-ipp-injected-octets *ipt-v3-2* *ipt-secret* (ipt-o "bob") *ipt-cfg1*)))
   (and (fn-inj-injectedp *ipt-v3-1*) (fn-inj-injectedp *ipt-v3-2*)
        (fn-inj-supplies-pathp *ipt-v3*)
        (not (equal s1 s2))
        (equal (fn-pb-path-agent s2 (fn-inj-decision-msgid *ipt-v3-2*)) *ipt-agent*)
        (fn-pb-same-articlep (fn-inj-decision-msgid *ipt-v3-1*) s2 s1))))

; PKT-786 KEYSTONE fn-nop-account-hash-is-the-served-account-value
; (books/native-operator.lisp): `account hash LOGIN' prints the value of
; LOGIN's account, the principal the served table finds for LOGIN.
(defun ipt-lines (lines)
  (if (consp lines)
      (append (fn-record-string-octets (car lines)) (list 10) (ipt-lines (cdr lines)))
    nil))
(defconst *ipt-auth-file*
  (ipt-lines
   (list "[login.\"alice\"]"
         "principal = \"abababababababababababababababababababababababababababababababab\""
         "salt = \"00000000000000000000000000000000\""
         "digest = \"1111111111111111111111111111111111111111111111111111111111111111\""
         "posting = true")))
(defconst *ipt-auth* (fn-native-auth-load *ipt-auth-file* t t nil nil 128))
(defconst *ipt-acfg* (fn-native-auth-result-config *ipt-auth*))
(defconst *ipt-stamp* (fn-clock-observation 5 1700000000 2 t))
(defconst *ipt-code* (fn-record-string-octets "k3y-friend-0001-7f3a"))
(defconst *ipt-robin* (fn-record-string-octets "robin"))
(defmacro ipt-v1 ()
  '(fn-cfg-apply-delta (fn-cfg-empty-value) 1 *ipt-stamp*
                       (fn-cfg-account-invite (fn-acct-code-digest-text *ipt-code*)
                                              "operator" "2000000000")))
(defmacro ipt-v2 ()
  '(fn-cfg-apply-delta
    (ipt-v1) 2 *ipt-stamp*
    (fn-acct-plan-delta (fn-acct-redeem-plan (ipt-v1) *ipt-stamp* *ipt-code*
                                             *ipt-robin*
                                             (fn-record-string-octets "correct horse")
                                             (make-list 16 :initial-element 7) nil))))
(defmacro ipt-served-cred (login v)
  `(fn-auth-find-cred (fn-ipp-octets ,login)
                      (fn-auth-config-creds (fn-auth-config-with-accounts *ipt-acfg* ,v))))

; Reachable witness, a credential-file login: every antecedent, then the
; conclusion; the account is the file's principal, not the login's spelling.
(assert-event (equal (fn-native-auth-result-status *ipt-auth*) :accepted))
(assert-event (ipt-served-cred "alice" (ipt-v2)))
(assert-event
 (equal (fn-nop-account-hash *ipt-secret* "alice" *ipt-auth-file* t 128)
        (fn-pa-account-value *ipt-secret*
                             (fn-ipp-octets (fn-auth-cred-principal
                                             (ipt-served-cred "alice" (ipt-v2)))))))
(assert-event (not (equal (fn-nop-account-hash *ipt-secret* "alice" *ipt-auth-file* t 128)
                          *ipt-hex*)))
; ... and it is the value the article stored under that account carries.
(assert-event
 (ipt-infixp (fn-nop-account-hash *ipt-secret* "alice" *ipt-auth-file* t 128)
             (fn-ipp-injected-octets *ipt-d* *ipt-secret*
                                     (fn-auth-cred-principal (ipt-served-cred "alice" (ipt-v2)))
                                     *ipt-cfg1*)))
; Reachable witness, an invitation-code account the file does not hold: the
; served table finds robin's redeemed credential; the operator's value is
; its principal's.
(assert-event (not (fn-auth-find-cred *ipt-robin* (fn-auth-config-creds *ipt-acfg*))))
(assert-event (ipt-served-cred "robin" (ipt-v2)))
(assert-event
 (equal (fn-nop-account-hash *ipt-secret* "robin" *ipt-auth-file* t 128)
        (fn-pa-account-value *ipt-secret*
                             (fn-ipp-octets (fn-auth-cred-principal
                                             (ipt-served-cred "robin" (ipt-v2)))))))
; Omitted hypothesis, the table finds LOGIN: carol is in neither table (the
; load is accepted, ACFG is its configuration); the conclusion fails.
(assert-event (not (ipt-served-cred "carol" (ipt-v2))))
(assert-event
 (not (equal (fn-nop-account-hash *ipt-secret* "carol" *ipt-auth-file* t 128)
             (fn-pa-account-value *ipt-secret*
                                  (fn-ipp-octets (fn-auth-cred-principal
                                                  (ipt-served-cred "carol" (ipt-v2))))))))
; Omitted hypothesis, the load is accepted: a file with a non-ASCII octet is
; refused; its configuration is the open one, whose table still finds robin
; through the redeemed row, and the operator prints nothing.
(defconst *ipt-bad-file* (list 200 10))
(assert-event (not (equal (fn-native-auth-result-status
                           (fn-native-auth-load *ipt-bad-file* t t nil nil 128))
                          :accepted)))
(assert-event (fn-auth-find-cred *ipt-robin*
                                 (fn-auth-config-creds
                                  (fn-auth-config-with-accounts
                                   (fn-native-auth-result-config
                                    (fn-native-auth-load *ipt-bad-file* t t nil nil 128))
                                   (ipt-v2)))))
(assert-event (null (fn-nop-account-hash *ipt-secret* "robin" *ipt-bad-file* t 128)))
