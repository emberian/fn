; Teeth for the Injection-Info parameters (PKT-597):
; books/injection-info-params-invariants.lisp (the keystones),
; books/injection-info-params.lisp (fn-ipp-injected-octets-without-parameters),
; books/injection-info-policy.lisp (the complaints address, the operator's
; account hash), the admin arm and the operator verb.
(in-package "ACL2")
(include-book "../../books/injection-info-params-invariants")
(include-book "../../books/native-operator")
(include-book "std/testing/must-fail" :dir :system)

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

(defconst *ipt-secret* (make-list 32 :initial-element 7))
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
; The operator's verb gives the value the article carries.
(assert-event (equal (fn-ipp-account-hash *ipt-secret* "alice") *ipt-hex*))
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
(must-fail
 (defthm ipt-carry-without-an-injection
   (equal (fn-ipp-injected-octets (fn-inj-decide source config obs) secret login cfg)
          (append (fn-ipp-prefix-with
                   (fn-ipp-date obs) (fn-inj-decision-msgid (fn-inj-decide source config obs))
                   (fn-inj-config-agent config) (fn-ipp-gid source) (fn-ipp-gdate source)
                   (fn-ipp-params secret login (fn-ipp-complaints cfg)))
                  source))))

; fn-ipp-with-params-of-an-injection: the same antecedent; its removal is
; the witness above with PARAMS the parameters.
(must-fail
 (defthm ipt-with-params-without-an-injection
   (equal (fn-ipp-with-params (fn-inj-decision-octets (fn-inj-decide source config obs))
                              (fn-inj-decision-msgid (fn-inj-decide source config obs))
                              params)
          (append (fn-ipp-prefix-with
                   (fn-ipp-date obs) (fn-inj-decision-msgid (fn-inj-decide source config obs))
                   (fn-inj-config-agent config) (fn-ipp-gid source) (fn-ipp-gdate source)
                   params)
                  source))))

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
(must-fail
 (defthm ipt-keeps-the-source-without-a-run
   (implies (fn-inj-injectedp (fn-inj-decide source config obs))
            (equal (fn-inj-source-of
                    (fn-ipp-with-params
                     (fn-inj-decision-octets (fn-inj-decide source config obs))
                     (fn-inj-decision-msgid (fn-inj-decide source config obs))
                     params)
                    (fn-inj-config-agent config)
                    (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                   (cons t source)))))
(must-fail
 (defthm ipt-keeps-the-source-without-an-injection
   (implies (fn-ipp-params-okp params)
            (equal (fn-inj-source-of
                    (fn-ipp-with-params
                     (fn-inj-decision-octets (fn-inj-decide source config obs))
                     (fn-inj-decision-msgid (fn-inj-decide source config obs))
                     params)
                    (fn-inj-config-agent config)
                    (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                   (cons t source)))))

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
(must-fail
 (defthm ipt-params-of-anyone
   (equal (fn-ipp-params secret login addr)
          (append *fn-ipp-account-open*
                  (fn-pa-account-value secret (fn-ipp-octets login))
                  *fn-ipp-quote*
                  (if (consp addr) (fn-ipp-complaints-param addr) nil)))))
(must-fail
 (defthm ipt-params-never-an-account
   (equal (fn-ipp-params secret login addr)
          (if (consp addr) (fn-ipp-complaints-param addr) nil))))
(must-fail
 (defthm ipt-everyone-has-parameters
   (consp (fn-ipp-params secret login addr))))

; fn-ipp-params-are-a-parameter-run: without parameters there is no run.
(assert-event
 (and (not (consp (fn-ipp-params nil nil (fn-ipp-complaints *ipt-cfg0*))))
      (not (fn-ipp-params-okp (fn-ipp-params nil nil (fn-ipp-complaints *ipt-cfg0*))))))
(assert-event
 (fn-ipp-params-okp (fn-ipp-params *ipt-secret* *ipt-login* (fn-ipp-complaints *ipt-cfg1*))))
(must-fail
 (defthm ipt-params-always-a-run
   (fn-ipp-params-okp (fn-ipp-params secret login (fn-ipp-complaints cfg)))))

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
(must-fail
 (defthm ipt-without-parameters-under-a-login
   (implies (not (fn-ipp-complaints cfg))
            (equal (fn-ipp-injected-octets d secret login cfg)
                   (fn-inj-decision-octets d)))))
(must-fail
 (defthm ipt-without-parameters-with-an-address
   (implies (not (fn-ipp-accountp secret login))
            (equal (fn-ipp-injected-octets d secret login cfg)
                   (fn-inj-decision-octets d)))))

; The complaints address: an addr-spec has no DQUOTE, backslash, ";", CR,
; LF; a string with a DQUOTE is no addr-spec (so it never reaches the
; header), and the admin plan refuses it.
(assert-event (fn-ipp-addr-specp (ipt-o "abuse@example.org")))
(assert-event (not (fn-ipp-addr-specp (ipt-o "a\"b@example.org"))))
(assert-event (not (fn-ipp-addr-specp (ipt-o "abuse"))))
(must-fail
 (defthm ipt-any-text-is-quote-free
   (not (member-equal 34 x))))

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
