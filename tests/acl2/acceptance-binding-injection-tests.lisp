; Literal teeth for the actual POST source recovery boundary.
(in-package "ACL2")
(include-book "../../books/acceptance-binding-injection")
(defconst *abit-source*
  (append (fn-record-string-octets "From: poster@example.invalid") '(13 10)
          (fn-record-string-octets "Subject: hello") '(13 10)
          (fn-record-string-octets "Newsgroups: fn.letters") '(13 10)
          (fn-record-string-octets "Message-ID: <binding@example.invalid>") '(13 10 13 10)
          (fn-record-string-octets "Hello, news.") '(13 10)))
(defconst *abit-agent* (fn-record-string-octets "fn.example.invalid"))
(defconst *abit-config*
  (fn-inj-make-config t *abit-agent*
                      (list (fn-record-string-octets "fn.letters")) 32768))
(defconst *abit-closed-config*
  (fn-inj-make-config nil *abit-agent*
                      (list (fn-record-string-octets "fn.letters")) 32768))
(defconst *abit-observation* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *abit-decision*
  (fn-inj-decide *abit-source* *abit-config* *abit-observation*))
; Complete antecedent and conclusion of the successful POST inverse.
(assert-event
 (and (fn-inj-injectedp *abit-decision*)
      (equal (fn-abi-post-source *abit-decision*) (cons t *abit-source*))
      (fn-ab-p (fn-abi-post-binding *abit-decision*))
      (equal (fn-abi-post-binding *abit-decision*)
             (fn-ab-for-received :post-d25 *abit-source*))))
; Hypothesis removal: the sole antecedent fails and its conclusion fails.
(assert-event
 (let ((refused (fn-inj-decide *abit-source* *abit-closed-config*
                             *abit-observation*)))
   (and (not (fn-inj-injectedp refused))
        (not (equal (fn-abi-post-source refused) (cons t *abit-source*)))
        (equal (fn-abi-post-binding refused) nil))))
; Exact incoming article profile; malformed native evidence cannot downgrade.
(assert-event
 (and (equal (fn-own-received-source-context *abit-source*) :relay-v1)
      (equal (fn-abi-received-binding *abit-source*)
             (fn-ab-for-received :relay-v1 *abit-source*))))
(defconst *abit-malformed*
  (append (fn-record-string-octets "FN-Authorship: !!!") '(13 10)
          *abit-source*))
(assert-event
 (and (equal (fn-own-received-source-context *abit-malformed*) nil)
      (equal (fn-abi-received-binding *abit-malformed*) nil)))
