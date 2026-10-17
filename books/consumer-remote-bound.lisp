; fn: the remote consumer is the account's bound consumer, reached over TLS
; (D48 / PKT-673: "authenticated remote access scoped to the account;
; operator controls stay private"; specs/applications.md).
;
; An FNCR request (books/consumer-remote-codec.lisp) names an operation, a
; login, the account's password and a consumer.  It is served by exactly
; the local consumer operations that already serve an account's bound
; consumer (books/consumer-bound.lisp, PRF-234): `bound-poll', `bound-wait',
; `bound-ack', and `position' / `status' once the same gate has passed.
; Nothing new decides delivery: every guarantee of fn-cbind-poll /
; fn-cbind-ack (a subsequence of the consumer's events, each readable under
; the account's rule; an ack in scope or a refusal) holds of a remote answer
; because a remote answer IS one of those answers.
;
; What the route admits, refuses and leaves uncertain:
;   * register, rebase and unregister are operator controls: refused
;     :operator-control, whatever the credential (the operator binds a
;     consumer to an account; the account cannot rebind or remove it).
;   * a consumer no binding names, or bound to another login than the one
;     the request names, is refused :credential (the same word a wrong
;     password gets, so a remote caller learns nothing about bindings).
;   * otherwise the gate of a bound consumer decides (credential, scope,
;     the account's read rule), and only then the operation runs.
;   * uncertain is never decided here: an ack's durable outcome lost with
;     its reply is the client's to settle with `position', as locally.
(in-package "ACL2")
(include-book "consumer-bound")
(include-book "consumer-remote-codec")

(defconst *fn-crbd-operator-operations* '(:register :rebase :unregister))
(defconst *fn-crbd-served-operations* '(:poll :wait :ack :position :status))

; The binding names LOGIN (octets as the FNCR text field carries them).
(defun fn-crbd-bound-to-p (oc consumer login)
  (declare (xargs :guard t))
  (let ((bound (fn-cbind-config-login oc consumer)))
    (and (stringp bound)
         (equal (fn-record-string-octets bound) login))))

; The local operation a remote request is, or (:refused REASON).
;   (:bound-poll CONSUMER SECRET)  (:bound-wait CONSUMER (SECONDS SECRET))
;   (:bound-ack CURSOR SECRET)     (:position CONSUMER nil) (:status CONSUMER nil)
; These are the argument shapes host/native/owner.lisp's
; fnn-owner-consumer-local-serialized / fnn-owner-consumer-local-wait take.
(defun fn-crbd-route (request oc acfg)
  (declare (xargs :guard t :verify-guards nil))
  (let ((op (fn-cp-nth 1 request)) (login (fn-cp-nth 2 request))
        (secret (fn-cp-nth 3 request)) (consumer (fn-cp-nth 4 request))
        (cursor (fn-cp-nth 6 request)) (seconds (fn-cp-nth 7 request)))
    (cond ((member-eq op *fn-crbd-operator-operations*)
           (list :refused :operator-control))
          ((not (member-eq op *fn-crbd-served-operations*))
           (list :refused :operation))
          ((not (fn-crbd-bound-to-p oc consumer login))
           (list :refused :credential))
          ((and (eq op :ack)
                (not (equal (fn-cbind-cursor-consumer cursor) consumer)))
           (list :refused :scope))
          (t (or (fn-cbind-gate oc acfg consumer secret)
                 (case op
                   (:poll (list :bound-poll consumer secret))
                   (:wait (list :bound-wait consumer (list seconds secret)))
                   (:ack (list :bound-ack cursor secret))
                   (:position (list :position consumer nil))
                   (otherwise (list :status consumer nil))))))))

; -----------------------------------------------------------------------------
; The statement (CNS-011 remote profile).  Every route is a refusal or the
; named account's bound operation, on the request's own consumer and
; password, with the bound gate passed at the route's own reading of the
; configuration.

(defthm fn-crbd-operator-controls-stay-private
  (implies (member-eq (fn-cp-nth 1 request) *fn-crbd-operator-operations*)
           (equal (fn-crbd-route request oc acfg)
                  '(:refused :operator-control)))
  :hints (("Goal" :in-theory '(fn-crbd-route member-equal
                               (:executable-counterpart member-equal)))))

; The bound gate answers nil (served) or a refusal, never an operation.
(defthm fn-crbd-gate-is-nil-or-a-refusal
  (implies (fn-cbind-gate oc acfg consumer secret)
           (equal (car (fn-cbind-gate oc acfg consumer secret)) :refused))
  :hints (("Goal" :in-theory (e/d (fn-cbind-gate)
                                  (fn-cbind-config-login fn-cbind-authenticp
                                   fn-col-scope-entry fn-cbind-group-readablep
                                   fn-cbind-read-pattern)))))

(defthm fn-crbd-route-is-the-accounts-bound-operation
  (let ((route (fn-crbd-route request oc acfg))
        (op (fn-cp-nth 1 request)) (secret (fn-cp-nth 3 request))
        (consumer (fn-cp-nth 4 request)))
    (implies (not (eq (car route) :refused))
             (and (member-eq op *fn-crbd-served-operations*)
                  (stringp (fn-cbind-config-login oc consumer))
                  (equal (fn-record-string-octets (fn-cbind-config-login oc consumer))
                         (fn-cp-nth 2 request))
                  (null (fn-cbind-gate oc acfg consumer secret))
                  (equal route
                         (case op
                           (:poll (list :bound-poll consumer secret))
                           (:wait (list :bound-wait consumer
                                        (list (fn-cp-nth 7 request) secret)))
                           (:ack (list :bound-ack (fn-cp-nth 6 request) secret))
                           (:position (list :position consumer nil))
                           (otherwise (list :status consumer nil))))
                  (implies (eq op :ack)
                           (equal (fn-cbind-cursor-consumer (fn-cp-nth 6 request))
                                  consumer)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-crbd-route fn-crbd-bound-to-p)
                                  (fn-cbind-gate fn-cbind-config-login
                                   fn-cbind-cursor-consumer fn-cp-nth
                                   fn-record-string-octets)))))

; Teeth on the account: a request naming any other login than the binding's
; is refused before the gate, whatever its password.
(defthm fn-crbd-another-login-is-refused
  (implies (and (not (member-eq (fn-cp-nth 1 request) *fn-crbd-operator-operations*))
                (member-eq (fn-cp-nth 1 request) *fn-crbd-served-operations*)
                (not (equal (fn-record-string-octets
                             (fn-cbind-config-login oc (fn-cp-nth 4 request)))
                            (fn-cp-nth 2 request))))
           (equal (fn-crbd-route request oc acfg) '(:refused :credential)))
  :hints (("Goal" :in-theory (e/d (fn-crbd-route fn-crbd-bound-to-p)
                                  (fn-cbind-gate fn-cbind-config-login
                                   fn-record-string-octets fn-cp-nth)))))

(in-theory (disable fn-crbd-bound-to-p fn-crbd-route))
