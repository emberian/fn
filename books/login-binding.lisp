;; fn: a login bound to a signing principal, and the posting policy that
;; reads the binding.
;
; The reader spike (planning/evidence/spike-reader-2026-09-25.md, deferral 1)
; measured that an AUTHINFO login is not related to any signing principal:
; login `ember' POSTed an article signed with guest's key and the node
; answered `verified' for guest's principal.  That is a correct signature
; claim, and it is all the node said.  This book adds the relation, as an
; operator's choice per node:
;
;   * a binding (LOGIN . PRINCIPAL), PRINCIPAL the 32 octets of a hybrid
;     principal, is the `signing' field of the login's table in the
;     credential file, written by `fn principal bind LOGIN PRINCIPAL-HEX'
;     (books/native-auth-admin.lisp fn-native-auth-admin-bind) and read by
;     books/native-auth-profile.lisp fn-native-auth-load-bindings;
;   * the policy is the durable configuration record `posting-policy'
;     (`fn policy set posting-policy bound-logins', books/native-admin.lisp),
;     applied live through the owner like every policy record;
;   * under the policy, a served POST from a bound login is refused unless it
;     carries an FN-Authorship carrier naming the bound principal: an
;     unsigned article is :login-unsigned, a carrier naming another principal
;     is :login-not-bound.  An unbound login, an unauthenticated connection
;     and a node without the policy are decided exactly as before.
;
; The gate decides from the carrier the article names
; (books/peer-authored-accept.lisp fn-pa-carrier-form), before the plan
; verifies it.  The host calls it first on the served path
; (host/native/owner.lisp fnn-owner-attempt-served through
; host/owner-host.lisp fn-owner-login-gate) and on a refusal relays the reason
; as the served word (fn-pa-served-word, the 441 line of
; books/nntp-post.lisp fn-post-store-refusal-text); on a pass it continues
; into the unchanged transit attempt, which calls fn-pa-current-plan.  The
; keystone below composes the two in that order.
;
; The verdict names the login it decided for: (:pass LOGIN BOUND) or
; (:refused REASON LOGIN), and fn-lb-verdict-line renders it into the
; service log.  The Store's kind-4 verdict record is unchanged: it names the
; principal and keyring generation, not the login.

(in-package "ACL2")
(include-book "peer-authored-accept")
(include-book "owner")

(defconst *fn-lb-policy-slot* "posting-policy")
(defconst *fn-lb-policy-bound-logins* "bound-logins")

; The policy as the owner's live configuration states it.
(defun fn-lb-policy-onp (cfg)
  (declare (xargs :guard t))
  (equal (fn-cfg-policy (fn-cfg-value cfg) *fn-lb-policy-slot*)
         *fn-lb-policy-bound-logins*))

; The principal LOGIN is bound to, or nil.  No login (nil) is never bound.
(defun fn-lb-binding (login bindings)
  (declare (xargs :guard t))
  (if (consp bindings)
      (if (and login (consp (car bindings)) (equal (car (car bindings)) login))
          (cdr (car bindings))
        (fn-lb-binding login (cdr bindings)))
    nil))

(defun fn-lb-gate (received login bindings policyp)
  (declare (xargs :guard t))
  (let ((bound (and policyp (fn-lb-binding login bindings))))
    (if (not bound)
        (list :pass login nil)
      (let ((form (fn-pa-carrier-form received)))
        (cond ((equal form :absent) (list :refused :login-unsigned login))
              ((and (consp form) (equal (car form) :ok))
               (if (equal (nth 2 form) bound)
                   (list :pass login bound)
                 (list :refused :login-not-bound login)))
              ; A present carrier the form refuses: the host's next step
              ; (fn-pa-carrier-form again, inside the transit attempt)
              ; refuses it with the carrier's own reason.
              (t (list :pass login bound)))))))

; The login of the served submission in flight: the AUTHINFO USER name of
; the connection that submitted it, once that connection authenticated.  A
; control or BP submission (fn-own-control-submissionp) has no connection
; and no login.
(defun fn-lb-inflight-login (o)
  (declare (xargs :guard t))
  (let* ((sub (fn-own-inflight o))
         (conn (and sub (not (fn-own-control-submissionp sub))
                    (fn-own-find-conn (fn-own-sub-id sub) (fn-own-conns o))))
         (as (and conn (fn-own-conn-session conn))))
    (if (and conn (fn-auth-session-subject as))
        (fn-auth-session-pending as)
      nil)))

; The function the host calls (host/owner-host.lisp fn-owner-login-gate):
; the owner, its live configuration and the binding table the native auth
; profile loaded.
(defun fn-lb-owner-gate (o cfg bindings received)
  (declare (xargs :guard t))
  (fn-lb-gate received (fn-lb-inflight-login o) bindings
              (fn-lb-policy-onp cfg)))

(defun fn-lb-verdict-reason (verdict)
  (declare (xargs :guard t))
  (if (and (consp verdict) (equal (car verdict) :refused) (consp (cdr verdict)))
      (car (cdr verdict))
    nil))

; One service-log line, or nil when no login decided anything (an
; unauthenticated connection, a control submission).
(defun fn-lb-verdict-line (verdict)
  (declare (xargs :guard t))
  (let ((login (if (equal (fn-inj-car verdict) :pass)
                   (fn-inj-nth 1 verdict)
                 (fn-inj-nth 2 verdict)))
        (bound (if (equal (fn-inj-car verdict) :pass) (fn-inj-nth 2 verdict) nil)))
    (if (not (and (fn-cbor-octet-listp login) (consp login)))
        nil
      (append (fn-record-string-octets "post login=")
              login
              (cond ((equal (fn-lb-verdict-reason verdict) :login-unsigned)
                     (fn-record-string-octets " refused login-unsigned"))
                    ((equal (fn-lb-verdict-reason verdict) :login-not-bound)
                     (fn-record-string-octets " refused login-not-bound"))
                    ((and (fn-cbor-octet-listp bound) (consp bound))
                     (append (fn-record-string-octets " bound=")
                             (fn-id-hex-octets bound)))
                    (t (fn-record-string-octets " unbound")))))))

;; ---------------------------------------------------------------------------
;; Theorems over fn-lb-owner-gate, the function the host calls, composed with
;; fn-pa-current-plan, the plan the host calls after it on a pass.

(defthm fn-lb-owner-gate-unfolds
  (equal (fn-lb-owner-gate o cfg bindings received)
         (fn-lb-gate received (fn-lb-inflight-login o) bindings
                     (fn-lb-policy-onp cfg))))

(local
 (defthm fn-lb-ok-plan-names-the-carrier-principal
   (implies (equal (car (fn-pa-current-plan received snapshots carried)) :ok)
            (and (consp (fn-pa-carrier-form received))
                 (equal (car (fn-pa-carrier-form received)) :ok)
                 (equal (nth 2 (fn-pa-current-plan received snapshots carried))
                        (nth 2 (fn-pa-carrier-form received)))))
   :hints (("Goal" :in-theory (e/d (fn-pa-current-plan)
                                   (fn-pa-carrier-form
                                    fn-hl-current-for-principal
                                    fn-hl-current-enrollment
                                    fn-pa-carriesp))))))

; KEYSTONE.  Under the policy, a served article from a bound login that the
; gate passes and the plan accepts under this node's enrollment carries the
; login's bound principal: the plan's principal (the one the kind-4 event
; and its `verified' verdict name) is the binding.
(defthm fn-lb-bound-login-accepted-signed-article-carries-its-principal
  (implies (and (fn-lb-policy-onp cfg)
                (equal (fn-lb-binding (fn-lb-inflight-login o) bindings)
                       principal)
                principal
                (equal (car (fn-lb-owner-gate o cfg bindings received)) :pass)
                (equal (car (fn-pa-current-plan received snapshots carried))
                       :ok))
           (equal (nth 2 (fn-pa-current-plan received snapshots carried))
                  principal))
  :hints (("Goal" :in-theory (e/d (fn-lb-gate)
                                  (fn-pa-current-plan fn-pa-carrier-form
                                   fn-lb-binding fn-lb-inflight-login
                                   fn-lb-policy-onp)))))

; KEYSTONE.  Under the policy, a bound login's article with no carrier is
; refused, whatever else it says.
(defthm fn-lb-bound-login-unsigned-article-is-refused
  (implies (and (fn-lb-policy-onp cfg)
                (fn-lb-binding (fn-lb-inflight-login o) bindings)
                (equal (fn-pa-carrier-form received) :absent))
           (equal (fn-lb-owner-gate o cfg bindings received)
                  (list :refused :login-unsigned (fn-lb-inflight-login o))))
  :hints (("Goal" :in-theory (e/d (fn-lb-gate)
                                  (fn-pa-carrier-form fn-lb-binding
                                   fn-lb-inflight-login fn-lb-policy-onp)))))

; KEYSTONE.  Under the policy, a bound login's article whose carrier names
; another principal is refused.
(defthm fn-lb-bound-login-other-principal-is-refused
  (implies (and (fn-lb-policy-onp cfg)
                (fn-lb-binding (fn-lb-inflight-login o) bindings)
                (equal (car (fn-pa-carrier-form received)) :ok)
                (not (equal (nth 2 (fn-pa-carrier-form received))
                            (fn-lb-binding (fn-lb-inflight-login o) bindings))))
           (equal (fn-lb-owner-gate o cfg bindings received)
                  (list :refused :login-not-bound (fn-lb-inflight-login o))))
  :hints (("Goal" :in-theory (e/d (fn-lb-gate)
                                  (fn-pa-carrier-form fn-lb-binding
                                   fn-lb-inflight-login fn-lb-policy-onp)))))

; KEYSTONE.  With the policy off the gate passes every article, so the host
; continues into the transit attempt it made before this book existed.
(defthm fn-lb-policy-off-never-refuses
  (implies (not (fn-lb-policy-onp cfg))
           (equal (car (fn-lb-owner-gate o cfg bindings received)) :pass))
  :hints (("Goal" :in-theory (e/d (fn-lb-gate)
                                  (fn-pa-carrier-form fn-lb-binding
                                   fn-lb-inflight-login fn-lb-policy-onp)))))

; KEYSTONE.  An unbound login (and an unauthenticated connection, whose login
; is nil) passes under the policy too.
(defthm fn-lb-unbound-login-never-refuses
  (implies (not (fn-lb-binding (fn-lb-inflight-login o) bindings))
           (equal (car (fn-lb-owner-gate o cfg bindings received)) :pass))
  :hints (("Goal" :in-theory (e/d (fn-lb-gate)
                                  (fn-pa-carrier-form fn-lb-binding
                                   fn-lb-inflight-login fn-lb-policy-onp)))))

; The verdict names the login it decided for, on every outcome.
(defthm fn-lb-verdict-names-the-login
  (equal (if (equal (car (fn-lb-owner-gate o cfg bindings received)) :pass)
             (nth 1 (fn-lb-owner-gate o cfg bindings received))
           (nth 2 (fn-lb-owner-gate o cfg bindings received)))
         (fn-lb-inflight-login o))
  :hints (("Goal" :in-theory (e/d (fn-lb-gate)
                                  (fn-pa-carrier-form fn-lb-binding
                                   fn-lb-inflight-login fn-lb-policy-onp)))))

; The only refusal reasons, and both are served reasons the host relays to
; their own 441 line.
(defthm fn-lb-refusal-reasons-are-served-reasons
  (implies (equal (car (fn-lb-owner-gate o cfg bindings received)) :refused)
           (member-equal (nth 1 (fn-lb-owner-gate o cfg bindings received))
                         *fn-pa-served-reasons*))
  :hints (("Goal" :in-theory (e/d (fn-lb-gate)
                                  (fn-pa-carrier-form fn-lb-binding
                                   fn-lb-inflight-login fn-lb-policy-onp)))))

(in-theory (disable fn-lb-policy-onp fn-lb-binding fn-lb-gate
                    fn-lb-inflight-login fn-lb-owner-gate
                    fn-lb-verdict-reason fn-lb-verdict-line))
