; Existing AUTHINFO credential/configuration API factored below replay.
; Public names, definitions, theorem statements and native name domain are
; unchanged. Account-authority replay uses this one actual validator without
; pulling the served protocol and its Store replay back into a cycle.
(in-package "ACL2")
(include-book "nntp-syntax")
(include-book "injection-shape")
(include-book "principal")
(include-book "auth-secret")
(local (in-theory (disable (tau-system))))
(local (in-theory (enable fn-inj-nth fn-inj-car fn-inj-cdr)))

; -----------------------------------------------------------------------------
; A credential
;
; (:fn-auth-cred name principal secret postingp).  `name' is the AUTHINFO
; USER argument as octets; `principal' is the substrate principal id
; (books/principal.lisp fn-prin-idp) this login speaks for, so an
; authenticated connection names a principal and not a string; `secret' is
; the stored VERIFIER (books/auth-secret.lisp fn-authsec-verifierp), never a
; secret --- fn-authsec-verifier-is-not-octets is what makes a cleartext
; token unrecognizable in this slot; `postingp' is whether this principal
; may POST.

(defconst *fn-auth-max-name-octets* 64)

(defun fn-auth-cred-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 5) (equal (car x) :fn-auth-cred)))
(defun fn-auth-cred-name (x)
  (declare (xargs :guard t))
  (fn-inj-nth 1 x))
(defun fn-auth-cred-principal (x)
  (declare (xargs :guard t))
  (fn-inj-nth 2 x))
(defun fn-auth-cred-secret (x)
  (declare (xargs :guard t))
  (fn-inj-nth 3 x))
(defun fn-auth-cred-postingp (x)
  (declare (xargs :guard t))
  (fn-inj-nth 4 x))
(defun fn-auth-make-cred (name principal secret postingp)
  (declare (xargs :guard t))
  (list :fn-auth-cred name principal secret postingp))

(defthm fn-auth-cred-shapep-of-fn-auth-make-cred
  (fn-auth-cred-shapep (fn-auth-make-cred name principal secret postingp)))
(defthm fn-auth-cred-name-of-fn-auth-make-cred
  (equal (fn-auth-cred-name (fn-auth-make-cred name principal secret postingp))
         name))
(defthm fn-auth-cred-principal-of-fn-auth-make-cred
  (equal (fn-auth-cred-principal
          (fn-auth-make-cred name principal secret postingp))
         principal))
(defthm fn-auth-cred-secret-of-fn-auth-make-cred
  (equal (fn-auth-cred-secret (fn-auth-make-cred name principal secret postingp))
         secret))
(defthm fn-auth-cred-postingp-of-fn-auth-make-cred
  (equal (fn-auth-cred-postingp
          (fn-auth-make-cred name principal secret postingp))
         postingp))
(defthm fn-auth-cred-shapep-forward-shape
  (implies (fn-auth-cred-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

; The accessor-of-nothing facts fn-defrecord generates and this hand-written
; record lacks (docs/proof-style.md section 1, "what opacity takes away"):
; a field that is there means the record is there.  Forward-chaining on the
; field term itself, never a rewrite.
(defthm fn-auth-cred-accessors-forward-consp
  (and (implies (fn-auth-cred-name x) (consp x))
       (implies (fn-auth-cred-principal x) (consp x))
       (implies (fn-auth-cred-secret x) (consp x))
       (implies (fn-auth-cred-postingp x) (consp x)))
  :rule-classes
  ((:forward-chaining :corollary (implies (fn-auth-cred-name x) (consp x))
                      :trigger-terms ((fn-auth-cred-name x)))
   (:forward-chaining :corollary (implies (fn-auth-cred-principal x) (consp x))
                      :trigger-terms ((fn-auth-cred-principal x)))
   (:forward-chaining :corollary (implies (fn-auth-cred-secret x) (consp x))
                      :trigger-terms ((fn-auth-cred-secret x)))
   (:forward-chaining :corollary (implies (fn-auth-cred-postingp x) (consp x))
                      :trigger-terms ((fn-auth-cred-postingp x))))
  :hints (("Goal" :in-theory (enable fn-auth-cred-name fn-auth-cred-principal
                                     fn-auth-cred-secret fn-auth-cred-postingp
                                     fn-inj-nth))))

(in-theory (disable (:d fn-auth-cred-shapep) (:d fn-auth-make-cred)
                    (:d fn-auth-cred-name) (:d fn-auth-cred-principal)
                    (:d fn-auth-cred-secret) (:d fn-auth-cred-postingp)))

(defun fn-auth-credp (x)
  (declare (xargs :guard t))
  (and (fn-auth-cred-shapep x)
       (fn-nntp-printable-tokenp (fn-auth-cred-name x))
       (consp (fn-auth-cred-name x))
       (true-listp (fn-auth-cred-name x))
       (<= (len (fn-auth-cred-name x)) *fn-auth-max-name-octets*)
       (fn-prin-idp (fn-auth-cred-principal x))
       (fn-authsec-verifierp (fn-auth-cred-secret x))
       (booleanp (fn-auth-cred-postingp x))))

(defun fn-auth-cred-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-auth-credp (car xs)) (fn-auth-cred-listp (cdr xs)))
    (null xs)))

(defun fn-auth-find-cred (name creds)
  (declare (xargs :guard t))
  (if (consp creds)
      (if (equal (fn-auth-cred-name (car creds)) name)
          (car creds)
        (fn-auth-find-cred name (cdr creds)))
    nil))

(defthm fn-auth-find-cred-is-a-cred
  (implies (and (fn-auth-cred-listp creds) (fn-auth-find-cred name creds))
           (fn-auth-credp (fn-auth-find-cred name creds))))

; -----------------------------------------------------------------------------
; The connection's authentication configuration, pinned at open
;
; (:fn-auth-config requiredp protected-onlyp tls-availablep creds).
;   requiredp        authentication is required before a state-changing command
;   protected-onlyp  AUTHINFO USER/PASS is refused on an unprotected
;                    connection (RFC 4643 section 2.3.2's 483)
;   tls-availablep   the host holds a certificate and key, so STARTTLS can be
;                    advertised and answered 382 rather than 580
;                    (RFC 4642 section 2.2.2)

(defun fn-auth-config-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 5) (equal (car x) :fn-auth-config)))
(defun fn-auth-config-requiredp (x)
  (declare (xargs :guard t))
  (fn-inj-nth 1 x))
(defun fn-auth-config-protected-onlyp (x)
  (declare (xargs :guard t))
  (fn-inj-nth 2 x))
(defun fn-auth-config-tls-availablep (x)
  (declare (xargs :guard t))
  (fn-inj-nth 3 x))
(defun fn-auth-config-creds (x)
  (declare (xargs :guard t))
  (fn-inj-nth 4 x))
(defun fn-auth-make-config (requiredp protected-onlyp tls-availablep creds)
  (declare (xargs :guard t))
  (list :fn-auth-config requiredp protected-onlyp tls-availablep creds))

(defthm fn-auth-config-shapep-of-fn-auth-make-config
  (fn-auth-config-shapep
   (fn-auth-make-config requiredp protected-onlyp tls-availablep creds)))
(defthm fn-auth-config-requiredp-of-fn-auth-make-config
  (equal (fn-auth-config-requiredp
          (fn-auth-make-config requiredp protected-onlyp tls-availablep creds))
         requiredp))
(defthm fn-auth-config-protected-onlyp-of-fn-auth-make-config
  (equal (fn-auth-config-protected-onlyp
          (fn-auth-make-config requiredp protected-onlyp tls-availablep creds))
         protected-onlyp))
(defthm fn-auth-config-tls-availablep-of-fn-auth-make-config
  (equal (fn-auth-config-tls-availablep
          (fn-auth-make-config requiredp protected-onlyp tls-availablep creds))
         tls-availablep))
(defthm fn-auth-config-creds-of-fn-auth-make-config
  (equal (fn-auth-config-creds
          (fn-auth-make-config requiredp protected-onlyp tls-availablep creds))
         creds))

(in-theory (disable (:d fn-auth-config-shapep) (:d fn-auth-make-config)
                    (:d fn-auth-config-requiredp)
                    (:d fn-auth-config-protected-onlyp)
                    (:d fn-auth-config-tls-availablep)
                    (:d fn-auth-config-creds)))

(defun fn-auth-configp (x)
  (declare (xargs :guard t))
  (and (fn-auth-config-shapep x)
       (booleanp (fn-auth-config-requiredp x))
       (booleanp (fn-auth-config-protected-onlyp x))
       (booleanp (fn-auth-config-tls-availablep x))
       (fn-auth-cred-listp (fn-auth-config-creds x))))

