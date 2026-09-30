; FNCR ingress only. No local-control dispatcher, authority seed, or durable
; write occurs here. The actual owner supplies its established publication6.
(in-package "ACL2")
(include-book "consumer-remote-codec")
(include-book "consumer-account-auth")

(defun fn-cre-header-octets ()
 (declare (xargs :guard t)) *fn-frame-header-octets*)

; An admitted decoder result is carried into this boundary. Do not run its
; whole definition recognizer again: that would be a second query walk.
(defun fn-cre-envelopep (request)
 (declare (xargs :guard t))
 (and (fn-cbor-at-mostp request 8) (equal (len request) 8)
      (true-listp request) (eq (car request) :remote-consumer)
      (member-eq (fn-cp-nth 1 request) *fn-cr-operations*)
      (fn-cai-namep (fn-cp-nth 2 request) *fn-auth-max-name-octets*)
      (fn-ncl-secretp (fn-cp-nth 3 request))
      (fn-cp-idp (fn-cp-nth 4 request))))

(defun fn-cre-receive-failure (observation)
 (declare (xargs :guard t))
 (if (member-eq (fn-cp-nth 0 observation) '(:refused :unavailable :uncertain :fault)) observation
  (case observation (:timeout '(:unavailable :timeout)) (:closed '(:unavailable :closed))
   (otherwise '(:fault :transport)))))

; Ten octets are inspected before requesting any payload allocation. This
; decides the exact remaining wire extent; it does not establish funding.
(defun fn-cre-header-plan (header protectedp g)
 (declare (xargs :guard t))
 (cond ((not (eq protectedp t)) '(:refused :protected-channel))
       ((not (and (fn-cbor-at-mostp header *fn-frame-header-octets*)
                  (equal (len header) *fn-frame-header-octets*)
                  (fn-cbor-octet-listp header))) '(:refused :frame))
       (t
        (let ((tail (nthcdr 6 header)))
         (if (not (and (fn-cbor-octet-listp tail) (consp tail)
                       (consp (cdr tail)) (consp (cddr tail)) (consp (cdddr tail))))
             '(:refused :frame)
        (let ((payload (fn-cbor-u32-from tail)))
         (if (and (equal (take 4 header) *fn-cr-magic*)
                  (equal (fn-cp-nth 4 header) *fn-cr-version*)
                  (equal (fn-cp-nth 5 header) 1)
                  (fn-frame-spec-listp (fn-cr-spec g))
                  (<= (nfix payload) (fn-frame-specs-width (fn-cr-spec g))))
             (list :receive (+ (nfix payload) *fn-frame-trailer-octets*))
           '(:refused :frame))))))))

; Ingress authenticates each invocation, including a WAIT wake. Result7 is
; (:authenticated request principal creation namespace revision epoch).
; Authentication alone does not authorize a query, an article, or a mutation.
(defun fn-cre-ingress (request protectedp g cp epoch count publication)
 (declare (ignore g) (xargs :guard t))
 (if (not (fn-cre-envelopep request)) '(:refused :request)
  (let ((auth (fn-cra-authenticate cp epoch count publication
                (fn-cp-nth 2 request) (fn-cp-nth 3 request) protectedp)))
   (if (eq (car auth) :ok)
       (list :authenticated request (fn-cp-nth 1 auth)
              (fn-cp-nth 2 auth) (fn-cp-nth 3 auth) (fn-cp-nth 4 auth) epoch)
     auth))))

; OLD is selected by the current-source bounded CP producer. Account creation
; is checked independently of principal, so two configured login names sharing
; a principal and password still cannot operate each other's registration.
(defun fn-cre-selected-route (ingress old)
 (declare (xargs :guard t))
 (if (not (eq (fn-cp-nth 0 ingress) :authenticated))
     (if (member-eq (fn-cp-nth 0 ingress) '(:refused :unavailable)) ingress
       '(:refused :authentication))
  (let* ((request (fn-cp-nth 1 ingress)) (op (fn-cp-nth 1 request))
         (principal (fn-cp-nth 2 ingress)) (creation (fn-cp-nth 3 ingress))
         (revision (fn-cp-nth 5 ingress))
         (own (and (fn-cbor-at-mostp old 10) (equal (len old) 10)
                   (eq (fn-cp-nth 0 old) :entry)
                   (equal (fn-cp-nth 1 old) (fn-cp-nth 4 request))
                   (equal (fn-cp-nth 2 old) principal)
                   (equal (fn-cp-nth 9 old) creation))))
   (cond ((and (eq op :register) (not old))
          (list :definition-request (fn-cp-nth 5 request) nil))
         ((not own) '(:refused :scope))
         ((member-eq op '(:register :rebase))
          (list :definition-request (fn-cp-nth 5 request) old))
         ((not (equal (fn-cp-nth 5 old) revision)) '(:refused :rebase-required))
         (t (list :definition-request (fn-cp-nth 8 old) old))))))

(defthm fn-cre-selected-existing-route-is-exact-account-and-consumer
 (implies (and old (eq (fn-cp-nth 0 (fn-cre-selected-route ingress old)) :definition-request))
  (and (eq (fn-cp-nth 0 ingress) :authenticated)
       (equal (fn-cp-nth 1 old) (fn-cp-nth 4 (fn-cp-nth 1 ingress)))
       (equal (fn-cp-nth 2 old) (fn-cp-nth 2 ingress))
       (equal (fn-cp-nth 9 old) (fn-cp-nth 3 ingress))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-cre-selected-route fn-cp-nth)
                              (fn-cbor-at-mostp len)))))

(local
 (defthm fn-cre-auth-has-no-ingress-tag
  (not (equal (car (fn-cra-authenticate cp epoch count pub login secret tls)) :authenticated))
  :hints (("Goal" :in-theory (e/d (fn-cra-authenticate)
                    (fn-cra-availablep fn-cai-namep fn-caa-current-binding
                     fn-cp-nth fn-authsec-checkp fn-auth-cred-secret
                     fn-auth-cred-name fn-auth-cred-principal))))))

(defthm fn-cre-ingress-authenticates-exact-named-current-account
 (let ((answer (fn-cre-ingress request tls g cp epoch count pub)))
  (implies (eq (car answer) :authenticated)
   (and (equal tls t) (fn-cre-envelopep request)
        (equal (fn-cra-authenticate cp epoch count pub
                 (fn-cp-nth 2 request) (fn-cp-nth 3 request) tls)
               (list :ok (fn-cp-nth 2 answer) (fn-cp-nth 3 answer)
                         (fn-cp-nth 4 answer) (fn-cp-nth 5 answer)))
        (equal (fn-cp-nth 1 answer) request))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-cra-authentication-uses-current-publication-by-definition
                       (login (fn-cp-nth 2 request)) (secret (fn-cp-nth 3 request))))
          :in-theory (e/d (fn-cre-ingress fn-cp-nth)
                          (fn-cra-authenticate fn-cre-envelopep)))))

(in-theory (disable fn-cre-envelopep fn-cre-header-plan fn-cre-ingress fn-cre-selected-route))
