; Current committed account authority for each FNCR request and WAIT wake.
; Publication6 is owner-maintained (:ready epoch namespace revision fence-count
; root4). These scalar checks consume its carried establishment relation; they
; neither recognize the account graph nor manufacture a ready publication.
(in-package "ACL2")
(include-book "consumer-account-relation")

(defun fn-cra-availablep (cp epoch event-count publication)
  (declare (xargs :guard t))
  (let ((authority (fn-cp-nth 6 cp)))
    (and (eq (fn-cp-nth 0 publication) :ready)
         (natp epoch) (equal epoch (fn-cp-nth 1 publication))
         (fn-cp-nth 3 authority)
         (equal (fn-cp-nth 3 authority) (fn-cp-nth 2 publication))
         (equal (fn-cp-nth 1 authority) (fn-cp-nth 3 publication))
         (natp event-count) (natp (fn-cp-nth 4 publication))
         (<= (fn-cp-nth 4 publication) event-count)
         (fn-cp-nth 5 publication) t)))

; Login and secret are the current request's admitted octets. Every call,
; including a WAIT resumption, performs this lookup/comparison anew. No
; previously authenticated session or cursor supplies account authority.
; The root's maintained relation supplies credential validity and exact
; row/name/descriptor coverage; bounded name checks additionally fail closed
; on an incorrectly installed alias. Funding is a separate caller premise.
(defun fn-cra-authenticate (cp epoch event-count publication login secret protectedp)
  (declare (xargs :guard t))
  (cond
   ((not (eq protectedp t)) (list :refused :protected-channel))
   ((not (fn-cra-availablep cp epoch event-count publication))
    (list :unavailable :account-authority))
   ((not (fn-cai-namep login *fn-auth-max-name-octets*))
    (list :refused :authentication))
   (t
    (let* ((binding (fn-caa-current-binding login (fn-cp-nth 5 publication)))
           (row (fn-cp-nth 1 binding)) (credential (fn-cp-nth 2 binding)))
      (if (and binding credential (eq (fn-cp-nth 0 binding) :account-binding)
               (equal login (fn-cp-nth 1 row))
               (equal login (fn-auth-cred-name credential))
               (fn-authsec-checkp (fn-auth-cred-secret credential) secret))
          (list :ok (fn-auth-cred-principal credential) (fn-cp-nth 2 row)
                (fn-cp-nth 2 publication) (fn-cp-nth 3 publication))
        (list :refused :authentication))))))

; Exact boundary facts; these do not establish owner publication reachability.
(defthm fn-cra-authentication-uses-current-publication-by-definition
  (implies (eq (car (fn-cra-authenticate cp epoch count pub login secret tls)) :ok)
           (and (eq tls t) (fn-cra-availablep cp epoch count pub)
                (fn-cai-namep login *fn-auth-max-name-octets*)
                (let* ((b (fn-caa-current-binding login (fn-cp-nth 5 pub)))
                       (r (fn-cp-nth 1 b)) (c (fn-cp-nth 2 b)))
                  (and (fn-cp-nth 3 r) c
                       (equal login (fn-cp-nth 1 r))
                       (equal login (fn-auth-cred-name c))
                       (fn-authsec-checkp (fn-auth-cred-secret c) secret)
                       (equal (fn-cra-authenticate cp epoch count pub login secret tls)
                              (list :ok (fn-auth-cred-principal c) (fn-cp-nth 2 r)
                                    (fn-cp-nth 2 pub) (fn-cp-nth 3 pub)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-cra-authenticate fn-caa-current-binding)
                (fn-cra-availablep fn-cai-namep fn-cai-lookup fn-cp-nth
                 fn-auth-cred-name fn-auth-cred-secret fn-auth-cred-principal
                 fn-authsec-checkp)))))

(defthm fn-cra-authentication-is-adopted-live-account
  (implies
   (and (fn-caar-root-relp (fn-cp-nth 4 (fn-cp-nth 6 cp))
                            (fn-cp-nth 2 (fn-cp-nth 6 cp)) (fn-cp-nth 5 pub))
        (eq (car (fn-cra-authenticate cp epoch count pub login secret tls)) :ok))
   (let* ((b (fn-caa-current-binding login (fn-cp-nth 5 pub)))
          (r (fn-cp-nth 1 b))
          (c (fn-cp-nth 2 b)))
     (and (member-equal r (fn-cp-nth 4 (fn-cp-nth 6 cp)))
          (fn-caar-bindingp r b (fn-cp-nth 2 (fn-cp-nth 6 cp)))
          (equal (fn-cp-nth 1 r) login) (fn-cp-nth 3 r)
          (equal (fn-cp-nth 1 (fn-cra-authenticate cp epoch count pub login secret tls))
                 (fn-auth-cred-principal c))
          (equal (fn-cp-nth 2 (fn-cra-authenticate cp epoch count pub login secret tls))
                 (fn-cp-nth 2 r)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cra-authentication-uses-current-publication-by-definition)
                 (:instance fn-caar-current-binding-is-adopted-live-account
                            (name login) (root (fn-cp-nth 5 pub))
                            (rows (fn-cp-nth 4 (fn-cp-nth 6 cp)))
                            (watermark (fn-cp-nth 2 (fn-cp-nth 6 cp)))))
           :in-theory
           (e/d (fn-cp-nth)
                (fn-cra-authenticate fn-cra-availablep fn-caar-root-relp
                 fn-caa-current-binding fn-caar-bindingp fn-auth-cred-principal)))))

(in-theory (disable fn-cra-availablep fn-cra-authenticate))
