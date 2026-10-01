(in-package "ACL2")
(include-book "../../books/consumer-account-auth")
(include-book "consumer-account-adoption-tests")
(include-book "../../books/consumer-authority-revision")

(defconst *crat-secret* '(115 101 99 114 101 116))
(defun fn-crat-row-op (login birth principal)
  (list :authority-row '(65) 0 login birth principal *caat-16*
        (fn-authsec-digest *caat-16* *crat-secret*) *caat-32* *caat-32* 1))
 ; The real digest attachment cannot be baked into DEFCONST. Build this
; model lifecycle inside each top-level fixture evaluation, as auth-secret's
; existing concrete tests do. No attachment-dependent logical axiom is added.
(defun fn-crat-fenced ()
  (let* ((begin (fn-caat-next *caat-initial* 1 '(:authority-begin (65) 0 1 7)))
         (one (fn-caat-next begin 2 (fn-crat-row-op '(97) 2 *caat-32*)))
         (two (fn-caat-next one 3 (fn-crat-row-op '(98) 3
                                                  (make-list 32 :initial-element 10))))
         (sealed (fn-caat-seal two 4))
         (prepared (fn-caat-next sealed 5 '(:authority-prepare (65) 0)))
         (ready (fn-caat-next prepared 6 '(:authority-prepare (65) 0))))
    (fn-caat-fence ready 7)))
(defun fn-crat-cp () (fn-cp-nth 1 (fn-crat-fenced)))
(defun fn-crat-root () (fn-cp-nth 2 (fn-crat-fenced)))
(defun fn-crat-pub ()
  (let ((cp (fn-crat-cp)))
    (list :ready 3 (fn-cp-nth 3 (fn-cp-nth 6 cp))
          (fn-cp-nth 1 (fn-cp-nth 6 cp)) (fn-cp-nth 3 cp) (fn-crat-root))))

; This exercises actual durable-step model constructors, not a forged ready
; account graph. Owner installation/funding/TLS/native reachability is separate.
;@positive fn-cra-authentication-uses-current-publication-by-definition
(assert-event
 (let* ((login '(97)) (b (fn-caa-current-binding login (fn-crat-root)))
        (r (fn-cp-nth 1 b)) (c (fn-cp-nth 2 b))
        (answer (fn-cra-authenticate (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp))
                                    (fn-crat-pub) login *crat-secret* t)))
   (and (fn-cp-statep (fn-crat-cp)) (eq (car (fn-crat-fenced)) :ok)
        (eq (car answer) :ok) (equal t t)
        (fn-cra-availablep (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub))
        (fn-cai-namep login *fn-auth-max-name-octets*)
        (fn-cp-nth 3 r) c (equal login (fn-cp-nth 1 r))
        (equal login (fn-auth-cred-name c))
        (fn-authsec-checkp (fn-auth-cred-secret c) *crat-secret*)
        (equal answer (list :ok (fn-auth-cred-principal c) (fn-cp-nth 2 r)
                            (fn-cp-nth 2 (fn-crat-pub)) (fn-cp-nth 3 (fn-crat-pub)))))))

; Equal passwords authenticate only the explicit account's own principal/token.
(assert-event
 (let ((a (fn-cra-authenticate (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub)
                              '(97) *crat-secret* t))
       (b (fn-cra-authenticate (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub)
                              '(98) *crat-secret* t)))
   (and (eq (car a) :ok) (eq (car b) :ok)
        (equal (fn-cp-nth 1 a) *caat-32*)
        (equal (fn-cp-nth 1 b) (make-list 32 :initial-element 10))
        (not (equal (fn-cp-nth 2 a) (fn-cp-nth 2 b))))))

(assert-event
 (and (equal (fn-cra-authenticate (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub)
                                  '(97) '(120) t) '(:refused :authentication))
      (equal (fn-cra-authenticate (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub)
                                  '(99) *crat-secret* t) '(:refused :authentication))
      (equal (fn-cra-authenticate (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub)
                                  '(97) *crat-secret* nil) '(:refused :protected-channel))))

; Freshness: every resumed WAIT must call again with current epoch and CP.
; A prior ready root cannot be authorized after reset or semantic revision.
(assert-event
 (and (equal (fn-cra-authenticate (fn-crat-cp) 4 (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub)
                                  '(97) *crat-secret* t) '(:unavailable :account-authority))
      (equal (fn-cra-authenticate
              (fn-carv-revision-state (fn-crat-cp) 2) 3 (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub)
              '(97) *crat-secret* t) '(:unavailable :account-authority))))

;@hypothesis-removal fn-cra-authentication-uses-current-publication-by-definition accepted-result
(assert-event
 (let ((answer (fn-cra-authenticate (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp))
                                    (fn-crat-pub) '(97) *crat-secret* nil)))
   (and (not (eq (car answer) :ok))
        (not (equal nil t)))))

; Corrupted-state witness: a credential for another exact name is never
; accepted through this alias, even with the correct matching password.
(assert-event
 (let* ((b (fn-caa-current-binding '(98) (fn-crat-root)))
        (alias-root (fn-caa-root 7 (fn-cai-put-octets '(97) b
                                      (fn-caa-root-index (fn-crat-root)))
                                (fn-cp-nth 3 (fn-crat-root))))
        (alias-pub (list :ready 3 (fn-cp-nth 2 (fn-crat-pub))
                         (fn-cp-nth 3 (fn-crat-pub)) (fn-cp-nth 4 (fn-crat-pub)) alias-root)))
   (and (fn-cra-availablep (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp)) alias-pub)
        (equal (fn-cra-authenticate (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp)) alias-pub
                                    '(97) *crat-secret* t)
               '(:refused :authentication)))))

(defun fn-crat-auth-conclusion (login secret tls pub rows watermark)
  (let* ((b (fn-caa-current-binding login (fn-cp-nth 5 pub)))
         (r (fn-cp-nth 1 b)) (c (fn-cp-nth 2 b))
         (answer (fn-cra-authenticate (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp))
                                     pub login secret tls)))
    (and (member-equal r rows) (fn-caar-bindingp r b watermark)
         (equal (fn-cp-nth 1 r) login) (fn-cp-nth 3 r)
         (equal (fn-cp-nth 1 answer) (fn-auth-cred-principal c))
         (equal (fn-cp-nth 2 answer) (fn-cp-nth 2 r)))))

;@positive fn-cra-authentication-is-adopted-live-account
(assert-event
 (let ((rows (fn-cp-nth 4 (fn-cp-nth 6 (fn-crat-cp))))
       (watermark (fn-cp-nth 2 (fn-cp-nth 6 (fn-crat-cp)))))
   (and (fn-caar-root-relp rows watermark (fn-crat-root))
        (eq (car (fn-cra-authenticate (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp))
                                     (fn-crat-pub) '(97) *crat-secret* t)) :ok)
        (fn-crat-auth-conclusion '(97) *crat-secret* t (fn-crat-pub) rows watermark))))

;@hypothesis-removal fn-cra-authentication-is-adopted-live-account accepted-result
(assert-event
 (let ((rows (fn-cp-nth 4 (fn-cp-nth 6 (fn-crat-cp))))
       (watermark (fn-cp-nth 2 (fn-cp-nth 6 (fn-crat-cp)))))
   (and (fn-caar-root-relp rows watermark (fn-crat-root))
        (not (eq (car (fn-cra-authenticate (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp))
                                          (fn-crat-pub) '(97) *crat-secret* nil)) :ok))
        (not (fn-crat-auth-conclusion '(97) *crat-secret* nil
                                      (fn-crat-pub) rows watermark)))))

; Corrupted-state hypothesis removal: an otherwise valid phantom account
; can pass local bounded credential tests, but is not durable adopted authority.
; The owner must establish the complete relation rather than recognize it here.
;@hypothesis-removal fn-cra-authentication-is-adopted-live-account complete-relation
(assert-event
 (let* ((b (fn-caa-current-binding '(97) (fn-crat-root)))
        (oldrow (fn-cp-nth 1 b)) (oldcred (fn-cp-nth 2 b))
        (cred (fn-auth-make-cred '(99) (fn-auth-cred-principal oldcred)
                                (fn-auth-cred-secret oldcred) t))
        (row (list :account '(99) (fn-cp-nth 2 oldrow) t
                   (fn-caar-credential-descriptor cred)))
        (root (fn-caa-root 7
                  (fn-cai-put-octets '(99) (list :account-binding row cred)
                                    (fn-caa-root-index (fn-crat-root)))
                  (cons cred (fn-cp-nth 3 (fn-crat-root)))))
        (pub (list :ready 3 (fn-cp-nth 2 (fn-crat-pub)) (fn-cp-nth 3 (fn-crat-pub))
                   (fn-cp-nth 4 (fn-crat-pub)) root))
        (rows (fn-cp-nth 4 (fn-cp-nth 6 (fn-crat-cp))))
        (watermark (fn-cp-nth 2 (fn-cp-nth 6 (fn-crat-cp)))))
   (and (not (fn-caar-root-relp rows watermark root))
        (eq (car (fn-cra-authenticate (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp))
                                     pub '(99) *crat-secret* t)) :ok)
        (not (fn-crat-auth-conclusion '(99) *crat-secret* t pub rows watermark)))))
