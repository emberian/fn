; A reader with no posting credential can still become an authorized transit
; peer through a principal binding.  This is a counterexample to the former
; OB-AUTH-FOLD claim of no submission of any kind, over a complete served read.
(in-package "ACL2")
(include-book "../../books/nntp-auth-fold")
(local (include-book "../../books/codec-attach"))
(include-book "std/testing/must-fail" :dir :system)

(defconst *aft-node* (fn-node-initial-state '("fn.letters") 1048576))
(defconst *aft-archive* (fn-node-acceptance *aft-node*))
(defconst *aft-principal* (make-list 32 :initial-element 7))
(defconst *aft-principal-hex* (fn-digest-hex *aft-principal*))
(defconst *aft-peer*
  (fn-cfg-peer-make "principal-peer" "principal.example.invalid"
                    '(:nntp "127.0.0.1" 119) '("fn.*" 32768 16) nil
                    (list :principal *aft-principal-hex*)))
(defconst *aft-cfg*
  (fn-config-replay
   0 510
   (list (fn-cfg-record-make
          0 0 1
          (append *fn-cfg-default-change* (list (fn-cfg-set-peer-delta *aft-peer*)))
          *fn-cfg-default-stamp*))))
(defconst *aft-secret* (fn-nntp-string-octets "correct-horse"))
(defconst *aft-verifier*
  (fn-authsec-verifier
   (make-list 16 :initial-element 3)
   '(60 237 250 71 154 204 168 180 72 224 241 93 232 185 72 59
     73 5 240 237 54 116 175 93 127 219 39 238 113 83 63 194)))
(defconst *aft-cred*
  (fn-auth-make-cred (fn-nntp-string-octets "reader") *aft-principal*
                     *aft-verifier* nil))
(defconst *aft-acfg* (fn-auth-make-config t nil t (list *aft-cred*)))
(defconst *aft-injection*
  (fn-inj-make-config t (fn-nntp-string-octets "fn.example.invalid")
                      (list (fn-nntp-string-octets "fn.letters")) 32768))
(defconst *aft-clock* (fn-clock-observation 1000000 843004800000 500 t))
(assert-event (fn-auth-configp *aft-acfg*))
(assert-event (fn-auth-config-requiredp *aft-acfg*))
(assert-event (not (fn-auth-cred-postingp *aft-cred*)))
(assert-event (fn-auth-checkp *aft-cred* *aft-secret*))
(assert-event (equal (fn-auth-principal-match *aft-principal* *aft-cfg*)
                     "principal-peer"))

(defconst *aft-open*
  (fn-served-open-peer *aft-archive* 510 32768 *aft-injection*
                       *aft-clock* *aft-clock* nil *aft-node* *aft-cfg*
                       *aft-acfg*))
(assert-event (fn-served-connp (fn-served-result-conn *aft-open*)))
(assert-event (fn-auth-fold-safe-connp (fn-served-result-conn *aft-open*)))
(assert-event (null (fn-auth-session-peer
                     (fn-served-conn-session
                      (fn-served-result-conn *aft-open*)))))
(assert-event (equal (fn-wire-state-mode
                      (fn-served-conn-wire (fn-served-result-conn *aft-open*)))
                     :command))

(defun aft-line (text)
  (append (fn-nntp-string-octets text) '(13 10)))
(defconst *aft-read*
  (append (aft-line "AUTHINFO USER reader")
          (aft-line "AUTHINFO PASS correct-horse")
          (aft-line "TAKETHIS <fresh@example.invalid>")
          (aft-line "Message-ID: <fresh@example.invalid>")
          (aft-line "Newsgroups: fn.letters")
          '(13 10)
          (aft-line "body")
          (aft-line ".")))
(defmacro aft-served-read ()
  '(fn-served-step (fn-served-result-conn *aft-open*) *aft-read*))
(assert-event
 (equal (fn-auth-session-peer
         (fn-served-conn-session (fn-served-result-conn (aft-served-read))))
        "principal-peer"))
(assert-event
 (fn-peer-submissionp
  (fn-served-submission (fn-served-result-effects (aft-served-read)))))
(assert-event
 (not (fn-inj-injectedp
       (fn-served-submission (fn-served-result-effects (aft-served-read))))))
(assert-event
 (fn-auth-fold-no-local-effectsp
  (fn-served-result-effects (aft-served-read))))
(assert-event
 (fn-auth-fold-no-local-effectsp
  (fn-served-result-effects
   (fn-served-step
    (fn-served-result-conn *aft-open*)
    (append (aft-line "AUTHINFO USER reader")
            (aft-line "AUTHINFO PASS correct-horse")
            (aft-line "POST"))))))

; Removing the no-posters authority premise permits a real authenticated
; local POST to complete in the same read.  This is a complete served fold,
; with the same nonempty credential list and source-bound configuration.
(defconst *aft-poster-cred*
  (fn-auth-make-cred (fn-nntp-string-octets "reader") *aft-principal*
                     *aft-verifier* t))
(defconst *aft-poster-acfg*
  (fn-auth-make-config t nil t (list *aft-poster-cred*)))
(defconst *aft-poster-open*
  (fn-served-open-peer *aft-archive* 510 32768 *aft-injection*
                       *aft-clock* *aft-clock* nil *aft-node* *aft-cfg*
                       *aft-poster-acfg*))
(defconst *aft-post-read*
  (append (aft-line "AUTHINFO USER reader")
          (aft-line "AUTHINFO PASS correct-horse")
          (aft-line "POST")
          (aft-line "From: reader@example.invalid")
          (aft-line "Subject: auth fold witness")
          (aft-line "Message-ID: <post@example.invalid>")
          (aft-line "Newsgroups: fn.letters")
          '(13 10)
          (aft-line "body")
          (aft-line ".")))
(defmacro aft-post-served-read ()
  '(fn-served-step (fn-served-result-conn *aft-poster-open*)
                   *aft-post-read*))
(defmacro aft-poster-login ()
  '(fn-served-step
    (fn-served-result-conn *aft-poster-open*)
    (append (aft-line "AUTHINFO USER reader")
            (aft-line "AUTHINFO PASS correct-horse"))))
(defmacro aft-poster-offer ()
  '(fn-served-step (fn-served-result-conn (aft-poster-login))
                   (aft-line "POST")))
(assert-event
 (equal (fn-wire-state-mode
         (fn-served-conn-wire (fn-served-result-conn (aft-poster-offer))))
        :article))
(assert-event
 (not (fn-auth-config-no-postersp *aft-poster-acfg*)))
(assert-event
 (fn-inj-injectedp
  (fn-served-submission
   (fn-served-result-effects (aft-post-served-read)))))
(assert-event
 (not (fn-auth-fold-no-local-effectsp
       (fn-served-result-effects (aft-post-served-read)))))
(local
 (must-fail
  (defthm aft-step-without-safe-connection-premise
    (fn-auth-fold-no-local-effectsp
     (fn-served-result-effects
      (fn-served-step (fn-served-result-conn *aft-poster-open*)
                      *aft-post-read*))))))
