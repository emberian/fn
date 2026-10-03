; Teeth for the per-connection authentication failure budget (sweep S044;
; books/nntp-auth.lisp fn-auth-failed, *fn-auth-failure-limit*).
;
; 1. KEYSTONE fn-auth-failed-pass-below-the-limit-is-481-and-keeps-the-connection
;    and KEYSTONE fn-auth-failed-pass-at-the-limit-is-481-400-and-closes:
;    a positive witness each, with every antecedent asserted, and one
;    hypothesis-removal witness per hypothesis (every retained hypothesis
;    holds, the omitted one fails, and so does the conclusion).
; 2. The served fold (fn-served-step, which host/native/owner.lisp
;    fnn-owner-handle-chunk runs for every read): ten pipelined
;    USER/PASS pairs with a wrong password in one read are answered with
;    exactly three 481 lines, then the 400, then the close; the line after
;    them is not answered.  A SASL failure counts against the same budget.
(in-package "ACL2")
(include-book "../../books/nntp-auth-fold")
(local (include-book "../../books/codec-attach"))

(defconst *fb-node* (fn-node-initial-state '("fn.letters") 1048576))
(defconst *fb-archive* (fn-node-acceptance *fb-node*))
(defconst *fb-verifier*
  (fn-authsec-verifier
   (make-list 16 :initial-element 3)
   '(42 82 187 10 181 221 230 125 199 188 135 91 193 55 205 245
     177 50 208 139 71 236 67 86 54 24 223 76 55 144 61 51)
   (car (fn-scram-keys (fn-nntp-string-octets "correct-horse")
                       (make-list 16 :initial-element 3) 4096))
   (cadr (fn-scram-keys (fn-nntp-string-octets "correct-horse")
                        (make-list 16 :initial-element 3) 4096))))
(defconst *fb-cred*
  (fn-auth-make-cred (fn-nntp-string-octets "reader")
                     (make-list 32 :initial-element 7) *fb-verifier* nil))
(defconst *fb-acfg* (fn-auth-make-config t nil t (list *fb-cred*)))
(defconst *fb-prot-acfg* (fn-auth-make-config t t t (list *fb-cred*)))
(defconst *fb-injection*
  (fn-inj-make-config t (fn-nntp-string-octets "fn.example.invalid")
                      (list (fn-nntp-string-octets "fn.letters")) 32768))
(defconst *fb-clock* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *fb-open*
  (fn-served-open *fb-archive* 510 32768 nil *fb-clock* *fb-injection*
                  *fb-acfg*))
(defconst *fb-conn* (fn-served-result-conn *fb-open*))
(defconst *fb-s0* (fn-served-conn-session *fb-conn*))
(assert-event (fn-auth-sessionp *fb-s0*))
(assert-event (equal (fn-auth-session-failures *fb-s0*) 0))
(assert-event (fn-auth-checkp *fb-cred* (fn-nntp-string-octets "correct-horse")))

(defun fb-o (s) (fn-nntp-string-octets s))
(defconst *fb-pass* (fb-o "PASS"))
(defconst *fb-wrong* (fb-o "wrong-horse"))

; A session with the name cached and N failures behind it.
(defun fb-at (n acfg tlsp)
  (fn-auth-make-session (fn-auth-session-base *fb-s0*) acfg (fb-o "reader")
                        nil tlsp nil nil nil n))

(defun fb-hyps (as keyword secret)
  ; The keystones' common hypotheses, in their order.
  (list (not (fn-auth-session-subject as))
        (not (and (fn-auth-config-protected-onlyp (fn-auth-session-config as))
                  (not (fn-auth-session-tlsp as))))
        (fn-auth-token-argp (list secret))
        (fn-nntp-keywordp keyword "PASS")
        (and (fn-auth-session-pending as) t)
        (not (fn-auth-checkp
              (fn-auth-find-cred (fn-auth-session-pending as)
                                 (fn-auth-config-creds (fn-auth-session-config as)))
              secret))))

(defun fb-below (as) (< (+ 1 (nfix (fn-auth-session-failures as))) *fn-auth-failure-limit*))

(defun fb-concl-below (as keyword secret)
  (let ((r (fn-auth-authinfo as (list keyword secret))))
    (and (equal (fn-post-result-effects r)
                (fn-auth-single as "481 authentication failed"))
         (equal (fn-auth-session-base (fn-post-result-session r))
                (fn-auth-session-base as)))))

(defun fb-concl-limit (as keyword secret)
  (let ((r (fn-auth-authinfo as (list keyword secret))))
    (and (equal (fn-post-result-effects r)
                (append (fn-auth-single as "481 authentication failed")
                        (fn-auth-single
                         as "400 too many authentication failures; closing connection")
                        (list (fn-nntp-close-effect))))
         (not (fn-nntp-session-openp
               (fn-auth-reader-session (fn-post-result-session r)))))))

; 1. Positive witnesses: every hypothesis holds and so does the conclusion.
(assert-event
 (let ((as (fb-at 1 *fb-acfg* nil)))
   (and (equal (fb-hyps as *fb-pass* *fb-wrong*) '(t t t t t t))
        (fb-below as)
        (fb-concl-below as *fb-pass* *fb-wrong*)
        (fn-nntp-session-openp
         (fn-auth-reader-session
          (fn-post-result-session (fn-auth-authinfo as (list *fb-pass* *fb-wrong*))))))))
(assert-event
 (let ((as (fb-at 2 *fb-acfg* nil)))
   (and (equal (fb-hyps as *fb-pass* *fb-wrong*) '(t t t t t t))
        (not (fb-below as))
        (fb-concl-limit as *fb-pass* *fb-wrong*))))

; Hypothesis removal, one per hypothesis, for each keystone.  WITNESS is
; (AS KEYWORD SECRET); I is the omitted hypothesis's position.
(defun fb-removal-okp (i as keyword secret limitp)
  (let ((h (fb-hyps as keyword secret)))
    (and (not (nth i h))
         (equal (remove-nth-fb i h) (make-list 5 :initial-element t))
         (if limitp
             (and (not (fb-below as)) (not (fb-concl-limit as keyword secret)))
           (and (fb-below as) (not (fb-concl-below as keyword secret)))))))

(defun remove-nth-fb (i xs)
  (if (zp i) (cdr xs) (cons (car xs) (remove-nth-fb (1- i) (cdr xs)))))

(defun fb-subject-at (n)
  (fn-auth-make-session (fn-auth-session-base *fb-s0*) *fb-acfg* (fb-o "reader")
                        (make-list 32 :initial-element 7) nil nil nil nil n))

(defun fb-removals (n limitp)
  (and
   ; 0: already authenticated: 502, nothing counted
   (fb-removal-okp 0 (fb-subject-at n) *fb-pass* *fb-wrong* limitp)
   ; 1: protected-only before TLS: 483
   (fb-removal-okp 1 (fb-at n *fb-prot-acfg* nil) *fb-pass* *fb-wrong* limitp)
   ; 2: no password token: 501
   (fb-removal-okp 2 (fb-at n *fb-acfg* nil) *fb-pass* nil limitp)
   ; 3: USER, not PASS: 381
   (fb-removal-okp 3 (fb-at n *fb-acfg* nil) (fb-o "USER") *fb-wrong* limitp)
   ; 4: no cached name: 482
   (fb-removal-okp 4 (fn-auth-make-session (fn-auth-session-base *fb-s0*) *fb-acfg*
                                           nil nil nil nil nil nil n)
                   *fb-pass* *fb-wrong* limitp)
   ; 5: the right password: 281
   (fb-removal-okp 5 (fb-at n *fb-acfg* nil) *fb-pass*
                   (fb-o "correct-horse") limitp)))

(assert-event (fb-removals 1 nil))
(assert-event (fb-removals 2 t))
; The limit hypothesis itself: below the limit the at-limit conclusion
; fails, at the limit the below-limit conclusion fails.
(assert-event
 (let ((as (fb-at 1 *fb-acfg* nil)))
   (and (equal (fb-hyps as *fb-pass* *fb-wrong*) '(t t t t t t))
        (fb-below as) (not (fb-concl-limit as *fb-pass* *fb-wrong*)))))
(assert-event
 (let ((as (fb-at 2 *fb-acfg* nil)))
   (and (equal (fb-hyps as *fb-pass* *fb-wrong*) '(t t t t t t))
        (not (fb-below as)) (not (fb-concl-below as *fb-pass* *fb-wrong*)))))

; 2. The served fold.
(include-book "arena-lift")
(defconst *sr-arena* nil)
(bpr-lift fn-served-step 2)
(defun fb-line (text) (append (fb-o text) '(13 10)))
(defun fb-pairs (n)
  (if (zp n) nil
    (append (fb-line "AUTHINFO USER reader") (fb-line "AUTHINFO PASS wrong-horse")
            (fb-pairs (1- n)))))
(defun fb-replies (effects)
  ; The reply lines' first three octets, in order.
  (if (atom effects) nil
    (if (and (consp (car effects)) (equal (caar effects) :reply))
        (cons (take 3 (cadar effects)) (fb-replies (cdr effects)))
      (fb-replies (cdr effects)))))
(defconst *fb-read* (append (fb-pairs 10) (fb-line "CAPABILITIES")))
(defmacro fb-step () '(in-arena-fn-served-step *sr-arena* *fb-conn* *fb-read*))
(assert-event
 (let ((effects (fn-served-result-effects (fb-step))))
   (and (equal (fb-replies effects)
               (list (fb-o "381") (fb-o "481") (fb-o "381") (fb-o "481")
                     (fb-o "381") (fb-o "481") (fb-o "400")))
        (member-equal (fn-nntp-close-effect) effects)
        (fn-served-quitp (fn-served-result-conn (fb-step))))))
; Mutation (labelled): without the budget -- a session whose count is
; reset before every PASS, which no transition produces -- the same read
; is answered pair after pair: three failures do not close it.
(assert-event
 (let* ((as (fb-at 0 *fb-acfg* nil))
        (r1 (fn-auth-authinfo as (list *fb-pass* *fb-wrong*)))
        (s1 (fn-post-result-session r1)))
   (and (equal (fn-auth-session-failures s1) 1)
        (fn-nntp-session-openp (fn-auth-reader-session s1)))))

; SASL: a failed exchange counts.  A PLAIN response with the wrong
; password, on a TLS session two failures in, closes the connection.
(assert-event
 (let* ((as (fn-auth-make-session (fn-auth-session-base *fb-s0*) *fb-acfg*
                                  '(:sasl-plain) nil t nil nil nil 2))
        (bad (append '(0) (fb-o "reader") '(0) *fb-wrong*))
        (r (fn-auth-sasl-continue as (fn-ot-b64-encode bad))))
   (and (equal (fn-auth-session-failures (fn-post-result-session r)) 3)
        (not (fn-nntp-session-openp
              (fn-auth-reader-session (fn-post-result-session r))))
        (member-equal (fn-nntp-close-effect) (fn-post-result-effects r)))))
