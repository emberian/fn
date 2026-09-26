; Teeth for books/peer-transit-forms.lisp (PRF-207): one admission decision,
; three wire forms.  Every witness is a computation through the function the
; host calls (`fn-peer-command', `fn-peer-step-pinned',
; `fn-peer-transit-outcome-effects') on a concrete node, configuration and
; session; every hypothesis has a removal witness and a must-fail.
(in-package "ACL2")
(include-book "../../books/peer-transit-forms")
(include-book "std/testing/must-fail" :dir :system)

(defun ptf-o (s) (fn-nntp-string-octets s))

; The peer record of tests/acl2/peer-inbound-tests.lisp: inbound fn.*, at
; most 32768 octets, at most 16 outstanding offers.
(defconst *ptf-peer*
  (fn-cfg-peer-make "innA" "inn.hbox.test" '(:nntp "127.0.0.1" 1119)
                    '("fn.*" 32768 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.1")))
(defconst *ptf-cfg*
  (fn-config-replay 0 510
                    (list (fn-cfg-record-make
                           0 0 1
                           (append *fn-cfg-default-change*
                                   (list (fn-cfg-set-policy "path-identity" "fnA.hbox.test")
                                         (fn-cfg-set-peer-delta *ptf-peer*)))
                           *fn-cfg-default-stamp*))))
(assert-event (fn-cfgp *ptf-cfg*))
(assert-event (equal (fn-cfg-peer-inbound-max-inflight *ptf-peer*) 16))
(defconst *ptf-node* (fn-node-initial-state '("fn.letters" "fn.test") 1048576))
(defconst *ptf-archive* (fn-node-acceptance *ptf-node*))
(defconst *ptf-ps* (fn-peer-open-session *ptf-archive* "innA" *ptf-node* *ptf-cfg*))
(assert-event (fn-peer-sessionp *ptf-ps*))
; The same connection with fifteen and sixteen 238s outstanding.
(defconst *ptf-ps15* (fn-peer-with-transfer *ptf-ps* nil 15))
(defconst *ptf-ps16* (fn-peer-with-transfer *ptf-ps* nil 16))
; A connection whose peer the configuration does not name.
(defconst *ptf-ghost* (fn-peer-open-session *ptf-archive* "ghost" *ptf-node* *ptf-cfg*))
(defconst *ptf-id* (ptf-o "<s1@example.invalid>"))
(defconst *ptf-args* (list *ptf-id*))
(defconst *ptf-bad-args* (list (ptf-o "not-a-message-id")))

(defun ptf-offer-d (ps args)
  (fn-peer-decide-offer (fn-peer-session-node ps) (fn-peer-session-cfg ps)
                        (fn-peer-session-peer ps) ps (car args) nil
                        (fn-peer-session-inflight ps)))
(defun ptf-code (ps k args)
  (fn-peer-wire-code (fn-post-result-effects (fn-peer-command ps (ptf-o k) args))))
; The theorem's full antecedent and conclusion on one (ps, ki, kc, args).
(defun ptf-k1-antecedent (ki kc args)
  (and (fn-nntp-keywordp ki "IHAVE") (fn-nntp-keywordp kc "CHECK")
       (fn-peer-msgid-argp args)))
(defun ptf-k1-conclusion (ps ki kc args)
  (let ((d (ptf-offer-d ps args))
        (ihave (fn-peer-wire-code (fn-post-result-effects (fn-peer-command ps ki args))))
        (check (fn-peer-wire-code (fn-post-result-effects (fn-peer-command ps kc args)))))
    (and (equal ihave (fn-peer-offer-code :ihave d))
         (equal check (fn-peer-offer-code :check d))
         (equal check (fn-peer-check-form ihave)))))

; -----------------------------------------------------------------------------
; KEYSTONE 1 (fn-peer-check-and-ihave-answer-one-offer-decision)

; Positive witnesses, one per decision kind, each with the whole antecedent
; and conclusion.  Wanted: 335 and 238.
(assert-event (ptf-k1-antecedent (ptf-o "IHAVE") (ptf-o "CHECK") *ptf-args*))
(assert-event (ptf-k1-conclusion *ptf-ps* (ptf-o "IHAVE") (ptf-o "CHECK") *ptf-args*))
(assert-event (equal (ptf-code *ptf-ps* "IHAVE" *ptf-args*) 335))
(assert-event (equal (ptf-code *ptf-ps* "CHECK" *ptf-args*) 238))
; Lower case is the same keyword (RFC 3977 section 3.1).
(assert-event (ptf-k1-conclusion *ptf-ps* (ptf-o "ihave") (ptf-o "check") *ptf-args*))
; Deferred (sixteen outstanding): 436 and 431.
(assert-event (ptf-k1-conclusion *ptf-ps16* (ptf-o "IHAVE") (ptf-o "CHECK") *ptf-args*))
(assert-event (equal (fn-peer-decision-kind (ptf-offer-d *ptf-ps16* *ptf-args*)) :defer))
(assert-event (equal (ptf-code *ptf-ps16* "IHAVE" *ptf-args*) 436))
(assert-event (equal (ptf-code *ptf-ps16* "CHECK" *ptf-args*) 431))
; Refused (not a peer): 435 and 438.
(assert-event (ptf-k1-conclusion *ptf-ghost* (ptf-o "IHAVE") (ptf-o "CHECK") *ptf-args*))
(assert-event (equal (ptf-code *ptf-ghost* "IHAVE" *ptf-args*) 435))
(assert-event (equal (ptf-code *ptf-ghost* "CHECK" *ptf-args*) 438))
; The CHECK reply echoes the Message-ID (RFC 4644 section 2.4).
(assert-event (equal (fn-post-result-effects (fn-peer-command *ptf-ps* (ptf-o "CHECK") *ptf-args*))
                     (list (fn-nntp-reply-effect
                            (fn-nntp-crlf (append (ptf-o "238 ") *ptf-id*))))))

; Tooth, hypothesis (fn-nntp-keywordp ki "IHAVE"): ki is MODE; the other two
; hold, the omitted one fails, and so does the conclusion (MODE <id> is not
; a transit command: no reply from this layer, no code).
(assert-event (and (fn-nntp-keywordp (ptf-o "CHECK") "CHECK")
                   (fn-peer-msgid-argp *ptf-args*)
                   (not (fn-nntp-keywordp (ptf-o "MODE") "IHAVE"))
                   (not (ptf-k1-conclusion *ptf-ps* (ptf-o "MODE") (ptf-o "CHECK") *ptf-args*))))
(must-fail
 (defthm ptf-k1-without-ihave
   (implies (and (fn-nntp-keywordp kc "CHECK") (fn-peer-msgid-argp args))
            (ptf-k1-conclusion ps ki kc args))
   :hints (("Goal" :in-theory (disable fn-peer-command fn-peer-decide-offer)))))

; Tooth, hypothesis (fn-nntp-keywordp kc "CHECK"): kc is IHAVE too.
(assert-event (and (fn-nntp-keywordp (ptf-o "IHAVE") "IHAVE")
                   (fn-peer-msgid-argp *ptf-args*)
                   (not (fn-nntp-keywordp (ptf-o "IHAVE") "CHECK"))
                   (not (ptf-k1-conclusion *ptf-ps* (ptf-o "IHAVE") (ptf-o "IHAVE") *ptf-args*))))
(must-fail
 (defthm ptf-k1-without-check
   (implies (and (fn-nntp-keywordp ki "IHAVE") (fn-peer-msgid-argp args))
            (ptf-k1-conclusion ps ki kc args))
   :hints (("Goal" :in-theory (disable fn-peer-command fn-peer-decide-offer)))))

; Tooth, hypothesis (fn-peer-msgid-argp args): both answer 501, which the
; offer decision (a Message-ID syntax refusal, 435 / 438) does not name.
(assert-event (and (fn-nntp-keywordp (ptf-o "IHAVE") "IHAVE")
                   (fn-nntp-keywordp (ptf-o "CHECK") "CHECK")
                   (not (fn-peer-msgid-argp *ptf-bad-args*))
                   (not (ptf-k1-conclusion *ptf-ps* (ptf-o "IHAVE") (ptf-o "CHECK") *ptf-bad-args*))
                   (equal (ptf-code *ptf-ps* "IHAVE" *ptf-bad-args*) 501)
                   (equal (ptf-code *ptf-ps* "CHECK" *ptf-bad-args*) 501)))
(must-fail
 (defthm ptf-k1-without-msgid
   (implies (and (fn-nntp-keywordp ki "IHAVE") (fn-nntp-keywordp kc "CHECK"))
            (ptf-k1-conclusion ps ki kc args))
   :hints (("Goal" :in-theory (disable fn-peer-decide-offer)))))

; -----------------------------------------------------------------------------
; KEYSTONE 2 (fn-peer-takethis-and-ihave-answer-one-transfer-verdict)

(defun ptf-k2 (d completion)
  (let ((ihave (fn-peer-transit-outcome-effects
                *ptf-ps* (fn-peer-make-submission "innA" :ihave *ptf-id* nil) d completion))
        (takethis (fn-peer-transit-outcome-effects
                   *ptf-ps* (fn-peer-make-submission "innA" :takethis *ptf-id* nil) d completion)))
    (list (fn-peer-wire-code ihave) (fn-peer-wire-code takethis)
          (and (member-equal (fn-nntp-close-effect) ihave) t)
          (and (member-equal (fn-nntp-close-effect) takethis) t))))
; Accepted, durable: 235 / 239.  Deferred before any attempt: 436 / 436.
; Refused: 437 / 439.  Refused by the store: 437 / 439.  Uncertain: 436 and
; a close on both.
(assert-event (equal (ptf-k2 (fn-peer-decision :want nil) :durable) '(235 239 nil nil)))
(assert-event (equal (ptf-k2 (fn-peer-decision :defer :busy) nil) '(436 436 nil nil)))
(assert-event (equal (ptf-k2 (fn-peer-decision :refuse :loop) nil) '(437 439 nil nil)))
(assert-event (equal (ptf-k2 (fn-peer-decision :have :history) nil) '(437 439 nil nil)))
(assert-event (equal (ptf-k2 (fn-peer-decision :want nil) :refused) '(437 439 nil nil)))
(assert-event (equal (ptf-k2 (fn-peer-decision :want nil) :uncertain) '(436 436 t t)))
; No hypothesis.  Tooth: the stronger claim that the two forms answer the
; same code is false, and the durable case says so.
(must-fail
 (defthm ptf-k2-same-code
   (equal (fn-peer-wire-code (fn-peer-transit-outcome-effects
                              ps (fn-peer-make-submission peer :takethis msgid octets) d completion))
          (fn-peer-wire-code (fn-peer-transit-outcome-effects
                              ps (fn-peer-make-submission peer :ihave msgid octets) d completion)))
   :hints (("Goal" :in-theory (disable fn-peer-transit-outcome-effects)))))

; -----------------------------------------------------------------------------
; The submission (fn-peer-transfer-submission-differs-only-in-form-unfolds):
; a TAKETHIS article and an IHAVE article reach the owner as the same
; (peer, Message-ID, octets).
(defconst *ptf-lines*
  (list (ptf-o "Newsgroups: fn.test") (ptf-o "Message-ID: <s1@example.invalid>")
        (ptf-o "") (ptf-o "body")))
(defun ptf-sub (kind)
  (fn-post-result-submission
   (fn-peer-step-pinned (fn-peer-with-transfer *ptf-ps* (list kind *ptf-id*) 0)
                        *ptf-archive* nil nil nil nil nil (list :article *ptf-lines*))))
(assert-event (fn-peer-sessionp (fn-peer-with-transfer *ptf-ps* (list :takethis *ptf-id*) 0)))
(assert-event (equal (ptf-sub :takethis)
                     (fn-peer-make-submission "innA" :takethis *ptf-id*
                                              (fn-post-body-octets *ptf-lines*))))
(assert-event (equal (ptf-sub :ihave)
                     (fn-peer-make-submission "innA" :ihave *ptf-id*
                                              (fn-post-body-octets *ptf-lines*))))

; -----------------------------------------------------------------------------
; KEYSTONE 3 (fn-peer-step-pinned-keeps-outstanding-offers-within-the-peer-bound)

(defun ptf-step (ps line)
  (fn-peer-step-pinned ps *ptf-archive* nil nil nil nil nil (list :command (ptf-o line))))
(defun ptf-inflight (r) (fn-peer-session-inflight (fn-post-result-session r)))
; A pipeline at the bound: the fifteenth-to-sixteenth CHECK is promised
; (238, count 16 = max-inflight), the next is 431 and the count stays 16;
; a TAKETHIS retires one promise.
(assert-event (equal (ptf-inflight (ptf-step *ptf-ps15* "CHECK <s1@example.invalid>")) 16))
(assert-event (equal (fn-post-result-effects (ptf-step *ptf-ps15* "CHECK <s1@example.invalid>"))
                     (list (fn-nntp-reply-effect (fn-nntp-crlf (append (ptf-o "238 ") *ptf-id*))))))
(assert-event (equal (ptf-inflight (ptf-step *ptf-ps16* "CHECK <s1@example.invalid>")) 16))
(assert-event (equal (fn-post-result-effects (ptf-step *ptf-ps16* "CHECK <s1@example.invalid>"))
                     (list (fn-nntp-reply-effect (fn-nntp-crlf (append (ptf-o "431 ") *ptf-id*))))))
(assert-event (equal (ptf-inflight (ptf-step *ptf-ps16* "TAKETHIS <s1@example.invalid>")) 15))
; No hypothesis.  Tooth: the stronger claim that no event raises the count
; is false; the counterexample is the witness above (the 238 raised it from
; 15 to 16), and the claim is not a theorem.
(assert-event (not (<= (ptf-inflight (ptf-step *ptf-ps15* "CHECK <s1@example.invalid>"))
                       (fn-peer-session-inflight *ptf-ps15*))))
(must-fail
 (defthm ptf-k3-never-raises
   (<= (nfix (fn-peer-session-inflight
              (fn-post-result-session
               (fn-peer-step-pinned ps archive index verdicts config observation
                                    injection wire-event))))
       (nfix (fn-peer-session-inflight ps)))
   :hints (("Goal" :in-theory (disable fn-peer-step-pinned)))))
