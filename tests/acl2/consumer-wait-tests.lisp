; Teeth for books/consumer-wait.lisp (PRF-252, CNS-007): a consumer wait.
; The subjects are what host/owner-host.lisp calls:
; fn-owner-consumer-local-wait-step calls fn-cwait-step (fn-cwait-step-over
; once the host lane switches it, flip-bridge's REQUEST; its loop is
; fn-cwait-run-over) and
; fn-owner-consumer-local-wait-admit calls fn-cwait-admit (both from
; host/native/owner.lisp fnn-owner-consumer-local-wait).
;
; A committed Store with two groups and two consumers, before and after the
; public article arrives:
;
;   "1"  query fn.private.x  unbound (the operator's; a plain wait)
;   "2"  query fn.public     bound to bob (a bound wait)
(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "../../books/consumer-wait")
; The record and statement decoders execute through their attachments.
(include-book "../../books/codec-attach")

; --- the Store ---------------------------------------------------------------
(defun cwt-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defun cwt-commit (s event)
  (fn-sn-finish
   (fn-sn-io
    (fn-sn-io
     (fn-sn-io (fn-sn-prepare-consumer (cwt-reserve s) event)
               :record-file :ok)
     :record-link :ok)
    :record-directory :ok)))
(defun cwt-article (s record)
  (fn-sn-finish
   (fn-sn-io
    (fn-sn-io
     (fn-sn-io (fn-sn-prepare (cwt-reserve s) record) :record-file :ok)
     :record-link :ok)
    :record-directory :ok)))
(defun cwt-register (s id group)
  (let ((d (fn-col-register (fn-own-start s 2) 256 id group)))
    (if (eq (car d) :write) (cwt-commit s (cadr d)) s)))

(defconst *cwt-public* '(102 110 46 112 117 98 108 105 99))           ; fn.public
(defconst *cwt-private* '(102 110 46 112 114 105 118 97 116 101 46 120)) ; fn.private.x
(defconst *cwt-c1* '(49))
(defconst *cwt-c2* '(50))

(defconst *cwt-empty*
  (cwt-register
   (cwt-register
    (cwt-commit (fn-sn-initial '("fn.public" "fn.private.x") 16)
                (fn-cpe-make 0 0 0 '(:bootstrap (1) (2))))
    *cwt-c1* *cwt-private*)
   *cwt-c2* *cwt-public*))
(defconst *cwt-full*
  (cwt-article *cwt-empty*
               ; The Store retains the HELD row (records flip): the news at
               ; arena handle 0 (fn-held-plain), its payload sealed there below.
               (fn-held-plain (fn-record-make 3 3 3 "<news@fn.test>" '(78)
                                              '("fn.public") "news-pin" "news-content"
                                              "news-release" 1 841000000)
                              0)))
; Both registrations and the article committed: frontier 4.
(assert-event (equal (fn-cp-nth 3 (fn-sn-consumer *cwt-full*)) 4))

; --- the configuration: "2" bound to bob, who reads fn.* but not fn.private.*
(defconst *cwt-v*
  (let ((v (fn-cfg-value (fn-cfg-initial))))
    (fn-cfg-value-make-full (fn-cfg-groups v) (fn-cfg-capacity v)
                            (fn-cfg-quotas v) (fn-cfg-policies v)
                            (fn-cfg-listeners v) (fn-cfg-peers v)
                            (fn-cfg-limits v) (fn-cfg-authorities v)
                            (fn-cfg-invitations v)
                            (list (fn-cfg-row-make "bob" "fn.*,!fn.private.*" "fn.*" 3)
                                  (fn-cfg-row-make "2" "bob" "" 6))
                            (fn-cfg-descriptions v))))
(assert-event
 (equal (fn-cfg-apply-delta
         (fn-cfg-apply-delta (fn-cfg-value (fn-cfg-initial)) 1 0
                             (fn-cfg-account-access "bob" "fn.*,!fn.private.*" "fn.*"))
         2 0 (fn-cfg-consumer-bind "2" "bob"))
        *cwt-v*))
(defconst *cwt-oc-empty*
  (fn-ocfg-make (fn-own-start *cwt-empty* 2) (fn-cfg-make 2 *cwt-v*) nil nil))
(defconst *cwt-oc-full*
  (fn-ocfg-make (fn-own-start *cwt-full* 2) (fn-cfg-make 2 *cwt-v*) nil nil))

; --- credentials (books/nntp-auth-teeth-tests' verifier literal) -------------
(defconst *cwt-secret* (fn-nntp-string-octets "correct-horse"))
(defconst *cwt-wrong* (fn-nntp-string-octets "wrong-horse"))
(defconst *cwt-salt* (make-list 16 :initial-element 3))
(defconst *cwt-verifier*
  (fn-authsec-verifier
   *cwt-salt*
   '(60 237 250 71 154 204 168 180 72 224 241 93 232 185 72 59
     73 5 240 237 54 116 175 93 127 219 39 238 113 83 63 194)))
(assert-event (equal *cwt-verifier* (fn-authsec-enrol *cwt-salt* *cwt-secret*)))
(defconst *cwt-acfg*
  (fn-auth-make-config
   t nil t
   (list (fn-auth-make-cred (fn-nntp-string-octets "bob")
                            (make-list 32 :initial-element 8) *cwt-verifier* t))))
(assert-event (fn-auth-configp *cwt-acfg*))

;; The host's step is over the arena (fn-cwait-step-over): the arena holds the
;; news payload at the handle its row names.
(defun cwt-arena (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-arena-seal-list '(78) fn-arena))
(defun cwt-step (oc id secret elapsed seconds)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (let ((fn-arena (cwt-arena fn-arena)))
        (mv (fn-cwait-step-over oc *cwt-acfg* id secret elapsed seconds fn-arena)
            fn-arena))
      r)))
(defun cwt-poll (oc id secret)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (let ((fn-arena (cwt-arena fn-arena)))
        (mv (fn-cwait-poll-over oc *cwt-acfg* id secret fn-arena) fn-arena))
      r)))
;; The arena-free poll, which KEYSTONE 2's run model reads.
(defun cwt-poll0 (oc id secret) (fn-cwait-poll oc *cwt-acfg* id secret))

; The polls themselves: where no held row is selected the poll over the arena
; is the arena-free poll (fn-cwait-step-over-is-step-unless-a-held-row); the
; news is a held row, which only the poll over the arena reports.
(assert-event (equal (cwt-poll *cwt-oc-empty* *cwt-c1* nil)
                     (cwt-poll0 *cwt-oc-empty* *cwt-c1* nil)))
(assert-event (equal (cwt-poll0 *cwt-oc-full* *cwt-c2* *cwt-secret*)
                     '(:refused :report)))
(assert-event (fn-held-p (caddr (fn-col-poll (fn-own-start *cwt-full* 2) *cwt-c2*))))
(assert-event (fn-cwait-empty-pagep (cwt-poll *cwt-oc-empty* *cwt-c1* nil)))
(assert-event (fn-cwait-empty-pagep (cwt-poll *cwt-oc-empty* *cwt-c2* *cwt-secret*)))
(assert-event (fn-cwait-empty-pagep (cwt-poll *cwt-oc-full* *cwt-c1* nil)))
(defun cwt-news () (cwt-poll *cwt-oc-full* *cwt-c2* *cwt-secret*))
(assert-event (equal (car (cwt-news)) :poll))
(assert-event (consp (caddr (cwt-news))))
; The article the news report carries, for an agent's reader.
(assert-event
 (equal (fn-cwait-report-article (caddr (cwt-news)))
        (list :ok "<news@fn.test>"
              '(78))))
(assert-event (equal (fn-cwait-report-article '(1 2 3)) '(:refused :codec)))
(assert-event (equal (fn-record-msgid
                      (fn-col-poll-article
                       (caddr (fn-col-poll (fn-own-start *cwt-full* 2) *cwt-c2*))))
                     "<news@fn.test>"))

; --- KEYSTONE 1: fn-cwait-step-is-the-poll-or-a-sleep-on-an-empty-page ---
; Conjunct 1 (no hypothesis), both disjuncts reached: an empty page 0 ms into
; a 30 s wait sleeps 30 000 ms; the news answers at once.
(assert-event (equal (cwt-step *cwt-oc-empty* *cwt-c1* nil 0 30) '(:sleep 30000)))
(assert-event (equal (cwt-step *cwt-oc-empty* *cwt-c2* *cwt-secret* 1200 30)
                     '(:sleep 28800)))
(assert-event (equal (cwt-step *cwt-oc-full* *cwt-c2* *cwt-secret* 5 30)
                     (list :answer (cwt-news))))
; Only the consumer with news answers: "1" still sleeps on the full Store.
(assert-event (equal (cwt-step *cwt-oc-full* *cwt-c1* nil 5 30) '(:sleep 29995)))
; A refusal answers at once (it is not an empty page).
(assert-event (equal (cwt-step *cwt-oc-empty* *cwt-c2* *cwt-wrong* 0 30)
                     '(:answer (:refused :credential))))
(assert-event (equal (cwt-step *cwt-oc-empty* *cwt-c2* nil 0 30)
                     '(:answer (:refused :bound))))
; Conjunct 2 positive: the timeout answers the empty page at its deadline.
(assert-event (equal (cwt-step *cwt-oc-empty* *cwt-c1* nil 30000 30)
                     (list :answer (cwt-poll *cwt-oc-empty* *cwt-c1* nil))))
(assert-event (equal (cwt-step *cwt-oc-empty* *cwt-c1* nil 0 0)
                     (list :answer (cwt-poll *cwt-oc-empty* *cwt-c1* nil))))
; Conjunct 2 without each hypothesis: elapsed not natural (a malformed
; elapsed answers the empty page early); the answer not empty (the news at
; 5 ms).  (A sleep's second element is its milliseconds, never a page.)
(defmacro cwt-k2 (elapsed seconds)
  `(<= (fn-cwait-deadline-ms ,seconds) ,elapsed))
(assert-event (equal (car (cwt-step *cwt-oc-empty* *cwt-c1* nil 'x 30)) :answer))
(must-fail-checked
 (assert-event (let ((r (cwt-step *cwt-oc-empty* *cwt-c1* nil 'x 30)))
                 (implies (fn-cwait-empty-pagep (cadr r))
                          (cwt-k2 'x 30)))))
(must-fail-checked
 (assert-event (let ((r (cwt-step *cwt-oc-full* *cwt-c2* *cwt-secret* 5 30)))
                 (implies (and (natp 5) (equal (car r) :answer))
                          (cwt-k2 5 30)))))
; Conjunct 3 without its hypothesis (before the deadline): a sleep.
(must-fail-checked
 (assert-event (equal (cwt-step *cwt-oc-empty* *cwt-c1* nil 29999 30)
                      (list :answer (cwt-poll *cwt-oc-empty* *cwt-c1* nil)))))
; Conjunct 4 without its hypothesis (an empty page): a sleep.
(must-fail-checked
 (assert-event (equal (cwt-step *cwt-oc-empty* *cwt-c1* nil 0 30)
                      (list :answer (cwt-poll *cwt-oc-empty* *cwt-c1* nil)))))

; --- KEYSTONE 2: fn-cwait-run-answers-the-poll-at-its-return-point ----------
; The wait of "2": admitted on the empty Store, woken 1 200 ms later by the
; commit of the news: it answers the news, the poll of the state it
; returned in.
(defun cwt-run ()
  (fn-cwait-run (list (cons *cwt-oc-empty* 0) (cons *cwt-oc-full* 1200))
                *cwt-acfg* *cwt-c2* *cwt-secret* 30))
; (The run model's poll is the arena-free one: over the held news it answers
; the refusal :report at its return point; the model's arena restatement is
; open, books/consumer-wait.lisp.)
(assert-event (equal (cwt-run)
                     (list :answer (cwt-poll0 *cwt-oc-full* *cwt-c2* *cwt-secret*)
                           *cwt-oc-full* 1200)))
(assert-event (equal (cadr (cwt-run))
                     (cwt-poll0 (caddr (cwt-run)) *cwt-c2* *cwt-secret*)))
; The wait of "1" over the same commits: no news for it; it times out on the
; empty page at 30 000 ms.
(defun cwt-timeout ()
  (fn-cwait-run (list (cons *cwt-oc-empty* 0) (cons *cwt-oc-full* 1200)
                      (cons *cwt-oc-full* 30000))
                *cwt-acfg* *cwt-c1* nil 30))
(assert-event (equal (car (cwt-timeout)) :answer))
(assert-event (fn-cwait-empty-pagep (cadr (cwt-timeout))))
(assert-event (equal (cadddr (cwt-timeout)) 30000))
; Without its hypothesis (the run answered): no observation answers.
(must-fail-checked
 (assert-event
  (equal (car (fn-cwait-run (list (cons *cwt-oc-empty* 0)) *cwt-acfg* *cwt-c1* nil 30))
         :answer)))
; The inner implication without each hypothesis: the answer not empty (the
; news at 1 200 ms is before the deadline); elapsed not natural.
(must-fail-checked
 (assert-event (<= (fn-cwait-deadline-ms 30) (cadddr (cwt-run)))))
(defun cwt-bad-run ()
  (fn-cwait-run (list (cons *cwt-oc-empty* 'x)) *cwt-acfg* *cwt-c1* nil 30))
(assert-event (fn-cwait-empty-pagep (cadr (cwt-bad-run))))
(must-fail-checked
 (assert-event (<= (fn-cwait-deadline-ms 30) (cadddr (cwt-bad-run)))))

; --- fn-cwait-run-sleeps-only-over-empty-pages ------------------------------
(assert-event
 (equal (fn-cwait-run (list (cons *cwt-oc-empty* 0) (cons *cwt-oc-full* 1200))
                      *cwt-acfg* *cwt-c2* *cwt-secret* 30)
        (fn-cwait-run (list (cons *cwt-oc-full* 1200))
                      *cwt-acfg* *cwt-c2* *cwt-secret* 30)))
; Without its hypothesis (the first step answered): the page is not empty.
(must-fail-checked
 (assert-event (fn-cwait-empty-pagep
                (cwt-poll *cwt-oc-full* *cwt-c2* *cwt-secret*))))

; --- KEYSTONE 2 over the arena: fn-cwait-run-over-answers-the-poll-at-its-
; return-point, the loop over the host's step fn-cwait-step-over.  Each
; observation carries the payloads sealed since the one before; the run
; starts on an empty arena.  CWT-RUN-OVER answers (R POLL-AT-RETURN
; PAYLOADS): the run's answer, the poll over the arena it returned with of
; the owner configuration it names, and that arena's payloads.
(defun cwt-payloads (h n fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil
                  :measure (nfix (- (nfix n) (nfix h)))))
  (if (and (natp h) (natp n) (< h n))
      (cons (fn-arena-payload h fn-arena) (cwt-payloads (1+ h) n fn-arena))
    nil))
(defun cwt-run-over-in (observations id secret fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (r fn-arena)
    (fn-cwait-run-over observations *cwt-acfg* id secret 30 fn-arena)
    (mv (list r
              (and r (fn-cwait-poll-over (caddr r) *cwt-acfg* id secret fn-arena))
              (cwt-payloads 0 (fn-arena-count fn-arena) fn-arena))
        fn-arena)))
(defun cwt-run-over (observations id secret)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (x fn-arena) (cwt-run-over-in observations id secret fn-arena) x)))
; The wait of "2": admitted on the empty Store (nothing sealed), woken 1 200
; ms later by the commit of the news (its payload sealed at handle 0): it
; answers the news, the poll over the arena of the configuration it
; returned in.
(defconst *cwt-obs*
  (list (list* *cwt-oc-empty* 0 nil) (list* *cwt-oc-full* 1200 (list '(78)))))
;; (Nullary functions, not constants: the digest attachment is not callable
;; in a defconst.)
(defun cwt-run-over-news () (cwt-run-over *cwt-obs* *cwt-c2* *cwt-secret*))
(assert-event
 (let ((r (car (cwt-run-over-news))))
   (and r (equal (car r) :answer)
        (equal (cadr r) (cadr (cwt-run-over-news)))
        (equal (cadr r) (cwt-news))
        (equal (caddr r) *cwt-oc-full*)
        (equal (cadddr r) 1200)
        (not (fn-cwait-empty-pagep (cadr r)))
        (equal (caddr (cwt-run-over-news)) '((78))))))
; The wait of "1" over the same commits: no news for it; it times out on the
; empty page at 30 000 ms, which is its deadline.
(defun cwt-timeout-over ()
  (cwt-run-over (append *cwt-obs* (list (list* *cwt-oc-full* 30000 nil))) *cwt-c1* nil))
(assert-event
 (let ((r (car (cwt-timeout-over))))
   (and (equal (car r) :answer)
        (equal (cadr r) (cadr (cwt-timeout-over)))
        (natp (cadddr r))
        (fn-cwait-empty-pagep (cadr r))
        (<= (fn-cwait-deadline-ms 30) (cadddr r)))))
; Without its hypothesis (the run answered): no observation answers.
(assert-event (null (car (cwt-run-over (list (list* *cwt-oc-empty* 0 nil)) *cwt-c1* nil))))
(must-fail-checked
 (assert-event
  (equal (car (car (cwt-run-over (list (list* *cwt-oc-empty* 0 nil)) *cwt-c1* nil)))
         :answer)))
; The inner implication without each hypothesis: the answer not empty (the
; news at 1 200 ms is before the deadline); elapsed not natural (a malformed
; elapsed answers the empty page at once).
(must-fail-checked
 (assert-event (<= (fn-cwait-deadline-ms 30) (cadddr (car (cwt-run-over-news))))))
(defun cwt-bad-over () (cwt-run-over (list (list* *cwt-oc-empty* 'x nil)) *cwt-c1* nil))
(assert-event (and (fn-cwait-empty-pagep (cadr (car (cwt-bad-over))))
                   (not (natp (cadddr (car (cwt-bad-over)))))))
(must-fail-checked
 (assert-event (<= (fn-cwait-deadline-ms 30) (cadddr (car (cwt-bad-over))))))
; Mutation witness (no hypothesis of the keystone): without the news's seal
; the row names a handle the arena lacks, and the answer is not the news.
(must-fail-checked
 (assert-event
  (equal (cadr (car (cwt-run-over (list (list* *cwt-oc-full* 1200 nil)) *cwt-c2* *cwt-secret*)))
         (cwt-news))))

; --- fn-cwait-run-over-sleeps-only-over-empty-pages --------------------------
; The first observation (the empty Store at 0 ms) is an empty page before
; the deadline, and the run from it is the run from the next one.
(assert-event
 (and (fn-cwait-empty-pagep (cwt-poll *cwt-oc-empty* *cwt-c2* *cwt-secret*))
      (equal (cwt-step *cwt-oc-empty* *cwt-c2* *cwt-secret* 0 30) '(:sleep 30000))
      (equal (car (cwt-run-over-news))
             (car (cwt-run-over (cdr *cwt-obs*) *cwt-c2* *cwt-secret*)))))
; Without its hypothesis (the step answered): the page is not empty.
(must-fail-checked
 (assert-event (fn-cwait-empty-pagep
                (cwt-poll *cwt-oc-full* *cwt-c2* *cwt-secret*))))

; --- KEYSTONE 3: fn-cwait-admit-leaves-workers-free -------------------------
(assert-event (equal (fn-cwait-capacity) 12))
(assert-event (equal (fn-cwait-admit 0) :admit))
(assert-event (equal (fn-cwait-admit 11) :admit))
(assert-event (equal (fn-cwait-admit 12) '(:refused :waiters)))
; Without the first conjunct's hypothesis: 12 is not admitted.
(must-fail-checked (assert-event (<= (+ 1 12) (fn-cwait-capacity))))
; Without the second's: 11 is admitted.
(must-fail-checked (assert-event (equal (fn-cwait-admit 11) '(:refused :waiters))))
