; Ground teeth for A0 and revised A3; A1 is held for context draft 4.
(in-package "ACL2")
(include-book "../../books/post-acceptance")
(include-book "../../books/records-attach")
(set-verify-guards-eagerness 0)

; c4's real, two-group prepared post and its injection configuration.
(with-guard-checking-event :none
 (encapsulate ()
(defun pc4-lines (xs)
  (if (consp xs)
      (append (fn-record-string-octets (car xs)) '(13 10) (pc4-lines (cdr xs)))
    nil))

(defconst *pc4-art*
  (pc4-lines '("From: poster@example.invalid" "Path: not-for-mail"
               "Subject: hello" "Newsgroups: fn.letters,fn.test"
               "Date: Tue, 22 Sep 2026 21:26:21 +0000"
               "Message-ID: <pc4@example.invalid>" "" "Hello, news.")))

(defconst *pc4-agent* (fn-record-string-octets "fnA.hbox.test"))

(defconst *pc4-icfg*
  (fn-inj-make-config t *pc4-agent*
                      (list (fn-record-string-octets "fn.letters")
                            (fn-record-string-octets "fn.test")) 32768))

(defconst *pc4-obs* (fn-clock-observation 1000000 843004800000 500 t))

(defconst *pc4-d* (fn-inj-decide *pc4-art* *pc4-icfg* *pc4-obs*))

(defconst *pc4-secret*
  (list (fn-ns-make-entry 1 (fn-record-string-octets "local")
                          (make-list 32 :initial-element 7))))

(defconst *pc4-login* (fn-record-string-octets "alice"))

(defconst *pc4-cfg*
  (fn-cfg-make 1 (fn-cfg-apply-delta
                 (fn-cfg-empty-value) 1 (fn-clock-observation 5 1700000000 2 t)
                 (fn-cfg-set-policy "complaints-to"
                                    (fn-record-string-octets "abuse@example.org")))))

(defconst *pc4-injected*
  (fn-ipp-injected-octets *pc4-d* *pc4-secret* *pc4-login* *pc4-cfg*))

(defconst *pc4-carry*
  (fn-apc-extend *pc4-injected* (fn-apc-extend *pc4-art* nil)))

(defconst *pc4-inj*
  (list *pc4-d* *pc4-secret* *pc4-login* *pc4-cfg* *pc4-carry* *pc4-icfg* *pc4-obs*))

(defconst *pc4-stored* (fn-pacc-stored-payload *pc4-art* *pc4-inj*))

(defconst *pc4-s* (fn-sn-initial '("fn.letters" "fn.test") 32))

(defconst *pc4-fields* '("<pc4@example.invalid>" ("fn.letters" "fn.test")
                       "pc4-obligation" "pc4-subject" "pc4-evidence" 1))

(defconst *pc4-rec*
  (fn-sn-article-record *pc4-s* *pc4-obs* (nth 0 *pc4-fields*) *pc4-stored*
                       (nth 1 *pc4-fields*) (nth 2 *pc4-fields*)
                       (nth 3 *pc4-fields*) (nth 4 *pc4-fields*) (nth 5 *pc4-fields*)))

(defconst *pc4-ctx* (fn-pctx-of-prepared *pc4-s* *pc4-rec* *pc4-art* *pc4-inj*))

(defconst *pc4-laid-out*
  (append (nth 1 *pc4-ctx*) (take (nth 3 *pc4-ctx*) *pc4-art*)
          (nth 2 *pc4-ctx*) (nthcdr (nth 3 *pc4-ctx*) *pc4-art*)
          (nth 4 *pc4-ctx*) (nth 5 *pc4-ctx*)))

(defun l2-row-wire-exec (row arena)
  (cond ((fn-held-p row)
         (fn-held-wire row
                       (if (and (natp (fn-record-payload row))
                                (< (fn-record-payload row) (fn-arena$a-count arena)))
                           (fn-arena$a-payload (fn-record-payload row) arena) nil)))
        ((fn-hstxa-p row) (fn-hstxa-stxa row))
        (t row)))

(defun l2-batch-record-octets (s obs art inj fields arena)
  (let* ((rec (fn-sn-article-record s obs (fn-pctx-get 0 fields)
                                   (fn-pacc-stored-payload art inj)
                                   (fn-pctx-get 1 fields) (fn-pctx-get 2 fields)
                                   (fn-pctx-get 3 fields) (fn-pctx-get 4 fields)
                                   (fn-pctx-get 5 fields)))
         (row (fn-apc-intern-row-at rec (fn-sn-keyring s)
                                    (fn-sn-keyring-generation s)
                                    (fn-arena$a-count arena) (fn-pctx-get 4 inj)))
         (sealed (fn-arena$a-seal-list (fn-record-payload rec) arena)))
    (fn-rcon-store-event-encode (l2-row-wire-exec row sealed))))

(local (defthm l2-batch-copy-equals-original-by-definition
  (equal (l2-batch-record-octets s obs art inj fields fn-arena)
         (fn-pacc-batch-record-octets s obs art inj fields fn-arena))
  :hints (("Goal" :in-theory '(l2-batch-record-octets l2-row-wire-exec
                               fn-pacc-batch-record-octets fn-row-wire-of
                               fn-row-bytes fn-arena-count fn-arena-payload
                               fn-arena-seal-list)))
  :rule-classes nil))

(defun p3-large-groups (n)
  (if (zp n) nil
    (cons (fn-record-octets-string
           (append '(102 110 46) (make-list 252 :initial-element 97)
                   (list (+ 97 (mod (nfix n) 26)))))
          (p3-large-groups (- n 1)))))

(defconst *p3-groups* (p3-large-groups 12))

(defconst *p3-rec*
  (fn-sn-article-record *pc4-s* *pc4-obs* (nth 0 *pc4-fields*)
                       (fn-pacc-stored-payload *pc4-art* *pc4-inj*) *p3-groups*
                       (nth 2 *pc4-fields*) (nth 3 *pc4-fields*)
                       (nth 4 *pc4-fields*) (nth 5 *pc4-fields*)))

(defconst *p3-ctx* (fn-pctx-of-prepared *pc4-s* *p3-rec* *pc4-art* *pc4-inj*))
; A0: whole antecedent and all three conclusions on the prepared post.
(assert-event
 (and (fn-octet-listp *pc4-art*) (fn-pacc-injectionp *pc4-inj* *pc4-art*)
  (mv-let (p0 ins ioff) (fn-pacc-splice *pc4-art* *pc4-inj*)
   (and (natp ioff) (<= ioff (len *pc4-art*))
    (equal *pc4-stored*
     (append p0 (take ioff *pc4-art*) ins (nthcdr ioff *pc4-art*)))))))

; A0 injection hypothesis removal: an absent decision loses the stored
; payload, while the recipe still includes the unchanged original article.
(assert-event
 (let ((inj (update-nth 0 nil *pc4-inj*)))
  (and (fn-octet-listp *pc4-art*) (not (fn-pacc-injectionp inj *pc4-art*))
   (mv-let (p0 ins ioff) (fn-pacc-splice *pc4-art* inj)
    (not (equal (fn-pacc-stored-payload *pc4-art* inj)
     (append p0 (take ioff *pc4-art*) ins (nthcdr ioff *pc4-art*))))))))

; A0 mutation: a second insertion at the end breaks the single-splice claim.
(assert-event
 (and (fn-octet-listp *pc4-art*) (fn-pacc-injectionp *pc4-inj* *pc4-art*)
  (mv-let (p0 ins ioff) (fn-pacc-splice *pc4-art* *pc4-inj*)
   (not (equal (append *pc4-stored* '(0))
    (append p0 (take ioff *pc4-art*) ins (nthcdr ioff *pc4-art*)))))))

; A3: all four hypotheses and equality at the seam's attached encoder.
(assert-event
 (and (fn-sn-statep *pc4-s*) (fn-record-p *pc4-rec*)
      (fn-octet-listp *pc4-art*) (fn-pacc-injectionp *pc4-inj* *pc4-art*)
  (equal (l2-batch-record-octets *pc4-s* *pc4-obs* *pc4-art* *pc4-inj*
                               *pc4-fields* nil)
         (fn-record-encode *pc4-rec*))))

; A3 state-recognizer removal: keyring generation -1 makes the interned
; context invalid and the STORE event empty, while the valid record encodes.
(assert-event
 (let* ((s (update-nth 6 -1 *pc4-s*))
        (rec (fn-sn-article-record s *pc4-obs* (nth 0 *pc4-fields*) *pc4-stored*
          (nth 1 *pc4-fields*) (nth 2 *pc4-fields*) (nth 3 *pc4-fields*)
          (nth 4 *pc4-fields*) (nth 5 *pc4-fields*))))
  (and (not (fn-sn-statep s)) (fn-record-p rec) (fn-octet-listp *pc4-art*)
       (fn-pacc-injectionp *pc4-inj* *pc4-art*)
       (not (equal (l2-batch-record-octets s *pc4-obs* *pc4-art* *pc4-inj*
                                         *pc4-fields* nil)
                   (fn-record-encode rec))))))

; A3 mutation: sealing different bytes at the predicted handle changes
; the event's record even when all of the keystone's hypotheses hold.
(defun pc4-mutated-batch-octets (s rec carry arena)
 (let* ((row (fn-apc-intern-row-at rec (fn-sn-keyring s)
                    (fn-sn-keyring-generation s) (fn-arena$a-count arena) carry))
        (sealed (fn-arena$a-seal-list '(0) arena)))
  (fn-rcon-store-event-encode (l2-row-wire-exec row sealed))))
(assert-event
 (and (fn-sn-statep *pc4-s*) (fn-record-p *pc4-rec*)
      (fn-octet-listp *pc4-art*) (fn-pacc-injectionp *pc4-inj* *pc4-art*)
      (not (equal (pc4-mutated-batch-octets *pc4-s* *pc4-rec* *pc4-carry* nil)
                  (fn-record-encode *pc4-rec*)))))

; A1 counterexample: the OLD context carries all groups in SUFTAIL.
; Twelve legal, 256-octet names overflow its fixed bound: reason for draft 4.
(assert-event
 (and (fn-record-p *p3-rec*) (fn-octet-listp *pc4-art*)
      (fn-pacc-injectionp *pc4-inj* *pc4-art*)
      (> (len (nth 5 *p3-ctx*)) (fn-adm-acc-out-max))
      (not (fn-pctx-p *p3-ctx*))))
 ))

; Removal audit: A0's octet recognizer is implied by injection success.
; A3 needs only its store recognizer; the other three removal witnesses
; cannot exist. These local stronger proofs document that finding, while
; the approved public keystone statements remain byte-identical.
(local (encapsulate ()
(defthm fn-pacct-redundancy-state-generation
 (implies (fn-sn-statep s) (natp (fn-sn-keyring-generation s)))
 :hints (("Goal" :in-theory '(fn-sn-statep))))

(defthm fn-pacct-redundancy-injection-carry
 (implies (fn-pacc-injectionp inj art) (fn-apc-p (fn-pctx-get 4 inj)))
 :hints (("Goal" :in-theory '(fn-pacc-injectionp))))

(defthm fn-pacct-redundancy-injection-decision
 (implies (fn-pacc-injectionp inj art)
  (and (fn-inj-configp (fn-pctx-get 5 inj))
       (equal (fn-pctx-get 0 inj) (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj)))
       (fn-inj-injectedp (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj)))))
 :hints (("Goal" :in-theory '(fn-pacc-injectionp))))

(defthm fn-pacct-redundancy-success-parse
 (implies (fn-inj-injectedp (fn-inj-decide art config obs))
  (and (fn-article-result-okp (fn-article-parse art))
       (fn-article-syntax-p (fn-article-result-article (fn-article-parse art)))))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
    '(fn-inj-decide fn-inj-refuse fn-inj-injectedp fn-inj-decision-status-of-fn-inj-make-decision)))))

(defthm fn-pacct-redundancy-parse-requires-octets
 (implies (fn-article-result-okp (fn-article-parse art)) (fn-cbor-octet-listp art))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-article-parse fn-article-parse-under fn-article-result-okp fn-article-error)))))

(defthm fn-pacct-redundancy-cbor-is-octets
 (equal (fn-cbor-octet-listp x) (fn-octet-listp x))
 :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp fn-octet-listp fn-octetp))))

(defthm fn-pacct-redundancy-injection-requires-octets
 (implies (fn-pacc-injectionp inj art) (fn-octet-listp art))
 :hints (("Goal" :use ((:instance fn-pacct-redundancy-injection-decision)
 (:instance fn-pacct-redundancy-success-parse (config (fn-pctx-get 5 inj)) (obs (fn-pctx-get 6 inj)))
 (:instance fn-pacct-redundancy-parse-requires-octets))
 :in-theory (union-theories (theory 'ground-zero) '(fn-pacct-redundancy-cbor-is-octets)))))

(defthm fn-pacct-redundancy-carried-facts-shape
 (fn-hf-p (fn-apc-held-facts-of bytes carry))
 :hints (("Goal" :in-theory (e/d (fn-apc-held-facts-of fn-hf-p fn-hf-internals fn-hf-startp)
 (fn-apc-control-of fn-hnov-of-parsed fn-hf-control-with-nov fn-hf-split-index fn-hf-body-lines-of)))))

(defthm fn-pacct-redundancy-verified-statement-shape
 (implies (fn-prin-verifiedp s keyring) (fn-stmt-p s))
 :hints (("Goal" :in-theory (enable fn-prin-verifiedp))))

(defthm fn-pacct-redundancy-carried-context-shape
 (implies (natp generation) (fn-hc-p (fn-apc-held-context-of bytes keyring generation carry)))
 :hints (("Goal" :in-theory (e/d (fn-apc-held-context-of fn-hc-p fn-hc-internals fn-hc-anyp fn-hc-verdictp fn-stx-verifiedp fn-stx-verdict fn-stx-make-verdict fn-stx-verdict-token fn-stx-verdict-generation)
 (fn-apc-stx-parse fn-stx-statement-of fn-stx-field fn-stx-parse-header fn-stx-reattach)))))

(defthm fn-pacct-redundancy-carried-row-held
 (implies (and (fn-record-p w) (natp generation) (natp h))
 (fn-held-p (fn-apc-intern-row-at w keyring generation h carry)))
 :hints (("Goal" :in-theory (e/d (fn-apc-intern-row-at fn-record-p fn-held-p fn-record-internals fn-held-internals)
 (fn-apc-held-facts-of fn-apc-held-context-of)))))

(defthm fn-pacct-redundancy-carried-row-alpha
 (implies (fn-record-shapep w)
 (equal (fn-held-wire (fn-apc-intern-row-at w keyring generation h carry) (fn-record-payload w)) w))
 :hints (("Goal" :in-theory (e/d (fn-held-wire fn-apc-intern-row-at)
 (fn-apc-held-facts-of fn-apc-held-context-of)))))

(defthm fn-pacct-redundancy-carried-row-handle
 (equal (fn-record-payload (fn-apc-intern-row-at w keyring generation h carry)) h)
 :hints (("Goal" :in-theory (enable fn-apc-intern-row-at))))

(defthm fn-pacct-redundancy-direct-intern-materializes
 (implies (and (fn-record-p w) (natp generation))
  (equal (fn-row-wire-of
           (fn-apc-intern-row-at w keyring generation (fn-arena-count fn-arena) carry)
           (fn-arena-seal-list (fn-record-payload w) fn-arena)) w))
 :hints (("Goal" :in-theory
 (e/d (fn-row-wire-of fn-row-bytes)
      (fn-apc-intern-row-at fn-held-p fn-held-wire fn-arena-payload-is-nth
       fn-arena-count-is-len fn-arena-seal-list-is-append
       fn-pacct-redundancy-carried-row-held fn-pacct-redundancy-carried-row-alpha fn-arena-seal-new-handle))
 :use ((:instance fn-pacct-redundancy-carried-row-held (h (fn-arena-count fn-arena)))
       (:instance fn-pacct-redundancy-carried-row-alpha (h (fn-arena-count fn-arena)))
       (:instance fn-arena-seal-new-handle (xs (fn-record-payload w)))))))

(defthm fn-pacct-redundancy-held-make-is-not-event
 (implies (natp sequence)
 (equal (fn-rcon-store-event-encode
 (fn-held-make sequence txid generation msgid payload groups oid subject evidence charge stamp facts context numbers withdrawn)) nil))
 :hints (("Goal" :in-theory (e/d
 (fn-rcon-store-event-encode fn-rcon-record-p-is-record-p fn-record-p fn-record-shapep
 fn-held-internals fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
 fn-stxe-internals fn-stxk-internals fn-stxa-internals fn-cpe-eventp fn-th-topic-eventp)
 (fn-store-retention-event-encode fn-stxe-encode fn-stxk-encode fn-stxa-encode fn-cpe-encode fn-th-topic-event-encode)))))

(defthm fn-pacct-redundancy-carried-row-event-nil
 (implies (natp (fn-record-sequence w))
 (equal (fn-rcon-store-event-encode (fn-apc-intern-row-at w keyring generation h carry)) nil))
 :hints (("Goal" :in-theory (e/d (fn-apc-intern-row-at) (fn-apc-held-context-of fn-apc-held-facts-of)))))

(defthm fn-pacct-redundancy-numeric-event-is-record-codec
 (implies (and (fn-record-shapep w) (natp (fn-record-sequence w)))
 (equal (fn-rcon-store-event-encode w) (fn-record-encode w)))
 :hints (("Goal" :in-theory (e/d
 (fn-rcon-store-event-encode fn-rcon-record-p-is-record-p fn-record-sequence fn-record-shapep fn-th-local-admin-eventp fn-th-at
 fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
 fn-stxe-internals fn-stxk-internals fn-stxa-internals fn-cpe-eventp fn-th-topic-eventp)
 (fn-record-p fn-store-retention-event-encode fn-stxe-encode fn-stxk-encode fn-stxa-encode fn-cpe-encode fn-th-topic-event-encode)))))

(defthm fn-pacct-redundancy-carried-row-not-composite
 (not (fn-hstxa-p (fn-apc-intern-row-at w keyring generation h carry)))
 :hints (("Goal" :in-theory (e/d (fn-apc-intern-row-at fn-hstxa-p fn-held-internals)
 (fn-apc-held-facts-of fn-apc-held-context-of fn-stxa-p fn-held-p)))))

(defthm fn-pacct-redundancy-encoded-intern-materializes
 (implies (and (fn-record-shapep w) (natp (fn-record-sequence w)) (natp generation))
  (equal (fn-rcon-store-event-encode (fn-row-wire-of
           (fn-apc-intern-row-at w keyring generation (fn-arena-count fn-arena) carry)
           (fn-arena-seal-list (fn-record-payload w) fn-arena))) (fn-record-encode w)))
 :hints (("Goal" :cases ((fn-record-p w)) :in-theory
 (e/d (fn-row-wire-of fn-row-bytes)
      (fn-apc-intern-row-at fn-held-p fn-held-wire fn-arena-payload-is-nth
       fn-arena-count-is-len fn-arena-seal-list-is-append fn-record-p fn-rcon-record-p
       fn-pacct-redundancy-carried-row-alpha fn-arena-seal-new-handle))
 :use ((:instance fn-pacct-redundancy-carried-row-alpha (h (fn-arena-count fn-arena)))
       (:instance fn-arena-seal-new-handle (xs (fn-record-payload w)))))))

(defthm fn-pacct-redundancy-state-identity-next
 (implies (fn-sn-statep s) (natp (fn-sn-identity-next s)))
 :hints (("Goal" :in-theory '(fn-sn-statep))))

(defthm fn-pacct-redundancy-article-wire-shape
 (implies (natp (fn-record-stamp-of-observation obs))
 (and (fn-record-shapep (fn-sn-article-record s obs msgid payload groups oid subject evidence charge))
 (equal (fn-record-sequence (fn-sn-article-record s obs msgid payload groups oid subject evidence charge))
 (fn-sn-identity-next s))))
 :hints (("Goal" :in-theory (enable fn-sn-article-record))))

(defthm fn-pacct-redundancy-clock-unusable-intern
 (equal (fn-rcon-store-event-encode
 (fn-row-wire-of (fn-apc-intern-row-at :clock-unusable keyring generation h carry) arena)) nil)
 :hints (("Goal" :in-theory (e/d
 (fn-rcon-store-event-encode fn-apc-intern-row-at fn-row-wire-of fn-record-internals
 fn-held-internals fn-held-p fn-hstxa-p fn-rcon-record-p-is-record-p fn-record-p
 fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p fn-stxe-internals fn-stxk-internals fn-stxa-internals fn-cpe-eventp fn-th-topic-eventp)
 (fn-store-retention-event-encode fn-stxe-encode fn-stxk-encode fn-stxa-encode fn-cpe-encode fn-th-topic-event-encode)))))

(defthm fn-pacct-redundancy-a3-needs-only-store-recognizer
  (let ((rec (fn-sn-article-record s obs msgid (fn-pacc-stored-payload art inj) groups oid subject evidence charge)))
    (implies (fn-sn-statep s)
             (equal (fn-pacc-batch-record-octets s obs art inj (list msgid groups oid subject evidence charge) fn-arena)
                    (fn-record-encode rec))))
  :hints (("Goal" :in-theory
    (union-theories (theory 'ground-zero)
      '(fn-pacc-batch-record-octets fn-pctx-get nfix zp 
        fn-rcon-record-p-is-record-p fn-pacct-redundancy-encoded-intern-materializes fn-pacct-redundancy-state-identity-next fn-pacct-redundancy-article-wire-shape fn-pacct-redundancy-clock-unusable-intern fn-record-encode-domain fn-sn-article-record fn-record-shapep fn-record-sequence fn-record-make (:executable-counterpart fn-record-p)
        fn-pacct-redundancy-state-generation fn-pacct-redundancy-injection-carry)))))
))
