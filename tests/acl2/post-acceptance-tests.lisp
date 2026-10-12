; Ground teeth for A0 and revised A3; A1 is held for context draft 4.
(in-package "ACL2")
(include-book "../../books/post-acceptance")
(include-book "../../books/records-attach")
(include-book "../../books/owner-agent")
(include-book "../../books/post-fields")
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
 (and (fn-pacc-injectionp *pc4-inj* *pc4-art*)
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
 (and (fn-pacc-injectionp *pc4-inj* *pc4-art*)
  (mv-let (p0 ins ioff) (fn-pacc-splice *pc4-art* *pc4-inj*)
   (not (equal (append *pc4-stored* '(0))
    (append p0 (take ioff *pc4-art*) ins (nthcdr ioff *pc4-art*)))))))

; A3: the store recognizer and equality at the seam's attached encoder.
(assert-event
 (and (fn-sn-statep *pc4-s*)
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
 (and (fn-sn-statep *pc4-s*)
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

; MOD4: forward envelopes keep the original poster's source as a suffix.
(with-guard-checking-event :none
 (encapsulate ()
(defun mod-names (xs) (if (consp xs) (cons (fn-record-octets-string (car xs)) (mod-names (cdr xs))) nil))
(defconst *mod-entry* (list :moderated (fn-record-string-octets "fn.mod") (fn-record-string-octets "fn.queue") (list (fn-record-string-octets "alice"))))
(defconst *mod-icfg* (fn-inj-make-config-closed t *pc4-agent* (list (fn-record-string-octets "fn.mod") (fn-record-string-octets "fn.queue") (fn-record-string-octets "fn.letters") (fn-record-string-octets "fn.test")) 32768 (list *mod-entry*)))
(defconst *mod-art* (pc4-lines '("From: poster@example.invalid" "Path: not-for-mail" "Subject: hello" "Newsgroups: fn.mod" "Date: Tue, 22 Sep 2026 21:26:21 +0000" "Message-ID: <pc4@example.invalid>" "" "Hello, news.")))
(defconst *mod-d* (fn-post-gated-decision *mod-art* *mod-icfg* *pc4-obs*))
(defconst *mod-sub* (fn-own-sub-make-author 1 1 :local *mod-d* *pc4-login* *pc4-login* nil))
(defconst *mod-take* (fn-apc-take *pc4-cfg* *mod-sub* *pc4-secret*))
(defconst *mod-inj* (list *mod-d* *pc4-secret* *pc4-login* *pc4-cfg* (cdr *mod-take*) *mod-icfg* *pc4-obs*))
(defconst *mod-stored* (fn-pacc-stored-payload *mod-art* *mod-inj*))
(defconst *mod-splice* (mv-let (p ins off) (fn-pacc-splice *mod-art* *mod-inj*) (list p ins off)))
(defconst *mod-rhs* (append (nth 0 *mod-splice*) (take (nth 2 *mod-splice*) *mod-art*) (nth 1 *mod-splice*) (nthcdr (nth 2 *mod-splice*) *mod-art*)))
(defconst *mod-s* (fn-sn-initial '("fn.mod" "fn.queue" "fn.letters" "fn.test") 32))
(defconst *mod-fields* (list (fn-record-octets-string (fn-inj-decision-msgid *mod-d*)) (mod-names (fn-inj-decision-groups *mod-d*)) "pc4-obligation" "pc4-subject" "pc4-evidence" 1))
(defconst *mod-rec* (fn-sn-article-record *mod-s* *pc4-obs* (nth 0 *mod-fields*) *mod-stored* (nth 1 *mod-fields*) (nth 2 *mod-fields*) (nth 3 *mod-fields*) (nth 4 *mod-fields*) (nth 5 *mod-fields*)))
(defun m2-art (mid date)
 (pc4-lines (append '("From: poster@example.invalid" "Path: not-for-mail" "Subject: hello" "Newsgroups: fn.mod")
 (if date '("Date: Tue, 22 Sep 2026 21:26:21 +0000") nil)
 (if mid '("Message-ID: <pc4@example.invalid>") nil) '("" "Hello, news."))))
(defun m2-inj (art icfg obs secret cfg)
 (let* ((d (fn-post-gated-decision art icfg obs))
 (sub (fn-own-sub-make-author 1 1 :local d *pc4-login* *pc4-login* nil))
 (tk (fn-apc-take cfg sub secret)))
 (list d secret *pc4-login* cfg (cdr tk) icfg obs)))
(defun m2-suffix (art inj)
 (let ((stored (fn-pacc-stored-payload art inj)))
 (and (<= (len art) (len stored)) (equal (nthcdr (- (len stored) (len art)) stored) art))))
(defun pc9-old-splice (art inj)
  (declare (xargs :guard t))
  (let* ((d (fn-pctx-get 0 inj)) (secret (fn-pctx-get 1 inj))
         (login (fn-pctx-get 2 inj)) (cfg (fn-pctx-get 3 inj))
         (carry (fn-pctx-get 4 inj)) (icfg (fn-pctx-get 5 inj))
         (obs (fn-pctx-get 6 inj)) (msgid (fn-inj-decision-msgid d))
         (candidate (fn-pctx-get 1 (fn-article-parse art)))
         (parsed (if (fn-article-syntax-p candidate) candidate '(nil nil nil)))
         (gid (not (fn-inj-nth 1
                              (if (fn-article-syntax-p parsed)
                                  (fn-af-proto-article-check parsed) nil))))
         (gdate (fn-inj-absentp parsed *fn-inj-date-name*))
         (agent (fn-inj-config-agent icfg))
         (date (fn-inj-date-octets (fn-inj-instant-of (fn-clock-wall obs))))
         (pathp (not (fn-inj-absentp parsed *fn-inj-path-name*)))
         (block (if pathp (fn-inj-block date msgid agent gid gdate)
                  (fn-inj-prefix date msgid agent gid gdate)))
         (params (fn-ipp-params secret login (fn-ipp-complaints cfg)))
         (injected (fn-ipp-injected-octets d secret login cfg))
         (fields (fn-apc-received-fields injected carry))
         (cl (fn-cll-lines (fn-cl-lock-value secret login msgid fields)
                           (fn-cl-key-values secret login fields))))
    (mv (fn-pctx-cat cl (fn-ipp-with-params block msgid params))
        (if pathp (fn-inj-path-insert agent) nil)
        (if pathp (nfix (fn-inj-path-offset art)) 0))))
(defun m2-a0 (art inj)
 (mv-let (p0 ins ioff) (fn-pacc-splice art inj)
  (and (natp ioff) (<= ioff (len art))
       (equal (fn-pacc-stored-payload art inj)
              (append p0 (take ioff art) ins (nthcdr ioff art))))))
(defun pc9-mod-variant (mid date)
 (let* ((art (m2-art mid date))
        (inj (m2-inj art *mod-icfg* *pc4-obs* *pc4-secret* *pc4-cfg*)))
  (and (fn-pacc-injectionp inj art) (m2-a0 art inj) (m2-suffix art inj))))
; Four MID/Date variants go through the real moderation gate and apc-take.
(assert-event (and (pc9-mod-variant t t) (pc9-mod-variant nil nil)
                   (pc9-mod-variant t nil) (pc9-mod-variant nil t)))
(defconst *pc9-old-splice-moderation-tooth*
 (and (fn-pacc-injectionp *mod-inj* *mod-art*)
      (equal (len *mod-stored*) 723)
      (mv-let (p0 ins off) (pc9-old-splice *mod-art* *mod-inj*)
       (let ((rhs (append p0 (take off *mod-art*) ins (nthcdr off *mod-art*))))
        (and (equal (len rhs) 411) (not (equal *mod-stored* rhs)))))))
; Named mutation tooth: the old direct witness loses the envelope prefix.
(assert-event *pc9-old-splice-moderation-tooth*)
(assert-event (and (fn-sn-statep *mod-s*) (fn-record-p *mod-rec*)
 (equal (l2-batch-record-octets *mod-s* *pc4-obs* *mod-art* *mod-inj* *mod-fields* nil)
        (fn-record-encode *mod-rec*))))

(defconst *m2-max-agent* (fn-record-octets-string (make-list 128 :initial-element 97)))
(defconst *m2-max-group* (fn-record-octets-string (make-list 256 :initial-element 109)))
(defconst *m2-max-queue* (fn-record-octets-string (make-list 256 :initial-element 113)))
(defconst *m2-max-complaints* (fn-record-octets-string (append (make-list 128 :initial-element 97) '(64) (make-list 127 :initial-element 98))))
(defconst *m2-max-cfg1* (fn-cfg-apply (fn-cfg-empty-value) 1 *pc4-obs*
 (list (fn-cfg-create-group *m2-max-group* *fn-cfg-default-policy-id*)
       (fn-cfg-create-group *m2-max-queue* *fn-cfg-default-policy-id*)
       (fn-cfg-set-capacity 1000000)
       (fn-cfg-set-policy "path-identity" *m2-max-agent*)
       (fn-cfg-set-policy "complaints-to" *m2-max-complaints*))))
(defconst *m2-max-delta* (fn-cfg-set-group-moderation *m2-max-group* *m2-max-queue* "" '("alice")))
(defconst *m2-max-cfg* (fn-cfg-make 2 (fn-cfg-apply-delta *m2-max-cfg1* 2 *pc4-obs* *m2-max-delta*)))
(defconst *m2-max-icfg* (fn-oag-post-config *m2-max-cfg* 131072))
(defun m2-ring (n) (if (zp n) nil (cons (fn-ns-make-entry n (fn-record-string-octets "local") (make-list 32 :initial-element 7)) (m2-ring (- n 1)))))
(defconst *m2-max-ring* (m2-ring 18))
(defun m2-max-art (mid date)
 (append (pc4-lines (append (list "From: poster@example.invalid" "Path: not-for-mail" "Subject: hello" (fn-record-octets-string (append (fn-record-string-octets "Newsgroups: ") (fn-record-string-octets *m2-max-group*))))
 (if date '("Date: Tue, 22 Sep 2026 21:26:21 +0000") nil)
 (if mid (list (fn-record-octets-string (append (fn-record-string-octets "Message-ID: <") (make-list 234 :initial-element 97) (fn-record-string-octets "@b>")))) nil) '("")))
 (make-list 65536 :initial-element 120) '(13 10)))
(defconst *m2-max-art* (m2-max-art nil nil))
(defconst *m2-max-inj* (m2-inj *m2-max-art* *m2-max-icfg* *pc4-obs* *m2-max-ring* *m2-max-cfg*))
(defconst *m2-max-stored* (fn-pacc-stored-payload *m2-max-art* *m2-max-inj*))
(defconst *m2-base-s* (fn-sn-initial (list *m2-max-group* *m2-max-queue*) 1000000))
(defconst *m2-max-s* (let* ((node (fn-sn-node *m2-base-s*)) (acc (fn-node-acceptance node)))
 (update-nth 9 4294967296 (update-nth 3 (update-nth 0 (update-nth 3 4294967296 acc) node) *m2-base-s*))))
(defconst *m2-max-fields* (list (fn-record-octets-string (fn-inj-decision-msgid (car *m2-max-inj*))) (mod-names (fn-inj-decision-groups (car *m2-max-inj*))) "pc4-obligation" "pc4-subject" "pc4-evidence" 1))
(defconst *m2-max-rec* (fn-sn-article-record *m2-max-s* *pc4-obs* (nth 0 *m2-max-fields*) *m2-max-stored* (nth 1 *m2-max-fields*) (nth 2 *m2-max-fields*) (nth 3 *m2-max-fields*) (nth 4 *m2-max-fields*) (nth 5 *m2-max-fields*)))
(defconst *m2-max-ctx* (fn-pctx-of-prepared *m2-max-s* *m2-max-rec* *m2-max-art* *m2-max-inj*))
; Codec maximum PRE witness: 227 record head + 2011 moderation prefix.
(assert-event (and (fn-cfgp *m2-max-cfg*) (fn-inj-configp *m2-max-icfg*)
 (fn-pacc-injectionp *m2-max-inj* *m2-max-art*)
 (fn-sn-statep *m2-max-s*) (fn-record-p *m2-max-rec*)
 (m2-a0 *m2-max-art* *m2-max-inj*) (m2-suffix *m2-max-art* *m2-max-inj*)
 (equal (len (nth 1 *m2-max-ctx*)) 2238) (fn-pctx-p *m2-max-ctx*)
 (eq (fn-pa-carrier-kind *m2-max-stored*) :absent)
 (equal (l2-batch-record-octets *m2-max-s* *pc4-obs* *m2-max-art* *m2-max-inj*
                              *m2-max-fields* nil)
        (fn-record-encode *m2-max-rec*))))

(defconst *m2-dot-art* (append (pc4-lines '("From: poster@example.invalid" "Path: not-for-mail" "Subject: hello" "Newsgroups: fn.mod" "")) (fn-record-string-octets ".first") '(13 10) (fn-record-string-octets "..second") '(13 10 0 255 13 10)))
(defconst *m2-dot-inj* (m2-inj *m2-dot-art* *mod-icfg* *pc4-obs* *pc4-secret* *pc4-cfg*))
; Dotted and binary body is preserved byte for byte, without dot stuffing.
(assert-event (and (fn-pacc-injectionp *m2-dot-inj* *m2-dot-art*)
 (m2-suffix *m2-dot-art* *m2-dot-inj*) (m2-a0 *m2-dot-art* *m2-dot-inj*)))

 ))
