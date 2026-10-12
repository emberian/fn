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
