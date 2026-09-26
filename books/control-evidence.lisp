; fn: `control log' and `control evidence MESSAGE-ID', rendered by ACL2
; (PKT-209, PRF-185).
;
; A withdrawing article (a cancel, or an ordinary article with one
; Supersedes target) is decided once, when the refresh that first publishes
; it runs `fn-ctl-article-withdrawals' (books/control-visible.lisp) under
; the configuration at its own Store txid.  The owner carries the records
; it decided in its committed view (`fn-own-view-withdrawals',
; books/owner.lisp `fn-own-refresh'), and recovery rebuilds the same list
; (`fn-ctl-refresh-withdrawals-is-the-journal',
; `fn-ctl-articles-withdrawals-is-the-journal').  Until now an operator could
; not read that list, nor why a cancel withdrew nothing.
;
;   control log                 one line per withdrawal record the owner
;                               holds, in its order: target, cause,
;                               principal, the principal's cancel scope, and
;                               the configuration generation it was decided
;                               under;
;   control evidence MSGID      the decision context of MSGID: whether the
;                               owner holds the article, the txid of its
;                               acceptance record, its stored verdict, the
;                               decision the refresh made for it (the record,
;                               a decline and its reason, or none: it names
;                               no target), and every record naming MSGID as
;                               its target with that record's effect on it.
;
; The running owner renders both over the view it carries
; (`fn-cev-live-report'); with no owner the offline command renders them
; over the replayed Store, deciding the records as recovery does
; (`fn-cev-offline-report').  They travel as FNLS pages
; (books/native-live-status.lisp): a request carrying a report kind and an
; argument is FNLS frame kind 3 (`fn-cev-request-encode'); FNLS kinds 1 and
; 2 are unchanged, so an old client never meets it, and an old owner answers
; it with the plain refusal (it decodes as nothing it knows).  No FNCT kind
; is taken.
;
; KEYSTONE `fn-cev-evidence-decision-is-in-the-log': under the owner's
; maintained relation (the carried records are the journal of the carried
; archive), the decision `control evidence' prints for a stored article is
; a record of `control log' exactly when it is a withdrawal record; and
; `fn-cev-decision-line-is-a-log-line': the words of that decision are one
; of the log's lines, so the two verbs cannot disagree.
;
; Cost (pessimistic, per request, under the owner mutex): `control log' is
; one pass over the records |WS|; `control evidence' one walk of the carried
; archive N for the article, one article parse, one walk of the Store's
; records R for its txid (`fn-ctl-record-txid', decoding signed composites
; before the match) and of the configuration journal, and one pass over WS.
; The offline command decides every record as recovery does: N article
; parses.  Paging bounds each reply (`fn-nls-page'), not the render.
;
; Prefix `fn-cev-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "control-evidence-grammar")
(include-book "native-live-status")
(include-book "native-control-reason")
(include-book "control-visible")

; -----------------------------------------------------------------------------
; Words

(defun fn-cev-string (x)
  (declare (xargs :guard t))
  (if (and (stringp x) (not (equal x ""))) (fn-nls-text x) (fn-nls-text "-")))

(defun fn-cev-scope-words (scope)
  (declare (xargs :guard t))
  (if (consp scope)
      (append (fn-cev-string (car scope))
              (if (consp (cdr scope))
                  (cons 44 (fn-cev-scope-words (cdr scope)))
                nil))
    nil))

(defun fn-cev-scope (scope)
  (declare (xargs :guard t))
  (if (consp scope) (fn-cev-scope-words scope) (fn-nls-text "-")))

(defun fn-cev-word (x)
  (declare (xargs :guard t))
  (fn-nctrl-reason-word x))

; The fields of withdrawal record W, after its first word.
(defun fn-cev-withdrawal-fields (w)
  (declare (xargs :guard t))
  (append (fn-nls-text " target=") (fn-cev-string (fn-ctl-w-target w))
          (fn-nls-text " cause=") (fn-cev-string (fn-ctl-w-cause w))
          (fn-nls-text " principal=") (fn-cev-string (fn-ctl-w-principal w))
          (fn-nls-text " scope=") (fn-cev-scope (fn-ctl-w-scope w))
          (fn-nls-field "generation" (fn-ctl-w-generation w))))

; One line of `control log'.
(defun fn-cev-log-line (w)
  (declare (xargs :guard t))
  (append (fn-nls-text "withdrawal") (fn-cev-withdrawal-fields w) *fn-nls-lf*))

(defun fn-cev-log-lines (ws)
  (declare (xargs :guard t))
  (if (consp ws)
      (cons (fn-cev-log-line (car ws)) (fn-cev-log-lines (cdr ws)))
    nil))

(defun fn-cev-join (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (append (true-list-fix (car lines)) (fn-cev-join (cdr lines)))
    nil))

; `control log': the count, then one line per record in the owner's order.
(defun fn-cev-log-report (ws)
  (declare (xargs :guard t))
  (append (fn-nls-text "withdrawals=") (fn-nls-nat (len ws)) *fn-nls-lf*
          (fn-cev-join (fn-cev-log-lines ws))))

; -----------------------------------------------------------------------------
; The decision context of one Message-ID

(defun fn-cev-find-article (msgid arts)
  (declare (xargs :guard t))
  (if (consp arts)
      (if (and (consp (car arts)) (equal (fn-article-msgid (car arts)) msgid))
          (car arts)
        (fn-cev-find-article msgid (cdr arts)))
    nil))

; The decision the refresh made for stored article A: the plan
; `fn-ctl-article-withdrawals' computes (a withdrawal record, or
; (:decline REASON)), or nil when A names no target.
(defun fn-cev-plan (a verdicts records configs)
  (declare (xargs :guard t))
  (if (consp a)
      (let ((target (fn-ctl-target-octets (fn-article-payload a))))
        (if target
            (fn-ctl-withdrawal-plan
             (fn-article-msgid a)
             (fn-ctl-lookup-verdict (fn-article-msgid a) verdicts)
             target
             (fn-ctl-config-at (fn-ctl-record-txid (fn-article-msgid a) records)
                               configs))
          nil))
    nil))

(defun fn-cev-decision-line (plan)
  (declare (xargs :guard t))
  (cond ((fn-ctl-withdrawalp plan)
         (append (fn-nls-text "decision=") (fn-cev-log-line plan)))
        ((and (consp plan) (equal (car plan) :decline))
         (append (fn-nls-text "decision=declined reason=")
                 (fn-cev-word (fn-ctl-at 1 plan)) *fn-nls-lf*))
        (t (append (fn-nls-text "decision=none") *fn-nls-lf*))))

; The effect of W on the stored target A (nil when A is not stored).
(defun fn-cev-effect-words (w a verdicts)
  (declare (xargs :guard t))
  (if (consp a)
      (let ((effect (fn-ctl-withdrawal-effect
                     w (fn-article-groups a)
                     (fn-ctl-lookup-verdict (fn-article-msgid a) verdicts))))
        (if (fn-ctl-effect-withdrawsp effect)
            (append (fn-nls-text " effect=") (fn-cev-word effect))
          (append (fn-nls-text " effect=declined reason=")
                  (fn-cev-word (fn-ctl-at 1 effect)))))
    (fn-nls-text " effect=target-absent")))

; Every record of WS whose target is MSGID, with its effect on A.
(defun fn-cev-targeting-lines (msgid ws a verdicts)
  (declare (xargs :guard t))
  (if (consp ws)
      (if (and (fn-ctl-withdrawalp (car ws))
               (equal (fn-ctl-w-target (car ws)) msgid))
          (append (fn-nls-text "withdrawn-by")
                  (fn-cev-withdrawal-fields (car ws))
                  (fn-cev-effect-words (car ws) a verdicts)
                  *fn-nls-lf*
                  (fn-cev-targeting-lines msgid (cdr ws) a verdicts))
        (fn-cev-targeting-lines msgid (cdr ws) a verdicts))
    nil))

(defun fn-cev-verdict-word (verdict)
  (declare (xargs :guard t))
  (if verdict (fn-cev-word (fn-stx-verdict-token verdict)) (fn-nls-text "unsigned")))

(defun fn-cev-txid-words (txid)
  (declare (xargs :guard t))
  (if (natp txid) (fn-nls-nat txid) (fn-nls-text "-")))

(defun fn-cev-evidence-report (msgid ws raw verdicts records configs)
  (declare (xargs :guard t))
  (let ((a (fn-cev-find-article msgid raw)))
    (append (fn-nls-text "evidence message-id=") (fn-cev-string msgid)
            (if (consp a)
                (append (fn-nls-text " stored=yes txid=")
                        (fn-cev-txid-words (fn-ctl-record-txid msgid records))
                        (fn-nls-text " verdict=")
                        (fn-cev-verdict-word (fn-ctl-lookup-verdict msgid verdicts))
                        *fn-nls-lf*
                        (fn-cev-decision-line (fn-cev-plan a verdicts records configs)))
              (append (fn-nls-text " stored=no") *fn-nls-lf*))
            (fn-cev-targeting-lines msgid ws a verdicts))))

; The report of KIND (`fn-cevg-kindp') over the records WS, the archive RAW,
; the verdicts, the Store's records and its configuration journal.
(defun fn-cev-report (kind ws raw verdicts records configs)
  (declare (xargs :guard t))
  (if (consp kind)
      (fn-cev-evidence-report (cdr kind) ws raw verdicts records configs)
    (fn-cev-log-report ws)))

; What the running owner answers, over the view it carries.  Host:
; host/native-live-status-host.lisp `fn-native-live-status-host-answer'
; (host/native/control.lisp `fnn-control-live-status-answer').
(defun fn-cev-live-report (kind oc)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((o (fn-ocfg-owner oc))
         (v (fn-own-view o))
         (s (fn-own-store o)))
    (fn-cev-report kind (fn-own-view-withdrawals v) (fn-own-view-raw v)
                   (fn-own-view-verdicts v)
                   (fn-sf-records (fn-sn-files s)) (fn-sn-config-history s))))

; What the offline command prints over the Store it replayed: the records
; decided as recovery decides them (`fn-ctl-articles-withdrawals').  Host:
; `fn-native-live-status-host-offline' (host/native/io.lisp
; `fnn-command-live-report').
(defun fn-cev-offline-report (kind s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((raw (fn-state-articles (fn-node-acceptance (fn-sn-node s))))
         (verdicts (fn-sn-verdicts s))
         (records (fn-sf-records (fn-sn-files s)))
         (configs (fn-sn-config-history s)))
    (fn-cev-report kind (fn-ctl-articles-withdrawals raw verdicts records configs)
                   raw verdicts records configs)))

; -----------------------------------------------------------------------------
; The request: FNLS frame kind 3, (uint CODE, uint OFFSET, bytes ARGUMENT).

(defconst *fn-cev-request-kind* 3)

(defun fn-cev-kind-code (kind)
  (declare (xargs :guard t))
  (cond ((equal kind :control-log) 8)
        ((and (consp kind) (equal (car kind) :control-evidence)) 9)
        (t 0)))

(defun fn-cev-kind-argument (kind)
  (declare (xargs :guard t))
  (if (consp kind) (fn-record-string-octets (cdr kind)) nil))

(defun fn-cev-request-encode (kind offset)
  (declare (xargs :guard t))
  (if (not (and (fn-cevg-kindp kind) (fn-record-uint32p offset)))
      :bad
    (fn-nls-seal *fn-cev-request-kind*
                 (append (fn-cbor-encode (cons :uint (fn-cev-kind-code kind)))
                         (fn-cbor-encode (cons :uint offset))
                         (fn-record-item-encode
                          (cons :bytes (fn-cev-kind-argument kind)))))))

(defun fn-cev-code-kind (code argument)
  (declare (xargs :guard t))
  (cond ((and (equal code 8) (null argument)) :control-log)
        ((and (equal code 9) (fn-cbor-octet-listp argument))
         (let ((kind (cons :control-evidence (fn-record-octets-string argument))))
           (if (fn-cevg-kindp kind) kind nil)))
        (t nil)))

(defun fn-cev-request-decode (octets)
  "(:live-status KIND OFFSET), or (:refused REASON)."
  (declare (xargs :guard t :verify-guards nil))
  (let ((opened (fn-nls-open octets *fn-cev-request-kind*)))
    (if (not (fn-frame-result-okp opened))
        (list :refused :frame)
      (let* ((r1 (fn-record-read-uint (fn-frame-result-payload opened)))
             (r2 (fn-record-read-uint (fn-record-parse-rest r1)))
             (r3 (fn-record-read-bytes (fn-record-parse-rest r2))))
        (if (not (and (fn-record-parse-okp r1) (fn-record-parse-okp r2)
                      (fn-record-parse-okp r3)
                      (natp (fn-record-parse-value r2))
                      (null (fn-record-parse-rest r3))))
            (list :refused :fields)
          (let ((kind (fn-cev-code-kind (fn-record-parse-value r1)
                                        (fn-record-parse-value r3))))
            (if kind
                (list :live-status kind (fn-record-parse-value r2))
              (list :refused :kind))))))))

; Either request the owner pages: a status report (frame kind 1) or a
; control report (frame kind 3).
(defun fn-cev-any-request-decode (octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((plain (fn-nls-request-decode octets)))
    (if (equal (car plain) :live-status)
        plain
      (fn-cev-request-decode octets))))

(defun fn-cev-any-request-encode (kind offset)
  (declare (xargs :guard t))
  (if (fn-cevg-kindp kind)
      (fn-cev-request-encode kind offset)
    (fn-nls-request-encode kind offset)))

; -----------------------------------------------------------------------------
; The keystones

(defthm fn-cev-find-article-is-a-member
  (implies (fn-cev-find-article msgid arts)
           (member-equal (fn-cev-find-article msgid arts) arts)))

(defthm fn-cev-plan-is-the-article-withdrawal-by-definition
  (equal (fn-ctl-article-withdrawals a verdicts records configs)
         (if (fn-ctl-withdrawalp (fn-cev-plan a verdicts records configs))
             (list (fn-cev-plan a verdicts records configs))
           nil))
  :hints (("Goal" :in-theory (e/d (fn-ctl-article-withdrawals fn-cev-plan)
                                  (fn-ctl-withdrawal-plan fn-ctl-withdrawalp
                                      fn-ctl-target-octets fn-ctl-config-at
                                      fn-ctl-record-txid fn-ctl-lookup-verdict)))))

(defthm fn-cev-journal-records-are-withdrawals
  (implies (member-equal w (fn-ctl-articles-withdrawals arts verdicts records configs))
           (fn-ctl-withdrawalp w))
  :hints (("Goal" :induct (fn-ctl-articles-withdrawals arts verdicts records configs)
           :in-theory (e/d (fn-ctl-articles-withdrawals)
                           (fn-ctl-withdrawalp fn-cev-plan fn-ctl-article-withdrawals
                            fn-ctl-articles-withdrawals-is-the-journal)))))

(defthm fn-cev-journal-holds-each-articles-record
  (implies (and (member-equal a arts)
                (fn-ctl-withdrawalp (fn-cev-plan a verdicts records configs)))
           (member-equal (fn-cev-plan a verdicts records configs)
                         (fn-ctl-articles-withdrawals arts verdicts records configs)))
  :hints (("Goal" :induct (len arts)
           :in-theory (e/d (fn-ctl-articles-withdrawals)
                           (fn-ctl-withdrawalp fn-cev-plan fn-ctl-article-withdrawals
                            fn-ctl-articles-withdrawals-is-the-journal)))))

(defthm fn-cev-plan-of-no-article
  (equal (fn-cev-plan nil verdicts records configs) nil)
  :hints (("Goal" :in-theory (enable fn-cev-plan))))

(defthm fn-cev-journal-holds-no-nil
  (not (member-equal nil (fn-ctl-articles-withdrawals arts verdicts records configs)))
  :hints (("Goal" :in-theory (disable fn-ctl-articles-withdrawals fn-ctl-withdrawalp
                                      fn-ctl-articles-withdrawals-is-the-journal)
           :use ((:instance fn-cev-journal-records-are-withdrawals (w nil))))))

; KEYSTONE.  The subject is `fn-cev-evidence-report''s decision
; (`fn-cev-plan' of the stored article `fn-cev-find-article' names), which
; host/native-live-status-host.lisp `fn-native-live-status-host-answer'
; renders through `fn-cev-live-report'.  WS is the owner's carried records;
; the one hypothesis is the owner's maintained relation (established by
; `fn-own-start''s refresh, preserved by every `fn-own-refresh':
; `fn-ctl-refresh-withdrawals-is-the-journal' with
; `fn-ctl-articles-withdrawals-is-the-journal'; the offline report
; establishes it by construction).
(defthm fn-cev-evidence-decision-is-in-the-log
  (implies (equal ws (fn-ctl-articles-withdrawals raw verdicts records configs))
           (iff (member-equal (fn-cev-plan (fn-cev-find-article msgid raw)
                                           verdicts records configs)
                              ws)
                (fn-ctl-withdrawalp (fn-cev-plan (fn-cev-find-article msgid raw)
                                                 verdicts records configs))))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawalp fn-cev-plan
                                      fn-cev-find-article
                                      fn-ctl-articles-withdrawals
                                      fn-ctl-articles-withdrawals-is-the-journal)
           :cases ((fn-cev-find-article msgid raw)))
          ("Subgoal 1" :use ((:instance fn-cev-journal-holds-each-articles-record
                            (a (fn-cev-find-article msgid raw)) (arts raw))
                 (:instance fn-cev-journal-records-are-withdrawals
                            (w (fn-cev-plan (fn-cev-find-article msgid raw)
                                            verdicts records configs))
                            (arts raw))))))

(defthm fn-cev-log-lines-member
  (implies (member-equal w ws)
           (member-equal (fn-cev-log-line w) (fn-cev-log-lines ws)))
  :hints (("Goal" :in-theory (disable fn-cev-log-line))))

; The words of a withdrawing decision are "decision=" and one of the lines
; `control log' prints over the same records.
(defthm fn-cev-decision-line-is-a-log-line
  (implies (and (equal ws (fn-ctl-articles-withdrawals raw verdicts records configs))
                (fn-ctl-withdrawalp (fn-cev-plan (fn-cev-find-article msgid raw)
                                                 verdicts records configs)))
           (let ((plan (fn-cev-plan (fn-cev-find-article msgid raw)
                                    verdicts records configs)))
             (and (equal (fn-cev-decision-line plan)
                         (append (fn-nls-text "decision=") (fn-cev-log-line plan)))
                  (member-equal (fn-cev-log-line plan) (fn-cev-log-lines ws)))))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawalp fn-cev-plan
                                      fn-cev-find-article fn-cev-log-line
                                      fn-ctl-articles-withdrawals fn-cev-log-lines)
           :use ((:instance fn-cev-evidence-decision-is-in-the-log)
                 (:instance fn-cev-log-lines-member
                            (w (fn-cev-plan (fn-cev-find-article msgid raw)
                                            verdicts records configs)))))))

; `control log' prints one line per record.
(defthm fn-cev-log-lines-len
  (equal (len (fn-cev-log-lines ws)) (len ws))
  :hints (("Goal" :in-theory '(fn-cev-log-lines len car-cons cdr-cons))))

(in-theory (disable fn-cev-plan-is-the-article-withdrawal-by-definition
                    fn-cev-plan fn-cev-find-article fn-cev-report
                    fn-cev-evidence-report fn-cev-log-report))
