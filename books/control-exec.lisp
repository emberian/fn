; fn: control-message execution (spike/control; design 2026-09-25 packets
; C2 to C4).  Every decision a control article causes is made here; the host
; carries it out and computes nothing of its own.
;
; SPIKE: defers logic-mode admission and guard verification of every fn-ctl-
; decision in this book (proof owner books/control-exec.lisp on dev).
;
; The durable home of every decision on the spike is the configuration's
; policy slot (`:set-policy' rows, staged through the operator's assured live
; path, fn-ocfg-step and fn-ocl-publish):
;
;   "ctl-grant NS P"   verbs | "revoked"     the operator's grant (native-admin)
;   "ctl-d MSGID"      the decision for the control article MSGID, one of
;                        "declined REASON"
;                        "cancel TARGET P NS|- GEN"  (a withdrawal record)
;                        "group newgroup|rmgroup NAME SERIAL P"
;                        "report SERIAL SCOPE +a +b -c ..."
;   "ctl-hw NAME"      the highest executed FN-Control-Serial for group NAME
;   "ctl-applied SCOPE" the last applied checkgroups serial for SCOPE
;
; SPIKE: defers the withdrawal and declined-discharge Store records and the
; `cause' field on configuration records (proof owners books/store-node.lisp,
; books/config-records.lisp): a decision is a policy row written in the same
; configuration record as the group delta it causes, so the discharge is
; atomic with the change; a cancel's record is its own generation.
; SPIKE: defers the record width: a decision longer than a label (256 octets)
; is recorded "declined record-width" (bound work never data, D27; dev's
; Store record has no such cap).
(in-package "ACL2")
(include-book "owner-config")
(include-book "native-admin")
(include-book "control-classify")
(include-book "stx-reader")
(include-book "msgid-index")
(include-book "group-bucket-index")

(program)

; ---------------------------------------------------------------------------
; Text helpers (strings, never the Lisp reader).

(defun fn-ctl-prefixp (prefix text)
  (and (stringp prefix) (stringp text)
       (<= (length prefix) (length text))
       (equal (subseq text 0 (length prefix)) prefix)))

(defun fn-ctl-after (prefix text)
  (subseq text (length prefix) (length text)))

(defun fn-ctl-split-aux (chars cur acc)
  (cond ((atom chars)
         (reverse (if cur (cons (coerce (reverse cur) 'string) acc) acc)))
        ((member (car chars) '(#\Space #\Tab #\Newline #\Return))
         (fn-ctl-split-aux (cdr chars) nil
                           (if cur (cons (coerce (reverse cur) 'string) acc) acc)))
        (t (fn-ctl-split-aux (cdr chars) (cons (car chars) cur) acc))))

(defun fn-ctl-split (text)
  (if (stringp text) (fn-ctl-split-aux (coerce text 'list) nil nil) nil))

(defun fn-ctl-split-commas-aux (chars cur acc)
  (cond ((atom chars) (reverse (cons (coerce (reverse cur) 'string) acc)))
        ((eql (car chars) #\,)
         (fn-ctl-split-commas-aux (cdr chars) nil
                                  (cons (coerce (reverse cur) 'string) acc)))
        (t (fn-ctl-split-commas-aux (cdr chars) (cons (car chars) cur) acc))))

(defun fn-ctl-split-commas (text)
  (if (stringp text) (fn-ctl-split-commas-aux (coerce text 'list) nil nil) nil))

(defun fn-ctl-join (words)
  (cond ((atom words) "")
        ((atom (cdr words)) (car words))
        (t (concatenate 'string (car words) " " (fn-ctl-join (cdr words))))))

(defun fn-ctl-digitsp (chars)
  (and (consp chars)
       (if (consp (cdr chars))
           (and (digit-char-p (car chars)) (fn-ctl-digitsp (cdr chars)))
         (and (digit-char-p (car chars)) t))))

; RFC 5537 section 5.2.3 compares serials zero-padded as strings; for digit
; strings that is numeric order.
(defun fn-ctl-digits-value (chars acc)
  (if (atom chars) acc
    (fn-ctl-digits-value (cdr chars) (+ (* 10 acc) (digit-char-p (car chars))))))

(defun fn-ctl-decimal (text)
  (if (and (stringp text) (fn-ctl-digitsp (coerce text 'list)))
      (fn-ctl-digits-value (coerce text 'list) 0)
    nil))

(defun fn-ctl-nat-string (n)
  (if (natp n) (coerce (explode-nonnegative-integer n 10 nil) 'string) "0"))

; ---------------------------------------------------------------------------
; Grants (the operator's rows, books/native-admin.lisp control plan).

(defun fn-ctl-grants (rows)
  ; ((NS P VERBS) ...) for every live grant row.
  (if (atom rows) nil
    (let* ((row (car rows))
           (a (fn-cfg-row-a row))
           (b (fn-cfg-row-b row))
           (rest (fn-ctl-grants (cdr rows))))
      (if (and (fn-ctl-prefixp "ctl-grant " a) (stringp b)
               (not (equal b "revoked")))
          (let ((words (fn-ctl-split (fn-ctl-after "ctl-grant " a))))
            (if (equal (len words) 2)
                (cons (list (car words) (cadr words) (fn-ctl-split-commas b))
                      rest)
              rest))
        rest))))

(defun fn-ctl-ns-covers (ns group)
  (and (stringp ns) (stringp group)
       (if (fn-ctl-prefixp "*" (reverse ns))
           (let ((base (fn-native-admin-namespace-base ns)))
             (or (equal group base)
                 (fn-ctl-prefixp (concatenate 'string base ".") group)))
         (equal group ns))))

(defun fn-ctl-ns-covers-all (ns groups)
  (if (atom groups) t
    (and (fn-ctl-ns-covers ns (car groups))
         (fn-ctl-ns-covers-all ns (cdr groups)))))

; The namespace of a grant to P for VERB covering every one of GROUPS.
(defun fn-ctl-grant-covering (p verb groups grants)
  (if (atom grants) nil
    (let ((g (car grants)))
      (if (and (equal (cadr g) p)
               (member-equal verb (caddr g))
               (consp groups)
               (fn-ctl-ns-covers-all (car g) groups))
          (car g)
        (fn-ctl-grant-covering p verb groups (cdr grants))))))

; Any grant to P for VERB at all (for the :no-grant / :verb-not-granted split).
(defun fn-ctl-grant-to (p grants)
  (if (atom grants) nil
    (or (equal (cadr (car grants)) p) (fn-ctl-grant-to p (cdr grants)))))

(defun fn-ctl-policy-lookup (label rows)
  (if (atom rows) nil
    (if (equal (fn-cfg-row-a (car rows)) label)
        (fn-cfg-row-b (car rows))
      (fn-ctl-policy-lookup label (cdr rows)))))

(defun fn-ctl-grants-for (p verb grants)
  (if (atom grants) nil
    (let ((g (car grants)))
      (if (and (equal (cadr g) p) (member-equal verb (caddr g)))
          (car g)
        (fn-ctl-grants-for p verb (cdr grants))))))

(defun fn-ctl-create-all (names)
  (if (atom names) nil
    (cons (fn-cfg-create-group (car names) *fn-cfg-default-policy-id*)
          (fn-ctl-create-all (cdr names)))))

(defun fn-ctl-retire-all (names)
  (if (atom names) nil
    (cons (fn-cfg-remove-group (car names)) (fn-ctl-retire-all (cdr names)))))

(defun fn-ctl-in-scope-any (name scopes)
  (if (atom scopes) nil
    (or (fn-ctl-ns-covers (concatenate 'string (car scopes) ".*") name)
        (fn-ctl-in-scope-any name (cdr scopes)))))

; ---------------------------------------------------------------------------
; The article side: classification, fields, the signer.

(defconst *fn-ctl-approved-name* '(97 112 112 114 111 118 101 100))
(defconst *fn-ctl-serial-name*
  ; "fn-control-serial"
  '(102 110 45 99 111 110 116 114 111 108 45 115 101 114 105 97 108))

(defun fn-ctl-field-text (name payload)
  ; The unfolded value of the one field NAME, trimmed, or nil.
  (let ((parsed (fn-article-parse payload)))
    (if (not (fn-article-result-okp parsed)) nil
      (let ((hits (fn-ctl-fields-named
                   name (fn-article-fields (fn-article-result-article parsed)))))
        (if (and (consp hits) (atom (cdr hits)))
            (let ((words (fn-ctl-split (fn-record-octets-string
                                        (fn-article-field-unfolded-value
                                         (car hits))))))
              (fn-ctl-join words))
          nil)))))

(defun fn-ctl-body-text (payload)
  (let ((parsed (fn-article-parse payload)))
    (if (fn-article-result-okp parsed)
        (fn-record-octets-string
         (fn-article-body (fn-article-result-article parsed)))
      "")))

(defun fn-ctl-octet-strings (xs)
  (if (atom xs) nil
    (cons (fn-record-octets-string (car xs)) (fn-ctl-octet-strings (cdr xs)))))

; The signer as this node recorded it at acceptance, from the pinned
; historical verdict (never a current keyring): (:verified P), (:carried P)
; or (:unsigned).
(defun fn-ctl-signer (msgid verdicts)
  (let* ((v (fn-stx-reader-lookup msgid verdicts))
         (token (fn-stx-verdict-token v))
         (detail (fn-stx-verdict-detail v)))
    (if (and (member-eq token '(:verified :carried))
             (true-listp detail) (equal (len detail) 32))
        (list token (fn-record-octets-string (fn-stx-hex-octets detail)))
      (list :unsigned))))

; ---------------------------------------------------------------------------
; fn-ctl-authorize: the design's authority decision (section 2.3).
; CLASSIFIED is fn-ctl-classify-octets; SIGNER fn-ctl-signer; GROUPS the
; groups the verb acts on.  (:execute NS) or (:decline REASON).
; Only a principal this node verified (:verified) executes: :carried (D23)
; and unsigned never do (rule 4).

(defun fn-ctl-authorize (verb signer groups grants approvedp)
  (cond ((member-equal verb '("ihave" "sendme"))
         (list :decline "unsupported-verb"))
        ((not (member-equal verb *fn-ctl-grant-verbs*))
         (list :decline "unsupported-verb"))
        ((eq (car signer) :unsigned) (list :decline "unsigned"))
        ((eq (car signer) :carried) (list :decline "carried"))
        ((and (not (equal verb "cancel")) (not approvedp))
         (list :decline "no-approved"))
        (t (let ((ns (fn-ctl-grant-covering (cadr signer) verb groups grants)))
             (cond (ns (list :execute ns))
                   ((not (fn-ctl-grant-to (cadr signer) grants))
                    (list :decline "no-grant"))
                   (t (list :decline "outside-namespace")))))))

; ---------------------------------------------------------------------------
; The decision for one filed control article: a list of configuration
; deltas, always containing its own "ctl-d MSGID" row (so every filed control
; article is discharged exactly once: pending = no row).

(defun fn-ctl-decision-row (msgid text)
  (let ((text (if (<= (length text) *fn-cfg-max-label*) text
                "declined record-width")))
    (fn-cfg-set-policy (concatenate 'string "ctl-d " msgid) text)))

(defun fn-ctl-cancel-decision (msgid args signer grants gen)
  ; RFC 5537 section 5.3: `cancel <msg-id>'.  An author's cancel needs no
  ; grant: whether it withdraws is decided against the target's own
  ; historical verdict when the view is built (fn-ctl-withdrawal-effect), so
  ; a cancel that arrives before its target is remembered (Q2: accept and
  ; hide).  NS is the covering grant's namespace, checked against the
  ; target's groups there too.
  (cond ((not (and (consp args) (atom (cdr args))))
         (list (fn-ctl-decision-row msgid "declined cancel-syntax")))
        ((eq (car signer) :unsigned)
         (list (fn-ctl-decision-row msgid "declined unsigned")))
        ((eq (car signer) :carried)
         (list (fn-ctl-decision-row msgid "declined carried")))
        (t (let* ((p (cadr signer))
                  (ns (let ((g (fn-ctl-grants-for p "cancel" grants)))
                        (if g g "-"))))
             (list (fn-ctl-decision-row
                    msgid (fn-ctl-join (list "cancel" (car args) p ns
                                             (fn-ctl-nat-string gen)))))))))

(defun fn-ctl-group-decision (msgid verb args signer payload grants cfg)
  ; newgroup NAME [moderated] / rmgroup NAME, ordered by the authority's
  ; signed FN-Control-Serial (section 2.6), never by arrival.
  (let* ((name (if (consp args) (car args) nil))
         (flags (if (consp args) (cdr args) nil))
         (serial (fn-ctl-decimal (fn-ctl-field-text *fn-ctl-serial-name* payload)))
         (approvedp (and (fn-ctl-field-text *fn-ctl-approved-name* payload) t))
         (decision (fn-ctl-authorize verb signer (if name (list name) nil)
                                     grants approvedp))
         (rows (fn-cfg-policies (fn-cfg-value cfg)))
         (hw (fn-ctl-decimal (fn-ctl-policy-lookup
                              (concatenate 'string "ctl-hw " (or name "")) rows)))
         (gen (fn-cfg-generation cfg))
         (live (and name (fn-cfg-group-livep (fn-cfg-value cfg) gen name))))
    (cond
     ((not (and (stringp name) (<= (len flags) 1)))
      (list (fn-ctl-decision-row msgid "declined group-syntax")))
     ((eq (car decision) :decline)
      (list (fn-ctl-decision-row
             msgid (concatenate 'string "declined " (cadr decision)))))
     ((and (equal verb "newgroup") (consp flags))
      (list (fn-ctl-decision-row
             msgid (if (equal (car flags) "moderated")
                       "declined moderation-unsupported"
                     "declined unknown-flag"))))
     ((not (fn-native-admin-group-name-creatablep name))
      (list (fn-ctl-decision-row msgid "declined not-creatable")))
     ((not serial) (list (fn-ctl-decision-row msgid "declined no-serial")))
     ((and hw (<= serial hw))
      (list (fn-ctl-decision-row msgid "declined stale-serial")))
     (t
      (let ((record (fn-ctl-decision-row
                     msgid (fn-ctl-join (list "group" verb name
                                              (fn-ctl-nat-string serial)
                                              (cadr signer)))))
            (mark (fn-cfg-set-policy (concatenate 'string "ctl-hw " name)
                                     (fn-ctl-nat-string serial))))
        ;; The delta is exactly the operator's (fn-ocl-request-deltas's
        ;; :create-group / :remove-group, books/native-admin.lisp
        ;; fn-native-admin-plan-deltas), staged with the decision and the
        ;; serial high-water in one configuration record.  A create of a
        ;; live group or a retire of an absent one changes no group and
        ;; still advances the high-water, so every arrival order of one
        ;; article set ends at the highest serial's state.
        (cond ((and (equal verb "newgroup") (not live))
               (list (fn-cfg-create-group name *fn-cfg-default-policy-id*)
                     record mark))
              ((and (equal verb "rmgroup") live)
               (list (fn-cfg-remove-group name) record mark))
              (t (list record mark))))))))

; checkgroups [chkscope] [#chksernr]: a report, never a change (2.7).
(defun fn-ctl-checkgroups-args (args scope serial)
  (if (atom args) (mv scope serial)
    (let ((w (fn-record-octets-string (car args))))
      (if (fn-ctl-prefixp "#" w)
          (fn-ctl-checkgroups-args (cdr args) scope
                                   (fn-ctl-decimal (fn-ctl-after "#" w)))
        (fn-ctl-checkgroups-args (cdr args) (cons w scope) serial)))))

(defun fn-ctl-body-lines-aux (chars cur acc)
  (cond ((atom chars) (reverse (if cur (cons (coerce (reverse cur) 'string) acc) acc)))
        ((eql (car chars) #\Newline)
         (fn-ctl-body-lines-aux (cdr chars) nil
                                (cons (coerce (reverse cur) 'string) acc)))
        ((eql (car chars) #\Return) (fn-ctl-body-lines-aux (cdr chars) cur acc))
        (t (fn-ctl-body-lines-aux (cdr chars) (cons (car chars) cur) acc))))

(defun fn-ctl-in-scope (name scopes)
  (if (atom scopes) t
    (fn-ctl-in-scope-any name scopes)))

; The groups the body lists (first word of each line) that are creatable
; and inside the scope; RFC 5537 section 5.2.3 MUST honour chkscope.
(defun fn-ctl-checkgroups-names (lines scopes)
  (if (atom lines) nil
    (let* ((words (fn-ctl-split (car lines)))
           (name (if (consp words) (car words) nil))
           (rest (fn-ctl-checkgroups-names (cdr lines) scopes)))
      (if (and name (fn-native-admin-group-name-creatablep name)
               (fn-ctl-in-scope name scopes)
               (not (member-equal name rest)))
          (cons name rest)
        rest))))

(defun fn-ctl-scoped-live (names scopes)
  (if (atom names) nil
    (if (and (fn-ctl-in-scope (car names) scopes)
             (not (fn-ctl-control-group-namep (car names))))
        (cons (car names) (fn-ctl-scoped-live (cdr names) scopes))
      (fn-ctl-scoped-live (cdr names) scopes))))

(defun fn-ctl-set-minus (xs ys)
  (if (atom xs) nil
    (if (member-equal (car xs) ys) (fn-ctl-set-minus (cdr xs) ys)
      (cons (car xs) (fn-ctl-set-minus (cdr xs) ys)))))

(defun fn-ctl-prefix-all (prefix xs)
  (if (atom xs) nil
    (cons (concatenate 'string prefix (car xs)) (fn-ctl-prefix-all prefix (cdr xs)))))

; (mv scopes serial adds retires) of a checkgroups article against CFG.
(defun fn-ctl-checkgroups-diff (args payload cfg)
  (mv-let (scopes serial) (fn-ctl-checkgroups-args args nil nil)
    (let* ((names (fn-ctl-checkgroups-names
                   (fn-ctl-body-lines-aux (coerce (fn-ctl-body-text payload) 'list)
                                          nil nil)
                   scopes))
           (live (fn-ctl-scoped-live
                  (fn-cfg-group-names (fn-cfg-value cfg) (fn-cfg-generation cfg))
                  scopes)))
      (mv scopes serial (fn-ctl-set-minus names live) (fn-ctl-set-minus live names)))))

(defun fn-ctl-checkgroups-decision (msgid args signer payload grants cfg)
  (mv-let (scopes serial adds retires) (fn-ctl-checkgroups-diff args payload cfg)
    (let ((decision (fn-ctl-authorize
                     "checkgroups" signer (if scopes scopes (list "*none*"))
                     grants (and (fn-ctl-field-text *fn-ctl-approved-name* payload) t))))
      (cond ((eq (car decision) :decline)
             (list (fn-ctl-decision-row
                    msgid (concatenate 'string "declined " (cadr decision)))))
            ((not serial) (list (fn-ctl-decision-row msgid "declined no-serial")))
            (t (list (fn-ctl-decision-row
                      msgid
                      (fn-ctl-join
                       (append (list "report" (fn-ctl-nat-string serial)
                                     (fn-ctl-join scopes))
                               (fn-ctl-prefix-all "+" adds)
                               (fn-ctl-prefix-all "-" retires))))))))))

; The operator's apply (`control apply-checkgroups MSGID'): the report's
; delta list against the CURRENT configuration, staged through the ordinary
; live path with the operator as the authority of record, plus the scope's
; applied serial.  :stale-serial when a later report was applied.
(defun fn-ctl-checkgroups-apply-deltas (msgid payload cfg)
  (let* ((rows (fn-cfg-policies (fn-cfg-value cfg)))
         (record (fn-ctl-policy-lookup (concatenate 'string "ctl-d " msgid) rows))
         (classified (fn-ctl-classify-octets payload)))
    (if (not (and (fn-ctl-prefixp "report " record)
                  (consp classified) (eq (car classified) :control)))
        (list :refused :not-a-report)
      (mv-let (scopes serial adds retires)
        (fn-ctl-checkgroups-diff (caddr classified) payload cfg)
        (let* ((label (concatenate 'string "ctl-applied " (fn-ctl-join scopes)))
               (applied (fn-ctl-decimal (fn-ctl-policy-lookup label rows))))
          (if (and applied serial (<= serial applied))
              (list :refused :stale-serial)
            (list :ok
                  (append (fn-ctl-create-all adds)
                          (fn-ctl-retire-all retires)
                          (list (fn-cfg-set-policy
                                 label (fn-ctl-nat-string serial)))))))))))

; The first grant namespace of P for VERB (a cancel's authority basis
; candidate; the target's groups are checked when the view is built).
; The decision deltas for one filed control article ARTICLE (an acceptance
; record) with the pinned VERDICTS, under configuration CFG.
(defun fn-ctl-decide (article verdicts cfg)
  (let* ((msgid (fn-article-msgid article))
         (payload (fn-article-payload article))
         (classified (fn-ctl-classify-octets payload))
         (grants (fn-ctl-grants (fn-cfg-policies (fn-cfg-value cfg))))
         (signer (fn-ctl-signer msgid verdicts)))
    (if (not (and (consp classified) (eq (car classified) :control)))
        (list (fn-ctl-decision-row msgid "declined malformed"))
      (let ((verb (fn-record-octets-string (cadr classified)))
            (args (caddr classified)))
        (cond
         ((equal verb "cancel")
          (fn-ctl-cancel-decision msgid (fn-ctl-octet-strings args) signer grants
                                  (fn-cfg-generation cfg)))
         ((member-equal verb '("newgroup" "rmgroup"))
          (fn-ctl-group-decision msgid verb (fn-ctl-octet-strings args) signer
                                 payload grants cfg))
         ((equal verb "checkgroups")
          (fn-ctl-checkgroups-decision msgid args signer payload grants cfg))
         (t (list (fn-ctl-decision-row
                   msgid (concatenate 'string "declined "
                                      (cadr (fn-ctl-authorize verb signer nil
                                                              grants nil)))))))))))

; ---------------------------------------------------------------------------
; Owed: the first filed control article with no decision row.  The host
; stages its deltas, publishes, and asks again; recovery asks the same
; question, so a kill between acceptance and the configuration record leaves
; the article owed and it is discharged exactly once afterwards.
; SPIKE: defers the incremental owed set (dev: fn-ctl-owed over the recovered
; journals); this scans the archive's control articles per ask.

(defun fn-ctl-control-articlep (article)
  (let ((groups (fn-article-groups article)))
    (and (consp groups) (fn-ctl-control-group-namep (car groups)))))

(defun fn-ctl-first-owed (articles rows)
  (if (atom articles) nil
    (let ((a (car articles)))
      (if (and (fn-ctl-control-articlep a)
               (not (fn-ctl-policy-lookup
                     (concatenate 'string "ctl-d " (fn-article-msgid a)) rows)))
          a
        (fn-ctl-first-owed (cdr articles) rows)))))

; ARCHIVE the unfiltered acceptance state, VERDICTS the Store's, CFG the
; live configuration.  nil when nothing is owed.
(defun fn-ctl-owed-deltas (archive verdicts cfg)
  (let ((owed (fn-ctl-first-owed (reverse (fn-state-articles archive))
                                 (fn-cfg-policies (fn-cfg-value cfg)))))
    (if owed (fn-ctl-decide owed verdicts cfg) nil)))

; ---------------------------------------------------------------------------
; The served view: withdrawal hides, never erases (section 2.5).

; Section 2.5's exact-source rule.  RECORD "cancel T P NS|-"; TARGET T's
; acceptance record; the target's historical verdict names its author.
(defun fn-ctl-withdrawal-effect (p ns target verdicts)
  (let* ((tsigner (fn-ctl-signer (fn-article-msgid target) verdicts))
         (groups (fn-article-groups target)))
    (cond ((and (member-eq (car tsigner) '(:verified :carried))
                (equal (cadr tsigner) p))
           "author")
          ((and (not (equal ns "-")) (consp groups)
                (fn-ctl-ns-covers-all ns groups))
           "authority")
          (t nil))))

; ((CAUSE-MSGID TARGET BASIS-OR-NIL) ...) from the decision rows.
(defun fn-ctl-cancel-records (rows)
  (if (atom rows) nil
    (let* ((a (fn-cfg-row-a (car rows)))
           (b (fn-cfg-row-b (car rows)))
           (rest (fn-ctl-cancel-records (cdr rows))))
      (if (and (fn-ctl-prefixp "ctl-d " a) (fn-ctl-prefixp "cancel " b))
          (let ((w (fn-ctl-split b)))
            (if (equal (len w) 5)
                (cons (list (fn-ctl-after "ctl-d " a) (cadr w) (caddr w) (cadddr w))
                      rest)
              rest))
        rest))))

; (mv withdrawn-msgids items).  ITEMS are the HDR :fn-control lines
; ((:fn-control . MSGID) . octets) for every decided control article.
(defun fn-ctl-effects (records index verdicts withdrawn items)
  (if (atom records) (mv withdrawn items)
    (let* ((r (car records))
           (cause (car r)) (target-id (cadr r)) (p (caddr r)) (ns (cadddr r))
           (target (fn-midx-lookup target-id index))
           (basis (and (consp target)
                       (not (fn-ctl-control-articlep target))
                       (fn-ctl-withdrawal-effect p ns target verdicts)))
           (text (cond (basis (fn-ctl-join (list "executed withdrawal" target-id basis)))
                       ((consp target) "declined no-grant")
                       (t (fn-ctl-join (list "owed target-absent" target-id))))))
      (fn-ctl-effects (cdr records) index verdicts
                      (if basis (cons target-id withdrawn) withdrawn)
                      (cons (cons (cons :fn-control cause)
                                  (fn-record-string-octets text))
                            items)))))

(defun fn-ctl-decision-items (rows)
  ; Every non-cancel decision renders its own row text.
  (if (atom rows) nil
    (let ((a (fn-cfg-row-a (car rows)))
          (b (fn-cfg-row-b (car rows)))
          (rest (fn-ctl-decision-items (cdr rows))))
      (if (and (fn-ctl-prefixp "ctl-d " a) (stringp b)
               (not (fn-ctl-prefixp "cancel " b)))
          (cons (cons (cons :fn-control (fn-ctl-after "ctl-d " a))
                      (fn-record-string-octets
                       (if (fn-ctl-prefixp "group " b)
                           (concatenate 'string "executed reconfigure " b)
                         b)))
                rest)
        rest))))

(defun fn-ctl-remove-withdrawn (articles withdrawn)
  (if (atom articles) nil
    (if (member-equal (fn-article-msgid (car articles)) withdrawn)
        (fn-ctl-remove-withdrawn (cdr articles) withdrawn)
      (cons (car articles) (fn-ctl-remove-withdrawn (cdr articles) withdrawn)))))

; The owner's view with every withdrawn target removed from the archive the
; connections pin (so ARTICLE/HEAD/BODY/STAT by Message-ID answer 430, by
; number 423, and OVER/LISTGROUP/HDR/NEWNEWS/NEXT/LAST skip it; numbers are
; the articles' own memberships, never reused), and the :fn-control items
; added to its verdict list.  Retention and history read the Store, not this
; view, so neither changes.
; SPIKE: defers restating K1 (fn-own-read-is-served-step-on-pinned-prefix)
; over fn-ctl-visible-view; the host applies it after fn-own-refresh
; (host/owner-host.lisp fn-owner-install-ocfg), and the trie and buckets are
; rebuilt over the filtered archive, not refreshed incrementally.
(defun fn-ctl-view-base (view)
  ; (archive index group-index verdicts) of the unfiltered view: a view this
  ; function already filtered carries its base under :fn-ctl-base.
  (let ((verdicts (fn-own-view-verdicts view)))
    (if (and (consp verdicts) (consp (car verdicts))
             (eq (car (car verdicts)) :fn-ctl-base))
        (cdr (car verdicts))
      (list (fn-own-view-archive view) (fn-own-view-index view)
            (fn-own-view-group-index view) verdicts))))

(defun fn-ctl-visible-view (view cfg)
  (let* ((rows (fn-cfg-policies (fn-cfg-value cfg)))
         (records (fn-ctl-cancel-records rows))
         (base (fn-ctl-view-base view))
         (archive (car base))
         (index (cadr base))
         (gindex (caddr base))
         (verdicts (cadddr base)))
    (mv-let (withdrawn items)
      (fn-ctl-effects records index verdicts nil (fn-ctl-decision-items rows))
      (if (and (atom withdrawn) (atom items))
          (fn-own-view-make-group-indexed
           (fn-own-view-version view) (fn-own-view-frontier view)
           archive verdicts index gindex)
        (let* ((articles (if withdrawn
                             (fn-ctl-remove-withdrawn (fn-state-articles archive)
                                                      withdrawn)
                           (fn-state-articles archive)))
               (filtered (if withdrawn
                             (fn-make-state (fn-state-groups archive)
                                            (fn-state-nexts archive)
                                            articles
                                            (fn-state-next-txid archive)
                                            (fn-state-pending archive)
                                            (fn-state-fenced archive))
                           archive)))
          (fn-own-view-make-group-indexed
           (fn-own-view-version view) (fn-own-view-frontier view)
           filtered
           (cons (cons :fn-ctl-base base) (append items verdicts))
           (if withdrawn (fn-midx-build articles) index)
           (if withdrawn (fn-gidx-build articles) gindex)))))))

; The withdrawn Message-IDs of the view (for the operator's `control log').
(defun fn-ctl-withdrawn-of-view (view cfg)
  (let ((base (fn-ctl-view-base view)))
    (mv-let (withdrawn items)
      (fn-ctl-effects (fn-ctl-cancel-records (fn-cfg-policies (fn-cfg-value cfg)))
                      (cadr base) (cadddr base) nil nil)
      (declare (ignore items))
      withdrawn)))

; The owner with its view made visible.
(defun fn-ctl-visible-owner (o cfg)
  (fn-own-make (fn-own-store o) (fn-ctl-visible-view (fn-own-view o) cfg)
               (fn-own-conns o) (fn-own-next-id o) (fn-own-max-conns o)
               (fn-own-pending o) (fn-own-ledger o) (fn-own-clock o)
               (fn-own-facts o) (fn-own-config o) (fn-own-queue o)
               (fn-own-inflight o) (fn-own-feeds o)))
