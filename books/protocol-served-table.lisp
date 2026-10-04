; protocol-served-table.lisp -- the SERVED columns of the protocol table: a
; command's view policy, effect, forms, costs, quantum and teeth, one row per
; served command (lane def-command, 2026-10-03; consultation c07).
;
; books/protocol-table.lisp is the reply-text source every book that emits a
; reply includes (fn-proto-text), so an edit there recertifies most of the
; tree (753 roots).  The served columns change with the view policy and the
; dispatcher's arms, which only the dispatch books read, so they live here:
; a policy edit costs this book's closure (books/protocol-served.lisp and
; what includes it), not the tree.  A row here is keyed by the protocol
; row's command name; this book refuses to certify unless the two tables
; name the same served commands (fn-proto-served-tablep), so the split
; cannot drift.  Each row is the `def-nntp-command' declaration the lane's
; brief asked for: from it books/protocol-served.lisp generates the served
; dispatcher's clause, each form's view contract, the command's case of the
; pinned-boundary theorem, the view policy's executable sites and the teeth
; the test book owes; tools/protocol_emit.py reads it (joined with the
; protocol table by name) for the spec's served command table
; (specs/nntp.md, tools/docs_check.py) and the debt ratchet
; (tools/view_policy_debt.json).
;
; THE SERVED COLUMNS: a command is a declaration.  Every row the served
; dispatcher answers (a protocol row with :arms, or an :auth row) has a row
; here that states its view policy, or this book refuses to certify
; (fn-proto-served-tablep); a row here names no protocol row, or a served
; protocol row has no row here, likewise.  The columns:
;
;   :view      the view the command reads (the row's default; a form may
;              differ), ONE of
;              :none       no article view (a session, auth or constant
;                          answer; its config/session/clock dependencies are
;                          named in :view-rfc);
;              :pinned     the connection's pinned view: archive, index, the
;                          catalog view V, verdicts, the pinned config
;                          (NNT-042's "other reads stay on that view");
;              :select     re-pinned to the owner's committed view before the
;                          arm, kept iff the reply is 211 (GROUP, LISTGROUP:
;                          books/served.lisp fn-served-advance-eventp is this
;                          column's executable site, *fn-proto-select-names*);
;              :completed  the latest completed durable discovery snapshot,
;                          captured once per response, the pin unmoved
;                          (decisions/command-view-policy-2026-10-03.md, B);
;              :pin-or-completed  by Message-ID: the pinned article when it is
;                          retrievable there, else the completed snapshot,
;                          number fields 0 on fallback (c07 C);
;              :live-index the live Message-ID index (a peer's offer).
;   :view-rfc  the policy's citation and its named dependencies, into the
;              spec's command table.
;   :view-decided  (VIEW ID): a ruling recorded but not landed, ID its open
;              registry row.  DEBT, counted and ratcheted (tools/protocol_emit.py
;              --check); the spec table shows the EXECUTED rule and the debt
;              beside it, never the ruling as the rule.
;   :effect    :none | :select (group and current article, kept iff 211) |
;              :current (may move the current article) | :close | :offer.
;   :forms     the command's FORMS, each (NAME :test TEST [:cat TERM] [:view V]
;              [:effect E] [:decided (V ID)] [:by (LEMMA ...)] [:open (DEF ...)]),
;              tried in order (the last TEST is t): TEST over the served
;              dispatcher's formals SESSION ARCHIVE INDEX VERDICTS ENV KEYWORD
;              ARGS V FN-ARENA FN-CAT, :cat the UNRESTRICTED route's answer
;              (absent: the test's value, a prelude computed once), :view the
;              form's view when it differs from the row's (ARTICLE n and
;              ARTICLE <id> differ), :by the hand -is- theorems the form's
;              case of the pinned-boundary theorem is proved from (names or
;              :instance forms), :open definitions that case opens besides
;              the dispatchers'.  books/protocol-served.lisp generates the
;              dispatcher's clause, one lemma per form (its view CONTRACT:
;              under the form's test and no earlier form's, the result equals
;              the reference on the pinned view), the row's case and the
;              keystone.  A row without :forms is served by the hand arms
;              (books/served-catalog-dispatch.lisp) under its row-level
;              :view, until declared.
;   :cost      what the command costs on each route, (:unrestricted TEXT
;              :restricted TEXT); required with :forms.  The restricted
;              route is the reference walk over the projected pin, so a -cat
;              cost claim is never the restricted client's (c07 F).
;   :quantum   nil, or (:cursor PRED): the reply may be one cursor effect the
;              host drains in quanta (books/served-plan-cursor.lisp); names
;              the def-cursor instance once that generator lands.
;   :teeth     command lines the generated teeth evaluate on both routes.
;
; The constants the macro defines: *fn-proto-select-names* (the :view
; :select rows, fn-served-advance-eventp's keywords), *fn-proto-archive-names*
; (the protocol table's :dispatch :archive rows, fn-nntp-archive-keywordp's),
; *fn-proto-served-names* (every served command) and *fn-proto-cat-rows* (the
; rows with :forms, in table order).

(in-package "ACL2")
(include-book "protocol-table")

; -----------------------------------------------------------------------------
; The schema

(defun fn-proto-row-plist (row)
  (declare (xargs :guard t))
  (and (consp row) (true-listp (cdr row)) (cdr row)))

(defun fn-proto-viewp (x)
  (declare (xargs :guard t))
  (and (member-equal x '(:none :pinned :select :completed :pin-or-completed :live-index)) t))

; A ruling recorded but not landed: (VIEW ID), ID the open registry row that
; carries it (counted debt: tools/protocol_emit.py --check, a ratchet).
(defun fn-proto-decidedp (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (consp x) (fn-proto-viewp (car x))
           (consp (cdr x)) (stringp (cadr x)) (<= 5 (length (cadr x)))
           (null (cddr x)))))

(defun fn-proto-effectp (x)
  (declare (xargs :guard t))
  (and (member-equal x '(:none :select :current :close :offer)) t))

(defun fn-proto-quantump (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (true-listp x) (equal (len x) 2) (equal (car x) :cursor)
           (symbolp (cadr x)) (cadr x) t)))

(defun fn-proto-string-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (stringp (car x)) (fn-proto-string-listp (cdr x)))
    (null x)))

(defun fn-proto-costp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (stringp (fn-proto-plist-get :unrestricted x))
       (stringp (fn-proto-plist-get :restricted x))))

; The lemmas a row's boundary case is proved from: names or :instance forms.
(defun fn-proto-cat-byp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (or (and (symbolp (car x)) (car x))
               (and (consp (car x)) (equal (car (car x)) :instance)
                    (consp (cdr (car x))) (symbolp (cadr (car x)))))
           (fn-proto-cat-byp (cdr x)))
    (null x)))

(defun fn-proto-mentionsp (sym term)
  (declare (xargs :guard t))
  (if (consp term)
      (or (fn-proto-mentionsp sym (car term))
          (fn-proto-mentionsp sym (cdr term)))
    (equal sym term)))

(defun fn-proto-mentions-anyp (syms term)
  (declare (xargs :guard t))
  (if (consp syms)
      (or (fn-proto-mentionsp (car syms) term)
          (fn-proto-mentions-anyp (cdr syms) term))
    nil))

; The view formals a :pinned command's arms may not read.
; A FORM of a served row: (NAME :test TEST [:cat TERM] [:view V] [:effect E]
; [:decided (V ID)] [:by (LEMMA ...)] [:open (DEF ...)]).  TEST is the arm's
; test over the dispatcher's formals; without :cat the arm answers with the
; test's value (a prelude, computed once).  A form's :view defaults to the
; row's.  The forms are tried in order; the last one's TEST is t.
(defun fn-proto-plist-hasp (key plist)
  (declare (xargs :guard t))
  (if (and (consp plist) (consp (cdr plist)))
      (or (equal (car plist) key)
          (fn-proto-plist-hasp key (cddr plist)))
    nil))

(defun fn-proto-formp (x)
  (declare (xargs :guard t))
  (and (consp x) (stringp (car x)) (true-listp (cdr x))
       (let ((plist (cdr x)))
         (and (fn-proto-plist-hasp :test plist)
              (or (null (fn-proto-plist-get :view plist))
                  (fn-proto-viewp (fn-proto-plist-get :view plist)))
              (or (null (fn-proto-plist-get :effect plist))
                  (fn-proto-effectp (fn-proto-plist-get :effect plist)))
              (fn-proto-decidedp (fn-proto-plist-get :decided plist))
              (fn-proto-cat-byp (fn-proto-plist-get :by plist))
              (fn-proto-symbol-listp (fn-proto-plist-get :open plist))))))

(defun fn-proto-formsp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (fn-proto-formp (car x))
       (if (consp (cdr x))
           (fn-proto-formsp (cdr x))
         (and (null (cdr x))
              (equal (fn-proto-plist-get :test (cdr (car x))) t)))))

(defun fn-proto-form-names (forms)
  (declare (xargs :guard t))
  (if (consp forms)
      (cons (if (consp (car forms)) (car (car forms)) nil)
            (fn-proto-form-names (cdr forms)))
    nil))

;; The forms' arms as cond clauses: (TEST TERM), or (TEST) for a prelude.
(defun fn-proto-form-clauses (forms)
  (declare (xargs :guard t))
  (if (consp forms)
      (let ((plist (if (consp (car forms)) (cdr (car forms)) nil)))
        (cons (if (and (true-listp plist) (fn-proto-plist-hasp :cat plist))
                  (list (fn-proto-plist-get :test plist) (fn-proto-plist-get :cat plist))
                (list (if (true-listp plist) (fn-proto-plist-get :test plist) nil)))
              (fn-proto-form-clauses (cdr forms))))
    nil))

(defconst *fn-proto-unpinned-formals* '(live completed))

; The served columns are consistent: a served row (one with :arms) names its
; view, effect and citation; served clauses come with the lemmas and the
; costs their case is stated from; a pinned command reads no other view.
;; -----------------------------------------------------------------------------
;; The served columns read (lane def-command).

(defun fn-proto-row-forms (row)
  (declare (xargs :guard t))
  (fn-proto-plist-get :forms (fn-proto-row-plist row)))

;; A protocol row is served when the reader dispatcher answers it (:arms) or
;; the auth layer does (:dispatch :auth).
(defun fn-proto-servedp (prow)
  (declare (xargs :guard t))
  (and (or (fn-proto-plist-get :arms (fn-proto-row-plist prow))
           (equal (fn-proto-plist-get :dispatch (fn-proto-row-plist prow)) :auth))
       t))

;; The names of the rows with :forms, in table order.
(defun fn-proto-cat-row-names (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (consp (car rows)) (stringp (car (car rows)))
               (fn-proto-row-forms (car rows)))
          (cons (car (car rows)) (fn-proto-cat-row-names (cdr rows)))
        (fn-proto-cat-row-names (cdr rows)))
    nil))

;; One flat clause per row with :forms: ((fn-nntp-keywordp keyword NAME) TERM).
(defun fn-proto-cat-flat-clauses (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (consp (car rows)) (stringp (car (car rows)))
               (fn-proto-row-forms (car rows)))
          (cons `((fn-nntp-keywordp keyword ,(car (car rows)))
                  ,(fn-proto-clauses-term (fn-proto-form-clauses (fn-proto-row-forms (car rows)))))
                (fn-proto-cat-flat-clauses (cdr rows)))
        (fn-proto-cat-flat-clauses (cdr rows)))
    nil))

;; The names of the rows whose :view is VIEW (the :select ones are
;; fn-served-advance-eventp's keywords).
(defun fn-proto-names-with-view (view rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (consp (car rows)) (stringp (car (car rows)))
               (equal (fn-proto-plist-get :view (fn-proto-row-plist (car rows))) view))
          (cons (car (car rows)) (fn-proto-names-with-view view (cdr rows)))
        (fn-proto-names-with-view view (cdr rows)))
    nil))

(defun fn-proto-names-with-dispatch (kind rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (consp (car rows)) (stringp (car (car rows)))
               (equal (fn-proto-plist-get :dispatch (fn-proto-row-plist (car rows))) kind))
          (cons (car (car rows)) (fn-proto-names-with-dispatch kind (cdr rows)))
        (fn-proto-names-with-dispatch kind (cdr rows)))
    nil))

;; Every keyword the served step does something with (the served protocol
;; rows).  HELP's table (books/nntp-help.lisp *fn-nntp-served-command-table*)
;; is checked set-equal to it (books/protocol-served.lisp).
(defun fn-proto-served-names (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (consp (car rows)) (stringp (car (car rows))) (fn-proto-servedp (car rows)))
          (cons (car (car rows)) (fn-proto-served-names (cdr rows)))
        (fn-proto-served-names (cdr rows)))
    nil))

; A served row is consistent: it names its view, effect and citation; its
; forms come with the costs their cases are stated from; the ruling it may
; carry names its registry row; and, a LINT (the contract is each form's
; generated theorem, books/protocol-served.lisp), a pinned command's arms
; (the protocol row's :arms and the forms here) name no live or completed
; view formal.
(defun fn-proto-served-row-okp (row prows)
  (declare (xargs :guard t))
  (and (consp row) (stringp (car row)) (true-listp (cdr row))
       (let* ((plist (cdr row))
              (prow (fn-proto-row (car row) prows))
              (arms (fn-proto-plist-get :arms (fn-proto-row-plist prow)))
              (view (fn-proto-plist-get :view plist))
              (forms (fn-proto-plist-get :forms plist)))
         (and prow
              (fn-proto-servedp prow)
              (fn-proto-viewp view)
              (fn-proto-effectp (fn-proto-plist-get :effect plist))
              (stringp (fn-proto-plist-get :view-rfc plist))
              (fn-proto-decidedp (fn-proto-plist-get :view-decided plist))
              (implies forms
                       (and (fn-proto-formsp forms)
                            (no-duplicatesp-equal (fn-proto-form-names forms))
                            (fn-proto-costp (fn-proto-plist-get :cost plist))))
              (fn-proto-quantump (fn-proto-plist-get :quantum plist))
              (fn-proto-string-listp (fn-proto-plist-get :teeth plist))
              (implies (member-equal view '(:pinned :none))
                       (not (fn-proto-mentions-anyp *fn-proto-unpinned-formals*
                                                    (list arms forms))))))))

(defun fn-proto-served-rows-okp (rows prows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (fn-proto-served-row-okp (car rows) prows)
           (fn-proto-served-rows-okp (cdr rows) prows))
    (null rows)))

(defun fn-proto-memberp (x ys)
  (declare (xargs :guard t))
  (if (consp ys)
      (or (equal x (car ys)) (fn-proto-memberp x (cdr ys)))
    nil))

(defun fn-proto-subsetp (xs ys)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-proto-memberp (car xs) ys) (fn-proto-subsetp (cdr xs) ys))
    t))

; The served table and the protocol table name the same served commands,
; once each: a served command with no row here, or a row here for a command
; the served step does not answer, refuses certification.
(defun fn-proto-served-tablep (rows prows)
  (declare (xargs :guard t))
  (and (fn-proto-served-rows-okp rows prows)
       (no-duplicatesp-equal (fn-proto-names rows))
       (fn-proto-subsetp (fn-proto-served-names prows) (fn-proto-names rows))))

(defmacro defprotocol-served (name &rest rows)
  `(progn
     (defconst ,name ',rows)
     (assert-event (fn-proto-served-tablep ,name *fn-proto-table*)
                   :msg "a served row is malformed, names no served protocol row, or a served protocol row has no served row (fn-proto-served-tablep)")
     (defconst *fn-proto-select-names* (fn-proto-names-with-view :select ,name))
     (defconst *fn-proto-archive-names* (fn-proto-names-with-dispatch :archive *fn-proto-table*))
     (defconst *fn-proto-served-names* (fn-proto-served-names *fn-proto-table*))
     (defconst *fn-proto-cat-rows* (fn-proto-cat-row-names ,name))))

; -----------------------------------------------------------------------------
; The table.  Rows in the protocol table's order.

(defprotocol-served *fn-proto-served-table*

  ("CAPABILITIES"
   :view :none :effect :none :view-rfc "RFC 3977 5.2; no article view: reads the auth config, subject, TLS state, posting configuration, peer context and compression (books/nntp-auth.lisp fn-auth-capability-lines-for-peer)")
  ("HELP"
   :view :none :effect :none :view-rfc "RFC 3977 7.2 (no archive)")
  ("MODE"
   :view :none :effect :none :view-rfc "RFC 3977 5.3 (no archive)")
  ("QUIT"
   :view :none :effect :close :view-rfc "RFC 3977 5.4 (no archive)")
  ("GROUP"
   :view :select :effect :select :view-rfc "NNT-042; RFC 3977 6.1.1.2"
   :forms (("name" :test (and (consp args) (null (cdr args)) (fn-nntp-printable-tokenp (car args)))
            :cat (fn-nntp-group-result-cat session archive (fn-nntp-token-string (car args)) v fn-cat)
            :view :select :effect :select
            :by ((:instance fn-nntp-group-result-cat-is-archive
                            (group (fn-nntp-token-string (car args))))))
           ("syntax" :test t :cat (fn-nntp-single session (fn-proto-text * :syntax))
            :view :none :effect :none))
   :cost (:unrestricted "the carried group summary at the top view, the probe pass otherwise (fn-scat-group-summary, fn-scat-group-low)"
          :restricted "the reference fold over the projected pinned archive (fn-nntp-group-result)")
   :teeth ("GROUP fn.test" "GROUP fn.other" "GROUP fn.none" "GROUP" "GROUP a b"))
  ("LISTGROUP"
   :view :select :effect :select :view-rfc "NNT-042; RFC 3977 6.1.2"
   :forms (("indexed" :test (fn-gidx-pinp index)
            :cat (fn-nntp-listgroup-command-cat session archive args v fn-cat)
            :view :select :effect :select
            :by ((:instance fn-nntp-listgroup-command-cat-is-archive)
                 (:instance fn-scat-built-listgroup-is-fold)
                 (:instance fn-proto-pin-buckets-are-built)))
           ("other" :test t :cat (fn-nntp-archive-command session archive env keyword args fn-arena)
            :view :select :effect :select))
   :cost (:unrestricted "carried group summary and number-table range probes (fn-nntp-listgroup-command-cat)"
          :restricted "the pinned group bucket command, refined to the reference archive fold")
   :teeth ("LISTGROUP fn.test" "LISTGROUP" "LISTGROUP fn.test 2-3" "LISTGROUP fn.none" "LISTGROUP a b c"))
  ("LAST"
   :view :pinned :effect :current :view-rfc "NNT-042 (other reads); RFC 3977 6.1.3"
   :forms (("current" :test (null args)
            :cat (fn-nntp-next-or-last-cat session archive :last v fn-arena fn-cat)
            :view :pinned :effect :current
            :by ((:instance fn-nntp-next-or-last-cat-is-next-or-last (direction :last))))
           ("syntax" :test t :cat (fn-nntp-archive-command session archive env keyword args fn-arena)
            :view :none :effect :none))
   :cost (:unrestricted "number-table probes from the current article to the next visible number, plus one catalog lookup"
          :restricted "the reference fold over the projected pinned archive (fn-nntp-next-or-last)")
   :teeth ("LAST" "LAST 1"))
  ("NEXT"
   :view :pinned :effect :current :view-rfc "NNT-042 (other reads); RFC 3977 6.1.4"
   :forms (("current" :test (null args)
            :cat (fn-nntp-next-or-last-cat session archive :next v fn-arena fn-cat)
            :view :pinned :effect :current
            :by ((:instance fn-nntp-next-or-last-cat-is-next-or-last (direction :next))))
           ("syntax" :test t :cat (fn-nntp-archive-command session archive env keyword args fn-arena)
            :view :none :effect :none))
   :cost (:unrestricted "number-table probes from the current article to the next visible number, plus one catalog lookup"
          :restricted "the reference fold over the projected pinned archive (fn-nntp-next-or-last)")
   :teeth ("NEXT" "NEXT 1"))
  ("ARTICLE"
   :view :pinned :view-decided (:pin-or-completed "PRF-1238") :effect :current :view-rfc "NNT-042 (pinned retrieval; a cancel after the pin leaves the article visible); the number, Message-ID and current forms; numeric success moves the current article; decided c07 C for the Message-ID form only: the pin first, then the completed snapshot, number fields 0 on fallback; RFC 3977 6.2.1"
   :forms (("number-withdrawn" :test (and (consp args) (null (cdr args))
                                         (fn-nntp-number-withdrawn-p-cat session index (car args) v fn-arena fn-cat))
            :cat (fn-nntp-withdrawn-reply session nil)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))))
           ("msgid-withdrawn" :test (and (consp args) (null (cdr args))
                                        (fn-nntp-message-id-tokenp (car args))
                                        (fn-nntp-msgid-withdrawn-p-cat index (car args) v fn-arena fn-cat))
            :cat (fn-nntp-withdrawn-reply session t)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)))
           ("compatibility" :test (fn-rcompat-reply-cat session archive index env keyword args v fn-arena fn-cat)
            :view :pinned :effect :current
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)))
           ("msgid" :test (and (consp args) (null (cdr args)) (fn-nntp-message-id-tokenp (car args)))
            :cat (fn-nntp-msgid-retrieval-cat session v :article (car args) fn-arena fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-msgid-retrieval-cat-is-scan (kind :article) (token (car args)))
                 (:instance fn-nntp-msgid-retrieval-indexed-refines-scan
                            (index (fn-gidx-pin-trie index)) (kind :article) (token (car args)))))
           ("number" :test (and (consp args) (null (cdr args)) (fn-nntp-number-tokenp (car args)))
            :cat (fn-nntp-number-retrieval-cat session v :article (car args) fn-arena fn-cat)
            :view :pinned :effect :current
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-number-retrieval-cat-is-walk (kind :article) (token (car args)))
                 (:instance fn-scat-pinned-number-line-is-number-retrieval)))
           ("current" :test (null args)
            :cat (fn-nntp-current-retrieval-cat session :article v fn-arena fn-cat)
            :view :pinned :effect :current
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-current-retrieval-cat-is-current-retrieval (kind :article)))
            :open (fn-nntp-retrieval))
           ("syntax" :test t :cat (fn-nntp-archive-command session archive env keyword args fn-arena)
            :view :none :effect :none
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply))))
   :cost (:unrestricted "number and Message-ID catalog probes with the pinned withdrawal test and compatibility prelude; payload bytes only for the selected article"
          :restricted "pinned Message-ID trie lookup or the reference number/current archive walk")
   :teeth ("ARTICLE 2" "ARTICLE" "ARTICLE <b@x>" "ARTICLE 9" "ARTICLE <missing@x>" "ARTICLE 1 2"))
  ("HEAD"
   :view :pinned :view-decided (:pin-or-completed "PRF-1238") :effect :current :view-rfc "NNT-042 (pinned retrieval); the number, Message-ID and current forms; numeric success moves the current article; decided c07 C for the Message-ID form only: the pin first, then the completed snapshot; RFC 3977 6.2.2"
   :forms (("number-withdrawn" :test (and (consp args) (null (cdr args))
                                         (fn-nntp-number-withdrawn-p-cat session index (car args) v fn-arena fn-cat))
            :cat (fn-nntp-withdrawn-reply session nil)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))))
           ("msgid-withdrawn" :test (and (consp args) (null (cdr args))
                                        (fn-nntp-message-id-tokenp (car args))
                                        (fn-nntp-msgid-withdrawn-p-cat index (car args) v fn-arena fn-cat))
            :cat (fn-nntp-withdrawn-reply session t)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)))
           ("compatibility" :test (fn-rcompat-reply-cat session archive index env keyword args v fn-arena fn-cat)
            :view :pinned :effect :current
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)))
           ("msgid" :test (and (consp args) (null (cdr args)) (fn-nntp-message-id-tokenp (car args)))
            :cat (fn-nntp-msgid-retrieval-cat session v :head (car args) fn-arena fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-msgid-retrieval-cat-is-scan (kind :head) (token (car args)))
                 (:instance fn-nntp-msgid-retrieval-indexed-refines-scan
                            (index (fn-gidx-pin-trie index)) (kind :head) (token (car args)))))
           ("number" :test (and (consp args) (null (cdr args)) (fn-nntp-number-tokenp (car args)))
            :cat (fn-nntp-number-retrieval-cat session v :head (car args) fn-arena fn-cat)
            :view :pinned :effect :current
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-number-retrieval-cat-is-walk (kind :head) (token (car args)))
                 (:instance fn-scat-pinned-number-line-is-number-retrieval)))
           ("current" :test (null args)
            :cat (fn-nntp-current-retrieval-cat session :head v fn-arena fn-cat)
            :view :pinned :effect :current
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-current-retrieval-cat-is-current-retrieval (kind :head)))
            :open (fn-nntp-retrieval))
           ("syntax" :test t :cat (fn-nntp-archive-command session archive env keyword args fn-arena)
            :view :none :effect :none
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply))))
   :cost (:unrestricted "number and Message-ID catalog probes with the pinned withdrawal test and compatibility prelude; payload bytes only for the selected article"
          :restricted "pinned Message-ID trie lookup or the reference number/current archive walk")
   :teeth ("HEAD 2" "HEAD" "HEAD <b@x>" "HEAD 9" "HEAD <missing@x>" "HEAD 1 2"))
  ("BODY"
   :view :pinned :view-decided (:pin-or-completed "PRF-1238") :effect :current :view-rfc "NNT-042 (pinned retrieval); the number, Message-ID and current forms; numeric success moves the current article; decided c07 C for the Message-ID form only: the pin first, then the completed snapshot; RFC 3977 6.2.3"
   :forms (("number-withdrawn" :test (and (consp args) (null (cdr args))
                                         (fn-nntp-number-withdrawn-p-cat session index (car args) v fn-arena fn-cat))
            :cat (fn-nntp-withdrawn-reply session nil)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))))
           ("msgid-withdrawn" :test (and (consp args) (null (cdr args))
                                        (fn-nntp-message-id-tokenp (car args))
                                        (fn-nntp-msgid-withdrawn-p-cat index (car args) v fn-arena fn-cat))
            :cat (fn-nntp-withdrawn-reply session t)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)))
           ("compatibility" :test (fn-rcompat-reply-cat session archive index env keyword args v fn-arena fn-cat)
            :view :pinned :effect :current
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)))
           ("msgid" :test (and (consp args) (null (cdr args)) (fn-nntp-message-id-tokenp (car args)))
            :cat (fn-nntp-msgid-retrieval-cat session v :body (car args) fn-arena fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-msgid-retrieval-cat-is-scan (kind :body) (token (car args)))
                 (:instance fn-nntp-msgid-retrieval-indexed-refines-scan
                            (index (fn-gidx-pin-trie index)) (kind :body) (token (car args)))))
           ("number" :test (and (consp args) (null (cdr args)) (fn-nntp-number-tokenp (car args)))
            :cat (fn-nntp-number-retrieval-cat session v :body (car args) fn-arena fn-cat)
            :view :pinned :effect :current
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-number-retrieval-cat-is-walk (kind :body) (token (car args)))
                 (:instance fn-scat-pinned-number-line-is-number-retrieval)))
           ("current" :test (null args)
            :cat (fn-nntp-current-retrieval-cat session :body v fn-arena fn-cat)
            :view :pinned :effect :current
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-current-retrieval-cat-is-current-retrieval (kind :body)))
            :open (fn-nntp-retrieval))
           ("syntax" :test t :cat (fn-nntp-archive-command session archive env keyword args fn-arena)
            :view :none :effect :none
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply))))
   :cost (:unrestricted "number and Message-ID catalog probes with the pinned withdrawal test and compatibility prelude; payload bytes only for the selected article"
          :restricted "pinned Message-ID trie lookup or the reference number/current archive walk")
   :teeth ("BODY 2" "BODY" "BODY <b@x>" "BODY 9" "BODY <missing@x>" "BODY 1 2"))
  ("STAT"
   :view :pinned :view-decided (:pin-or-completed "PRF-1238") :effect :current :view-rfc "NNT-042 (pinned retrieval); the number, Message-ID and current forms; numeric success moves the current article; decided c07 C for the Message-ID form only: the pin first, then the completed snapshot; RFC 3977 6.2.4"
   :forms (("number-withdrawn" :test (and (consp args) (null (cdr args))
                                         (fn-nntp-number-withdrawn-p-cat session index (car args) v fn-arena fn-cat))
            :cat (fn-nntp-withdrawn-reply session nil)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))))
           ("msgid-withdrawn" :test (and (consp args) (null (cdr args))
                                        (fn-nntp-message-id-tokenp (car args))
                                        (fn-nntp-msgid-withdrawn-p-cat index (car args) v fn-arena fn-cat))
            :cat (fn-nntp-withdrawn-reply session t)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)))
           ("compatibility" :test (fn-rcompat-reply-cat session archive index env keyword args v fn-arena fn-cat)
            :view :pinned :effect :current
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)))
           ("msgid" :test (and (consp args) (null (cdr args)) (fn-nntp-message-id-tokenp (car args)))
            :cat (fn-nntp-msgid-retrieval-cat session v :stat (car args) fn-arena fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-msgid-retrieval-cat-is-scan (kind :stat) (token (car args)))
                 (:instance fn-nntp-msgid-retrieval-indexed-refines-scan
                            (index (fn-gidx-pin-trie index)) (kind :stat) (token (car args)))))
           ("number" :test (and (consp args) (null (cdr args)) (fn-nntp-number-tokenp (car args)))
            :cat (fn-nntp-number-retrieval-cat session v :stat (car args) fn-arena fn-cat)
            :view :pinned :effect :current
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-number-retrieval-cat-is-walk (kind :stat) (token (car args)))
                 (:instance fn-scat-pinned-number-line-is-number-retrieval)))
           ("current" :test (null args)
            :cat (fn-nntp-current-retrieval-cat session :stat v fn-arena fn-cat)
            :view :pinned :effect :current
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-current-retrieval-cat-is-current-retrieval (kind :stat)))
            :open (fn-nntp-retrieval))
           ("syntax" :test t :cat (fn-nntp-archive-command session archive env keyword args fn-arena)
            :view :none :effect :none
            :by ((:instance fn-nntp-number-withdrawn-p-cat-is-archive (token (car args)))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply))))
   :cost (:unrestricted "number and Message-ID catalog probes with the pinned withdrawal test and compatibility prelude; payload bytes only for the selected article"
          :restricted "pinned Message-ID trie lookup or the reference number/current archive walk")
   :teeth ("STAT 2" "STAT" "STAT <b@x>" "STAT 9" "STAT <missing@x>" "STAT 1 2"))
  ("OVER"
   :view :pinned :effect :none :view-rfc "NNT-042 (other reads); RFC 3977 8.3"
   :quantum (:cursor fn-ovw-cursor-effectp)
   :forms (("xref" :test (fn-nntp-xref-reply-cat session archive index env keyword args v fn-arena fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)))
           ("range" :test (and (fn-gidx-pinp index) (consp args) (null (cdr args))
                               (fn-nntp-range-okp (fn-nntp-parse-range (car args))))
            :cat (fn-nntp-over-range-ovw session v (car args) (fn-nntp-keywordp keyword "XOVER") nil fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-nntp-over-range-ovw-expands-to-over-range-cat
                            (token (car args)) (legacyp (fn-nntp-keywordp keyword "XOVER")))
                 (:instance fn-nntp-over-range-cat-is-archive
                            (token (car args)) (legacyp (fn-nntp-keywordp keyword "XOVER")))
                 (:instance fn-nntp-parse-range-ok-has-natural-bounds (token (car args)))
                 (:instance fn-nntp-over-range-indexed-equals-fold
                            (token (car args)) (legacyp (fn-nntp-keywordp keyword "XOVER")))
                 (:instance fn-nntp-over-range-indexed-preserves-session
                            (buckets (fn-gidx-pin-buckets index)) (trie (fn-gidx-pin-trie index))
                            (token (car args)) (legacyp (fn-nntp-keywordp keyword "XOVER")))
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built))
            :open (fn-nntp-over-response fn-nntp-xover-response fn-nntp-result-session
                   fn-nntp-result-effects))
           ("current" :test (null args)
            :cat (fn-nntp-archive-command session archive env keyword args fn-arena)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)))
           ("msgid" :test (and (consp args) (null (cdr args)) (fn-nntp-message-id-tokenp (car args)))
            :cat (fn-nntp-archive-command session archive env keyword args fn-arena)
            :view :pinned :effect :none :decided (:pin-or-completed "PRF-1238")
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)))
           ("other" :test t
            :cat (fn-nntp-archive-command session archive env keyword args fn-arena)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built))))
   :cost (:unrestricted "one cursor quantum of W numbers per scheduling step (books/served-plan-cursor.lisp), including the configured Xref server captured by the cursor; retained output bytes are not yet separately bounded"
          :restricted "the reference walk over the projected pinned archive (fn-nntp-over-range-indexed, no cursor)")
   :teeth ("OVER 1-3" "OVER 2" "OVER 2-" "OVER 9-10" "OVER" "OVER <a@x>" "OVER 1-3 x"))
  ("XOVER"
   :view :pinned :effect :none :view-rfc "NNT-042 (other reads); RFC 2980 2.8"
   :quantum (:cursor fn-ovw-cursor-effectp)
   :forms (("xref" :test (fn-nntp-xref-reply-cat session archive index env keyword args v fn-arena fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)))
           ("range" :test (and (fn-gidx-pinp index) (consp args) (null (cdr args))
                               (fn-nntp-range-okp (fn-nntp-parse-range (car args))))
            :cat (fn-nntp-over-range-ovw session v (car args) (fn-nntp-keywordp keyword "XOVER") nil fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-nntp-over-range-ovw-expands-to-over-range-cat
                            (token (car args)) (legacyp (fn-nntp-keywordp keyword "XOVER")))
                 (:instance fn-nntp-over-range-cat-is-archive
                            (token (car args)) (legacyp (fn-nntp-keywordp keyword "XOVER")))
                 (:instance fn-nntp-parse-range-ok-has-natural-bounds (token (car args)))
                 (:instance fn-nntp-over-range-indexed-equals-fold
                            (token (car args)) (legacyp (fn-nntp-keywordp keyword "XOVER")))
                 (:instance fn-nntp-over-range-indexed-preserves-session
                            (buckets (fn-gidx-pin-buckets index)) (trie (fn-gidx-pin-trie index))
                            (token (car args)) (legacyp (fn-nntp-keywordp keyword "XOVER")))
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built))
            :open (fn-nntp-over-response fn-nntp-xover-response fn-nntp-result-session
                   fn-nntp-result-effects))
           ("current" :test (null args)
            :cat (fn-nntp-archive-command session archive env keyword args fn-arena)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)))
           ("msgid" :test (and (consp args) (null (cdr args)) (fn-nntp-message-id-tokenp (car args)))
            :cat (fn-nntp-archive-command session archive env keyword args fn-arena)
            :view :pinned :effect :none :decided (:pin-or-completed "PRF-1238")
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)))
           ("other" :test t
            :cat (fn-nntp-archive-command session archive env keyword args fn-arena)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built))))
   :cost (:unrestricted "one cursor quantum of W numbers per scheduling step (books/served-plan-cursor.lisp), including the configured Xref server captured by the cursor; retained output bytes are not yet separately bounded"
          :restricted "the reference walk over the projected pinned archive (fn-nntp-over-range-indexed, no cursor)")
   :teeth ("XOVER 1-3" "XOVER 2" "XOVER 2-" "XOVER 9-10" "XOVER" "XOVER <a@x>" "XOVER 1-3 x"))
  ("HDR"
   :view :pinned :view-decided (:pin-or-completed "PRF-1238") :effect :none
   :view-rfc "NNT-042 (other reads); Message-ID completed fallback remains PRF-1238 debt; RFC 3977 8.5"
   :quantum (:cursor fn-ovw-cursor-effectp)
   :forms (("compatibility" :test (fn-rcompat-reply-cat session archive index env keyword args v fn-arena fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)))
           ("verified" :test (and (consp args) (fn-nntp-keywordp (car args) ":FN-VERIFIED"))
            :cat (fn-nntp-verdict-hdr-response-cat session verdicts args v fn-arena fn-cat) :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-verdict-hdr-response-cat-is-archive)))
           ("control" :test (and (consp args) (fn-nntp-keywordp (car args) ":FN-CONTROL"))
            :cat (fn-nntp-control-hdr-response-cat session archive index verdicts args v fn-arena fn-cat) :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-verdict-hdr-response-cat-is-archive)
                 (:instance fn-nntp-control-hdr-response-cat-is-pinned)))
           ("enrollment" :test (and (consp args) (fn-nntp-keywordp (car args) ":FN-ENROLLMENT"))
            :cat (fn-nntp-enrollment-hdr-response-cat session index verdicts args v fn-arena fn-cat) :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-verdict-hdr-response-cat-is-archive)
                 (:instance fn-nntp-control-hdr-response-cat-is-pinned)
                 (:instance fn-nntp-enrollment-hdr-response-cat-is-pinned)))
           ("ordinary" :test t
            :cat (fn-nntp-hdr-command-cat session args v nil fn-arena fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-verdict-hdr-response-cat-is-archive)
                 (:instance fn-nntp-control-hdr-response-cat-is-pinned)
                 (:instance fn-nntp-enrollment-hdr-response-cat-is-pinned)
                 (:instance fn-nntp-hdr-command-cat-is-archive (legacyp nil)))
            :open (fn-nntp-hdr-response)))
   :cost (:unrestricted "a range is the header cursor (lane cold-line): one quantum of W numbers per scheduling step, at most fn-clq-payload-quantum when the field is read from payloads (books/over-window.lisp fn-ovw-step-payloads-fit); the current and Message-ID forms read one article"
          :restricted "reference pinned archive walk; whole response allocated")
   :teeth ("HDR Subject 1-3" "HDR Subject" "HDR Subject <b@x>" "HDR Xref 1-3"
           "HDR :FN-VERIFIED 1-3" "HDR :FN-CONTROL <b@x>" "HDR :FN-ENROLLMENT <b@x>" "HDR"))
  ("XHDR"
   :view :pinned :effect :none :view-rfc "NNT-042 (other reads); RFC 2980 2.6"
   :quantum (:cursor fn-ovw-cursor-effectp)
   :forms (("compatibility" :test (fn-rcompat-reply-cat session archive index env keyword args v fn-arena fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)))
           ("ordinary" :test t
            :cat (fn-nntp-hdr-command-cat session args v t fn-arena fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-hdr-command-cat-is-archive (legacyp t)))
            :open (fn-nntp-xhdr-response)))
   :cost (:unrestricted "a range is the header cursor (lane cold-line): one quantum of W numbers per scheduling step, at most fn-clq-payload-quantum when the field is read from payloads (books/over-window.lisp fn-ovw-step-payloads-fit); the current and Message-ID forms read one article"
          :restricted "reference pinned archive walk; whole response allocated")
   :teeth ("XHDR Subject 1-3" "XHDR Subject" "XHDR Subject <b@x>" "XHDR Xref 1-3" "XHDR"))
  ("XPAT"
   :view :pinned :effect :none :view-rfc "NNT-042 (other reads); RFC 2980 2.9"
   :quantum (:cursor fn-ovw-cursor-effectp)
   :forms (("any" :test t :cat (fn-nntp-xpat-response-cat session args v fn-arena fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xpat-response-cat-is-archive))))
   :cost (:unrestricted "a range is the header cursor (lane cold-line): one quantum of W numbers per scheduling step, at most fn-clq-payload-quantum when the field is read from payloads (books/over-window.lisp fn-ovw-step-payloads-fit)"
          :restricted "the reference walk over the projected pinned archive (fn-nntp-xpat-response)")
   :teeth ("XPAT Subject 1-3 *" "XPAT Subject 2 *b*" "XPAT Subject <b@x> *" "XPAT Subject 1-3" "XPAT"))
  ("LIST"
   :view :pinned :view-decided (:completed "PRF-1237") :effect :none
   :view-rfc "NNT-042 today (ACTIVE and COUNTS: the pinned groups and summaries; NEWSGROUPS, SUBSCRIPTIONS, MOTD and ACTIVE.TIMES: the pinned groups and the pinned configuration); decided 2026-10-02 (build/coordinator/decisions/list-view-2026-10-02.md): LIST, ACTIVE and COUNTS answer the latest completed durable view, the pin unmoved; NEWSGROUPS and ACTIVE.TIMES under consultation c07; RFC 3977 7.6.1, 7.6.3; RFC 6048 2.2.2"
   :forms (("xref" :test (fn-nntp-xref-reply-cat session archive index env keyword args v fn-arena fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)))
           ("counts" :test (and (fn-gidx-pinp index) (consp args)
                                (fn-nntp-keyword-tokenp (car args))
                                (fn-nntp-keywordp (car args) "COUNTS"))
            :cat (fn-nntp-list-counts-command-cat session archive (fn-nntp-env-closed env)
                                                 (cdr args) v fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)
                 (:instance fn-nntp-list-counts-command-cat-is-archive
                            (closed (fn-nntp-env-closed env)) (args (cdr args)))
                 (:instance fn-scat-gidx-list-counts-is-fold
                            (buckets (fn-gidx-pin-buckets index))
                            (closed (fn-nntp-env-closed env)) (args (cdr args)))))
           ("compatibility" :test (fn-rcompat-reply-cat session archive index env keyword args v fn-arena fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)))
           ("active" :test (fn-scat-list-active-formp args)
            :cat (fn-nntp-list-active-cat session archive (fn-nntp-env-closed env) args v fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply)
                 (:instance fn-nntp-list-active-cat-is-list-command)))
           ("other" :test t
            :cat (fn-nntp-archive-command session archive env keyword args fn-arena)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-xref-reply-col-is-xref-reply)
                 (:instance fn-proto-statep-article-listp)
                 (:instance fn-proto-pin-trie-is-built)
                 (:instance fn-proto-pin-buckets-are-built)
                 (:instance fn-rcompat-reply-cat-is-rcompat-reply))))
   :cost (:unrestricted "ACTIVE and COUNTS use carried group summaries with configured-group walks; compatibility and other variants walk pinned listing/creation facts; whole reply allocated"
          :restricted "pinned group bucket COUNTS or the reference archive/listing walks; whole reply allocated")
   :teeth ("LIST" "LIST ACTIVE" "LIST ACTIVE fn.*" "LIST COUNTS" "LIST COUNTS fn.test"
           "LIST OVERVIEW.FMT" "LIST ACTIVE.TIMES" "LIST SUBSCRIPTIONS" "LIST NEWSGROUPS"
           "LIST MOTD" "LIST UNKNOWN" "LIST ACTIVE a b"))
  ("NEWGROUPS"
   :view :pinned :view-decided (:completed "PRF-1237") :effect :none :view-rfc "NNT-042 by silence today (the pinned creation facts filtered to the pinned groups); decided c07 B: the completed discovery snapshot; RFC 3977 7.3"
   :forms (("compatibility" :test (fn-rcompat-reply-cat session archive index env keyword args v fn-arena fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-rcompat-reply-cat-is-rcompat-reply)))
           ("other" :test t
            :cat (fn-nntp-archive-command session archive env keyword args fn-arena)
            :view :pinned :effect :none
            :by ((:instance fn-rcompat-reply-cat-is-rcompat-reply))))
   :cost (:unrestricted "creation-fact and configured-group walks over the pinned environment and archive; whole reply allocated"
          :restricted "the same pinned creation-fact and configured-group walks; whole reply allocated")
   :teeth ("NEWGROUPS 20261001 000000 GMT" "NEWGROUPS 20261001 000000"
           "NEWGROUPS 261001 000000 GMT" "NEWGROUPS" "NEWGROUPS 20261001 000000 BAD"))
  ("NEWNEWS"
   :view :pinned :view-decided (:completed "PRF-1237") :effect :none :view-rfc "NNT-042 by silence today (the pinned article root retained across one-candidate quanta); decided c07 C: one completed discovery snapshot captured at the first quantum and held across quanta; RFC 3977 7.4"
   :quantum (:cursor fn-nnw-meta-effectp)
   :forms (("any" :test t
            :cat (fn-nntp-newnews-response-stream session archive env args fn-arena fn-cat)
            :view :pinned :effect :none
            :by ((:instance fn-nntp-newnews-response-stream-expands-to-cat)
                 (:instance fn-nntp-newnews-response-stream-keeps-session)
                 (:instance fn-nntp-newnews-response-cat-is-newnews-response))))
   :cost (:unrestricted "one retained group/member entry or wildcard matcher microstep or indexed output phase per quantum and at most W emitted bytes; fixed reference-only initialization; matcher/comparison and composed heap tariff, physical resource custody, legacy cold metadata fallback and completed-view capture remain GEN-CURSOR debt"
          :restricted "the reference whole pinned archive walk, including payload tombstone reads")
   :teeth ("NEWNEWS * 20261001 000000 GMT" "NEWNEWS fn.* 20261001 000000 GMT" "NEWNEWS fn.* 20261001 000000" "NEWNEWS"))
  ("DATE"
   :view :none :effect :none :view-rfc "RFC 3977 7.1; no article view. DEFECT (c07): answers the clock observation pinned at accept (fn-nntp-env-observation; books/served.lisp fn-served-conn-observation), not the current reading; fixed separately")
  ("POST"
   :view :none :effect :offer :view-rfc "RFC 3977 6.3.1 (no archive)")
  ("IHAVE"
   :view :live-index :effect :none :view-rfc "a reader connection: 502; a peer connection decides the offer on the LIVE Message-ID index (books/served-catalog-chain.lisp fn-scr-history-hasp); RFC 3977 6.3.2")
  ("CHECK"
   :view :live-index :effect :none :view-rfc "as IHAVE; RFC 4644 2.3")
  ("TAKETHIS"
   :view :live-index :effect :none :view-rfc "RFC 4644 2.4; PHASED: the offer begins the article (books/served-catalog-chain.lisp fn-scr-peer-command :takethis), the duplicate and admission decisions belong to the received body's later phases")
  ("AUTHINFO"
   :view :none :effect :none :view-rfc "RFC 4643 (no archive)")
  ("STARTTLS"
   :view :none :effect :none :view-rfc "RFC 4642 (no archive)")
  ("COMPRESS"
   :view :none :effect :none :view-rfc "RFC 8054 (no archive)")
  ("XREDEEM"
   :view :none :effect :none :view-rfc "PRF-164 (no archive)")
  ("XFNCATCHUP"
   :view :pinned :effect :none :view-rfc "NNT-053: the pinned view and the log position the peer names")
  ("XFN-ZARTICLE"
   :view :pinned :effect :none :view-rfc "NNT-055: the pinned Message-ID index"))
