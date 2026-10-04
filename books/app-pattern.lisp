; fn: the zmq-pattern surface as declarations (D49, D50;
; planning/design/zmq-surface-2026-10-04.md section 4).
;
; A pattern is ONE `def-pattern' form: its article kind, its roles (each a
; verb over one group variable) and the guarantee words it carries.  Nothing
; else is written per pattern.  From the declarations this book computes
;
;   * each role's PLAN: a list of steps over the closed step vocabulary
;     below, every step an existing control request or an offline ACL2
;     function (fn-pat-role-plan; a role that posts encodes, signs and
;     authors; a role that reads registers once and then waits, projects,
;     decodes, delivers and acknowledges);
;   * each role's ARGUMENTS, from the steps' needs in one canonical order
;     (fn-pat-plan-args), so the command line and its usage text are the
;     plan's (fn-pat-usage-text);
;   * the argv grammar of the one host verb `fn pattern NAME ROLE ARGS...'
;     (fn-pat-cli-plan), which answers the plan and its bindings or a named
;     refusal.
;
; The host verb (host/native/pattern.lisp) is a fixed loop over the step
; vocabulary; adding a pattern adds a declaration and no host code.
;
; Three acknowledgements stay three (design section 1): the transport ACK
; (a control reply frame arrived), the RETENTION RECEIPT (hybrid-author
; answered accepted or already stored: exit 0) and the APPLICATION OUTCOME
; (the reader's own `ack' of its cursor, after its delivery).  A posting
; role reports the retention receipt; a reading role delivers, then acks.
;
; Keystones here (codec-free):
;   fn-pat-cli-run-binds-every-step  an accepted command line binds every
;       argument every step of its plan needs, to a nonempty word;
;   fn-pat-values-check-is-the-kind   the posting role's value check refuses
;       exactly the values outside article kind `opaque' v1, so what a role
;       posts is a value of the kind and PRF-1320..1322 apply to it.
; The delivery keystone (the payload a reader delivers is the payload the
; writer encoded) needs the codec and is in books/app-pattern-delivery.lisp.

(in-package "ACL2")
(include-book "article-kind")
(local (include-book "arithmetic-5/top" :dir :system))

; -----------------------------------------------------------------------------
; 1. The vocabularies.  Closed: a declaration outside them is refused when it
; is admitted.

(defconst *fn-pat-kinds* '(:opaque-1))

; :posts G  -- the role sends one message of the kind to group G.
; :reads G  -- the role is a consumer of group G and delivers its messages.
(defconst *fn-pat-verbs* '(:posts :reads))

; The guarantee words (design section 3).  A word is a property the pattern
; RELIES ON, carried to the usage text and the export row; each word's
; owner is named in *fn-pat-guarantee-owners*.
(defconst *fn-pat-guarantees*
  '(:retention-receipt :at-least-once :history-order :reclaim-gap
    :withdrawal-event :no-drop))

(defconst *fn-pat-guarantee-owners*
  '((:retention-receipt . "hybrid-author exit 0 = stored byte for byte (D25, D01)")
    (:at-least-once . "a reader acks only after delivery; ack is monotone (specs/consumer-progress.md)")
    (:history-order . "the consumer cursor reads one group in Store commit order")
    (:reclaim-gap . "reclaimed content is an explicit unavailable gap (specs/consumer-progress.md)")
    (:withdrawal-event . "a withdrawn message arrives as a withdrawal report (PKT-710)")
    (:no-drop . "registration starts at position 0 and no reader is dropped")))

; The step vocabulary.  A step is (OP) or (OP KIND).
(defconst *fn-pat-step-ops*
  '(:encode :sign :author :register :wait :project :decode :deliver :ack))

; What each step needs from the command line.  :group is the role's group
; variable (its word is the group variable's name, e.g. TOPIC).
(defconst *fn-pat-step-needs*
  '((:encode :group :from :msgid :payload)
    (:sign :keys :spool)
    (:author :control :generation)
    (:register :control :consumer :group)
    (:wait :control :consumer :out)
    (:project)
    (:decode)
    (:deliver :out)
    (:ack :control)))

; The one order the arguments of every role appear in.
(defconst *fn-pat-arg-order*
  '(:control :generation :consumer :keys :group :from :msgid :payload :spool :out))

; -----------------------------------------------------------------------------
; 2. Words: octets of lowercase names, decimals.

(defun fn-pat-octets-of-chars (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (consp cs)
      (cons (char-code (car cs)) (fn-pat-octets-of-chars (cdr cs)))
    nil))

(defun fn-pat-word (sym)
  (declare (xargs :guard (symbolp sym)))
  (let ((cs (coerce (symbol-name sym) 'list)))
    (if (standard-char-listp cs)
        (fn-pat-octets-of-chars (string-downcase1 cs))
      (fn-pat-octets-of-chars cs))))

(defun fn-pat-upword (sym)
  (declare (xargs :guard (symbolp sym)))
  (fn-pat-octets-of-chars (coerce (symbol-name sym) 'list)))

; Least significant digit first (as books/byte-store-txn-name.lisp).
(defun fn-pat-digits-rev (n)
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (if (< n 10)
        (list (+ 48 n))
      (cons (+ 48 (mod n 10)) (fn-pat-digits-rev (floor n 10))))))

(defun fn-pat-decimal (n)
  (declare (xargs :guard t))
  (rev (fn-pat-digits-rev n)))

; N in at least WIDTH digits, zero-padded.
(defun fn-pat-zeros (k)
  (declare (xargs :guard (natp k)))
  (if (zp k) nil (cons 48 (fn-pat-zeros (1- k)))))

(defun fn-pat-padded (n width)
  (declare (xargs :guard (natp width)))
  (let ((d (fn-pat-decimal n)))
    (append (fn-pat-zeros (nfix (- width (len d)))) d)))

(defun fn-pat-digit-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (integerp (car xs)) (<= 48 (car xs)) (<= (car xs) 57)
           (fn-pat-digit-listp (cdr xs)))
    (null xs)))

(defun fn-pat-digits-value (xs acc)
  (declare (xargs :guard (and (fn-pat-digit-listp xs) (natp acc))))
  (if (consp xs)
      (fn-pat-digits-value (cdr xs) (+ (* 10 acc) (- (car xs) 48)))
    acc))

; A decimal word of 1..10 digits, its value; nil otherwise.
(defun fn-pat-parse-nat (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (<= (len xs) 10) (fn-pat-digit-listp xs))
      (fn-pat-digits-value xs 0)
    nil))

; -----------------------------------------------------------------------------
; 3. The RFC 5322 Date a posting role writes (row 2 of the kind; fn keeps
; it and never checks it), from Unix seconds: "Sun, 04 Oct 2026 12:00:00
; +0000".  The civil date is H. Hinnant's days-to-civil.

(defconst *fn-pat-day-names*
  '((83 117 110) (77 111 110) (84 117 101) (87 101 100) (84 104 117)
    (70 114 105) (83 97 116)))
(defconst *fn-pat-month-names*
  '((74 97 110) (70 101 98) (77 97 114) (65 112 114) (77 97 121) (74 117 110)
    (74 117 108) (65 117 103) (83 101 112) (79 99 116) (78 111 118) (68 101 99)))

; (YEAR MONTH DAY) of a day count since 1970-01-01.
(defun fn-pat-civil (days)
  (declare (xargs :guard (natp days)))
  (let* ((z (+ days 719468))
         (era (floor z 146097))
         (doe (- z (* era 146097)))
         (yoe (floor (+ doe (- (floor doe 1460)) (floor doe 36524)
                        (- (floor doe 146096)))
                     365))
         (doy (- doe (+ (* 365 yoe) (floor yoe 4) (- (floor yoe 100)))))
         (mp (floor (+ (* 5 doy) 2) 153))
         (d (+ 1 (- doy (floor (+ (* 153 mp) 2) 5))))
         (m (if (< mp 10) (+ mp 3) (- mp 9)))
         (y (+ yoe (* era 400) (if (<= m 2) 1 0))))
    (mv (nfix y) (nfix m) (nfix d))))

(defthm fn-pat-civil-natural-0
  (natp (mv-nth 0 (fn-pat-civil d)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (union-theories '(fn-pat-civil mv-nth nfix natp)
                                             (theory 'minimal-theory)))))
(defthm fn-pat-civil-natural-1
  (natp (mv-nth 1 (fn-pat-civil d)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (union-theories '(fn-pat-civil mv-nth nfix natp)
                                             (theory 'minimal-theory)))))
(defthm fn-pat-civil-natural-2
  (natp (mv-nth 2 (fn-pat-civil d)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (union-theories '(fn-pat-civil mv-nth nfix natp)
                                             (theory 'minimal-theory)))))

(defun fn-pat-name-at (i names)
  (declare (xargs :guard t))
  (true-list-fix (nth (nfix i) (true-list-fix names))))

(defun fn-pat-date-text (seconds)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-pat-civil
                                                            fn-pat-name-at
                                                            fn-pat-padded)))))
  (let* ((s (nfix seconds))
         (days (floor s 86400))
         (sod (mod s 86400)))
    (mv-let (year month day)
      (fn-pat-civil days)
      (append (fn-pat-name-at (mod (+ days 4) 7) *fn-pat-day-names*) '(44 32)
              (fn-pat-padded day 2) '(32)
              (fn-pat-name-at (+ -1 month) *fn-pat-month-names*) '(32)
              (fn-pat-padded year 4) '(32)
              (fn-pat-padded (floor sod 3600) 2) '(58)
              (fn-pat-padded (floor (mod sod 3600) 60) 2) '(58)
              (fn-pat-padded (mod sod 60) 2)
              '(32 43 48 48 48 48)))))

; -----------------------------------------------------------------------------
; 4. Plans.  A plan is (ONCE LOOP): the steps run once, then the steps run
; per message until the loop ends (a reading role only).

(defun fn-pat-role-plan (verb kind)
  (declare (xargs :guard t))
  (case verb
    (:posts (list (list (list :encode kind) (list :sign) (list :author)) nil))
    (:reads (list (list (list :register))
                  (list (list :wait) (list :project) (list :decode kind)
                        (list :deliver) (list :ack))))
    (otherwise (list nil nil))))

(defun fn-pat-steps-needs (steps)
  (declare (xargs :guard t))
  (if (consp steps)
      (append (cdr (assoc-eq (and (consp (car steps)) (caar steps))
                             *fn-pat-step-needs*))
              (fn-pat-steps-needs (cdr steps)))
    nil))

(defun fn-pat-plan-needs (plan)
  (declare (xargs :guard t))
  (append (fn-pat-steps-needs (and (consp plan) (car plan)))
          (fn-pat-steps-needs (and (consp plan) (consp (cdr plan)) (cadr plan)))))

(defun fn-pat-order-filter (order needs)
  (declare (xargs :guard (true-listp needs)))
  (if (consp order)
      (if (member-equal (car order) needs)
          (cons (car order) (fn-pat-order-filter (cdr order) needs))
        (fn-pat-order-filter (cdr order) needs))
    nil))

(defun fn-pat-plan-args (plan)
  (declare (xargs :guard t))
  (fn-pat-order-filter *fn-pat-arg-order* (true-list-fix (fn-pat-plan-needs plan))))

(defun fn-pat-plan-loopsp (plan)
  (declare (xargs :guard t))
  (and (consp plan) (consp (cdr plan)) (consp (cadr plan))))

; -----------------------------------------------------------------------------
; 5. Declarations.  A role is (ROLE VERB GROUP), three symbols.

(defun fn-pat-rolep (role)
  (declare (xargs :guard t))
  (and (true-listp role) (equal (len role) 3)
       (symbolp (car role)) (car role)
       (member-eq (cadr role) *fn-pat-verbs*)
       (symbolp (caddr role)) (caddr role)
       (not (member-eq (car role) '(help :help)))))

(defun fn-pat-role-listp (roles)
  (declare (xargs :guard t))
  (if (consp roles)
      (and (fn-pat-rolep (car roles)) (fn-pat-role-listp (cdr roles)))
    (null roles)))

(defun fn-pat-role-names (roles)
  (declare (xargs :guard (fn-pat-role-listp roles)))
  (if (consp roles) (cons (caar roles) (fn-pat-role-names (cdr roles))) nil))

; Some role of ROLES has VERB over GROUP.
(defun fn-pat-has-rolep (verb group roles)
  (declare (xargs :guard (fn-pat-role-listp roles)))
  (if (consp roles)
      (or (and (eq (cadr (car roles)) verb) (eq (caddr (car roles)) group))
          (fn-pat-has-rolep verb group (cdr roles)))
    nil))

; Every group a role posts to is read by some role, and every group a role
; reads is posted to by some role: a pattern carries messages somewhere.
(defun fn-pat-roles-pairedp (roles all)
  (declare (xargs :guard (and (fn-pat-role-listp roles) (fn-pat-role-listp all))))
  (if (consp roles)
      (and (fn-pat-has-rolep (if (eq (cadr (car roles)) :posts) :reads :posts)
                             (caddr (car roles)) all)
           (fn-pat-roles-pairedp (cdr roles) all))
    t))

(defun fn-pat-declp (name kind roles guarantee)
  (declare (xargs :guard t))
  (and (symbolp name) name
       (not (member-eq name '(help :help)))
       (member-eq kind *fn-pat-kinds*)
       (consp roles)
       (fn-pat-role-listp roles)
       (no-duplicatesp-eq (fn-pat-role-names roles))
       (fn-pat-roles-pairedp roles roles)
       (symbol-listp guarantee)
       (subsetp-eq guarantee *fn-pat-guarantees*)
       (no-duplicatesp-eq guarantee)))

; The normal form a pattern row holds: (NAME-WORD NAME KIND ROLE-ROWS
; GUARANTEE), each role row (ROLE-WORD ROLE VERB GROUP GROUP-UPWORD PLAN).
(defun fn-pat-role-rows (roles kind)
  (declare (xargs :guard (fn-pat-role-listp roles)))
  (if (consp roles)
      (let ((role (car roles)))
        (cons (list (fn-pat-word (car role)) (car role) (cadr role) (caddr role)
                    (fn-pat-upword (caddr role))
                    (fn-pat-role-plan (cadr role) kind))
              (fn-pat-role-rows (cdr roles) kind)))
    nil))

(defun fn-pat-row (name decl)
  (declare (xargs :guard t :verify-guards nil))
  (let ((kind (nth 0 decl)) (roles (nth 1 decl)) (guarantee (nth 2 decl)))
    (list (fn-pat-word name) name kind (fn-pat-role-rows roles kind) guarantee)))

(defun fn-pat-rows (alist)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp alist) (consp (car alist)))
      (cons (fn-pat-row (caar alist) (cdar alist)) (fn-pat-rows (cdr alist)))
    nil))

; (def-pattern NAME :kind KIND :roles ((ROLE VERB GROUP) ...) :guarantee (W ...))
; admits one row of the table fn-pat-table, or is refused by name.
(defmacro def-pattern (name &key kind roles guarantee)
  `(make-event
    (cond ((not (fn-pat-declp ',name ',kind ',roles ',guarantee))
           (er soft 'def-pattern
               "~x0 is not a pattern declaration: a kind of ~x1, roles (ROLE ~
                VERB GROUP) with verbs of ~x2, unique role names, every ~
                group both posted to and read, guarantee words of ~x3."
               ',name *fn-pat-kinds* *fn-pat-verbs* *fn-pat-guarantees*))
          ((assoc-eq ',name (table-alist 'fn-pat-table (w state)))
           (er soft 'def-pattern "pattern ~x0 is already declared." ',name))
          (t (value '(table fn-pat-table ',name '(,kind ,roles ,guarantee)))))))

; After the last def-pattern: the constant the host reads.
(defmacro fn-pat-finalize ()
  '(make-event
    `(defconst *fn-pat-patterns*
       ',(fn-pat-rows (reverse (table-alist 'fn-pat-table (w state)))))))

; -----------------------------------------------------------------------------
; 6. The declarations.

(def-pattern pubsub
  :kind :opaque-1
  :roles ((pub :posts topic)
          (sub :reads topic))
  :guarantee (:retention-receipt :at-least-once :history-order :reclaim-gap
              :withdrawal-event :no-drop))

(fn-pat-finalize)

; -----------------------------------------------------------------------------
; 7. Lookup, usage and the argv grammar.

(defun fn-pat-find (word rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (consp (car rows)) (equal (caar rows) word))
          (car rows)
        (fn-pat-find word (cdr rows)))
    nil))

(defun fn-pat-at (n x)
  (declare (xargs :guard (natp n)))
  (cond ((atom x) nil)
        ((zp n) (car x))
        (t (fn-pat-at (1- n) (cdr x)))))

(defun fn-pat-row-roles (row) (declare (xargs :guard t)) (fn-pat-at 3 row))
(defun fn-pat-role-plan-of (role-row) (declare (xargs :guard t)) (fn-pat-at 5 role-row))
(defun fn-pat-role-group-upword (role-row) (declare (xargs :guard t)) (fn-pat-at 4 role-row))

(defun fn-pat-arg-word (arg group-upword)
  (declare (xargs :guard t))
  (if (eq arg :group)
      (true-list-fix group-upword)
    (if (symbolp arg) (fn-pat-upword arg) nil)))

(defun fn-pat-arg-words (args group-upword)
  (declare (xargs :guard t))
  (if (consp args)
      (append '(32) (fn-pat-arg-word (car args) group-upword)
              (fn-pat-arg-words (cdr args) group-upword))
    nil))

; "fn pattern NAME ROLE ARG ... [--timeout S] [--count N]" for one role.
(defun fn-pat-role-usage (name-word role-row)
  (declare (xargs :guard t))
  (let ((plan (fn-pat-role-plan-of role-row)))
    (append (fn-pat-octets-of-chars (coerce "  fn pattern " 'list))
            (true-list-fix name-word) '(32)
            (true-list-fix (and (consp role-row) (car role-row)))
            (fn-pat-arg-words (fn-pat-plan-args plan)
                              (fn-pat-role-group-upword role-row))
            (if (fn-pat-plan-loopsp plan)
                (fn-pat-octets-of-chars (coerce " [--timeout S] [--count N]" 'list))
              nil)
            '(10))))

(defun fn-pat-roles-usage (name-word role-rows)
  (declare (xargs :guard t))
  (if (consp role-rows)
      (append (fn-pat-role-usage name-word (car role-rows))
              (fn-pat-roles-usage name-word (cdr role-rows)))
    nil))

(defun fn-pat-rows-usage (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (append (fn-pat-roles-usage (and (consp (car rows)) (caar rows))
                                  (fn-pat-row-roles (car rows)))
              (fn-pat-rows-usage (cdr rows)))
    nil))

(defun fn-pat-usage-text ()
  (declare (xargs :guard t))
  (append (fn-pat-octets-of-chars
           (coerce "usage: fn pattern NAME ROLE ARG...  (docs/agents.md, Patterns)
" 'list))
          (fn-pat-rows-usage *fn-pat-patterns*)))

; Bind ARGS to the words of ARGV in order: ((ARG . WORD) ...).
(defun fn-pat-bind (args argv)
  (declare (xargs :guard t))
  (if (and (consp args) (consp argv))
      (cons (cons (car args) (car argv)) (fn-pat-bind (cdr args) (cdr argv)))
    nil))

(defconst *fn-pat-timeout-word* '(45 45 116 105 109 101 111 117 116)) ; --timeout
(defconst *fn-pat-count-word* '(45 45 99 111 117 110 116))            ; --count
(defconst *fn-pat-default-timeout* 30)
(defconst *fn-pat-max-timeout* 3600)

; The options after the positional words of a looping role: (:ok TIMEOUT
; COUNT) or (:usage :option).  COUNT 0 is "until a wait finds nothing".
(defun fn-pat-options (words timeout count)
  (declare (xargs :guard t :measure (len words)))
  (cond ((atom words) (list :ok timeout count))
        ((and (equal (car words) *fn-pat-timeout-word*) (consp (cdr words))
              (posp (fn-pat-parse-nat (cadr words)))
              (<= (fn-pat-parse-nat (cadr words)) *fn-pat-max-timeout*))
         (fn-pat-options (cddr words) (fn-pat-parse-nat (cadr words)) count))
        ((and (equal (car words) *fn-pat-count-word*) (consp (cdr words))
              (natp (fn-pat-parse-nat (cadr words))))
         (fn-pat-options (cddr words) timeout (fn-pat-parse-nat (cadr words))))
        (t (list :usage :option))))

; A word the host may hand to a step: nonempty octets without NUL.
(defun fn-pat-wordp (xs)
  (declare (xargs :guard t))
  (and (consp xs) (fn-cbor-octet-listp xs) (not (member 0 xs))))

(defun fn-pat-words-p (xs)
  (declare (xargs :guard t))
  (if (consp xs) (and (fn-pat-wordp (car xs)) (fn-pat-words-p (cdr xs))) (null xs)))

; The plan of `fn pattern NAME ROLE ARGV...':
;   (:help TEXT)
;   (:usage REASON)  REASON :pattern, :role, :argc, :word or :option
;   (:run NAME ROLE KIND PLAN BINDINGS TIMEOUT COUNT)
(defun fn-pat-cli-plan (name role argv)
  (declare (xargs :guard t))
  (let ((row (fn-pat-find name *fn-pat-patterns*))
        (argv (true-list-fix argv)))
    (cond ((equal name '(104 101 108 112)) (list :help (fn-pat-usage-text)))
          ((not (consp row)) (list :usage :pattern))
          (t (let ((role-row (fn-pat-find role (fn-pat-row-roles row))))
               (if (not (consp role-row))
                   (list :usage :role)
                 (let* ((plan (fn-pat-role-plan-of role-row))
                        (args (fn-pat-plan-args plan))
                        (n (len args)))
                   (cond ((< (len argv) n) (list :usage :argc))
                         ((and (< n (len argv)) (not (fn-pat-plan-loopsp plan)))
                          (list :usage :argc))
                         ((not (fn-pat-words-p (take n argv)))
                          (list :usage :word))
                         (t (let ((opts (fn-pat-options (nthcdr n argv)
                                                        *fn-pat-default-timeout* 0)))
                              (if (not (equal (car opts) :ok))
                                  opts
                                (list :run (fn-pat-at 1 row) (fn-pat-at 1 role-row) (fn-pat-at 2 row)
                                      plan (fn-pat-bind args argv)
                                      (fn-pat-at 1 opts) (fn-pat-at 2 opts)))))))))))))

; -----------------------------------------------------------------------------
; 8. The posting role's values: the kind's eight, from the command line's
; From, group and Message-ID, the Date of the host's clock, the Subject
; "pattern NAME" and the media type application/octet-stream.

(defconst *fn-pat-media-type*
  '(97 112 112 108 105 99 97 116 105 111 110 47 111 99 116 101 116 45 115 116
    114 101 97 109))                                    ; application/octet-stream

(defun fn-pat-subject (name-word)
  (declare (xargs :guard t))
  (append '(112 97 116 116 101 114 110 32) (true-list-fix name-word)))  ; "pattern "

(defun fn-pat-values (name-word from seconds group msgid)
  (declare (xargs :guard t))
  (fn-ak-values from (fn-pat-date-text seconds) group (fn-pat-subject name-word)
                msgid *fn-pat-media-type*))

; The first row whose value is outside the kind, by its field kind word
; (fn-ak-rows-check: :from, :groups, :msgid, ...), or nil.  The host refuses
; by name.
(defun fn-pat-values-check (name-word from seconds group msgid)
  (declare (xargs :guard t))
  (fn-ak-rows-check *fn-ak-v1-rows* (fn-pat-values name-word from seconds group msgid)))

; -----------------------------------------------------------------------------
; 9. Keystones.

; The word bound to ARG (the host reads its arguments with this).
(defun fn-pat-lookup (arg bindings)
  (declare (xargs :guard t))
  (cond ((atom bindings) nil)
        ((and (consp (car bindings)) (equal (caar bindings) arg)) (cdar bindings))
        (t (fn-pat-lookup arg (cdr bindings)))))

; Every binding an accepted command line makes covers the plan's needs.
(defun fn-pat-bindings-coverp (needs bindings)
  (declare (xargs :guard t))
  (if (consp needs)
      (and (fn-pat-wordp (fn-pat-lookup (car needs) bindings))
           (fn-pat-bindings-coverp (cdr needs) bindings))
    t))

; KEYSTONE: the posting role's check refuses exactly the values outside
; kind `opaque' v1.  So a role that posts only after the check answered nil
; posts a value of the kind, and the acceptance keystones fn-ak-layout-parses
; (PRF-1320), fn-ak-layout-is-injected (PRF-1321) and
; fn-ak-layout-is-a-hybrid-injection (PRF-1322) apply to it.
(defthm fn-pat-values-check-is-the-kind
  (iff (fn-pat-values-check name-word from seconds group msgid)
       (not (fn-ak-rows-valuesp *fn-ak-v1-rows*
                                (fn-pat-values name-word from seconds group msgid))))
  :hints (("Goal" :in-theory (disable fn-pat-values fn-ak-rows-valuesp
                                      (:e fn-ak-rows-valuesp)))))

(local
 (defthm fn-pat-lookup-bind-word
   (implies (and (member-equal a args) (<= (len args) (len argv))
                 (fn-pat-words-p (take (len args) argv)))
            (fn-pat-wordp (fn-pat-lookup a (fn-pat-bind args argv))))
   :hints (("Goal" :induct (fn-pat-bind args argv)
                   :in-theory (enable fn-pat-bind fn-pat-lookup fn-pat-words-p)))))

(local
 (defthm fn-pat-order-filter-members
   (implies (and (member-equal a needs) (member-equal a order))
            (member-equal a (fn-pat-order-filter order needs)))))

(local
 (defthm fn-pat-cover-when-all-bound
   (implies (and (subsetp-equal needs args)
                 (<= (len args) (len argv))
                 (fn-pat-words-p (take (len args) argv)))
            (fn-pat-bindings-coverp needs (fn-pat-bind args argv)))
   :hints (("Goal" :induct (len needs)
                   :in-theory (enable fn-pat-bindings-coverp subsetp-equal)))))

(local
 (defthm fn-pat-options-never-run
   (not (equal (car (fn-pat-options words timeout count)) :run))
   :hints (("Goal" :in-theory (enable fn-pat-options)))))

(local
 (defthm fn-pat-member-true-list-fix
   (iff (member-equal a (true-list-fix xs)) (member-equal a xs))))

(local
 (defthm fn-pat-needs-in-order-filter
   (implies (and (subsetp-equal sub needs)
                 (subsetp-equal sub order))
            (subsetp-equal sub (fn-pat-order-filter order (true-list-fix needs))))
   :hints (("Goal" :induct (len sub)
                   :in-theory (e/d (subsetp-equal) (fn-pat-order-filter))))))

(local
 (defthm fn-pat-steps-needs-ordered
   (subsetp-equal (fn-pat-steps-needs steps) *fn-pat-arg-order*)
   :hints (("Goal" :in-theory (enable subsetp-equal)))))

(local
 (defthm fn-pat-subsetp-append
   (iff (subsetp-equal (append x y) z)
        (and (subsetp-equal x z) (subsetp-equal y z)))))

(local
 (defthm fn-pat-subsetp-cons
   (implies (subsetp-equal x y) (subsetp-equal x (cons a y)))))

(local (defthm fn-pat-subsetp-refl (subsetp-equal x x)))

(local
 (defthm fn-pat-plan-needs-ordered
   (subsetp-equal (fn-pat-plan-needs plan) *fn-pat-arg-order*)
   :hints (("Goal" :in-theory (e/d (fn-pat-plan-needs) (fn-pat-steps-needs))))))

(local
 (defthm fn-pat-plan-needs-in-args
   (subsetp-equal (fn-pat-plan-needs plan) (fn-pat-plan-args plan))
   :hints (("Goal" :in-theory (e/d (fn-pat-plan-args)
                                   (fn-pat-order-filter fn-pat-plan-needs
                                    fn-pat-needs-in-order-filter))
                   :use ((:instance fn-pat-needs-in-order-filter
                                    (order *fn-pat-arg-order*)
                                    (sub (fn-pat-plan-needs plan))
                                    (needs (fn-pat-plan-needs plan))))))))

; KEYSTONE: an accepted command line binds every argument every step of its
; plan needs (once and per message) to a nonempty word without NUL, so the
; host's plan loop never meets an unbound argument.
(defthm fn-pat-cli-run-binds-every-step
  (let ((cli (fn-pat-cli-plan name role argv)))
    (implies (equal (car cli) :run)
             (fn-pat-bindings-coverp (fn-pat-plan-needs (nth 4 cli))
                                     (nth 5 cli))))
  :hints (("Goal" :in-theory (disable fn-pat-plan-needs fn-pat-plan-args
                                      fn-pat-options fn-pat-find
                                      fn-pat-usage-text fn-pat-words-p
                                      fn-pat-bindings-coverp fn-pat-bind))))
