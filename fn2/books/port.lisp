; The port form (layer E; fn2/docs/e-surface.md section 2; WIDEST-ROLE section 2,
; Port). A port is an interface as data: DEFPORT declares its verbs once
; (request and result fields, the effect, how a lost reply is settled, the
; grant scope and meter dimensions that are its first preconditions, its
; refusal words), and DEFCARRIER binds the verbs to one wire (an FNCT frame
; kind and request code, or a command of a DEFGRAMMAR table). Both live in the
; grammar machinery: every verb and every carrier is a (:command NAME) row
; through FN2-DECLARE, beside the NNTP commands, so the parser, the machine,
; the client tables, the checkers and the wire-grammar export read one
; declaration. What is generated, and checked at expansion (a macro refusal,
; never a run-time surprise):
; - the verb and reason enums, the per-verb readers, the outcome recognizer
;   (an outcome is (:accepted VALUES) with one value per result field,
;   (:refused REASON [DETAIL]) with a reason the verb may give (DETAIL, e.g.
;   the evidence outcome beside an article's conflict refusal), or (:uncertain PHASE),
;   which only a :durable verb can produce);
; - PORT-admit, the precondition order every verb shares: grant, then meter,
;   then the verb's own predicate. The refusal words of the first two steps
;   (access, meter) are added to every verb by the generator, so no verb can
;   omit them;
; - per carrier: every verb bound, refused by name, or declared not carried;
;   for a grammar carrier, every outcome class the verb can produce has a
;   reply row of that class in the bound command (accepted, refused and
;   uncertain stay distinct all the way out); the carrier's loss signature
;   per verb as a set of (field . word), so a bridge's loss is computed as
;   their union.
(in-package "ACL2")
(include-book "grammar")
(fn2-book-layer :e)

(make-event (value (fn2-declare '(:operation-set fn2-port) nil nil nil)))

(defconst *fn2-port-effects* '(:read :durable :park))
(defconst *fn2-port-retries* '(:op :idempotent :position :repeat))
(defconst *fn2-port-grant-scopes* '(:read :append :consume))
; The preconditions' refusal words, added to every verb (section 6).
(defconst *fn2-port-precondition-reasons* '(access meter))
;; Losses (section 2.3) are independent, so a loss signature is a product:
;; per verb, the set of (FIELD . WORD) a translation does not carry, FIELD one
;; of the verb's request or result fields or * for the whole verb. A bridge
;; through two carriers loses the union of their losses, verb by verb.
(defconst *fn2-port-loss-words* '(:retry-by-message-id :reply-code-only :no-position :not-carried))
(defun fn2-port-loss-union (a b)
  (declare (xargs :guard (and (true-listp a) (true-listp b))))
  (union-equal a b))
(defthm fn2-port-loss-union-keeps-both
  (implies (or (member-equal x a) (member-equal x b))
           (member-equal x (fn2-port-loss-union a b))))

;; ---------------------------------------------------------------------------
;; DEFPORT

(defun fn2-port-symbols-p (xs)
  (declare (xargs :verify-guards nil))
  (if (atom xs) (null xs)
    (and (car xs) (symbolp (car xs)) (not (keywordp (car xs))) (not (eq (car xs) t))
         (fn2-port-symbols-p (cdr xs)))))
(defun fn2-port-field-name (f)
  (declare (xargs :verify-guards nil))
  (if (and (consp f) (eq (car f) :opt)) (cadr f) f))
(defun fn2-port-field-names (fs)
  (declare (xargs :verify-guards nil))
  (if (atom fs) nil (cons (fn2-port-field-name (car fs)) (fn2-port-field-names (cdr fs)))))
(defun fn2-port-subset-p (xs ys)
  (declare (xargs :verify-guards nil))
  (if (atom xs) t (and (member-equal (car xs) ys) (fn2-port-subset-p (cdr xs) ys))))
(defun fn2-port-grant-p (g)
  (declare (xargs :verify-guards nil))
  (and (true-listp g) (equal (len g) 2) (member-eq (car g) *fn2-port-grant-scopes*) (symbolp (cadr g))))

; The first problem with one verb's row, or nil.
(defun fn2-port-verb-problem (v fields reasons)
  (declare (xargs :verify-guards nil))
  (let* ((name (car v)) (p (cdr v))
         (req (fn2-port-field-names (fn2-decl-get :request p)))
         (res (fn2-port-field-names (fn2-decl-get :result p)))
         (effect (fn2-decl-get :effect p)) (retry (fn2-decl-get :retry p))
         (grant (fn2-decl-get :grant p)) (meter (fn2-decl-get :meter p))
         (own (fn2-decl-get :reasons p)))
    (cond ((not (and (symbolp name) name (not (keywordp name)))) (list :verb-name name))
          ((not (keyword-value-listp p)) (list :verb-row name))
          ((not (and (fn2-port-symbols-p req) (fn2-port-subset-p req fields))) (list :request-field name))
          ((not (and (fn2-port-symbols-p res) (fn2-port-subset-p res fields))) (list :result-field name))
          ((not (member-eq effect *fn2-port-effects*)) (list :effect name))
          ((not (member-eq retry *fn2-port-retries*)) (list :retry name))
          ; A durable verb's lost reply must be settleable: by its operation
          ; identity, by repeating it, or by asking the position.
          ((and (eq effect :durable) (eq retry :repeat)) (list :durable-unsettleable name))
          ((not (fn2-port-grant-p grant)) (list :grant name))
          ((not (member-eq (cadr grant) req)) (list :grant-field name))
          ((not (and (keyword-listp meter) (consp meter) (member-eq :requests meter))) (list :meter name))
          ((not (and (fn2-port-symbols-p own) (fn2-port-subset-p own reasons))) (list :reasons name))
          ((intersectp-eq own *fn2-port-precondition-reasons*) (list :precondition-reason-restated name))
          ((not (stringp (fn2-decl-get :spec p))) (list :spec name))
          (t nil))))
(defun fn2-port-verbs-problem (vs fields reasons seen)
  (declare (xargs :verify-guards nil))
  (cond ((atom vs) (and vs (list :verbs vs)))
        ((not (consp (car vs))) (list :verb (car vs)))
        ((member-eq (caar vs) seen) (list :duplicate-verb (caar vs)))
        (t (or (fn2-port-verb-problem (car vs) fields reasons)
               (fn2-port-verbs-problem (cdr vs) fields reasons (cons (caar vs) seen))))))
(defun fn2-port-problem (fields reasons verbs)
  (declare (xargs :verify-guards nil))
  (cond ((not (and (alistp fields) (fn2-port-symbols-p (strip-cars fields))
                   (no-duplicatesp-eq (strip-cars fields)))) (list :fields))
        ((not (and (fn2-port-symbols-p reasons) (no-duplicatesp-eq reasons)
                   (not (intersectp-eq reasons *fn2-port-precondition-reasons*)))) (list :reasons))
        ((atom verbs) (list :no-verbs))
        (t (fn2-port-verbs-problem verbs (strip-cars fields) reasons nil))))

(defun fn2-port-verb-declarations (port verbs)
  (declare (xargs :verify-guards nil))
  (if (atom verbs) nil
    (let ((p (cdar verbs)))
      (cons (fn2-declare (list :command (fn2-gram-sym port "-" (caar verbs)))
              (list :grammar port :port t :verb (caar verbs)
                    :request (fn2-decl-get :request p) :result (fn2-decl-get :result p)
                    :effect (fn2-decl-get :effect p) :retry (fn2-decl-get :retry p)
                    :grant (fn2-decl-get :grant p) :meter (fn2-decl-get :meter p)
                    :reasons (append *fn2-port-precondition-reasons* (fn2-decl-get :reasons p))
                    :spec (fn2-decl-get :spec p))
              nil nil)
            (fn2-port-verb-declarations port (cdr verbs))))))
(defun fn2-port-case-arms (verbs key)
  (declare (xargs :verify-guards nil))
  (if (atom verbs) nil
    (let* ((p (cdar verbs))
           (v (case key
                (:reasons (append *fn2-port-precondition-reasons* (fn2-decl-get :reasons p)))
                (:arity (len (fn2-port-field-names (fn2-decl-get :result p))))
                (:grant-scope (car (fn2-decl-get :grant p)))
                (:grant-field (cadr (fn2-decl-get :grant p)))
                (otherwise (fn2-decl-get key p)))))
      (cons `(,(caar verbs) ',v) (fn2-port-case-arms (cdr verbs) key)))))

(defun fn2-port-reader (port verbs suffix key)
  (declare (xargs :verify-guards nil))
  `(defun ,(fn2-gram-sym port "-verb-" suffix) (verb)
     (declare (xargs :guard t))
     (case verb ,@(fn2-port-case-arms verbs key) (otherwise nil))))
(defun fn2-port-events (port fields reasons verbs)
  (declare (xargs :verify-guards nil))
  `(progn
       (defconst ,(fn2-gram-const port "-verbs") ',(strip-cars verbs))
       (defconst ,(fn2-gram-const port "-fields") ',fields)
       (defconst ,(fn2-gram-const port "-reasons") ',(append *fn2-port-precondition-reasons* reasons))
       ,@(fn2-port-verb-declarations port verbs)
       (defun ,(fn2-gram-sym port "-verb-p") (verb)
         (declare (xargs :guard t))
         (if (member-eq verb ,(fn2-gram-const port "-verbs")) t nil))
       ,(fn2-port-reader port verbs "effect" :effect)
       ,(fn2-port-reader port verbs "retry" :retry)
       ,(fn2-port-reader port verbs "reasons" :reasons)
       ,(fn2-port-reader port verbs "arity" :arity)
       ,(fn2-port-reader port verbs "request" :request)
       ,(fn2-port-reader port verbs "result" :result)
       ,(fn2-port-reader port verbs "grant-scope" :grant-scope)
       ,(fn2-port-reader port verbs "grant-field" :grant-field)
       ,(fn2-port-reader port verbs "meter" :meter)
       ,(fn2-port-reader port verbs "spec" :spec)
       ; An outcome the verb may produce: accepted with one value per result
       ; field, refused with one of its words, uncertain only when durable.
       (defun ,(fn2-gram-sym port "-outcome-p") (verb outcome)
         (declare (xargs :guard t))
         (and (consp outcome) (true-listp outcome)
              (case (car outcome)
                (:accepted (and (equal (len outcome) 2) (true-listp (cadr outcome))
                                (equal (len (cadr outcome)) (,(fn2-gram-sym port "-verb-arity") verb))))
                (:refused (and (member (len outcome) '(2 3)) (symbolp (cadr outcome))
                               (member-eq (cadr outcome) (,(fn2-gram-sym port "-verb-reasons") verb))
                               t))
                (:uncertain (and (equal (len outcome) 2)
                                 (eq (,(fn2-gram-sym port "-verb-effect") verb) :durable)))
                (otherwise nil))))
       ; The precondition order (section 6): grant, then meter, then the
       ; verb's own predicate. GRANT-OK is the grant predicate's answer;
       ; METER is the ledger's code for the verb's reservation (:ok, :limit,
       ; :shared); a shared exhaustion is a continuation (:park), never a
       ; refusal. :proceed means the verb's own predicate runs next.
       (defun ,(fn2-gram-sym port "-admit") (verb grant-ok meter)
         (declare (xargs :guard t))
         (cond ((not (,(fn2-gram-sym port "-verb-p") verb)) '(:refused :no-such-verb))
               ((not grant-ok) '(:refused access))
               ((eq meter :limit) '(:refused meter))
               ((eq meter :shared) :park)
               ((eq meter :ok) :proceed)
               (t '(:refused meter))))
       (make-event (value (fn2-declare '(:operation-set ,port) nil nil nil)))))

(defmacro defport (port &key fields reasons verbs)
  (let ((problem (and (symbolp port) (fn2-port-problem fields reasons verbs))))
    (if (or problem (not (symbolp port)))
        (er hard 'defport "Invalid port declaration ~x0: ~x1." port problem)
      (fn2-port-events port fields reasons verbs))))

;; ---------------------------------------------------------------------------
;; DEFCARRIER

; The port's verb rows, read from the declaration table.
(defun fn2-port-rows (port rows)
  (declare (xargs :verify-guards nil))
  (cond ((atom rows) nil)
        ((and (eq (fn2-decl-get :grammar (cdar rows)) port) (fn2-decl-get :port (cdar rows)))
         (cons (cons (fn2-decl-get :verb (cdar rows)) (cdar rows)) (fn2-port-rows port (cdr rows))))
        (t (fn2-port-rows port (cdr rows)))))
(defun fn2-port-classes (row)
  (declare (xargs :verify-guards nil))
  (if (eq (fn2-decl-get :effect row) :durable) '(:accepted :refused :uncertain) '(:accepted :refused)))
(defun fn2-port-reply-classes (replies)
  (declare (xargs :verify-guards nil))
  (if (atom replies) nil (cons (fn2-decl-get :class (cdar replies)) (fn2-port-reply-classes (cdr replies)))))
(defun fn2-port-missing-class (need have)
  (declare (xargs :verify-guards nil))
  (cond ((atom need) nil) ((member-eq (car need) have) (fn2-port-missing-class (cdr need) have)) (t (car need))))
(defun fn2-port-losses-p (losses rows)
  ; Each loss (VERB FIELD WORD): VERB a port verb, FIELD one of its fields or *.
  (declare (xargs :verify-guards nil))
  (if (atom losses) (null losses)
    (let* ((l (car losses)) (row (and (consp l) (cdr (assoc-eq (car l) rows)))))
      (and (true-listp l) (equal (len l) 3) row
           (or (eq (cadr l) '*)
               (member-eq (cadr l) (append (fn2-port-field-names (fn2-decl-get :request row))
                                           (fn2-port-field-names (fn2-decl-get :result row)))))
           (member-eq (caddr l) *fn2-port-loss-words*)
           (fn2-port-losses-p (cdr losses) rows)))))
(defun fn2-port-not-carried-p (verb losses)
  (declare (xargs :verify-guards nil))
  (cond ((atom losses) nil)
        ((and (eq (caar losses) verb) (eq (cadr (car losses)) '*) (eq (caddr (car losses)) :not-carried)) t)
        (t (fn2-port-not-carried-p verb (cdr losses)))))
; The classes of the named terminal replies of a grammar command (a
; continuation such as POST's 340 is never a terminal outcome).
(defun fn2-port-terminal-classes (keys replies)
  (declare (xargs :verify-guards nil))
  (cond ((atom keys) nil)
        ((assoc-eq (car keys) replies)
         (cons (fn2-decl-get :class (cdr (assoc-eq (car keys) replies)))
               (fn2-port-terminal-classes (cdr keys) replies)))
        (t (cons :no-such-reply (fn2-port-terminal-classes (cdr keys) replies)))))
; The first problem with one binding, given the carrier's kind.
(defun fn2-port-binding-problem (b rows grammar world)
  (declare (xargs :verify-guards nil))
  (let ((row (cdr (assoc-eq (car b) rows))))
    (cond ((not (consp b)) (list :binding b))
          ((null row) (list :not-a-verb (car b)))
          (grammar
           ; (VERB CMD :terminal (REPLY-KEY ...)): the terminal replies that
           ; carry the verb's outcomes, covering every class it can produce.
           (let* ((cmd (and (consp (cdr b)) (symbolp (cadr b)) (fn2-gram-sym grammar "-" (cadr b))))
                  (crow (and cmd (fn2-decl-row (list :command cmd) world)))
                  (keys (fn2-decl-get :terminal (cddr b)))
                  (classes (and crow (fn2-port-terminal-classes keys (fn2-decl-get :replies crow))))
                  (missing (fn2-port-missing-class (fn2-port-classes row) classes)))
             (cond ((not (and crow (eq (fn2-decl-get :grammar crow) grammar))) (list :no-such-command (car b) cmd))
                   ((not (and (keyword-value-listp (cddr b)) (consp keys) (symbol-listp keys))) (list :terminal (car b)))
                   ((member-eq :no-such-reply classes) (list :no-such-reply (car b) cmd keys))
                   (missing (list :class-unrepresented (car b) cmd missing))
                   (t nil))))
          ((not (and (true-listp b) (equal (len b) 3) (natp (cadr b)) (< (cadr b) 256)
                     (natp (caddr b)) (< (caddr b) 256))) (list :frame-binding b))
          (t nil))))
(defun fn2-port-bindings-problem (bs rows grammar world)
  (declare (xargs :verify-guards nil))
  (if (atom bs) nil
    (or (fn2-port-binding-problem (car bs) rows grammar world)
        (fn2-port-bindings-problem (cdr bs) rows grammar world))))
(defun fn2-port-frame-keys (bs)
  (declare (xargs :verify-guards nil))
  (if (atom bs) nil (cons (cdar bs) (fn2-port-frame-keys (cdr bs)))))
; Every verb exactly once: bound, refused by name, or declared not carried.
(defun fn2-port-coverage-problem (verbs bound refused losses)
  (declare (xargs :verify-guards nil))
  (if (atom verbs) nil
    (let* ((v (car verbs))
           (n (+ (if (member-eq v bound) 1 0) (if (member-eq v refused) 1 0)
                 (if (fn2-port-not-carried-p v losses) 1 0))))
      (if (equal n 1) (fn2-port-coverage-problem (cdr verbs) bound refused losses)
        (list :coverage v n)))))
(defun fn2-port-carrier-problem (port grammar frame binds refuses loses world)
  (declare (xargs :verify-guards nil))
  (let* ((rows (fn2-port-rows port (fn2-decl-rows :command world)))
         (verbs (strip-cars rows)))
    (cond ((atom rows) (list :no-such-port port))
          ((not (or (and grammar (symbolp grammar) (null frame)) (and (eq frame :fnct) (null grammar))))
           (list :carrier-kind grammar frame))
          ((not (and (alistp binds) (no-duplicatesp-eq (strip-cars binds)))) (list :binds))
          ((and frame (not (no-duplicatesp-equal (fn2-port-frame-keys binds)))) (list :frame-code-reused))
          ((not (and (symbol-listp refuses) (fn2-port-subset-p refuses verbs))) (list :refuses))
          ((not (fn2-port-losses-p loses rows)) (list :loses))
          (t (or (fn2-port-bindings-problem binds rows grammar world)
                 (fn2-port-coverage-problem verbs (strip-cars binds) refuses loses))))))

(defun fn2-port-verb-loss (verb refuses losses)
  ; The set of (FIELD . WORD) the carrier loses for VERB.
  (declare (xargs :verify-guards nil))
  (cond ((member-eq verb refuses) '((* . :not-carried)))
        ((atom losses) nil)
        ((eq (caar losses) verb)
         (fn2-port-loss-union (list (cons (cadr (car losses)) (caddr (car losses))))
                              (fn2-port-verb-loss verb nil (cdr losses))))
        (t (fn2-port-verb-loss verb refuses (cdr losses)))))
(defun fn2-port-loss-arms (verbs refuses losses)
  (declare (xargs :verify-guards nil))
  (if (atom verbs) nil
    (cons `(,(car verbs) ',(fn2-port-verb-loss (car verbs) refuses losses))
          (fn2-port-loss-arms (cdr verbs) refuses losses))))

(defun fn2-port-carrier-events (carrier port grammar frame binds refuses loses world)
  (declare (xargs :verify-guards nil))
  (let ((verbs (strip-cars (fn2-port-rows port (fn2-decl-rows :command world)))))
    `(progn
       ,(fn2-declare (list :command carrier)
          (list :grammar port :carrier t :wire (or grammar frame) :binds binds :refuses refuses :loses loses)
          nil nil)
       (defconst ,(fn2-gram-const carrier "-binds") ',binds)
       (defun ,(fn2-gram-sym carrier "-binding") (verb)
         (declare (xargs :guard t))
         (cdr (assoc-eq verb ,(fn2-gram-const carrier "-binds"))))
       ; The carrier's loss per verb: the (field . word) pairs it declares.
       (defun ,(fn2-gram-sym carrier "-loss") (verb)
         (declare (xargs :guard t))
         (case verb ,@(fn2-port-loss-arms verbs refuses loses) (otherwise '((* . :not-carried))))))))

(defmacro defcarrier (carrier &key port grammar frame binds refuses loses)
  `(make-event
    (let ((problem (fn2-port-carrier-problem ',port ',grammar ',frame ',binds ',refuses ',loses (w state))))
      (if problem (er soft 'defcarrier "Invalid carrier ~x0: ~x1." ',carrier problem)
        (value (fn2-port-carrier-events ',carrier ',port ',grammar ',frame ',binds ',refuses ',loses (w state)))))))
