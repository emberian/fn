; fn: `fn-defrecord' --- the opaque-record pattern of docs/proof-style.md,
; generated instead of written.
;
; Section 1 of docs/proof-style.md fixes what a record is: a shape predicate,
; a constructor, total `mbe' accessors, one accessor-of-constructor lemma per
; field, three forward-chaining shape facts, and the withdrawal of every
; `:definition' rune so that nothing above the record opens it.  Written by
; hand that is eleven events for a three-field record and forty-one for a
; nine-field one; `books/acceptance.lisp' and `books/scheduler.lisp' each
; carry more than forty of them, and every one is an opportunity to omit a
; forward fact and hand the next lane a rule fan (BOARD 2026-09-20, the C2,
; checkpoint, reader-profile and article-exports diagnoses).
;
; This book has no `include-book' and leaves no rule enabled: its helpers are
; `:program' mode, so they have no definitional axiom, and it defines only
; macros.  A book that uses `fn-defrecord' must have the two total selectors
; in scope --- `fn-ag-car' and `fn-ag-cdr' from `books/acceptance-alloc.lisp'
; by default, or whatever `:car'/`:cdr' name it passes.
;
; What is deliberately NOT generated:
;
;   * no `consp'/`true-listp' rewrite rule.  The three shape facts are
;     `:forward-chaining' only (proof-style section 1).
;   * no enabled equality beyond the record lemmas.  Injectivity is
;     `:rule-classes nil' by default, a name for one includer's `:use'
;     (proof-style sections 3 and 7); `:injective :rewrite' asks for the rule
;     and is the caller's decision to defend.
;   * no `len' conjunct in the recognizer.  The recognizer is written over
;     the shape predicate and the accessors, never over `car'/`len'.
;
; Layout.  `:positional' (the default) is the tree's existing raw-list
; encoding: the constructor is a `list' call, an untagged record puts field i
; at index i, and a `:tag' keyword occupies index 0 and shifts the fields by
; one.  Both forms are in the tree today (`fn-sched-item' untagged,
; `fn-sched-state' tagged `:fn-sched-state'), and both are what
; `books/records.lisp' and the host CBOR codec already encode, so a migration
; to `fn-defrecord' moves no bytes.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; Term and symbol plumbing.  `:program' mode on purpose: these run at
; macroexpansion time and must contribute no rune to any includer.

(defun fn-defrecord-nest (k fn term)
  (declare (xargs :mode :program))
  (if (zp k) term (fn-defrecord-nest (1- k) fn (list fn term))))

; `(car (cdr^k var))', in the primitives `car-fn'/`cdr-fn'.
(defun fn-defrecord-selector (k car-fn cdr-fn var)
  (declare (xargs :mode :program))
  (list car-fn (fn-defrecord-nest k cdr-fn var)))

(defun fn-defrecord-name (parts witness)
  (declare (xargs :mode :program))
  (packn-pos parts witness))

(defun fn-defrecord-field-accessors (fields)
  (declare (xargs :mode :program))
  (if (endp fields) nil
    (cons (car (car fields)) (fn-defrecord-field-accessors (cdr fields)))))

; The type entry of a field spec: `t', a unary predicate, or a term over `x'.
(defun fn-defrecord-field-type (field)
  (declare (xargs :mode :program))
  (if (consp (cdr field)) (cadr field) t))

; -----------------------------------------------------------------------------
; The generated events, one builder each.

; One total `mbe' accessor per field, guards verified after the fact.  The
; `:logic' body is the raw selector, so the accessor IS `(car (cdr^i x))' in
; the logic and any unfolding an includer wants is the definition; the `:exec'
; body is the total helper, which is why the guard can be `t'.
(defun fn-defrecord-accessor-events (fields index car-fn cdr-fn)
  (declare (xargs :mode :program))
  (if (endp fields) nil
    (let ((accessor (car (car fields))))
      (list* `(defun ,accessor (x)
                (declare (xargs :guard t :verify-guards nil))
                (mbe :logic ,(fn-defrecord-selector index 'car 'cdr 'x)
                     :exec ,(fn-defrecord-selector index car-fn cdr-fn 'x)))
             `(verify-guards ,accessor)
             (fn-defrecord-accessor-events (cdr fields) (1+ index) car-fn cdr-fn)))))

(defun fn-defrecord-of-constructor-events (fields formals shape constructor call)
  (declare (xargs :mode :program))
  (if (endp fields) nil
    (let ((accessor (car (car fields))))
      (cons `(defthm ,(fn-defrecord-name (list accessor "-OF-" constructor) shape)
               (equal (,accessor ,call) ,(car formals)))
            (fn-defrecord-of-constructor-events (cdr fields) (cdr formals)
                                                shape constructor call)))))

(defun fn-defrecord-consp-conjuncts (accessors)
  (declare (xargs :mode :program))
  (if (endp accessors) nil
    (cons `(implies (,(car accessors) x) (consp x))
          (fn-defrecord-consp-conjuncts (cdr accessors)))))

; One `:forward-chaining' class per field, triggered on the field term.  A
; single rule whose conclusion is a conjunction would be triggered on whichever
; term ACL2 chose; the point of this family is that `(stringp (fn-x-field a))'
; in a hypothesis puts `(consp a)' in the context, so each conjunct gets its
; own trigger (proof-style section 1).
(defun fn-defrecord-consp-classes (accessors)
  (declare (xargs :mode :program))
  (if (endp accessors) nil
    (cons `(:forward-chaining
            :corollary (implies (,(car accessors) x) (consp x))
            :trigger-terms ((,(car accessors) x)))
          (fn-defrecord-consp-classes (cdr accessors)))))

(defun fn-defrecord-recognizer-conjuncts (fields)
  (declare (xargs :mode :program))
  (if (endp fields) nil
    (let* ((accessor (car (car fields)))
           (type (fn-defrecord-field-type (car fields)))
           (rest (fn-defrecord-recognizer-conjuncts (cdr fields))))
      (cond ((eq type t) rest)
            ((symbolp type) (cons `(,type (,accessor x)) rest))
            (t (cons type rest))))))

(defun fn-defrecord-internals-runes (names)
  (declare (xargs :mode :program))
  (if (endp names) nil
    (cons `(:d ,(car names)) (fn-defrecord-internals-runes (cdr names)))))

(defun fn-defrecord-equal-conjuncts (left right)
  (declare (xargs :mode :program))
  (if (endp left) nil
    (cons `(equal ,(car left) ,(car right))
          (fn-defrecord-equal-conjuncts (cdr left) (cdr right)))))

(defun fn-defrecord-primed (formals witness)
  (declare (xargs :mode :program))
  (if (endp formals) nil
    (cons (fn-defrecord-name (list (car formals) "-2") witness)
          (fn-defrecord-primed (cdr formals) witness))))

; -----------------------------------------------------------------------------
; fn-defrecord
;
;   (fn-defrecord fn-sched-config
;     :tag :fn-sched-config
;     :constructor (fn-sched-config queue-bound aging-limit retry-bound)
;     :fields ((fn-sched-queue-bound posp)
;              (fn-sched-aging-limit posp)
;              (fn-sched-retry-bound posp)))
;
; generates, in this order: the shape predicate; the constructor; one total
; `mbe' accessor per field with its `verify-guards'; `<shape>-of-<ctor>'; one
; `<accessor>-of-<ctor>' per field; `<ctor>-injective'; the three
; forward-chaining shape facts `<shape>-forward-shape',
; `<name>-accessors-forward-consp' and `<recognizer>-forward-shape'; the
; recognizer, written over the shape predicate and the accessors; and
; `<name>-internals' --- the `:d' runes of the shape, the constructor and
; every accessor --- withdrawn on the spot.
;
; Accessor names are given in full because the tree does not derive them from
; the record name (`fn-sched-config' has `fn-sched-queue-bound', `fn-sched-state'
; has `fn-sched-generation'), and the constructor is given with its formals
; because those formals are the variables of the generated lemmas.
;
; A field type is `t' (unconstrained), a unary predicate symbol applied to the
; field, or a term over the recognizer variable `x'; `:extra' supplies
; whole-record conjuncts in the same vocabulary.  `:recognizer nil' suppresses
; the recognizer for a record that has none (`fn-sched-result'), and then the
; third forward fact is not generated either.

(defmacro fn-defrecord (name &key
                             constructor          ; (ctor formal ...); required
                             fields               ; ((accessor type) ...)
                             tag                  ; keyword at index 0, or nil
                             (layout ':positional)
                             shape                ; default <name>-SHAPEP
                             (recognizer ':default) ; symbol, or nil to suppress
                             extra                ; more recognizer conjuncts
                             (injective 'nil)     ; nil | :rewrite
                             internals            ; default <name>-INTERNALS
                             (car-fn 'fn-ag-car)
                             (cdr-fn 'fn-ag-cdr))
  (let* ((ctor (car constructor))
         (formals (cdr constructor))
         (accessors (fn-defrecord-field-accessors fields))
         (shapep (or shape (fn-defrecord-name (list name "-SHAPEP") name)))
         (recp (cond ((eq recognizer :default)
                      (fn-defrecord-name (list name "P") name))
                     (t recognizer)))
         (theory (or internals (fn-defrecord-name (list name "-INTERNALS") name)))
         (offset (if tag 1 0))
         (width (+ offset (len fields)))
         (call (cons ctor formals))
         (primed (fn-defrecord-primed formals name))
         (internal-names (cons shapep (cons ctor accessors))))
    (if (not (eq layout :positional))
        (er hard? 'fn-defrecord
            "~x0 is the only layout fn-defrecord generates; ~x1 asked for ~x2."
            :positional name layout)
    (cons
     'progn
     (append
     (list
      `(defun ,shapep (x)
         (declare (xargs :guard t))
         (and (true-listp x)
              (equal (len x) ,width)
              ,@(if tag (list `(equal (car x) ,tag)) nil)))
      `(defun ,ctor ,formals
         (declare (xargs :guard t))
         (list ,@(if tag (cons tag formals) formals))))
     (fn-defrecord-accessor-events fields offset car-fn cdr-fn)
     (list
      `(defthm ,(fn-defrecord-name (list shapep "-OF-" ctor) name)
         (,shapep ,call)))
     (fn-defrecord-of-constructor-events fields formals shapep ctor call)
     (list
      `(defthm ,(fn-defrecord-name (list ctor "-INJECTIVE") name)
         (equal (equal ,call ,(cons ctor primed))
                (and ,@(fn-defrecord-equal-conjuncts formals primed)))
         ,@(if (eq injective :rewrite) nil (list :rule-classes 'nil)))
      `(defthm ,(fn-defrecord-name (list shapep "-FORWARD-SHAPE") name)
         (implies (,shapep x) (and (consp x) (true-listp x)))
         :rule-classes :forward-chaining)
      `(defthm ,(fn-defrecord-name (list name "-ACCESSORS-FORWARD-CONSP") name)
         (and ,@(fn-defrecord-consp-conjuncts accessors))
         :rule-classes ,(fn-defrecord-consp-classes accessors))
      `(deftheory ,theory ',(fn-defrecord-internals-runes internal-names))
      `(in-theory (disable ,theory)))
     (if (null recp) nil
       (list
        `(defun ,recp (x)
           (declare (xargs :guard t))
           (and (,shapep x)
                ,@(fn-defrecord-recognizer-conjuncts fields)
                ,@extra))
        `(defthm ,(fn-defrecord-name (list recp "-FORWARD-SHAPE") name)
           (implies (,recp x) (and (consp x) (true-listp x)))
           :rule-classes :forward-chaining
           :hints (("Goal" :in-theory (enable ,shapep)))))))))))

; -----------------------------------------------------------------------------
; fn-defrecord-export

(defun fn-defrecord-export-recognizers (records)
  (declare (xargs :mode :program))
  (if (endp records) nil
    (cons (fn-defrecord-name (list (car records) "P") (car records))
          (fn-defrecord-export-recognizers (cdr records)))))

; The book-final export theory of docs/proof-style.md section 2.
;
;   (fn-defrecord-export fn-sched-vocabulary
;     :records (fn-sched-contact fn-sched-config fn-sched-item fn-sched-state)
;     :also (fn-sched-initial-state fn-sched-step fn-sched-trace))
;
; names, in one `deftheory', the recognizers of the book's records (each
; `<record>p'), any further recognizers spelled out under `:recognizers', and
; the proof vocabulary under `:also'; then withdraws the whole name.  A book
; above re-enables exactly that vocabulary in one line without knowing the
; list, which is the only sanctioned way to open another cluster's internals
; --- and never book-wide (proof-style, "Never enable a vocabulary
; book-wide").

(defmacro fn-defrecord-export (theory &key records recognizers also)
  (list 'progn
        `(deftheory ,theory
           ',(append (fn-defrecord-export-recognizers records) recognizers also))
        `(in-theory (disable ,theory))))
