; Arm contracts (R7; DSL-METATHEORY 5.2-5.3, section 8 decision 2). Every
; continuation and observation handler of a machine declares what it may
; cost, write, change and become, and its body is written in a restricted
; arm language whose violations are macro refusals. Outside calls declare
; their work and resource effects with defcost. This book is a library of
; expansion-time functions; defmachine and defmachine-callback use it.
(in-package "ACL2")
(include-book "resources")
(include-book "operations")

(defconst *fn2-arm-dimensions* '(:bytes :steps :descriptors))
; An op reservation is held only across one issue: the pending operation is
; the outstanding table's, never part of a row's holds (D0).
(defconst *fn2-arm-transient-kinds* '(:operation))
; What an arm body may call besides its declared operations: arithmetic,
; comparison and logic over values, never over a table.
(defconst *fn2-arm-primitives*
  '(+ - * < <= > >= = /= equal eq eql min max nfix ifix zp zip natp posp
    integerp unsigned-byte-p 1+ 1- floor mod logand logior ash not
    binary-+ binary-* unary-- null))
(defconst *fn2-arm-control* '(if cond and or mv prog2$ progn case))
(defconst *fn2-arm-keys* '(:cost :writes :tables :next :uses :language :on-refusal :paths))
; The emitter's own stop branches (refused snapshots) may set the stop
; reason; every arm may therefore change the control child.
(defconst *fn2-arm-implicit-tables* '(fn2-core-control))

; Every problem of a check at once (DEV-LOOP 2): the non-nil messages of
; PS, one per numbered line after HEAD (a message), or the one alone.
(defun fn2-arm-nonnil (ps)
  (declare (xargs :guard t))
  (cond ((atom ps) nil) ((car ps) (cons (car ps) (fn2-arm-nonnil (cdr ps)))) (t (fn2-arm-nonnil (cdr ps)))))
(defun fn2-arm-problem-lines (ps n)
  (declare (xargs :verify-guards nil))
  (if (atom ps) ""
    (msg "~%  (~x0) ~@1~@2" n (car ps) (fn2-arm-problem-lines (cdr ps) (+ 1 n)))))
(defun fn2-arm-problems (head ps)
  (declare (xargs :verify-guards nil))
  (let ((ps (fn2-arm-nonnil ps)))
    (cond ((atom ps) nil)
          ((atom (cdr ps)) (msg "~@0~@1" head (car ps)))
          (t (msg "~@0~x1 problems, all of them:~@2" head (len ps) (fn2-arm-problem-lines ps 1))))))

(defun fn2-arm-get (key plist)
  (declare (xargs :verify-guards nil))
  (cond ((atom plist) nil)
        ((atom (cdr plist)) nil)
        ((eq key (car plist)) (cadr plist))
        (t (fn2-arm-get key (cddr plist)))))
(defun fn2-arm-plistp (plist keys)
  (declare (xargs :verify-guards nil))
  (if (atom plist) (null plist)
    (and (consp (cdr plist)) (member-eq (car plist) keys)
         (fn2-arm-plistp (cddr plist) keys))))
(defun fn2-arm-namesp (x)
  (declare (xargs :verify-guards nil))
  (if (atom x) (null x)
    (and (symbolp (car x)) (car x) (not (keywordp (car x))) (not (eq (car x) t))
         (fn2-arm-namesp (cdr x)))))
(defun fn2-arm-subsetp (a b)
  (declare (xargs :verify-guards nil))
  (if (atom a) t (and (member-equal (car a) b) (fn2-arm-subsetp (cdr a) b))))
(defun fn2-arm-minus (a b)
  (declare (xargs :verify-guards nil))
  (if (atom a) nil
    (if (member-equal (car a) b) (fn2-arm-minus (cdr a) b)
      (cons (car a) (fn2-arm-minus (cdr a) b)))))
;; Holds and effects as multisets (G3, D F13): two ranges of one kind are two
;; holdings, and two calls that each release one are two releases.
(defun fn2-arm-mminus (a b)
  ; A less one occurrence of each element of B
  (declare (xargs :verify-guards nil))
  (if (atom b) a
    (fn2-arm-mminus (if (member-equal (car b) a) (remove1-equal (car b) a) a) (cdr b))))
(defun fn2-arm-msubsetp (a b)
  ; every element of A, as often as A has it, is in B
  (declare (xargs :verify-guards nil))
  (if (atom a) t
    (and (member-equal (car a) b) (fn2-arm-msubsetp (cdr a) (remove1-equal (car a) b)))))

; ----------------------------------------------------------------------
; Cost forms: F ::= nat | *CONSTANT* | (+ F ...) | (max F ...) | (* nat F)
;                 | (:cost FN DIMENSION)
(mutual-recursion
 (defun fn2-cost-formp (form)
   (declare (xargs :verify-guards nil :measure (acl2-count form)))
   (cond ((natp form) t)
         ((symbolp form) (and form (not (keywordp form)) (not (eq form t))))
         ((atom form) nil)
         ((eq (car form) :cost)
          (and (true-listp form) (equal (len form) 3) (symbolp (cadr form)) (cadr form)
               (member-eq (caddr form) *fn2-arm-dimensions*)))
         ((member-eq (car form) '(+ max)) (fn2-cost-formsp (cdr form)))
         ((eq (car form) '*)
          (and (true-listp form) (equal (len form) 3) (natp (cadr form))
               (fn2-cost-formp (caddr form))))
         (t nil)))
 (defun fn2-cost-formsp (forms)
   (declare (xargs :verify-guards nil :measure (acl2-count forms)))
   (if (atom forms) (null forms)
     (and (fn2-cost-formp (car forms)) (fn2-cost-formsp (cdr forms))))))
(defun fn2-cost-plistp (cost)
  (declare (xargs :verify-guards nil))
  (and (fn2-arm-plistp cost *fn2-arm-dimensions*)
       (fn2-cost-formsp (list (or (fn2-arm-get :bytes cost) 0) (or (fn2-arm-get :steps cost) 0)
                              (or (fn2-arm-get :descriptors cost) 0)))))

; The calls a cost form cites, which must be calls the arm declares.
(mutual-recursion
 (defun fn2-cost-cites (form)
   (declare (xargs :verify-guards nil :measure (acl2-count form)))
   (cond ((atom form) nil)
         ((eq (car form) :cost) (list (cadr form)))
         ((eq (car form) '*) (fn2-cost-cites (caddr form)))
         (t (fn2-cost-cites-list (cdr form)))))
 (defun fn2-cost-cites-list (forms)
   (declare (xargs :verify-guards nil :measure (acl2-count forms)))
   (if (atom forms) nil
     (append (fn2-cost-cites (car forms)) (fn2-cost-cites-list (cdr forms))))))

(defun fn2-cost-constant (name world)
  (declare (xargs :verify-guards nil))
  (let ((c (getpropc name 'const nil world)))
    (and (quotep c) (natp (unquote c)) (unquote c))))
(defun fn2-cost-dimension-index (dimension)
  (declare (xargs :verify-guards nil))
  (case dimension (:bytes 0) (:steps 1) (otherwise 2)))
; A cited cost: a defcost row's (constant) form, or the evaluated bound a
; same-kind callback recorded when it was defined (a callee is defined before
; its caller, so no walk through callbacks is needed). NIL means unknown.
(mutual-recursion
 (defun fn2-cost-value (form world)
   (declare (xargs :verify-guards nil :measure (acl2-count form)))
   (cond ((natp form) form)
         ((symbolp form) (fn2-cost-constant form world))
         ((atom form) nil)
         ((eq (car form) :cost)
          (let ((row (fn2-decl-row (list :cost (cadr form)) world)))
            (if row
                (let ((f (fn2-decl-get (caddr form) row)))
                  (cond ((natp f) f) ((symbolp f) (fn2-cost-constant f world)) (t nil)))
              (let ((values (fn2-decl-get :cost-values (fn2-operation-row (cadr form) world))))
                (and (true-listp values) (equal (len values) 3)
                     (nth (fn2-cost-dimension-index (caddr form)) values))))))
         ((eq (car form) '+) (fn2-cost-sum (cdr form) world))
         ((eq (car form) 'max) (fn2-cost-max (cdr form) world))
         ((eq (car form) '*)
          (let ((v (fn2-cost-value (caddr form) world))) (and v (* (nfix (cadr form)) v))))
         (t nil)))
 (defun fn2-cost-sum (forms world)
   (declare (xargs :verify-guards nil :measure (acl2-count forms)))
   (if (atom forms) 0
     (let ((a (fn2-cost-value (car forms) world)) (b (fn2-cost-sum (cdr forms) world)))
       (and a b (+ a b)))))
 (defun fn2-cost-max (forms world)
   (declare (xargs :verify-guards nil :measure (acl2-count forms)))
   (if (atom forms) 0
     (let ((a (fn2-cost-value (car forms) world)) (b (fn2-cost-max (cdr forms) world)))
       (and a b (max a b))))))
(defun fn2-cost-values (cost world)
  (declare (xargs :verify-guards nil))
  (list (fn2-cost-value (or (fn2-arm-get :bytes cost) 0) world)
        (fn2-cost-value (or (fn2-arm-get :steps cost) 0) world)
        (fn2-cost-value (or (fn2-arm-get :descriptors cost) 0) world)))

; ----------------------------------------------------------------------
; defcost FN: the declared work of an outside call (constant bounds), the
; core children it may change, the acting row's fields it may write, and
; its resource effects in D0's effect forms (books/resources.lisp):
; (:acquire KINDS), (:acquire KINDS :for KIND), (:release KINDS),
; (:transfer KINDS :to KIND); :per-use when the kind is the caller's (its
; :uses entry then says which); :target (KIND FROM TO) when the call moves
; a row of another kind from phase FROM to TO.
; :answers (CODE ...) or t: the call's first result is an answer code (the
; whole set, or an open one); an arm's :do of it routes every answer
; (machine-arms.lisp).
; :child names the operation's body over the core children it touches
; (MACHINE-FORM 6.5 P2): the same formals with fn2-core replaced by those
; children, the same results with fn2-core replaced likewise.
(defconst *fn2-cost-keys* '(:bytes :steps :descriptors :tables :own-writes :effects :target :answers :faults :child :doc))
(defun fn2-cost-boundp (x)
  (declare (xargs :verify-guards nil))
  (or (natp x) (and (symbolp x) x (not (keywordp x)) (not (eq x t)))))
(defun fn2-arm-effect-shapep (effect)
  (declare (xargs :verify-guards nil))
  (and (true-listp effect) (consp (cdr effect))
       (member-eq (car effect) '(:acquire :release :transfer))
       (consp (cadr effect))
       (fn2-resource-kinds-known-p (cadr effect) *fn2-resource-order*)
       (let ((rest (cddr effect)))
         (case (car effect)
           (:acquire (or (null rest) (and (equal (len rest) 2) (eq (car rest) :for)
                                          (symbolp (cadr rest)) (cadr rest))))
           (:release (null rest))
           (otherwise (and (equal (len rest) 2) (eq (car rest) :to)
                           (symbolp (cadr rest)) (cadr rest)))))))
(defun fn2-arm-effects-shapep (effects)
  (declare (xargs :verify-guards nil))
  (if (atom effects) (null effects)
    (and (fn2-arm-effect-shapep (car effects)) (fn2-arm-effects-shapep (cdr effects)))))
;; A defcost's :tables names core children, or groups them by layer:
;; (:layers L ...) stands for every core child declared by a layer-L book
;; (a machine kind's table counts as its machine's layer). A lower layer's
;; declaration names an upper layer's tables this way, never by their names;
;; the group is resolved where the contract is checked, after every layer
;; registered its children.
(defun fn2-cost-tables-p (tables)
  (declare (xargs :verify-guards nil))
  (if (atom tables) (null tables)
    (and (or (and (symbolp (car tables)) (car tables) (not (keywordp (car tables))))
             (and (consp (car tables)) (eq (caar tables) :layers)
                  (consp (cdar tables)) (keyword-listp (cdar tables))))
         (fn2-cost-tables-p (cdr tables)))))
(defun fn2-cost-child-layer (row world)
  (declare (xargs :verify-guards nil))
  (if (eq (fn2-decl-get :order (cdr row)) :machine)
      (fn2-decl-get :layer (fn2-decl-row (list :machine (fn2-decl-get :stobj (cdr row))) world))
    (fn2-decl-get :layer (cdr row))))
(defun fn2-cost-layer-children (layers rows world)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (append (and (member-eq (fn2-cost-child-layer (car rows) world) layers) (list (caar rows)))
            (fn2-cost-layer-children layers (cdr rows) world))))
(defun fn2-cost-tables (tables world)
  (declare (xargs :verify-guards nil))
  (if (atom tables) nil
    (append (if (consp (car tables))
                (fn2-cost-layer-children (cdar tables) (fn2-decl-rows :core-child world) world)
              (list (car tables)))
            (fn2-cost-tables (cdr tables) world))))
(defun fn2-cost-problem (fn args)
  (declare (xargs :verify-guards nil))
  (cond ((not (and (symbolp fn) fn (not (keywordp fn))))
         (msg "defcost names a function, not ~x0." fn))
        ((not (fn2-arm-plistp args *fn2-cost-keys*))
         (msg "defcost ~x0: keys are ~v1." fn *fn2-cost-keys*))
        ((not (and (fn2-cost-boundp (or (fn2-arm-get :bytes args) 0))
                   (fn2-cost-boundp (or (fn2-arm-get :steps args) 0))
                   (fn2-cost-boundp (or (fn2-arm-get :descriptors args) 0))))
         (msg "defcost ~x0: a cost is a natural or a named constant." fn))
        ((not (and (fn2-cost-tables-p (fn2-arm-get :tables args))
                   (fn2-arm-namesp (fn2-arm-get :own-writes args))))
         (msg "defcost ~x0: :tables names core children or (:layers L ...) groups; :own-writes names fields." fn))
        ((not (or (eq (fn2-arm-get :effects args) :per-use)
                  (fn2-arm-effects-shapep (fn2-arm-get :effects args))))
         (msg "defcost ~x0: malformed resource effects ~x1." fn (fn2-arm-get :effects args)))
        ((not (or (null (fn2-arm-get :target args))
                  (and (true-listp (fn2-arm-get :target args))
                       (equal (len (fn2-arm-get :target args)) 3)
                       (fn2-arm-namesp (list (car (fn2-arm-get :target args)))))))
         (msg "defcost ~x0: :target is (KIND FROM TO)." fn))
        ((not (or (null (fn2-arm-get :answers args)) (eq (fn2-arm-get :answers args) t)
                  (and (keyword-listp (fn2-arm-get :answers args)) (consp (fn2-arm-get :answers args)))))
         (msg "defcost ~x0: :answers is t or a non-empty list of answer codes." fn))
        ((not (keyword-listp (fn2-arm-get :faults args)))
         (msg "defcost ~x0: :faults is a list of answer codes." fn))
        ((not (symbolp (fn2-arm-get :child args)))
         (msg "defcost ~x0: :child names a function." fn))
        ((not (stringp (fn2-arm-get :doc args)))
         (msg "defcost ~x0 needs a one-line :doc." fn))
        (t nil)))
(defmacro defcost (fn &rest args)
  (let ((problem (fn2-cost-problem fn args)))
    (if problem
        `(make-event (er soft 'defcost "~@0" ',problem))
      (fn2-declare (list :cost fn)
        (list :bytes (or (fn2-arm-get :bytes args) 0) :steps (or (fn2-arm-get :steps args) 0)
              :descriptors (or (fn2-arm-get :descriptors args) 0)
              :tables (fn2-arm-get :tables args) :own-writes (fn2-arm-get :own-writes args)
              :effects (fn2-arm-get :effects args) :target (fn2-arm-get :target args)
              :answers (fn2-arm-get :answers args) :faults (fn2-arm-get :faults args) :child (fn2-arm-get :child args)
              :doc (fn2-arm-get :doc args) :proof '(:owed))
        (list (list :function fn :at :callbacks)) nil))))

; ----------------------------------------------------------------------
; Arm contracts: (TAG FN :cost (...) :writes (...) :tables (...) :next (...)
; :uses (...) [:from (...)] [:language :unchecked]). TAG is a phase for a
; continuation and an event for an observation handler (:from then names
; the phases it observes in). A :uses entry is an operation name, or
; (NAME :effects EFFECTS) for a :per-use operation.
(defun fn2-arm-use-name (use)
  (declare (xargs :verify-guards nil))
  (if (consp use) (car use) use))
(defun fn2-arm-use-names (uses)
  (declare (xargs :verify-guards nil))
  (if (atom uses) nil
    (cons (fn2-arm-use-name (car uses)) (fn2-arm-use-names (cdr uses)))))
(defun fn2-arm-usesp (uses)
  (declare (xargs :verify-guards nil))
  (if (atom uses) (null uses)
    (and (or (and (symbolp (car uses)) (car uses) (not (keywordp (car uses))))
             (and (true-listp (car uses)) (equal (len (car uses)) 3)
                  (symbolp (caar uses)) (caar uses) (eq (cadar uses) :effects)
                  (fn2-arm-effects-shapep (caddar uses))))
         (fn2-arm-usesp (cdr uses)))))
(defun fn2-arm-contract-problem (name entry states fields observationp)
  (declare (xargs :verify-guards nil))
  (let ((c (and (consp entry) (consp (cdr entry)) (cddr entry))))
    (cond
     ((not (and (consp entry) (consp (cdr entry)) (symbolp (cadr entry)) (cadr entry)))
      (msg "~x0: malformed arm ~x1." name entry))
     ((not (and (fn2-arm-plistp c (if observationp (cons :from *fn2-arm-keys*) *fn2-arm-keys*))
                (fn2-arm-get :cost c) (member-eq :writes c) (member-eq :next c)
                (member-eq :uses c)))
      (msg "~x0: arm ~x1 needs its contract (:cost :writes :next :uses; optional :tables ~
            :language~s2); the bare (TAG FN) form is retired." name (car entry)
           (if observationp " :from" "")))
     ((not (fn2-cost-plistp (fn2-arm-get :cost c)))
      (msg "~x0: arm ~x1's :cost ~x2 is not a cost form over constants and declared calls."
           name (car entry) (fn2-arm-get :cost c)))
     ((not (and (fn2-arm-namesp (fn2-arm-get :writes c))
                (fn2-arm-subsetp (fn2-arm-get :writes c) fields)))
      (msg "~x0: arm ~x1 writes ~x2, which are not all its own fields ~x3 (phase moves are :next)."
           name (car entry) (fn2-arm-get :writes c) fields))
     ((not (and (true-listp (fn2-arm-get :next c)) (fn2-arm-subsetp (fn2-arm-get :next c) states)))
      (msg "~x0: arm ~x1's :next ~x2 names phases outside ~x3." name (car entry) (fn2-arm-get :next c) states))
     ((not (and (true-listp (fn2-arm-get :from c)) (fn2-arm-subsetp (fn2-arm-get :from c) states)))
      (msg "~x0: arm ~x1's :from ~x2 names phases outside ~x3." name (car entry) (fn2-arm-get :from c) states))
     ((not (fn2-arm-usesp (fn2-arm-get :uses c)))
      (msg "~x0: arm ~x1's :uses ~x2 is malformed." name (car entry) (fn2-arm-get :uses c)))
     ((not (fn2-arm-namesp (fn2-arm-get :tables c)))
      (msg "~x0: arm ~x1's :tables must name core children." name (car entry)))
     ((not (member-eq (fn2-arm-get :language c) '(nil :unchecked)))
      (msg "~x0: arm ~x1's :language is :unchecked or absent." name (car entry)))
     ((not (subsetp-eq (fn2-cost-cites-list (list (fn2-arm-get :bytes (fn2-arm-get :cost c))
                                                  (fn2-arm-get :steps (fn2-arm-get :cost c))
                                                  (fn2-arm-get :descriptors (fn2-arm-get :cost c))))
                       (fn2-arm-use-names (fn2-arm-get :uses c))))
      (msg "~x0: arm ~x1's cost cites calls outside its :uses." name (car entry)))
     (t nil))))
(defun fn2-arm-contracts-problem (name entries states fields observationp)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (or (fn2-arm-contract-problem name (car entries) states fields observationp)
        (fn2-arm-contracts-problem name (cdr entries) states fields observationp))))
(defun fn2-arm-holds-problem-syntax (name holds states)
  (declare (xargs :verify-guards nil))
  (cond ((atom holds) (and holds (msg "~x0: :holds is a list of (PHASE KIND ...)." name)))
        ((not (and (consp (car holds)) (member-eq (caar holds) states)
                   (true-listp (cdar holds))
                   (or (equal (cdar holds) '(:retained))
                       (and (fn2-resource-kinds-known-p (cdar holds) *fn2-resource-order*)
                            (fn2-resource-ascending-p (cdar holds) *fn2-resource-order*)))
                   (not (assoc-eq (caar holds) (cdr holds)))))
         (msg "~x0: :holds entry ~x1 must be a phase with D0 resource kinds in rank order, or ~
               (PHASE :retained), once." name (car holds)))
        (t (fn2-arm-holds-problem-syntax name (cdr holds) states))))
(defun fn2-arm-holds-of (phase holds)
  (declare (xargs :verify-guards nil))
  (let ((entry (and (alistp holds) (assoc-eq phase holds)))) (and (consp entry) (cdr entry))))
; A retained phase (PHASE :retained) acquires nothing on entry and keeps
; exactly what the entering path held: its holds are the path's, not a
; static set. D0 checks it per path only (fn2-arm-paths-problem).
(defun fn2-arm-retained-p (phase holds)
  (declare (xargs :verify-guards nil))
  (equal (fn2-arm-holds-of phase holds) '(:retained)))
(defun fn2-arm-retained-phases (holds)
  (declare (xargs :verify-guards nil))
  (if (atom holds) nil
    (append (and (consp (car holds)) (equal (cdar holds) '(:retained)) (list (caar holds)))
            (fn2-arm-retained-phases (cdr holds)))))

; ----------------------------------------------------------------------
; The restricted arm language (decision 2), checked over the submitted body
; of a callback whose contract claims completeness. ENV is a plist:
;   :kind K :put K-PUT-CORE :rows ((ROW-VAR . FIELD) ...) :phases ((CONST . PHASE) ...)
;   :writes :next :uses (names) :tables :world
; Accepted: variables and constants; quote; let, let*, b* (symbol and mv
; binders), mv-let; if, cond, and, or, mv, case; the scalar primitives;
; (fn2-call CALLEE ...) of a same-kind callback in :uses; the kind's PUT-CORE
; on its own row (id) for declared fields, and phase only to a constant in
; :next; fn2-machine-result and fn2-machine-with-work; calls of declared
; operations in :uses. A row variable read after its field was written on
; the same path is a stale read and refused.
(defun fn2-arm-env (key env) (declare (xargs :verify-guards nil)) (fn2-arm-get key env))
(defun fn2-arm-callee-contract (callee env)
  (declare (xargs :verify-guards nil))
  (let ((row (fn2-operation-row callee (fn2-arm-env :world env))))
    (and (equal (fn2-decl-get :owner row) (list :machine (fn2-arm-env :kind env)))
         (fn2-decl-get :contract row))))
(defun fn2-arm-phase-constants (form phases)
  (declare (xargs :verify-guards nil))
  (cond ((symbolp form) (let ((p (assoc-eq form phases))) (and p (list (cdr p)))))
        ((atom form) nil)
        ((eq (car form) 'quote) nil)
        (t (append (fn2-arm-phase-constants (car form) phases)
                   (fn2-arm-phase-constants (cdr form) phases)))))
(defun fn2-arm-phase-pairs (pairs)
  (declare (xargs :verify-guards nil))
  (if (atom pairs) nil
    (if (and (consp (car pairs)) (eq (caar pairs) 'phase))
        (cons (car pairs) (fn2-arm-phase-pairs (cdr pairs)))
      (fn2-arm-phase-pairs (cdr pairs)))))
(defun fn2-arm-put-fields (pairs)
  (declare (xargs :verify-guards nil))
  (if (atom pairs) nil
    (if (and (consp (car pairs)) (not (eq (caar pairs) 'phase)))
        (cons (caar pairs) (fn2-arm-put-fields (cdr pairs)))
      (fn2-arm-put-fields (cdr pairs)))))
; Every own field FORM may write, syntactically: an over-approximation.
(defun fn2-arm-writes-of (form env)
  (declare (xargs :verify-guards nil))
  (cond ((atom form) nil)
        ((eq (car form) 'quote) nil)
        ((eq (car form) (fn2-arm-env :put env))
         (append (fn2-arm-put-fields (cddr form)) (fn2-arm-writes-of (cddr form) env)))
        ((eq (car form) 'fn2-call)
         (append (fn2-arm-get :writes (fn2-arm-callee-contract (cadr form) env))
                 (fn2-arm-writes-of (cddr form) env)))
        ((and (symbolp (car form)) (member-eq (car form) (fn2-arm-env :uses env)))
         (append (fn2-decl-get :own-writes (fn2-decl-row (list :cost (car form)) (fn2-arm-env :world env)))
                 (fn2-arm-writes-of (cdr form) env)))
        (t (append (fn2-arm-writes-of (car form) env) (fn2-arm-writes-of (cdr form) env)))))
(defun fn2-arm-binds-core (vars) (declare (xargs :verify-guards nil)) (member-eq 'fn2-core vars))
(defun fn2-arm-strip-declares (forms)
  (declare (xargs :verify-guards nil))
  (if (and (consp forms) (consp (car forms)) (eq (caar forms) 'declare))
      (fn2-arm-strip-declares (cdr forms)) forms))
(mutual-recursion
 (defun fn2-arm-walk (form written env fuel)
   (declare (xargs :verify-guards nil :measure (nfix fuel)))
   (if (zp fuel) (msg "is too deeply nested to check.")
   (cond
    ((symbolp form)
     (let ((field (cdr (assoc-eq form (fn2-arm-env :rows env)))))
       (and field (member-eq field written)
            (msg "reads ~x0 after writing ~x1 on the same path (a stale row read; read it before the write)."
                 form field))))
    ((atom form) nil)
    ((eq (car form) 'quote) nil)
    ((not (symbolp (car form))) (msg "applies a non-symbol ~x0." (car form)))
    ((member-eq (car form) '(let let*))
     (if (not (and (true-listp form) (doublet-listp (cadr form))))
         (msg "has a malformed binding ~x0." form)
       (if (eq (car form) 'let)
           (or (fn2-arm-walk-bindings (cadr form) written env (1- fuel))
               (fn2-arm-walk-list (fn2-arm-strip-declares (cddr form))
                 (if (fn2-arm-binds-core (strip-cars (cadr form)))
                     (append (fn2-arm-writes-of (strip-cadrs (cadr form)) env) written) written) env (1- fuel)))
         (fn2-arm-walk-sequential (cadr form) (fn2-arm-strip-declares (cddr form)) written env (1- fuel)))))
    ((eq (car form) 'b*)
     (if (not (true-listp (cadr form))) (msg "has a malformed b* ~x0." form)
       (fn2-arm-walk-bstar (cadr form) (cddr form) written env (1- fuel))))
    ((eq (car form) 'mv-let)
     (if (not (and (true-listp form) (symbol-listp (cadr form)) (consp (cddr form))))
         (msg "has a malformed mv-let ~x0." form)
       (or (fn2-arm-walk (caddr form) written env (1- fuel))
           (fn2-arm-walk-list (fn2-arm-strip-declares (cdddr form))
             (if (fn2-arm-binds-core (cadr form))
                 (append (fn2-arm-writes-of (caddr form) env) written) written) env (1- fuel)))))
    ((eq (car form) 'cond) (fn2-arm-walk-clauses (cdr form) written env (1- fuel)))
    ((eq (car form) 'case)
     (or (fn2-arm-walk (cadr form) written env (1- fuel)) (fn2-arm-walk-case (cddr form) written env (1- fuel))))
    ((member-eq (car form) *fn2-arm-control*) (fn2-arm-walk-list (cdr form) written env (1- fuel)))
    ((member-eq (car form) *fn2-arm-primitives*) (fn2-arm-walk-list (cdr form) written env (1- fuel)))
    ((member-eq (car form) '(fn2-machine-result fn2-machine-with-work))
     (fn2-arm-walk-list (cdr form) written env (1- fuel)))
    ((eq (car form) 'fn2-call)
     (let ((contract (fn2-arm-callee-contract (cadr form) env)))
       (cond ((not (member-eq (cadr form) (fn2-arm-env :uses env)))
              (msg "forwards to ~x0, which is not in its :uses." (cadr form)))
             ((not contract)
              (msg "forwards to ~x0, which is not a contracted callback of ~x1." (cadr form)
                   (fn2-arm-env :kind env)))
             ((not (fn2-arm-subsetp (fn2-arm-get :writes contract) (fn2-arm-env :writes env)))
              (msg "forwards to ~x0, which writes ~x1 beyond its :writes." (cadr form)
                   (fn2-arm-minus (fn2-arm-get :writes contract) (fn2-arm-env :writes env))))
             ((not (fn2-arm-subsetp (fn2-arm-get :next contract) (fn2-arm-env :next env)))
              (msg "forwards to ~x0, which may move to ~x1 beyond its :next." (cadr form)
                   (fn2-arm-minus (fn2-arm-get :next contract) (fn2-arm-env :next env))))
             ((not (fn2-arm-subsetp (fn2-arm-get :tables contract) (fn2-arm-env :tables env)))
              (msg "forwards to ~x0, which changes ~x1 beyond its :tables." (cadr form)
                   (fn2-arm-minus (fn2-arm-get :tables contract) (fn2-arm-env :tables env))))
             (t (fn2-arm-walk-list (cddr form) written env (1- fuel))))))
    ((eq (car form) (fn2-arm-env :put env))
     (cond ((not (eq (cadr form) 'id))
            (msg "writes another row of its kind (~x0); its own row is id." (cadr form)))
           ((not (fn2-arm-subsetp (fn2-arm-put-fields (cddr form)) (fn2-arm-env :writes env)))
            (msg "writes ~x0, outside its :writes ~x1."
                 (fn2-arm-minus (fn2-arm-put-fields (cddr form)) (fn2-arm-env :writes env))
                 (fn2-arm-env :writes env)))
           ((not (fn2-arm-subsetp (fn2-arm-phase-constants
                                   (strip-cadrs (fn2-arm-phase-pairs (cddr form))) (fn2-arm-env :phases env))
                                  (fn2-arm-env :next env)))
            (msg "moves to ~x0, outside its :next ~x1."
                 (fn2-arm-minus (fn2-arm-phase-constants
                                 (strip-cadrs (fn2-arm-phase-pairs (cddr form))) (fn2-arm-env :phases env))
                                (fn2-arm-env :next env))
                 (fn2-arm-env :next env)))
           (t (fn2-arm-walk-bindings (cddr form) written env (1- fuel)))))
    ((member-eq (car form) (fn2-arm-env :uses env))
     (let ((row (fn2-decl-row (list :cost (car form)) (fn2-arm-env :world env))))
       (cond ((not row)
              (msg "calls ~x0, which has no defcost (a helper hides its effects)." (car form)))
             ((not (fn2-arm-subsetp (fn2-decl-get :own-writes row) (fn2-arm-env :writes env)))
              (msg "calls ~x0, which writes ~x1 of its row beyond its :writes." (car form)
                   (fn2-arm-minus (fn2-decl-get :own-writes row) (fn2-arm-env :writes env))))
             ((not (fn2-arm-subsetp (fn2-cost-tables (fn2-decl-get :tables row) (fn2-arm-env :world env))
                                    (fn2-arm-env :tables env)))
              (msg "calls ~x0, which changes ~x1 beyond its :tables." (car form)
                   (fn2-arm-minus (fn2-cost-tables (fn2-decl-get :tables row) (fn2-arm-env :world env))
                                  (fn2-arm-env :tables env))))
             (t (fn2-arm-walk-list (cdr form) written env (1- fuel))))))
    (t (msg "calls ~x0, which is neither in its :uses nor in the arm language." (car form))))))
 (defun fn2-arm-walk-list (forms written env fuel)
   (declare (xargs :verify-guards nil :measure (nfix fuel)))
   (if (zp fuel) (msg "is too deeply nested to check.")
   (if (atom forms) nil
     (or (fn2-arm-walk (car forms) written env (1- fuel)) (fn2-arm-walk-list (cdr forms) written env (1- fuel))))))
 (defun fn2-arm-walk-bindings (bindings written env fuel)
   (declare (xargs :verify-guards nil :measure (nfix fuel)))
   (if (zp fuel) (msg "is too deeply nested to check.")
   (if (atom bindings) nil
     (or (and (consp (car bindings)) (consp (cdar bindings))
              (fn2-arm-walk (cadar bindings) written env (1- fuel)))
         (fn2-arm-walk-bindings (cdr bindings) written env (1- fuel))))))
 (defun fn2-arm-walk-sequential (bindings body written env fuel)
   (declare (xargs :verify-guards nil :measure (nfix fuel)))
   (if (zp fuel) (msg "is too deeply nested to check.")
   (if (atom bindings) (fn2-arm-walk-list body written env (1- fuel))
     (or (fn2-arm-walk (cadar bindings) written env (1- fuel))
         (fn2-arm-walk-sequential (cdr bindings) body
           (if (eq (caar bindings) 'fn2-core) (append (fn2-arm-writes-of (cadar bindings) env) written) written)
           env (1- fuel))))))
 (defun fn2-arm-walk-bstar (bindings body written env fuel)
   (declare (xargs :verify-guards nil :measure (nfix fuel)))
   (if (zp fuel) (msg "is too deeply nested to check.")
   (cond ((atom bindings) (fn2-arm-walk-list body written env (1- fuel)))
         ((not (and (consp (car bindings)) (consp (cdar bindings))))
          (msg "has an unsupported b* binder ~x0." (car bindings)))
         (t (let ((vars (cond ((symbolp (caar bindings)) (list (caar bindings)))
                              ((and (consp (caar bindings)) (eq (caaar bindings) 'mv)) (cdaar bindings))
                              (t :bad))))
              (if (eq vars :bad) (msg "has an unsupported b* binder ~x0." (car bindings))
                (or (fn2-arm-walk (cadar bindings) written env (1- fuel))
                    (fn2-arm-walk-bstar (cdr bindings) body
                      (if (fn2-arm-binds-core vars)
                          (append (fn2-arm-writes-of (cadar bindings) env) written) written)
                      env (1- fuel)))))))))
 (defun fn2-arm-walk-clauses (clauses written env fuel)
   (declare (xargs :verify-guards nil :measure (nfix fuel)))
   (if (zp fuel) (msg "is too deeply nested to check.")
   (if (atom clauses) nil
     (or (fn2-arm-walk-list (and (true-listp (car clauses)) (car clauses)) written env (1- fuel))
         (fn2-arm-walk-clauses (cdr clauses) written env (1- fuel))))))
 (defun fn2-arm-walk-case (clauses written env fuel)
   (declare (xargs :verify-guards nil :measure (nfix fuel)))
   (if (zp fuel) (msg "is too deeply nested to check.")
   (if (atom clauses) nil
     (or (and (consp (car clauses)) (fn2-arm-walk-list (cdar clauses) written env (1- fuel)))
         (fn2-arm-walk-case (cdr clauses) written env (1- fuel)))))))

; ----------------------------------------------------------------------

; Resource effects of an arm (HIGHER-STRUCTURES entry 2: in a conservative
; program what a row holds is a function of its phase). For every source
; phase S and successor S', the arm's operations must acquire exactly
; holds(S') - holds(S) and release (or transfer) exactly holds(S) - holds(S'):
; every needed move has a declared effect, and every declared own-row effect
; is some move. Effects on behalf of another row must move that row between
; the phases its operation's :target names.
; A forwarded callback's effects are those of the operations it uses
; (FUEL bounds the walk; callees are defined before their callers).
(mutual-recursion
 (defun fn2-arm-use-effects-fuel (use fuel world)
   (declare (xargs :verify-guards nil :measure (list (nfix fuel) 1) :well-founded-relation l<))
   (if (consp use) (fn2-arm-get :effects (cdr use))
     (let ((row (fn2-decl-row (list :cost use) world)))
       (if row (fn2-decl-get :effects row)
         (if (zp fuel) '((:fuel-exhausted))
           (fn2-arm-uses-effects-fuel
            (fn2-arm-get :uses (fn2-decl-get :contract (fn2-operation-row use world)))
            (1- fuel) world))))))
 (defun fn2-arm-uses-effects-fuel (uses fuel world)
   (declare (xargs :verify-guards nil :measure (list (nfix fuel) (+ 2 (acl2-count uses)))
                   :well-founded-relation l<))
   (if (atom uses) nil
     (let ((e (fn2-arm-use-effects-fuel (car uses) fuel world)))
       (append (if (eq e :per-use) nil e) (fn2-arm-uses-effects-fuel (cdr uses) fuel world))))))
(defun fn2-arm-use-effects (use world)
  (declare (xargs :verify-guards nil))
  (fn2-arm-use-effects-fuel use 8 world))
(defun fn2-arm-effect-kinds (effects ops for)
  ; Kinds of EFFECTS whose operator is in OPS: FOR nil = the acting row's
  ; own effects (no :for / :to), else effects naming FOR as target.
  (declare (xargs :verify-guards nil))
  (if (atom effects) nil
    (let* ((e (car effects)) (target (fn2-arm-get (if (eq (car e) :transfer) :to :for) (cddr e))))
      (append (and (member-eq (car e) ops) (if for (eq target for) (not target)) (cadr e))
              (fn2-arm-effect-kinds (cdr effects) ops for)))))
(defun fn2-arm-uses-effects (uses world)
  (declare (xargs :verify-guards nil))
  (fn2-arm-uses-effects-fuel uses 8 world))
(defun fn2-arm-per-use-missing (uses world)
  (declare (xargs :verify-guards nil))
  (if (atom uses) nil
    (if (eq (fn2-arm-use-effects (car uses) world) :per-use) (fn2-arm-use-name (car uses))
      (fn2-arm-per-use-missing (cdr uses) world))))
(defun fn2-arm-moves-from (s nexts holds)
  (declare (xargs :verify-guards nil))
  (if (atom nexts) nil
    (let ((h (fn2-arm-holds-of s holds)) (h1 (fn2-arm-holds-of (car nexts) holds)))
      (cons (list s (car nexts) (fn2-arm-minus (fn2-arm-mminus h1 h) *fn2-arm-transient-kinds*)
                  (fn2-arm-mminus h h1))
            (fn2-arm-moves-from s (cdr nexts) holds)))))
(defun fn2-arm-moves (sources nexts holds)
  ; ((S S' acquired released) ...) over every source and successor
  (declare (xargs :verify-guards nil))
  (if (atom sources) nil
    (append (fn2-arm-moves-from (car sources) nexts holds)
            (fn2-arm-moves (cdr sources) nexts holds))))
(defun fn2-arm-moves-problem (moves acquires releases)
  (declare (xargs :verify-guards nil))
  (cond ((atom moves) nil)
        ((not (fn2-arm-msubsetp (caddar moves) acquires))
         (msg "moves ~x0 -> ~x1 without acquiring ~x2." (caar moves) (cadar moves)
              (fn2-arm-mminus (caddar moves) acquires)))
        ((not (fn2-arm-msubsetp (car (cdddar moves)) releases))
         (msg "moves ~x0 -> ~x1 without releasing ~x2." (caar moves) (cadar moves)
              (fn2-arm-mminus (car (cdddar moves)) releases)))
        (t (fn2-arm-moves-problem (cdr moves) acquires releases))))
(defun fn2-arm-moved-kinds (moves acquiredp)
  (declare (xargs :verify-guards nil))
  (if (atom moves) nil
    (append (if acquiredp (caddar moves) (car (cdddar moves)))
            (fn2-arm-moved-kinds (cdr moves) acquiredp))))
(defun fn2-arm-target-problem (uses world)
  (declare (xargs :verify-guards nil))
  (if (atom uses) nil
    (let* ((name (fn2-arm-use-name (car uses)))
           (row (fn2-decl-row (list :cost name) world))
           (target (fn2-decl-get :target row))
           (effects (fn2-arm-use-effects (car uses) world)))
      (or (and target
               (let ((holds (fn2-decl-get :holds (fn2-decl-row (list :machine (car target)) world))))
                 (or (fn2-arm-retained-p (cadr target) holds) (fn2-arm-retained-p (caddr target) holds)))
               (msg "uses ~x0, which moves a ~x1 row ~x2 -> ~x3 through a retained phase on its behalf; ~
                     a retained phase's holds are its own row's path's." name (car target) (cadr target) (caddr target)))
          (and target (not (eq effects :per-use))
               (let* ((kind (car target))
                      (holds (fn2-decl-get :holds (fn2-decl-row (list :machine kind) world)))
                      (gain (fn2-arm-minus (fn2-arm-minus (fn2-arm-holds-of (caddr target) holds)
                                                          (fn2-arm-holds-of (cadr target) holds))
                                           *fn2-arm-transient-kinds*))
                      (given (append (fn2-arm-effect-kinds effects '(:transfer :acquire) kind))))
                 (and (not (and (fn2-arm-subsetp gain given) (fn2-arm-subsetp given gain)))
                      (msg "uses ~x0, which gives a ~x1 row ~x2 while moving it ~x3 -> ~x4 needs ~x5."
                           name kind given (cadr target) (caddr target) gain))))
          (fn2-arm-target-problem (cdr uses) world)))))
(defun fn2-arm-transfer-kinds (effects)
  ; the kinds every :transfer gives up, whatever its receiver
  (declare (xargs :verify-guards nil))
  (if (atom effects) nil
    (append (and (consp (car effects)) (eq (caar effects) :transfer) (fn2-arm-get :to (cddar effects)) (cadar effects))
            (fn2-arm-transfer-kinds (cdr effects)))))
;; TRANSFERSP (a path's check, G3 F14): a transfer to another row is the
;; giver's release too
(defun fn2-arm-resource-problem-1 (sources nexts holds uses world transfersp)
  (declare (xargs :verify-guards nil))
  (let* ((effects (fn2-arm-uses-effects uses world))
         (acquires (fn2-arm-minus (fn2-arm-effect-kinds effects '(:acquire) nil) *fn2-arm-transient-kinds*))
         (releases (append (fn2-arm-effect-kinds effects '(:release :transfer) nil)
                           (and transfersp (fn2-arm-transfer-kinds effects))))
         (moves (fn2-arm-moves sources nexts holds)))
    (cond ((assoc-eq :fuel-exhausted effects)
           (msg "exhausts effect-expansion fuel in :uses (cyclic or too-deep :uses chain)."))
          ((fn2-arm-per-use-missing uses world)
           (msg "uses ~x0 without naming its per-use effect: write (~x0 :effects ...)."
                (fn2-arm-per-use-missing uses world)))
          ((fn2-arm-moves-problem moves acquires releases))
          ((if (or transfersp (equal (len moves) 1))
               (not (fn2-arm-msubsetp acquires (fn2-arm-moved-kinds moves t)))
             (not (fn2-arm-subsetp acquires (fn2-arm-moved-kinds moves t))))
           (msg "acquires ~x0, which no move to a declared successor holds (an undeclared resource effect)."
                (fn2-arm-mminus acquires (fn2-arm-moved-kinds moves t))))
          ((if (or transfersp (equal (len moves) 1))
               (not (fn2-arm-msubsetp releases (fn2-arm-moved-kinds moves nil)))
             (not (fn2-arm-subsetp releases (fn2-arm-moved-kinds moves nil))))
           (msg "releases ~x0, which no move to a declared successor gives up (an undeclared resource effect)."
                (fn2-arm-mminus releases (fn2-arm-moved-kinds moves nil))))
          (t (fn2-arm-target-problem uses world)))))
(defun fn2-arm-resource-problem (sources nexts holds uses world)
  (declare (xargs :verify-guards nil))
  (fn2-arm-resource-problem-1 sources nexts holds uses world nil))
; ----------------------------------------------------------------------
; Per-path holds (G3, D F14). A generated arm's contract lists its :paths,
; (SOURCES ENDS USES ENTRY SETS STOP) (machine-arms.lisp), and D0 checks each
; path on its own: from each phase it can start in to each it can end in,
; its own calls acquire exactly what the move gains and release exactly what
; it gives up. A conditional hold (PHASE K F V ...) of WHILE holds K in PHASE
; while the enum field F is one of V; the path's tests fix F at entry (else
; every value of DOMS is checked) and its writes fix F at its end. A path
; that stops the core moves nothing.
(defun fn2-arm-while-holds (phase vals while)
  ; the kinds WHILE holds in PHASE under the field values VALS ((F . V) ...)
  (declare (xargs :verify-guards nil))
  (if (atom while) nil
    (let ((w (car while)))
      (append (and (consp w) (eq (car w) phase) (consp (cdr w)) (consp (cddr w))
                   (member-eq (cdr (assoc-eq (caddr w) vals)) (cdddr w)) (list (cadr w)))
              (fn2-arm-while-holds phase vals (cdr while))))))
(defun fn2-arm-assign-cons (f v rests)
  (declare (xargs :verify-guards nil))
  (if (atom rests) nil (cons (acons f v (car rests)) (fn2-arm-assign-cons f v (cdr rests)))))
(defun fn2-arm-assign-each (f vs rests)
  (declare (xargs :verify-guards nil))
  (if (atom vs) nil (append (fn2-arm-assign-cons f (car vs) rests) (fn2-arm-assign-each f (cdr vs) rests))))
(defun fn2-arm-assignments (doms)
  ; every ((F . V) ...) choosing one V of each (F V ...) in DOMS
  (declare (xargs :verify-guards nil))
  (if (atom doms) (list nil)
    (fn2-arm-assign-each (caar doms) (cdar doms) (fn2-arm-assignments (cdr doms)))))
(defun fn2-arm-entry-doms (doms entry)
  (declare (xargs :verify-guards nil))
  (if (atom doms) nil
    (cons (or (assoc-eq (caar doms) entry) (car doms)) (fn2-arm-entry-doms (cdr doms) entry))))
(defun fn2-arm-end-doms (doms sets a)
  ; each field at the path's end: its write, any value (:any), or its entry value in A
  (declare (xargs :verify-guards nil))
  (if (atom doms) nil
    (let* ((f (caar doms)) (s (assoc-eq f sets)))
      (cons (cond ((null s) (list f (cdr (assoc-eq f a))))
                  ((eq (cdr s) :any) (car doms))
                  (t (list f (cdr s))))
            (fn2-arm-end-doms (cdr doms) sets a)))))
(defun fn2-arm-holds-under (phase a holds while)
  (declare (xargs :verify-guards nil))
  (append (fn2-arm-holds-of phase holds) (fn2-arm-while-holds phase a while)))
(defun fn2-arm-path-end-problem (s srch e a endas uses holds while world)
  ; the move S -> E under every end assignment; a retained E keeps SRCH
  (declare (xargs :verify-guards nil))
  (if (atom endas) nil
    (let ((p (fn2-arm-resource-problem-1 '(:path-from) '(:path-to)
                                         (list (cons :path-from srch)
                                               (cons :path-to (if (fn2-arm-retained-p e holds) srch
                                                                (fn2-arm-holds-under e (car endas) holds while))))
                                         uses world t)))
      (if p (msg "on a path ~x0 -> ~x1~@2 calling ~x3: ~@4" s e
                 (if a (msg " (at entry ~x0, at its end ~x1)" a (car endas)) "")
                 (fn2-arm-use-names uses) p)
        (fn2-arm-path-end-problem s srch e a (cdr endas) uses holds while world)))))
(defun fn2-arm-path-ends-problem-all (s srch ends a endas uses holds while world)
  (declare (xargs :verify-guards nil))
  (if (atom ends) nil
    (or (fn2-arm-path-end-problem s srch (car ends) a endas uses holds while world)
        (fn2-arm-path-ends-problem-all s srch (cdr ends) a endas uses holds while world))))
; RET ((R SET ...) ...): each retained phase R with every set a path entering
; it can hold (fn2-machine-retained-sets); a path from R is checked from each.
(defun fn2-arm-start-holds (s a holds while ret)
  (declare (xargs :verify-guards nil))
  (if (fn2-arm-retained-p s holds) (or (cdr (assoc-eq s ret)) (list nil))
    (list (fn2-arm-holds-under s a holds while))))
(defun fn2-arm-path-starts-problem (s srchs ends a endas uses holds while world)
  (declare (xargs :verify-guards nil))
  (if (atom srchs) nil
    (let ((p (fn2-arm-path-ends-problem-all s (car srchs) ends a endas uses holds while world)))
      (if p (if (fn2-arm-retained-p s holds) (msg "~@0 (retained ~x1, entered holding ~x2)" p s (car srchs)) p)
        (fn2-arm-path-starts-problem s (cdr srchs) ends a endas uses holds while world)))))
(defun fn2-arm-path-entries-problem (s as path doms holds while ret world)
  (declare (xargs :verify-guards nil))
  (if (atom as) nil
    (let* ((a (car as)) (ends (if (eq (cadr path) :stay) (list s) (cadr path)))
           (endas (fn2-arm-assignments (fn2-arm-end-doms doms (nth 4 path) a))))
      (or (fn2-arm-path-starts-problem s (fn2-arm-start-holds s a holds while ret) ends a endas (caddr path)
                                       holds while world)
          (fn2-arm-path-entries-problem s (cdr as) path doms holds while ret world)))))
(defun fn2-arm-path-sources-problem (sources path doms holds while ret world)
  (declare (xargs :verify-guards nil))
  (if (atom sources) nil
    (or (fn2-arm-path-entries-problem (car sources) (fn2-arm-assignments (fn2-arm-entry-doms doms (nth 3 path)))
                                      path doms holds while ret world)
        (fn2-arm-path-sources-problem (cdr sources) path doms holds while ret world))))
(defun fn2-arm-paths-problems (sources paths doms holds while ret world)
  (declare (xargs :verify-guards nil))
  (if (atom paths) nil
    (let ((path (car paths)))
      (cons (and (not (nth 5 path))
                 (fn2-arm-path-sources-problem (if (eq (car path) :any) sources (intersection-eq (car path) sources))
                                               path doms holds while ret world))
            (fn2-arm-paths-problems sources (cdr paths) doms holds while ret world)))))
(defun fn2-arm-paths-problem (sources paths doms holds while ret world)
  ; SOURCES the arm's phases, DOMS ((F V ...) ...) the conditional fields' values
  (declare (xargs :verify-guards nil))
  ; every path's problem (fn2-arm-problems), not only the first path's
  (fn2-arm-problems "" (fn2-arm-paths-problems sources paths doms holds while ret world)))
; The same declarations as D0's effect rows, for D0's checker.
;; One row per operation reached (through forwarded callbacks), each from
;; the holds of the arm's source phase: alternative paths are separate rows.
(defun fn2-arm-step-held (held effects)
  ; HELD after EFFECTS: accumulate own non-transient acquires along the path
  (declare (xargs :verify-guards nil))
  (union-eq held (fn2-arm-minus (fn2-arm-effect-kinds effects '(:acquire) nil) *fn2-arm-transient-kinds*)))
(defun fn2-arm-effect-rows-seq (kind source uses held fuel world)
  ; (mv rows held-after)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (if (atom uses) (mv nil held)
    (if (zp fuel)
        (mv (list (list (list (list kind source) (fn2-arm-use-name (car uses)))
                        :holds-before held :effects '((:fuel-exhausted))))
            held)
      (let* ((use (car uses)) (name (fn2-arm-use-name use))
             (callee (and (atom use) (not (fn2-decl-row (list :cost name) world))
                          (fn2-decl-get :contract (fn2-operation-row name world)))))
        (mv-let (rows1 held1)
          (if callee
              (fn2-arm-effect-rows-seq kind source (fn2-arm-get :uses callee) held (1- fuel) world)
            (let ((e (fn2-arm-use-effects use world)))
              (mv (and (consp e)
                       (list (list (list (list kind source) name)
                                   :holds-before held :effects e)))
                  (if (consp e) (fn2-arm-step-held held e) held))))
          (mv-let (rows2 held2)
            (fn2-arm-effect-rows-seq kind source (cdr uses) held1 (1- fuel) world)
            (mv (append rows1 rows2) held2)))))))
(defun fn2-arm-effect-rows-from (kind source uses holds fuel world)
  (declare (xargs :verify-guards nil))
  (mv-let (rows held)
    (fn2-arm-effect-rows-seq kind source uses (fn2-arm-holds-of source holds) fuel world)
    (declare (ignore held))
    rows))
(defun fn2-arm-effect-rows (kind sources uses holds world)
  (declare (xargs :verify-guards nil))
  (if (atom sources) nil
    (append (fn2-arm-effect-rows-from kind (car sources) uses holds 256 world)
            (fn2-arm-effect-rows kind (cdr sources) uses holds world))))
(defun fn2-arm-path-starts-effect-rows (kind s srchs uses world)
  (declare (xargs :verify-guards nil))
  (if (atom srchs) nil
    (mv-let (rows held)
      (fn2-arm-effect-rows-seq kind s uses (car srchs) 256 world)
      (declare (ignore held))
      (append rows (fn2-arm-path-starts-effect-rows kind s (cdr srchs) uses world)))))
(defun fn2-arm-path-entries-effect-rows (kind s as uses holds while ret world)
  (declare (xargs :verify-guards nil))
  (if (atom as) nil
    (append (fn2-arm-path-starts-effect-rows kind s (fn2-arm-start-holds s (car as) holds while ret) uses world)
            (fn2-arm-path-entries-effect-rows kind s (cdr as) uses holds while ret world))))
(defun fn2-arm-path-sources-effect-rows (kind sources path doms holds while ret world)
  (declare (xargs :verify-guards nil))
  (if (atom sources) nil
    (append (fn2-arm-path-entries-effect-rows kind (car sources)
              (fn2-arm-assignments (fn2-arm-entry-doms doms (nth 3 path)))
              (caddr path) holds while ret world)
            (fn2-arm-path-sources-effect-rows kind (cdr sources) path doms holds while ret world))))
(defun fn2-arm-paths-effect-rows (kind sources paths doms holds while ret world)
  (declare (xargs :verify-guards nil))
  (if (atom paths) nil
    (let ((path (car paths)))
      (append (and (not (nth 5 path))
                   (fn2-arm-path-sources-effect-rows kind
                     (if (eq (car path) :any) sources (intersection-eq (car path) sources))
                     path doms holds while ret world))
              (fn2-arm-paths-effect-rows kind sources (cdr paths) doms holds while ret world)))))
; ----------------------------------------------------------------------
; The frame predicate of an arm's invariant row: cores as lists of children.
; Every child outside CHILDREN is unchanged; in the kind's table (child TABLE)
; every column outside COLUMNS is unchanged and the declared columns change
; only at ROW. Executable, so its teeth evaluate.
(defun fn2-arm-equal-except (row a b)
  (declare (xargs :verify-guards nil))
  (and (equal (len a) (len b)) (equal (update-nth (nfix row) nil a) (update-nth (nfix row) nil b))))
(defun fn2-arm-frame-children (i c0 c1 free)
  (declare (xargs :verify-guards nil :measure (acl2-count c0)))
  (if (atom c0) (atom c1)
    (and (consp c1) (or (member-equal i free) (equal (car c0) (car c1)))
         (fn2-arm-frame-children (+ 1 i) (cdr c0) (cdr c1) free))))
(defun fn2-arm-frame-columns (k t0 t1 row columns)
  (declare (xargs :verify-guards nil :measure (acl2-count t0)))
  (if (atom t0) (atom t1)
    (and (consp t1)
         (if (member-equal k columns) (fn2-arm-equal-except row (car t0) (car t1))
           (equal (car t0) (car t1)))
         (fn2-arm-frame-columns (+ 1 k) (cdr t0) (cdr t1) row columns))))
(defun fn2-arm-framep (table row columns children c0 c1)
  (declare (xargs :verify-guards nil))
  (and (fn2-arm-frame-children 0 c0 c1 (cons table children))
       (or (member-equal table children)
           (fn2-arm-frame-columns 0 (nth table c0) (nth table c1) row columns))))
(defun fn2-arm-frame-positive ()
  (declare (xargs :verify-guards nil))
  ; child 1 is the table; column 0 declared; row 1 changes there only.
  (and (fn2-arm-framep 1 1 '(0) '(2) '(a ((0 0) (5 5)) c) '(a ((0 9) (5 5)) z))
       (fn2-arm-framep 1 1 '(0) nil '(a ((0 0) (5 5)) c) '(a ((0 0) (5 5)) c))))
(defun fn2-arm-frame-negative ()
  (declare (xargs :verify-guards nil))
  (and (not (fn2-arm-framep 1 1 '(0) nil '(a ((0 0) (5 5)) c) '(a ((0 0) (5 6)) c)))   ; undeclared column
       (not (fn2-arm-framep 1 1 '(0) nil '(a ((0 0) (5 5)) c) '(a ((9 0) (5 5)) c)))   ; another row
       (not (fn2-arm-framep 1 1 '(0) nil '(a ((0 0) (5 5)) c) '(b ((0 0) (5 5)) c))))) ; undeclared child
