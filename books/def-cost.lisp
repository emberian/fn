; fn: `def-cost' --- an entry's visit cost DERIVED from its executed body
; (lane def-entry round two, 2026-10-03; consultations c04/c06 and the
; coordinator's rulings: a cost is derived, never declared; an unknown callee
; is UNACCOUNTED, never zero; a declared bound is a theorem about the derived
; cost; the route is read from the final world; a served guard whose cost
; depends on a whole-state size is refused, not charged).
;
;   (def-cost NAME
;     [:visits BOUND :sizes ((S TERM) ...)]  ; BOUND over the size names S; TERM over
;                                            ; NAME's formals (a request size, a profile
;                                            ; field, a carried list's length)
;     [:unaccounted (F ...)]                 ; the callees the derivation cannot cost:
;                                            ; checked EQUAL to the derived set
;     [:hints H] [:measure-hints H])         ; the bound's and the twin's admission hints
;
; THE TWINS.  `NAME-visits' is a definition with NAME's control structure,
; written from NAME's TRANSLATED BODY in the world (never from a user term):
; a variable or constant costs 0; (if a b c) costs a's cost plus b's or c's
; by a's value; a lambda application costs its actuals plus its body with the
; same bindings; (return-last 'mbe1-raw EXEC LOGIC) costs EXEC, the arm that
; runs; any other return-last costs its arguments; a call (f A ...) costs its
; actuals plus f's CONTRACT on them:
;
;   * f in `*fn-cost-contracts*' (the trusted base, below): the row's :visits
;     template with a1 a2 ... the actuals -- (len a1) for a list walk, 0 for a
;     cons-cell step or an arithmetic step on a fixnum;
;   * f a concrete stobj's accessor, updater, length or recognizer (the
;     world's `stobj-function' property): 1, one array or field operation
;     in raw Lisp whatever its logical body says;
;   * f with a def-cost row: (f-visits A ...), the callee's own derived twin;
;   * f = NAME: (NAME-visits A ...), the twin recurring as the body does, with
;     the body's measure and well-founded relation copied from the world;
;   * f defined, not recursive, its body under `*fn-cost-inline-nodes*' nodes
;     and every call in it costed: INLINED, the body's derived cost with the
;     actuals substituted (a record accessor, a one-line wrapper);
;   * else UNACCOUNTED: (fn-cost-unaccounted 'f (list A ...)), a constrained
;     natural with no axiom, so no bound over it is provable and the row
;     names it; a constrained function (an attachment runs), a mutual
;     recursion, a body past the fuel, a `:program' callee are all this.
;
; The twin is an ordinary `defun' (:verify-guards nil) when NAME takes no
; stobj, else a `defun-nx' over the stobj formals renamed (S -> S-v): the
; stobj's VALUE is a term there, as def-carried's trace treats it.
; `NAME-route-visits' adds what the host evaluates ONCE at the entry (the
; route, below) to (NAME-visits ...): a kind check is never counted per
; recursive call of the body's twin.
;
; THE ROUTE, from the world.  NAME in `fn-interfaces' with :raw-with: the
; host evaluates the kind checks only (fnn-entry-guard), so the entry's cost
; is kinds + body (:raw).  NAME in `fn-interfaces' without: the counterpart
; evaluates the whole guard before the body (:served): kinds + the rest of
; the guard + body; and the rest of the guard's derived cost MUST NOT mention
; a whole-state size (`*fn-cost-whole-state-sizes*': the catalog's count, the
; arena's, the record list): that is the walk AGENTS.md forbids on a served
; path, so the declaration is REFUSED naming the size, never charged
; (fn-splan-cursor-step's catalog guard per quantum).  NAME not an entry:
; body only (:internal).  Which route is a world fact recorded in the row,
; and `def-cost-check' regenerates the twin's body and the route in the
; current world and refuses on any difference, so a changed body, guard or
; interface declaration cannot keep a stale cost.
;
; THE BOUND.  With :visits, the theorem
;   NAME-visits-bound: (implies G (<= (NAME-route-visits ...) (+ BOUND[S := TERM] U ...)))
; where G is NAME's guard and U ... the unaccounted terms the twin holds: a
; bound is always PARTIAL over them, stated as such (the row's :unaccounted
; must equal the derived list, else refused), and complete when the list is
; empty.  The default hints open the twin and induct on it when it recurs.
; The owed teeth row (lanedumps/generators-2.md, contract v1) names the claim
; and the subject; the teeth book states the witness (an executable twin is
; evaluated; a defun-nx twin takes a :witness-lemma).
;
; Refused, each by name: NAME not a :logic function; a :sizes name that is
; not a symbol, or a size TERM over other variables; BOUND over anything but
; the size names and constants; :unaccounted not the derived set; a served
; guard over a whole-state size; a row declared twice; a twin name taken.
;
; What is NOT derived here (v1): allocation (the row records :allocation
; :deferred), the attachment a constrained function runs (unaccounted), the
; cost of a kind check that is not in the contract table (unaccounted).  The
; contract table is the trusted base: one row per primitive with its reason;
; tools/cost_obligations.py emits it to planning/cost-contracts.json and
; refuses a row that changed or vanished against the committed copy.

(in-package "ACL2")
(include-book "definterface") ; fn-di-guard-kinds, fn-di-kind-checks; fn-cd-subst

; ---------------------------------------------------------------------------
; The unaccounted cost: a natural nothing else is known about.

(encapsulate
  (((fn-cost-unaccounted * *) => *))
  (local (defun fn-cost-unaccounted (f args) (declare (ignore f args)) 0))
  (defthm fn-cost-unaccounted-natp
    (natp (fn-cost-unaccounted f args))
    :rule-classes :type-prescription))

; ---------------------------------------------------------------------------
; The trusted base: the primitives' contracts.  TEMPLATE over a1 ... an, the
; actuals in order; :reason says why, in raw Lisp on this toolchain.

(defconst *fn-cost-contracts*
  '((car 0 "one cell read")
    (cdr 0 "one cell read")
    (cons 0 "one cell allocated, no visit")
    (consp 0 "a type test")
    (atom 0 "a type test")
    (null 0 "a type test")
    (not 0 "a boolean step")
    (eq 0 "a pointer comparison")
    (eql 0 "a pointer or fixnum comparison")
    (equal (binary-+ '1 (acl2-count a1)) "a structural comparison walks the smaller operand; counted as the first, a conservative bound")
    (zp 0 "a fixnum test")
    (natp 0 "a type test")
    (integerp 0 "a type test")
    (symbolp 0 "a type test")
    (stringp 0 "a type test")
    (keywordp 0 "a type test")
    (booleanp 0 "a type test")
    (characterp 0 "a type test")
    (true-listp (binary-+ '1 (len a1)) "walks the list to its end")
    (len (binary-+ '1 (len a1)) "walks the list to its end")
    (binary-+ 0 "an arithmetic step; bignums are not counted (D27: profile fields are u64)")
    (binary-* 0 "an arithmetic step")
    (unary-- 0 "an arithmetic step")
    (< 0 "a comparison")
    (floor 0 "an arithmetic step")
    (mod 0 "an arithmetic step")
    (nfix 0 "a fixnum step")
    (ifix 0 "a fixnum step")
    (nth (binary-+ '1 (nfix a1)) "walks a1 cells")
    (nthcdr (binary-+ '1 (nfix a1)) "walks a1 cells")
    (take (binary-+ '1 (nfix a1)) "walks a1 cells")
    (member-equal (binary-+ '1 (len a2)) "walks the list")
    (assoc-equal (binary-+ '1 (len a2)) "walks the alist")
    (append (binary-+ '1 (len a1)) "walks the first list")
    (binary-append (binary-+ '1 (len a1)) "walks the first list")
    (revappend (binary-+ '1 (len a1)) "walks the first list")
    (reverse (binary-+ '1 (len a1)) "walks the list")
    (code-char 0 "a table read")
    (char-code 0 "a table read")
    (get-global 0 "a symbol-value read in raw Lisp")
    (put-global 0 "a symbol-value write in raw Lisp")
    (boundp-global 0 "a symbol-value test in raw Lisp")
    (boundp-global1 0 "a symbol-value test in raw Lisp")
    (fn-cbor-octet-listp (binary-+ '1 (len a1)) "the kind check walks the octets (books/payload-kinds.lisp: at most linear in its argument)")
    (fn-octet-list-listp (binary-+ '1 (len a1)) "the kind check walks the outer list; each element's walk is the inner kind's")
    (fn-cat-count 0 "an abstract stobj count field")
    (fn-arena-count 0 "an abstract stobj count field")
    (fn-cat-at 1 "one catalog row read")))

(defconst *fn-cost-whole-state-sizes*
  '(fn-cat-count fn-arena-count fn-hist-count fn-sn-records fn-sn-files))

(defconst *fn-cost-inline-nodes* 400)

(defconst *fn-cost-fuel* 60)

(defconst *fn-cost-keys* '(:visits :sizes :unaccounted :hints :measure-hints))

; ---------------------------------------------------------------------------
; Term plumbing (:program).

(defun fn-cost-get (key kvs)
  (declare (xargs :mode :program))
  (cadr (assoc-keyword key kvs)))

(defun fn-cost-nodes (x)
  (declare (xargs :mode :program))
  (if (consp x) (+ 1 (fn-cost-nodes (car x)) (fn-cost-nodes (cdr x))) 1))

(defun fn-cost-plus (a b)
  (declare (xargs :mode :program))
  ; a + b, zeros dropped
  (cond ((equal a ''0) b)
        ((equal a 0) b)
        ((or (equal b ''0) (equal b 0)) a)
        (t (list 'binary-+ a b))))

(defun fn-cost-sum (terms)
  (declare (xargs :mode :program))
  (if (atom terms) ''0 (fn-cost-plus (car terms) (fn-cost-sum (cdr terms)))))

(defun fn-cost-template-vars (n)
  (declare (xargs :mode :program))
  ; (a1 ... an)
  (if (zp n) nil (append (fn-cost-template-vars (1- n))
                         (list (intern-in-package-of-symbol
                                (concatenate 'string "A" (coerce (explode-nonnegative-integer n 10 nil) 'string))
                                'fn-cost-get)))))

(defun fn-cost-contract-term (row actuals)
  (declare (xargs :mode :program))
  ; the row's template with a1 ... an the actuals; a number is a constant
  (let ((template (cadr row)))
    (if (integerp template)
        (kwote template)
      (fn-cd-subst template (pairlis$ (fn-cost-template-vars (len actuals)) actuals)))))

(defun fn-cost-twin-name (fn)
  (declare (xargs :mode :program))
  (packn-pos (list fn '-visits) fn))

(defun fn-cost-route-name (fn)
  (declare (xargs :mode :program))
  (packn-pos (list fn '-route-visits) fn))

(defun fn-cost-bound-name (fn)
  (declare (xargs :mode :program))
  (packn-pos (list fn '-visits-bound) fn))

(mutual-recursion
 (defun fn-cost-calls (term)
   (declare (xargs :mode :program))
   ; the function symbols TERM calls, lambdas opened
   (cond ((or (atom term) (eq (car term) 'quote)) nil)
         ((consp (car term))
          (union-eq (fn-cost-calls (car (last (car term)))) (fn-cost-calls-lst (cdr term))))
         (t (add-to-set-eq (car term) (fn-cost-calls-lst (cdr term))))))
 (defun fn-cost-calls-lst (terms)
   (declare (xargs :mode :program))
   (if (atom terms) nil (union-eq (fn-cost-calls (car terms)) (fn-cost-calls-lst (cdr terms))))))

(defun fn-cost-recursivep (fn w)
  (declare (xargs :mode :program))
  (member-eq fn (fn-cost-calls (getpropc fn 'unnormalized-body nil w))))

; ---------------------------------------------------------------------------
; The derivation.  (mv COST UNACCOUNTED): COST a term over the formals (and
; the let-bound variables of the translated body), UNACCOUNTED the names.

(mutual-recursion
 (defun fn-cost-term (term self stack fuel w)
   (declare (xargs :mode :program))
   (cond
    ((or (atom term) (eq (car term) 'quote)) (mv ''0 nil))
    ((consp (car term))
     ; ((lambda (v ...) body) a ...): the actuals, then the body bound the same way
     (mv-let (acost aun) (fn-cost-terms (cdr term) self stack fuel w)
       (mv-let (bcost bun) (fn-cost-term (car (last (car term))) self stack fuel w)
         (mv (fn-cost-plus acost
                           (if (equal bcost ''0)
                               ''0
                             (list (list 'lambda (cadr (car term)) bcost) (cdr term))))
             (union-eq aun bun)))))
    ((eq (car term) 'if)
     (mv-let (tcost tun) (fn-cost-term (cadr term) self stack fuel w)
       (mv-let (acost aun) (fn-cost-term (caddr term) self stack fuel w)
         (mv-let (bcost bun) (fn-cost-term (cadddr term) self stack fuel w)
           (mv (fn-cost-plus tcost (if (and (equal acost ''0) (equal bcost ''0))
                                       ''0
                                     (list 'if (cadr term) acost bcost)))
               (union-eq tun (union-eq aun bun)))))))
    ((eq (car term) 'return-last)
     (if (equal (cadr term) ''mbe1-raw)
         (fn-cost-term (caddr term) self stack fuel w)   ; the :exec arm runs
       (fn-cost-terms (cddr term) self stack fuel w)))
    (t (mv-let (acost aun) (fn-cost-terms (cdr term) self stack fuel w)
         (mv-let (ccost cun) (fn-cost-call (car term) (cdr term) self stack fuel w)
           (mv (fn-cost-plus acost ccost) (union-eq aun cun)))))))
 (defun fn-cost-terms (terms self stack fuel w)
   (declare (xargs :mode :program))
   (if (atom terms)
       (mv ''0 nil)
     (mv-let (c u) (fn-cost-term (car terms) self stack fuel w)
       (mv-let (cs us) (fn-cost-terms (cdr terms) self stack fuel w)
         (mv (fn-cost-plus c cs) (union-eq u us))))))
 (defun fn-cost-call (fn actuals self stack fuel w)
   (declare (xargs :mode :program))
   ; the contract of FN on ACTUALS
   (let ((row (assoc-eq fn *fn-cost-contracts*))
         (body (getpropc fn 'unnormalized-body nil w)))
     (cond
      (row (mv (fn-cost-contract-term row actuals) nil))
      ((getpropc fn 'stobj-function nil w)
       ; a concrete stobj's accessor, updater, length or recognizer: one
       ; array or field operation in raw Lisp, whatever its logical body
       ; (an array length is (len (nth i st)) in the logic, O(1) executed)
       (mv ''1 nil))
      ((eq fn self) (mv (cons (fn-cost-twin-name fn) actuals) nil))
      ((assoc-eq fn (table-alist 'fn-cost w))
       (mv (cons (fn-cost-twin-name fn) actuals) nil))
      ((and body
            (not (eq (symbol-class fn w) :program))
            (not (member-eq fn stack))
            (not (fn-cost-recursivep fn w))
            (not (getpropc fn 'constrainedp nil w))
            (< (fn-cost-nodes body) *fn-cost-inline-nodes*)
            (not (zp fuel)))
       ; inlined: the callee's derived cost with the actuals for its formals
       (mv-let (c u) (fn-cost-term body self (cons fn stack) (1- fuel) w)
         (if u
             (mv (list 'fn-cost-unaccounted (kwote fn) (cons 'list actuals)) (list fn))
           (mv (fn-cd-subst c (pairlis$ (getpropc fn 'formals nil w) actuals)) nil))))
      (t (mv (list 'fn-cost-unaccounted (kwote fn) (cons 'list actuals)) (list fn)))))))

(mutual-recursion
 (defun fn-cost-mentions (term fns)
   (declare (xargs :mode :program))
   ; the first of FNS applied in TERM, else nil
   (cond ((or (atom term) (eq (car term) 'quote)) nil)
         ((and (symbolp (car term)) (member-eq (car term) fns)) (car term))
         (t (or (and (consp (car term)) (fn-cost-mentions (car (last (car term))) fns))
                (fn-cost-mentions-lst (cdr term) fns)))))
 (defun fn-cost-mentions-lst (terms fns)
   (declare (xargs :mode :program))
   (cond ((atom terms) nil)
         (t (or (fn-cost-mentions (car terms) fns) (fn-cost-mentions-lst (cdr terms) fns))))))

; ---------------------------------------------------------------------------
; The route: what the host evaluates before the body.

(defun fn-cost-route (fn w)
  (declare (xargs :mode :program))
  (let ((entry (assoc-eq fn (table-alist 'fn-interfaces w))))
    (cond ((null entry) :internal)
          ((assoc-keyword :raw-with (cdr entry)) :raw)
          (t :served))))

(defun fn-cost-kind-conjuncts (conjuncts formals stobjs kinds)
  (declare (xargs :mode :program))
  (cond ((atom conjuncts) nil)
        ((fn-di-kind-checks (list (car conjuncts)) formals stobjs kinds)
         (cons (car conjuncts) (fn-cost-kind-conjuncts (cdr conjuncts) formals stobjs kinds)))
        (t (fn-cost-kind-conjuncts (cdr conjuncts) formals stobjs kinds))))

(defun fn-cost-other-conjuncts (conjuncts formals stobjs kinds w)
  (declare (xargs :mode :program))
  ; the guard conjuncts the counterpart evaluates beyond the kind checks: a
  ; stobj formal's own recognizer is held by the stobj discipline (a live
  ; stobj is that stobj), never evaluated, as definterface reads it
  (cond ((atom conjuncts) nil)
        ((or (fn-di-kind-checks (list (car conjuncts)) formals stobjs kinds)
             (fn-di-stobj-recognizer-conjunctp (car conjuncts) formals stobjs w))
         (fn-cost-other-conjuncts (cdr conjuncts) formals stobjs kinds w))
        (t (cons (car conjuncts) (fn-cost-other-conjuncts (cdr conjuncts) formals stobjs kinds w)))))

(defun fn-cost-guard-parts (fn w)
  (declare (xargs :mode :program))
  ; (mv KINDS REST): the guard's kind conjuncts and the others
  (let* ((conjuncts (fn-di-conjuncts (getpropc fn 'guard *t* w)))
         (formals (getpropc fn 'formals nil w))
         (stobjs (getpropc fn 'stobjs-in nil w))
         (kinds (fn-di-guard-kinds w)))
    (mv (fn-cost-kind-conjuncts conjuncts formals stobjs kinds)
        (fn-cost-other-conjuncts conjuncts formals stobjs kinds w))))

(defun fn-cost-derive (fn w)
  (declare (xargs :mode :program))
  ; (mv MSG ROUTE ROUTE-COST BODY-COST UNACCOUNTED): what the host evaluates
  ; before the body on the entry's route (kinds; the rest of the guard when
  ; served), and the body, over the original formals
  (let ((route (fn-cost-route fn w)))
    (mv-let (kinds rest)
      (fn-cost-guard-parts fn w)
      (mv-let (kcost kun) (fn-cost-terms (if (eq route :internal) nil kinds) fn nil *fn-cost-fuel* w)
        (mv-let (rcost run) (fn-cost-terms (if (eq route :served) rest nil) fn nil *fn-cost-fuel* w)
          (mv-let (bcost bun) (fn-cost-term (getpropc fn 'unnormalized-body nil w) fn nil *fn-cost-fuel* w)
            (let ((size (and (eq route :served)
                             (fn-cost-mentions rcost *fn-cost-whole-state-sizes*))))
              (if size
                  (mv (msg "~x0 is a served entry (fn-interfaces, no :raw-with) whose guard ~
                            the counterpart evaluates on every call, and that guard's ~
                            derived cost depends on ~x1, a whole-state size: the walk ~
                            AGENTS.md forbids on a served path.  It is not charged: carry ~
                            the relation (def-carried) and dispatch raw, or move the check ~
                            off the served route" fn size)
                      route nil nil nil)
                (mv nil route (fn-cost-plus kcost rcost) bcost
                    (union-eq kun (union-eq run bun)))))))))))

; ---------------------------------------------------------------------------
; The events.

(defun fn-cost-stobj-alist1 (formals stobjs fn)
  (declare (xargs :mode :program))
  (cond ((atom formals) nil)
        ((car stobjs) (cons (cons (car formals) (packn-pos (list (car formals) '-v) fn))
                            (fn-cost-stobj-alist1 (cdr formals) (cdr stobjs) fn)))
        (t (fn-cost-stobj-alist1 (cdr formals) (cdr stobjs) fn))))

(defun fn-cost-stobj-alist (fn w)
  (declare (xargs :mode :program))
  ; stobj formal -> its renamed value variable
  (let ((formals (getpropc fn 'formals nil w))
        (stobjs (getpropc fn 'stobjs-in nil w)))
    (fn-cost-stobj-alist1 formals stobjs fn)))

(defun fn-cost-rename (formals alist)
  (declare (xargs :mode :program))
  (cond ((atom formals) nil)
        (t (cons (let ((b (assoc-eq (car formals) alist))) (if b (cdr b) (car formals)))
                 (fn-cost-rename (cdr formals) alist)))))

(defun fn-cost-sizesp (x)
  (declare (xargs :mode :program))
  (if (atom x)
      (null x)
    (and (true-listp (car x)) (equal (len (car x)) 2) (symbolp (caar x)) (caar x)
         (fn-cost-sizesp (cdr x)))))

(mutual-recursion
 (defun fn-cost-unaccounted-terms (term)
   (declare (xargs :mode :program))
   ; every (fn-cost-unaccounted ...) subterm, each once
   (cond ((or (atom term) (eq (car term) 'quote)) nil)
         ((eq (car term) 'fn-cost-unaccounted) (list term))
         ((consp (car term))
          (union-equal (fn-cost-unaccounted-terms (car (last (car term))))
                       (fn-cost-unaccounted-terms-lst (cdr term))))
         (t (fn-cost-unaccounted-terms-lst (cdr term)))))
 (defun fn-cost-unaccounted-terms-lst (terms)
   (declare (xargs :mode :program))
   (if (atom terms)
       nil
     (union-equal (fn-cost-unaccounted-terms (car terms))
                  (fn-cost-unaccounted-terms-lst (cdr terms))))))

(defun fn-cost-problem (fn kvs w)
  (declare (xargs :mode :program))
  ; (mv MSG ROUTE (ROUTE-COST . BODY-COST) UNACCOUNTED SIZES BOUND)
  (let ((sizes (fn-cost-get :sizes kvs))
        (bound (fn-cost-get :visits kvs)))
    (cond
     ((not (and (symbolp fn) fn)) (mv (msg "~x0 is not a function name" fn) nil nil nil nil nil))
     ((not (keyword-value-listp kvs)) (mv (msg "~x0: options are not a keyword list" fn) nil nil nil nil nil))
     ((fn-cd-unknown-keys kvs *fn-cost-keys*)
      (mv (msg "~x0: unknown keyword(s) ~&1; the keywords are ~&2"
               fn (fn-cd-unknown-keys kvs *fn-cost-keys*) *fn-cost-keys*)
          nil nil nil nil nil))
     ((eq (getpropc fn 'formals :none w) :none)
      (mv (msg "~x0 is not a function in this world" fn) nil nil nil nil nil))
     ((eq (symbol-class fn w) :program)
      (mv (msg "~x0 is :program mode: its body is not a term the world holds; convert it ~
                to :logic first" fn)
          nil nil nil nil nil))
     ((assoc-eq fn (table-alist 'fn-cost w))
      (mv (msg "~x0 already has a cost row; a row is declared once" fn) nil nil nil nil nil))
     ((or (getpropc (fn-cost-twin-name fn) 'formals nil w)
          (getpropc (fn-cost-route-name fn) 'formals nil w))
      (mv (msg "~x0: ~x1 or ~x2 is already a function of this world"
               fn (fn-cost-twin-name fn) (fn-cost-route-name fn))
          nil nil nil nil nil))
     ((not (fn-cost-sizesp sizes))
      (mv (msg "~x0: :sizes ~x1 is not ((S TERM) ...)" fn sizes) nil nil nil nil nil))
     ((and (assoc-keyword :visits kvs) (null bound))
      (mv (msg "~x0: :visits names no bound" fn) nil nil nil nil nil))
     ((not (true-listp (fn-cost-get :unaccounted kvs)))
      (mv (msg "~x0: :unaccounted ~x1 is not a list" fn (fn-cost-get :unaccounted kvs))
          nil nil nil nil nil))
     (t
      (mv-let (bad sterms)
        (fn-cd-translate-list (strip-cadrs sizes) w)
        (cond
         (bad (mv (msg "~x0: size term ~x1 does not translate in this world" fn (car bad))
                  nil nil nil nil nil))
         ((not (subsetp-eq (all-vars1-lst sterms nil) (getpropc fn 'formals nil w)))
          (mv (msg "~x0: a size term mentions a variable that is not a formal ~x1"
                   fn (getpropc fn 'formals nil w))
              nil nil nil nil nil))
         (t
          (mv-let (badb bterms)
            (fn-cd-translate-list (and bound (list bound)) w)
            (cond
             (badb (mv (msg "~x0: :visits ~x1 does not translate in this world" fn bound)
                       nil nil nil nil nil))
             ((and bound (not (subsetp-eq (all-vars (car bterms)) (strip-cars sizes))))
              (mv (msg "~x0: :visits ~x1 mentions ~&2, not size names ~&3"
                       fn bound
                       (set-difference-eq (all-vars (car bterms)) (strip-cars sizes))
                       (strip-cars sizes))
                  nil nil nil nil nil))
             (t
              (mv-let (msg route rcost bcost unaccounted)
                (fn-cost-derive fn w)
                (cond
                 (msg (mv msg nil nil nil nil nil))
                 ((not (and (subsetp-eq unaccounted (fn-cost-get :unaccounted kvs))
                            (subsetp-eq (fn-cost-get :unaccounted kvs) unaccounted)))
                  (mv (msg "~x0: the derivation leaves ~&1 unaccounted (no contract, no ~
                            cost row, not inlinable); the declaration says ~x2.  Declare ~
                            exactly the derived list: a bound is partial over it"
                           fn unaccounted (fn-cost-get :unaccounted kvs))
                      nil nil nil nil nil))
                 (t (mv nil route (cons rcost bcost) unaccounted
                        (pairlis$ (strip-cars sizes) (pairlis$ sterms nil))
                        (and bound (car bterms))))))))))))))))

(defun fn-cost-sizes-alist (sizes)
  (declare (xargs :mode :program))
  ; ((S . TERM) ...) from the normalized ((S (TERM)) ...)
  (if (atom sizes) nil (cons (cons (caar sizes) (car (cdar sizes))) (fn-cost-sizes-alist (cdr sizes)))))

(defun fn-cost-events (fn kvs route cost unaccounted sizes bound w)
  (declare (xargs :mode :program))
  ; COST = (ROUTE-COST . BODY-COST): NAME-visits is the body's twin (recurring
  ; as the body does); NAME-route-visits adds what the host evaluates once at
  ; the entry, so a kind check is never counted per recursive call
  (let* ((alist (fn-cost-stobj-alist fn w))
         (formals (fn-cost-rename (getpropc fn 'formals nil w) alist))
         (twin (fn-cost-twin-name fn))
         (rtwin (fn-cost-route-name fn))
         (rcost (fn-cd-subst (car cost) alist))
         (bcost (fn-cd-subst (cdr cost) alist))
         (recursive (fn-cost-recursivep fn w))
         (j (getpropc fn 'justification nil w))
         (measure (and recursive j (fn-cd-subst (access justification j :measure) alist)))
         (rel (and recursive j (access justification j :rel)))
         (guard (fn-cd-subst (getpropc fn 'guard *t* w) alist))
         (us (union-equal (fn-cost-unaccounted-terms rcost) (fn-cost-unaccounted-terms bcost)))
         (bound-term (and bound
                          (fn-cost-sum (cons (fn-cd-subst (fn-cd-subst bound (fn-cost-sizes-alist sizes)) alist)
                                             us))))
         (stobjs (strip-cars alist))
         (def (if stobjs 'defun-nx 'defun))
         (name (fn-cost-bound-name fn)))
    `(progn
       (,def ,twin ,formals
        (declare (xargs :verify-guards nil
                        ,@(and measure (list :measure measure))
                        ,@(and rel (list :well-founded-relation rel))
                        ,@(and (fn-cost-get :measure-hints kvs)
                               (list :hints (fn-cost-get :measure-hints kvs)))))
        ,bcost)
       (,def ,rtwin ,formals
        (declare (xargs :verify-guards nil))
        ,(fn-cost-plus rcost (cons twin formals)))
       ,@(and bound
              `((defthm ,name
                  ,(if (equal guard *t*)
                       `(<= (,rtwin ,@formals) ,bound-term)
                     `(implies ,guard (<= (,rtwin ,@formals) ,bound-term)))
                  :hints ,(if (assoc-keyword :hints kvs)
                              (fn-cost-get :hints kvs)
                            `(("Goal" :in-theory (enable ,twin ,rtwin)
                               ,@(and recursive (list :induct (cons twin formals)))))))))
       (table fn-cost ',fn
              '(:route ,route :twin ,twin :route-twin ,rtwin
                :route-cost ,(car cost) :body-cost ,(cdr cost) :unaccounted ,unaccounted
                :sizes ,(fn-cost-sizes-alist sizes) :bound ,bound
                :theorem ,(and bound name) :allocation :deferred))
       ,@(and bound
              `((table fn-teeth-owed ',name
                       '(:by def-cost
                         :claim (,(if (equal guard *t*) nil `((g ,guard)))
                                 (<= (,rtwin ,@formals) ,bound-term))
                         :subject ,fn
                         :visits ((route (,rtwin ,@formals) ,bound-term)))))))))

(defmacro def-cost (fn &rest kvs)
  `(make-event
    (mv-let (problem route cost unaccounted sizes bound)
      (fn-cost-problem ',fn ',kvs (w state))
      (if problem
          (er soft 'def-cost "~x0: ~@1" ',fn problem)
        (value (fn-cost-events ',fn ',kvs route cost unaccounted sizes bound (w state)))))))

; Re-derive in the current world and compare with the row: a changed body,
; guard or interface declaration refuses.
(defmacro def-cost-check (fn)
  `(make-event
    (let ((row (cdr (assoc-eq ',fn (table-alist 'fn-cost (w state))))))
      (if (null row)
          (er soft 'def-cost-check "no cost row for ~x0 in this world" ',fn)
        (mv-let (msg route rcost bcost unaccounted)
          (fn-cost-derive ',fn (w state))
          (cond (msg (er soft 'def-cost-check "~x0: ~@1" ',fn msg))
                ((not (eq route (fn-cost-get :route row)))
                 (er soft 'def-cost-check "~x0: the route is now ~x1, the row says ~x2"
                     ',fn route (fn-cost-get :route row)))
                ((not (and (equal rcost (fn-cost-get :route-cost row))
                           (equal bcost (fn-cost-get :body-cost row))))
                 (er soft 'def-cost-check "~x0: the derived cost is now ~x1 at the entry and ~
                                           ~x2 in the body; the row holds ~x3 and ~x4"
                     ',fn rcost bcost (fn-cost-get :route-cost row) (fn-cost-get :body-cost row)))
                ((not (and (subsetp-eq unaccounted (fn-cost-get :unaccounted row))
                           (subsetp-eq (fn-cost-get :unaccounted row) unaccounted)))
                 (er soft 'def-cost-check "~x0: the unaccounted callees are now ~x1; the row says ~x2"
                     ',fn unaccounted (fn-cost-get :unaccounted row)))
                (t (value '(value-triple ',fn)))))))))
