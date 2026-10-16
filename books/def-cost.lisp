; fn: `def-cost' --- an entry's visit cost DERIVED from its executed body
; (lane def-entry round two, 2026-10-03; consultations c04/c06 and the
; coordinator's rulings: a cost is derived, never declared; an unknown callee
; is UNACCOUNTED, never zero; a declared bound is a theorem about the derived
; cost; the route is read from the final world; a served guard whose cost
; depends on a whole-state size is refused, not charged).
; Rows are checked in the final world by books/cost-final-world.lisp, after
; the interface declarations and every callee's cost row are present.
;
;   (def-cost NAME
;     [:visits BOUND :sizes ((S TERM) ...)]  ; BOUND over the size names S; TERM over
;                                            ; NAME's formals (a request size, a profile
;                                            ; field, a carried list's length)
;     [:conses BOUND :cons-unaccounted (F ...) :cons-hints H]
;                                         ; optional logical cons dimension, same body
;     [:unaccounted (F ...)]                 ; the callees the derivation cannot cost:
;                                            ; checked EQUAL to the derived set
;     [:calls ((TAG (TARGET...) [:unaccounted (...) :measure-hints H :stop-at (FN...) :argument N]) ...)]
;     [:hints H] [:measure-hints H])         ; the bound's and the twin's admission hints
;
; LOGICAL CALL COORDINATES. :calls uses the SAME translated-body walker,
; charging one at a marked callee boundary, while still charging marked calls
; in its arguments. Other defined callees are followed through their actual
; bodies; primitive operations and native field accesses contain no nested
; logical call. Opaque/unsupported callees remain unaccounted, indexed by
; (TAG . FN), never silently zero. FN-TAG is derived from the body, not guards
; or host syscalls; ordinary route/guard visit accounting is unchanged.
; :stop-at names separately accounted call boundaries; their entire calls
; contribute zero to this coordinate, while their evaluated arguments still count.
; :argument N sums NFIX of actual argument N at each marked boundary;
; omitted, each marked boundary contributes one. It derives requested byte
; counts and offsets from executed call arguments without a parallel planner.
; A tag has one target/boundary/argument signature throughout a world. def-cost-check re-derives
; every coordinate and validates its source, formals, twin and canonical tag.
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
; THE ROUTE, from the world. NAME in `fn-interfaces' with :raw-with or
; :raw-guarded: the
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
; Unaccounted bound terms form a bag: each occurrence contributes one summand,
; including occurrences in different IF branches, in both cost dimensions.
; At each lambda application, simultaneous actual-for-formal substitution in
; collected body terms composes through nested lambdas, retaining the actuals'
; own unaccounted terms. Calls of cost twins inherit their body leaves with
; simultaneous actual substitution; a bound refuses a recursive callee whose
; row still has unaccounted leaves, since its repeated bag is not finite.
; The owed teeth row (lanedumps/generators-2.md, contract v1) names the claim
; and the subject; the teeth book states the witness (an executable twin is
; evaluated; a defun-nx twin takes a :witness-lemma).
;
; Refused, each by name: NAME not a :logic function; a :sizes name that is
; not a symbol, or a size TERM over other variables; BOUND over anything but
; the size names and constants; :unaccounted not the derived set; a served
; guard over a whole-state size; a row declared twice; a twin name taken.
;
; With :conses or :cons-unaccounted, the same engine also generates
; NAME-conses/NAME-route-conses and an optional bound in the SAME cost row.
; Quoted constants are borrowed, CONS costs one, copied list spines cost
; their length. MV-LET value bindings explicitly collect multiple values.
; Unknown leaves propagate independently for each dimension; a visit-only
; row never supplies a cons allocation contract. Stobj native allocations
; remain unknown. These are logical constructors, not physical bytes, peak
; residency, integer allocation, collector copying or native vector storage.
;
; What is NOT derived here: the physical heap tariff, the attachment a constrained function runs (unaccounted), the
; cost of a kind check that is not in the contract table (unaccounted).  The
; contract table is the trusted base: one row per primitive with its reason;
; tools/cost_obligations.py emits it to planning/cost-contracts.json and
; refuses a row that changed or vanished against the committed copy.

(in-package "ACL2")
(include-book "decimal-text")
(include-book "definterface") ; fn-di-guard-kinds, fn-di-kind-checks; fn-cd-subst

; ---------------------------------------------------------------------------
; The unaccounted cost: a natural nothing else is known about.

(encapsulate
  (((fn-cost-unaccounted * *) => *))
  (local (defun fn-cost-unaccounted (f args) (declare (ignore f args)) 0))
  (defthm fn-cost-unaccounted-natp
    (natp (fn-cost-unaccounted f args))
    :rule-classes :type-prescription))

(encapsulate
  (((fn-cost-unaccounted-conses * *) => *))
  (local (defun fn-cost-unaccounted-conses (f args)
           (declare (ignore f args)) 0))
  (defthm fn-cost-unaccounted-conses-natp
    (natp (fn-cost-unaccounted-conses f args))
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
    (fn-cat-horizon 1 "one cell of the catalog's withdrawal horizon")
    (fn-cat-group-raw-low 1 "one hash-table probe of the maintained raw low")
    (fn-arena-count 0 "an abstract stobj count field")
    (fn-cat-at 1 "one catalog row read")))

(defconst *fn-cost-whole-state-sizes*
  '(fn-cat-count fn-arena-count fn-hist-count fn-sn-records fn-sn-files))

(defconst *fn-cost-inline-nodes* 400)

(defconst *fn-cost-fuel* 60)

; Logical cons constructors only: neither a byte tariff nor retained heap.
; Constants borrow their representation. Arithmetic/character primitives may
; allocate other native objects; those allocations are outside this dimension.
(defconst *fn-cost-cons-contracts*
  '((cons 1 "one fresh logical cons")
    (car 0 "borrowed cell read") (cdr 0 "borrowed cell read")
    (consp 0 "test") (atom 0 "test") (null 0 "test") (not 0 "test")
    (eq 0 "comparison") (eql 0 "comparison") (equal 0 "comparison")
    (zp 0 "test") (natp 0 "test") (integerp 0 "test")
    (symbolp 0 "test") (stringp 0 "test") (keywordp 0 "test")
    (booleanp 0 "test") (characterp 0 "test") (true-listp 0 "read-only walk")
    (len 0 "read-only walk") (length 0 "read-only length")
    (binary-+ 0 "non-cons arithmetic") (binary-* 0 "non-cons arithmetic")
    (unary-- 0 "non-cons arithmetic") (< 0 "comparison")
    (floor 0 "non-cons arithmetic") (mod 0 "non-cons arithmetic")
    (nfix 0 "test") (ifix 0 "test")
    (nth 0 "borrowed cell read") (nthcdr 0 "borrowed tail")
    (mv-nth 0 "borrowed multiple-value component")
    (member-equal 0 "borrowed tail") (assoc-equal 0 "borrowed pair")
    (take (nfix a1) "one fresh cell per requested position")
    (append (len a1) "copies the first spine")
    (binary-append (len a1) "copies the first spine")
    (revappend (len a1) "copies the first spine")
    (char 0 "indexed character read; no list conversion executes")
    (code-char 0 "character lookup") (char-code 0 "character lookup")))

(defconst *fn-cost-keys*
  '(:visits :sizes :unaccounted :hints :measure-hints
    :conses :cons-unaccounted :cons-hints :calls))

(defun fn-cost-dimension-key (key dimension)
  (declare (xargs :mode :program))
  (if (eq dimension :conses)
      (case key (:visits :conses) (:unaccounted :cons-unaccounted)
            (:hints :cons-hints) (otherwise key))
    key))

(defun fn-cost-unknown-name (dimension)
  (declare (xargs :mode :program))
  (if (eq dimension :conses) 'fn-cost-unaccounted-conses 'fn-cost-unaccounted))

(defun fn-cost-dimension-name (fn part dimension)
  (declare (xargs :mode :program))
  (if (and (consp dimension) (eq (car dimension) :calls))
      (packn-pos (append (list fn) (and (eq part :route) (list '-route))
                        (list '- (cadr dimension))
                        (and (eq part :bound) (list '-bound))) fn)
    (packn-pos (append (list fn)
                    (and (eq part :route) (list '-route))
                    (list (if (eq dimension :conses) '-conses '-visits))
                    (and (eq part :bound) (list '-bound))) fn)))

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
                                (concatenate 'string "A" (fn-decimal-text n))
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

(defun fn-cost-used-bindings (formals actuals used)
  (declare (xargs :mode :program))
  (if (atom formals)
      (mv nil nil)
    (mv-let (fs as) (fn-cost-used-bindings (cdr formals) (cdr actuals) used)
      (if (member-eq (car formals) used)
          (mv (cons (car formals) fs) (cons (car actuals) as))
        (mv fs as)))))

(defun fn-cost-bind-body (formals actuals body)
  (declare (xargs :mode :program))
  ; Actual evaluation costs are already added separately.  Keep only the
  ; bindings needed by the cost body: a value computation can disappear
  ; when its cost becomes a constant, and ACL2 rejects unused lambda formals.
  (mv-let (fs as) (fn-cost-used-bindings formals actuals (all-vars body))
    (if (atom fs) body (cons (list 'lambda fs body) as))))

(defun fn-cost-call-primitivep (fn)
 (declare (xargs :mode :program))
 (or (member-eq fn '(if quote return-last acl2-numberp unary-/ coerce rationalp realpart imagpart intern-in-package-of-symbol))
     (and (assoc-eq fn *fn-cost-contracts*)
          (not (equal (subseq (symbol-name fn) 0 (min 3 (length (symbol-name fn)))) "FN-")))))
(defun fn-cost-call-reach (pending seen unknown targets boundaries w)
 (declare (xargs :mode :program))
 (if (atom pending) (if unknown :unknown :none)
  (let* ((fn (car pending)) (rest (cdr pending))
         (body (getpropc fn 'unnormalized-body nil w)))
   (cond ((member-eq fn targets) :yes)
         ((member-eq fn boundaries) (fn-cost-call-reach rest (cons fn seen) unknown targets boundaries w))
         ((member-eq fn seen) (fn-cost-call-reach rest seen unknown targets boundaries w))
         ((or (fn-cost-call-primitivep fn) (getpropc fn 'stobj-function nil w))
          (fn-cost-call-reach rest (cons fn seen) unknown targets boundaries w))
         ((and body (not (eq (symbol-class fn w) :program))
                    (not (getpropc fn 'constrainedp nil w)))
          (fn-cost-call-reach (append (fn-cost-calls body) rest) (cons fn seen) unknown targets boundaries w))
         (t (fn-cost-call-reach rest (cons fn seen) t targets boundaries w))))))

(mutual-recursion
 (defun fn-cost-term-dimension (term self stack fuel w dimension)
   (declare (xargs :mode :program))
   (cond
    ((or (atom term) (eq (car term) 'quote)) (mv ''0 nil))
    ((consp (car term))
     ; ((lambda (v ...) body) a ...): the actuals, then the body bound the same way
     (mv-let (acost aun) (fn-cost-terms-dimension (cdr term) self stack fuel w dimension)
       (mv-let (bcost bun) (fn-cost-term-dimension (car (last (car term))) self stack fuel w dimension)
         (mv (fn-cost-plus acost
                           (fn-cost-bind-body (cadr (car term)) (cdr term) bcost))
             (union-eq aun bun)))))
    ((eq (car term) 'if)
     (mv-let (tcost tun) (fn-cost-term-dimension (cadr term) self stack fuel w dimension)
       (mv-let (acost aun) (fn-cost-term-dimension (caddr term) self stack fuel w dimension)
         (mv-let (bcost bun) (fn-cost-term-dimension (cadddr term) self stack fuel w dimension)
           (mv (fn-cost-plus tcost (if (and (equal acost ''0) (equal bcost ''0))
                                       ''0
                                     (list 'if (cadr term) acost bcost)))
               (union-eq tun (union-eq aun bun)))))))
    ((eq (car term) 'return-last)
     (if (equal (cadr term) ''mbe1-raw)
         (fn-cost-term-dimension (caddr term) self stack fuel w dimension)   ; the :exec arm runs
       (fn-cost-terms-dimension (cddr term) self stack fuel w dimension)))
    (t (mv-let (acost aun) (fn-cost-terms-dimension (cdr term) self stack fuel w dimension)
         (mv-let (ccost cun) (fn-cost-call-dimension (car term) (cdr term) self stack fuel w dimension)
           (mv (fn-cost-plus acost ccost) (union-eq aun cun)))))))
 (defun fn-cost-terms-dimension (terms self stack fuel w dimension)
   (declare (xargs :mode :program))
   (if (atom terms)
       (mv ''0 nil)
     (mv-let (c u) (fn-cost-term-dimension (car terms) self stack fuel w dimension)
       (mv-let (cs us) (fn-cost-terms-dimension (cdr terms) self stack fuel w dimension)
         (mv (fn-cost-plus c cs) (union-eq u us))))))
 (defun fn-cost-call-dimension (fn actuals self stack fuel w dimension)
   (declare (xargs :mode :program))
   ; the contract of FN on ACTUALS
   (if (and (consp dimension) (eq (car dimension) :calls))
       (fn-cost-call-count-callee fn actuals self stack fuel w dimension)
    (let ((row (assoc-eq fn (if (eq dimension :conses) *fn-cost-cons-contracts* *fn-cost-contracts*)))
         (body (getpropc fn 'unnormalized-body nil w)))
     (cond
      (row (mv (fn-cost-contract-term row actuals) nil))
      ((and (not (eq dimension :conses)) (getpropc fn 'stobj-function nil w))
       ; a concrete stobj's accessor, updater, length or recognizer: one
       ; array or field operation in raw Lisp, whatever its logical body
       ; (an array length is (len (nth i st)) in the logic, O(1) executed)
       (mv ''1 nil))
      ((getpropc fn 'stobj-function nil w)
       ; Its native allocation is not its logical list implementation.
       ; Resizes/creators/updaters need an explicit representation contract.
       (mv (list (fn-cost-unknown-name dimension) (kwote fn) (cons 'list actuals)) (list fn)))
      ((eq fn self) (mv (cons (fn-cost-dimension-name fn :body dimension) actuals) nil))
      ((and (assoc-eq fn (table-alist 'fn-cost w))
            (or (not (eq dimension :conses))
                (fn-cost-get :cons-twin (cdr (assoc-eq fn (table-alist 'fn-cost w))))))
       ; A twin is callable even when its derivation is partial.  Its row's
       ; unknown leaves remain unknown in every caller, not just here.
       (mv (cons (fn-cost-dimension-name fn :body dimension) actuals)
           (fn-cost-get (fn-cost-dimension-key :unaccounted dimension)
                        (cdr (assoc-eq fn (table-alist 'fn-cost w))))))
      ((and body
            (not (eq (symbol-class fn w) :program))
            (not (member-eq fn stack))
            (not (fn-cost-recursivep fn w))
            (not (getpropc fn 'constrainedp nil w))
            (< (fn-cost-nodes body) *fn-cost-inline-nodes*)
            (not (zp fuel)))
       ; inlined: the callee's derived cost with the actuals for its formals
       (mv-let (c u) (fn-cost-term-dimension body self (cons fn stack) (1- fuel) w dimension)
         (if u
             (mv (list (fn-cost-unknown-name dimension) (kwote fn) (cons 'list actuals)) (list fn))
           (mv (fn-cd-subst c (pairlis$ (getpropc fn 'formals nil w) actuals)) nil))))
      (t (mv (list (fn-cost-unknown-name dimension) (kwote fn) (cons 'list actuals)) (list fn)))))))
(defun fn-cost-call-count-callee (fn actuals self stack fuel w dimension)
 (declare (xargs :mode :program))
 (let* ((targets (caddr dimension)) (boundaries (cadddr dimension)) (argument (car (cddddr dimension))) (tag (cadr dimension))
        (row (cdr (assoc-equal (list fn tag) (table-alist 'fn-cost-call-counts w))))
        (body (getpropc fn 'unnormalized-body nil w))
        (reach (fn-cost-call-reach (list fn) nil nil targets boundaries w))
        (unknown (list 'fn-cost-unaccounted (kwote (cons tag fn)) (cons 'list actuals))))
  (cond ((member-eq fn targets)
         (mv (if (natp argument) (list 'nfix (nth argument actuals)) ''1) nil))
        ((member-eq fn boundaries) (mv ''0 nil))
        ((eq reach :none) (mv ''0 nil))
        ((eq fn self) (mv (cons (fn-cost-dimension-name fn :body dimension) actuals) nil))
        ((and row (equal targets (fn-cost-get :targets row))
                   (equal boundaries (fn-cost-get :stop-at row))
                   (equal argument (fn-cost-get :argument row)))
         (mv (cons (fn-cost-get :twin row) actuals) (fn-cost-get :unaccounted row)))
        ((and body (not (eq (symbol-class fn w) :program))
              (not (getpropc fn 'constrainedp nil w))
              (not (member-eq fn stack)) (not (fn-cost-recursivep fn w))
              (< (fn-cost-nodes body) *fn-cost-inline-nodes*) (not (zp fuel)))
         (mv-let (cost un) (fn-cost-term-dimension body self (cons fn stack) (1- fuel) w dimension)
          (mv (fn-cd-subst cost (pairlis$ (getpropc fn 'formals nil w) actuals)) un)))
        (t (mv unknown (list fn))))))
)


(defun fn-cost-term (term self stack fuel w)
  (declare (xargs :mode :program))
  (fn-cost-term-dimension term self stack fuel w :visits))
(defun fn-cost-terms (terms self stack fuel w)
  (declare (xargs :mode :program))
  (fn-cost-terms-dimension terms self stack fuel w :visits))
(defun fn-cost-call (fn actuals self stack fuel w)
  (declare (xargs :mode :program))
  (fn-cost-call-dimension fn actuals self stack fuel w :visits))

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
          ((or (assoc-keyword :raw-with (cdr entry))
               (assoc-keyword :raw-guarded (cdr entry))) :raw)
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

(defun fn-cost-derive-dimension (fn w dimension)
  (declare (xargs :mode :program))
  ; (mv MSG ROUTE ROUTE-COST BODY-COST UNACCOUNTED): what the host evaluates
  ; before the body on the entry's route (kinds; the rest of the guard when
  ; served), and the body, over the original formals
  (let ((route (fn-cost-route fn w)))
    (mv-let (kinds rest)
      (fn-cost-guard-parts fn w)
      (mv-let (kcost kun) (fn-cost-terms-dimension (if (eq route :internal) nil kinds) fn nil *fn-cost-fuel* w dimension)
        (mv-let (rcost run) (fn-cost-terms-dimension (if (eq route :served) rest nil) fn nil *fn-cost-fuel* w dimension)
          (mv-let (bcost bun) (fn-cost-term-dimension (getpropc fn 'unnormalized-body nil w) fn nil *fn-cost-fuel* w dimension)
            (let ((size (and (eq route :served)
                             (fn-cost-mentions rcost *fn-cost-whole-state-sizes*))))
              (if size
                  (mv (msg "~x0 is a served entry (fn-interfaces, no raw declaration) whose guard ~
                            the counterpart evaluates on every call, and that guard's ~
                            derived cost depends on ~x1, a whole-state size: the walk ~
                            AGENTS.md forbids on a served path.  It is not charged: carry ~
                            the relation (def-carried) and dispatch raw, or move the check ~
                            off the served route" fn size)
                      route nil nil nil)
                (mv nil route (fn-cost-plus kcost rcost) bcost
                    (union-eq kun (union-eq run bun)))))))))))

(defun fn-cost-derive (fn w)
  (declare (xargs :mode :program))
  (fn-cost-derive-dimension fn w :visits))

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

(defun fn-cost-twin-row (twin rows)
  (declare (xargs :mode :program))
  (cond ((atom rows) nil)
        ((or (eq twin (fn-cost-get :twin (cdar rows)))
             (eq twin (fn-cost-get :cons-twin (cdar rows)))) (car rows))
        (t (fn-cost-twin-row twin (cdr rows)))))

(mutual-recursion
 (defun fn-cost-unaccounted-walk (term w path)
   (declare (xargs :mode :program))
   ; Return the first recursive partial callee and the bag of finite leaves.
   ; PATH contains only row expansions on this path, not sibling occurrences.
   ; Actual costs and every occurrence (including both IF arms) remain separate.
   (cond
    ((or (atom term) (eq (car term) 'quote)) (mv nil nil))
    ((member-eq (car term) '(fn-cost-unaccounted fn-cost-unaccounted-conses))
     (mv nil (list term)))
    ((consp (car term))
     (mv-let (bad body-terms)
       (fn-cost-unaccounted-walk (car (last (car term))) w path)
       (mv-let (abad actual-terms)
         (fn-cost-unaccounted-walk-lst (cdr term) w path)
         (mv (or bad abad)
             (append (sublis-var-lst (pairlis$ (cadr (car term)) (cdr term)) body-terms)
                     actual-terms)))))
    (t
     (let* ((entry (fn-cost-twin-row (car term) (table-alist 'fn-cost w)))
            (row (cdr entry))
            (conses (and entry (eq (car term) (fn-cost-get :cons-twin row)))))
       (mv-let (abad actual-terms)
         (fn-cost-unaccounted-walk-lst (cdr term) w path)
         (cond
          ((not entry) (mv abad actual-terms))
          ((or (fn-cost-recursivep (car entry) w)
               (member-eq (car entry) path))
           (mv (or (and (fn-cost-get (if conses :cons-unaccounted :unaccounted) row)
                        (car entry)) abad)
               actual-terms))
          (t
           (mv-let (bad body-terms)
             (fn-cost-unaccounted-walk
              (fn-cost-get (if conses :cons-body-cost :body-cost) row)
              w (cons (car entry) path))
             (mv (or bad abad)
                 (append (sublis-var-lst
                          (pairlis$ (getpropc (car entry) 'formals nil w) (cdr term))
                          body-terms)
                         actual-terms))))))))))
 (defun fn-cost-unaccounted-walk-lst (terms w path)
   (declare (xargs :mode :program))
   (if (atom terms) (mv nil nil)
     (mv-let (bad leaves)
       (fn-cost-unaccounted-walk (car terms) w path)
       (mv-let (rest-bad rest-leaves)
         (fn-cost-unaccounted-walk-lst (cdr terms) w path)
         (mv (or bad rest-bad) (append leaves rest-leaves)))))))

(defun fn-cost-unaccounted-terms (term w)
  (declare (xargs :mode :program))
  (mv-let (bad terms) (fn-cost-unaccounted-walk term w nil)
    (declare (ignore bad))
    terms))

(defun fn-cost-unaccounted-terms-lst (terms w)
  (declare (xargs :mode :program))
  (mv-let (bad leaves) (fn-cost-unaccounted-walk-lst terms w nil)
    (declare (ignore bad))
    leaves))

(defun fn-cost-problem-dimension (fn kvs w dimension)
  (declare (xargs :mode :program))
  ; (mv MSG ROUTE (ROUTE-COST . BODY-COST) UNACCOUNTED SIZES BOUND)
  (let ((sizes (fn-cost-get :sizes kvs))
        (bound (fn-cost-get (fn-cost-dimension-key :visits dimension) kvs)))
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
     ((and (assoc-eq fn (table-alist 'fn-cost w))
            (or (not (eq dimension :conses))
                (fn-cost-get :cons-twin (cdr (assoc-eq fn (table-alist 'fn-cost w))))))
      (mv (msg "~x0 already has a cost row; a row is declared once" fn) nil nil nil nil nil))
     ((or (getpropc (fn-cost-dimension-name fn :body dimension) 'formals nil w)
          (getpropc (fn-cost-dimension-name fn :route dimension) 'formals nil w))
      (mv (msg "~x0: ~x1 or ~x2 is already a function of this world"
               fn (fn-cost-dimension-name fn :body dimension) (fn-cost-dimension-name fn :route dimension))
          nil nil nil nil nil))
     ((not (fn-cost-sizesp sizes))
      (mv (msg "~x0: :sizes ~x1 is not ((S TERM) ...)" fn sizes) nil nil nil nil nil))
     ((and (assoc-keyword (fn-cost-dimension-key :visits dimension) kvs) (null bound))
      (mv (msg "~x0: :visits names no bound" fn) nil nil nil nil nil))
     ((not (true-listp (fn-cost-get (fn-cost-dimension-key :unaccounted dimension) kvs)))
      (mv (msg "~x0: :unaccounted ~x1 is not a list" fn (fn-cost-get (fn-cost-dimension-key :unaccounted dimension) kvs))
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
                (fn-cost-derive-dimension fn w dimension)
                (mv-let (recursive-callee us)
                  (fn-cost-unaccounted-walk-lst (list rcost bcost) w nil)
                (cond
                 (msg (mv msg nil nil nil nil nil))
                 ((and bound recursive-callee)
                  (mv (msg "~x0: ~x1's twin recurs over unaccounted leaves, so no finite ~
                            partial bound exists; give the callee a :visits bound"
                           fn recursive-callee)
                      nil nil nil nil nil))
                 ((not (subsetp-eq
                        (all-vars1-lst us nil)
                        (getpropc fn 'formals nil w)))
                  (mv (msg "~x0: unaccounted cost terms ~x1 have free variables outside formals ~x2"
                           fn us
                           (getpropc fn 'formals nil w))
                      nil nil nil nil nil))
                 ((not (and (subsetp-eq unaccounted (fn-cost-get (fn-cost-dimension-key :unaccounted dimension) kvs))
                            (subsetp-eq (fn-cost-get (fn-cost-dimension-key :unaccounted dimension) kvs) unaccounted)))
                  (mv (msg "~x0: the derivation leaves ~&1 unaccounted (no contract, no ~
                            cost row, not inlinable); the declaration says ~x2.  Declare ~
                            exactly the derived list: a bound is partial over it"
                           fn unaccounted (fn-cost-get (fn-cost-dimension-key :unaccounted dimension) kvs))
                      nil nil nil nil nil))
                 (t (mv nil route (cons rcost bcost) unaccounted
                        (pairlis$ (strip-cars sizes) (pairlis$ sterms nil))
                        (and bound (car bterms)))))))))))))))))

(defun fn-cost-problem (fn kvs w)
  (declare (xargs :mode :program))
  (fn-cost-problem-dimension fn kvs w :visits))

(defun fn-cost-sizes-alist (sizes)
  (declare (xargs :mode :program))
  ; ((S . TERM) ...) from the normalized ((S (TERM)) ...)
  (if (atom sizes) nil (cons (cons (caar sizes) (car (cdar sizes))) (fn-cost-sizes-alist (cdr sizes)))))

(mutual-recursion
 (defun fn-cost-value-term (term w)
   (declare (xargs :mode :program))
   ; Translated MV-LET binds the complete MV list as a lambda actual.
   ; Reconstructed source must explicitly collect that list: ACL2 refuses
   ; an ordinary value-context call to a multiple-value function.
   (cond ((or (atom term) (eq (car term) 'quote)) term)
         ((consp (car term))
          (cons (list 'lambda (cadr (car term))
                      (fn-cost-value-term (car (last (car term))) w))
                (fn-cost-value-terms (cdr term) w)))
         (t (let* ((call (cons (car term) (fn-cost-value-terms (cdr term) w)))
                   (outs (getpropc (car term) 'stobjs-out nil w)))
              (if (< 1 (len outs)) (list 'mv-list (len outs) call) call)))))
 (defun fn-cost-value-terms (terms w)
   (declare (xargs :mode :program))
   (if (atom terms) nil
     (cons (fn-cost-value-term (car terms) w)
           (fn-cost-value-terms (cdr terms) w)))))

(defun fn-cost-events-dimension (fn kvs route cost unaccounted sizes bound w dimension)
  (declare (xargs :mode :program))
  ; COST = (ROUTE-COST . BODY-COST): NAME-visits is the body's twin (recurring
  ; as the body does); NAME-route-visits adds what the host evaluates once at
  ; the entry, so a kind check is never counted per recursive call
  (let* ((alist (fn-cost-stobj-alist fn w))
         (formals (fn-cost-rename (getpropc fn 'formals nil w) alist))
         (twin (fn-cost-dimension-name fn :body dimension))
         (rtwin (fn-cost-dimension-name fn :route dimension))
         (rcost (fn-cost-value-term (fn-cd-subst (car cost) alist) w))
         (bcost (fn-cost-value-term (fn-cd-subst (cdr cost) alist) w))
         (recursive (fn-cost-mentions (cdr cost) (list twin)))
         (j (getpropc fn 'justification nil w))
         (measure (and recursive j (fn-cd-subst (access justification j :measure) alist)))
         (rel (and recursive j (access justification j :rel)))
         (guard (fn-cd-subst (getpropc fn 'guard *t* w) alist))
         (us (append (fn-cost-unaccounted-terms rcost w) (fn-cost-unaccounted-terms bcost w)))
         (bound-term (and bound
                          (fn-cost-sum (cons (fn-cd-subst (fn-cd-subst bound (fn-cost-sizes-alist sizes)) alist)
                                             us))))
         (stobjs (strip-cars alist))
         (def (if stobjs 'defun-nx 'defun))
         (name (fn-cost-dimension-name fn :bound dimension)))
    `(progn
       (,def ,twin ,formals
        (declare ,@(and formals `((ignorable ,@formals)))
                 (xargs :verify-guards nil
                        ,@(and measure (list :measure measure))
                        ,@(and rel (list :well-founded-relation rel))
                        ,@(and recursive (list :ruler-extenders :all))
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
                  :hints ,(if (assoc-keyword (fn-cost-dimension-key :hints dimension) kvs)
                              (fn-cost-get (fn-cost-dimension-key :hints dimension) kvs)
                            `(("Goal" :in-theory (enable ,twin ,rtwin)
                               ,@(and recursive (list :induct (cons twin formals)))))))))
       (table fn-cost ',fn
              ',(if (eq dimension :conses)
                    (append `(:cons-twin ,twin :cons-route-twin ,rtwin
                              :cons-route-cost ,(car cost) :cons-body-cost ,(cdr cost)
                              :cons-unaccounted ,unaccounted :cons-bound ,bound
                              :cons-theorem ,(and bound name) :allocation :logical-conses)
                            (cdr (assoc-eq fn (table-alist 'fn-cost w))))
                  `(:route ,route :twin ,twin :route-twin ,rtwin
                    :route-cost ,(car cost) :body-cost ,(cdr cost) :unaccounted ,unaccounted
                    :sizes ,(fn-cost-sizes-alist sizes) :bound ,bound
                    :theorem ,(and bound name) :allocation :deferred)))
       ,@(and bound
              `((table fn-teeth-owed ',name
                       '(:by def-cost
                         :claim (,(if (equal guard *t*) nil `((g ,guard)))
                                 (<= (,rtwin ,@formals) ,bound-term))
                         :subject ,fn
                         ,(if (eq dimension :conses) :conses :visits)
                         ((route (,rtwin ,@formals) ,bound-term)))))))))

(defun fn-cost-events (fn kvs route cost unaccounted sizes bound w)
  (declare (xargs :mode :program))
  (fn-cost-events-dimension fn kvs route cost unaccounted sizes bound w :visits))

; Derived logical call coordinates; the ordinary visit/allocation derivations remain intact.
(defun fn-cost-call-targets-problem (targets w)
 (declare (xargs :mode :program))
 (if (atom targets) (and targets (msg "targets must be a proper list"))
  (let ((fn (car targets)))
   (cond ((or (not (symbolp fn)) (member-eq fn '(if quote return-last))
              (eq (getpropc fn 'formals :none w) :none)
              (eq (symbol-class fn w) :program))
          (msg "marked target ~x0 is not an executable logical function" fn))
         (t (fn-cost-call-targets-problem (cdr targets) w))))))

(defun fn-cost-call-signature (targets boundaries argument)
 (declare (xargs :mode :program))
 (if (or boundaries (natp argument))
     (list :targets targets :stop-at boundaries :argument argument) targets))

(defun fn-cost-call-argument-problem (targets argument w)
 (declare (xargs :mode :program))
 (if (atom targets) nil
  (if (< argument (len (getpropc (car targets) 'formals nil w)))
   (fn-cost-call-argument-problem (cdr targets) argument w)
   (msg "argument ~x0 is outside marked target ~x1's arity" argument (car targets)))))

(defun fn-cost-call-spec-problem (fn spec w)
 (declare (xargs :mode :program))
 (let ((tag (car spec)) (targets (cadr spec)))
  (cond ((not (and (true-listp spec) (symbolp tag) tag (consp targets)
                   (true-listp targets) (symbol-listp targets) (no-duplicatesp-eq targets)
                   (keyword-value-listp (cddr spec))))
         (msg "call count must be (TAG (TARGET...) [:unaccounted (...) :measure-hints H :stop-at (FN...) :argument N])"))
        ((fn-cd-unknown-keys (cddr spec) '(:unaccounted :measure-hints :stop-at :argument))
         (msg "unknown call count keyword(s): ~x0" (fn-cd-unknown-keys (cddr spec) '(:unaccounted :measure-hints :stop-at :argument))))
        ((and (assoc-keyword :argument (cddr spec))
              (not (natp (fn-cost-get :argument (cddr spec)))))
         (msg ":argument must be a zero-based natural argument index"))
        ((and (assoc-keyword :argument (cddr spec))
              (fn-cost-call-argument-problem targets (fn-cost-get :argument (cddr spec)) w))
         (fn-cost-call-argument-problem targets (fn-cost-get :argument (cddr spec)) w))
        ((not (and (true-listp (fn-cost-get :stop-at (cddr spec)))
                    (symbol-listp (fn-cost-get :stop-at (cddr spec)))
                    (no-duplicatesp-eq (fn-cost-get :stop-at (cddr spec)))))
         (msg ":stop-at must be a proper duplicate-free list of logical callees"))
        ((intersectp-eq targets (fn-cost-get :stop-at (cddr spec)))
         (msg "a counted target cannot also be a stopped boundary"))
        ((not (true-listp (fn-cost-get :unaccounted (cddr spec))))
         (msg "call count :unaccounted must be a proper list"))
        ((member-eq tag '(visits route-visits conses route-conses visits-bound conses-bound))
         (msg "call tag ~x0 collides with a standard cost coordinate" tag))
        (t
         (let* ((key (list fn tag))
                (oldtargets (cdr (assoc-eq tag (table-alist 'fn-cost-call-tags w))))
                (twin (fn-cost-dimension-name fn :body (list :calls tag targets))))
          (cond ((assoc-equal key (table-alist 'fn-cost-call-counts w))
                 (msg "~x0 already has call coordinate ~x1" fn tag))
                ((not (eq (getpropc twin 'formals :none w) :none))
                 (msg "generated call twin ~x0 already exists" twin))
                ((and oldtargets (not (equal oldtargets (fn-cost-call-signature targets (fn-cost-get :stop-at (cddr spec)) (fn-cost-get :argument (cddr spec))))))
                 (msg "call tag ~x0 has different marked targets in this world" tag))
                (t (or (fn-cost-call-targets-problem targets w)
                       (fn-cost-call-targets-problem (fn-cost-get :stop-at (cddr spec)) w)))))))))

(defun fn-cost-call-events-one (fn spec w)
 (declare (xargs :mode :program))
 (let* ((problem (fn-cost-call-spec-problem fn spec w))
        (tag (car spec)) (targets (cadr spec))
        (boundaries (fn-cost-get :stop-at (cddr spec)))
        (argument (fn-cost-get :argument (cddr spec)))
        (dimension (list :calls tag targets boundaries argument))
        (twin (fn-cost-dimension-name fn :body dimension))
        (alist (fn-cost-stobj-alist fn w))
        (formals (fn-cost-rename (getpropc fn 'formals nil w) alist))
        (j (getpropc fn 'justification nil w))
        (measure (and j (fn-cd-subst (access justification j :measure) alist)))
        (rel (and j (access justification j :rel)))
        (def (if alist 'defun-nx 'defun)))
  (if problem (mv problem nil)
   (mv-let (cost un)
    (fn-cost-term-dimension (getpropc fn 'unnormalized-body nil w)
                     fn nil *fn-cost-fuel* w dimension)
    (if (not (and (subsetp-eq un (fn-cost-get :unaccounted (cddr spec)))
                  (subsetp-eq (fn-cost-get :unaccounted (cddr spec)) un)))
     (mv (msg "~x0 call coordinate ~x1 has unaccounted callees ~x2; declaration says ~x3"
               fn tag un (fn-cost-get :unaccounted (cddr spec))) nil)
     (mv nil
      `((,def ,twin ,formals
          (declare ,@(and formals `((ignorable ,@formals)))
                   (xargs :verify-guards nil
                     ,@(and measure (fn-cost-mentions cost (list twin)) (list :measure measure))
                     ,@(and rel (fn-cost-mentions cost (list twin)) (list :well-founded-relation rel))
                     ,@(and j (fn-cost-mentions cost (list twin)) (list :ruler-extenders :all))
                     ,@(and (fn-cost-get :measure-hints (cddr spec))
                       (list :hints (fn-cost-get :measure-hints (cddr spec))))))
          ,(fn-cost-value-term (fn-cd-subst cost alist) w))
        (table fn-cost-call-tags ',tag ',(fn-cost-call-signature targets boundaries argument))
        (table fn-cost-call-counts '(,fn ,tag)
         '(:targets ,targets :stop-at ,boundaries :argument ,argument :twin ,twin :body-cost ,cost :unaccounted ,un
           :formals ,(getpropc fn 'formals nil w)
           :source-body ,(getpropc fn 'unnormalized-body nil w)
           :coordinate :logical-calls)))))))))

(defun fn-cost-call-events-list (fn specs w)
 (declare (xargs :mode :program))
 (if (atom specs)
  (if specs (mv (msg ":calls must be a proper list") nil) (mv nil nil))
  (mv-let (problem one) (fn-cost-call-events-one fn (car specs) w)
   (if problem (mv problem nil)
    (mv-let (problem rest) (fn-cost-call-events-list fn (cdr specs) w)
     (if problem (mv problem nil) (mv nil (append one rest))))))))

(defun fn-cost-call-check-rows (fn rows w)
 (declare (xargs :mode :program))
 (if (atom rows) nil
  (let* ((key (caar rows)) (row (cdar rows)) (tag (cadr key)))
   (if (not (eq (car key) fn)) (fn-cost-call-check-rows fn (cdr rows) w)
    (mv-let (cost un)
     (fn-cost-term-dimension (getpropc fn 'unnormalized-body nil w) fn nil *fn-cost-fuel* w
                      (list :calls tag (fn-cost-get :targets row) (fn-cost-get :stop-at row) (fn-cost-get :argument row)))
     (cond ((not (equal (fn-cost-call-signature (fn-cost-get :targets row) (fn-cost-get :stop-at row) (fn-cost-get :argument row))
                              (cdr (assoc-eq tag (table-alist 'fn-cost-call-tags w)))))
            (msg "~x0 call coordinate ~x1 disagrees with its canonical targets" fn tag))
           ((fn-cost-call-targets-problem (fn-cost-get :targets row) w)
            (fn-cost-call-targets-problem (fn-cost-get :targets row) w))
           ((or (fn-cost-call-targets-problem (fn-cost-get :stop-at row) w)
                (intersectp-eq (fn-cost-get :targets row) (fn-cost-get :stop-at row)))
            (msg "~x0 call coordinate ~x1 has invalid stopped boundaries" fn tag))
           ((and (fn-cost-get :argument row)
                 (or (not (natp (fn-cost-get :argument row)))
                     (fn-cost-call-argument-problem (fn-cost-get :targets row) (fn-cost-get :argument row) w)))
            (msg "~x0 call coordinate ~x1 has an invalid argument index" fn tag))
           ((not (equal (fn-cost-get :source-body row) (getpropc fn 'unnormalized-body nil w)))
            (msg "~x0 call coordinate ~x1 has stale source body" fn tag))
           ((not (equal (fn-cost-get :formals row) (getpropc fn 'formals nil w)))
            (msg "~x0 call coordinate ~x1 has stale formals" fn tag))
           ((not (equal (fn-cost-get :twin row) (fn-cost-dimension-name fn :body (list :calls tag nil))))
            (msg "~x0 call coordinate ~x1 names the wrong twin" fn tag))
           ((not (and (equal cost (fn-cost-get :body-cost row))
                      (subsetp-eq un (fn-cost-get :unaccounted row))
                      (subsetp-eq (fn-cost-get :unaccounted row) un)))
            (msg "~x0 call coordinate ~x1 no longer derives from this world" fn tag))
           (t (fn-cost-call-check-rows fn (cdr rows) w))))))))

(defun fn-cost-call-events (fn specs w)
 (declare (xargs :mode :program))
 (cond ((not (true-listp specs)) (mv (msg ":calls must be a proper list") nil))
       ((not (no-duplicatesp-eq (strip-cars specs)))
        (mv (msg "a call tag is declared twice for ~x0" fn) nil))
       (t (fn-cost-call-events-list fn specs w))))
(defun fn-cost-call-check-problem (fn w)
 (declare (xargs :mode :program))
 (fn-cost-call-check-rows fn (table-alist 'fn-cost-call-counts w) w))
(defun fn-cost-call-orphans-problem (rows w)
 (declare (xargs :mode :program))
 (if (atom rows) nil
  (let ((key (caar rows)))
   (if (and (true-listp key) (equal (len key) 2)
            (assoc-eq (car key) (table-alist 'fn-cost w)))
    (fn-cost-call-orphans-problem (cdr rows) w)
    (msg "call coordinate ~x0 has no ordinary def-cost row" key)))))


(defmacro def-cost (fn &rest kvs)
  `(progn
     (make-event
      (mv-let (problem route cost unaccounted sizes bound)
        (fn-cost-problem ',fn ',kvs (w state))
        (if problem
            (er soft 'def-cost "~x0: ~@1" ',fn problem)
          (mv-let (call-problem call-events)
            (fn-cost-call-events ',fn (fn-cost-get :calls ',kvs) (w state))
            (if call-problem (er soft 'def-cost "~x0: ~@1" ',fn call-problem)
              (value (cons 'progn
                       (cons (fn-cost-events ',fn ',kvs route cost unaccounted sizes bound (w state))
                             call-events))))))))
     ,@(and (or (assoc-keyword :conses kvs) (assoc-keyword :cons-unaccounted kvs))
            `((make-event
               (mv-let (problem route cost unaccounted sizes bound)
                 (fn-cost-problem-dimension ',fn ',kvs (w state) :conses)
                 (if problem
                     (er soft 'def-cost "~x0 logical conses: ~@1" ',fn problem)
                   (value (fn-cost-events-dimension ',fn ',kvs route cost unaccounted
                                                     sizes bound (w state) :conses)))))))))

; Re-derive in the current world and compare with the row: a changed body,
; guard or interface declaration refuses.
(defun fn-cost-check-problem (fn w)
  (declare (xargs :mode :program))
  (let ((ordinary-problem (let ((row (cdr (assoc-eq fn (table-alist 'fn-cost w)))))
    (if (null row)
        (msg "no cost row for ~x0 in this world" fn)
      (mv-let (msg route rcost bcost unaccounted)
        (fn-cost-derive fn w)
        (cond (msg (msg "~x0: ~@1" fn msg))
              ((not (eq route (fn-cost-get :route row)))
               (msg "~x0: the route is now ~x1, the row says ~x2"
                    fn route (fn-cost-get :route row)))
              ((not (and (equal rcost (fn-cost-get :route-cost row))
                         (equal bcost (fn-cost-get :body-cost row))))
               (msg "~x0: the derived cost is now ~x1 at the entry and ~
                          ~x2 in the body; the row holds ~x3 and ~x4"
                    fn rcost bcost (fn-cost-get :route-cost row) (fn-cost-get :body-cost row)))
              ((not (and (subsetp-eq unaccounted (fn-cost-get :unaccounted row))
                         (subsetp-eq (fn-cost-get :unaccounted row) unaccounted)))
               (msg "~x0: the unaccounted callees are now ~x1; the row says ~x2"
                    fn unaccounted (fn-cost-get :unaccounted row)))
              (t
               (if (not (fn-cost-get :cons-twin row))
                   nil
                 (mv-let (cmsg croute crc cbc cun)
                   (fn-cost-derive-dimension fn w :conses)
                   (if (and (null cmsg) (eq croute route)
                            (equal crc (fn-cost-get :cons-route-cost row))
                            (equal cbc (fn-cost-get :cons-body-cost row))
                            (subsetp-eq cun (fn-cost-get :cons-unaccounted row))
                            (subsetp-eq (fn-cost-get :cons-unaccounted row) cun))
                       nil
                     (msg "~x0: logical cons derivation changed" fn)))))))))))
    (or ordinary-problem (fn-cost-call-check-problem fn w))))

(defmacro def-cost-check (fn)
  `(make-event
    (let ((problem (fn-cost-check-problem ',fn (w state))))
      (if problem
          (er soft 'def-cost-check "~@0" problem)
        (value '(value-triple ',fn))))))

(defun fn-cost-check-all-problem (rows w)
  (declare (xargs :mode :program))
  (if (atom rows) nil
    (let ((problem (fn-cost-check-problem (caar rows) w))
          (rest (fn-cost-check-all-problem (cdr rows) w)))
      (cond ((and problem rest) (msg "~@0~%~@1" problem rest))
            (problem problem)
            (t rest)))))

(defmacro def-cost-check-all ()
  `(make-event
    (let* ((rows (table-alist 'fn-cost (w state)))
           (problem (or (fn-cost-call-orphans-problem (table-alist 'fn-cost-call-counts (w state)) (w state))
                        (fn-cost-check-all-problem rows (w state)))))
      (if problem
          (er soft 'def-cost-check-all "~@0" problem)
        (value `(value-triple ,(len rows)))))))

; The operation validator runs after costs exist, so the entry route was
; read from its final interface declaration.  It consumes the one existing
; derivation; there is no second user-written visit count or tariff bound.
(mutual-recursion
 (defun fn-cost-operation-drawp (term draw slot tariff)
   (declare (xargs :mode :program))
   (cond ((or (atom term) (eq (car term) 'quote)) nil)
         ((consp (car term))
          (or (fn-cost-operation-drawp (car (last (car term))) draw slot tariff)
              (fn-cost-operation-draws-p (cdr term) draw slot tariff)))
         (t (or (and (eq (car term) draw)
                     (equal (cadr term) (list 'quote slot))
                     (member-eq tariff (fn-cost-calls (caddr term))))
                (fn-cost-operation-draws-p (cdr term) draw slot tariff)))))
 (defun fn-cost-operation-draws-p (terms draw slot tariff)
   (declare (xargs :mode :program))
   (if (atom terms) nil
     (or (fn-cost-operation-drawp (car terms) draw slot tariff)
         (fn-cost-operation-draws-p (cdr terms) draw slot tariff)))))

(defun fn-cost-operation-bad-function (fns w)
  (declare (xargs :mode :program))
  (cond ((atom fns) nil)
        ((or (eq (getpropc (car fns) 'formals :none w) :none)
             (eq (symbol-class (car fns) w) :program)) (car fns))
        (t (fn-cost-operation-bad-function (cdr fns) w))))

(defun fn-cost-operation-problem (fn w)
  (declare (xargs :mode :program))
  (let* ((entry (cdr (assoc-eq fn (table-alist 'fn-interfaces w))))
         (op (fn-di-get :operation entry))
         (row (cdr (assoc-eq fn (table-alist 'fn-cost w))))
         (coordinates (cadr (getpropc '*fn-rv-coordinates* 'const nil w)))
         (fns (list (fn-di-get :funding op) (fn-di-get :tariff op)
                    (fn-di-get :draw op) (fn-di-get :physical op)
                    (fn-di-get :outcome op))))
    (cond ((not (fn-di-operation-formp op)) (msg "~x0 has no well-formed :operation" fn))
          ((null row) (msg "~x0 has no derived cost row" fn))
          ((not (and (subsetp-eq (fn-di-get :unaccounted op) (fn-cost-get :unaccounted row))
                     (subsetp-eq (fn-cost-get :unaccounted row) (fn-di-get :unaccounted op))))
           (msg "~x0's operation hides or invents unresolved cost dependencies" fn))
          ((not (subsetp-eq (fn-di-get :coverage op) (strip-cars coordinates)))
           (msg "~x0's operation names an unknown resource coordinate" fn))
          ((not (fn-cost-operation-drawp (getpropc fn 'unnormalized-body nil w)
                                         (fn-di-get :draw op) (fn-di-get :slot op)
                                         (fn-di-get :tariff op)))
           (msg "~x0's declared draw, fixed slot and tariff do not match its executed body" fn))
          ((eq (fn-di-get :stage op) :accounted)
           ; Allocation derivation/refusal tariff and full principal/tree
           ; correspondence are still owed.  A partial slice cannot enable
           ; the image's full cost admission gate by changing an annotation.
           (msg "~x0: full operation accounting is owed; :projection cannot enable a full tariff gate" fn))
          (t
           (let ((bad (fn-cost-operation-bad-function fns w)))
             (and bad (msg "~x0's operation dependency ~x1 is not an executable logical function" fn bad)))))))

(defmacro def-operation-check (fn)
  `(progn
     (def-cost-check ,fn)
     (make-event
      (let ((problem (fn-cost-operation-problem ',fn (w state))))
        (if problem (er soft 'def-operation-check "~@0" problem)
          (value '(value-triple :operation-projection-checked)))))))
