; fn: `def-carried' --- a carried invariant from one declaration: the
; obligation table checked complete in the world, the trace theorem by
; functional instantiation of a generic theory, and the rows D40's raw
; dispatch consumes (planning/design-store-representation-2026-10-01.md
; section 3; build/coordinator/scholar-proof-engineering-2026-10-01.md 2.3).
;
; AGENTS.md: "No whole-state revalidation on a served path: carry the
; invariant in state and prove it preserved."  Until this book the carrying
; argument -- "established at every host-called open, preserved by every
; transition the host installs" -- was a hand-maintained COMMENT table
; (books/owner-host-relation.lisp COVERAGE, 35 rows) and D40's `:raw-with'
; lists were to be copied from it by hand.  Here the table is one form,
; checked against the WORLD when it is admitted:
;
;   (def-carried NAME
;     :invariant R                      ; the carried relation: a function of
;                                       ; one formal, the carried state
;     :established ((FN THM) ...)       ; where the host first obtains a
;                                       ; state satisfying R, and the theorem
;                                       ; concluding (R <... (FN ...) ...>)
;     :transitions ((FN THM) | FN ...)  ; every transition the host installs
;                                       ; and its preservation theorem; a
;                                       ; bare FN is an obligation still owed
;                                       ; and is REFUSED with the statement
;     [:concludes ((PRED THM) ...)]     ; the bridges: R implies a guard
;                                       ; predicate the entry guard carries
;     [:writers (W ...)]                ; the functions that write the
;                                       ; carried state (an installer, a
;                                       ; global's put): completeness, below
;     [:trace t | nil | :if-shaped])    ; the trace theorem (default
;                                       ; :if-shaped)
;
; Admitted, it checks:
;
;   * R is a function of exactly one formal;
;   * every named THM is a theorem of this world.  A transition theorem is
;     (implies H C) with a conjunct of H applying R, C applying R, and FN
;     called in C -- the carrying shape; an establishing theorem concludes
;     R of a term that calls FN; a bridge theorem has R among its
;     hypotheses' heads and PRED among its conclusion's conjuncts' heads;
;   * a transition with no theorem is refused, and the refusal states the
;     obligation (the statement to prove and name);
;   * COMPLETENESS: every entry of the `fn-interfaces' table
;     (books/definterface.lisp: the host-called entries) whose call closure
;     reaches a writer is a listed transition or establishing point.  A
;     host-called function that mutates the carried state and has no
;     theorem is refused BY NAME.  The table is complete only where the
;     declarations are loaded (the image world, host/interfaces.lisp), so
;     `(def-carried-check NAME)' re-runs the same check there.
;
; Emits:
;
;   (table fn-carried NAME '(:invariant R :established ... :transitions ...
;                            :concludes ... :writers ... :trace t|nil))
;
; and, when every transition theorem has the SHAPE
;   (implies (and H1 ... Hk) (R TERM)), with TERM calling FN once on distinct
;   variables that are all of TERM's variables, one Hi = (R s) for a variable
;   s of that call and the other Hi over those variables alone,
; the trace theorem by functional instantiation of the generic theory below:
;
;   (defun-nx NAME-step (s e) ...)      ; e = (FN . args): the transition's
;                                       ; carried state, R's argument in THM
;   (defun-nx NAME-okp (s e) ...)       ; THM's other hypotheses at e
;   (defun-nx NAME-run (s es) ...)      ; the trace
;   (defun-nx NAME-run-okp (s es) ...)
;   (defthm NAME-step-carries ...)      ; by :use of each transition theorem
;   (defthm NAME-run-carries            ; the instance of fn-cd-run-carries
;     (implies (and (R s) (NAME-run-okp s es)) (R (NAME-run s es))))
;
; NAME-run-carries is what "carried" means: along every trace of the listed
; transitions from a state satisfying R, R holds at every step -- so a
; served entry guarded by R may be dispatched raw (D40) without evaluating
; R.  The per-transition proofs stay by hand (they are the content); the
; generator fixes their statements, their completeness and the composition.
;
; The D40 row: `(fn-cd-raw-with NAME ENTRY w)' is the theorem list a
; `definterface' declaration `:raw-with (:carried NAME)' resolves to
; (books/definterface.lisp): the bridges, the establishing theorems and
; ENTRY's own preservation theorem; nil when ENTRY is not a transition of
; NAME.  So the annotation is DERIVED from the table, and D40's declaration
; lint becomes a completeness check over the world.
;
; What is NOT claimed: the trace theorem is over the listed transitions as
; ACL2 functions.  That the host calls nothing else that writes the carried
; state is the completeness check over `fn-interfaces' (every host-called
; entry is declared: tools/interface_emit.py refuses an undeclared dispatch),
; and that the entry guard runs before raw dispatch is host/native/io.lisp's.
;
; This book has no `include-book'; its helpers are `:program' mode, declared
; per defun.  The generic theory (fn-cd-inv, fn-cd-okp, fn-cd-step,
; fn-cd-run, fn-cd-run-okp, fn-cd-run-carries) is the one logic-mode part,
; and the export at the end leaves only fn-cd-run-carries enabled.

(in-package "ACL2")

; ---------------------------------------------------------------------------
; The generic theory: an invariant, a step admissible at a state, and the
; trace.  Proved once; every instance is a functional instantiation.

(encapsulate
  (((fn-cd-inv *) => *)
   ((fn-cd-okp * *) => *)
   ((fn-cd-step * *) => *))
  (local (defun fn-cd-inv (s) (declare (ignore s)) t))
  (local (defun fn-cd-okp (s e) (declare (ignore s e)) t))
  (local (defun fn-cd-step (s e) (declare (ignore e)) s))
  (defthm fn-cd-step-carries
    (implies (and (fn-cd-inv s) (fn-cd-okp s e))
             (fn-cd-inv (fn-cd-step s e)))))

(defun fn-cd-run (s es)
  (declare (xargs :measure (acl2-count es)))
  (if (atom es)
      s
    (fn-cd-run (fn-cd-step s (car es)) (cdr es))))

(defun fn-cd-run-okp (s es)
  (declare (xargs :measure (acl2-count es)))
  (if (atom es)
      t
    (and (fn-cd-okp s (car es))
         (fn-cd-run-okp (fn-cd-step s (car es)) (cdr es)))))

(defthm fn-cd-run-carries
  (implies (and (fn-cd-inv s) (fn-cd-run-okp s es))
           (fn-cd-inv (fn-cd-run s es)))
  :hints (("Goal" :induct (fn-cd-run s es)
           :in-theory (enable fn-cd-run fn-cd-run-okp))))

; ---------------------------------------------------------------------------
; The form.

(defconst *fn-cd-keys*
  '(:invariant :established :transitions :concludes :writers :trace))

(defun fn-cd-get (key kvs)
  (declare (xargs :mode :program))
  (cadr (assoc-keyword key kvs)))

(defun fn-cd-trace-mode (kvs)
  (declare (xargs :mode :program))
  (if (assoc-keyword :trace kvs) (fn-cd-get :trace kvs) :if-shaped))

(defun fn-cd-unknown-keys (kvs)
  (declare (xargs :mode :program))
  (cond ((atom kvs) nil)
        ((member-eq (car kvs) *fn-cd-keys*) (fn-cd-unknown-keys (cddr kvs)))
        (t (cons (car kvs) (fn-cd-unknown-keys (cddr kvs))))))

(defun fn-cd-pairp (x)
  (declare (xargs :mode :program))
  ; (SYM SYM), neither nil
  (and (true-listp x) (equal (len x) 2)
       (symbolp (car x)) (car x) (symbolp (cadr x)) (cadr x)))

(defun fn-cd-pairsp (x)
  (declare (xargs :mode :program))
  (if (atom x) (null x) (and (fn-cd-pairp (car x)) (fn-cd-pairsp (cdr x)))))

(defun fn-cd-transition-entriesp (x)
  (declare (xargs :mode :program))
  ; (SYM | (SYM SYM)) ...
  (if (atom x)
      (null x)
    (and (or (and (symbolp (car x)) (car x)) (fn-cd-pairp (car x)))
         (fn-cd-transition-entriesp (cdr x)))))

(defun fn-cd-first-bare (transitions)
  (declare (xargs :mode :program))
  (cond ((atom transitions) nil)
        ((symbolp (car transitions)) (car transitions))
        (t (fn-cd-first-bare (cdr transitions)))))

(defun fn-cd-refusal (name kvs)
  (declare (xargs :mode :program))
  ; nil when the form is well-formed; else (REASON . DETAILS)
  (cond
   ((not (and (symbolp name) name)) (list :bad-name name))
   ((not (keyword-value-listp kvs)) (list :bad-options kvs))
   ((fn-cd-unknown-keys kvs) (cons :unknown-keyword (fn-cd-unknown-keys kvs)))
   ((not (and (fn-cd-get :invariant kvs) (symbolp (fn-cd-get :invariant kvs))))
    (list :no-invariant name))
   ((not (fn-cd-pairsp (fn-cd-get :established kvs)))
    (list :bad-established (fn-cd-get :established kvs)))
   ((null (fn-cd-get :established kvs)) (list :no-established name))
   ((not (fn-cd-transition-entriesp (fn-cd-get :transitions kvs)))
    (list :bad-transitions (fn-cd-get :transitions kvs)))
   ((not (fn-cd-pairsp (fn-cd-get :concludes kvs)))
    (list :bad-concludes (fn-cd-get :concludes kvs)))
   ((not (symbol-listp (fn-cd-get :writers kvs)))
    (list :bad-writers (fn-cd-get :writers kvs)))
   ((not (member-eq (fn-cd-trace-mode kvs) '(t nil :if-shaped)))
    (list :bad-trace (fn-cd-trace-mode kvs)))
   (t nil)))

(defun fn-cd-refusal-text (reason)
  (declare (xargs :mode :program))
  (case (car reason)
    (:no-invariant (msg "~x0 has no :invariant: name the carried relation."
                        (cadr reason)))
    (:no-established (msg "~x0 has no :established ((FN THM) ...): a carried ~
                           invariant names where the host first obtains it."
                          (cadr reason)))
    (:bad-established (msg ":established ~x0 is not ((FN THM) ...)." (cadr reason)))
    (:bad-transitions (msg ":transitions ~x0 is not ((FN THM) | FN ...)." (cadr reason)))
    (:bad-concludes (msg ":concludes ~x0 is not ((PRED THM) ...)." (cadr reason)))
    (:bad-writers (msg ":writers ~x0 is not a list of function names." (cadr reason)))
    (:bad-trace (msg ":trace ~x0 is not t, nil or :if-shaped." (cadr reason)))
    (:unknown-keyword (msg "unknown keyword(s) ~&0; the keywords are ~&1."
                           (cdr reason) *fn-cd-keys*))
    (otherwise (msg "malformed form: ~x0." reason))))

; ---------------------------------------------------------------------------
; What the world says.

(defun fn-cd-conjuncts (term)
  (declare (xargs :mode :program))
  ; the conjuncts of a translated term ((if a b 'nil) is a conjunction)
  (if (and (consp term) (eq (car term) 'if) (equal (cadddr term) *nil*))
      (append (fn-cd-conjuncts (cadr term)) (fn-cd-conjuncts (caddr term)))
    (list term)))

(defun fn-cd-split (formula hyps)
  (declare (xargs :mode :program))
  ; (mv HYPS CONCLUSION) of (implies H1 (implies H2 ... C))
  (if (and (consp formula) (eq (car formula) 'implies))
      (fn-cd-split (caddr formula) (append hyps (fn-cd-conjuncts (cadr formula))))
    (mv hyps formula)))

(defun fn-cd-head (term)
  (declare (xargs :mode :program))
  ; the function a translated term applies (through a lambda's body); nil
  ; for a variable or a constant
  (cond ((atom term) nil)
        ((eq (car term) 'quote) nil)
        ((consp (car term)) (fn-cd-head (car (last (car term)))))
        (t (car term))))

(defun fn-cd-with-head (fn terms)
  (declare (xargs :mode :program))
  (cond ((atom terms) nil)
        ((eq (fn-cd-head (car terms)) fn)
         (cons (car terms) (fn-cd-with-head fn (cdr terms))))
        (t (fn-cd-with-head fn (cdr terms)))))

(defun fn-cd-without-head (fn terms)
  (declare (xargs :mode :program))
  (cond ((atom terms) nil)
        ((eq (fn-cd-head (car terms)) fn) (fn-cd-without-head fn (cdr terms)))
        (t (cons (car terms) (fn-cd-without-head fn (cdr terms))))))

(mutual-recursion
 (defun fn-cd-calls (fn term)
   (declare (xargs :mode :program))
   ; every subterm of the translated TERM that applies FN
   (cond ((atom term) nil)
         ((eq (car term) 'quote) nil)
         (t (let ((inner (fn-cd-calls-lst
                          fn (if (consp (car term))
                                 (cons (car (last (car term))) (cdr term))
                               (cdr term)))))
              (if (eq (car term) fn) (cons term inner) inner)))))
 (defun fn-cd-calls-lst (fn terms)
   (declare (xargs :mode :program))
   (if (atom terms)
       nil
     (append (fn-cd-calls fn (car terms)) (fn-cd-calls-lst fn (cdr terms))))))

(defun fn-cd-theorem (thm w)
  (declare (xargs :mode :program))
  (getpropc thm 'theorem nil w))

(defun fn-cd-transition-shape (r fn formula)
  (declare (xargs :mode :program))
  ; (TERM CALL SVAR OTHERS) when FORMULA has the trace shape (above); nil
  (mv-let (hyps concl)
    (fn-cd-split formula nil)
    (let* ((rhyps (fn-cd-with-head r hyps))
           (others (fn-cd-without-head r hyps))
           (term (and (consp concl) (eq (car concl) r)
                      (consp (cdr concl)) (null (cddr concl))
                      (cadr concl)))
           (calls (and term (fn-cd-calls fn term)))
           (call (and (consp calls) (null (cdr calls)) (car calls)))
           (args (cdr call))
           (svar (and (consp rhyps) (null (cdr rhyps))
                      (consp (cdr (car rhyps))) (null (cddr (car rhyps)))
                      (cadr (car rhyps)))))
      (and term call
           (symbol-listp args) (no-duplicatesp-eq args)
           svar (symbolp svar) (member-eq svar args)
           (subsetp-eq (all-vars term) args)
           (subsetp-eq (all-vars1-lst others nil) args)
           (list term call svar others)))))

(defun fn-cd-heads-of (terms)
  (declare (xargs :mode :program))
  (if (atom terms)
      nil
    (cons (fn-cd-head (car terms)) (fn-cd-heads-of (cdr terms)))))

(defun fn-cd-transition-problem (r fn thm w)
  (declare (xargs :mode :program))
  (let ((formula (fn-cd-theorem thm w)))
    (if (null formula)
        (msg "transition ~x0 names ~x1, which is not a theorem in this world"
             fn thm)
      (mv-let (hyps concl)
        (fn-cd-split formula nil)
        (cond
         ((not (member-eq r (fn-cd-heads-of hyps)))
          (msg "transition ~x0's theorem ~x1 has no hypothesis applying ~x2, ~
                so it does not carry the invariant across the transition (a ~
                theorem that establishes it belongs under :established)"
               fn thm r))
         ((not (eq (fn-cd-head concl) r))
          (msg "transition ~x0's theorem ~x1 does not conclude ~x2 (its ~
                conclusion applies ~x3)"
               fn thm r (fn-cd-head concl)))
         ((not (member-eq fn (all-fnnames concl)))
          (msg "transition ~x0's theorem ~x1 concludes ~x2 of a term that ~
                never calls ~x0"
               fn thm r))
         (t nil))))))

(defun fn-cd-transitions-problem (r transitions w)
  (declare (xargs :mode :program))
  (cond ((atom transitions) nil)
        (t (or (fn-cd-transition-problem r (car (car transitions))
                                         (cadr (car transitions)) w)
               (fn-cd-transitions-problem r (cdr transitions) w)))))

(defun fn-cd-established-problem (r established w)
  (declare (xargs :mode :program))
  (if (atom established)
      nil
    (let* ((fn (car (car established)))
           (thm (cadr (car established)))
           (formula (fn-cd-theorem thm w)))
      (cond
       ((null formula)
        (msg "establishing point ~x0 names ~x1, which is not a theorem in ~
              this world" fn thm))
       (t (mv-let (hyps concl)
            (fn-cd-split formula nil)
            (declare (ignore hyps))
            (cond
             ((not (eq (fn-cd-head concl) r))
              (msg "establishing point ~x0's theorem ~x1 does not conclude ~
                    ~x2 (its conclusion applies ~x3)"
                   fn thm r (fn-cd-head concl)))
             ((not (member-eq fn (all-fnnames concl)))
              (msg "establishing point ~x0's theorem ~x1 concludes ~x2 of a ~
                    term that never calls ~x0" fn thm r))
             (t (fn-cd-established-problem r (cdr established) w)))))))))

(defun fn-cd-concludes-problem (r concludes w)
  (declare (xargs :mode :program))
  (if (atom concludes)
      nil
    (let* ((pred (car (car concludes)))
           (thm (cadr (car concludes)))
           (formula (fn-cd-theorem thm w)))
      (cond
       ((null formula)
        (msg "bridge for ~x0 names ~x1, which is not a theorem in this world"
             pred thm))
       (t (mv-let (hyps concl)
            (fn-cd-split formula nil)
            (cond
             ((not (member-eq r (fn-cd-heads-of hyps)))
              (msg "bridge ~x0 has no hypothesis applying ~x1: it is not a ~
                    consequence of the carried invariant" thm r))
             ((not (member-eq pred (fn-cd-heads-of (fn-cd-conjuncts concl))))
              (msg "bridge ~x0 does not conclude ~x1 (its conclusion's ~
                    conjuncts apply ~&2)"
                   thm pred (fn-cd-heads-of (fn-cd-conjuncts concl))))
             (t (fn-cd-concludes-problem r (cdr concludes) w)))))))))

; Completeness: the fn-interfaces entries whose call closure reaches a
; writer.  A depth-first reachability over 'unnormalized-body with a memo:
; T is memoised when found; NIL only when no function still being explored
; (a recursion cycle) was met on the way, so a cycle never hides a path.

(mutual-recursion
 (defun fn-cd-reach1 (fn writers memo stack w)
   (declare (xargs :mode :program))
   ; (mv REACHES TAINTED MEMO)
   (cond ((member-eq fn writers) (mv t nil memo))
         ((assoc-eq fn memo) (mv (cdr (assoc-eq fn memo)) nil memo))
         ((member-eq fn stack) (mv nil t memo))
         (t (mv-let (r tainted memo)
              (fn-cd-reach-lst (all-fnnames (getpropc fn 'unnormalized-body nil w))
                               writers memo (cons fn stack) w)
              (if (or r (not tainted))
                  (mv r nil (acons fn r memo))
                (mv nil t memo))))))
 (defun fn-cd-reach-lst (fns writers memo stack w)
   (declare (xargs :mode :program))
   (if (atom fns)
       (mv nil nil memo)
     (mv-let (r tainted memo)
       (fn-cd-reach1 (car fns) writers memo stack w)
       (if r
           (mv t nil memo)
         (mv-let (r2 tainted2 memo)
           (fn-cd-reach-lst (cdr fns) writers memo stack w)
           (mv r2 (or tainted tainted2) memo)))))))

(defun fn-cd-reaching-entries (entries writers memo w)
  (declare (xargs :mode :program))
  ; the names of the fn-interfaces rows ENTRIES whose definition reaches a
  ; writer
  (cond ((atom entries) nil)
        ((eq (getpropc (car (car entries)) 'formals :none w) :none)
         (fn-cd-reaching-entries (cdr entries) writers memo w))
        (t (mv-let (r tainted memo)
             (fn-cd-reach1 (car (car entries)) writers memo nil w)
             (declare (ignore tainted))
             (if r
                 (cons (car (car entries))
                       (fn-cd-reaching-entries (cdr entries) writers memo w))
               (fn-cd-reaching-entries (cdr entries) writers memo w))))))

(defun fn-cd-first-unlisted (reaching listed)
  (declare (xargs :mode :program))
  (cond ((atom reaching) nil)
        ((member-eq (car reaching) listed) (fn-cd-first-unlisted (cdr reaching) listed))
        (t (car reaching))))

(defun fn-cd-shapes (r transitions w)
  (declare (xargs :mode :program))
  ; ((FN THM TERM CALL SVAR OTHERS) ...) when every transition has the trace
  ; shape; else (:unshaped FN THM) for the first that has not
  (if (atom transitions)
      nil
    (let* ((fn (car (car transitions)))
           (thm (cadr (car transitions)))
           (shape (fn-cd-transition-shape r fn (fn-cd-theorem thm w))))
      (if (null shape)
          (list :unshaped fn thm)
        (let ((rest (fn-cd-shapes r (cdr transitions) w)))
          (if (eq (car rest) :unshaped)
              rest
            (cons (list* fn thm shape) rest)))))))

(defun fn-cd-problem (name kvs w)
  (declare (xargs :mode :program))
  ; nil, or a msg naming the first check the world refutes
  (let* ((r (fn-cd-get :invariant kvs))
         (established (fn-cd-get :established kvs))
         (transitions (fn-cd-get :transitions kvs))
         (concludes (fn-cd-get :concludes kvs))
         (writers (fn-cd-get :writers kvs))
         (formals (getpropc r 'formals :none w))
         (bare (fn-cd-first-bare transitions)))
    (cond
     ((eq formals :none)
      (msg "invariant ~x0 is not a function in this world" r))
     ((not (and (consp formals) (null (cdr formals))))
      (msg "invariant ~x0 takes ~x1 formals; a carried relation is a function ~
            of one formal, the carried state" r (len formals)))
     (bare
      (msg "transition ~x0 has no preservation theorem.  The obligation: ~
            (implies (and (~x1 s) ...) (~x1 <the carried state of (~x0 ~&2)>)) ~
            where s is the carried state among ~x0's arguments; prove it and ~
            name it as (~x0 THM)."
           bare r (getpropc bare 'formals nil w)))
     ((fn-cd-established-problem r established w))
     ((fn-cd-transitions-problem r transitions w))
     ((fn-cd-concludes-problem r concludes w))
     ((and writers
           (fn-cd-first-unlisted
            (fn-cd-reaching-entries (table-alist 'fn-interfaces w) writers nil w)
            (append (strip-cars established) (strip-cars transitions))))
      (msg "host-called entry ~x0 (fn-interfaces) reaches a writer of the ~
            carried state (~&1) and is neither a transition nor an ~
            establishing point of ~x2: its preservation theorem is owed"
           (fn-cd-first-unlisted
            (fn-cd-reaching-entries (table-alist 'fn-interfaces w) writers nil w)
            (append (strip-cars established) (strip-cars transitions)))
           writers name))
     ((and (eq (fn-cd-trace-mode kvs) t)
           (eq (car (fn-cd-shapes r transitions w)) :unshaped))
      (let ((u (fn-cd-shapes r transitions w)))
        (msg ":trace t, but transition ~x0's theorem ~x1 has not the trace ~
              shape (implies (and H ... (~x2 s) ...) (~x2 TERM)), TERM ~
              calling ~x0 once on distinct variables that are all its ~
              variables, every other hypothesis over those variables"
             (cadr u) (caddr u) r)))
     (t nil))))

; ---------------------------------------------------------------------------
; The events.

(mutual-recursion
 (defun fn-cd-subst (term alist)
   (declare (xargs :mode :program))
   ; ALIST's values for its variables in the translated TERM; a lambda's
   ; body is closed, so only its actuals are substituted
   (cond ((atom term)
          (let ((b (assoc-eq term alist))) (if b (cdr b) term)))
         ((eq (car term) 'quote) term)
         (t (cons (car term) (fn-cd-subst-lst (cdr term) alist)))))
 (defun fn-cd-subst-lst (terms alist)
   (declare (xargs :mode :program))
   (if (atom terms)
       nil
     (cons (fn-cd-subst (car terms) alist) (fn-cd-subst-lst (cdr terms) alist)))))

(defun fn-cd-arg-alist (args svar i)
  (declare (xargs :mode :program))
  ; the call's variables: the carried state to s, the others to the event's
  (cond ((atom args) nil)
        ((eq (car args) svar)
         (cons (cons svar 's) (fn-cd-arg-alist (cdr args) svar (1+ i))))
        (t (cons (cons (car args) (list 'nth i '(cdr e)))
                 (fn-cd-arg-alist (cdr args) svar (1+ i))))))

(defun fn-cd-step-arms (shapes)
  (declare (xargs :mode :program))
  (if (atom shapes)
      nil
    (let* ((shape (car shapes))
           (fn (car shape)) (term (caddr shape)) (call (cadddr shape))
           (svar (car (cddddr shape)))
           (alist (fn-cd-arg-alist (cdr call) svar 0)))
      (cons (list fn (fn-cd-subst term alist))
            (fn-cd-step-arms (cdr shapes))))))

(defun fn-cd-okp-arms (shapes)
  (declare (xargs :mode :program))
  (if (atom shapes)
      nil
    (let* ((shape (car shapes))
           (fn (car shape)) (call (cadddr shape))
           (svar (car (cddddr shape))) (others (cadr (cddddr shape)))
           (alist (fn-cd-arg-alist (cdr call) svar 0)))
      (cons (list fn (if others (cons 'and (fn-cd-subst-lst others alist)) t))
            (fn-cd-okp-arms (cdr shapes))))))

(defun fn-cd-instance-bindings (alist)
  (declare (xargs :mode :program))
  (if (atom alist)
      nil
    (cons (list (car (car alist)) (cdr (car alist)))
          (fn-cd-instance-bindings (cdr alist)))))

(defun fn-cd-instances (shapes)
  (declare (xargs :mode :program))
  (if (atom shapes)
      nil
    (let* ((shape (car shapes))
           (thm (cadr shape)) (call (cadddr shape))
           (svar (car (cddddr shape)))
           (alist (fn-cd-arg-alist (cdr call) svar 0)))
      (cons (list* :instance thm (fn-cd-instance-bindings alist))
            (fn-cd-instances (cdr shapes))))))

(defun fn-cd-trace-events (name r shapes)
  (declare (xargs :mode :program))
  (let ((step (packn-pos (list name '-step) name))
        (okp (packn-pos (list name '-okp) name))
        (run (packn-pos (list name '-run) name))
        (run-okp (packn-pos (list name '-run-okp) name))
        (step-carries (packn-pos (list name '-step-carries) name))
        (run-carries (packn-pos (list name '-run-carries) name)))
    `((defun-nx ,step (s e)
        (case (car e) ,@(fn-cd-step-arms shapes) (otherwise s)))
      (defun-nx ,okp (s e)
        (case (car e) ,@(fn-cd-okp-arms shapes) (otherwise t)))
      (defun-nx ,run (s es)
        (declare (xargs :measure (acl2-count es)))
        (if (atom es) s (,run (,step s (car es)) (cdr es))))
      (defun-nx ,run-okp (s es)
        (declare (xargs :measure (acl2-count es)))
        (if (atom es) t (and (,okp s (car es)) (,run-okp (,step s (car es)) (cdr es)))))
      (defthm ,step-carries
        (implies (and (,r s) (,okp s e)) (,r (,step s e)))
        :hints (("Goal" :in-theory (union-theories '(,step ,okp eql)
                                                   (theory 'minimal-theory))
                 :use ,(fn-cd-instances shapes))))
      (defthm ,run-carries
        (implies (and (,r s) (,run-okp s es)) (,r (,run s es)))
        :hints (("Goal" :by (:functional-instance fn-cd-run-carries
                                                  (fn-cd-inv ,r)
                                                  (fn-cd-okp ,okp)
                                                  (fn-cd-step ,step)
                                                  (fn-cd-run ,run)
                                                  (fn-cd-run-okp ,run-okp))))))))

(defun fn-cd-events (name kvs w)
  (declare (xargs :mode :program))
  (let* ((r (fn-cd-get :invariant kvs))
         (transitions (fn-cd-get :transitions kvs))
         (mode (fn-cd-trace-mode kvs))
         (shapes (and mode (fn-cd-shapes r transitions w)))
         (traced (and mode shapes (not (eq (car shapes) :unshaped)))))
    `(progn
       (table fn-carried ',name
              '(:invariant ,r
                :established ,(fn-cd-get :established kvs)
                :transitions ,transitions
                :concludes ,(fn-cd-get :concludes kvs)
                :writers ,(fn-cd-get :writers kvs)
                :trace ,(if traced t nil)))
       ,@(if traced (fn-cd-trace-events name r shapes) nil))))

(defmacro def-carried (name &rest kvs)
  (let ((reason (fn-cd-refusal name kvs)))
    (if reason
        `(make-event (er soft 'def-carried "~x0: ~@1" ',name
                         ',(fn-cd-refusal-text reason)))
      `(make-event
        (let ((problem (fn-cd-problem ',name ',kvs (w state))))
          (if problem
              (er soft 'def-carried "~x0: ~@1" ',name problem)
            (value (fn-cd-events ',name ',kvs (w state)))))))))

; Re-run NAME's checks in the world as now loaded: in the image world, where
; host/interfaces.lisp has declared every host-called entry, the
; completeness check bites.
(defmacro def-carried-check (name)
  `(make-event
    (let* ((row (cdr (assoc-eq ',name (table-alist 'fn-carried (w state)))))
           (problem (if row
                        (fn-cd-problem ',name row (w state))
                      (msg "no carried invariant ~x0 in this world" ',name))))
      (if problem
          (er soft 'def-carried-check "~x0: ~@1" ',name problem)
        (value '(value-triple ',name))))))

; The D40 row (books/definterface.lisp `:raw-with (:carried NAME)').
(defun fn-cd-raw-with (name entry w)
  (declare (xargs :mode :program))
  ; the theorems that let ENTRY, a transition of the carried invariant NAME,
  ; be dispatched raw: the bridges, the establishing theorems, its own; nil
  ; when NAME is no carried invariant or ENTRY no transition of it
  (let* ((row (cdr (assoc-eq name (table-alist 'fn-carried w))))
         (transition (assoc-eq entry (fn-cd-get :transitions row))))
    (and row transition
         (append (strip-cadrs (fn-cd-get :concludes row))
                 (strip-cadrs (fn-cd-get :established row))
                 (list (cadr transition))))))

(in-theory (disable fn-cd-run fn-cd-run-okp))
