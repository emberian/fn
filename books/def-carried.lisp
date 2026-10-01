; fn: `def-carried' --- a carried invariant from one declaration: the
; obligation table checked complete against the world, the trace theorem by
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
;     :invariant R                        ; the carried relation: a function
;                                         ; of one formal, the carried state
;     :established ((FN THM [PATTERN]) ...)
;                                         ; where the host first obtains a
;                                         ; state satisfying R: THM concludes
;                                         ; (R <the state FN returns>)
;     :transitions ((FN THM [PATTERN]) | FN ...)
;                                         ; every transition and its
;                                         ; preservation theorem; a bare FN
;                                         ; is an obligation still owed and
;                                         ; is REFUSED with the statement
;     [:concludes ((PRED THM) ...)]       ; the bridges: R implies a guard
;                                         ; predicate an entry guard carries
;     [:complete-by (:enumeration "why")] ; a value-typed state only (below)
;     [:trace nil])                       ; omit the trace theorem
;
; PATTERN says where the carried state is in FN's result: a term over the
; placeholder `_' (default `_': the call itself), such as (mv-nth 2 _) or
; (fn-tcl-result-session _) for a value state.  For a carried stobj, only
; `_` for its sole output or (mv-nth K _) at a world-confirmed output
; position is allowed for transitions.  The theorem's conclusion must be R of exactly
; PATTERN with `_' replaced by a call (FN v1 ... vn) on distinct variables
; -- never R of some larger term that merely contains the call (a theorem
; about (fn-open (fn-break s)) is not fn-break's preservation).
;
; Admitted, it checks:
;
;   * R is a function of exactly one formal, and NAME is not yet declared;
;   * every named THM is a theorem of this world.  A transition theorem is
;     (implies H (R TERM)) where H has exactly one conjunct applying R, and
;     that to a variable s; TERM is PATTERN over (FN v1 .. vn) with the vi
;     distinct variables, s among them, all of TERM's variables among them,
;     and every other conjunct of H over them alone (so the theorem IS a
;     step from a state to the state FN returns).  An establishing theorem
;     concludes R of PATTERN over such a call (its hypotheses are the
;     open's preconditions).  A bridge has R among its hypotheses' heads
;     and PRED among its conclusion's conjuncts' heads;
;   * a transition with no theorem is refused with the obligation stated;
;   * COMPLETENESS, derived from the world and never from the declaration.
;     When R's formal is a stobj (fn-cdt-st, state): every entry of the
;     `fn-interfaces' table (books/definterface.lisp: the host-called
;     entries) whose `stobjs-out' returns that stobj can produce a new
;     value of the carried state, so it must be a listed transition or
;     establishing point, or the form is refused BY NAME.  The table is
;     complete only where the declarations are loaded (the image world,
;     host/interfaces.lisp): `(def-carried-check NAME)' re-runs the same
;     check there, and books/definterface.lisp runs it whenever a
;     `:raw-with (:carried NAME)' is accepted -- at image build too, where
;     host/native/io.lisp fnn-install-raw-dispatch re-checks every raw
;     entry.  When R's formal is a value (a session record the host
;     threads), no such derivation exists: the form must say
;     `:complete-by (:enumeration "why")', which the row records as the
;     claim it is; `:complete-by' on a stobj-typed state is refused.
;
; VACUITY, refuted under a step limit (*fn-cd-vacuity-steps*) in a closed
; theory (R opened one level, else minimal-theory): the expansion must FAIL
; to prove (R x) with x free (a relation that is constantly true carries
; nothing), and, per transition, must fail to prove that its hypotheses are
; contradictory.  These are refutation attempts,
; not witnesses: a trivial relation or a contradiction that takes more
; steps than the limit to expose is not caught; a ground witness is the
; teeth book's (tests/acl2/def-carried-tests.lisp), and for a state that is
; the ACL2 state no ground witness is expressible in a book.
;
; Emits:
;
;   (table fn-carried NAME '(:invariant R :state ST|nil :established ...
;                            :transitions ... :concludes ... :complete-by ...
;                            :trace t|nil))
;   (local (must-fail (with-prover-step-limit N (thm (R x)))))
;   (local (must-fail (with-prover-step-limit N (thm (not (and H...)))))) ...
;
; and, unless :trace nil, the trace theorem by functional instantiation of
; the generic theory below:
;
;   (defun-nx NAME-step (s e) ...)      ; e = (FN . args): the state FN returns
;   (defun-nx NAME-okp (s e) ...)       ; THM's other hypotheses at e
;   (defun-nx NAME-run (s es) ...)      ; the trace
;   (defun-nx NAME-run-okp (s es) ...)
;   (defthm NAME-step-carries ...)      ; one case per event, each closed by
;                                       ; the transition theorem as a rule
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
; ACL2 functions.  That the host calls nothing else that returns the carried
; state is the completeness check over `fn-interfaces' (every host-called
; entry is declared: tools/interface_emit.py refuses an undeclared dispatch),
; and that the entry guard runs before raw dispatch is host/native/io.lisp's.
;
; Includes std/testing/must-fail for the vacuity refutations; the helpers are
; `:program' mode, declared per defun.  The generic theory (fn-cd-inv,
; fn-cd-okp, fn-cd-step, fn-cd-run, fn-cd-run-okp, fn-cd-run-carries) is the
; one logic-mode part; the export at the end leaves only fn-cd-run-carries
; enabled.

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

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
  '(:invariant :established :transitions :concludes :complete-by :trace))

(defconst *fn-cd-vacuity-steps* 50000)

(defun fn-cd-get (key kvs)
  (declare (xargs :mode :program))
  (cadr (assoc-keyword key kvs)))

(defun fn-cd-unknown-keys (kvs)
  (declare (xargs :mode :program))
  (cond ((atom kvs) nil)
        ((member-eq (car kvs) *fn-cd-keys*) (fn-cd-unknown-keys (cddr kvs)))
        (t (cons (car kvs) (fn-cd-unknown-keys (cddr kvs))))))

(defun fn-cd-entryp (x)
  (declare (xargs :mode :program))
  ; (FN THM) or (FN THM PATTERN): FN and THM non-nil symbols
  (and (true-listp x) (or (equal (len x) 2) (equal (len x) 3))
       (symbolp (car x)) (car x) (symbolp (cadr x)) (cadr x)))

(defun fn-cd-entriesp (x)
  (declare (xargs :mode :program))
  (if (atom x) (null x) (and (fn-cd-entryp (car x)) (fn-cd-entriesp (cdr x)))))

(defun fn-cd-pairp (x)
  (declare (xargs :mode :program))
  (and (true-listp x) (equal (len x) 2)
       (symbolp (car x)) (car x) (symbolp (cadr x)) (cadr x)))

(defun fn-cd-pairsp (x)
  (declare (xargs :mode :program))
  (if (atom x) (null x) (and (fn-cd-pairp (car x)) (fn-cd-pairsp (cdr x)))))

(defun fn-cd-transition-entriesp (x)
  (declare (xargs :mode :program))
  (if (atom x)
      (null x)
    (and (or (and (symbolp (car x)) (car x)) (fn-cd-entryp (car x)))
         (fn-cd-transition-entriesp (cdr x)))))

(defun fn-cd-first-bare (transitions)
  (declare (xargs :mode :program))
  (cond ((atom transitions) nil)
        ((symbolp (car transitions)) (car transitions))
        (t (fn-cd-first-bare (cdr transitions)))))

(defun fn-cd-complete-by-formp (x)
  (declare (xargs :mode :program))
  (or (null x)
      (and (true-listp x) (equal (len x) 2) (eq (car x) :enumeration)
           (stringp (cadr x)) (< 0 (length (cadr x))))))

(defun fn-cd-refusal (name kvs)
  (declare (xargs :mode :program))
  ; nil when the form is well-formed; else (REASON . DETAILS)
  (cond
   ((not (and (symbolp name) name)) (list :bad-name name))
   ((not (keyword-value-listp kvs)) (list :bad-options kvs))
   ((fn-cd-unknown-keys kvs) (cons :unknown-keyword (fn-cd-unknown-keys kvs)))
   ((not (and (fn-cd-get :invariant kvs) (symbolp (fn-cd-get :invariant kvs))))
    (list :no-invariant name))
   ((not (fn-cd-entriesp (fn-cd-get :established kvs)))
    (list :bad-established (fn-cd-get :established kvs)))
   ((null (fn-cd-get :established kvs)) (list :no-established name))
   ((not (fn-cd-transition-entriesp (fn-cd-get :transitions kvs)))
    (list :bad-transitions (fn-cd-get :transitions kvs)))
   ((not (fn-cd-pairsp (fn-cd-get :concludes kvs)))
    (list :bad-concludes (fn-cd-get :concludes kvs)))
   ((not (fn-cd-complete-by-formp (fn-cd-get :complete-by kvs)))
    (list :bad-complete-by (fn-cd-get :complete-by kvs)))
   ((not (member-eq (fn-cd-get :trace kvs) '(t nil)))
    (list :bad-trace (fn-cd-get :trace kvs)))
   (t nil)))

(defun fn-cd-refusal-text (reason)
  (declare (xargs :mode :program))
  (case (car reason)
    (:no-invariant (msg "~x0 has no :invariant: name the carried relation."
                        (cadr reason)))
    (:no-established (msg "~x0 has no :established ((FN THM [PATTERN]) ...): ~
                           a carried invariant names where the host first ~
                           obtains it." (cadr reason)))
    (:bad-established (msg ":established ~x0 is not ((FN THM [PATTERN]) ...)."
                           (cadr reason)))
    (:bad-transitions (msg ":transitions ~x0 is not ((FN THM [PATTERN]) | FN ...)."
                           (cadr reason)))
    (:bad-concludes (msg ":concludes ~x0 is not ((PRED THM) ...)." (cadr reason)))
    (:bad-complete-by (msg ":complete-by ~x0 is not (:enumeration \"why\")."
                           (cadr reason)))
    (:bad-trace (msg ":trace ~x0 is not t or nil." (cadr reason)))
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

(defun fn-cd-heads-of (terms)
  (declare (xargs :mode :program))
  (if (atom terms)
      nil
    (cons (fn-cd-head (car terms)) (fn-cd-heads-of (cdr terms)))))

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

(defun fn-cd-theorem (thm w)
  (declare (xargs :mode :program))
  (getpropc thm 'theorem nil w))

(defun fn-cd-pattern (entry)
  (declare (xargs :mode :program))
  (if (equal (len entry) 3) (caddr entry) '_))

(mutual-recursion
 (defun fn-cd-translate-pattern (x)
   (declare (xargs :mode :program))
   ; PATTERN as a translated term: constants quoted (a theorem's formula
   ; holds (mv-nth '2 ...)), variables and `_' kept
   (cond ((eq x '_) x)
         ((and (symbolp x) x (not (eq x t)) (not (keywordp x))) x)
         ((atom x) (list 'quote x))
         ((eq (car x) 'quote) x)
         (t (cons (car x) (fn-cd-translate-pattern-lst (cdr x))))))
 (defun fn-cd-translate-pattern-lst (xs)
   (declare (xargs :mode :program))
   (if (atom xs)
       nil
     (cons (fn-cd-translate-pattern (car xs)) (fn-cd-translate-pattern-lst (cdr xs))))))

(defun fn-cd-returned-call (fn pattern term)
  (declare (xargs :mode :program))
  ; the call (FN v1 .. vn) when TERM is exactly PATTERN with `_' replaced by
  ; it and the vi are distinct variables; else nil
  (let* ((calls (fn-cd-calls fn term))
         (call (and (consp calls) (null (cdr calls)) (car calls))))
    (and call
         (symbol-listp (cdr call)) (no-duplicatesp-eq (cdr call))
         (equal (fn-cd-subst (fn-cd-translate-pattern pattern) (list (cons '_ call)))
                term)
         call)))

(defun fn-cd-transition-shape (r fn pattern formula)
  (declare (xargs :mode :program))
  ; (TERM CALL SVAR OTHERS) when FORMULA is a step from s to the state FN
  ; returns (the shape in the header); else nil
  (mv-let (hyps concl)
    (fn-cd-split formula nil)
    (let* ((rhyps (fn-cd-with-head r hyps))
           (others (fn-cd-without-head r hyps))
           (term (and (consp concl) (eq (car concl) r)
                      (consp (cdr concl)) (null (cddr concl))
                      (cadr concl)))
           (call (and term (fn-cd-returned-call fn pattern term)))
           (svar (and (consp rhyps) (null (cdr rhyps))
                      (consp (cdr (car rhyps))) (null (cddr (car rhyps)))
                      (cadr (car rhyps)))))
      (and call
           svar (symbolp svar) (member-eq svar (cdr call))
           (subsetp-eq (all-vars term) (cdr call))
           (subsetp-eq (all-vars1-lst others nil) (cdr call))
           (list term call svar others)))))

(defun fn-cd-stobj-patternp (r fn pattern w)
  (declare (xargs :mode :program))
  ; Value-state projections retain their explicit enumeration contract.
  ; A stobj projection is determined by ACL2, never by an author-supplied
  ; operation that might repair the returned state.
  (let ((st (car (getpropc r 'stobjs-in nil w)))
        (outputs (getpropc fn 'stobjs-out nil w)))
    (or (null st)
        (if (eq pattern '_)
            (equal outputs (list st))
          (and (true-listp pattern) (equal (len pattern) 3)
               (eq (car pattern) 'mv-nth)
               (natp (cadr pattern))
               (< (cadr pattern) (len outputs))
               (eq (caddr pattern) '_)
               (eq (nth (cadr pattern) outputs) st))))))

(defun fn-cd-transition-problem (r entry w)
  (declare (xargs :mode :program))
  (let* ((fn (car entry))
         (thm (cadr entry))
         (pattern (fn-cd-pattern entry))
         (formula (fn-cd-theorem thm w)))
    (cond
     ((not (fn-cd-stobj-patternp r fn pattern w))
      (msg "transition ~x0 has invalid carried-stobj PATTERN ~x1: use `_
            only for a sole carried-stobj output, or (mv-nth K _) where
            ACL2's stobjs-out identifies that carried stobj at K"
           fn pattern))
     ((null formula)
      (msg "transition ~x0 names ~x1, which is not a theorem in this world"
           fn thm))
     (t (mv-let (hyps concl)
        (fn-cd-split formula nil)
        (let ((rhyps (fn-cd-with-head r hyps)))
          (cond
           ((null rhyps)
            (msg "transition ~x0's theorem ~x1 has no hypothesis applying ~x2, ~
                  so it does not carry the invariant across the transition ~
                  (a theorem that establishes it belongs under :established)"
                 fn thm r))
           ((not (and (null (cdr rhyps)) (consp (cdr (car rhyps)))
                      (symbolp (cadr (car rhyps))) (cadr (car rhyps))))
            (msg "transition ~x0's theorem ~x1 must assume ~x2 of exactly one ~
                  variable, the state before the step; it assumes ~x3"
                 fn thm r rhyps))
           ((not (eq (fn-cd-head concl) r))
            (msg "transition ~x0's theorem ~x1 does not conclude ~x2 (its ~
                  conclusion applies ~x3)"
                 fn thm r (fn-cd-head concl)))
           ((not (fn-cd-returned-call fn pattern (cadr concl)))
            (msg "transition ~x0's theorem ~x1 concludes ~x2 of ~x3, which is ~
                  not ~x4 over a call (~x0 v1 ... vn) on distinct variables: ~
                  the conclusion must be about the state ~x0 returns (name its ~
                  place in the result as the entry's PATTERN over `_')"
                 fn thm r (cadr concl) pattern))
           ((null (fn-cd-transition-shape r fn pattern formula))
            (msg "transition ~x0's theorem ~x1 is not a step from the assumed ~
                  state to the state ~x0 returns: the assumed state must be ~
                  one of the call's variables, and the conclusion's and the ~
                  other hypotheses' variables must all be the call's"
                 fn thm))
           (t nil))))))))

(defun fn-cd-transitions-problem (r transitions w)
  (declare (xargs :mode :program))
  (cond ((atom transitions) nil)
        (t (or (fn-cd-transition-problem r (car transitions) w)
               (fn-cd-transitions-problem r (cdr transitions) w)))))

(defun fn-cd-established-problem (r established w)
  (declare (xargs :mode :program))
  (if (atom established)
      nil
    (let* ((entry (car established))
           (fn (car entry))
           (thm (cadr entry))
           (pattern (fn-cd-pattern entry))
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
             ((not (and (consp (cdr concl)) (null (cddr concl))
                        (fn-cd-returned-call fn pattern (cadr concl))))
              (msg "establishing point ~x0's theorem ~x1 concludes ~x2 of ~x3, ~
                    which is not ~x4 over a call (~x0 v1 ... vn) on distinct ~
                    variables: the conclusion must be about the state ~x0 ~
                    returns"
                   fn thm r (cadr concl) pattern))
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

; Completeness over the fn-interfaces table: the declared entries that
; return the carried stobj.
(defun fn-cd-returning-entries (entries st w)
  (declare (xargs :mode :program))
  (cond ((atom entries) nil)
        ((member-eq st (getpropc (car (car entries)) 'stobjs-out nil w))
         (cons (car (car entries)) (fn-cd-returning-entries (cdr entries) st w)))
        (t (fn-cd-returning-entries (cdr entries) st w))))

(defun fn-cd-first-unlisted (names listed)
  (declare (xargs :mode :program))
  (cond ((atom names) nil)
        ((member-eq (car names) listed) (fn-cd-first-unlisted (cdr names) listed))
        (t (car names))))

(defun fn-cd-state-stobj (r w)
  (declare (xargs :mode :program))
  ; the stobj R's one formal is, or nil for a value
  (car (getpropc r 'stobjs-in nil w)))

(defun fn-cd-problem (name kvs w)
  (declare (xargs :mode :program))
  ; nil, or a msg naming the first check the world refutes
  (let* ((r (fn-cd-get :invariant kvs))
         (established (fn-cd-get :established kvs))
         (transitions (fn-cd-get :transitions kvs))
         (concludes (fn-cd-get :concludes kvs))
         (complete-by (fn-cd-get :complete-by kvs))
         (formals (getpropc r 'formals :none w))
         (st (fn-cd-state-stobj r w))
         (bare (fn-cd-first-bare transitions))
         (listed (append (strip-cars established) (strip-cars transitions)))
         (unlisted (and st (fn-cd-first-unlisted
                            (fn-cd-returning-entries (table-alist 'fn-interfaces w) st w)
                            listed))))
    (cond
     ((eq formals :none)
      (msg "invariant ~x0 is not a function in this world" r))
     ((not (and (consp formals) (null (cdr formals))))
      (msg "invariant ~x0 takes ~x1 formals; a carried relation is a function ~
            of one formal, the carried state" r (len formals)))
     (bare
      (msg "transition ~x0 has no preservation theorem.  The obligation: ~
            (implies (and (~x1 s) ...) (~x1 <the state (~x0 ~&2) returns>)) ~
            where s is the carried state among ~x0's arguments; prove it and ~
            name it as (~x0 THM [PATTERN])."
           bare r (getpropc bare 'formals nil w)))
     ((fn-cd-established-problem r established w))
     ((fn-cd-transitions-problem r transitions w))
     ((fn-cd-concludes-problem r concludes w))
     ((and st complete-by)
      (msg ":complete-by on ~x0, whose state is the stobj ~x1: completeness is ~
            derived from the world there (every declared entry returning ~x1), ~
            never claimed" name st))
     ((and (null st) (null complete-by))
      (msg "~x0's state is a value, not a stobj, so the world cannot say which ~
            declared entries produce it: say :complete-by (:enumeration ~
            \"why the transition list is complete\")" name))
     (unlisted
      (msg "host-called entry ~x0 (fn-interfaces) returns the carried state ~
            ~x1 and is neither a transition nor an establishing point of ~x2: ~
            its preservation theorem is owed"
           unlisted st name))
     (t nil))))

; ---------------------------------------------------------------------------
; The events.

(defun fn-cd-shapes (r transitions w)
  (declare (xargs :mode :program))
  ; ((FN THM TERM CALL SVAR OTHERS) ...): every transition's shape (checked
  ; present by fn-cd-problem)
  (if (atom transitions)
      nil
    (let ((entry (car transitions)))
      (cons (list* (car entry) (cadr entry)
                   (fn-cd-transition-shape r (car entry) (fn-cd-pattern entry)
                                           (fn-cd-theorem (cadr entry) w)))
            (fn-cd-shapes r (cdr transitions) w)))))

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

(defun fn-cd-vacuity-events (r shapes)
  (declare (xargs :mode :program))
  ; per transition: its hypotheses are not provably contradictory
  (if (atom shapes)
      nil
    (let* ((shape (car shapes))
           (svar (car (cddddr shape))) (others (cadr (cddddr shape))))
      (cons `(local (must-fail
                     (with-prover-step-limit
                      ,*fn-cd-vacuity-steps*
                      (thm (not (and (,r ,svar) ,@others))
                           :hints (("Goal" :in-theory (theory 'minimal-theory)))))))
            (fn-cd-vacuity-events r (cdr shapes))))))

(defun fn-cd-unruled-instances (shapes w)
  (declare (xargs :mode :program))
  ; the transition theorems that are no rewrite rule (:rule-classes nil),
  ; instantiated at their event for :use; every other theorem is a rule
  (if (atom shapes)
      nil
    (let* ((shape (car shapes))
           (thm (cadr shape)) (call (cadddr shape))
           (svar (car (cddddr shape)))
           (alist (fn-cd-arg-alist (cdr call) svar 0)))
      (if (getpropc thm 'classes nil w)
          (fn-cd-unruled-instances (cdr shapes) w)
        (cons (list* :instance thm (fn-cd-instance-bindings alist))
              (fn-cd-unruled-instances (cdr shapes) w))))))

(defun fn-cd-trace-events (name r shapes w)
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
        ; one case per event; the transition theorems close each as rewrite
        ; rules over their own variables (a generated per-arm lemma over the
        ; event's literals does not: a disjunctive hypothesis lets the
        ; clausifier substitute into the call, and a :use of every arm at
        ; once is a 4^n clausification, both measured on 23 transitions)
        :hints (("Goal" :in-theory (union-theories '(,step ,okp eql case-split force
                                                     (:executable-counterpart equal)
                                                     ,@(strip-cadrs shapes))
                                                   (theory 'minimal-theory))
                 ,@(let ((instances (fn-cd-unruled-instances shapes w)))
                     (if instances (list :use instances) nil)))))
      (defthm ,run-carries
        (implies (and (,r s) (,run-okp s es)) (,r (,run s es)))
        :hints (("Goal" :by (:functional-instance fn-cd-run-carries
                                                  (fn-cd-inv ,r)
                                                  (fn-cd-okp ,okp)
                                                  (fn-cd-step ,step)
                                                  (fn-cd-run ,run)
                                                  (fn-cd-run-okp ,run-okp))))))))

(defun fn-cd-normalize (entries)
  (declare (xargs :mode :program))
  ; every entry as (FN THM PATTERN)
  (if (atom entries)
      nil
    (cons (list (car (car entries)) (cadr (car entries)) (fn-cd-pattern (car entries)))
          (fn-cd-normalize (cdr entries)))))

(defun fn-cd-events (name kvs w)
  (declare (xargs :mode :program))
  (let* ((r (fn-cd-get :invariant kvs))
         (transitions (fn-cd-get :transitions kvs))
         (traced (not (and (assoc-keyword :trace kvs) (null (fn-cd-get :trace kvs)))))
         (shapes (fn-cd-shapes r transitions w))
         (x (car (getpropc r 'formals nil w))))
    `(progn
       (table fn-carried ',name
              '(:invariant ,r
                :state ,(fn-cd-state-stobj r w)
                :established ,(fn-cd-normalize (fn-cd-get :established kvs))
                :transitions ,(fn-cd-normalize transitions)
                :concludes ,(fn-cd-get :concludes kvs)
                :complete-by ,(fn-cd-get :complete-by kvs)
                :trace ,(if traced t nil)))
       (local (must-fail (with-prover-step-limit
                          ,*fn-cd-vacuity-steps*
                          (thm (,r ,x)
                               :hints (("Goal" :in-theory (union-theories
                                                           '(,r)
                                                           (theory 'minimal-theory))))))))
       ,@(fn-cd-vacuity-events r shapes)
       ,@(if traced (fn-cd-trace-events name r shapes w) nil))))

(defmacro def-carried (name &rest kvs)
  (let ((reason (fn-cd-refusal name kvs)))
    (if reason
        `(make-event (er soft 'def-carried "~x0: ~@1" ',name
                         ',(fn-cd-refusal-text reason)))
      `(make-event
        (let ((problem (if (assoc-eq ',name (table-alist 'fn-carried (w state)))
                           (msg "~x0 is already a carried invariant of this world; ~
                                 a row is declared once" ',name)
                         (fn-cd-problem ',name ',kvs (w state)))))
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
