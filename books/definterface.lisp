; fn: `definterface' --- one declaration per host-called entry (G7).
;
; The raw host reaches ACL2 only through `fnn-call' (host/native/io.lisp),
; which checks the entry's arity and the KIND conjuncts of its guard
; (fnn-entry-guard-spec) before it runs the entry.  What the host may call,
; which kinds its guard refuses, which byte-carrying formals it leaves
; unguarded and why, which keystones are about it and whether the extractor
; starts from it were four hand lists in three tools (harness_check's
; ENTRY_KIND_EXEMPT, tools/extract/build.sh's ROOTS and EXTRA, the prose of
; the proofs registry).  Here each is one form, checked against the WORLD
; when it is admitted:
;
;   (definterface NAME
;     :class CLASS                  ; :common-lisp-compliant (guard-verified),
;                                   ; :ideal or :program -- ACL2's symbol-class
;     [:kinds ((FORMAL RECOGNIZER) ...)]  ; the guard's kind conjuncts, in
;                                   ; position order; default none
;     [:exempt ((FORMAL "why") ...)] ; byte-carrying formals the guard does
;                                   ; not kind, each with its reason
;     [:keystones (THM | (THM :via CALLEE) ...)]
;     [:root :extract | :extract-extra] ; an extraction root, or one of the
;                                   ; extractor's EXTRA functions
;     [:direct "why"]               ; the raw host applies it directly, not
;                                   ; through fnn-call's entry guard
;     [:raw-guarded (ARITY INPUT-STOBJ-SLOTS OUTPUT-STOBJ-SLOTS)]
;                                   ; compiled callback with guard T or only
;                                   ; its own supplied stobj recognizers;
;                                   ; no invariant or relational guard
;     [:raw-with (THM ...)])        ; RAW DISPATCH (D40): the host calls the
;                                   ; guard-verified definition, not its
;                                   ; executable counterpart; THM ... is the
;                                   ; named preservation argument for the
;                                   ; guard conjuncts the entry guard does
;                                   ; not evaluate
;
; Admitted, it checks, in the world as loaded (so a declaration cannot drift
; from the definition it declares):
;
;   * NAME is a function (it has formals) or a stobj creator;
;   * CLASS is NAME's symbol-class: a declaration of :common-lisp-compliant
;     is a claim that the entry is guard-verified, and the world confirms it;
;   * :kinds is EXACTLY what the host entry guard derives from NAME's guard
;     (the same rule as fnn-entry-guard-spec and the extractor's
;     xt-entry-guard-spec: each conjunct (R v), v a non-stobj formal, R in
;     *fn-entry-guard-kinds*), in position order -- so the registry's kinds
;     are the kinds the host evaluates;
;   * each :exempt formal is a formal of NAME with no kind conjunct;
;   * each keystone THM is a theorem whose formula calls NAME, or, for
;     (THM :via CALLEE), calls CALLEE and CALLEE is in NAME's call closure
;     (a :program entry cannot appear in a theorem; its keystones are about
;     the logic functions it runs);
;   * :raw-with (D40, lane depth-debt-9): NAME is :common-lisp-compliant
;     (guard verification is the condition for faithful raw execution: the
;     raw definition is the logical function only where its guard holds);
;     every guard conjunct that is not a kind check (fnn-entry-guard
;     evaluates those before either dispatch) nor a stobj formal's own
;     recognizer (the stobj discipline holds it) is over stobj formals only --
;     a conjunct over an argument the host passes per call is refused, no
;     preservation theorem can establish it; each such conjunct's head that
;     the tree defines (a boot-strap primitive such as boundp-global fails
;     loud in raw Lisp and is exempt) is the CONCLUSION of a named theorem;
;     every named THM is a theorem of this world and mentions a function of
;     that argument (the head, or a function a concluding theorem mentions:
;     the establishing and per-transition theorems are stated over the
;     carried relation, the bridge theorem concludes the head from it); and
;     the guard has at least one such conjunct (a raw dispatch that skips
;     nothing is refused: the annotation is a boundary claim, not a default).
;     host/native/io.lisp fnn-install-raw-dispatch reads the table at image
;     build and dispatches those entries raw; the developer selector
;     FN_NATIVE_DISPATCH_COUNTERPART keeps the counterpart path for a native
;     that compares both.  `:raw-with (:carried NAME)' consults nothing a
;     user wrote: it resolves only to the statements def-carried GENERATED
;     for the carried invariant NAME (books/def-carried.lisp, table
;     fn-carried) -- NAME-ENTRY-carries and every NAME-PRED-bridge -- and is
;     refused unless the row backs the entry in this world
;     (fn-cd-raw-problem: a stobj row, the entry a transition, the row
;     complete, every generated formula equal to the statement regenerated
;     from the world, no declared :hyps) and every skipped guard conjunct
;     is the invariant of the entry's state or a conjunct of a generated
;     bridge (fn-cd-uncovered-conjunct); the occurrence lint above is for
;     literal lists only.
;
; and then records the declaration in the table `fn-interfaces'.  A failed
; check is a soft error naming the entry and the check.  The registry half
; is tools/interface_emit.py, which reads the same forms without evaluating
; them and generates planning/interfaces.json and tools/extract/roots.sh; its
; host-binding check reads the raw host itself (a declared entry the host
; never dispatches is stale; see that tool).
;
; This book includes only books/def-carried (whose row a `:raw-with
; (:carried NAME)' re-checks) and leaves no rule: its helpers are
; :program mode.  *fn-entry-guard-kinds* is read from the world
; (books/payload-kinds.lisp), not included, so the file that holds the
; declarations decides what is loaded.

(in-package "ACL2")
(include-book "def-carried") ; fn-cd-problem: a (:carried NAME) row re-checked

(defconst *fn-di-keys* '(:class :kinds :exempt :keystones :root :direct :delegates
                         :raw-with :raw-guarded))

(defconst *fn-di-classes* '(:common-lisp-compliant :ideal :program))

(defun fn-di-get (key kvs)
  (declare (xargs :mode :program))
  (cadr (assoc-keyword key kvs)))

(defun fn-di-unknown-keys (kvs)
  (declare (xargs :mode :program))
  (cond ((atom kvs) nil)
        ((member-eq (car kvs) *fn-di-keys*) (fn-di-unknown-keys (cddr kvs)))
        (t (cons (car kvs) (fn-di-unknown-keys (cddr kvs))))))

(defun fn-di-kinds-formp (x)
  (declare (xargs :mode :program))
  ; ((FORMAL RECOGNIZER) ...)
  (if (atom x)
      (null x)
    (and (true-listp (car x))
         (equal (len (car x)) 2)
         (symbolp (car (car x)))
         (symbolp (cadr (car x)))
         (fn-di-kinds-formp (cdr x)))))

(defun fn-di-exempt-formp (x)
  (declare (xargs :mode :program))
  ; ((FORMAL "why") ...), each reason non-empty
  (if (atom x)
      (null x)
    (and (true-listp (car x))
         (equal (len (car x)) 2)
         (symbolp (car (car x)))
         (stringp (cadr (car x)))
         (< 0 (length (cadr (car x))))
         (fn-di-exempt-formp (cdr x)))))

(defun fn-di-keystone-entryp (x)
  (declare (xargs :mode :program))
  (or (and (symbolp x) x t)
      (and (true-listp x)
           (equal (len x) 3)
           (symbolp (car x))
           (eq (cadr x) :via)
           (symbolp (caddr x)))))

(defun fn-di-keystones-formp (x)
  (declare (xargs :mode :program))
  (if (atom x)
      (null x)
    (and (fn-di-keystone-entryp (car x))
         (fn-di-keystones-formp (cdr x)))))

(defun fn-di-any-keyword (xs)
  (declare (xargs :mode :program))
  (and (consp xs) (or (keywordp (car xs)) (fn-di-any-keyword (cdr xs)))))

(defun fn-di-raw-with-formp (x)
  (declare (xargs :mode :program))
  ; (THM ...): a non-empty list of theorem names, none a keyword; or exactly
  ; (:carried NAME), the carried invariant whose row names them
  ; (books/def-carried.lisp)
  (and (consp x)
       (if (eq (car x) :carried)
           (and (consp (cdr x)) (null (cddr x)) (symbolp (cadr x)) (cadr x) t)
         (and (symbol-listp x) (not (member-eq nil x))
              (not (fn-di-any-keyword x))))))

(defun fn-di-raw-guarded-formp (x)
  (declare (xargs :mode :program))
  ; Exact ABI: (input-arity stobjs-in stobjs-out).
  (and (true-listp x) (equal (len x) 3) (natp (car x))
       (symbol-listp (cadr x)) (equal (len (cadr x)) (car x))
       (consp (caddr x)) (symbol-listp (caddr x))))

(defun fn-di-refusal (name kvs)
  (declare (xargs :mode :program))
  ; nil when the form is well-formed; else (REASON . DETAILS)
  (cond
   ((not (and (symbolp name) name)) (list :bad-name name))
   ((not (keyword-value-listp kvs)) (list :bad-options kvs))
   ((fn-di-unknown-keys kvs) (cons :unknown-keyword (fn-di-unknown-keys kvs)))
   ((not (member-eq (fn-di-get :class kvs) *fn-di-classes*))
    (list :bad-class (fn-di-get :class kvs)))
   ((not (fn-di-kinds-formp (fn-di-get :kinds kvs)))
    (list :bad-kinds (fn-di-get :kinds kvs)))
   ((not (fn-di-exempt-formp (fn-di-get :exempt kvs)))
    (list :bad-exempt (fn-di-get :exempt kvs)))
   ((not (no-duplicatesp-eq (strip-cars (fn-di-get :exempt kvs))))
    (list :duplicate-exempt (strip-cars (fn-di-get :exempt kvs))))
   ((not (fn-di-keystones-formp (fn-di-get :keystones kvs)))
    (list :bad-keystones (fn-di-get :keystones kvs)))
   ((not (member-eq (fn-di-get :root kvs) '(nil :extract :extract-extra)))
    (list :bad-root (fn-di-get :root kvs)))
   ((and (assoc-keyword :direct kvs)
         (not (and (stringp (fn-di-get :direct kvs))
                   (< 0 (length (fn-di-get :direct kvs))))))
    (list :bad-direct (fn-di-get :direct kvs)))
   ((and (assoc-keyword :delegates kvs)
         (not (and (symbolp (fn-di-get :delegates kvs))
                   (fn-di-get :delegates kvs))))
    (list :bad-delegates (fn-di-get :delegates kvs)))
   ((and (assoc-keyword :raw-with kvs)
         (not (fn-di-raw-with-formp (fn-di-get :raw-with kvs))))
    (list :bad-raw-with (fn-di-get :raw-with kvs)))
   ((and (assoc-keyword :raw-guarded kvs)
         (not (fn-di-raw-guarded-formp (fn-di-get :raw-guarded kvs))))
    (list :bad-raw-guarded (fn-di-get :raw-guarded kvs)))
   ((and (assoc-keyword :raw-guarded kvs) (assoc-keyword :raw-with kvs))
    (list :dual-raw-routes))
   (t nil)))

; -----------------------------------------------------------------------------
; What the world says.

(defun fn-di-conjuncts (term)
  (declare (xargs :mode :program))
  ; the conjuncts of a translated guard ((if a b 'nil) is a conjunction), in
  ; the order fnn-guard-conjuncts gives them
  (if (and (consp term) (eq (car term) 'if) (equal (cadddr term) *nil*))
      (append (fn-di-conjuncts (cadr term)) (fn-di-conjuncts (caddr term)))
    (list term)))

(defun fn-di-position (x xs i)
  (declare (xargs :mode :program))
  (cond ((atom xs) nil)
        ((eq x (car xs)) i)
        (t (fn-di-position x (cdr xs) (1+ i)))))

(defun fn-di-kind-checks (conjuncts formals stobjs kinds)
  (declare (xargs :mode :program))
  ; each (POSITION FORMAL RECOGNIZER) as fnn-entry-guard-spec collects it
  (if (atom conjuncts)
      nil
    (let* ((c (car conjuncts))
           (rest (fn-di-kind-checks (cdr conjuncts) formals stobjs kinds)))
      (if (and (consp c) (symbolp (car c)) (consp (cdr c)) (null (cddr c))
               (symbolp (cadr c)) (member-eq (cadr c) formals)
               (null (nth (fn-di-position (cadr c) formals 0) stobjs))
               (assoc-eq (car c) kinds))
          (cons (list (fn-di-position (cadr c) formals 0) (cadr c) (car c))
                rest)
        rest))))

(defun fn-di-insert (x sorted)
  (declare (xargs :mode :program))
  ; stable insertion by position (fnn-entry-guard-spec sorts by position)
  (cond ((atom sorted) (list x))
        ((< (car x) (car (car sorted))) (cons x sorted))
        (t (cons (car sorted) (fn-di-insert x (cdr sorted))))))

(defun fn-di-sort (xs)
  (declare (xargs :mode :program))
  (if (atom xs) nil (fn-di-insert (car xs) (fn-di-sort (cdr xs)))))

(defun fn-di-strip-positions (checks)
  (declare (xargs :mode :program))
  (if (atom checks)
      nil
    (cons (cdr (car checks)) (fn-di-strip-positions (cdr checks)))))

(defun fn-di-guard-kinds (w)
  (declare (xargs :mode :program))
  ; *fn-entry-guard-kinds* as the world holds it (a defconst's 'const
  ; property is the quoted value), or nil when it is not loaded
  (let ((q (getpropc '*fn-entry-guard-kinds* 'const nil w)))
    (if (and (consp q) (eq (car q) 'quote)) (cadr q) nil)))

(defun fn-di-world-kinds (name w)
  (declare (xargs :mode :program))
  ; ((FORMAL RECOGNIZER) ...) in position order: the host entry guard's checks
  (let ((formals (getpropc name 'formals :none w)))
    (if (eq formals :none)
        nil
      (fn-di-strip-positions
       (fn-di-sort
        (fn-di-kind-checks (fn-di-conjuncts (getpropc name 'guard *t* w))
                           formals
                           (getpropc name 'stobjs-in nil w)
                           (fn-di-guard-kinds w)))))))

(defun fn-di-callees (fns seen n w)
  (declare (xargs :mode :program))
  ; the call closure of FNS (at most N functions): every function whose
  ; definition some function in it calls
  (cond ((or (atom fns) (zp n)) seen)
        ((member-eq (car fns) seen) (fn-di-callees (cdr fns) seen n w))
        (t (let ((body (getpropc (car fns) 'unnormalized-body nil w)))
             (fn-di-callees (append (all-fnnames body) (cdr fns))
                            (cons (car fns) seen)
                            (1- n) w)))))

(defun fn-di-keystone-problem (name entry w)
  (declare (xargs :mode :program))
  (let* ((thm (if (symbolp entry) entry (car entry)))
         (target (if (symbolp entry) name (caddr entry)))
         (formula (getpropc thm 'theorem nil w)))
    (cond ((null formula)
           (msg "keystone ~x0 is not a theorem in this world" thm))
          ((not (member-eq target (all-fnnames formula)))
           (msg "keystone ~x0 does not call ~x1" thm target))
          ((and (consp entry)
                (not (member-eq target (fn-di-callees (list name) nil 100000 w))))
           (msg "keystone ~x0's function ~x1 is not in ~x2's call closure"
                thm target name))
          (t nil))))

(defun fn-di-keystones-problem (name entries w)
  (declare (xargs :mode :program))
  (if (atom entries)
      nil
    (or (fn-di-keystone-problem name (car entries) w)
        (fn-di-keystones-problem name (cdr entries) w))))

(defun fn-di-exempt-problem (exempt formals kinds)
  (declare (xargs :mode :program))
  (cond ((atom exempt) nil)
        ((not (member-eq (car (car exempt)) formals))
         (msg ":exempt names ~x0, which is not a formal" (car (car exempt))))
        ((assoc-eq (car (car exempt)) kinds)
         (msg ":exempt names ~x0, which the guard kinds" (car (car exempt))))
        (t (fn-di-exempt-problem (cdr exempt) formals kinds))))

(defun fn-di-delegates-problem (name callee w)
  (declare (xargs :mode :program))
  ; :delegates CALLEE: NAME's decision is CALLEE's because NAME's body is
  ; exactly CALLEE applied to NAME's formals -- every theorem about CALLEE is
  ; one about NAME by definition (tools/coverage.py files the entry as
  ; plumbing that delegates, and refuses it when CALLEE has no direct
  ; theorem).  A wrapper that branches, projects or reorders is not one.
  (cond ((null callee) nil)
        ((eq (getpropc callee 'formals :none w) :none)
         (msg ":delegates ~x0, which is not a function in this world" callee))
        ((not (equal (getpropc name 'unnormalized-body nil w)
                     (cons callee (getpropc name 'formals nil w))))
         (msg "~x0's body is not exactly ~x1 applied to ~x0's formals, so it ~
               does not delegate its decision to ~x1"
              name callee))
        (t nil)))

; -----------------------------------------------------------------------------
; :raw-with (D40).  The conjuncts raw dispatch leaves unevaluated are the
; guard's conjuncts that are not kind checks; the annotation names the
; theorems that establish and preserve them.

(defun fn-di-conjunct-head (c)
  (declare (xargs :mode :program))
  ; the function symbol a translated conjunct applies (through a let's
  ; lambda); nil for a variable or a constant
  (cond ((atom c) nil)
        ((eq (car c) 'quote) nil)
        ((consp (car c)) (fn-di-conjunct-head (car (last (car c)))))
        (t (car c))))

(defun fn-di-non-stobj-vars (vars formals stobjs)
  (declare (xargs :mode :program))
  ; the variables of VARS that are formals the host passes (not stobjs)
  (cond ((atom vars) nil)
        ((and (member-eq (car vars) formals)
              (null (nth (fn-di-position (car vars) formals 0) stobjs)))
         (cons (car vars) (fn-di-non-stobj-vars (cdr vars) formals stobjs)))
        (t (fn-di-non-stobj-vars (cdr vars) formals stobjs))))

(defun fn-di-stobj-recognizer-conjunctp (c formals stobjs w)
  (declare (xargs :mode :program))
  ; (R v) with v a stobj formal and R its exact world recognizer:
  ; accessors also carry the stobj-function property, but a field's value
  ; is not established by the stobj calling convention. The discipline
  ; establishes it -- the live stobj is that stobj -- so raw dispatch skips
  ; nothing here
  (and (consp c) (symbolp (car c)) (consp (cdr c)) (null (cddr c))
       (symbolp (cadr c)) (member-eq (cadr c) formals)
       (nth (fn-di-position (cadr c) formals 0) stobjs)
       (eq (car c) (get-stobj-recognizer (cadr c) w))))

(defun fn-di-invariant-conjuncts (conjuncts formals stobjs kinds w)
  (declare (xargs :mode :program))
  ; the conjuncts fnn-entry-guard does not evaluate and no discipline holds:
  ; every conjunct that is neither a kind check on a non-stobj formal nor a
  ; stobj formal's own recognizer
  (cond ((atom conjuncts) nil)
        ((or (fn-di-kind-checks (list (car conjuncts)) formals stobjs kinds)
             (fn-di-stobj-recognizer-conjunctp (car conjuncts) formals stobjs w))
         (fn-di-invariant-conjuncts (cdr conjuncts) formals stobjs kinds w))
        (t (cons (car conjuncts)
                 (fn-di-invariant-conjuncts (cdr conjuncts) formals stobjs kinds w)))))

(defun fn-di-conjunct-over-argument (conjuncts formals stobjs)
  (declare (xargs :mode :program))
  ; the first invariant conjunct that constrains a host-passed argument, as
  ; (CONJUNCT . VARIABLE); nil when every one is over stobjs alone
  (cond ((atom conjuncts) nil)
        ((fn-di-non-stobj-vars (all-vars (car conjuncts)) formals stobjs)
         (cons (car conjuncts)
               (car (fn-di-non-stobj-vars (all-vars (car conjuncts)) formals stobjs))))
        (t (fn-di-conjunct-over-argument (cdr conjuncts) formals stobjs))))

(defun fn-di-invariant-heads (conjuncts w)
  (declare (xargs :mode :program))
  ; the heads the tree defines, each once; a boot-strap primitive is exempt
  (cond ((atom conjuncts) nil)
        (t (let ((head (fn-di-conjunct-head (car conjuncts)))
                 (rest (fn-di-invariant-heads (cdr conjuncts) w)))
             (if (and head
                      (not (getpropc head 'predefined nil w))
                      (not (member-eq head rest)))
                 (cons head rest)
               rest)))))

(defun fn-di-theorem-conclusion (formula)
  (declare (xargs :mode :program))
  (if (and (consp formula) (eq (car formula) 'implies))
      (fn-di-theorem-conclusion (caddr formula))
    formula))

(defun fn-di-missing-theorem (thms w)
  (declare (xargs :mode :program))
  (cond ((atom thms) nil)
        ((null (getpropc (car thms) 'theorem nil w)) (car thms))
        (t (fn-di-missing-theorem (cdr thms) w))))

(defun fn-di-positive-conclusion-headp (head formula)
  (declare (xargs :mode :program))
  ; Occurrence is not establishment: NOT, IFF and EQUAL can all mention
  ; HEAD while concluding its failure. Only a positive top-level conjunct
  ; counts here. This remains a declaration lint, not a guard proof.
  (let ((conclusion (fn-di-theorem-conclusion formula)))
    (and (consp conclusion) (eq (car conclusion) head))))

(defun fn-di-concluding-theorems (head thms w)
  (declare (xargs :mode :program))
  ; the theorems of THMS whose conclusion applies HEAD
  (cond ((atom thms) nil)
        ((fn-di-positive-conclusion-headp
          head (getpropc (car thms) 'theorem nil w))
         (cons (car thms) (fn-di-concluding-theorems head (cdr thms) w)))
        (t (fn-di-concluding-theorems head (cdr thms) w))))

(defun fn-di-unconcluded-head (heads thms w)
  (declare (xargs :mode :program))
  (cond ((atom heads) nil)
        ((null (fn-di-concluding-theorems (car heads) thms w)) (car heads))
        (t (fn-di-unconcluded-head (cdr heads) thms w))))

(defun fn-di-theorems-fnnames (thms w)
  (declare (xargs :mode :program))
  (if (atom thms)
      nil
    (append (all-fnnames (getpropc (car thms) 'theorem nil w))
            (fn-di-theorems-fnnames (cdr thms) w))))

(defun fn-di-guard-preservation-theoremp (name head formula guard)
  (declare (xargs :mode :program))
  ; A deliberately narrow lint: a positive conclusion about this entry,
  ; with no hypothesis stronger than its literal guard. It does not establish
  ; the initial invariant or identify the right returned stobj/effects.
  (and (consp formula) (eq (car formula) 'implies)
       (fn-di-positive-conclusion-headp head formula)
       (member-eq name (all-fnnames (caddr formula)))
       (subsetp-equal (fn-di-conjuncts (cadr formula))
                     (fn-di-conjuncts guard))))

(defun fn-di-has-guard-preservation (name head thms guard w)
  (declare (xargs :mode :program))
  (and (consp thms)
       (or (fn-di-guard-preservation-theoremp
            name head (getpropc (car thms) 'theorem nil w) guard)
           (fn-di-has-guard-preservation name head (cdr thms) guard w))))

(defun fn-di-unpreserved-head (name heads thms guard w)
  (declare (xargs :mode :program))
  (cond ((atom heads) nil)
        ((not (fn-di-has-guard-preservation name (car heads) thms guard w))
         (car heads))
        (t (fn-di-unpreserved-head name (cdr heads) thms guard w))))

(defun fn-di-related-fnnames (heads thms w)
  (declare (xargs :mode :program))
  ; the heads, and every function a theorem concluding one of them mentions:
  ; what a named theorem must be about
  (if (atom heads)
      nil
    (append (cons (car heads)
                  (fn-di-theorems-fnnames (fn-di-concluding-theorems (car heads) thms w) w))
            (fn-di-related-fnnames (cdr heads) thms w))))

(defun fn-di-unrelated-theorem (thms related w)
  (declare (xargs :mode :program))
  (cond ((atom thms) nil)
        ((null (intersection-eq (all-fnnames (getpropc (car thms) 'theorem nil w))
                                related))
         (car thms))
        (t (fn-di-unrelated-theorem (cdr thms) related w))))

(defun fn-di-raw-with-theorems (name kvs w)
  (declare (xargs :mode :program))
  ; the theorems a :raw-with names: the literal list, or for (:carried N)
  ; only the statements def-carried GENERATED for NAME (books/def-carried.lisp
  ; fn-cd-raw-with: N-NAME-carries and every N-PRED-bridge); nil when N is no
  ; carried invariant of this world or NAME no transition of it
  (let ((form (fn-di-get :raw-with kvs)))
    (if (and (consp form) (eq (car form) :carried))
        (fn-cd-raw-with (cadr form) name w)
      form)))

(defun fn-di-defined-conjuncts (conjuncts w)
  (declare (xargs :mode :program))
  ; CONJUNCTS less those a boot-strap primitive heads (fn-di-invariant-heads)
  (cond ((atom conjuncts) nil)
        ((let ((head (fn-di-conjunct-head (car conjuncts))))
           (or (null head) (getpropc head 'predefined nil w)))
         (fn-di-defined-conjuncts (cdr conjuncts) w))
        (t (cons (car conjuncts) (fn-di-defined-conjuncts (cdr conjuncts) w)))))

(defun fn-di-raw-with-list-problem (name thms heads w)
  (declare (xargs :mode :program))
  ; a literal :raw-with list: the declaration lint (occurrence, not proof)
  (let ((missing (fn-di-missing-theorem thms w))
        (unconcluded (fn-di-unconcluded-head heads thms w))
        (unpreserved (fn-di-unpreserved-head
                      name heads thms (getpropc name 'guard *t* w) w))
        (unrelated (fn-di-unrelated-theorem
                    thms (fn-di-related-fnnames heads thms w) w)))
    (cond
     (missing
      (msg ":raw-with names ~x0, which is not a theorem in this world" missing))
     (unconcluded
      (msg ":raw-with on ~x0: no named theorem concludes ~x1, a guard ~
            conjunct raw dispatch leaves unevaluated (the named theorems ~
            are ~&2)" name unconcluded thms))
     (unpreserved
      (msg ":raw-with on ~x0: no named positive preservation theorem for ~x1 ~
            mentions this entry under no hypotheses stronger than its guard"
           name unpreserved))
     (unrelated
      (msg ":raw-with names ~x0, which mentions no function of ~x1's ~
            guard argument (~&2)" unrelated name
           (fn-di-related-fnnames heads thms w)))
     (t nil))))

(defun fn-di-raw-with-problem (name kvs w)
  (declare (xargs :mode :program))
  ; nil, or a msg naming the first check the world refutes.  For (:carried
  ; N) nothing a user wrote is consulted: def-carried's row, re-checked here
  ; with every generated statement regenerated and compared, must back NAME
  ; (fn-cd-raw-problem), and every skipped guard conjunct must be N's
  ; invariant of NAME's state or a conjunct of a generated bridge
  ; (fn-cd-uncovered-conjunct).
  (let ((form (fn-di-get :raw-with kvs)))
    (if (null form)
        nil
      (let* ((carried (and (eq (car form) :carried) (cadr form)))
             (formals (getpropc name 'formals nil w))
             (stobjs (getpropc name 'stobjs-in nil w))
             (conjuncts (fn-di-invariant-conjuncts
                         (fn-di-conjuncts (getpropc name 'guard *t* w))
                         formals stobjs (fn-di-guard-kinds w) w))
             (over-argument (fn-di-conjunct-over-argument conjuncts formals stobjs))
             (heads (fn-di-invariant-heads conjuncts w)))
        (cond
         ((and carried (fn-cd-raw-problem carried name w))
          (msg ":raw-with ~x0 on ~x1: ~@2" form name (fn-cd-raw-problem carried name w)))
         ((not (eq (fn-di-get :class kvs) :common-lisp-compliant))
          (msg ":raw-with on ~x0, which is not :common-lisp-compliant: only a ~
                guard-verified definition executes faithfully raw" name))
         (over-argument
          (msg ":raw-with on ~x0, whose guard conjunct ~x1 constrains the ~
                host-passed argument ~x2: no preservation theorem establishes ~
                a per-call argument, and raw dispatch would leave it unchecked"
               name (car over-argument) (cdr over-argument)))
         ((null heads)
          (msg ":raw-with on ~x0, whose guard has no conjunct beyond its kind ~
                checks and boot-strap primitives: raw dispatch would skip ~
                nothing" name))
         (carried
          (let ((c (fn-cd-uncovered-conjunct
                    carried name (fn-di-defined-conjuncts conjuncts w) w)))
            (and c
                 (msg ":raw-with ~x0 on ~x1: guard conjunct ~x2 is neither the ~
                       carried invariant of ~x1's state nor a conjunct of a ~
                       generated bridge" form name c))))
         (t (fn-di-raw-with-list-problem name form heads w)))))))

(defun fn-di-raw-guarded-conjunctsp (conjuncts formals slots w)
  (declare (xargs :mode :program))
  (if (atom conjuncts) (null conjuncts)
    (and (or (equal (car conjuncts) '(quote t))
             (fn-di-stobj-recognizer-conjunctp (car conjuncts) formals slots w))
         (fn-di-raw-guarded-conjunctsp (cdr conjuncts) formals slots w))))

(defun fn-di-raw-guarded-problem (name kvs w)
  (declare (xargs :mode :program))
  ; Distinct from raw-with: this route skips NO invariant/kind guard.
  ; Host ownership must supply the genuine instances named by the slots.
  (if (not (assoc-keyword :raw-guarded kvs)) nil
    (let ((spec (fn-di-get :raw-guarded kvs))
          (formals (getpropc name 'formals :none w)))
      (cond
       ((assoc-keyword :raw-with kvs) (msg "~x0 declares incompatible raw routes" name))
       ((not (fn-di-raw-guarded-formp spec)) (msg "~x0 has malformed raw-guarded ABI ~x1" name spec))
       ((not (and (eq (fn-di-get :class kvs) :common-lisp-compliant)
                  (eq (symbol-class name w) :common-lisp-compliant)))
        (msg "~x0 is not declared and verified for raw-guarded execution" name))
       ((eq formals :none) (msg "~x0 has no validated formals" name))
       ((not (equal (car spec) (len formals))) (msg "~x0 raw-guarded arity disagrees with its world" name))
       ((not (equal (cadr spec) (stobjs-in name w))) (msg "~x0 raw-guarded input slots disagree with its world" name))
       ((not (equal (caddr spec) (stobjs-out name w))) (msg "~x0 raw-guarded output slots disagree with its world" name))
       ((not (fn-di-raw-guarded-conjunctsp
               (fn-di-conjuncts (guard name nil w))
               formals (stobjs-in name w) w))
        (msg "~x0 raw-guarded guard contains a kind, invariant, or relation beyond supplied stobj recognition" name))
       (t nil)))))

(defun fn-di-raw-guarded-target (name kvs w)
  (declare (xargs :mode :program))
  ; Only a creator may resolve through the registered abstract stobj EXEC.
  ; Ordinary callbacks retain their original subject and raw definition.
  (let ((problem (fn-di-raw-guarded-problem name kvs w)))
    (if problem (mv problem nil)
      (let* ((outputs (stobjs-out name w))
             (st (and (equal (len outputs) 1) (car outputs)))
             (candidatep (and st (equal (getpropc name 'formals :none w) nil)
                              (equal (stobjs-in name w) nil)))
             (creatorp (and candidatep (eq name (get-stobj-creator st w))))
             (info (and creatorp (getpropc st 'absstobj-info nil w))))
        (if (and candidatep (not creatorp))
            (mv (msg "~x0 lacks its registered stobj creator role" name) nil)
          (if (not info)
              (if (and creatorp
                       (not (eq (car (get-event st w)) 'defstobj)))
                  (mv (msg "~x0 lacks registered abstract creator metadata" name) nil)
                (mv nil name))
          (let* ((foundation (and (consp info) (car info)))
                 (entry (and (true-listp info) (alistp (cdr info))
                             (assoc-eq name (cdr info))))
                 (target (and (true-listp entry) (equal (len entry) 3)
                              (caddr entry))))
            (if (and (symbolp foundation) foundation
                     (not (eq foundation st))
                     target (symbolp target)
                     (eq target (get-stobj-creator foundation w))
                     (equal (getpropc name 'formals :none w) nil)
                     (equal (getpropc target 'formals :none w) nil)
                     (equal (stobjs-in target w) nil)
                     (equal (stobjs-out target w) (list foundation))
                     (eq (symbol-class target w) :common-lisp-compliant)
                     (fn-di-raw-guarded-conjunctsp
                      (fn-di-conjuncts (guard target nil w)) nil nil w))
                (mv nil target)
              (mv (msg "~x0 has missing or incompatible registered creator EXEC metadata" name) nil)))))))))

(defun fn-di-problem (name kvs w)
  (declare (xargs :mode :program))
  ; nil, or a msg naming the first check the world refutes
  (let ((formals (getpropc name 'formals :none w)))
    (cond
     ((eq formals :none) (msg "~x0 is not a function in this world" name))
     ((not (eq (symbol-class name w) (fn-di-get :class kvs)))
      (msg "~x0 is ~x1, declared ~x2" name (symbol-class name w)
           (fn-di-get :class kvs)))
     ((not (equal (fn-di-world-kinds name w) (fn-di-get :kinds kvs)))
      (msg "~x0's guard kinds are ~x1 (the host entry guard's), declared ~x2"
           name (fn-di-world-kinds name w) (fn-di-get :kinds kvs)))
     ((fn-di-exempt-problem (fn-di-get :exempt kvs) formals
                            (fn-di-world-kinds name w)))
     ((fn-di-keystones-problem name (fn-di-get :keystones kvs) w))
     ((fn-di-delegates-problem name (fn-di-get :delegates kvs) w))
     ((fn-di-raw-with-problem name kvs w))
     ((fn-di-raw-guarded-problem name kvs w))
     (t nil))))

(defun fn-di-refusal-text (reason)
  (declare (xargs :mode :program))
  (case (car reason)
    (:bad-class (msg ":class ~x0 is not one of ~&1." (cadr reason) *fn-di-classes*))
    (:unknown-keyword (msg "unknown keyword(s) ~&0; the keywords are ~&1."
                           (cdr reason) *fn-di-keys*))
    (:bad-root (msg ":root ~x0 is not :extract or :extract-extra." (cadr reason)))
    (:bad-delegates (msg ":delegates ~x0 is not a function name." (cadr reason)))
    (:bad-raw-guarded (msg ":raw-guarded ~x0 is not an exact (arity input-slots output-slots) ABI." (cadr reason)))
    (:dual-raw-routes (msg ":raw-with and :raw-guarded are incompatible."))
    (:bad-raw-with (msg ":raw-with ~x0 is not a non-empty list of theorem names."
                        (cadr reason)))
    (otherwise (msg "malformed form: ~x0." reason))))

; The events a checked declaration adds: the table entry, and for a declared
; :delegates CALLEE the wrapper equation NAME-is-CALLEE-by-definition, which
; NAME's definition proves at once (the 2026-09-29 review: a true alias gets
; its equating theorem generated, so the world -- not a source-form rule --
; carries that every theorem about CALLEE is one about NAME; a wrapper that
; transforms gets a keystone instead).  :rule-classes nil: it is a
; restatement, cited by nothing, and never a rewrite.
(defun fn-di-events (name kvs w)
  (declare (xargs :mode :program))
  (let ((callee (fn-di-get :delegates kvs))
        (formals (getpropc name 'formals nil w)))
    (if callee
        `(progn (table fn-interfaces ',name ',kvs)
                (defthm ,(intern-in-package-of-symbol
                          (concatenate 'string (symbol-name name) "-IS-"
                                       (symbol-name callee) "-BY-DEFINITION")
                          name)
                  (equal (,name ,@formals) (,callee ,@formals))
                  :rule-classes nil
                  :hints (("Goal" :in-theory '(,name)))))
      `(table fn-interfaces ',name ',kvs))))

(defmacro definterface (name &rest kvs)
  (let ((reason (fn-di-refusal name kvs)))
    (if reason
        `(make-event (er soft 'definterface "~x0: ~@1" ',name
                         ',(fn-di-refusal-text reason)))
      `(make-event
        (let ((problem (fn-di-problem ',name ',kvs (w state))))
          (if problem
              (er soft 'definterface "~x0: ~@1" ',name problem)
            (value (fn-di-events ',name ',kvs (w state)))))
))))
