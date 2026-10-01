; fn: `def-carried' --- a carried invariant from one declaration.  The
; generator writes the statements D40's raw dispatch trusts, from the world,
; and proves them with the declared theorems as hints only; the obligation
; table is checked complete against the world; the trace theorem follows by
; functional instantiation of a generic theory
; (planning/design-store-representation-2026-10-01.md section 3;
; build/coordinator/lanedumps/deputy-1.md section 3).
;
; AGENTS.md: "No whole-state revalidation on a served path: carry the
; invariant in state and prove it preserved."
;
;   (def-carried NAME
;     :invariant R                    ; a function of one formal, the state
;     :established ((FN THM [:hyps (H ...)] [:state I] [:result P]
;                       [:ok OK :witness (T ...)]
;                       [:produced ((P THM [:assuming (A ...)]) ...)]) ...)
;     :transitions ((FN THM [:hyps (H ...)] [:state I] [:result P]) | FN ...)
;     [:concludes ((PRED THM) ...)]   ; bridges to the entry guards
;     [:complete-by (:enumeration "why")]   ; a value state only
;     [:trace nil])
;
; THE STATEMENTS ARE GENERATED.  Nothing reads a declared theorem's
; statement: THM is only `:use'd, in the minimal theory, to prove an event
; this book writes.  With s the carried formal of FN, G FN's guard from the
; world, Hs the declared :hyps and RET the carried state FN returns:
;
;   NAME-FN-carries      (implies (and (R s) G H...) (R RET))   per transition
;   NAME-FN-establishes  (implies (and G H...) (R RET))         per open
;                        (implies (and G H...) (if OK (R RET) t)) per open
;                        that can REFUSE, declaring :ok OK, a term over `_'
;                        (the call) alone: its success word.  An open that
;                        refuses establishes nothing on its refusal arm; the
;                        word is the open's own answer, which the host
;                        branches on, never a premise about its input, so
;                        such a row still backs raw dispatch.  :ok on a
;                        transition is refused (one that refuses and leaves
;                        the state preserves R already).
;   NAME-FN-reaches      (and G H... [OK]) at a declared :witness  per open
;                        declaring :witness (required with :ok; required on
;                        every open of a row that backs raw dispatch, r24-F1:
;                        otherwise a never-true guard or invariant makes
;                        every statement vacuous and the transitions' skipped
;                        guards unjustified).
;                        :witness (T1 ... Tn), one term per formal of FN
;                        (stobj formals included, as terms over their
;                        logical values), and the statement is G, the Hs
;                        and OK with each formal replaced by its Ti.  A
;                        theorem, so some instance of FN's arguments meets
;                        the guard and the open answers success there: OK
;                        is not never-true, and the conditional
;                        establishment is not vacuous.  (A Ti may mention
;                        variables; the theorem then holds at every
;                        instance, in particular a ground one.)  The
;                        reachability is a WORLD FACT, not a probe: the row
;                        records :witness and :reaches, and fn-cd-problem
;                        regenerates the statement and demands the theorem
;                        by the exact-formula rule, so a hand-written
;                        `table fn-carried' row with a never-true OK has no
;                        provable reaches theorem and backs no raw dispatch
;                        (hole H1, deputy2/def-carried-ok).
;   NAME-FN-P-produced   (implies (and A...) (and H...)[F := (P pf...)])
;                        per producer P of an open's argument F.  An open
;                        whose establishment needs premises Hs its guard
;                        does not say (all over ONE formal F) names the
;                        functions whose output the host hands it there
;                        (:produced), each with THM and the NAMED
;                        ASSUMPTIONS As over P's formals pf it rests on
;                        (applications of encapsulate-constrained FN-ASSUME-
;                        functions, books/assumptions*.lisp).  D40 then
;                        accepts the open's :hyps -- discharged, not unchecked
;                        -- when FN is not itself a host entry
;                        (fn-interfaces) and every function body in the world
;                        that calls FN passes a literal call of a declared P
;                        at F (fn-cd-produced-host-problem; a let-bound or
;                        computed argument is refused).  Raw dispatch then
;                        rests on the As, named.  Transitions take no :hyps.
;   NAME-PRED-bridge     (implies (R x) (and C...))             per bridge
;
; where the Cs are every conjunct of a listed transition's guard that
; applies PRED to that transition's carried formal alone, renamed to x (R's
; formal).  RET is derived, never declared, when R's formal is a stobj ST:
; s is FN's ST argument (stobjs-in) and RET is the call itself or
; (mv-nth K call) at ST's place in stobjs-out; :state and :result are
; refused there.  A VALUE state (a record the host threads) has no such
; world fact: the entry says :state I (FN's I-th formal) and :result P (a
; term over `_', the call; default `_'), and the row is a model-level claim
; that backs no raw dispatch.  So a true theorem about another term -- a
; repaired result, a composed call, another state -- proves no generated
; statement, and is refused where the proof fails.
;
; Admission refuses, each by name: a malformed form; R not a unary
; function; a redeclared NAME; a bare transition (the obligation stated);
; an entry whose statement cannot be generated (no ST argument or result;
; :hyps over other variables); a bridge with no guard conjunct to conclude;
; COMPLETENESS -- for a stobj state, every `fn-interfaces' entry
; (books/definterface.lisp) whose stobjs-out returns ST must be listed, so
; the table is complete wherever the declarations are loaded (the image
; world; `def-carried-check' re-runs it there and definterface runs it at
; every `:raw-with (:carried NAME)'); a value state must say :complete-by,
; and a stobj state may not; VACUITY, refuted under *fn-cd-vacuity-steps*
; in the minimal theory: (R x) must not be provable, nor any entry's
; hypotheses contradictory (a bounded probe, not a witness: the teeth book
; carries the ground witnesses); and any generated statement ACL2 does not
; prove.
;
; Emits the row (table fn-carried NAME '(:invariant R :state ST|nil
; :established ((FN THM :name NAME-FN-establishes :hyps (H...)
; [:ok OK :witness (T...) :reaches NAME-FN-reaches] [:state I :result P]) ...) :transitions (... :name NAME-FN-carries ...)
; :concludes ((PRED THM :name NAME-PRED-bridge) ...) :complete-by ...
; :trace t|nil)), the generated theorems, and unless :trace nil the trace:
; NAME-step/-okp/-run/-run-okp (defun-nx; okp is G and the Hs at the event)
; and NAME-run-carries, (implies (and (R s) (NAME-run-okp s es)) (R
; (NAME-run s es))), by functional instantiation of fn-cd-run-carries.
;
; D40 (books/definterface.lisp `:raw-with (:carried NAME)') resolves ONLY to
; generated names -- NAME-FN-carries and every NAME-PRED-bridge
; (fn-cd-raw-with) -- and accepts the entry only when fn-cd-raw-problem is
; nil: a stobj row, FN a transition, the row re-checked in the current
; world with every generated name's formula EQUAL to the statement
; regenerated now (so a hand-written table row naming another theorem is
; refused), a non-empty :established whose every open declares :witness
; (its generated NAME-FN-reaches present, r24-F1: R holds of some state),
; and no :hyps in the row but an open's premises discharged by
; its producers (a declared hypothesis is a premise the host does not check:
; every transition of a raw row is guard-only, every open guard-only or
; produced).  Each skipped guard conjunct must then be (R s) itself or
; a conjunct of a generated bridge (fn-cd-uncovered-conjunct).
;
; What is NOT claimed: that the host calls nothing else returning ST is the
; completeness check over `fn-interfaces' (tools/interface_emit.py refuses
; an undeclared dispatch); that the entry guard runs before raw dispatch is
; host/native/io.lisp's.  A value row's enumeration is the claim it says.

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

(defconst *fn-cd-entry-keys* '(:hyps :state :result :ok :witness :produced))

(defconst *fn-cd-vacuity-steps* 50000)

(defun fn-cd-get (key kvs)
  (declare (xargs :mode :program))
  (cadr (assoc-keyword key kvs)))

(defun fn-cd-unknown-keys (kvs keys)
  (declare (xargs :mode :program))
  (cond ((atom kvs) nil)
        ((member-eq (car kvs) keys) (fn-cd-unknown-keys (cddr kvs) keys))
        (t (cons (car kvs) (fn-cd-unknown-keys (cddr kvs) keys)))))

(defun fn-cd-producersp (x)
  (declare (xargs :mode :program))
  ; ((PRODUCER THM [:assuming (A ...)]) ...)
  (if (atom x)
      (null x)
    (and (true-listp (car x)) (consp (cdar x))
         (symbolp (caar x)) (caar x) (symbolp (cadar x)) (cadar x)
         (keyword-value-listp (cddar x))
         (null (fn-cd-unknown-keys (cddar x) '(:assuming)))
         (true-listp (fn-cd-get :assuming (cddar x)))
         (fn-cd-producersp (cdr x)))))

(defun fn-cd-entryp (x)
  (declare (xargs :mode :program))
  ; (FN THM . OPTIONS): FN and THM non-nil symbols, OPTIONS over
  ; *fn-cd-entry-keys* with :hyps a list
  (and (true-listp x) (consp (cdr x))
       (symbolp (car x)) (car x) (symbolp (cadr x)) (cadr x)
       (keyword-value-listp (cddr x))
       (null (fn-cd-unknown-keys (cddr x) *fn-cd-entry-keys*))
       (true-listp (fn-cd-get :hyps (cddr x)))
       (true-listp (fn-cd-get :witness (cddr x)))
       (fn-cd-producersp (fn-cd-get :produced (cddr x)))))

(defun fn-cd-entriesp (x bare-ok)
  (declare (xargs :mode :program))
  (if (atom x)
      (null x)
    (and (or (fn-cd-entryp (car x)) (and bare-ok (symbolp (car x)) (car x)))
         (fn-cd-entriesp (cdr x) bare-ok))))

(defun fn-cd-pairsp (x)
  (declare (xargs :mode :program))
  (if (atom x)
      (null x)
    (and (true-listp (car x)) (equal (len (car x)) 2)
         (symbolp (caar x)) (caar x) (symbolp (cadar x)) (cadar x)
         (fn-cd-pairsp (cdr x)))))

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
   ((fn-cd-unknown-keys kvs *fn-cd-keys*)
    (cons :unknown-keyword (fn-cd-unknown-keys kvs *fn-cd-keys*)))
   ((not (and (fn-cd-get :invariant kvs) (symbolp (fn-cd-get :invariant kvs))))
    (list :no-invariant name))
   ((not (fn-cd-entriesp (fn-cd-get :established kvs) nil))
    (list :bad-established (fn-cd-get :established kvs)))
   ((null (fn-cd-get :established kvs)) (list :no-established name))
   ((not (fn-cd-entriesp (fn-cd-get :transitions kvs) t))
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
    (:no-established (msg "~x0 has no :established ((FN THM ...) ...): a ~
                           carried invariant names where the host first ~
                           obtains it." (cadr reason)))
    (:bad-established (msg ":established ~x0 is not ((FN THM [:hyps (H ...)] ~
                           [:state I] [:result P]) ...)." (cadr reason)))
    (:bad-transitions (msg ":transitions ~x0 is not ((FN THM [:hyps (H ...)] ~
                           [:state I] [:result P]) | FN ...)." (cadr reason)))
    (:bad-concludes (msg ":concludes ~x0 is not ((PRED THM) ...)." (cadr reason)))
    (:bad-complete-by (msg ":complete-by ~x0 is not (:enumeration \"why\")."
                           (cadr reason)))
    (:bad-trace (msg ":trace ~x0 is not t or nil." (cadr reason)))
    (:unknown-keyword (msg "unknown keyword(s) ~&0; the keywords are ~&1."
                           (cdr reason) *fn-cd-keys*))
    (otherwise (msg "malformed form: ~x0." reason))))

; ---------------------------------------------------------------------------
; The generated statements, from the world.

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

(defun fn-cd-conj (terms)
  (declare (xargs :mode :program))
  ; the translated (and . TERMS)
  (cond ((atom terms) *t*)
        ((atom (cdr terms)) (car terms))
        (t (list 'if (car terms) (fn-cd-conj (cdr terms)) *nil*))))

(defun fn-cd-state-stobj (r w)
  (declare (xargs :mode :program))
  ; the stobj R's one formal is, or nil for a value
  (car (getpropc r 'stobjs-in nil w)))

(defun fn-cd-stobj-position (st slots w)
  (declare (xargs :mode :program))
  ; the first position in SLOTS (a stobjs-in or stobjs-out) holding ST or a
  ; stobj congruent to it, which a caller may pass the live ST
  (cond ((atom slots) nil)
        ((and (car slots)
              (eq (congruent-stobj-rep (car slots) w) (congruent-stobj-rep st w)))
         0)
        (t (let ((k (fn-cd-stobj-position st (cdr slots) w))) (and k (1+ k))))))

(defun fn-cd-translate-list (xs w)
  (declare (xargs :mode :program))
  ; (mv BAD TERMS): BAD = (X) for the first X that does not translate
  (if (atom xs)
      (mv nil nil)
    (mv-let (erp val)
      (translate-cmp (car xs) t t t 'def-carried w (default-state-vars nil))
      (if erp
          (mv (list (car xs)) nil)
        (mv-let (bad rest) (fn-cd-translate-list (cdr xs) w)
          (mv bad (cons val rest)))))))

(defun fn-cd-normal-producers (name fn producers w)
  (declare (xargs :mode :program))
  ; (mv BAD PRODUCERS'): each (P THM :assuming (A'...) :name NAME-FN-P-produced)
  ; with its assumptions translated
  (if (atom producers)
      (mv nil nil)
    (mv-let (bad as)
      (fn-cd-translate-list (fn-cd-get :assuming (cddar producers)) w)
      (if bad
          (mv bad nil)
        (mv-let (bad rest)
          (fn-cd-normal-producers name fn (cdr producers) w)
          (mv bad (cons (list (caar producers) (cadar producers)
                              :assuming as
                              :name (packn-pos (list name '- fn '- (caar producers)
                                                     '-produced)
                                               name))
                        rest)))))))

(defun fn-cd-normal-entry (name suffix st entry w)
  (declare (xargs :mode :program))
  ; (mv MSG ENTRY'): ENTRY with its generated name and translated options
  (let* ((fn (car entry))
         (opts (cddr entry))
         (result (if (assoc-keyword :result opts) (fn-cd-get :result opts) '_)))
    (cond
     ((null (getpropc (cadr entry) 'theorem nil w))
      (mv (msg "~x0 names ~x1, which is not a theorem in this world"
               fn (cadr entry))
          nil))
     ((and st (or (assoc-keyword :state opts) (assoc-keyword :result opts)))
      (mv (msg "~x0: the carried state is the stobj ~x1, so its place in ~
                ~x0's arguments and result is the world's (stobjs-in, ~
                stobjs-out), never declared: drop :state and :result" fn st)
          nil))
     ((and (null st) (eq suffix '-carries) (not (natp (fn-cd-get :state opts))))
      (mv (msg "~x0: the carried state is a value, so say which formal it ~
                is: :state I, a 0-based position" fn)
          nil))
     ((and (null st) (assoc-keyword :state opts) (not (natp (fn-cd-get :state opts))))
      (mv (msg "~x0: :state ~x1 is not a 0-based position" fn (fn-cd-get :state opts))
          nil))
     ((and (assoc-keyword :ok opts) (eq suffix '-carries))
      (mv (msg "~x0: :ok is for an establishing point; a transition that ~
                refuses and leaves the state as it was preserves the ~
                invariant already, so drop :ok" fn)
          nil))
     ((and (assoc-keyword :ok opts) (not (assoc-keyword :witness opts)))
      (mv (msg "~x0 declares :ok but no :witness: name arguments (one term ~
                per formal ~x1) at which the guard holds and the open ~
                answers success, so that its establishment is not vacuous"
               fn (getpropc fn 'formals nil w))
          nil))
     ((and (assoc-keyword :witness opts) (eq suffix '-carries))
      (mv (msg "~x0: :witness is for an establishing point: the arguments at ~
                which it establishes the invariant" fn)
          nil))
     ((and (fn-cd-get :produced opts) (eq suffix '-carries))
      (mv (msg "~x0: :produced is for an establishing point; a transition's ~
                carried state is the one it is handed, so its preservation ~
                takes no premise beyond its guard" fn)
          nil))
     ((and (fn-cd-get :produced opts) (null (fn-cd-get :hyps opts)))
      (mv (msg "~x0 declares :produced but no :hyps: a producer discharges ~
                the declared premises of the argument it produces" fn)
          nil))
     ((and (assoc-keyword :witness opts)
           (not (equal (len (fn-cd-get :witness opts))
                       (len (getpropc fn 'formals nil w)))))
      (mv (msg "~x0's :witness ~x1 is not one term per formal ~x2"
               fn (fn-cd-get :witness opts) (getpropc fn 'formals nil w))
          nil))
     (t (mv-let (bad terms)
          (fn-cd-translate-list (list* result
                                       (if (assoc-keyword :ok opts) (fn-cd-get :ok opts) t)
                                       (fn-cd-get :hyps opts))
                                w)
          (mv-let (badw witness)
            (fn-cd-translate-list (fn-cd-get :witness opts) w)
           (mv-let (badp produced)
            (fn-cd-normal-producers name fn (fn-cd-get :produced opts) w)
            (cond
             ((or bad badw)
              (mv (msg "~x0: ~x1 does not translate in this world" fn
                       (car (or bad badw)))
                  nil))
             (badp
              (mv (msg "~x0: ~x1 does not translate in this world" fn (car badp))
                  nil))
             ((and (assoc-keyword :ok opts) (not (equal (all-vars (cadr terms)) '(_))))
              (mv (msg "~x0's :ok ~x1 is not a term over `_' (the call) alone"
                       fn (fn-cd-get :ok opts))
                  nil))
             (t
              (mv nil (list* fn (cadr entry)
                             :name (packn-pos (list name '- fn suffix) name)
                             :hyps (cddr terms)
                             (append (and (assoc-keyword :ok opts) (list :ok (cadr terms)))
                                     (and (assoc-keyword :witness opts)
                                          (list :witness witness
                                                :reaches (packn-pos (list name '- fn '-reaches)
                                                                    name)))
                                     (and produced (list :produced produced))
                                     (if st nil
                                       (list :state (fn-cd-get :state opts)
                                             :result (car terms)))))))))))))))

(defun fn-cd-parts (st entry w)
  (declare (xargs :mode :program))
  ; (mv MSG S RET HYPS) of a normalized ENTRY (FN ...): FN's carried formal,
  ; the carried state FN returns, and FN's guard then the declared :hyps
  (let* ((fn (car entry))
         (opts (cddr entry))
         (formals (getpropc fn 'formals :none w))
         (call (cons fn formals))
         (hyps (fn-cd-get :hyps opts))
         (guard (getpropc fn 'guard *t* w))
         (all (if (equal guard *t*) hyps (cons guard hyps))))
    (cond
     ((eq formals :none)
      (mv (msg "~x0 is not a function in this world" fn) nil nil nil))
     ((not (subsetp-eq (all-vars1-lst hyps nil) formals))
      (mv (msg "~x0's :hyps ~x1 mention variables that are not its formals ~x2"
               fn hyps formals)
          nil nil nil))
     (st
      ; ONE input slot may hold the carried stobj (or one congruent to it),
      ; and RET is the output slot of that SAME stobj: with two congruent
      ; slots a call may pass the live state in either, and an output
      ; congruent to it may be the other one (r15-F1)
      (let* ((ins (stobjs-in fn w))
             (i (fn-cd-stobj-position st ins w))
             (k (and i (position-eq (nth i ins) (stobjs-out fn w)))))
        (cond ((null i)
               (mv (msg "~x0 takes no ~x1 argument, so it carries no ~x1" fn st)
                   nil nil nil))
              ((fn-cd-stobj-position st (nthcdr (1+ i) ins) w)
               (mv (msg "~x0 takes more than one argument that is ~x1 or ~
                         congruent to it (stobjs-in ~x2), so which one carries ~
                         ~x1 is not determined" fn st ins)
                   nil nil nil))
              ((null k)
               (mv (msg "~x0 does not return the carried stobj ~x1 (its ~
                         stobjs-out are ~x2)" fn st (stobjs-out fn w))
                   nil nil nil))
              (t (mv nil (nth i formals)
                     (if (cdr (stobjs-out fn w)) (list 'mv-nth (kwote k) call) call)
                     all)))))
     (t
      (let ((i (fn-cd-get :state opts))
            (result (fn-cd-get :result opts)))
        (cond ((and i (not (< i (len formals))))
               (mv (msg "~x0 has ~x1 formals; :state ~x2 is none of them"
                        fn (len formals) i)
                   nil nil nil))
              ((not (equal (all-vars result) '(_)))
               (mv (msg "~x0's :result ~x1 is not a term over `_' (the call) ~
                         alone" fn result)
                   nil nil nil))
              (t (mv nil (and i (nth i formals))
                     (fn-cd-subst result (list (cons '_ call)))
                     all))))))))

(defun fn-cd-ok-term (entry w)
  (declare (xargs :mode :program))
  ; the declared :ok of a normalized establishing ENTRY, over its call; nil
  ; when the open cannot refuse
  (let ((ok (fn-cd-get :ok (cddr entry))))
    (and ok
         (fn-cd-subst ok (list (cons '_ (cons (car entry)
                                              (getpropc (car entry) 'formals nil w))))))))

(defun fn-cd-statement (kind r st entry w)
  (declare (xargs :mode :program))
  ; (mv MSG STATEMENT): KIND :carries for a transition, :establishes for an open
  (mv-let (msg s ret hyps)
    (fn-cd-parts st entry w)
    (let ((ok (and (eq kind :establishes) (fn-cd-ok-term entry w))))
      (cond (msg (mv msg nil))
            ((eq kind :carries)
             (mv nil (list 'implies (fn-cd-conj (cons (list r s) hyps)) (list r ret))))
            (t (let ((conclusion (if ok (list 'if ok (list r ret) *t*) (list r ret))))
                 (mv nil (if hyps
                             (list 'implies (fn-cd-conj hyps) conclusion)
                           conclusion))))))))

(defun fn-cd-reaches-statement (st entry w)
  (declare (xargs :mode :program))
  ; (mv MSG STATEMENT) for a normalized establishing ENTRY declaring :ok or
  ; :witness: FN's guard, its :hyps and its :ok (if any), each formal
  ; replaced by its :witness term; (mv nil nil) when ENTRY declares neither
  (let* ((fn (car entry))
         (opts (cddr entry))
         (ok (fn-cd-ok-term entry w))
         (formals (getpropc fn 'formals nil w))
         (witness (fn-cd-get :witness opts)))
    (cond
     ((and (null ok) (not (assoc-keyword :witness opts))) (mv nil nil))
     ((not (and (true-listp witness) (equal (len witness) (len formals))))
      (mv (msg "~x0 declares :ok but its :witness ~x1 is not one term per ~
                formal ~x2: its success is not shown reachable" fn witness formals)
          nil))
     (t (mv-let (msg s ret hyps)
          (fn-cd-parts st entry w)
          (declare (ignore s ret))
          (if msg
              (mv msg nil)
            (mv nil (fn-cd-subst (fn-cd-conj (append hyps (and ok (list ok))))
                                 (pairlis$ formals witness)))))))))

(defun fn-cd-generated-problem (name statement w)
  (declare (xargs :mode :program))
  (let ((formula (getpropc name 'theorem nil w)))
    (and (not (equal formula statement))
         (msg "~x0 is not the generated statement in this world: it is ~x1, ~
               the statement is ~x2" name formula statement))))

;  A NAMED ASSUMPTION is an application of a function an encapsulate
; introduced (constrained) whose name begins FN-ASSUME- (AGENTS.md: "A named
; assumption is an `encapsulate' with a local witness in
; books/assumptions.lisp or a book it includes").
(defun fn-cd-named-assumptionp (a w)
  (declare (xargs :mode :program))
  (and (consp a) (symbolp (car a)) (not (eq (car a) 'quote))
       (getpropc (car a) 'constrainedp nil w)
       (let ((n (symbol-name (car a))))
         (and (< 10 (length n)) (equal (subseq n 0 10) "FN-ASSUME-")))))

(defun fn-cd-first-unnamed-assumption (as w)
  (declare (xargs :mode :program))
  (cond ((atom as) nil)
        ((fn-cd-named-assumptionp (car as) w)
         (fn-cd-first-unnamed-assumption (cdr as) w))
        (t (list (car as)))))

(defun fn-cd-produced-formal (entry)
  (declare (xargs :mode :program))
  ; the one formal a normalized ENTRY's declared :hyps mention, or nil
  (let ((vars (all-vars1-lst (fn-cd-get :hyps (cddr entry)) nil)))
    (and (consp vars) (null (cdr vars)) (car vars))))

(defun fn-cd-produced-statement (entry producer w)
  (declare (xargs :mode :program))
  ; (mv MSG STATEMENT): PRODUCER = (P THM :assuming (A...) ...) of the
  ; establishing ENTRY; the entry's declared :hyps, their one formal F
  ; replaced by P's call over P's formals, under the named assumptions As
  (let* ((fn (car entry))
         (p (car producer))
         (as (fn-cd-get :assuming (cddr producer)))
         (hyps (fn-cd-get :hyps (cddr entry)))
         (f (fn-cd-produced-formal entry))
         (pformals (getpropc p 'formals :none w)))
    (cond
     ((null f)
      (mv (msg "~x0's :hyps ~x1 do not mention exactly one formal: a producer ~
                discharges the premises of the one argument it produces" fn hyps)
          nil))
     ((eq pformals :none)
      (mv (msg "~x0's producer ~x1 is not a function in this world" fn p) nil))
     ((eq p fn)
      (mv (msg "~x0 cannot produce its own argument" fn) nil))
     ((not (subsetp-eq (all-vars1-lst as nil) pformals))
      (mv (msg "~x0's producer ~x1: :assuming ~x2 mention variables that are ~
                not ~x1's formals ~x3" fn p as pformals)
          nil))
     ((fn-cd-first-unnamed-assumption as w)
      (mv (msg "~x0's producer ~x1: ~x2 is not a named assumption (an ~
                application of an encapsulate-constrained FN-ASSUME- function, ~
                books/assumptions*.lisp)"
               fn p (car (fn-cd-first-unnamed-assumption as w)))
          nil))
     (t (let ((conclusion (fn-cd-subst (fn-cd-conj hyps) (list (cons f (cons p pformals))))))
          (mv nil (if as (list 'implies (fn-cd-conj as) conclusion) conclusion)))))))

(defun fn-cd-produced-problem (entry producers generatedp w)
  (declare (xargs :mode :program))
  (if (atom producers)
      nil
    (mv-let (msg statement)
      (fn-cd-produced-statement entry (car producers) w)
      (or msg
          (and generatedp
               (fn-cd-generated-problem (fn-cd-get :name (cddar producers)) statement w))
          (fn-cd-produced-problem entry (cdr producers) generatedp w)))))

(defun fn-cd-pred-conjuncts (pred terms s)
  (declare (xargs :mode :program))
  ; the TERMS applying PRED with S their only variable
  (cond ((atom terms) nil)
        ((and (consp (car terms)) (eq (caar terms) pred)
              (subsetp-eq (all-vars (car terms)) (list s)))
         (cons (car terms) (fn-cd-pred-conjuncts pred (cdr terms) s)))
        (t (fn-cd-pred-conjuncts pred (cdr terms) s))))

(defun fn-cd-bridge-conjuncts (pred r st transitions w)
  (declare (xargs :mode :program))
  ; every guard conjunct of a listed transition applying PRED to its
  ; carried formal alone, renamed to R's formal
  (if (atom transitions)
      nil
    (mv-let (msg s ret hyps)
      (fn-cd-parts st (car transitions) w)
      (declare (ignore ret hyps))
      (union-equal
       (and (null msg)
            (fn-cd-subst-lst
             (fn-cd-pred-conjuncts
              pred (flatten-ands-in-lit (getpropc (caar transitions) 'guard *t* w)) s)
             (list (cons s (car (getpropc r 'formals nil w))))))
       (fn-cd-bridge-conjuncts pred r st (cdr transitions) w)))))

(defun fn-cd-bridge-statement (r st bridge transitions w)
  (declare (xargs :mode :program))
  (let ((cs (fn-cd-bridge-conjuncts (car bridge) r st transitions w)))
    (if cs
        (mv nil (list 'implies (list r (car (getpropc r 'formals nil w)))
                      (fn-cd-conj cs)))
      (mv (msg "bridge ~x0: no listed transition's guard applies ~x0 to its ~
                carried state alone, so ~x1 has nothing to conclude"
               (car bridge) r)
          nil))))

(defun fn-cd-entries-problem (kind r st entries generatedp w)
  (declare (xargs :mode :program))
  (if (atom entries)
      nil
    (mv-let (msg statement)
      (fn-cd-statement kind r st (car entries) w)
      (mv-let (rmsg reaches)
        (if (eq kind :establishes)
            (fn-cd-reaches-statement st (car entries) w)
          (mv nil nil))
        (or msg
            rmsg
            (and generatedp
                 (fn-cd-generated-problem (fn-cd-get :name (cddar entries)) statement w))
            (and generatedp reaches
                 (fn-cd-generated-problem (fn-cd-get :reaches (cddar entries)) reaches w))
            (and (eq kind :establishes)
                 (fn-cd-produced-problem (car entries)
                                         (fn-cd-get :produced (cddar entries))
                                         generatedp w))
            (fn-cd-entries-problem kind r st (cdr entries) generatedp w))))))

(defun fn-cd-bridges-problem (r st bridges transitions generatedp w)
  (declare (xargs :mode :program))
  (if (atom bridges)
      nil
    (mv-let (msg statement)
      (fn-cd-bridge-statement r st (car bridges) transitions w)
      (or msg
          (and generatedp
               (fn-cd-generated-problem (fn-cd-get :name (cddar bridges)) statement w))
          (fn-cd-bridges-problem r st (cdr bridges) transitions generatedp w)))))

; Completeness over the fn-interfaces table: the declared entries that
; return the carried stobj or one congruent to it.
(defun fn-cd-returning-entries (entries st w)
  (declare (xargs :mode :program))
  (cond ((atom entries) nil)
        ((fn-cd-stobj-position st (getpropc (car (car entries)) 'stobjs-out nil w) w)
         (cons (car (car entries)) (fn-cd-returning-entries (cdr entries) st w)))
        (t (fn-cd-returning-entries (cdr entries) st w))))

(defun fn-cd-first-unlisted (names listed)
  (declare (xargs :mode :program))
  (cond ((atom names) nil)
        ((member-eq (car names) listed) (fn-cd-first-unlisted (cdr names) listed))
        (t (car names))))

(defun fn-cd-invariant-problem (r w)
  (declare (xargs :mode :program))
  (let ((formals (getpropc r 'formals :none w)))
    (cond ((eq formals :none) (msg "invariant ~x0 is not a function in this world" r))
          ((not (and (consp formals) (null (cdr formals))))
           (msg "invariant ~x0 takes ~x1 formals; a carried relation is a ~
                 function of one formal, the carried state" r (len formals)))
          (t nil))))

(defun fn-cd-problem (name row generatedp w)
  (declare (xargs :mode :program))
  ; nil, or a msg naming the first check the world refutes for the
  ; normalized ROW; GENERATEDP: every generated name holds its statement
  (let* ((r (fn-cd-get :invariant row))
         (st (fn-cd-state-stobj r w))
         (established (fn-cd-get :established row))
         (transitions (fn-cd-get :transitions row))
         (complete-by (fn-cd-get :complete-by row))
         (unlisted (and st (fn-cd-first-unlisted
                            (fn-cd-returning-entries (table-alist 'fn-interfaces w) st w)
                            (append (strip-cars established) (strip-cars transitions))))))
    (cond
     ((fn-cd-invariant-problem r w))
     ((atom established)
      (msg "~x0 has no establishing point: nothing shows ~x1 holds of any ~
            state (r24-F1)" name r))
     ((fn-cd-entries-problem :establishes r st established generatedp w))
     ((fn-cd-entries-problem :carries r st transitions generatedp w))
     ((fn-cd-bridges-problem r st (fn-cd-get :concludes row) transitions generatedp w))
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

(defun fn-cd-normal-entries (name suffix st entries w)
  (declare (xargs :mode :program))
  (if (atom entries)
      (mv nil nil)
    (mv-let (msg entry)
      (fn-cd-normal-entry name suffix st (car entries) w)
      (if msg
          (mv msg nil)
        (mv-let (msg rest)
          (fn-cd-normal-entries name suffix st (cdr entries) w)
          (mv msg (cons entry rest)))))))

(defun fn-cd-normal-bridges (name bridges)
  (declare (xargs :mode :program))
  (if (atom bridges)
      nil
    (cons (list (caar bridges) (cadar bridges)
                :name (packn-pos (list name '- (caar bridges) '-bridge) name))
          (fn-cd-normal-bridges name (cdr bridges)))))

(defun fn-cd-first-non-theorem (names w)
  (declare (xargs :mode :program))
  (cond ((atom names) nil)
        ((getpropc (car names) 'theorem nil w) (fn-cd-first-non-theorem (cdr names) w))
        (t (car names))))

(defun fn-cd-declare (name kvs w)
  (declare (xargs :mode :program))
  ; (mv MSG ROW): the normalized row of a well-formed declaration
  (let* ((r (fn-cd-get :invariant kvs))
         (st (fn-cd-state-stobj r w))
         (bare (fn-cd-first-bare (fn-cd-get :transitions kvs))))
    (cond
     ((assoc-eq name (table-alist 'fn-carried w))
      (mv (msg "~x0 is already a carried invariant of this world; a row is ~
                declared once" name)
          nil))
     ((fn-cd-invariant-problem r w) (mv (fn-cd-invariant-problem r w) nil))
     (bare
      (mv (msg "transition ~x0 has no preservation theorem.  The obligation, ~
                generated: (implies (and (~x1 s) <~x0's guard>) (~x1 <the ~
                state (~x0 ~&2) returns>)) where s is the carried state among ~
                ~x0's arguments; prove it and name it as (~x0 THM)."
               bare r (getpropc bare 'formals nil w))
          nil))
     ((fn-cd-first-non-theorem (strip-cadrs (fn-cd-get :concludes kvs)) w)
      (mv (msg "a bridge names ~x0, which is not a theorem in this world"
               (fn-cd-first-non-theorem (strip-cadrs (fn-cd-get :concludes kvs)) w))
          nil))
     (t
      (mv-let (msg established)
        (fn-cd-normal-entries name '-establishes st (fn-cd-get :established kvs) w)
        (mv-let (msg2 transitions)
          (fn-cd-normal-entries name '-carries st (fn-cd-get :transitions kvs) w)
          (let ((row (list :invariant r :state st
                           :established established :transitions transitions
                           :concludes (fn-cd-normal-bridges name (fn-cd-get :concludes kvs))
                           :complete-by (fn-cd-get :complete-by kvs)
                           :trace (not (and (assoc-keyword :trace kvs)
                                            (null (fn-cd-get :trace kvs)))))))
            (cond (msg (mv msg nil))
                  (msg2 (mv msg2 nil))
                  (t (mv (fn-cd-problem name row nil w) row))))))))))

; ---------------------------------------------------------------------------
; The events.

(defun fn-cd-names (entries)
  (declare (xargs :mode :program))
  (if (atom entries)
      nil
    (cons (fn-cd-get :name (cddar entries)) (fn-cd-names (cdr entries)))))

(defun fn-cd-produced-defthms (entry producers w)
  (declare (xargs :mode :program))
  ; per producer, the discharged premises at its output, from its THM
  (if (atom producers)
      nil
    (mv-let (msg statement)
      (fn-cd-produced-statement entry (car producers) w)
      (declare (ignore msg))
      (cons `(defthm ,(fn-cd-get :name (cddar producers)) ,statement
               :hints (("Goal" :use ,(cadar producers)
                        :in-theory (theory 'minimal-theory)))
               :rule-classes nil)
            (fn-cd-produced-defthms entry (cdr producers) w)))))

(defun fn-cd-defthms (kind r st entries rule w)
  (declare (xargs :mode :program))
  ; the generated statements, each proved from its declared theorem
  (if (atom entries)
      nil
    (mv-let (msg statement)
      (fn-cd-statement kind r st (car entries) w)
      (declare (ignore msg))
      (mv-let (rmsg reaches)
        (if (eq kind :establishes)
            (fn-cd-reaches-statement st (car entries) w)
          (mv nil nil))
        (declare (ignore rmsg))
        (append
         ; the open's success, reached at its witness: proved in the
         ; current theory (a ground witness evaluates)
         (and reaches
              `((defthm ,(fn-cd-get :reaches (cddar entries)) ,reaches
                  :rule-classes nil)))
         (and (eq kind :establishes)
              (fn-cd-produced-defthms (car entries)
                                      (fn-cd-get :produced (cddar entries)) w))
         (cons `(defthm ,(fn-cd-get :name (cddar entries)) ,statement
                  :hints (("Goal" :use ,(cadar entries)
                           :in-theory (theory 'minimal-theory)))
                  :rule-classes ,rule)
               (fn-cd-defthms kind r st (cdr entries) rule w)))))))

(defun fn-cd-bridge-defthms (r st bridges transitions w)
  (declare (xargs :mode :program))
  (if (atom bridges)
      nil
    (mv-let (msg statement)
      (fn-cd-bridge-statement r st (car bridges) transitions w)
      (declare (ignore msg))
      (cons `(defthm ,(fn-cd-get :name (cddar bridges)) ,statement
               :hints (("Goal" :use ,(cadar bridges)
                        :in-theory (theory 'minimal-theory)))
               :rule-classes nil)
            (fn-cd-bridge-defthms r st (cdr bridges) transitions w)))))

; Preserve the same bounded refutation probe, but give its refusal a
; stable diagnostic that distinguishes the vacuity checks.
(defmacro fn-cd-nonvacuous (message statement hints)
  `(make-event
    (mv-let (erp val state)
      (must-fail (with-prover-step-limit ,*fn-cd-vacuity-steps*
                   (thm ,statement :hints ,hints)))
      (declare (ignore val))
      (if erp
          (er soft 'def-carried ,message)
        (value '(value-triple :nonvacuous))))))

(defun fn-cd-vacuity-events (kind r st entries w)
  (declare (xargs :mode :program))
  ; per entry: its hypotheses are not provably contradictory
  (if (atom entries)
      nil
    (mv-let (msg s ret hyps)
      (fn-cd-parts st (car entries) w)
      (declare (ignore msg ret))
      (let ((hyps (if (eq kind :carries) (cons (list r s) hyps) hyps)))
        ; an :ok open's success is shown reachable by its generated
        ; NAME-FN-reaches theorem (fn-cd-defthms), a world fact
        (append
         (and hyps
              `((local (fn-cd-nonvacuous
                        ,(if (eq kind :carries)
                             "transition hypotheses are provably contradictory"
                           "establishing hypotheses are provably contradictory")
                        (not ,(fn-cd-conj hyps))
                        (("Goal" :in-theory (theory 'minimal-theory)))))))
         (fn-cd-vacuity-events kind r st (cdr entries) w))))))

(defun fn-cd-arg-alist (formals s i)
  (declare (xargs :mode :program))
  ; the carried formal to s, the others to the event's arguments
  (cond ((atom formals) nil)
        ((eq (car formals) s)
         (cons (cons s 's) (fn-cd-arg-alist (cdr formals) s (1+ i))))
        (t (cons (cons (car formals) (list 'nth i '(cdr e)))
                 (fn-cd-arg-alist (cdr formals) s (1+ i))))))

(defun fn-cd-trace-arms (st entries w)
  (declare (xargs :mode :program))
  ; (mv STEP-ARMS OKP-ARMS): per transition, the state it returns and its
  ; guard and :hyps, at the event
  (if (atom entries)
      (mv nil nil)
    (mv-let (msg s ret hyps)
      (fn-cd-parts st (car entries) w)
      (declare (ignore msg))
      (let ((alist (fn-cd-arg-alist (getpropc (caar entries) 'formals nil w) s 0)))
        (mv-let (steps okps)
          (fn-cd-trace-arms st (cdr entries) w)
          (mv (cons (list (caar entries) (fn-cd-subst ret alist)) steps)
              (cons (list (caar entries) (fn-cd-subst (fn-cd-conj hyps) alist)) okps)))))))

(defun fn-cd-trace-events (name r st transitions w)
  (declare (xargs :mode :program))
  (let ((step (packn-pos (list name '-step) name))
        (okp (packn-pos (list name '-okp) name))
        (run (packn-pos (list name '-run) name))
        (run-okp (packn-pos (list name '-run-okp) name)))
    (mv-let (steps okps)
      (fn-cd-trace-arms st transitions w)
      `((defun-nx ,step (s e) (case (car e) ,@steps (otherwise s)))
        (defun-nx ,okp (s e) (case (car e) ,@okps (otherwise t)))
        (defun-nx ,run (s es)
          (declare (xargs :measure (acl2-count es)))
          (if (atom es) s (,run (,step s (car es)) (cdr es))))
        (defun-nx ,run-okp (s es)
          (declare (xargs :measure (acl2-count es)))
          (if (atom es) t (and (,okp s (car es)) (,run-okp (,step s (car es)) (cdr es)))))
        ; one case per event, each closed by its generated NAME-FN-carries
        ; as a rewrite rule (a :use of every arm at once is a 4^n
        ; clausification, measured on 23 transitions)
        (defthm ,(packn-pos (list name '-step-carries) name)
          (implies (and (,r s) (,okp s e)) (,r (,step s e)))
          :hints (("Goal" :in-theory (union-theories
                                      '(,step ,okp eql case-split force
                                        (:executable-counterpart equal)
                                        ,@(fn-cd-names transitions))
                                      (theory 'minimal-theory)))))
        (defthm ,(packn-pos (list name '-run-carries) name)
          (implies (and (,r s) (,run-okp s es)) (,r (,run s es)))
          :hints (("Goal" :by (:functional-instance fn-cd-run-carries
                                                    (fn-cd-inv ,r)
                                                    (fn-cd-okp ,okp)
                                                    (fn-cd-step ,step)
                                                    (fn-cd-run ,run)
                                                    (fn-cd-run-okp ,run-okp)))))
        (in-theory (disable ,@(fn-cd-names transitions)))))))

(defun fn-cd-events (name row w)
  (declare (xargs :mode :program))
  (let* ((r (fn-cd-get :invariant row))
         (st (fn-cd-get :state row))
         (established (fn-cd-get :established row))
         (transitions (fn-cd-get :transitions row))
         (traced (fn-cd-get :trace row)))
    `(progn
       (table fn-carried ',name ',row)
       (local (fn-cd-nonvacuous
               "the carried invariant is provably always true"
               (,r ,(car (getpropc r 'formals nil w)))
               (("Goal" :in-theory (union-theories '(,r) (theory 'minimal-theory))))))
       ,@(fn-cd-vacuity-events :establishes r st established w)
       ,@(fn-cd-vacuity-events :carries r st transitions w)
       ,@(fn-cd-defthms :establishes r st established nil w)
       ,@(fn-cd-defthms :carries r st transitions (if traced :rewrite nil) w)
       ,@(fn-cd-bridge-defthms r st (fn-cd-get :concludes row) transitions w)
       ,@(and traced (fn-cd-trace-events name r st transitions w)))))

(defmacro def-carried (name &rest kvs)
  (let ((reason (fn-cd-refusal name kvs)))
    (if reason
        `(make-event (er soft 'def-carried "~x0: ~@1" ',name
                         ',(fn-cd-refusal-text reason)))
      `(make-event
        (mv-let (problem row)
          (fn-cd-declare ',name ',kvs (w state))
          (if problem
              (er soft 'def-carried "~x0: ~@1" ',name problem)
            (value (fn-cd-events ',name row (w state)))))))))

; Re-run NAME's checks in the world as now loaded, the generated statements
; included: in the image world, where host/interfaces.lisp has declared
; every host-called entry, the completeness check bites.
(defmacro def-carried-check (name)
  `(make-event
    (let* ((row (cdr (assoc-eq ',name (table-alist 'fn-carried (w state)))))
           (problem (if row
                        (fn-cd-problem ',name row t (w state))
                      (msg "no carried invariant ~x0 in this world" ',name))))
      (if problem
          (er soft 'def-carried-check "~x0: ~@1" ',name problem)
        (value '(value-triple ',name))))))

; ---------------------------------------------------------------------------
; D40 (books/definterface.lisp `:raw-with (:carried NAME)').

(defun fn-cd-raw-with (name fn w)
  (declare (xargs :mode :program))
  ; the generated theorems a raw FN rests on: NAME-FN-carries and every
  ; NAME-PRED-bridge; nil unless FN is a transition of the row NAME
  (let* ((row (cdr (assoc-eq name (table-alist 'fn-carried w))))
         (transition (assoc-eq fn (fn-cd-get :transitions row))))
    (and row transition
         (cons (fn-cd-get :name (cddr transition))
               (fn-cd-names (fn-cd-get :concludes row))))))

;  An establishing point with :produced: its declared :hyps are discharged
; at every producer's output (NAME-FN-P-produced, generated, under named
; assumptions only), so they back raw dispatch WHEN the host can hand FN no
; other argument there.  That is a world fact too: FN is not itself a
; host-called entry (fn-interfaces), and every function body in the world
; that calls FN passes, at the produced formal, a literal call of a declared
; producer (fn-cd-unproduced-call).  A let-bound or computed argument is
; refused: the check is syntactic and conservative.
(defun fn-cd-declared-hyps (entries produced-ok)
  (declare (xargs :mode :program))
  ; the first entry with :hyps not discharged by a producer
  (cond ((atom entries) nil)
        ((and (fn-cd-get :hyps (cddar entries))
              (not (and produced-ok (fn-cd-get :produced (cddar entries)))))
         (car entries))
        (t (fn-cd-declared-hyps (cdr entries) produced-ok))))

(mutual-recursion
 (defun fn-cd-unproduced-actual (term fn pos producers)
   (declare (xargs :mode :program))
   ; (ACTUAL) for the first call of FN in TERM whose argument at POS is not a
   ; call of one of PRODUCERS, else nil
   (cond ((or (atom term) (eq (car term) 'quote)) nil)
         ((and (eq (car term) fn)
               (let ((a (nth pos (cdr term))))
                 (not (and (consp a) (member-eq (car a) producers)))))
          (list (nth pos (cdr term))))
         ((consp (car term))
          (or (fn-cd-unproduced-actual (caddr (car term)) fn pos producers)
              (fn-cd-unproduced-actual-lst (cdr term) fn pos producers)))
         (t (fn-cd-unproduced-actual-lst (cdr term) fn pos producers))))
 (defun fn-cd-unproduced-actual-lst (terms fn pos producers)
   (declare (xargs :mode :program))
   (if (atom terms)
       nil
     (or (fn-cd-unproduced-actual (car terms) fn pos producers)
         (fn-cd-unproduced-actual-lst (cdr terms) fn pos producers)))))

(defun fn-cd-unproduced-call (fn pos producers wrld)
  (declare (xargs :mode :program))
  ; (CALLER ACTUAL) for the first function in the world WRLD whose body
  ; calls FN with an unproduced argument at POS, else nil
  (cond ((atom wrld) nil)
        ((and (eq (cadar wrld) 'unnormalized-body)
              (not (eq (cddar wrld) *acl2-property-unbound*))
              (fn-cd-unproduced-actual (cddar wrld) fn pos producers))
         (cons (caar wrld) (fn-cd-unproduced-actual (cddar wrld) fn pos producers)))
        (t (fn-cd-unproduced-call fn pos producers (cdr wrld)))))

(defun fn-cd-produced-host-problem (entries w)
  (declare (xargs :mode :program))
  ; the first establishing entry with :produced the host can hand an
  ; unproduced argument, as a msg
  (cond
   ((atom entries) nil)
   ((null (fn-cd-get :produced (cddar entries)))
    (fn-cd-produced-host-problem (cdr entries) w))
   (t
    (let* ((fn (caar entries))
           (f (fn-cd-produced-formal (car entries)))
           (pos (position-eq f (getpropc fn 'formals nil w)))
           (producers (strip-cars (fn-cd-get :produced (cddar entries))))
           (bad (and pos (fn-cd-unproduced-call fn pos producers w))))
      (cond
       ((assoc-eq fn (table-alist 'fn-interfaces w))
        (msg "~x0 is a host-called entry (fn-interfaces): the host may hand it ~
              any ~x1, so its produced premises back no raw dispatch" fn f))
       ((null pos) (msg "~x0 has no formal ~x1" fn f))
       (bad
        (msg "~x0 calls ~x1 with ~x2 as ~x3, which is not a call of a declared ~
              producer ~&4: the premises ~x5 are not discharged there"
             (car bad) fn (cadr bad) f producers (fn-cd-get :hyps (cddar entries))))
       (t (fn-cd-produced-host-problem (cdr entries) w)))))))

(defun fn-cd-unwitnessed-1 (entries)
  (declare (xargs :mode :program))
  (cond ((atom entries) nil)
        ((null (fn-cd-get :reaches (cddar entries))) (caar entries))
        (t (fn-cd-unwitnessed-1 (cdr entries)))))

(defun fn-cd-raw-problem (name fn w)
  (declare (xargs :mode :program))
  ; nil when the row NAME backs raw dispatch of FN in this world; else a msg
  (let* ((row (cdr (assoc-eq name (table-alist 'fn-carried w))))
         (hyps (or (fn-cd-declared-hyps (fn-cd-get :established row) t)
                   (fn-cd-declared-hyps (fn-cd-get :transitions row) nil))))
    (cond
     ((null row) (msg "no carried invariant ~x0 in this world" name))
     ((null (assoc-eq fn (fn-cd-get :transitions row)))
      (msg "~x0 is not a transition of ~x1: only a listed transition's ~
            generated preservation backs raw dispatch" fn name))
     ((null (fn-cd-state-stobj (fn-cd-get :invariant row) w))
      (msg "value-state carried rows are enumerated, not world-derived, and ~
            cannot back raw dispatch"))
     ((fn-cd-problem name row t w)
      (msg "the carried invariant's row no longer checks in this world: ~@0"
           (fn-cd-problem name row t w)))
     (hyps
      (msg "~x0 declares :hyps ~x1 at ~x2 beyond its guard: the host does not ~
            check them, so the carried premise is a claim and backs no raw ~
            dispatch" name (fn-cd-get :hyps (cddr hyps)) (car hyps)))
     ((fn-cd-unwitnessed-1 (fn-cd-get :established row))
      (msg "~x0 establishes ~x1 at no witnessed argument (~x2 declares no ~
            :witness): only a row whose every establishing point is shown ~
            reachable (its generated NAME-FN-reaches) backs raw dispatch, so ~
            that the invariant the transitions assume holds of some state"
           name (fn-cd-get :invariant row) (fn-cd-unwitnessed-1 (fn-cd-get :established row))))
     ((fn-cd-produced-host-problem (fn-cd-get :established row) w))
     (t nil))))

(defun fn-cd-uncovered-conjunct (name fn conjuncts w)
  (declare (xargs :mode :program))
  ; the first of FN's guard CONJUNCTS that is neither (R s) of FN's carried
  ; formal s nor a conjunct of a generated bridge of the row NAME; called
  ; after fn-cd-raw-problem is nil
  (let* ((row (cdr (assoc-eq name (table-alist 'fn-carried w))))
         (r (fn-cd-get :invariant row))
         (st (fn-cd-state-stobj r w))
         (transitions (fn-cd-get :transitions row))
         (s (mv-let (msg s ret hyps)
              (fn-cd-parts st (assoc-eq fn transitions) w)
              (declare (ignore msg ret hyps))
              s))
         (c (car conjuncts)))
    (cond
     ((atom conjuncts) nil)
     ((or (equal c (list r s))
          (and (consp c)
               (assoc-eq (car c) (fn-cd-get :concludes row))
               (member-equal (fn-cd-subst c (list (cons s (car (getpropc r 'formals nil w)))))
                             (fn-cd-bridge-conjuncts (car c) r st transitions w))))
      (fn-cd-uncovered-conjunct name fn (cdr conjuncts) w))
     (t c))))

(in-theory (disable fn-cd-run fn-cd-run-okp))
