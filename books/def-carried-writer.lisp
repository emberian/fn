; fn: `def-carried-writer' --- a host-called writer's obligations for a
; carried invariant, from one declaration (lane def-entry, 2026-10-03: the
; first piece of def-entry, the per-entry generator whose declaration is the
; source of truth for the interface row, the carried-invariant obligations,
; the cost bound and the crash points; build/coordinator/lanedumps/def-entry.md).
; This book is the obligation half for STATE WRITERS: what stage 5 wrote by
; hand ten times in host/owner-retain-host.lisp (229 lines for ten writers,
; each the same proof with a different keystone), and what STAGE-5B measured
; (lanedumps/stage-5.md): the expensive part is GUARD VERIFICATION in the
; default theory (fn-owner-take 192 s / 21.9M steps and failed; a goal that
; closes in 706 steps under minimal-theory and eight named rules).
;
; A PROFILE names, once, what every writer of one carried invariant shares.
; The CARRIER is the stobj the invariant reads (`state' included: the legacy
; instance, where the carried value lives in state globals); the INSTALLERS
; are the functions that write the carried value, each with a frame lemma;
; nothing else may write it.
;
;   (def-carried-profile NAME
;     :invariant R                 ; the carried relation, one formal, a stobj
;     :installers (FN ...)         ; the carrier's writers of the carried value
;     [:carried-globals (KEY ...)] ; legacy carrier `state': the globals R reads
;     :at ((VAR TERM) ...)         ; a model keystone is instantiated with VAR := TERM
;                                  ; (over R's formal; renamed to the writer's)
;     :bridge THM                  ; (implies (R s) <the model invariant at :at>)
;     :frame (THM ...)             ; writes beside the carried value keep R; an
;                                  ; installer of a value the model invariant holds of
;                                  ; keeps R (rewrite rules; the row is the frame set)
;     [:theory (RUNE ...)]         ; fixed runes beside minimal-theory for the proofs
;     [:guard-theory (RUNE ...)]   ; fixed runes beside minimal-theory for verify-guards
;     [:step (STEP EVENT-FORMAL)]  ; the event-dispatching transition writers go through
;     [:row PILOT]                 ; the def-carried row whose bridges (:concludes) a
;                                  ; writer's guard conjuncts are checked against
;     [:suffix SYM])               ; theorem names FN-preserves-SYM (default R)
;
; A WRITER is a declaration against a profile:
;
;   (def-carried-writer FN
;     :profile NAME
;     [:opens (G ...)]             ; callees the proofs unfold (installers never are)
;     [:via (THM | (THM (VAR TERM) ...) ...)]   ; model keystones, each :use'd at the
;                                  ; profile's :at bindings THM mentions, plus its own
;     [:lemmas (THM ...)]          ; theorems enabled as rules (a callee's own writer
;                                  ; theorem, a conditional install lemma)
;     [:step (EVENT-TERM THM) | (STEP EVENT-TERM THM)]
;                                  ; FN goes through the profile's STEP (or the named
;                                  ; one, whose event formal is its one non-stobj
;                                  ; formal) at EVENT-TERM, (list :KIND ...) over FN's
;                                  ; formals: STEP-KIND-preserves-SYM is generated
;                                  ; first, from THM, or reused when it is already a
;                                  ; theorem with that very statement
;     [:bridges ((PRED THM) ...)]  ; bridges FN's guard adds to the row: THM proves
;                                  ; (implies (R x) <PRED's conjunct at x>)
;     [:hyps (H ...)]              ; hypotheses beside (R s), each a conjunct of FN's
;                                  ; guard (a two-stobj premise, an io-safety conjunct);
;                                  ; one the guard does not state is refused
;     [:name THM]                  ; the theorem's name (default FN-preserves-SYM)
;     [:guard-theory (RUNE ...)] [:guard-hints H] [:hints H])   ; H replaces; the row says so
;
; CHECKED AT EXPANSION, from the world, before any proof (each refused by name):
;
;   * FN is a function, :logic mode (a :program function has no theorem),
;     takes the carrier once and returns it (fn-cd-parts' words); the formal
;     s and the returned state RET are the world's (stobjs-in, stobjs-out),
;     never declared, so the declarations survive a carrier move unchanged.
;   * THE GUARD, definterface's two rules that otherwise bite at `:raw-with',
;     long after the proof (books/definterface.lisp fn-di-raw-with-problem):
;     every conjunct of FN's guard is a kind check (the host entry guard
;     evaluates it), a stobj formal's own recognizer, headed by a boot-strap
;     primitive (boundp-global fails loud in raw Lisp), (R s) itself, or a
;     conjunct over s alone whose head has a bridge -- in the profile's :row
;     (its :concludes) or in this writer's :bridges.  A conjunct over an
;     argument the host passes per call is refused: no preservation theorem
;     can establish it, so it belongs in the body as a refusal.  A conjunct
;     over other stobjs alone (a two-stobj premise) is not refused but
;     RECORDED (:uncovered): the writer's preservation is proved under it,
;     and the entry stays on the counterpart path (def-carried's
;     fn-cd-uncovered-conjunct refuses raw dispatch of it) until a
;     multi-stobj row can state it.
;   * THE WRITES, a DIAGNOSIS that runs before the proof (the admitted theorem
;     is the claim; this scan only refuses earlier, by name, what the proof
;     could not close): in the translated bodies of FN and its :opens, every
;     call of a function that returns the carrier is one of: an :opens callee
;     (scanned itself, so a hidden writer is a callee of some scanned body);
;     an installer, whose non-stobj arguments are COVERED -- their head
;     (through if, mv-nth, car/cdr and let-bound variables) is a function some
;     :via, :lemmas, :frame or step theorem mentions; a function such a
;     theorem mentions; else refused, naming the call.  put-global of a
;     carried global outside an installer is refused by key.  No lemma could
;     carry R across an uncovered write, so the proof could only fail (the
;     30-minute guard-proof hang of stage 5, f-put-global unfolded, was this
;     class).  The put-global keys the scan sees are recorded (:put-keys);
;     they are what the proof opens, NOT the entry's effect closure, which is
;     def-entry's (c) over every reachable definition and no business of a
;     proof hint (consultation c06, section 4).
;
; EMITTED, in order, each an ordinary event:
;
;   (verify-guards FN :hints minimal-theory + FN + :opens + the profile's and
;      the writer's :guard-theory)         ; when FN is :ideal (its defun said
;                                          ; :verify-guards nil); :guard-hints replaces
;   STEP-KIND-preserves-SYM   (implies (R s) (R (STEP EVENT-TERM ...)))   ; with :step
;   FN-preserves-SYM          (implies (and (R s) H...) (R RET))
;      ; THE STRONGER STATEMENT, the hand theorems' (the guard is not a
;      ; hypothesis; the Hs are only the guard conjuncts a writer declares it
;      ; needs).  def-carried's row then GENERATES its own
;      ; (implies (and (R s) G) (R RET)) -- NAME-FN-carries -- and proves it
;      ; from this one by :use, as the pilot row does from the hand theorems:
;      ; the row theorem is derived from the stronger one, never the stronger
;      ; one renamed to the weaker (c06, section 7).  Proved in
;      ; (union-theories '(FN :opens :lemmas the-step-lemma :frame :theory)
;      ; (theory 'minimal-theory)) with :use of every :via instance and the bridge.
;   (table fn-carried-writers FN ROW)      ; :profile :theorem :via :opens :lemmas :step
;                                          ; :bridges :hyps :put-keys :uncovered :hand-hints
;   (table fn-teeth-owed THM (:by def-carried-writer))   ; the teeth generator's row
;                                          ; (lanedumps/generators-2.md defteeth-check)
;
; The declared theorems are hints; nothing reads their statements.
;
; THE ROW.  (def-carried-writers-row NAME :profile P :from PILOT [:trace T])
; writes the def-carried row for the profile's writers: the invariant, the
; establishing points (with their :ok, :witness, :hyps and :produced) and
; the bridges are READ from PILOT's fn-carried row (declared once, in a
; certified book); the transitions are PILOT's plus every fn-carried-writers
; row of profile P as (FN THM); the bridges PILOT's plus the writers'
; :bridges (one theorem per PRED; two writers naming different theorems for
; one PRED is refused).  def-carried then generates and proves its own
; statements from these as hints and runs its completeness check over
; fn-interfaces, which decides whether the row backs raw dispatch (D40).
; (def-carried-writers-owed P :from PILOT) prints, without refusing, the
; host-called entries that return the carrier and are neither PILOT's nor a
; declared writer's: the first is what the row would refuse on.
;
; Not here: the fn-interfaces row, the cost bound, the crash points and the
; teeth bodies (def-entry's (a), (d)-(g)); an establishing producer such as
; fn-owner-recover-from-store-open is def-carried's :established entry, which
; the row reads from PILOT.  This book includes definterface (hence
; def-carried) and leaves no rule: its helpers are :program mode.

(in-package "ACL2")
(include-book "definterface")

(defconst *fn-cw-profile-keys*
  '(:invariant :installers :carried-globals :at :bridge :frame :theory :guard-theory
    :step :row :suffix))

(defconst *fn-cw-keys*
  '(:profile :opens :via :lemmas :step :bridges :hyps :name :guard-theory :guard-hints
    :hints))

(defun fn-cw-get (key kvs)
  (declare (xargs :mode :program))
  (cadr (assoc-keyword key kvs)))

; ---------------------------------------------------------------------------
; The profile.

(defun fn-cw-bindingsp (x)
  (declare (xargs :mode :program))
  ; ((VAR TERM) ...)
  (if (atom x)
      (null x)
    (and (true-listp (car x)) (equal (len (car x)) 2)
         (symbolp (caar x)) (caar x)
         (fn-cw-bindingsp (cdr x)))))

(defun fn-cw-first-non-theorem (names w)
  (declare (xargs :mode :program))
  (cond ((atom names) nil)
        ((and (symbolp (car names)) (getpropc (car names) 'theorem nil w))
         (fn-cw-first-non-theorem (cdr names) w))
        (t (list (car names)))))

(defun fn-cw-first-non-function (names w)
  (declare (xargs :mode :program))
  (cond ((atom names) nil)
        ((and (symbolp (car names)) (not (eq (getpropc (car names) 'formals :none w) :none)))
         (fn-cw-first-non-function (cdr names) w))
        (t (list (car names)))))

(defun fn-cw-first-non-rune (runes w)
  (declare (xargs :mode :program))
  ; a :theory entry: a symbol with a theorem or a definition, or an explicit rune
  (cond ((atom runes) nil)
        ((and (symbolp (car runes))
              (or (getpropc (car runes) 'theorem nil w)
                  (not (eq (getpropc (car runes) 'formals :none w) :none))))
         (fn-cw-first-non-rune (cdr runes) w))
        ((and (consp (car runes)) (keywordp (caar runes)))
         (fn-cw-first-non-rune (cdr runes) w))
        (t (list (car runes)))))

(defun fn-cw-first-non-returning (fns st w)
  (declare (xargs :mode :program))
  ; the first of FNS that is not a function returning the stobj ST
  (cond ((atom fns) nil)
        ((and (symbolp (car fns))
              (not (eq (getpropc (car fns) 'formals :none w) :none))
              (fn-cd-stobj-position st (stobjs-out (car fns) w) w))
         (fn-cw-first-non-returning (cdr fns) st w))
        (t (list (car fns)))))

(defun fn-cw-profile-problem (name kvs w)
  (declare (xargs :mode :program))
  ; nil, or a msg naming the first check the form or the world refutes
  (let* ((r (fn-cw-get :invariant kvs))
         (st (and r (symbolp r) (fn-cd-state-stobj r w)))
         (formal (and r (symbolp r) (car (getpropc r 'formals nil w))))
         (step (fn-cw-get :step kvs)))
    (cond
     ((not (and (symbolp name) name)) (msg "~x0 is not a profile name" name))
     ((not (keyword-value-listp kvs)) (msg "~x0: options are not a keyword list" name))
     ((fn-cd-unknown-keys kvs *fn-cw-profile-keys*)
      (msg "~x0: unknown keyword(s) ~&1; the keywords are ~&2"
           name (fn-cd-unknown-keys kvs *fn-cw-profile-keys*) *fn-cw-profile-keys*))
     ((assoc-eq name (table-alist 'fn-carried-profiles w))
      (msg "~x0 is already a profile of this world; a profile is declared once" name))
     ((fn-cd-invariant-problem r w))
     ((null st)
      (msg "~x0: the invariant ~x1 takes a value, not a stobj: a writer profile ~
            carries a stobj (`state' included), whose place in each writer's ~
            arguments and result the world gives" name r))
     ((not (and (consp (fn-cw-get :installers kvs)) (symbol-listp (fn-cw-get :installers kvs))))
      (msg "~x0 has no :installers: name the functions that write the carried value ~
            of ~x1 (each with a frame lemma); nothing else may write it" name st))
     ((fn-cw-first-non-returning (fn-cw-get :installers kvs) st w)
      (msg "~x0: installer ~x1 is not a function returning ~x2"
           name (car (fn-cw-first-non-returning (fn-cw-get :installers kvs) st w)) st))
     ((not (symbol-listp (fn-cw-get :carried-globals kvs)))
      (msg "~x0: :carried-globals ~x1 is not a list of symbols"
           name (fn-cw-get :carried-globals kvs)))
     ((and (fn-cw-get :carried-globals kvs) (not (eq st 'state)))
      (msg "~x0: :carried-globals is for the legacy carrier `state'; the carrier ~
            here is ~x1" name st))
     ((not (fn-cw-bindingsp (fn-cw-get :at kvs)))
      (msg "~x0: :at ~x1 is not ((VAR TERM) ...)" name (fn-cw-get :at kvs)))
     ((not (and (symbolp (fn-cw-get :bridge kvs)) (fn-cw-get :bridge kvs)))
      (msg "~x0 has no :bridge: name the theorem (implies (~x1 ~x2) <the model ~
            invariant at :at>) every writer proof uses" name r formal))
     ((fn-cw-first-non-theorem (cons (fn-cw-get :bridge kvs) (fn-cw-get :frame kvs)) w)
      (msg "~x0: ~x1 is not a theorem in this world"
           name (car (fn-cw-first-non-theorem
                      (cons (fn-cw-get :bridge kvs) (fn-cw-get :frame kvs)) w))))
     ((fn-cw-first-non-rune (append (fn-cw-get :theory kvs) (fn-cw-get :guard-theory kvs)) w)
      (msg "~x0: ~x1 is neither a rule nor a function nor a rune"
           name (car (fn-cw-first-non-rune
                      (append (fn-cw-get :theory kvs) (fn-cw-get :guard-theory kvs)) w))))
     ((and step (not (and (true-listp step) (equal (len step) 2)
                          (symbolp (car step)) (symbolp (cadr step)))))
      (msg "~x0: :step ~x1 is not (STEP EVENT-FORMAL)" name step))
     ((and step (fn-cw-first-non-returning (list (car step)) st w))
      (msg "~x0: :step names ~x1, which is not a function returning ~x2 in this world"
           name (car step) st))
     ((and step (not (member-eq (cadr step) (getpropc (car step) 'formals nil w))))
      (msg "~x0: :step's event formal ~x1 is not a formal of ~x2 ~x3"
           name (cadr step) (car step) (getpropc (car step) 'formals nil w)))
     ((and (fn-cw-get :row kvs)
           (not (assoc-eq (fn-cw-get :row kvs) (table-alist 'fn-carried w))))
      (msg "~x0: :row ~x1 is not a carried invariant of this world" name (fn-cw-get :row kvs)))
     ((and (fn-cw-get :row kvs)
           (not (eq (fn-cd-get :invariant
                               (cdr (assoc-eq (fn-cw-get :row kvs) (table-alist 'fn-carried w))))
                    r)))
      (msg "~x0: :row ~x1 carries ~x2, not ~x3" name (fn-cw-get :row kvs)
           (fn-cd-get :invariant (cdr (assoc-eq (fn-cw-get :row kvs) (table-alist 'fn-carried w))))
           r))
     ((and (assoc-keyword :suffix kvs)
           (not (and (symbolp (fn-cw-get :suffix kvs)) (fn-cw-get :suffix kvs))))
      (msg "~x0: :suffix ~x1 is not a symbol" name (fn-cw-get :suffix kvs)))
     (t (mv-let (bad terms)
          (fn-cd-translate-list (strip-cadrs (fn-cw-get :at kvs)) w)
          (cond (bad (msg "~x0: :at term ~x1 does not translate in this world" name (car bad)))
                ((not (subsetp-eq (all-vars1-lst terms nil) (list formal)))
                 (msg "~x0: an :at term mentions a variable other than ~x1, the ~
                       invariant's formal" name formal))
                (t nil)))))))

(defun fn-cw-profile-row (kvs w)
  (declare (xargs :mode :program))
  (let ((r (fn-cw-get :invariant kvs)))
    (list :invariant r
          :state (fn-cd-state-stobj r w)
          :formal (car (getpropc r 'formals nil w))
          :installers (fn-cw-get :installers kvs)
          :carried-globals (fn-cw-get :carried-globals kvs)
          :at (fn-cw-get :at kvs)
          :bridge (fn-cw-get :bridge kvs)
          :frame (fn-cw-get :frame kvs)
          :theory (fn-cw-get :theory kvs)
          :guard-theory (fn-cw-get :guard-theory kvs)
          :step (fn-cw-get :step kvs)
          :row (fn-cw-get :row kvs)
          :suffix (if (assoc-keyword :suffix kvs) (fn-cw-get :suffix kvs) r))))

(defmacro def-carried-profile (name &rest kvs)
  `(make-event
    (let ((problem (fn-cw-profile-problem ',name ',kvs (w state))))
      (if problem
          (er soft 'def-carried-profile "~x0: ~@1" ',name problem)
        (value `(table fn-carried-profiles ',',name
                       ',(fn-cw-profile-row ',kvs (w state))))))))

; ---------------------------------------------------------------------------
; The guard: definterface's rules, at expansion.

(defun fn-cw-bridge-heads (profile bridges w)
  (declare (xargs :mode :program))
  ; the PREDs with a bridge: the profile's :row :concludes and the writer's :bridges
  (let ((row (cdr (assoc-eq (fn-cd-get :row profile) (table-alist 'fn-carried w)))))
    (append (strip-cars (fn-cd-get :concludes row)) (strip-cars bridges))))

(defun fn-cw-conjunct-class (c fn s r profile bridges w)
  (declare (xargs :mode :program))
  ; :skipped (a kind check, a stobj recognizer, a primitive head, (R s), a
  ; bridged conjunct over s alone), :uncovered (over other stobjs alone), or
  ; (:argument . VAR) / (:unbridged . HEAD) for a refusal
  (let* ((formals (getpropc fn 'formals nil w))
         (stobjs (getpropc fn 'stobjs-in nil w))
         (head (fn-di-conjunct-head c))
         (vars (all-vars c)))
    (cond
     ((fn-di-kind-checks (list c) formals stobjs (fn-di-guard-kinds w)) :skipped)
     ((fn-di-stobj-recognizer-conjunctp c formals stobjs w) :skipped)
     ; a conjunct over a host-passed argument is refused whatever its head:
     ; (< n 100) is as unprovable by preservation as (fn-okp n) (liaison r72
     ; on c1d69fb6a); only a conjunct over stobjs alone may be skipped for
     ; a fail-loud primitive head
     ((fn-di-non-stobj-vars vars formals stobjs)
      (cons :argument (car (fn-di-non-stobj-vars vars formals stobjs))))
     ((or (null head) (member-eq head *fn-di-fail-loud-primitives*)) :skipped)
     ((equal c (list r s)) :skipped)
     ((not (member-eq s vars)) :uncovered)
     ((and (equal vars (list s)) (member-eq head (fn-cw-bridge-heads profile bridges w)))
      :skipped)
     ((equal vars (list s)) (cons :unbridged head))
     (t :uncovered))))

(defun fn-cw-guard-classes (conjuncts fn s r profile bridges w)
  (declare (xargs :mode :program))
  ; (mv REFUSAL UNCOVERED): the first refusing conjunct as (CLASS CONJUNCT), and
  ; the recorded ones
  (if (atom conjuncts)
      (mv nil nil)
    (let ((class (fn-cw-conjunct-class (car conjuncts) fn s r profile bridges w)))
      (if (consp class)
          (mv (list class (car conjuncts)) nil)
        (mv-let (refusal uncovered)
          (fn-cw-guard-classes (cdr conjuncts) fn s r profile bridges w)
          (mv refusal (if (eq class :uncovered) (cons (car conjuncts) uncovered) uncovered)))))))

; ---------------------------------------------------------------------------
; The writes: every call returning the carrier, in the opened bodies.

(defun fn-cw-theorem-fnnames (thms w)
  (declare (xargs :mode :program))
  (if (atom thms)
      nil
    (union-eq (all-fnnames (getpropc (car thms) 'theorem nil w))
              (fn-cw-theorem-fnnames (cdr thms) w))))

(defun fn-cw-via-name (via)
  (declare (xargs :mode :program))
  (if (consp via) (car via) via))

(defun fn-cw-via-names (vias)
  (declare (xargs :mode :program))
  (if (atom vias) nil (cons (fn-cw-via-name (car vias)) (fn-cw-via-names (cdr vias)))))

(defun fn-cw-head-covered (term env covered)
  (declare (xargs :mode :program))
  ; nil when TERM's value is produced by a covered function (through if,
  ; mv-nth and ENV, the let-bound variables), else (TERM): the uncovered one
  (cond ((atom term)
         (let ((b (assoc-eq term env)))
           (if b (fn-cw-head-covered (cdr b) env covered) (list term))))
        ((eq (car term) 'quote) nil)
        ((eq (car term) 'if)
         (or (fn-cw-head-covered (caddr term) env covered)
             (fn-cw-head-covered (cadddr term) env covered)))
        ((eq (car term) 'mv-nth) (fn-cw-head-covered (caddr term) env covered))
        ((member-eq (car term) '(car cdr))
         ; a projection of a model call's pair (the owner's (cdr (fn-ocfg-fault ...)))
         (fn-cw-head-covered (cadr term) env covered))
        ((consp (car term)) (fn-cw-head-covered (car (last (car term))) env covered))
        ((member-eq (car term) covered) nil)
        (t (list term))))

(defun fn-cw-non-stobj-args (args stobjs)
  (declare (xargs :mode :program))
  (cond ((atom args) nil)
        ((car stobjs) (fn-cw-non-stobj-args (cdr args) (cdr stobjs)))
        (t (cons (car args) (fn-cw-non-stobj-args (cdr args) (cdr stobjs))))))

(defun fn-cw-first-uncovered-arg (args env covered)
  (declare (xargs :mode :program))
  (cond ((atom args) nil)
        ((fn-cw-head-covered (car args) env covered))
        (t (fn-cw-first-uncovered-arg (cdr args) env covered))))

(mutual-recursion
 (defun fn-cw-write-problem (term env fn st opens installers globals covered w)
   (declare (xargs :mode :program))
   ; nil, or a msg: the first call in the translated TERM that writes the
   ; carrier ST without a lemma to carry R across it
   (cond
    ((or (atom term) (eq (car term) 'quote)) nil)
    ((consp (car term))
     ; a lambda: its actuals, then its body with the formals bound to them
     (or (fn-cw-write-problem-lst (cdr term) env fn st opens installers globals covered w)
         (fn-cw-write-problem (car (last (car term)))
                              (append (pairlis$ (cadr (car term)) (cdr term)) env)
                              fn st opens installers globals covered w)))
    ((member-eq (car term) '(if return-last hide))
     ; the translation's control forms carry no stobjs-out of their own
     (fn-cw-write-problem-lst (cdr term) env fn st opens installers globals covered w))
    ((eq (car term) 'put-global)
     (let ((key (if (quotep (cadr term)) (unquote (cadr term)) :computed)))
       (if (member-eq key globals)
           (msg "~x0 writes the carried global ~x1 directly (put-global, in its body ~
                 or an :opens callee), not through an installer ~&2: no frame lemma ~
                 carries the invariant across that write" fn key installers)
         (fn-cw-write-problem-lst (cdr term) env fn st opens installers globals covered w))))
    ((and (fn-cd-stobj-position st (stobjs-out (car term) w) w)
          (not (member-eq (car term) opens)))
     (cond
      ((member-eq (car term) installers)
       (let ((bad (fn-cw-first-uncovered-arg
                   (fn-cw-non-stobj-args (cdr term) (stobjs-in (car term) w))
                   env covered)))
         (if bad
             (msg "~x0 installs ~x1 through ~x2, and no :via, :lemmas, :frame or step ~
                   theorem mentions the function that produces it: nothing shows ~
                   the installed value keeps the invariant" fn (car bad) (car term))
           (fn-cw-write-problem-lst (cdr term) env fn st opens installers globals covered w))))
      ((member-eq (car term) covered)
       (fn-cw-write-problem-lst (cdr term) env fn st opens installers globals covered w))
      (t (msg "~x0 calls ~x1, which returns the carrier ~x2 and is neither opened ~
               (:opens), an installer of the profile, nor the subject of a :via, ~
               :lemmas, :frame or step theorem: nothing carries the invariant ~
               across it" fn (car term) st))))
    (t (fn-cw-write-problem-lst (cdr term) env fn st opens installers globals covered w))))
 (defun fn-cw-write-problem-lst (terms env fn st opens installers globals covered w)
   (declare (xargs :mode :program))
   (if (atom terms)
       nil
     (or (fn-cw-write-problem (car terms) env fn st opens installers globals covered w)
         (fn-cw-write-problem-lst (cdr terms) env fn st opens installers globals covered w)))))

(defun fn-cw-writes-problem (fns fn st opens installers globals covered w)
  (declare (xargs :mode :program))
  (if (atom fns)
      nil
    (or (fn-cw-write-problem (getpropc (car fns) 'unnormalized-body nil w) nil
                             fn st opens installers globals covered w)
        (fn-cw-writes-problem (cdr fns) fn st opens installers globals covered w))))

(mutual-recursion
 (defun fn-cw-put-keys (term)
   (declare (xargs :mode :program))
   ; the quoted keys of every (put-global 'KEY v s) in the translated TERM
   (cond ((or (atom term) (eq (car term) 'quote)) nil)
         ((consp (car term))
          (append (fn-cw-put-keys (car (last (car term)))) (fn-cw-put-keys-lst (cdr term))))
         ((eq (car term) 'put-global)
          (cons (if (quotep (cadr term)) (unquote (cadr term)) :computed)
                (fn-cw-put-keys-lst (cddr term))))
         (t (fn-cw-put-keys-lst (cdr term)))))
 (defun fn-cw-put-keys-lst (terms)
   (declare (xargs :mode :program))
   (if (atom terms)
       nil
     (append (fn-cw-put-keys (car terms)) (fn-cw-put-keys-lst (cdr terms))))))

(defun fn-cw-written-keys (fns w)
  (declare (xargs :mode :program))
  (if (atom fns)
      nil
    (union-eq (fn-cw-put-keys (getpropc (car fns) 'unnormalized-body nil w))
              (fn-cw-written-keys (cdr fns) w))))

; ---------------------------------------------------------------------------
; The writer: checks, then the events.

(defun fn-cw-viasp (x)
  (declare (xargs :mode :program))
  ; (THM | (THM (VAR TERM) ...) ...)
  (if (atom x)
      (null x)
    (and (or (and (symbolp (car x)) (car x))
             (and (consp (car x)) (symbolp (caar x)) (caar x)
                  (fn-cw-bindingsp (cdar x))))
         (fn-cw-viasp (cdr x)))))

(defun fn-cw-conj (terms)
  (declare (xargs :mode :program))
  (cond ((atom terms) t)
        ((atom (cdr terms)) (car terms))
        (t (cons 'and terms))))

(defun fn-cw-label-hyps (hyps i fn)
  (declare (xargs :mode :program))
  ; ((h1 H1) (h2 H2) ...)
  (if (atom hyps)
      nil
    (cons (list (packn-pos (list 'h i) fn) (car hyps))
          (fn-cw-label-hyps (cdr hyps) (1+ i) fn))))

(defun fn-cw-untranslate-ret (ret)
  (declare (xargs :mode :program))
  ; fn-cd-parts' returned-state term, its quoted mv-nth index unquoted
  (if (and (consp ret) (eq (car ret) 'mv-nth) (quotep (cadr ret)))
      (list 'mv-nth (unquote (cadr ret)) (caddr ret))
    ret))

(defun fn-cw-first-non-conjunct (hyps conjuncts)
  (declare (xargs :mode :program))
  ; the first of HYPS (translated) that is not among the guard's CONJUNCTS
  (cond ((atom hyps) nil)
        ((member-equal (car hyps) conjuncts) (fn-cw-first-non-conjunct (cdr hyps) conjuncts))
        (t (list (car hyps)))))

(defun fn-cw-step-kind (event)
  (declare (xargs :mode :program))
  ; :KIND of an EVENT term (list :KIND ...), else nil
  (and (consp event) (eq (car event) 'list) (consp (cdr event))
       (keywordp (cadr event)) (cadr event)))

(defun fn-cw-step-name (pstep profile event fn)
  (declare (xargs :mode :program))
  (packn-pos (list pstep '- (symbol-name (fn-cw-step-kind event))
                   '-preserves- (fn-cd-get :suffix profile))
             fn))

(defun fn-cw-step-statement (pstep evf event profile w)
  (declare (xargs :mode :program))
  ; (implies (R s) (R (STEP ... EVENT ...))), untranslated
  (let ((r (fn-cd-get :invariant profile))
        (st (fn-cd-get :state profile)))
    (mv-let (msg s ret all)
      (fn-cd-parts st (list pstep 'none) w)
      (declare (ignore msg all))
      (list 'implies (list r s)
            (list r (fn-cw-untranslate-ret (fn-cd-subst ret (list (cons evf event)))))))))

(defun fn-cw-step-reusable (name statement w)
  (declare (xargs :mode :program))
  ; :absent, :reusable (a theorem whose formula is STATEMENT translated), or
  ; :other (a theorem with another formula)
  (let ((formula (getpropc name 'theorem nil w)))
    (cond ((null formula) :absent)
          (t (mv-let (bad terms)
               (fn-cd-translate-list (list statement) w)
               (if (and (null bad) (equal (car terms) formula)) :reusable :other))))))

(defun fn-cw-theorem-name (fn kvs profile)
  (declare (xargs :mode :program))
  (if (assoc-keyword :name kvs)
      (fn-cw-get :name kvs)
    (packn-pos (list fn '-preserves- (fn-cd-get :suffix profile)) fn)))

(defun fn-cw-covered (kvs profile w)
  (declare (xargs :mode :program))
  ; the functions some :via, :lemmas, :frame or step theorem mentions
  (union-eq (and (fn-cw-get :step kvs)
                 (list (if (equal (len (fn-cw-get :step kvs)) 3)
                           (car (fn-cw-get :step kvs))
                         (car (fn-cd-get :step profile)))))
            (fn-cw-theorem-fnnames (append (fn-cw-via-names (fn-cw-get :via kvs))
                                           (fn-cw-get :lemmas kvs)
                                           (fn-cd-get :frame profile))
                                   w)))

(defun fn-cw-non-stobj-formals (formals stobjs)
  (declare (xargs :mode :program))
  (cond ((atom formals) nil)
        ((car stobjs) (fn-cw-non-stobj-formals (cdr formals) (cdr stobjs)))
        (t (cons (car formals) (fn-cw-non-stobj-formals (cdr formals) (cdr stobjs))))))

(defun fn-cw-resolve-step (fn step profile w)
  (declare (xargs :mode :program))
  ; (mv MSG STEP-FN EVENT-FORMAL EVENT THM) of a writer's :step, (EVENT THM)
  ; through the profile's step or (STEP EVENT THM) through a named one
  (let ((st (fn-cd-get :state profile)))
    (cond
     ((null step) (mv nil nil nil nil nil))
     ((not (and (true-listp step) (member (len step) '(2 3))))
      (mv (msg "~x0: :step ~x1 is not (EVENT-TERM THM) or (STEP EVENT-TERM THM)" fn step)
          nil nil nil nil))
     ((and (equal (len step) 2) (null (fn-cd-get :step profile)))
      (mv (msg "~x0 declares :step (EVENT-TERM THM) but its profile ~x1 names no step ~
                transition: say (STEP EVENT-TERM THM)" fn (fn-cd-get :invariant profile))
          nil nil nil nil))
     ((equal (len step) 2)
      (mv nil (car (fn-cd-get :step profile)) (cadr (fn-cd-get :step profile))
          (car step) (cadr step)))
     ((not (and (symbolp (car step)) (car step)
                (not (eq (getpropc (car step) 'formals :none w) :none))
                (fn-cd-stobj-position st (stobjs-out (car step) w) w)))
      (mv (msg "~x0: :step names ~x1, which is not a function returning ~x2 in this world"
               fn (car step) st)
          nil nil nil nil))
     (t (let ((evfs (fn-cw-non-stobj-formals (getpropc (car step) 'formals nil w)
                                            (stobjs-in (car step) w))))
          (if (and (consp evfs) (null (cdr evfs)))
              (mv nil (car step) (car evfs) (cadr step) (caddr step))
            (mv (msg "~x0: :step's ~x1 has ~x2 non-stobj formals ~x3; the event formal ~
                      is not determined (name it in the profile's :step)"
                     fn (car step) (len evfs) evfs)
                nil nil nil nil)))))))

(defun fn-cw-step-event (step)
  (declare (xargs :mode :program))
  (if (equal (len step) 3) (cadr step) (car step)))

(defun fn-cw-step-thm (step)
  (declare (xargs :mode :program))
  (if (equal (len step) 3) (caddr step) (cadr step)))

(defun fn-cw-problem (fn kvs w)
  (declare (xargs :mode :program))
  ; (mv MSG UNCOVERED): MSG nil when every check passes; UNCOVERED the guard
  ; conjuncts over other stobjs alone, recorded in the row
  (let* ((pname (fn-cw-get :profile kvs))
         (profile (cdr (assoc-eq pname (table-alist 'fn-carried-profiles w))))
         (r (fn-cd-get :invariant profile))
         (st (fn-cd-get :state profile))
         (opens (fn-cw-get :opens kvs))
         (vias (fn-cw-get :via kvs))
         (lemmas (fn-cw-get :lemmas kvs))
         (step (fn-cw-get :step kvs))
         (bridges (fn-cw-get :bridges kvs)))
    (cond
     ((not (and (symbolp fn) fn)) (mv (msg "~x0 is not a function name" fn) nil))
     ((not (keyword-value-listp kvs)) (mv (msg "~x0: options are not a keyword list" fn) nil))
     ((fn-cd-unknown-keys kvs *fn-cw-keys*)
      (mv (msg "~x0: unknown keyword(s) ~&1; the keywords are ~&2"
               fn (fn-cd-unknown-keys kvs *fn-cw-keys*) *fn-cw-keys*)
          nil))
     ((null profile)
      (mv (msg "~x0: :profile ~x1 is not a carried-writer profile of this world ~
                (def-carried-profile)" fn pname)
          nil))
     ((assoc-eq fn (table-alist 'fn-carried-writers w))
      (mv (msg "~x0 is already a declared writer of this world; a writer is declared once" fn)
          nil))
     ((eq (getpropc fn 'formals :none w) :none)
      (mv (msg "~x0 is not a function in this world" fn) nil))
     ((eq (symbol-class fn w) :program)
      (mv (msg "~x0 is :program mode: no theorem can be stated about it; convert it ~
                to :logic (with :verify-guards nil; the guards are verified here)" fn)
          nil))
     ((not (symbol-listp opens)) (mv (msg "~x0: :opens ~x1 is not a list of names" fn opens) nil))
     ((fn-cw-first-non-function opens w)
      (mv (msg "~x0: :opens names ~x1, which is not a function in this world"
               fn (car (fn-cw-first-non-function opens w)))
          nil))
     ((not (fn-cw-viasp vias))
      (mv (msg "~x0: :via ~x1 is not (THM | (THM (VAR TERM) ...) ...)" fn vias) nil))
     ((fn-cw-first-non-theorem (fn-cw-via-names vias) w)
      (mv (msg "~x0: :via names ~x1, which is not a theorem in this world"
               fn (car (fn-cw-first-non-theorem (fn-cw-via-names vias) w)))
          nil))
     ((not (symbol-listp lemmas)) (mv (msg "~x0: :lemmas ~x1 is not a list of names" fn lemmas) nil))
     ((fn-cw-first-non-theorem lemmas w)
      (mv (msg "~x0: :lemmas names ~x1, which is not a theorem in this world"
               fn (car (fn-cw-first-non-theorem lemmas w)))
          nil))
     ((and step (mv-let (m a b c d) (fn-cw-resolve-step fn step profile w)
                  (declare (ignore a b c d)) m))
      (mv (mv-let (m a b c d) (fn-cw-resolve-step fn step profile w)
            (declare (ignore a b c d)) m)
          nil))
     ((and step (not (fn-cw-step-kind (fn-cw-step-event step))))
      (mv (msg "~x0: :step's event ~x1 is not a (list :KIND ...) term" fn (fn-cw-step-event step))
          nil))
     ((and step (fn-cw-first-non-theorem (list (fn-cw-step-thm step)) w))
      (mv (msg "~x0: :step names ~x1, which is not a theorem in this world"
               fn (fn-cw-step-thm step))
          nil))
     ((not (fn-cd-pairsp bridges))
      (mv (msg "~x0: :bridges ~x1 is not ((PRED THM) ...)" fn bridges) nil))
     ((fn-cw-first-non-theorem (strip-cadrs bridges) w)
      (mv (msg "~x0: :bridges names ~x1, which is not a theorem in this world"
               fn (car (fn-cw-first-non-theorem (strip-cadrs bridges) w)))
          nil))
     ((not (true-listp (fn-cw-get :hyps kvs)))
      (mv (msg "~x0: :hyps ~x1 is not a list of terms" fn (fn-cw-get :hyps kvs)) nil))
     ((and (assoc-keyword :name kvs)
           (not (and (symbolp (fn-cw-get :name kvs)) (fn-cw-get :name kvs))))
      (mv (msg "~x0: :name ~x1 is not a symbol" fn (fn-cw-get :name kvs)) nil))
     ((fn-cw-first-non-rune (fn-cw-get :guard-theory kvs) w)
      (mv (msg "~x0: :guard-theory names ~x1, which is neither a rule nor a function nor ~
                a rune" fn (car (fn-cw-first-non-rune (fn-cw-get :guard-theory kvs) w)))
          nil))
     ((getpropc (fn-cw-theorem-name fn kvs profile) 'theorem nil w)
      (mv (msg "~x0: ~x1 is already a theorem of this world"
               fn (fn-cw-theorem-name fn kvs profile))
          nil))
     ((and step (mv-let (m pstep evf event thm) (fn-cw-resolve-step fn step profile w)
                  (declare (ignore m thm))
                  (eq (fn-cw-step-reusable (fn-cw-step-name pstep profile event fn)
                                           (fn-cw-step-statement pstep evf event profile w) w)
                      :other)))
      (mv (msg "~x0: the step lemma ~x1 is already a theorem of this world with another ~
                statement" fn (mv-let (m pstep evf event thm) (fn-cw-resolve-step fn step profile w)
                                (declare (ignore m evf thm))
                                (fn-cw-step-name pstep profile event fn)))
          nil))
     (t
      (mv-let (msg s ret all)
        (fn-cd-parts st (list fn 'none) w)
        (declare (ignore ret all))
        (if msg
            (mv msg nil)
          (mv-let (bade eterms)
            (fn-cd-translate-list (append (fn-cw-get :hyps kvs)
                                          (and step (list (fn-cw-step-event step))))
                                  w)
            (mv-let (refusal uncovered)
              (fn-cw-guard-classes (flatten-ands-in-lit (getpropc fn 'guard *t* w))
                                   fn s r profile bridges w)
              (let* ((hterms (take (len (fn-cw-get :hyps kvs)) eterms))
                     (eterms (nthcdr (len (fn-cw-get :hyps kvs)) eterms))
                     (wp (fn-cw-writes-problem (cons fn opens) fn st opens
                                               (fn-cd-get :installers profile)
                                               (fn-cd-get :carried-globals profile)
                                               (fn-cw-covered kvs profile w) w)))
                (cond
                 (bade (mv (msg "~x0: ~x1 does not translate in this world" fn (car bade))
                           nil))
                 ((fn-cw-first-non-conjunct
                   hterms (flatten-ands-in-lit (getpropc fn 'guard *t* w)))
                  (mv (msg "~x0: :hyps ~x1 is not a conjunct of ~x0's guard: a hypothesis ~
                            the guard does not state is a premise the host does not ~
                            check, and def-carried refuses it on a transition"
                           fn (car (fn-cw-first-non-conjunct
                                    hterms (flatten-ands-in-lit (getpropc fn 'guard *t* w)))))
                      nil))
                 ((and step (not (subsetp-eq (all-vars (car eterms))
                                             (getpropc fn 'formals nil w))))
                  (mv (msg "~x0: :step's event ~x1 mentions variables that are not ~x0's ~
                            formals ~x2" fn (fn-cw-step-event step) (getpropc fn 'formals nil w))
                      nil))
                 ((and refusal (eq (car (car refusal)) :argument))
                  (mv (msg "~x0's guard conjunct ~x1 is over ~x2, an argument the host ~
                            passes per call, and is not a kind check: no preservation ~
                            theorem can establish it (definterface refuses the raw ~
                            dispatch), so it belongs in the body as a refusal"
                           fn (cadr refusal) (cdr (car refusal)))
                      nil))
                 (refusal
                  (mv (msg "~x0's guard conjunct ~x1 applies ~x2 to the carried state ~
                            and no bridge concludes it from ~x3 (the row ~x4's ~
                            :concludes, this writer's :bridges): declare :bridges ~
                            ((~x2 THM)) with THM proving (implies (~x3 x) <the conjunct ~
                            at x>)"
                           fn (cadr refusal) (cdr (car refusal)) r (fn-cd-get :row profile))
                      nil))
                 (wp (mv wp nil))
                 (t (mv nil uncovered))))))))))))

(defun fn-cw-subst-sym (var new term)
  (declare (xargs :mode :program))
  ; the untranslated TERM with the symbol VAR replaced by NEW (quotes kept)
  (cond ((eq term var) new)
        ((atom term) term)
        ((eq (car term) 'quote) term)
        (t (cons (fn-cw-subst-sym var new (car term))
                 (fn-cw-subst-sym var new (cdr term))))))

(defun fn-cw-at-bindings (at formal s thm w)
  (declare (xargs :mode :program))
  ; the profile's :at bindings whose variable THM mentions, over the writer's
  ; carried formal S in place of the invariant's FORMAL
  (let ((vars (all-vars (getpropc thm 'theorem nil w))))
    (cond ((atom at) nil)
          ((member-eq (caar at) vars)
           (cons (list (caar at) (fn-cw-subst-sym formal s (cadar at)))
                 (fn-cw-at-bindings (cdr at) formal s thm w)))
          (t (fn-cw-at-bindings (cdr at) formal s thm w)))))

(defun fn-cw-instances (vias at formal s w)
  (declare (xargs :mode :program))
  (if (atom vias)
      nil
    (let* ((thm (fn-cw-via-name (car vias)))
           (own (if (consp (car vias)) (cdar vias) nil)))
      (cons `(:instance ,thm ,@(fn-cw-at-bindings at formal s thm w) ,@own)
            (fn-cw-instances (cdr vias) at formal s w)))))

(defun fn-cw-step-events (fn kvs profile w)
  (declare (xargs :mode :program))
  ; (mv NAME EVENTS): the lemma that STEP at the writer's event keeps R, or
  ; the existing one's name and no event
  (mv-let (msg pstep evf event thm)
    (fn-cw-resolve-step fn (fn-cw-get :step kvs) profile w)
    (declare (ignore msg))
    (let* ((name (fn-cw-step-name pstep profile event fn))
           (statement (fn-cw-step-statement pstep evf event profile w))
           (formal (fn-cd-get :formal profile))
           (s (mv-let (m s ret all) (fn-cd-parts (fn-cd-get :state profile) (list pstep 'none) w)
                (declare (ignore m ret all)) s)))
      (if (eq (fn-cw-step-reusable name statement w) :reusable)
          (mv name nil)
        (mv name
            `((defthm ,name
                ,statement
                :hints (("Goal" :in-theory (union-theories
                                            '(,pstep ,@(fn-cd-get :frame profile)
                                              ,@(fn-cd-get :theory profile))
                                            (theory 'minimal-theory))
                         :use (,@(fn-cw-instances (list thm) (fn-cd-get :at profile)
                                                  formal s w)
                               ,(fn-cd-get :bridge profile)))))))))))

(defun fn-cw-events (fn kvs uncovered w)
  (declare (xargs :mode :program))
  (let* ((pname (fn-cw-get :profile kvs))
         (profile (cdr (assoc-eq pname (table-alist 'fn-carried-profiles w))))
         (r (fn-cd-get :invariant profile))
         (st (fn-cd-get :state profile))
         (formal (fn-cd-get :formal profile))
         (opens (fn-cw-get :opens kvs))
         (vias (fn-cw-get :via kvs))
         (lemmas (fn-cw-get :lemmas kvs))
         (step (fn-cw-get :step kvs))
         (name (fn-cw-theorem-name fn kvs profile))
         (keys (fn-cw-written-keys (cons fn opens) w)))
    (mv-let (msg s ret all)
      (fn-cd-parts st (list fn 'none) w)
      (declare (ignore msg all))
      (mv-let (step-name step-events)
        (if step (fn-cw-step-events fn kvs profile w) (mv nil nil))
      (let ((statement `(implies ,(fn-cw-conj (cons (list r s) (fn-cw-get :hyps kvs)))
                                 (,r ,(fn-cw-untranslate-ret ret)))))
        `(progn
           ,@(and (eq (symbol-class fn w) :ideal)
                  `((verify-guards ,fn
                      :hints ,(if (assoc-keyword :guard-hints kvs)
                                  (fn-cw-get :guard-hints kvs)
                                `(("Goal" :in-theory (union-theories
                                                      '(,fn ,@opens
                                                        ,@(fn-cd-get :guard-theory profile)
                                                        ,@(fn-cw-get :guard-theory kvs))
                                                      (theory 'minimal-theory))))))))
           ,@step-events
           (defthm ,name
             ,statement
             :hints ,(if (assoc-keyword :hints kvs)
                         (fn-cw-get :hints kvs)
                       `(("Goal" :in-theory (union-theories
                                             '(,fn ,@opens ,@lemmas
                                               ,@(and step (list step-name))
                                               ,@(fn-cd-get :frame profile)
                                               ,@(fn-cd-get :theory profile))
                                             (theory 'minimal-theory))
                          :use (,@(fn-cw-instances vias (fn-cd-get :at profile) formal s w)
                                ,(fn-cd-get :bridge profile))))))
           (table fn-carried-writers ',fn
                  '(:profile ,pname :theorem ,name :via ,vias :opens ,opens
                    :lemmas ,lemmas :step ,step :bridges ,(fn-cw-get :bridges kvs)
                    :hyps ,(fn-cw-get :hyps kvs)
                    :put-keys ,keys :uncovered ,uncovered
                    :hand-hints ,(if (or (assoc-keyword :hints kvs)
                                         (assoc-keyword :guard-hints kvs))
                                     t nil)))
           ; the teeth contract v1 (lanedumps/generators-2.md): the claim is the
           ; labelled source hypotheses and the conclusion; the subject is FN
           (table fn-teeth-owed ',name
                  '(:by def-carried-writer
                    :claim (((inv (,r ,s))
                             ,@(fn-cw-label-hyps (fn-cw-get :hyps kvs) 1 fn))
                            (,r ,(fn-cw-untranslate-ret ret)))
                    :subject ,fn))))))))

(defmacro def-carried-writer (fn &rest kvs)
  `(make-event
    (mv-let (problem uncovered)
      (fn-cw-problem ',fn ',kvs (w state))
      (if problem
          (er soft 'def-carried-writer "~x0: ~@1" ',fn problem)
        (value (fn-cw-events ',fn ',kvs uncovered (w state)))))))

; ---------------------------------------------------------------------------
; The row: def-carried over the profile's writers, the pilot's open and bridges.

(defun fn-cw-profile-writers (pname rows)
  (declare (xargs :mode :program))
  ; (FN THM) for every fn-carried-writers row of profile PNAME, oldest first
  (cond ((atom rows) nil)
        ((eq (fn-cd-get :profile (cdar rows)) pname)
         (append (fn-cw-profile-writers pname (cdr rows))
                 (list (list (caar rows) (fn-cd-get :theorem (cdar rows))))))
        (t (fn-cw-profile-writers pname (cdr rows)))))

(defun fn-cw-profile-bridges (pname rows)
  (declare (xargs :mode :program))
  ; every (PRED THM) the profile's writers declare, oldest first
  (cond ((atom rows) nil)
        ((eq (fn-cd-get :profile (cdar rows)) pname)
         (append (fn-cw-profile-bridges pname (cdr rows)) (fn-cd-get :bridges (cdar rows))))
        (t (fn-cw-profile-bridges pname (cdr rows)))))

(defun fn-cw-merge-bridges (bridges acc)
  (declare (xargs :mode :program))
  ; (mv CONFLICT MERGED): one theorem per PRED, or the conflicting pair
  (cond ((atom bridges) (mv nil (reverse acc)))
        ((assoc-eq (caar bridges) acc)
         (if (eq (cadr (assoc-eq (caar bridges) acc)) (cadar bridges))
             (fn-cw-merge-bridges (cdr bridges) acc)
           (mv (list (assoc-eq (caar bridges) acc) (car bridges)) nil)))
        (t (fn-cw-merge-bridges (cdr bridges) (cons (car bridges) acc)))))

(defun fn-cw-producers-form (producers)
  (declare (xargs :mode :program))
  ; a normalized :produced back to the input form (P THM :assuming (A ...))
  (if (atom producers)
      nil
    (cons (list* (caar producers) (cadar producers)
                 (let ((as (fn-cd-get :assuming (cddar producers))))
                   (and as (list :assuming as))))
          (fn-cw-producers-form (cdr producers)))))

(defun fn-cw-entry-form (entry)
  (declare (xargs :mode :program))
  ; a normalized def-carried entry back to its input form
  (let ((opts (cddr entry)))
    (list* (car entry) (cadr entry)
           (append (and (fn-cd-get :hyps opts) (list :hyps (fn-cd-get :hyps opts)))
                   (and (assoc-keyword :ok opts) (list :ok (fn-cd-get :ok opts)))
                   (and (assoc-keyword :witness opts)
                        (list :witness (fn-cd-get :witness opts)))
                   (and (fn-cd-get :produced opts)
                        (list :produced (fn-cw-producers-form (fn-cd-get :produced opts))))
                   (and (assoc-keyword :state opts)
                        (list :state (fn-cd-get :state opts)
                              :result (fn-cd-get :result opts)))))))

(defun fn-cw-entry-forms (entries)
  (declare (xargs :mode :program))
  (if (atom entries) nil (cons (fn-cw-entry-form (car entries)) (fn-cw-entry-forms (cdr entries)))))

(defun fn-cw-pairs (entries)
  (declare (xargs :mode :program))
  (if (atom entries) nil (cons (list (caar entries) (cadar entries)) (fn-cw-pairs (cdr entries)))))

(defun fn-cw-row-form (name pname pilot kvs w)
  (declare (xargs :mode :program))
  ; (mv MSG FORM): the def-carried form, or why not
  (let* ((profile (cdr (assoc-eq pname (table-alist 'fn-carried-profiles w))))
         (row (cdr (assoc-eq pilot (table-alist 'fn-carried w))))
         (writers (fn-cw-profile-writers pname (table-alist 'fn-carried-writers w))))
    (mv-let (conflict bridges)
      (fn-cw-merge-bridges
       (append (fn-cw-pairs (fn-cd-get :concludes row))
               (fn-cw-profile-bridges pname (table-alist 'fn-carried-writers w)))
       nil)
      (cond
       ((null profile) (mv (msg "~x0: :profile ~x1 is not a profile of this world" name pname) nil))
       ((null row) (mv (msg "~x0: :from ~x1 is not a carried invariant of this world" name pilot) nil))
       ((not (eq (fn-cd-get :invariant row) (fn-cd-get :invariant profile)))
        (mv (msg "~x0: the pilot row ~x1 carries ~x2, the profile ~x3 carries ~x4"
                 name pilot (fn-cd-get :invariant row) pname (fn-cd-get :invariant profile))
            nil))
       ((null writers)
        (mv (msg "~x0: no writer of profile ~x1 is declared in this world" name pname) nil))
       (conflict
        (mv (msg "~x0: the bridge for ~x1 is named twice with different theorems, ~x2 ~
                  and ~x3" name (caar conflict) (cadar conflict) (cadadr conflict))
            nil))
       (t (mv nil
              `(def-carried ,name
                 :invariant ,(fn-cd-get :invariant row)
                 :established ,(fn-cw-entry-forms (fn-cd-get :established row))
                 :transitions ,(append (fn-cw-pairs (fn-cd-get :transitions row)) writers)
                 :concludes ,bridges
                 ,@(and (fn-cd-get :complete-by row)
                        (list :complete-by (fn-cd-get :complete-by row)))
                 :trace ,(if (assoc-keyword :trace kvs) (fn-cw-get :trace kvs) nil))))))))

(defmacro def-carried-writers-row (name &rest kvs)
  `(make-event
    (mv-let (problem form)
      (fn-cw-row-form ',name (cadr (assoc-keyword :profile ',kvs))
                      (cadr (assoc-keyword :from ',kvs)) ',kvs (w state))
      (if problem
          (er soft 'def-carried-writers-row "~x0: ~@1" ',name problem)
        (value form)))))

; The owed entries: declared host-called entries (fn-interfaces) that return
; the carrier and are neither the pilot's nor a declared writer's.
(defun fn-cw-owed (pname pilot w)
  (declare (xargs :mode :program))
  (let* ((profile (cdr (assoc-eq pname (table-alist 'fn-carried-profiles w))))
         (row (cdr (assoc-eq pilot (table-alist 'fn-carried w))))
         (st (fn-cd-get :state profile))
         (listed (append (strip-cars (fn-cd-get :established row))
                         (strip-cars (fn-cd-get :transitions row))
                         (strip-cars (fn-cw-profile-writers
                                      pname (table-alist 'fn-carried-writers w))))))
    (and profile st
         (set-difference-eq
          (fn-cd-returning-entries (table-alist 'fn-interfaces w) st w)
          listed))))

(defmacro def-carried-writers-owed (pname &key from)
  `(make-event
    (let ((owed (fn-cw-owed ',pname ',from (w state))))
      (prog2$ (cw "~%def-carried-writers-owed ~x0: ~x1 host-called entr~#2~[y~/ies~] ~
                   return~#2~[s~/~] the carrier with no writer row: ~x3~%"
                  ',pname (len owed) (if (equal (len owed) 1) 0 1) owed)
              (value `(value-triple ',(len owed)))))))
