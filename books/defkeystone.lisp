; fn: `defteeth' and `defkeystone' --- a keystone's teeth, generated from a
; declared CLAIM bound to the theorem as the world stores it (TEETH CONTRACT
; v1, build/coordinator/lanedumps/generators-2.md, after consultation c04).
;
; AGENTS.md ("What makes a claim") fixes what a keystone ships with: a
; reachable positive witness asserting the complete antecedent and
; conclusion; per hypothesis a removal witness that checks every retained
; hypothesis, the failure of the omitted one and the failure of the
; conclusion; corrupted-state and mutation witnesses labelled apart; and a
; registry row naming the subject, the function the host calls.  Here the
; schema is the macro, for a theorem the form states (defkeystone) or one
; admitted anywhere (defteeth):
;
;   (defteeth NAME
;     :claim (((L1 H1) ... (Ln Hn)) C)      ; REQUIRED: labelled source hypotheses
;                                           ; and the conclusion
;     [:subject FN]                         ; the host-called function; REQUIRED
;                                           ; when a bound is stated
;     :witness ((VAR VAL) ...)              ; the positive witness, executable;
;     [:witness-lemma THM]                  ; or a named ground theorem instead of
;                                           ; evaluation (its formula is checked)
;     :breaks ((Li ((VAR VAL) ...) [:logical "why outside the guard domain"]
;                  [:lemma THM]) ...)       ; one per Li
;     :mutations ((L (:conclusion C2) | (:hypothesis Li H2) ((VAR VAL) ...)
;                    [:lemma THM]) ...)
;                | (:not-applicable "why") | (:deferred "why")
;     [:corrupt ((L ((VAR VAL) ...)) ...)]
;     [:visits ((L V B :attains ((VAR VAL) ...) | :not-attained "why"
;                  [:rests-on (A ...)] [:hints H]) ...)]
;     [:allocation (... the same shape ...)]
;     [:must-fail t]                        ; also register the weakened and
;                                           ; mutant statements as must-fail-checked
;     [:hints H])
;
;   (defkeystone NAME TERM :subject FN [:id "PRF-NNN"] [:restates K] [:hyps (L..)]
;     . SPEC)                               ; = (defthm NAME TERM ...) then defteeth,
;                                           ; the :claim derived from TERM's source
;                                           ; `implies' / `and'
;
; BINDING (c04 1e).  When the form runs, (implies (and H1 .. Hn) C) is
; TRANSLATED in the current world and must be EQUAL to (getpropc NAME
; 'theorem); else the form is refused (:claim-differs, printing both).  A
; label names a DECLARED source hypothesis, so a removal is per declared
; hypothesis, never per translated conjunct.  The static tools
; (tools/ledger.py defteeth_expansion) read the :claim and never the world.
;
; WITNESS MODES (c04 1a).  The positive witness and every bound witness run
; UNDER THE GUARDS, as the host would (a guard violation fails the book).  A
; removal, mutation or corrupted-state witness runs under the guards too,
; unless its entry says `:logical "why"', when it is evaluated for its
; LOGICAL value (with-guard-checking :none) and the row records the label as
; a :logical removal.  Any witness entry may say `:lemma THM' instead: THM is
; a theorem of the world whose formula must EQUAL the translated claim
; instantiated at the entry's bindings (a predicate no evaluator runs is
; witnessed by a proved ground fact, never pretended executed).
;
; MUTATIONS (c04 1c) are CHECKED EDITS of the claim, never a free term:
; (:conclusion C2) is the claim with C2 for C (refused when C2 is C, nil or
; t); (:hypothesis Li H2) has H2 for Hi (refused when H2 is Hi or t).  At the
; mutation witness every Hi holds, C holds, and the edited part fails ((not
; C2); for a hypothesis edit, H2 holds and C fails).  `:not-applicable' and
; `:deferred', each with a reason, are RECORDED and counted; a deferred
; mutation is not a tooth.
;
; BOUNDS (c04 1d).  A :visits or :allocation entry states a cost claim
; NAME-visits-L / NAME-allocation-L, (implies (and H...) (<= V B)), proved
; with the entry's :hints, evaluated at the witness, and (equal V B) at the
; :attains bindings or `:not-attained "why"' recorded: a bound nothing
; attains is slack, not a claim.  V is the caller's visit-counting term;
; this book records it and does not derive it (COST-GATE / DEF-ENTRY tie it
; to the executed definition).  `:rests-on (A ...)' names the facts the
; bound rests on.  A bound without :subject is refused.
;
; MUST-FAIL (c04 1f, 6e) is OFF by default: a must-fail is proof-search
; exhaustion within a step limit, not a counterexample; the evaluated
; witnesses are the teeth.  `:must-fail t' also registers NAME-without-Li
; and NAME-mutant-L as must-fail-checked (then the book includes
; tests/acl2/must-fail-checked).
;
; Emitted, in order (fn-dk-teeth-events): the positive assert-event (or the
; lemma check); per hypothesis the removal assert-event (every retained Hj,
; not Hi, not C) [and its must-fail]; per mutation its assert-event [and
; must-fail]; per corrupted state; per bound its defthm, witness and
; attainment; and (table fn-teeth 'NAME ROW).  An assert-event carries its
; label in :msg ("NAME: witness", "NAME: without L", "NAME: mutant L",
; "NAME: corrupt L", "NAME: visits L", "NAME: attains L").
;
; ROW IDENTITY.  ROW = (:by defteeth|defkeystone :claim CLAIM :formula
; FORMULA :subject FN :hyps (L...) :removals ((L :reachable|:logical) ...)
; :mutations ((L :conclusion|:hypothesis) ...) | :not-applicable | :deferred
; :corrupt (L...) :visits ((L V B :attains|:not-attained :rests-on (A...))
; ...) :allocation (...)).  FORMULA is the world's theorem at declaration: a
; restatement under the same name is a new obligation (defteeth-check sees
; the row no longer match the world).  Declared once per name.
;
; FOR A GENERATOR (c04 6f).  A source-side macro cannot read K from the world
; before admitting it.  It emits, in its progn, in order: (defthm K ...);
; (table fn-teeth-owed 'K '(:by MACRO :claim CLAIM [:subject FN] [:visits
; ((V B [:rests-on (A ...)]) ...)] [:allocation (...)])), the debt: what the
; teeth MUST say; and, when the witnesses are in hand, (defteeth K :claim
; CLAIM ...) as a LATER event of the same progn (it is a make-event, so it
; binds to the world after the defthm).  World-free helpers:
; (fn-teeth-refusal NAME SPEC) -> nil or (REASON . DETAILS) over the SPEC
; alone; (fn-teeth-form NAME SPEC) -> the make-event form to splice.  No
; helper takes a world.
;
; CONSUMERS.  (1) at expansion: every refusal, a soft error naming the gap;
; (2) `(defteeth-check)', the last form of a book that declares teeth for a
; generator's keystones: every fn-teeth-owed row of the included books has a
; row whose :claim, :subject and every owed bound (V, B, :rests-on) are
; EQUAL and whose :formula is still the world's theorem; (3) the late gate
; in `make check', tools/keystone_emit.py --check over the obligation
; manifest planning/teeth-obligations.json (one entry per registry event and
; per owed row; generated never downgrades; a new name must be generated).
;
; The static tools read the SAME expansion without evaluating anything:
; tools/ledger.py mirrors fn-dk-teeth-events form for form from the :claim,
; and tests/acl2/defkeystone-tests.lisp pins both to one literal expansion
; (tests/test_ledger.py reads that literal).  Change one, change the other
; and the literal together.  This book has no `include-book' and leaves no
; rule: its helpers are `:program' mode (declared per defun, as
; books/defrecord.lisp does, so tools/ledger.py's `exports_no_rule' sees a
; macro book).

(in-package "ACL2")


(defconst *fn-dk-spec-keys*
  '(:claim :subject :witness :witness-lemma :breaks :mutations :corrupt
    :visits :allocation :must-fail :hints))

(defconst *fn-dk-keys*
  (append '(:id :restates :hyps :rule-classes :otf-flg) *fn-dk-spec-keys*))

(defconst *fn-dk-bound-kinds* '((:visits . -visits-) (:allocation . -allocation-)))

(defun fn-dk-get (key kvs)
  (declare (xargs :mode :program))
  (cadr (assoc-keyword key kvs)))

; ---------------------------------------------------------------------------
; The claim: (((L1 H1) ... (Ln Hn)) C).

(defun fn-dk-labelled-hypsp (x)
  (declare (xargs :mode :program))
  (if (atom x)
      (null x)
    (and (true-listp (car x)) (equal (len (car x)) 2)
         (symbolp (caar x)) (caar x)
         (fn-dk-labelled-hypsp (cdr x)))))

(defun fn-dk-claimp (x)
  (declare (xargs :mode :program))
  (and (true-listp x) (equal (len x) 2)
       (fn-dk-labelled-hypsp (car x))
       (no-duplicatesp-eq (strip-cars (car x)))))

(defun fn-dk-claim-labels (claim)
  (declare (xargs :mode :program))
  (strip-cars (car claim)))

(defun fn-dk-claim-hyps (claim)
  (declare (xargs :mode :program))
  (strip-cadrs (car claim)))

(defun fn-dk-claim-concl (claim)
  (declare (xargs :mode :program))
  (cadr claim))

(defun fn-dk-implies (hyps concl)
  (declare (xargs :mode :program))
  (cond ((atom hyps) concl)
        ((atom (cdr hyps)) `(implies ,(car hyps) ,concl))
        (t `(implies (and ,@hyps) ,concl))))

(defun fn-dk-conj (terms)
  (declare (xargs :mode :program))
  (if (and (consp terms) (atom (cdr terms)))
      (car terms)
    `(and ,@terms)))

(defun fn-dk-statement (claim)
  (declare (xargs :mode :program))
  (fn-dk-implies (fn-dk-claim-hyps claim) (fn-dk-claim-concl claim)))

; defkeystone derives the claim from TERM's source `implies'/`and'.
(defun fn-dk-source-hyps (term)
  (declare (xargs :mode :program))
  (if (and (consp term) (eq (car term) 'implies) (true-listp term)
           (equal (len term) 3))
      (let ((h (cadr term)))
        (if (and (consp h) (eq (car h) 'and))
            (cdr h)
          (list h)))
    nil))

(defun fn-dk-source-concl (term)
  (declare (xargs :mode :program))
  (if (and (consp term) (eq (car term) 'implies) (true-listp term)
           (equal (len term) 3))
      (caddr term)
    term))

(defun fn-dk-default-labels (i n name)
  (declare (xargs :mode :program))
  (if (zp n)
      nil
    (cons (packn-pos (list 'h i) name)
          (fn-dk-default-labels (1+ i) (1- n) name))))

(defun fn-dk-pairs (labels hyps)
  (declare (xargs :mode :program))
  (if (atom labels)
      nil
    (cons (list (car labels) (car hyps)) (fn-dk-pairs (cdr labels) (cdr hyps)))))

(defun fn-dk-claim-of (name term kvs)
  (declare (xargs :mode :program))
  ; the claim a defkeystone form states: TERM's hypotheses under :hyps or
  ; H1..Hn, and its conclusion
  (let* ((hyps (fn-dk-source-hyps term))
         (labels (if (assoc-keyword :hyps kvs)
                     (fn-dk-get :hyps kvs)
                   (fn-dk-default-labels 1 (len hyps) name))))
    (list (fn-dk-pairs labels hyps) (fn-dk-source-concl term))))

; ---------------------------------------------------------------------------
; The spec's shapes.

(defun fn-dk-bindingsp (x)
  (declare (xargs :mode :program))
  ; ((VAR VAL) ...) with distinct symbol VARs
  (and (true-listp x)
       (doublet-listp x)
       (symbol-listp (strip-cars x))
       (no-duplicatesp-eq (strip-cars x))))

(defun fn-dk-unknown-keys-of (kvs keys)
  (declare (xargs :mode :program))
  (cond ((atom kvs) nil)
        ((member-eq (car kvs) keys) (fn-dk-unknown-keys-of (cddr kvs) keys))
        (t (cons (car kvs) (fn-dk-unknown-keys-of (cddr kvs) keys)))))

(defun fn-dk-reasonp (x)
  (declare (xargs :mode :program))
  (and (stringp x) (< 0 (length x))))

(defun fn-dk-entry-optsp (opts keys)
  (declare (xargs :mode :program))
  ; a witness entry's options: among KEYS, :lemma a symbol, :logical a reason
  (and (keyword-value-listp opts)
       (null (fn-dk-unknown-keys-of opts keys))
       (or (null (assoc-keyword :lemma opts))
           (and (symbolp (fn-dk-get :lemma opts)) (fn-dk-get :lemma opts)))
       (or (null (assoc-keyword :logical opts))
           (fn-dk-reasonp (fn-dk-get :logical opts)))))

(defun fn-dk-break-entryp (x)
  (declare (xargs :mode :program))
  ; (LABEL BINDINGS [:logical "why"] [:lemma THM])
  (and (true-listp x) (<= 2 (len x))
       (symbolp (car x)) (car x)
       (fn-dk-bindingsp (cadr x))
       (fn-dk-entry-optsp (cddr x) '(:logical :lemma))))

(defun fn-dk-break-entriesp (x)
  (declare (xargs :mode :program))
  (if (atom x)
      (null x)
    (and (fn-dk-break-entryp (car x))
         (fn-dk-break-entriesp (cdr x)))))

(defun fn-dk-exemptionp (x)
  (declare (xargs :mode :program))
  ; (:not-applicable "why") or (:deferred "why")
  (and (true-listp x) (equal (len x) 2)
       (member-eq (car x) '(:not-applicable :deferred))
       (fn-dk-reasonp (cadr x))))

(defun fn-dk-editp (x)
  (declare (xargs :mode :program))
  ; (:conclusion C2) or (:hypothesis Li H2)
  (and (true-listp x)
       (or (and (equal (len x) 2) (eq (car x) :conclusion))
           (and (equal (len x) 3) (eq (car x) :hypothesis)
                (symbolp (cadr x)) (cadr x)))))

(defun fn-dk-mutation-entryp (x)
  (declare (xargs :mode :program))
  ; (LABEL EDIT BINDINGS [:logical "why"] [:lemma THM])
  (and (true-listp x) (<= 3 (len x))
       (symbolp (car x)) (car x)
       (fn-dk-editp (cadr x))
       (fn-dk-bindingsp (caddr x))
       (fn-dk-entry-optsp (cdddr x) '(:logical :lemma))))

(defun fn-dk-mutationsp (x)
  (declare (xargs :mode :program))
  (if (atom x)
      (null x)
    (and (fn-dk-mutation-entryp (car x))
         (fn-dk-mutationsp (cdr x)))))

(defun fn-dk-mutation-entries (x)
  (declare (xargs :mode :program))
  (if (fn-dk-exemptionp x) nil x))

(defun fn-dk-corruptsp (x)
  (declare (xargs :mode :program))
  ; ((LABEL BINDINGS) ...)
  (if (atom x)
      (null x)
    (and (true-listp (car x))
         (equal (len (car x)) 2)
         (symbolp (car (car x)))
         (fn-dk-bindingsp (cadr (car x)))
         (fn-dk-corruptsp (cdr x)))))

(defun fn-dk-bound-entryp (x)
  (declare (xargs :mode :program))
  ; (LABEL V B :attains BINDINGS | :not-attained "why" [:rests-on (A ...)]
  ;  [:hints H] [:lemma THM])
  (and (true-listp x) (<= 3 (len x))
       (symbolp (car x)) (car x)
       (keyword-value-listp (cdddr x))
       (null (fn-dk-unknown-keys-of (cdddr x) '(:attains :not-attained :rests-on :hints :lemma)))
       (let ((attains (assoc-keyword :attains (cdddr x)))
             (none (assoc-keyword :not-attained (cdddr x))))
         (and (or attains none)
              (not (and attains none))
              (or (null attains) (fn-dk-bindingsp (cadr attains)))
              (or (null none) (fn-dk-reasonp (cadr none)))
              (true-listp (fn-dk-get :rests-on (cdddr x)))))))

(defun fn-dk-boundsp (x)
  (declare (xargs :mode :program))
  (if (atom x)
      (null x)
    (and (fn-dk-bound-entryp (car x))
         (fn-dk-boundsp (cdr x)))))

(defun fn-dk-first-unbroken (labels hyps breaks)
  (declare (xargs :mode :program))
  ; the first (LABEL HYP) with no :breaks entry, or nil
  (cond ((atom labels) nil)
        ((assoc-eq (car labels) breaks)
         (fn-dk-first-unbroken (cdr labels) (cdr hyps) breaks))
        (t (list (car labels) (car hyps)))))

(defun fn-dk-first-stray (entries labels)
  (declare (xargs :mode :program))
  ; the first entry label that names no hypothesis, or nil
  (cond ((atom entries) nil)
        ((member-eq (car (car entries)) labels)
         (fn-dk-first-stray (cdr entries) labels))
        (t (car (car entries)))))

(defun fn-dk-constantp (x)
  (declare (xargs :mode :program))
  (or (null x) (eq x t) (equal x ''nil) (equal x ''t)))

(defun fn-dk-first-bad-edit (mutations claim)
  (declare (xargs :mode :program))
  ; (LABEL REASON-KEYWORD) for the first mutation whose edit is no edit
  (if (atom mutations)
      nil
    (let* ((m (car mutations))
           (edit (cadr m))
           (labels (fn-dk-claim-labels claim))
           (hyps (fn-dk-claim-hyps claim)))
      (cond
       ((eq (car edit) :conclusion)
        (cond ((fn-dk-constantp (cadr edit)) (list (car m) :constant-conclusion))
              ((equal (cadr edit) (fn-dk-claim-concl claim)) (list (car m) :same-conclusion))
              (t (fn-dk-first-bad-edit (cdr mutations) claim))))
       (t
        (let ((i (position-eq (cadr edit) labels)))
          (cond ((null i) (list (car m) :edit-names-no-hypothesis))
                ((or (eq (caddr edit) t) (equal (caddr edit) ''t))
                 (list (car m) :trivial-hypothesis))
                ((equal (caddr edit) (nth i hyps)) (list (car m) :same-hypothesis))
                (t (fn-dk-first-bad-edit (cdr mutations) claim)))))))))

(defun fn-dk-spec-refusal (name kvs keys)
  (declare (xargs :mode :program))
  ; nil when the SPEC (the keyword-value list KVS, over KEYS) is well-formed;
  ; else (REASON . DETAILS), which names the offending hypothesis, entry or
  ; keyword.  World-free.  tests/acl2/defkeystone-tests asserts each reason.
  (let* ((claim (fn-dk-get :claim kvs))
         (labels (and (fn-dk-claimp claim) (fn-dk-claim-labels claim)))
         (hyps (and (fn-dk-claimp claim) (fn-dk-claim-hyps claim)))
         (breaks (fn-dk-get :breaks kvs))
         (mutations (fn-dk-get :mutations kvs))
         (visits (fn-dk-get :visits kvs))
         (allocation (fn-dk-get :allocation kvs)))
    (cond
     ((not (keyword-value-listp kvs)) (list :bad-options kvs))
     ((fn-dk-unknown-keys-of kvs keys)
      (cons :unknown-keyword (fn-dk-unknown-keys-of kvs keys)))
     ((not (assoc-keyword :claim kvs)) (list :no-claim name))
     ((not (fn-dk-claimp claim)) (list :bad-claim claim))
     ((not (and (fn-dk-get :witness kvs)
                (fn-dk-bindingsp (fn-dk-get :witness kvs))))
      (list :no-witness name))
     ((and (assoc-keyword :witness-lemma kvs)
           (not (and (symbolp (fn-dk-get :witness-lemma kvs)) (fn-dk-get :witness-lemma kvs))))
      (list :bad-witness-lemma (fn-dk-get :witness-lemma kvs)))
     ((and (assoc-keyword :subject kvs)
           (not (and (symbolp (fn-dk-get :subject kvs)) (fn-dk-get :subject kvs))))
      (list :bad-subject (fn-dk-get :subject kvs)))
     ((not (fn-dk-break-entriesp breaks)) (list :bad-breaks breaks))
     ((not (no-duplicatesp-eq (strip-cars breaks)))
      (list :duplicate-break (strip-cars breaks)))
     ((fn-dk-first-stray breaks labels)
      (list :break-names-no-hypothesis (fn-dk-first-stray breaks labels)))
     ((fn-dk-first-unbroken labels hyps breaks)
      (cons :no-breaking-value (fn-dk-first-unbroken labels hyps breaks)))
     ((null (assoc-keyword :mutations kvs)) (list :no-mutation name))
     ((not (or (fn-dk-exemptionp mutations) (fn-dk-mutationsp mutations)))
      (list :bad-mutations mutations))
     ((not (no-duplicatesp-eq (strip-cars (fn-dk-mutation-entries mutations))))
      (list :duplicate-mutation (strip-cars (fn-dk-mutation-entries mutations))))
     ((fn-dk-first-bad-edit (fn-dk-mutation-entries mutations) claim)
      (cons :bad-edit (fn-dk-first-bad-edit (fn-dk-mutation-entries mutations) claim)))
     ((not (fn-dk-corruptsp (fn-dk-get :corrupt kvs)))
      (list :bad-corrupt (fn-dk-get :corrupt kvs)))
     ((not (fn-dk-boundsp visits)) (list :bad-bound visits))
     ((not (no-duplicatesp-eq (strip-cars visits)))
      (list :duplicate-bound (strip-cars visits)))
     ((not (fn-dk-boundsp allocation)) (list :bad-bound allocation))
     ((not (no-duplicatesp-eq (strip-cars allocation)))
      (list :duplicate-bound (strip-cars allocation)))
     ((and (or visits allocation) (not (assoc-keyword :subject kvs)))
      (list :bound-without-subject name))
     ((not (member-eq (fn-dk-get :must-fail kvs) '(t nil)))
      (list :bad-must-fail (fn-dk-get :must-fail kvs)))
     (t nil))))

(defun fn-teeth-refusal (name kvs)
  (declare (xargs :mode :program))
  ; the world-free refusal of (defteeth NAME . KVS)
  (cond ((not (and (symbolp name) name)) (list :bad-name name))
        (t (fn-dk-spec-refusal name kvs *fn-dk-spec-keys*))))

(defun fn-dk-refusal (name term kvs)
  (declare (xargs :mode :program))
  ; defkeystone: the form's own checks, then the SPEC's over the derived claim
  (cond
   ((not (and (symbolp name) name)) (list :bad-name name))
   ((not (keyword-value-listp kvs)) (list :bad-options kvs))
   ((fn-dk-unknown-keys-of kvs *fn-dk-keys*)
    (cons :unknown-keyword (fn-dk-unknown-keys-of kvs *fn-dk-keys*)))
   ((assoc-keyword :claim kvs) (list :claim-is-the-term name))
   ((not (and (fn-dk-get :subject kvs) (symbolp (fn-dk-get :subject kvs))))
    (list :no-subject name))
   ((let ((labels (fn-dk-get :hyps kvs)))
      (and (assoc-keyword :hyps kvs)
           (not (and (symbol-listp labels) (no-duplicatesp-eq labels)
                     (equal (len labels) (len (fn-dk-source-hyps term)))))))
    (list :bad-labels (fn-dk-get :hyps kvs) (len (fn-dk-source-hyps term))))
   (t (fn-dk-spec-refusal name
                          (list* :claim (fn-dk-claim-of name term kvs) kvs)
                          *fn-dk-keys*))))

; ---------------------------------------------------------------------------
; The events.

(defun fn-dk-override (base over)
  (declare (xargs :mode :program))
  ; BASE's bindings with OVER's values where OVER binds the same variable,
  ; then OVER's other bindings, in order
  (cond ((atom base) over)
        ((assoc-eq (car (car base)) over)
         (cons (assoc-eq (car (car base)) over)
               (fn-dk-override (cdr base)
                               (remove1-assoc-eq (car (car base)) over))))
        (t (cons (car base) (fn-dk-override (cdr base) over)))))

(defun fn-dk-at (bindings term)
  (declare (xargs :mode :program))
  `(let* ,bindings (declare (ignorable ,@(strip-cars bindings))) ,term))

(defun fn-dk-all-at (bindings terms)
  (declare (xargs :mode :program))
  (if (atom terms)
      nil
    (cons (fn-dk-at bindings (car terms))
          (fn-dk-all-at bindings (cdr terms)))))

(defun fn-dk-without (i hyps)
  (declare (xargs :mode :program))
  ; HYPS less its I-th (0-based) element
  (if (zp i)
      (cdr hyps)
    (cons (car hyps) (fn-dk-without (1- i) (cdr hyps)))))

(defun fn-dk-with (i x hyps)
  (declare (xargs :mode :program))
  ; HYPS with X for its I-th element
  (if (zp i)
      (cons x (cdr hyps))
    (cons (car hyps) (fn-dk-with (1- i) x (cdr hyps)))))

(defun fn-dk-hint-args (kvs)
  (declare (xargs :mode :program))
  (if (assoc-keyword :hints kvs) (list :hints (fn-dk-get :hints kvs)) nil))

(defun fn-dk-label-msg (name words)
  (declare (xargs :mode :program))
  (concatenate 'string (symbol-name name) ": " words))

(defun fn-dk-witness-event (name msg bindings terms opts)
  (declare (xargs :mode :program))
  ; the assert-event of TERMS at BINDINGS, logical under :logical, or the
  ; lemma check under :lemma (fn-dk-lemma-check, resolved in the world)
  (let ((claim (fn-dk-conj terms))
        (lemma (fn-dk-get :lemma opts)))
    (cond (lemma `(fn-dk-lemma-check ,name ,lemma ,bindings ,claim ,msg))
          ((assoc-keyword :logical opts)
           `(assert-event (with-guard-checking :none ,(fn-dk-at bindings claim))
                          :msg ,(fn-dk-label-msg
                                 name (concatenate 'string msg " (logical: "
                                                   (fn-dk-get :logical opts) ")"))))
          (t `(assert-event ,(fn-dk-at bindings claim) :msg ,(fn-dk-label-msg name msg))))))

(defun fn-dk-removals (name i labels hyps concl witness breaks hint-args must-fail)
  (declare (xargs :mode :program))
  ; LABELS is the tail from the I-th hypothesis on; HYPS is all of them
  (if (atom labels)
      nil
    (let* ((entry (assoc-eq (car labels) breaks))
           (b (fn-dk-override witness (cadr entry)))
           (retained (fn-dk-without i hyps)))
      (append
       (list (fn-dk-witness-event
              name (concatenate 'string "without " (symbol-name (car labels)))
              b (append retained (list `(not ,(nth i hyps)) `(not ,concl)))
              (cddr entry)))
       (and must-fail
            `((local (must-fail-checked
                      (defthm ,(packn-pos (list name '-without- (car labels)) name)
                        ,(fn-dk-implies retained concl)
                        ,@hint-args)))))
       (fn-dk-removals name (1+ i) (cdr labels) hyps concl witness
                       breaks hint-args must-fail)))))

(defun fn-dk-mutant-statement (claim edit)
  (declare (xargs :mode :program))
  (let ((hyps (fn-dk-claim-hyps claim))
        (concl (fn-dk-claim-concl claim)))
    (if (eq (car edit) :conclusion)
        (fn-dk-implies hyps (cadr edit))
      (fn-dk-implies (fn-dk-with (position-eq (cadr edit) (fn-dk-claim-labels claim))
                                 (caddr edit) hyps)
                     concl))))

(defun fn-dk-mutant-witness-terms (claim edit)
  (declare (xargs :mode :program))
  ; every Hi, C, and the failure of the edited part
  (let ((hyps (fn-dk-claim-hyps claim))
        (concl (fn-dk-claim-concl claim)))
    (if (eq (car edit) :conclusion)
        (append hyps (list concl `(not ,(cadr edit))))
      (append (fn-dk-without (position-eq (cadr edit) (fn-dk-claim-labels claim)) hyps)
              (list (caddr edit) `(not ,concl))))))

(defun fn-dk-mutants (name claim witness mutations hint-args must-fail)
  (declare (xargs :mode :program))
  (if (atom mutations)
      nil
    (let* ((m (car mutations))
           (b (fn-dk-override witness (caddr m))))
      (append
       (list (fn-dk-witness-event
              name (concatenate 'string "mutant " (symbol-name (car m)))
              b (fn-dk-mutant-witness-terms claim (cadr m)) (cdddr m)))
       (and must-fail
            `((local (must-fail-checked
                      (defthm ,(packn-pos (list name '-mutant- (car m)) name)
                        ,(fn-dk-mutant-statement claim (cadr m))
                        ,@hint-args)))))
       (fn-dk-mutants name claim witness (cdr mutations) hint-args must-fail)))))

(defun fn-dk-corrupts (name hyps concl witness corrupts)
  (declare (xargs :mode :program))
  (if (atom corrupts)
      nil
    (let ((b (fn-dk-override witness (cadr (car corrupts)))))
      (cons `(assert-event
              (with-guard-checking :none
                ,(fn-dk-at b `(and (not ,(fn-dk-conj hyps)) (not ,concl))))
              :msg ,(fn-dk-label-msg
                     name (concatenate 'string "corrupt "
                                       (symbol-name (car (car corrupts))))))
            (fn-dk-corrupts name hyps concl witness (cdr corrupts))))))

(defun fn-dk-bound-events (name kind hyps witness entries)
  (declare (xargs :mode :program))
  ; per bound (L V B . OPTS) of KIND: the cost theorem, its witness, and
  ; the state that attains it
  (if (atom entries)
      nil
    (let* ((entry (car entries))
           (label (car entry))
           (v (cadr entry))
           (bound (caddr entry))
           (opts (cdddr entry))
           (attains (assoc-keyword :attains opts))
           (hint-args (fn-dk-hint-args opts))
           (word (string-downcase (symbol-name kind))))
      (append
       `((defthm ,(packn-pos (list name (cdr (assoc-eq kind *fn-dk-bound-kinds*)) label)
                             name)
           ,(fn-dk-implies hyps `(<= ,v ,bound))
           ,@hint-args))
       (list (fn-dk-witness-event
              name (concatenate 'string word " " (symbol-name label))
              witness (append hyps (list `(<= ,v ,bound)))
              (and (assoc-keyword :lemma opts) (list :lemma (fn-dk-get :lemma opts)))))
       (and attains
            (list (fn-dk-witness-event
                   name (concatenate 'string "attains " (symbol-name label))
                   (fn-dk-override witness (cadr attains))
                   (append hyps (list `(equal ,v ,bound)))
                   nil)))
       (fn-dk-bound-events name kind hyps witness (cdr entries))))))

(defun fn-dk-bound-rows (entries)
  (declare (xargs :mode :program))
  ; (L V B :attains|:not-attained :rests-on (A ...)) per entry
  (if (atom entries)
      nil
    (let ((opts (cdddr (car entries))))
      (cons (list (car (car entries)) (cadr (car entries)) (caddr (car entries))
                  (if (assoc-keyword :attains opts) :attains :not-attained)
                  :rests-on (fn-dk-get :rests-on opts))
            (fn-dk-bound-rows (cdr entries))))))

(defun fn-dk-removal-rows (labels breaks)
  (declare (xargs :mode :program))
  (if (atom labels)
      nil
    (cons (list (car labels)
                (if (assoc-keyword :logical (cddr (assoc-eq (car labels) breaks)))
                    :logical
                  :reachable))
          (fn-dk-removal-rows (cdr labels) breaks))))

(defun fn-dk-mutation-rows (mutations)
  (declare (xargs :mode :program))
  (if (atom mutations)
      nil
    (cons (list (car (car mutations)) (car (cadr (car mutations))))
          (fn-dk-mutation-rows (cdr mutations)))))

(defun fn-dk-row (name by claim formula kvs)
  (declare (xargs :mode :program))
  ; the fn-teeth row: the claim, the world's formula, labels and kinds; never
  ; a binding
  (let ((mutations (fn-dk-get :mutations kvs)))
    `(table fn-teeth ',name
            '(:by ,by
              :claim ,claim
              :formula ,formula
              :subject ,(fn-dk-get :subject kvs)
              :hyps ,(fn-dk-claim-labels claim)
              :removals ,(fn-dk-removal-rows (fn-dk-claim-labels claim) (fn-dk-get :breaks kvs))
              :mutations ,(if (fn-dk-exemptionp mutations)
                              (car mutations)
                            (fn-dk-mutation-rows mutations))
              :corrupt ,(strip-cars (fn-dk-get :corrupt kvs))
              :visits ,(fn-dk-bound-rows (fn-dk-get :visits kvs))
              :allocation ,(fn-dk-bound-rows (fn-dk-get :allocation kvs))))))

(defun fn-dk-teeth-events (name by claim formula kvs)
  (declare (xargs :mode :program))
  ; the teeth of NAME for a well-formed SPEC KVS over CLAIM; FORMULA is the
  ; world's theorem (nil in the static mirror's reading); BY names the macro
  (let* ((hyps (fn-dk-claim-hyps claim))
         (concl (fn-dk-claim-concl claim))
         (labels (fn-dk-claim-labels claim))
         (witness (fn-dk-get :witness kvs))
         (hint-args (fn-dk-hint-args kvs))
         (must-fail (fn-dk-get :must-fail kvs)))
    (append
     (list (fn-dk-witness-event name "witness" witness (append hyps (list concl))
                                (and (assoc-keyword :witness-lemma kvs)
                                     (list :lemma (fn-dk-get :witness-lemma kvs)))))
     (fn-dk-removals name 0 labels hyps concl witness (fn-dk-get :breaks kvs)
                     hint-args must-fail)
     (fn-dk-mutants name claim witness (fn-dk-mutation-entries (fn-dk-get :mutations kvs))
                    hint-args must-fail)
     (fn-dk-corrupts name hyps concl witness (fn-dk-get :corrupt kvs))
     (fn-dk-bound-events name :visits hyps witness (fn-dk-get :visits kvs))
     (fn-dk-bound-events name :allocation hyps witness (fn-dk-get :allocation kvs))
     (list (fn-dk-row name by claim formula kvs)))))

(defun fn-dk-refusal-text (reason)
  (declare (xargs :mode :program))
  (case (car reason)
    (:no-claim (msg "~x0 has no :claim (((LABEL HYP) ...) CONCLUSION): the teeth ~
                     are bound to the declared statement." (cadr reason)))
    (:bad-claim (msg ":claim ~x0 is not (((LABEL HYP) ...) CONCLUSION) with distinct ~
                      labels." (cadr reason)))
    (:claim-is-the-term (msg "~x0: defkeystone derives the claim from its TERM; ~
                              drop :claim (use :hyps for labels)." (cadr reason)))
    (:claim-differs (msg "~x0: the declared claim ~x1 translates to ~x2, but the ~
                          theorem in this world is ~x3: the teeth are bound to the ~
                          literal theorem." (cadr reason) (caddr reason)
                         (cadddr reason) (car (cddddr reason))))
    (:no-breaking-value
     (msg "hypothesis ~x0, ~x1, has no breaking value in :breaks.  A keystone ~
           ships a removal witness per hypothesis (AGENTS.md): give (~x0 ((VAR ~
           VAL) ...)) at which the other hypotheses hold and this one and the ~
           conclusion fail."
          (cadr reason) (caddr reason)))
    (:no-witness (msg "~x0 has no :witness ((VAR VAL) ...): a keystone with no ~
                       reachable positive witness is refused."
                      (cadr reason)))
    (:no-subject (msg "~x0 has no :subject: name the function the host calls."
                      (cadr reason)))
    (:bound-without-subject
     (msg "~x0 states a visit or allocation bound and no :subject: a cost claim ~
           names the host-called function it is about." (cadr reason)))
    (:no-mutation (msg "~x0 names no :mutations: give a checked edit of the ~
                        statement, ((LABEL (:conclusion C2) | (:hypothesis Li H2) ~
                        ((VAR VAL) ...)) ...), or say :mutations (:not-applicable ~
                        \"why\") or (:deferred \"why\") so the row records it."
                       (cadr reason)))
    (:bad-edit (msg "mutation ~x0 is no edit of the statement (~x1): a mutant is ~
                     a false neighbour, never the claim itself or a constant."
                    (cadr reason) (caddr reason)))
    (:break-names-no-hypothesis
     (msg ":breaks names ~x0, which labels no hypothesis." (cadr reason)))
    (:bad-bound (msg "a bound ~x0 is not ((LABEL VISITS BOUND :attains ((VAR VAL) ~
                      ...) | :not-attained \"why\" [:rests-on (A ...)] [:hints ...]) ~
                      ...)." (cadr reason)))
    (:not-a-theorem (msg "~x0 is not a theorem in this world: defteeth names an ~
                          admitted theorem." (cadr reason)))
    (:lemma-differs (msg "~x0: the witness lemma ~x1 states ~x2, not the instantiated ~
                          claim ~x3." (cadr reason) (caddr reason) (cadddr reason)
                         (car (cddddr reason))))
    (:declared-twice (msg "~x0 already has teeth in this world (table fn-teeth); ~
                           teeth are declared once." (cadr reason)))
    (:unknown-keyword (msg "unknown keyword(s) ~&0; the keywords are ~&1."
                           (cdr reason) *fn-dk-keys*))
    (otherwise (msg "malformed form: ~x0." reason))))

; ---------------------------------------------------------------------------
; Binding to the world, when the form runs.

(defun fn-dt-translate (x w)
  (declare (xargs :mode :program))
  ; (mv BAD TERM): the translation of X in W, or BAD = (X)
  (mv-let (erp val)
    (translate-cmp x t t t 'defteeth w (default-state-vars nil))
    (if erp (mv (list x) nil) (mv nil val))))

(mutual-recursion
 (defun fn-dt-subst (term alist)
   (declare (xargs :mode :program))
   (cond ((atom term)
          (let ((b (assoc-eq term alist))) (if b (cdr b) term)))
         ((eq (car term) 'quote) term)
         (t (cons (car term) (fn-dt-subst-lst (cdr term) alist)))))
 (defun fn-dt-subst-lst (terms alist)
   (declare (xargs :mode :program))
   (if (atom terms)
       nil
     (cons (fn-dt-subst (car terms) alist) (fn-dt-subst-lst (cdr terms) alist)))))

(defun fn-dt-bindings-alist (bindings w)
  (declare (xargs :mode :program))
  ; (mv BAD ALIST): each VAR to its translated VAL
  (if (atom bindings)
      (mv nil nil)
    (mv-let (bad val)
      (fn-dt-translate (cadr (car bindings)) w)
      (if bad
          (mv bad nil)
        (mv-let (bad rest)
          (fn-dt-bindings-alist (cdr bindings) w)
          (mv bad (acons (car (car bindings)) val rest)))))))

(defun fn-dt-lemma-problem (name lemma bindings claim w)
  (declare (xargs :mode :program))
  ; nil, or the refusal: LEMMA's formula is not CLAIM translated and
  ; instantiated at BINDINGS
  (mv-let (bad term)
    (fn-dt-translate claim w)
    (mv-let (badb alist)
      (fn-dt-bindings-alist bindings w)
      (cond ((or bad badb) (list :bad-term name (car (or bad badb))))
            ((null (getpropc lemma 'theorem nil w)) (list :not-a-theorem lemma))
            ((not (equal (getpropc lemma 'theorem nil w) (fn-dt-subst term alist)))
             (list :lemma-differs name lemma (getpropc lemma 'theorem nil w)
                   (fn-dt-subst term alist)))
            (t nil)))))

; A witness entry's `:lemma THM': checked when the event runs, as the
; evaluated witnesses are.
(defmacro fn-dk-lemma-check (name lemma bindings claim msg)
  `(make-event
    (let ((problem (fn-dt-lemma-problem ',name ',lemma ',bindings ',claim (w state))))
      (if problem
          (er soft 'defteeth "~x0 (~s1): ~@2" ',name ,msg (fn-dk-refusal-text problem))
        (value '(value-triple ',(packn-pos (list name '- lemma) name)))))))

(defun fn-dt-world-problem (name claim w)
  (declare (xargs :mode :program))
  ; nil, or the refusal the world decides: NAME is a theorem whose formula is
  ; the translated CLAIM, and has no teeth yet
  (mv-let (bad term)
    (fn-dt-translate (fn-dk-statement claim) w)
    (cond ((null (getpropc name 'theorem nil w)) (list :not-a-theorem name))
          ((assoc-eq name (table-alist 'fn-teeth w)) (list :declared-twice name))
          (bad (list :bad-term name (car bad)))
          ((not (equal term (getpropc name 'theorem nil w)))
           (list :claim-differs name (fn-dk-statement claim) term
                 (getpropc name 'theorem nil w)))
          (t nil))))

(defun fn-dt-expand (name by kvs state)
  (declare (xargs :mode :program :stobjs state))
  ; the event list of (defteeth NAME . KVS) in the current world, or a soft error
  (let* ((w (w state))
         (claim (fn-dk-get :claim kvs))
         (problem (fn-dt-world-problem name claim w)))
    (if problem
        (er soft by "~x0: ~@1" name (fn-dk-refusal-text problem))
      (value (cons 'progn (fn-dk-teeth-events name by claim
                                              (getpropc name 'theorem nil w) kvs))))))

(defun fn-teeth-form (name kvs)
  (declare (xargs :mode :program))
  ; the make-event a generator splices after NAME's defthm
  `(make-event (fn-dt-expand ',name 'defteeth ',kvs state)))

(defmacro defteeth (name &rest kvs)
  ; A refusal is a SOFT error event, so it fails like any refused event (and
  ; under must-fail prints nothing a certification log reads as a failure).
  (let ((reason (fn-teeth-refusal name kvs)))
    (if reason
        `(make-event (er soft 'defteeth "~x0: ~@1" ',name
                         ',(fn-dk-refusal-text reason)))
      (fn-teeth-form name kvs))))

(defun fn-dk-spec-of (name term kvs)
  (declare (xargs :mode :program))
  ; the defteeth SPEC a defkeystone form stands for
  (list* :claim (fn-dk-claim-of name term kvs)
         (fn-dk-unknown-keys-of kvs '(:id :restates :hyps :rule-classes :otf-flg))))

(defun fn-dk-expand (form)
  (declare (xargs :mode :program))
  ; FORM is the whole (defkeystone NAME TERM . KVS); the events it stands for:
  ; the defthm, the restates check, then the teeth bound to the world
  (let* ((name (cadr form))
         (term (caddr form))
         (kvs (cdddr form))
         (restates (fn-dk-get :restates kvs)))
    `(progn
       (defthm ,name ,term
         ,@(fn-dk-hint-args kvs)
         ,@(if (assoc-keyword :rule-classes kvs)
               (list :rule-classes (fn-dk-get :rule-classes kvs))
             nil)
         ,@(if (assoc-keyword :otf-flg kvs)
               (list :otf-flg (fn-dk-get :otf-flg kvs))
             nil))
       ,@(if restates
             `((assert-event
                (equal (getpropc ',name 'theorem nil (w state))
                       (getpropc ',restates 'theorem nil (w state)))
                :msg ,(fn-dk-label-msg name "restates")))
           nil)
       (make-event (fn-dt-expand ',name 'defkeystone ',(fn-dk-spec-of name term kvs) state)))))

(defmacro defkeystone (&whole form name term &rest kvs)
  (let ((reason (fn-dk-refusal name term kvs)))
    (if reason
        `(make-event (er soft 'defkeystone "~x0: ~@1" ',name
                         ',(fn-dk-refusal-text reason)))
      (fn-dk-expand form))))

; ---------------------------------------------------------------------------
; A generator's debt and its check.
; (table fn-teeth-owed 'NAME '(:by MACRO :claim CLAIM [:subject FN]
;   [:visits ((V B [:rests-on (A ...)]) ...)] [:allocation (...)]))

(defun fn-dk-unknown-keys (kvs)
  (declare (xargs :mode :program))
  (fn-dk-unknown-keys-of kvs *fn-dk-keys*))

(defun fn-dt-bound-statedp (owed rows)
  (declare (xargs :mode :program))
  ; OWED = (V B [:rests-on (A ...)]) is among the declared ROWS
  ; (L V B :attains|:not-attained :rests-on (A ...))
  (cond ((atom rows) nil)
        ((and (equal (cadr (car rows)) (car owed))
              (equal (caddr (car rows)) (cadr owed))
              (set-equalp-equal (fn-dk-get :rests-on (cddddr (car rows)))
                                (fn-dk-get :rests-on (cddr owed))))
         t)
        (t (fn-dt-bound-statedp owed (cdr rows)))))

(defun fn-dt-first-unstated (owed rows)
  (declare (xargs :mode :program))
  (cond ((atom owed) nil)
        ((fn-dt-bound-statedp (car owed) rows) (fn-dt-first-unstated (cdr owed) rows))
        (t (car owed))))

(defun fn-dt-owed-problem (owed teeth w)
  (declare (xargs :mode :program))
  ; nil, or a msg for the first owed keystone whose teeth are missing, state
  ; another claim or subject, omit a bound, or no longer match the world
  (if (atom owed)
      nil
    (let* ((name (car (car owed)))
           (debt (cdr (car owed)))
           (row (cdr (assoc-eq name teeth)))
           (by (fn-dk-get :by debt)))
      (cond ((null row)
             (msg "~x0 (admitted by ~x1) has no teeth in this world: (defteeth ~x0 ~
                   ...) is owed" name by))
            ((not (equal (fn-dk-get :claim row) (fn-dk-get :claim debt)))
             (msg "~x0's teeth state the claim ~x1, not the one ~x2 owes, ~x3"
                  name (fn-dk-get :claim row) by (fn-dk-get :claim debt)))
            ((and (assoc-keyword :subject debt)
                  (not (eq (fn-dk-get :subject row) (fn-dk-get :subject debt))))
             (msg "~x0's teeth name the subject ~x1, not ~x2 as ~x3 owes"
                  name (fn-dk-get :subject row) (fn-dk-get :subject debt) by))
            ((fn-dt-first-unstated (fn-dk-get :visits debt) (fn-dk-get :visits row))
             (msg "~x0's teeth do not state the visit bound ~x1 (owed by ~x2) with ~
                   the same terms and the same :rests-on facts"
                  name (fn-dt-first-unstated (fn-dk-get :visits debt) (fn-dk-get :visits row))
                  by))
            ((fn-dt-first-unstated (fn-dk-get :allocation debt) (fn-dk-get :allocation row))
             (msg "~x0's teeth do not state the allocation bound ~x1 (owed by ~x2) ~
                   with the same terms and the same :rests-on facts"
                  name (fn-dt-first-unstated (fn-dk-get :allocation debt)
                                             (fn-dk-get :allocation row))
                  by))
            ((not (equal (fn-dk-get :formula row) (getpropc name 'theorem nil w)))
             (msg "~x0 was restated since its teeth were declared: the row's formula ~
                   is not this world's theorem; declare the teeth again" name))
            (t (fn-dt-owed-problem (cdr owed) teeth w))))))

(defmacro defteeth-check ()
  `(make-event
    (let ((problem (fn-dt-owed-problem (table-alist 'fn-teeth-owed (w state))
                                       (table-alist 'fn-teeth (w state))
                                       (w state))))
      (if problem
          (er soft 'defteeth-check "~@0." problem)
        (value '(value-triple :teeth-complete))))))
