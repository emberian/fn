; Teeth for books/def-carried.lisp.
;
;   1. A carried invariant over a stobj the world confirms: the row; the
;      trace theorem (fn-cdt-carried-run-carries, its statement pinned, and
;      instances of the step and run theorems at literal events); reachable
;      positive witnesses for every fixture transition (antecedent and
;      conclusion evaluated on a local stobj); the D40 row data; and the
;      `:raw-with (:carried NAME)' declaration definterface resolves from it.
;   2. One refusal per world check, each under must-fail with the check
;      asserted by its words: an invariant that is no function or not unary;
;      a transition whose theorem is missing, carries nothing (no hypothesis
;      applying the invariant), assumes the invariant of a non-variable,
;      concludes another predicate, concludes the invariant of a term that
;      merely CONTAINS the call (the reviewed hole: (fn-cdt-open (fn-cdt-bump
;      n st)) is not fn-cdt-bump's preservation), or whose pattern is wrong;
;      an establishing theorem concluding something else; a bridge with no
;      invariant hypothesis or the wrong conclusion; a bare transition (the
;      obligation owed); COMPLETENESS derived from the world: a declared
;      entry returning the stobj and unlisted, including one declared AFTER
;      the row (def-carried-check, and the :raw-with acceptance that runs
;      it); :complete-by on a stobj state; a value state without
;      :complete-by; a redeclaration; a constantly-true invariant; a
;      transition with contradictory hypotheses.
;   3. One refusal per malformed form (fn-cd-refusal).
;   4. The `:raw-with (:carried ...)' refusals: an establishing point is
;      not a transition; no such carried invariant; (:carried) and
;      (:carried N extra).

(in-package "ACL2")
(include-book "../../books/def-carried")
(include-book "../../books/definterface")
(include-book "../../books/payload-kinds") ; *fn-entry-guard-kinds*
(include-book "must-fail-checked")

(defstobj fn-cdt-st
  (fn-cdt-n :type integer :initially 0)
  (fn-cdt-log :type t :initially nil))

; The carried relation and a predicate it implies.
(defun fn-cdt-relp (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (< 0 (fn-cdt-n fn-cdt-st)))

(defun fn-cdt-nonzerop (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (not (equal (fn-cdt-n fn-cdt-st) 0)))

; The establishing point, three transitions (one answering a value), and a
; reader that returns no stobj.
(defun fn-cdt-open (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (update-fn-cdt-n 1 fn-cdt-st))

(defun fn-cdt-bump (n fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st :guard (and (natp n) (fn-cdt-relp fn-cdt-st))))
  (update-fn-cdt-n (+ n (fn-cdt-n fn-cdt-st)) fn-cdt-st))

(defun fn-cdt-note (x fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st :guard (fn-cdt-relp fn-cdt-st)))
  (let ((fn-cdt-st (update-fn-cdt-log (cons x (fn-cdt-log fn-cdt-st)) fn-cdt-st)))
    (mv x fn-cdt-st)))

(defun fn-cdt-reset (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (update-fn-cdt-n 1 fn-cdt-st))

(defun fn-cdt-peek (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (fn-cdt-n fn-cdt-st))

(defthm fn-cdt-open-establishes
  (fn-cdt-relp (fn-cdt-open fn-cdt-st)))

(defthm fn-cdt-bump-carries
  (implies (and (natp n) (fn-cdt-relp fn-cdt-st))
           (fn-cdt-relp (fn-cdt-bump n fn-cdt-st))))

(defthm fn-cdt-note-carries
  (implies (fn-cdt-relp fn-cdt-st)
           (fn-cdt-relp (mv-nth 1 (fn-cdt-note x fn-cdt-st)))))

(defthm fn-cdt-reset-carries
  (implies (fn-cdt-relp fn-cdt-st)
           (fn-cdt-relp (fn-cdt-reset fn-cdt-st))))

(defthm fn-cdt-relp-nonzero
  (implies (fn-cdt-relp fn-cdt-st)
           (fn-cdt-nonzerop fn-cdt-st)))

(defthm fn-cdt-unrelated
  (equal (len (list x)) 1))

; Carries, but not from a state to the state the transition returns.
(defthm fn-cdt-bump-carries-shifted
  (implies (and (natp n) (fn-cdt-relp fn-cdt-st))
           (fn-cdt-relp (fn-cdt-bump (+ 1 n) fn-cdt-st))))

; The reviewed hole: the invariant of a term that merely contains the call.
(defthm fn-cdt-open-of-bump
  (implies (fn-cdt-relp fn-cdt-st)
           (fn-cdt-relp (fn-cdt-open (fn-cdt-bump n fn-cdt-st)))))

; Assumes the invariant of a projection, not of a variable.
(defthm fn-cdt-bump-of-open
  (implies (fn-cdt-relp (fn-cdt-open fn-cdt-st))
           (fn-cdt-relp (fn-cdt-bump 0 (fn-cdt-open fn-cdt-st)))))

; Contradictory hypotheses.
(defthm fn-cdt-bump-contradictory
  (implies (and (natp n) (not (natp n)) (fn-cdt-relp fn-cdt-st))
           (fn-cdt-relp (fn-cdt-bump n fn-cdt-st))))

; A constantly-true relation.
(defun fn-cdt-truep (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (or (fn-cdt-relp fn-cdt-st) t))

(defthm fn-cdt-open-establishes-truep
  (fn-cdt-truep (fn-cdt-open fn-cdt-st)))

(defthm fn-cdt-bump-carries-truep
  (implies (fn-cdt-truep fn-cdt-st)
           (fn-cdt-truep (fn-cdt-bump n fn-cdt-st)))
  :rule-classes nil)
(defthm fn-cdt-note-carries-truep
  (implies (fn-cdt-truep fn-cdt-st)
           (fn-cdt-truep (mv-nth 1 (fn-cdt-note x fn-cdt-st))))
  :rule-classes nil)
(defthm fn-cdt-reset-carries-truep
  (implies (fn-cdt-truep fn-cdt-st)
           (fn-cdt-truep (fn-cdt-reset fn-cdt-st)))
  :rule-classes nil)

; The host-called entries, declared (completeness reads this table).
(definterface fn-cdt-open :class :common-lisp-compliant)
(definterface fn-cdt-bump :class :common-lisp-compliant :kinds ((n natp)))
(definterface fn-cdt-note :class :common-lisp-compliant)
(definterface fn-cdt-reset :class :common-lisp-compliant)
(definterface fn-cdt-peek :class :common-lisp-compliant)

; The entries returning the stobj, derived; the reader is not among them.
(assert-event
 (equal (fn-cd-returning-entries (table-alist 'fn-interfaces (w state))
                                 'fn-cdt-st (w state))
        '(fn-cdt-reset fn-cdt-note fn-cdt-bump fn-cdt-open)))
(assert-event (eq (fn-cd-state-stobj 'fn-cdt-relp (w state)) 'fn-cdt-st))

; ---------------------------------------------------------------------------
; 3. Malformed forms.

(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes)) :bogus 1)
 :unchecked "def-carried refuses an unknown keyword at expansion")
(must-fail-checked
 (def-carried fn-cdt-x :established ((fn-cdt-open fn-cdt-open-establishes)))
 :unchecked "def-carried refuses a form with no :invariant")
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp)
 :unchecked "def-carried refuses a form with no establishing point")
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump)))
 :unchecked "def-carried refuses a transition entry that is neither FN nor (FN THM [PATTERN])")
(assert-event
 (equal (fn-cd-refusal 'fn-cdt-x '(:invariant fn-cdt-relp
                                   :established ((fn-cdt-open fn-cdt-open-establishes))
                                   :trace :maybe))
        '(:bad-trace :maybe)))
(assert-event
 (equal (fn-cd-refusal 'fn-cdt-x '(:invariant fn-cdt-relp
                                   :established ((fn-cdt-open fn-cdt-open-establishes))
                                   :complete-by (:enumeration)))
        '(:bad-complete-by (:enumeration))))
(assert-event
 (equal (fn-cd-refusal 'fn-cdt-x '(:invariant fn-cdt-relp
                                   :established ((fn-cdt-open fn-cdt-open-establishes))
                                   :concludes (fn-cdt-nonzerop)))
        '(:bad-concludes (fn-cdt-nonzerop))))

; ---------------------------------------------------------------------------
; 2. World refusals.  Each: the problem asserted by the check's words, then
; the form under must-fail.  WORDS is searched in the msg's raw format
; string (a `~'-newline continuation is not joined there), so a phrase
; never straddles one.

(defmacro fn-cdt-problem-says (words kvs)
  `(assert-event
    (let ((problem (fn-cd-problem 'fn-cdt-x ',kvs (w state))))
      (and problem (search ,words (car problem)) t))))

(fn-cdt-problem-says "is not a function in this world"
 (:invariant fn-cdt-nope :established ((fn-cdt-open fn-cdt-open-establishes))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-nope
   :established ((fn-cdt-open fn-cdt-open-establishes)))
 :unchecked "the invariant is no function")

(fn-cdt-problem-says "of one formal"
 (:invariant fn-cdt-bump :established ((fn-cdt-open fn-cdt-open-establishes))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-bump
   :established ((fn-cdt-open fn-cdt-open-establishes)))
 :unchecked "the invariant is not unary")

(fn-cdt-problem-says "is not a theorem in this world"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-no-such-theorem))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-no-such-theorem)))
 :unchecked "the transition's theorem is not in the world")

(fn-cdt-problem-says "no hypothesis applying"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-open-establishes))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-open-establishes)))
 :unchecked "an establishing theorem carries nothing across a transition")

(fn-cdt-problem-says "of exactly one"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-bump-of-open))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-bump-of-open)))
 :unchecked "the transition's theorem assumes the invariant of a projection, not a state variable")

(fn-cdt-problem-says "does not conclude"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-relp-nonzero))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-relp-nonzero)))
 :unchecked "the transition's theorem concludes another predicate")

; The reviewed hole: (fn-cdt-open (fn-cdt-bump n st)) contains the call but
; is not the state fn-cdt-bump returns.
(fn-cdt-problem-says "the state ~x0 returns"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-open-of-bump))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-open-of-bump)))
 :unchecked "a theorem about a term that merely contains the call is not its preservation")

; The theorem about another transition.
(fn-cdt-problem-says "the state ~x0 returns"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-reset-carries))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-reset-carries)))
 :unchecked "the transition's theorem is about another transition")

; A call on a non-variable argument.
(fn-cdt-problem-says "the state ~x0 returns"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-bump-carries-shifted))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-bump-carries-shifted)))
 :unchecked "the call's argument is not a variable")

; The wrong pattern: the note answers (mv x st); its state is (mv-nth 1 _).
(fn-cdt-problem-says "invalid carried-stobj PATTERN"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-note fn-cdt-note-carries))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-note fn-cdt-note-carries)))
 :unchecked "the state is (mv-nth 1 _) of the note, not the call")

(fn-cdt-problem-says "establishing point"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-unrelated))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-unrelated)))
 :unchecked "the establishing theorem concludes something else")

(fn-cdt-problem-says "must have exactly one hypothesis"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :concludes ((fn-cdt-nonzerop fn-cdt-open-establishes))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :concludes ((fn-cdt-nonzerop fn-cdt-open-establishes)))
 :unchecked "the bridge has no invariant hypothesis")

(fn-cdt-problem-says "does not conclude"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :concludes ((fn-cdt-peek fn-cdt-relp-nonzero))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :concludes ((fn-cdt-peek fn-cdt-relp-nonzero)))
 :unchecked "the bridge concludes another predicate")

; The obligation owed: a bare transition, refused with the statement.
(fn-cdt-problem-says "has no preservation theorem"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-bump-carries) fn-cdt-reset)))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-bump-carries) fn-cdt-reset))
 :unchecked "a transition with no theorem is an obligation owed")

; Completeness, derived: fn-cdt-reset returns the stobj, is declared, and
; is unlisted.  No :writers to trust.
(fn-cdt-problem-says "returns the carried state"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                (fn-cdt-note fn-cdt-note-carries (mv-nth 1 _)))))
(assert-event
 (eq (cdr (assoc #\0 (cdr (fn-cd-problem
                           'fn-cdt-x
                           '(:invariant fn-cdt-relp
                             :established ((fn-cdt-open fn-cdt-open-establishes))
                             :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                                           (fn-cdt-note fn-cdt-note-carries (mv-nth 1 _))))
                           (w state)))))
     'fn-cdt-reset))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                 (fn-cdt-note fn-cdt-note-carries (mv-nth 1 _))))
 :unchecked "a declared entry that returns the carried state and is unlisted")

; :complete-by is a claim; a stobj state refuses it.
(fn-cdt-problem-says "never claimed"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                (fn-cdt-note fn-cdt-note-carries (mv-nth 1 _))
                (fn-cdt-reset fn-cdt-reset-carries))
  :complete-by (:enumeration "no")))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                 (fn-cdt-note fn-cdt-note-carries (mv-nth 1 _))
                 (fn-cdt-reset fn-cdt-reset-carries))
   :complete-by (:enumeration "no"))
 :unchecked ":complete-by on a stobj-typed state")

; The general must-fail-checked helper cannot translate declarations.
; This adapter runs the very event list def-carried emits, and exposes the
; first refusal as a translatable assertion.  Before running a vacuity
; event it checks the probe's theorem/hint translation with fn-mfc-check.
; A different refusal or successful admission makes the outer must-fail
; FAIL.  make-event rolls back these trial table/event updates.
(defun fn-cdt-first-event-refusal (events state)
  (declare (xargs :mode :program :stobjs state))
  (if (atom events)
      (value nil)
    (let* ((event (car events))
           (event (if (eq (car event) 'local) (cadr event) event))
           (probe (eq (car event) 'fn-cd-nonvacuous)))
      (er-progn
       (if probe
           (fn-mfc-check `(thm ,(caddr event) :hints ,(cadddr event))
                         20 'fn-cdt-first-event-refusal state)
         (value :ok))
       (mv-let (erp pair state)
         (with-output! :off :all
           (trans-eval event 'fn-cdt-first-event-refusal state t))
         (cond (erp (value :unexpected-evaluation-error))
               ((not (equal (car pair) '(nil nil state)))
                (value :unexpected-result-signature))
               ((car (cdr pair))
                (value (if probe (cadr event) :unexpected-event-refusal)))
               (t (fn-cdt-first-event-refusal (cdr events) state))))))))

(defmacro fn-cdt-vacuity-acceptance (name kvs expected)
  `(make-event
    (if (fn-cd-declaration-problem ',name ',kvs (w state))
        (er soft 'fn-cdt-vacuity-acceptance
            "the complete declaration must pass all ordinary world checks")
      (er-let* ((reason
                 (fn-cdt-first-event-refusal
                  (cdr (fn-cd-events ',name ',kvs (w state))) state)))
        (value `(assert-event ,(not (equal reason ,expected))
                             :msg ,,expected))))))

; Complete constant-T declaration: no omission can mask the intended guard.
(must-fail-checked
 (fn-cdt-vacuity-acceptance fn-cdt-true-carried
  (:invariant fn-cdt-truep
   :established ((fn-cdt-open fn-cdt-open-establishes-truep))
   :transitions ((fn-cdt-bump fn-cdt-bump-carries-truep)
                 (fn-cdt-note fn-cdt-note-carries-truep (mv-nth 1 _))
                 (fn-cdt-reset fn-cdt-reset-carries-truep))
   :trace nil)
  "the carried invariant is provably always true"))

; Complete contradictory-hypothesis declaration; trace generation is off
; so deleting the contradiction guard would admit the whole declaration.
(must-fail-checked
 (fn-cdt-vacuity-acceptance fn-cdt-contradictory-carried
  (:invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-bump-contradictory)
                 (fn-cdt-note fn-cdt-note-carries (mv-nth 1 _))
                 (fn-cdt-reset fn-cdt-reset-carries))
   :trace nil)
  "transition hypotheses are provably contradictory"))

; r08-F1: complete declarations, checked at the same world-check boundary
; def-carried uses.  These assert the diagnostic independently of failure.
(encapsulate ()
 (local
  (defun fn-cdt-break (fn-cdt-st)
    (declare (xargs :stobjs fn-cdt-st :guard (fn-cdt-relp fn-cdt-st)))
    (update-fn-cdt-n 0 fn-cdt-st)))
 (local
  (defthm fn-cdt-break-repaired
    (implies (fn-cdt-relp fn-cdt-st)
             (fn-cdt-relp (fn-cdt-open (fn-cdt-break fn-cdt-st))))))
 (local (definterface fn-cdt-break :class :common-lisp-compliant))
 (local
  (fn-cdt-problem-says "invalid carried-stobj PATTERN"
   (:invariant fn-cdt-relp
    :established ((fn-cdt-open fn-cdt-open-establishes))
    :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                  (fn-cdt-note fn-cdt-note-carries (mv-nth 1 _))
                  (fn-cdt-reset fn-cdt-reset-carries)
                  (fn-cdt-break fn-cdt-break-repaired (fn-cdt-open _))))))
 (local
  (must-fail-checked
   (assert-event
    (null (fn-cd-problem
           'fn-cdt-repaired-carried
           '(:invariant fn-cdt-relp
             :established ((fn-cdt-open fn-cdt-open-establishes))
             :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                           (fn-cdt-note fn-cdt-note-carries (mv-nth 1 _))
                           (fn-cdt-reset fn-cdt-reset-carries)
                           (fn-cdt-break fn-cdt-break-repaired (fn-cdt-open _))))
           (w state)))
    :msg "invalid carried-stobj PATTERN: fn-cdt-break (fn-cdt-open _)"))))

(fn-cdt-problem-says "invalid carried-stobj PATTERN"
 (:invariant fn-cdt-relp
  :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                (fn-cdt-note fn-cdt-note-carries (mv-nth 0 _))
                (fn-cdt-reset fn-cdt-reset-carries))))
(must-fail-checked
 (assert-event
  (null (fn-cd-problem
         'fn-cdt-wrong-output
         '(:invariant fn-cdt-relp
           :established ((fn-cdt-open fn-cdt-open-establishes))
           :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                         (fn-cdt-note fn-cdt-note-carries (mv-nth 0 _))
                         (fn-cdt-reset fn-cdt-reset-carries)))
         (w state)))
  :msg "invalid carried-stobj PATTERN: fn-cdt-note (mv-nth 0 _)"))

; Enumeration of every pattern-accepting keyword/state-kind pair.  The
; assertion negates the EXACT expected diagnostic (including FN/PATTERN),
; so an unrelated refusal or acceptance makes must-fail-checked fail.
; These are complete declarations; trace nil prevents generated-name or
; trace-proof failures from masking the pattern check.
(defmacro fn-cdt-pattern-acceptance (name kvs fn pattern stobjp)
  `(assert-event
    (not (equal
          (fn-cd-declaration-problem ',name ',kvs (w state))
          ,(if stobjp
               `(msg "~x0 has invalid carried-stobj PATTERN ~x1: use `_ only for a sole carried-stobj output, or (mv-nth K _) where ACL2's stobjs-out identifies that carried stobj at K" ',fn ',pattern)
             `(msg "~x0 has invalid carried-value PATTERN ~x1: use `_, an in-range (mv-nth K _) for multiple outputs, or (SEL _) with a defined non-recursive unary logical selector" ',fn ',pattern))))))

(encapsulate ()
 (local
  (defun fn-cdt-bad-return (fn-cdt-st)
    (declare (xargs :stobjs fn-cdt-st))
    (update-fn-cdt-n 0 fn-cdt-st)))
 (local (definterface fn-cdt-bad-return :class :common-lisp-compliant))
 (local
  (defthm fn-cdt-bad-return-established-repaired
    (fn-cdt-relp (fn-cdt-open (fn-cdt-bad-return fn-cdt-st)))))
 (local
  (defthm fn-cdt-bad-return-transition-repaired
    (implies (fn-cdt-relp fn-cdt-st)
             (fn-cdt-relp (fn-cdt-open (fn-cdt-bad-return fn-cdt-st))))))
 ; STOBJ :transitions
 (local
  (must-fail-checked
   (fn-cdt-pattern-acceptance fn-cdt-enum-st-transition
    (:invariant fn-cdt-relp
     :established ((fn-cdt-open fn-cdt-open-establishes))
     :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                   (fn-cdt-note fn-cdt-note-carries (mv-nth 1 _))
                   (fn-cdt-reset fn-cdt-reset-carries)
                   (fn-cdt-bad-return fn-cdt-bad-return-transition-repaired (fn-cdt-open _)))
     :trace nil)
    fn-cdt-bad-return (fn-cdt-open _) t)))
 ; STOBJ :established
 (local
  (must-fail-checked
   (fn-cdt-pattern-acceptance fn-cdt-enum-st-established
    (:invariant fn-cdt-relp
     :established ((fn-cdt-open fn-cdt-open-establishes)
                   (fn-cdt-bad-return fn-cdt-bad-return-established-repaired (fn-cdt-open _)))
     :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                   (fn-cdt-note fn-cdt-note-carries (mv-nth 1 _))
                   (fn-cdt-reset fn-cdt-reset-carries))
     :trace nil)
    fn-cdt-bad-return (fn-cdt-open _) t)))
 (local
  (assert-event
   (null (fn-cd-returned-call
          'fn-cdt-relp 'fn-cdt-bad-return '(fn-cdt-open _)
          '(fn-cdt-open (fn-cdt-bad-return fn-cdt-st)) (w state))))))

(encapsulate ()
 (local (defun fn-cdt-vp (s) (equal s '(1))))
 (local (defun fn-cdt-vrepair (s) (declare (ignore s)) (cons 1 nil)))
 (local (defun fn-cdt-vbad (s) (declare (ignore s)) nil))
 (local (defun fn-cdt-vselect (x) (car x)))
 (local (defun fn-cdt-vid (x) x))
 (local (defun fn-cdt-vstep (s) (list s)))
 (local (defun fn-cdt-vrecursive (x)
          (if (consp (cdr x)) (fn-cdt-vrecursive (cdr x)) (car x))))
 (local (defthm fn-cdt-vopen (fn-cdt-vp (fn-cdt-vrepair s))))
 (local (defthm fn-cdt-vbad-open
          (fn-cdt-vp (fn-cdt-vrepair (fn-cdt-vbad s)))))
 (local (defthm fn-cdt-vbad-carries
          (implies (fn-cdt-vp s)
                   (fn-cdt-vp (fn-cdt-vrepair (fn-cdt-vbad s))))))
 (local (defthm fn-cdt-vstep-carries
          (implies (fn-cdt-vp s)
                   (fn-cdt-vp (fn-cdt-vselect (fn-cdt-vstep s))))))
 (local (defthm fn-cdt-vnested-carries
          (implies (fn-cdt-vp s)
                   (fn-cdt-vp (fn-cdt-vid (fn-cdt-vid (fn-cdt-vrepair s)))))))
 (local (defthm fn-cdt-vrecursive-carries
          (implies (fn-cdt-vp s)
                   (fn-cdt-vp (fn-cdt-vrecursive (fn-cdt-vstep s))))))
 ; VALUE :transitions
 (local
  (must-fail-checked
   (fn-cdt-pattern-acceptance fn-cdt-enum-v-transition
    (:invariant fn-cdt-vp
     :established ((fn-cdt-vrepair fn-cdt-vopen))
     :transitions ((fn-cdt-vbad fn-cdt-vbad-carries (fn-cdt-vrepair _)))
     :complete-by (:enumeration "repair opens; bad is the sole transition") :trace nil)
    fn-cdt-vbad (fn-cdt-vrepair _) nil)))
 ; VALUE :established
 (local
  (must-fail-checked
   (fn-cdt-pattern-acceptance fn-cdt-enum-v-established
    (:invariant fn-cdt-vp
     :established ((fn-cdt-vbad fn-cdt-vbad-open (fn-cdt-vrepair _)))
     :transitions ((fn-cdt-vstep fn-cdt-vstep-carries (fn-cdt-vselect _)))
     :complete-by (:enumeration "bad opens; step is the sole transition") :trace nil)
    fn-cdt-vbad (fn-cdt-vrepair _) nil)))
 (local
  (must-fail-checked
   (fn-cdt-pattern-acceptance fn-cdt-enum-v-nested
    (:invariant fn-cdt-vp
     :established ((fn-cdt-vrepair fn-cdt-vopen))
     :transitions ((fn-cdt-vrepair fn-cdt-vnested-carries (fn-cdt-vid (fn-cdt-vid _))))
     :complete-by (:enumeration "repair opens and is the sole transition") :trace nil)
    fn-cdt-vrepair (fn-cdt-vid (fn-cdt-vid _)) nil)))
 (local
  (must-fail-checked
   (fn-cdt-pattern-acceptance fn-cdt-enum-v-recursive
    (:invariant fn-cdt-vp
     :established ((fn-cdt-vrepair fn-cdt-vopen))
     :transitions ((fn-cdt-vstep fn-cdt-vrecursive-carries (fn-cdt-vrecursive _)))
     :complete-by (:enumeration "repair opens; step is the sole transition") :trace nil)
    fn-cdt-vstep (fn-cdt-vrecursive _) nil)))
 ; Positive selector fixture includes generated step/run theorems.
 (local
  (def-carried fn-cdt-vcarried
    :invariant fn-cdt-vp
    :established ((fn-cdt-vrepair fn-cdt-vopen))
    :transitions ((fn-cdt-vstep fn-cdt-vstep-carries (fn-cdt-vselect _)))
    :complete-by (:enumeration "repair opens; step is the sole transition")))
 (local
  (thm
   (let ((s (fn-cdt-vrepair nil)) (e '(fn-cdt-vstep nil)))
     (and (fn-cdt-vp s) (fn-cdt-vcarried-okp s e)
          (fn-cdt-vp (fn-cdt-vcarried-step s e))
          (fn-cdt-vcarried-run-okp s (list e))
          (fn-cdt-vp (fn-cdt-vcarried-run s (list e)))))
   :hints (("Goal" :in-theory (disable fn-cdt-vcarried-step-carries
                                       fn-cdt-vcarried-run-carries)))))
 (local
  (assert-event
   (and (fn-cd-valid-pattern-p 'fn-cdt-vp 'fn-cdt-vstep '(fn-cdt-vselect _) (w state))
        (not (fn-cd-valid-pattern-p 'fn-cdt-vp 'fn-cdt-vstep '(mv-nth 0 _) (w state)))
        (null (fn-cd-returned-call 'fn-cdt-vp 'fn-cdt-vbad '(fn-cdt-vrepair _)
                                 '(fn-cdt-vrepair (fn-cdt-vbad s)) (w state))))))
 (local
  (must-fail-checked
   (assert-event
    (not (equal
          (fn-di-raw-with-problem
           'fn-cdt-vstep '(:class :common-lisp-compliant :raw-with (:carried fn-cdt-vcarried))
           (w state))
          (msg ":raw-with ~x0 on ~x1: value-state carried rows are enumerated, not world-derived, and cannot back raw dispatch"
               '(:carried fn-cdt-vcarried) 'fn-cdt-vstep)))))))

; Bridge teeth: inspect the exact declaration check def-carried executes.
; The adapter keeps the original declaration as data: def-carried's deliberate
; make-event refusal cannot pass must-fail-checked's translation preflight.
; Negating equality makes any other refusal (or acceptance) fail the tooth.
(defmacro fn-cdt-bridge-acceptance (declaration expected)
  `(assert-event
    (not (equal (or (fn-cd-refusal ',(cadr declaration) ',(cddr declaration))
                    (fn-cd-declaration-problem
                     ',(cadr declaration) ',(cddr declaration) (w state)))
                ,expected))))

(encapsulate ()
 (local
  (encapsulate ()
(defstobj r14-st (r14-n :type (integer 0 *) :initially 0))
(defun r14-r (r14-st)
  (declare (xargs :stobjs r14-st))
  (< 0 (r14-n r14-st)))
(defun r14-p (r14-st)
  (declare (xargs :stobjs r14-st))
  (equal (r14-n r14-st) 1))
(defun r14-open (r14-st)
  (declare (xargs :stobjs r14-st))
  (update-r14-n 1 r14-st))
(defun r14-break-p (r14-st)
  (declare (xargs :stobjs r14-st
                  :guard (and (r14-r r14-st) (r14-p r14-st))))
  (update-r14-n 2 r14-st))
(defthm r14-open-r (r14-r (r14-open r14-st)))
(defthm r14-break-r
  (implies (r14-r r14-st) (r14-r (r14-break-p r14-st))))
(defthm r14-repaired-bridge
  (implies (r14-r r14-st)
           (r14-p (r14-open (r14-break-p r14-st))))
  :rule-classes nil)
(definterface r14-open :class :common-lisp-compliant)
(definterface r14-break-p :class :common-lisp-compliant)
(must-fail-checked
 (fn-cdt-bridge-acceptance
 (def-carried r14-carried
  :invariant r14-r
  :established ((r14-open r14-open-r))
  :transitions ((r14-break-p r14-break-r))
  :concludes ((r14-p r14-repaired-bridge))
  :trace nil)
 (msg "bridge ~x0 calls a function returning the carried stobj ~x1: bridges must describe the same state, never a transformed state"
      'r14-repaired-bridge 'r14-st)))

; The same honest R transition has no bridge for guard head P. No bridge,
; establishing theorem, or occurrence of the entry may fill that gap.
(def-carried r14-no-bridge
  :invariant r14-r
  :established ((r14-open r14-open-r))
  :transitions ((r14-break-p r14-break-r))
  :trace nil)
(must-fail-checked
 (assert-event
  (not (equal
        (fn-di-raw-with-problem
         'r14-break-p '(:class :common-lisp-compliant
                        :raw-with (:carried r14-no-bridge)) (w state))
        (msg ":raw-with ~x0 on ~x1: guard head ~x2 has no validated bridge from the carried invariant"
             '(:carried r14-no-bridge) 'r14-break-p 'r14-p)))))

; A genuine bridge and a transition whose guard carries its consequence.
(defun r14-q (r14-st)
  (declare (xargs :stobjs r14-st))
  (not (equal (r14-n r14-st) 0)))
(defun r14-good (r14-st)
  (declare (xargs :stobjs r14-st :guard (and (r14-r r14-st) (r14-q r14-st))))
  (update-r14-n 3 r14-st))
(defthm r14-good-r
  (implies (r14-r r14-st) (r14-r (r14-good r14-st))))
(defthm r14-same-state-bridge
  (implies (r14-r r14-st) (r14-q r14-st)))
(definterface r14-good :class :common-lisp-compliant)
(def-carried r14-with-bridge
  :invariant r14-r
  :established ((r14-open r14-open-r))
  :transitions ((r14-break-p r14-break-r) (r14-good r14-good-r))
  :concludes ((r14-q r14-same-state-bridge))
  :trace nil)
(definterface r14-good :class :common-lisp-compliant
  :raw-with (:carried r14-with-bridge))
)))

(encapsulate ()
 (local
  (encapsulate ()
   (defun fn-cdt-bridge-r (x) (natp x))
   (defun fn-cdt-bridge-p (x) (integerp x))
   (defun fn-cdt-bridge-open (x) (declare (ignore x)) 0)
   (defthm fn-cdt-bridge-established
     (fn-cdt-bridge-r (fn-cdt-bridge-open x)))
   (defun fn-cdt-bridge-arg (x y) (declare (ignore y)) x)
   (defthm fn-cdt-bridge-extra-hyp
     (implies (and (fn-cdt-bridge-r x) (natp y)) (fn-cdt-bridge-p x)))
   (defthm fn-cdt-bridge-nonvariable
     (implies (fn-cdt-bridge-r (car x)) (fn-cdt-bridge-p (car x))))
   (defthm fn-cdt-bridge-extra-var
     (implies (fn-cdt-bridge-r x)
              (fn-cdt-bridge-p (fn-cdt-bridge-arg x y))))
   (defthm fn-cdt-bridge-ok
     (implies (fn-cdt-bridge-r x) (fn-cdt-bridge-p x)))
   (must-fail-checked
    (fn-cdt-bridge-acceptance
     (def-carried fn-cdt-bridge-extra-hyp-row
       :invariant fn-cdt-bridge-r
       :established ((fn-cdt-bridge-open fn-cdt-bridge-established))
       :concludes ((fn-cdt-bridge-p fn-cdt-bridge-extra-hyp))
       :complete-by (:enumeration "no transitions") :trace nil)
     (msg "bridge ~x0 must have exactly one hypothesis (~x1 x), with x a variable"
          'fn-cdt-bridge-extra-hyp 'fn-cdt-bridge-r)))
   (must-fail-checked
    (fn-cdt-bridge-acceptance
     (def-carried fn-cdt-bridge-nonvariable-row
       :invariant fn-cdt-bridge-r
       :established ((fn-cdt-bridge-open fn-cdt-bridge-established))
       :concludes ((fn-cdt-bridge-p fn-cdt-bridge-nonvariable))
       :complete-by (:enumeration "no transitions") :trace nil)
     (msg "bridge ~x0 must have exactly one hypothesis (~x1 x), with x a variable"
          'fn-cdt-bridge-nonvariable 'fn-cdt-bridge-r)))
   (must-fail-checked
    (fn-cdt-bridge-acceptance
     (def-carried fn-cdt-bridge-extra-var-row
       :invariant fn-cdt-bridge-r
       :established ((fn-cdt-bridge-open fn-cdt-bridge-established))
       :concludes ((fn-cdt-bridge-p fn-cdt-bridge-extra-var))
       :complete-by (:enumeration "no transitions") :trace nil)
     (msg "bridge ~x0's ~x1 conclusion has free variables other than the carried state variable ~x2"
          'fn-cdt-bridge-extra-var 'fn-cdt-bridge-p 'x)))
   (def-carried fn-cdt-bridge-ok-row
     :invariant fn-cdt-bridge-r
       :established ((fn-cdt-bridge-open fn-cdt-bridge-established))
     :concludes ((fn-cdt-bridge-p fn-cdt-bridge-ok))
     :complete-by (:enumeration "no transitions") :trace nil))))

; ---------------------------------------------------------------------------
; 1. Accepted.

(def-carried fn-cdt-carried
  :invariant fn-cdt-relp
  :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                (fn-cdt-note fn-cdt-note-carries (mv-nth 1 _))
                (fn-cdt-reset fn-cdt-reset-carries))
  :concludes ((fn-cdt-nonzerop fn-cdt-relp-nonzero)))

(assert-event
 (equal (cdr (assoc-eq 'fn-cdt-carried (table-alist 'fn-carried (w state))))
        '(:invariant fn-cdt-relp
          :state fn-cdt-st
          :established ((fn-cdt-open fn-cdt-open-establishes _))
          :transitions ((fn-cdt-bump fn-cdt-bump-carries _)
                        (fn-cdt-note fn-cdt-note-carries (mv-nth 1 _))
                        (fn-cdt-reset fn-cdt-reset-carries _))
          :concludes ((fn-cdt-nonzerop fn-cdt-relp-nonzero))
          :complete-by nil
          :trace t)))

; A complete redeclaration with :trace nil has no generated-name collision
; to mask deletion of the freshness guard.  Check its specific diagnostic
; at the exact declaration checker used by def-carried.
(assert-event
 (let ((problem
        (fn-cd-declaration-problem
         'fn-cdt-carried
         '(:invariant fn-cdt-relp
           :established ((fn-cdt-open fn-cdt-open-establishes))
           :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                         (fn-cdt-note fn-cdt-note-carries (mv-nth 1 _))
                         (fn-cdt-reset fn-cdt-reset-carries))
           :trace nil)
         (w state))))
   (and problem (search "a row is declared once" (car problem)) t)))
(must-fail-checked
 (assert-event
  (null (fn-cd-declaration-problem
         'fn-cdt-carried
         '(:invariant fn-cdt-relp
           :established ((fn-cdt-open fn-cdt-open-establishes))
           :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                         (fn-cdt-note fn-cdt-note-carries (mv-nth 1 _))
                         (fn-cdt-reset fn-cdt-reset-carries))
           :trace nil)
         (w state)))
  :msg "a row is declared once"))

; The trace theorem, its statement pinned.
(assert-event
 (equal (getpropc 'fn-cdt-carried-run-carries 'theorem nil (w state))
        '(implies (if (fn-cdt-relp s) (fn-cdt-carried-run-okp s es) 'nil)
                  (fn-cdt-relp (fn-cdt-carried-run s es)))))

; Instances of the step and run theorems at literal events: bump by 3; then
; bump by 3, note x, reset.
(defthm fn-cdt-step-witness
  (implies (fn-cdt-relp s)
           (fn-cdt-relp (fn-cdt-carried-step s '(fn-cdt-bump 3))))
  :hints (("Goal" :use ((:instance fn-cdt-carried-step-carries (e '(fn-cdt-bump 3))))
           :in-theory (e/d (fn-cdt-carried-okp)
                           (fn-cdt-carried-step-carries fn-cdt-carried-step)))))

(defthm fn-cdt-trace-witness
  (implies (fn-cdt-relp s)
           (fn-cdt-relp (fn-cdt-carried-run
                         s '((fn-cdt-bump 3) (fn-cdt-note x) (fn-cdt-reset)))))
  :hints (("Goal" :use ((:instance fn-cdt-carried-run-carries
                                   (es '((fn-cdt-bump 3) (fn-cdt-note x) (fn-cdt-reset)))))
           :in-theory (e/d (fn-cdt-carried-run-okp fn-cdt-carried-okp)
                           (fn-cdt-carried-run-carries fn-cdt-carried-run)))))

; Reachable positive witnesses, evaluated: from the open, each transition's
; antecedent holds and its conclusion holds after it.
(defun fn-cdt-witness-bump ()
  (declare (xargs :guard t))
  (with-local-stobj fn-cdt-st
    (mv-let (ok fn-cdt-st)
      (let* ((fn-cdt-st (fn-cdt-open fn-cdt-st))
             (before (and (natp 3) (fn-cdt-relp fn-cdt-st)))
             (fn-cdt-st (fn-cdt-bump 3 fn-cdt-st)))
        (mv (and before (fn-cdt-relp fn-cdt-st)) fn-cdt-st))
      ok)))
(assert-event (fn-cdt-witness-bump) :msg "fn-cdt-bump-carries: witness")

(defun fn-cdt-witness-note ()
  (declare (xargs :guard t))
  (with-local-stobj fn-cdt-st
    (mv-let (ok fn-cdt-st)
      (let* ((fn-cdt-st (fn-cdt-open fn-cdt-st))
             (before (fn-cdt-relp fn-cdt-st)))
        (mv-let (x fn-cdt-st)
          (fn-cdt-note 'x fn-cdt-st)
          (mv (and before (eq x 'x) (fn-cdt-relp fn-cdt-st)) fn-cdt-st)))
      ok)))
(assert-event (fn-cdt-witness-note) :msg "fn-cdt-note-carries: witness")

(defun fn-cdt-witness-reset ()
  (declare (xargs :guard t))
  (with-local-stobj fn-cdt-st
    (mv-let (ok fn-cdt-st)
      (let* ((fn-cdt-st (fn-cdt-open fn-cdt-st))
             (fn-cdt-st (fn-cdt-bump 5 fn-cdt-st))
             (before (fn-cdt-relp fn-cdt-st))
             (fn-cdt-st (fn-cdt-reset fn-cdt-st)))
        (mv (and before (fn-cdt-relp fn-cdt-st)) fn-cdt-st))
      ok)))
(assert-event (fn-cdt-witness-reset) :msg "fn-cdt-reset-carries: witness")

; The D40 row data.
(assert-event
 (equal (fn-cd-raw-with 'fn-cdt-carried 'fn-cdt-bump (w state))
        '(fn-cdt-relp-nonzero fn-cdt-open-establishes fn-cdt-bump-carries)))
(assert-event (null (fn-cd-raw-with 'fn-cdt-carried 'fn-cdt-open (w state))))
(assert-event (null (fn-cd-raw-with 'fn-cdt-carried 'fn-cdt-peek (w state))))
(assert-event (null (fn-cd-raw-with 'fn-cdt-nope 'fn-cdt-bump (w state))))

(def-carried-check fn-cdt-carried)
(must-fail-checked (def-carried-check fn-cdt-nope)
                   :unchecked "no such carried invariant")

; A value-typed state: completeness cannot be derived, so the form must
; say :complete-by; with it, the row records the claim.
(defun fn-cdt-vp (x)
  (declare (xargs :guard t))
  (and (consp x) (natp (car x))))
(defun fn-cdt-vopen (n)
  (declare (xargs :guard t))
  (cons (nfix n) nil))
(defun fn-cdt-vbump (k x)
  (declare (xargs :guard (and (natp k) (fn-cdt-vp x))))
  (cons (+ k (car x)) (cdr x)))
(defthm fn-cdt-vopen-establishes (fn-cdt-vp (fn-cdt-vopen n)))
(defthm fn-cdt-vbump-carries
  (implies (and (natp k) (fn-cdt-vp x)) (fn-cdt-vp (fn-cdt-vbump k x))))
(fn-cdt-problem-says "is a value, not a stobj"
 (:invariant fn-cdt-vp :established ((fn-cdt-vopen fn-cdt-vopen-establishes))
  :transitions ((fn-cdt-vbump fn-cdt-vbump-carries))))
(must-fail-checked
 (def-carried fn-cdt-vx :invariant fn-cdt-vp
   :established ((fn-cdt-vopen fn-cdt-vopen-establishes))
   :transitions ((fn-cdt-vbump fn-cdt-vbump-carries)))
 :unchecked "a value-typed state without :complete-by")
(def-carried fn-cdt-vcarried
  :invariant fn-cdt-vp
  :established ((fn-cdt-vopen fn-cdt-vopen-establishes))
  :transitions ((fn-cdt-vbump fn-cdt-vbump-carries))
  :complete-by (:enumeration "a value this test threads; fn-cdt-vbump is its one transition")
  :trace nil)
(assert-event
 (equal (fn-cd-get :complete-by
                   (cdr (assoc-eq 'fn-cdt-vcarried (table-alist 'fn-carried (w state)))))
        '(:enumeration "a value this test threads; fn-cdt-vbump is its one transition")))
(assert-event
 (null (getpropc 'fn-cdt-vcarried-run-carries 'theorem nil (w state))))

; ---------------------------------------------------------------------------
; 4. definterface's `:raw-with (:carried NAME)': the D40 checker over the
; resolved theorems (the bridge, the open, the entry's own preservation),
; after the row's own checks are re-run in the current world.

(definterface fn-cdt-bump
  :class :common-lisp-compliant
  :kinds ((n natp))
  :raw-with (:carried fn-cdt-carried))
(definterface fn-cdt-note
  :class :common-lisp-compliant
  :raw-with (:carried fn-cdt-carried))

(assert-event
 (equal (cdr (assoc-eq 'fn-cdt-bump (table-alist 'fn-interfaces (w state))))
        '(:class :common-lisp-compliant :kinds ((n natp))
          :raw-with (:carried fn-cdt-carried))))
(assert-event
 (equal (fn-di-raw-with-theorems 'fn-cdt-bump
                                 '(:raw-with (:carried fn-cdt-carried)) (w state))
        '(fn-cdt-relp-nonzero fn-cdt-open-establishes fn-cdt-bump-carries)))

; Refused: an establishing point is not a transition of the invariant.
(assert-event
 (fn-di-problem 'fn-cdt-open '(:class :common-lisp-compliant
                               :raw-with (:carried fn-cdt-carried)) (w state)))
(must-fail-checked
 (definterface fn-cdt-open :class :common-lisp-compliant
   :raw-with (:carried fn-cdt-carried))
 :unchecked "fn-cdt-open establishes the invariant; it is not a transition")

; Refused: no such carried invariant.
(assert-event
 (fn-di-problem 'fn-cdt-bump '(:class :common-lisp-compliant :kinds ((n natp))
                               :raw-with (:carried fn-cdt-nope)) (w state)))
(must-fail-checked
 (definterface fn-cdt-bump :class :common-lisp-compliant :kinds ((n natp))
   :raw-with (:carried fn-cdt-nope))
 :unchecked "no carried invariant fn-cdt-nope in this world")

; Refused at the form: (:carried) and (:carried N extra).
(assert-event (not (fn-di-raw-with-formp '(:carried))))
(assert-event (not (fn-di-raw-with-formp '(:carried fn-cdt-carried extra))))
(must-fail-checked
 (definterface fn-cdt-bump :class :common-lisp-compliant :kinds ((n natp))
   :raw-with (:carried))
 :unchecked "(:carried) names no invariant")
(must-fail-checked
 (definterface fn-cdt-bump :class :common-lisp-compliant :kinds ((n natp))
   :raw-with (:carried fn-cdt-carried extra))
 :unchecked "(:carried N extra) is malformed")

; Completeness bites after the row: an entry returning the stobj declared
; later refuses both def-carried-check and a new :raw-with acceptance.
(defun fn-cdt-zap (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (update-fn-cdt-n 0 fn-cdt-st))
(definterface fn-cdt-zap :class :common-lisp-compliant)
(assert-event
 (eq (cdr (assoc #\0 (cdr (fn-cd-problem
                           'fn-cdt-carried
                           (cdr (assoc-eq 'fn-cdt-carried
                                          (table-alist 'fn-carried (w state))))
                           (w state)))))
     'fn-cdt-zap))
(must-fail-checked (def-carried-check fn-cdt-carried)
                   :unchecked "fn-cdt-zap returns the carried state and has no theorem")
(assert-event
 (fn-di-problem 'fn-cdt-reset '(:class :common-lisp-compliant
                                :raw-with (:carried fn-cdt-carried)) (w state)))
(must-fail-checked
 (definterface fn-cdt-reset :class :common-lisp-compliant
   :raw-with (:carried fn-cdt-carried))
 :unchecked "the row is no longer complete in this world: fn-cdt-zap is owed")
