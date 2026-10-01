; Teeth for books/def-carried.lisp: the generated statements, and that a
; theorem about any other term proves none of them.
;
;   1. Accepted: a stobj row; its normalized table row, every generated
;      statement pinned literally, def-carried-check (each generated name's
;      formula re-generated and compared), the trace theorem and its
;      instances, evaluated reachable witnesses with the complete antecedent
;      and conclusion of each generated statement, hypothesis-removal
;      witnesses (corrupted input state), the D40 resolution (generated names
;      only) and the `:raw-with (:carried NAME)' declarations it accepts.
;   2. Malformed forms (fn-cd-refusal), each refusal asserted exactly.
;   3. World refusals, each asserted by its words, and the generated
;      statement's proof failure asserted BY ITS GENERATED NAME for every
;      theorem about another term.
;   4. The review findings as must-fails with their specific refusal:
;      r02-F1/F2/F3, r08-F1, r09-F1/F2, r14-F1; and the paths r15 is asked
;      about: a hand-written table row naming a non-generated theorem, a row
;      with declared :hyps, a guard conjunct of R over another term.
;   5. The `:raw-with (:carried ...)' refusals; completeness after the row.
;
; fn-cdt-refused runs exactly what `def-carried' runs (fn-cd-refusal,
; fn-cd-declare, then the events fn-cd-events emits, in order, inside a
; make-event whose world is rolled back) and asserts the FIRST refusal: a
; malformed-form reason keyword, a msg's format string containing EXPECTED,
; or the name of the generated defthm / the vacuity probe's message.  Any
; other refusal, or admission, fails the assertion.

(in-package "ACL2")
(include-book "../../books/def-carried")
(include-book "../../books/definterface")
(include-book "../../books/payload-kinds") ; *fn-entry-guard-kinds*
(include-book "must-fail-checked")

(defun fn-cdt-first-refusal (events state)
  (declare (xargs :mode :program :stobjs state))
  (if (atom events)
      (value :admitted)
    (let* ((event (car events))
           (event (if (eq (car event) 'local) (cadr event) event)))
      (mv-let (erp pair state)
        (with-output! :off :all
          (trans-eval event 'fn-cdt-first-refusal state t))
        (cond (erp (value (list :evaluation-error (car event))))
              ((not (equal (car pair) '(nil nil state)))
               (value (list :unexpected-signature (car event))))
              ((car (cdr pair))
               (value (if (member-eq (car event) '(defthm fn-cd-nonvacuous))
                          (cadr event)
                        (list :refused (car event)))))
              (t (fn-cdt-first-refusal (cdr events) state)))))))

(defun fn-cdt-reason (name kvs state)
  (declare (xargs :mode :program :stobjs state))
  (let ((form (fn-cd-refusal name kvs)))
    (if form
        (value (car form))
      (mv-let (problem row)
        (fn-cd-declare name kvs (w state))
        (if problem
            (value (car problem))
          (fn-cdt-first-refusal (cdr (fn-cd-events name row (w state))) state))))))

(defmacro fn-cdt-refused (name kvs expected)
  `(make-event
    (er-let* ((reason (fn-cdt-reason ',name ',kvs state)))
      (value (list 'assert-event
                   (if (stringp ',expected)
                       (and (stringp reason) (search ',expected reason) t)
                     (equal reason ',expected))
                   :msg (list 'quote (msg "refused by ~x0, expected ~x1"
                                          reason ',expected)))))))

; ---------------------------------------------------------------------------
; The fixture.

(defstobj fn-cdt-st
  (fn-cdt-n :type integer :initially 0)
  (fn-cdt-log :type t :initially nil))

(defun fn-cdt-relp (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (< 0 (fn-cdt-n fn-cdt-st)))

(defun fn-cdt-nonzerop (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (not (equal (fn-cdt-n fn-cdt-st) 0)))

(defun fn-cdt-open (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (update-fn-cdt-n 1 fn-cdt-st))

(defun fn-cdt-bump (n fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st :guard (and (natp n) (fn-cdt-relp fn-cdt-st))))
  (update-fn-cdt-n (+ n (fn-cdt-n fn-cdt-st)) fn-cdt-st))

; Its guard carries a second predicate the bridge concludes.
(defun fn-cdt-note (x fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st
                  :guard (and (fn-cdt-relp fn-cdt-st) (fn-cdt-nonzerop fn-cdt-st))))
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

; True theorems about OTHER terms: each proves no generated statement.
(defthm fn-cdt-unrelated (equal (len (list x)) 1))
(defthm fn-cdt-bump-carries-shifted          ; another argument
  (implies (and (natp n) (fn-cdt-relp fn-cdt-st))
           (fn-cdt-relp (fn-cdt-bump (+ 1 n) fn-cdt-st))))
(defthm fn-cdt-open-of-bump                  ; a term containing the call
  (implies (fn-cdt-relp fn-cdt-st)
           (fn-cdt-relp (fn-cdt-open (fn-cdt-bump n fn-cdt-st)))))
(defthm fn-cdt-bump-of-open                  ; the invariant of a projection
  (implies (fn-cdt-relp (fn-cdt-open fn-cdt-st))
           (fn-cdt-relp (fn-cdt-bump 0 (fn-cdt-open fn-cdt-st)))))

; A constantly-true relation.
(defun fn-cdt-truep (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (or (fn-cdt-relp fn-cdt-st) t))
(defthm fn-cdt-open-establishes-truep (fn-cdt-truep (fn-cdt-open fn-cdt-st)))
(defthm fn-cdt-truep-always (fn-cdt-truep fn-cdt-st) :rule-classes nil)

(definterface fn-cdt-open :class :common-lisp-compliant)
(definterface fn-cdt-bump :class :common-lisp-compliant :kinds ((n natp)))
(definterface fn-cdt-note :class :common-lisp-compliant)
(definterface fn-cdt-reset :class :common-lisp-compliant)
(definterface fn-cdt-peek :class :common-lisp-compliant)

(assert-event
 (equal (fn-cd-returning-entries (table-alist 'fn-interfaces (w state))
                                 'fn-cdt-st (w state))
        '(fn-cdt-reset fn-cdt-note fn-cdt-bump fn-cdt-open)))
(assert-event (eq (fn-cd-state-stobj 'fn-cdt-relp (w state)) 'fn-cdt-st))

; ---------------------------------------------------------------------------
; 2. Malformed forms.

(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes)) :bogus 1)
                :unknown-keyword)
(fn-cdt-refused fn-cdt-x (:established ((fn-cdt-open fn-cdt-open-establishes)))
                :no-invariant)
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp) :no-established)
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions ((fn-cdt-bump)))
                :bad-transitions)
; r08-F1's declared PATTERN, positional, is no longer grammar at all.
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions ((fn-cdt-note fn-cdt-note-carries (mv-nth 1 _))))
                :bad-transitions)
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes (fn-cdt-open _))))
                :bad-established)
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes :pattern _)))
                :bad-established)
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes :hyps t)))
                :bad-established)
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :concludes (fn-cdt-nonzerop))
                :bad-concludes)
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :complete-by (:enumeration))
                :bad-complete-by)
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :trace :maybe)
                :bad-trace)
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-note fn-cdt-note-carries (mv-nth 1 _))))
 :unchecked "a positional PATTERN is refused at expansion")

; ---------------------------------------------------------------------------
; 3. World refusals.

(defconst *fn-cdt-complete*
  ; every fixture entry returning the stobj, with its own theorem
  '((fn-cdt-bump fn-cdt-bump-carries)
    (fn-cdt-note fn-cdt-note-carries)
    (fn-cdt-reset fn-cdt-reset-carries)))

(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-nope
                          :established ((fn-cdt-open fn-cdt-open-establishes)))
                "is not a function in this world")
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-bump
                          :established ((fn-cdt-open fn-cdt-open-establishes)))
                "of one formal")
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions ((fn-cdt-bump fn-cdt-no-such-theorem)))
                "which is not a theorem in this world")
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions ((fn-cdt-bump fn-cdt-bump-carries) fn-cdt-reset))
                "has no preservation theorem")
; Completeness, derived (r02-F1: no declared writer list to omit from).
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                                        (fn-cdt-note fn-cdt-note-carries)))
                "returns the carried state")
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                                        (fn-cdt-note fn-cdt-note-carries)
                                        (fn-cdt-reset fn-cdt-reset-carries))
                          :complete-by (:enumeration "no"))
                "never claimed")
; The stobj's place in arguments and result is the world's.
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                                        (fn-cdt-note fn-cdt-note-carries :result (mv-nth 1 _))
                                        (fn-cdt-reset fn-cdt-reset-carries)))
                "never declared")
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions ((fn-cdt-bump fn-cdt-bump-carries :state 1)
                                        (fn-cdt-note fn-cdt-note-carries)
                                        (fn-cdt-reset fn-cdt-reset-carries)))
                "never declared")
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-peek fn-cdt-open-establishes)))
                "does not return the carried stobj")
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions ((fn-cdt-bump fn-cdt-bump-carries :hyps ((natp k)))
                                        (fn-cdt-note fn-cdt-note-carries)
                                        (fn-cdt-reset fn-cdt-reset-carries)))
                "mention variables that are not its formals")
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions ((fn-cdt-bump fn-cdt-bump-carries :hyps ((fn-cdt-nope n)))
                                        (fn-cdt-note fn-cdt-note-carries)
                                        (fn-cdt-reset fn-cdt-reset-carries)))
                "does not translate")
; A bridge must have a guard conjunct to conclude, and a theorem.
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions #.*fn-cdt-complete*
                          :concludes ((fn-cdt-peek fn-cdt-relp-nonzero)))
                "has nothing to conclude")
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions #.*fn-cdt-complete*
                          :concludes ((fn-cdt-nonzerop fn-cdt-no-such-theorem)))
                "a bridge names")
; Vacuity, refuted: a constant-T invariant; contradictory declared hyps.
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-truep
                          :established ((fn-cdt-open fn-cdt-open-establishes-truep))
                          :transitions ((fn-cdt-bump fn-cdt-truep-always)
                                        (fn-cdt-note fn-cdt-truep-always)
                                        (fn-cdt-reset fn-cdt-truep-always))
                          :trace nil)
                "the carried invariant is provably always true")
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions ((fn-cdt-bump fn-cdt-bump-carries :hyps ((not (natp n))))
                                        (fn-cdt-note fn-cdt-note-carries)
                                        (fn-cdt-reset fn-cdt-reset-carries))
                          :trace nil)
                "transition hypotheses are provably contradictory")
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes
                                                     :hyps ((not (fn-cdt-stp fn-cdt-st)))))
                          :transitions #.*fn-cdt-complete* :trace nil)
                "establishing hypotheses are provably contradictory")

; Every theorem about another term: the generated statement fails, refused
; by the generated name.
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions ((fn-cdt-bump fn-cdt-open-establishes)
                                        (fn-cdt-note fn-cdt-note-carries)
                                        (fn-cdt-reset fn-cdt-reset-carries)))
                fn-cdt-x-fn-cdt-bump-carries)
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions ((fn-cdt-bump fn-cdt-relp-nonzero)
                                        (fn-cdt-note fn-cdt-note-carries)
                                        (fn-cdt-reset fn-cdt-reset-carries)))
                fn-cdt-x-fn-cdt-bump-carries)
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions ((fn-cdt-bump fn-cdt-open-of-bump)
                                        (fn-cdt-note fn-cdt-note-carries)
                                        (fn-cdt-reset fn-cdt-reset-carries)))
                fn-cdt-x-fn-cdt-bump-carries)
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions ((fn-cdt-bump fn-cdt-reset-carries)
                                        (fn-cdt-note fn-cdt-note-carries)
                                        (fn-cdt-reset fn-cdt-reset-carries)))
                fn-cdt-x-fn-cdt-bump-carries)
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions ((fn-cdt-bump fn-cdt-bump-carries-shifted)
                                        (fn-cdt-note fn-cdt-note-carries)
                                        (fn-cdt-reset fn-cdt-reset-carries)))
                fn-cdt-x-fn-cdt-bump-carries)
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-open-establishes))
                          :transitions ((fn-cdt-bump fn-cdt-bump-of-open)
                                        (fn-cdt-note fn-cdt-note-carries)
                                        (fn-cdt-reset fn-cdt-reset-carries)))
                fn-cdt-x-fn-cdt-bump-carries)
(fn-cdt-refused fn-cdt-x (:invariant fn-cdt-relp
                          :established ((fn-cdt-open fn-cdt-unrelated))
                          :transitions #.*fn-cdt-complete*)
                fn-cdt-x-fn-cdt-open-establishes)

; ---------------------------------------------------------------------------
; 4. The review findings: each exploit a must-fail with its refusal.

; r02-F2 and r08-F1: a transition whose theorem is about the REPAIRED
; result (open after break).  The generated statement is about break's own
; result and is false (break leaves 0), so its proof fails; the declared
; repair is no longer expressible (positional: grammar; :result: refused
; on a stobj).
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
  (fn-cdt-refused fn-cdt-broken
                  (:invariant fn-cdt-relp
                   :established ((fn-cdt-open fn-cdt-open-establishes))
                   :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                                 (fn-cdt-note fn-cdt-note-carries)
                                 (fn-cdt-reset fn-cdt-reset-carries)
                                 (fn-cdt-break fn-cdt-break-repaired))
                   :trace nil)
                  fn-cdt-broken-fn-cdt-break-carries))
 (local
  (must-fail-checked
   (def-carried fn-cdt-broken
     :invariant fn-cdt-relp
     :established ((fn-cdt-open fn-cdt-open-establishes))
     :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                   (fn-cdt-note fn-cdt-note-carries)
                   (fn-cdt-reset fn-cdt-reset-carries)
                   (fn-cdt-break fn-cdt-break-repaired))
     :trace nil)
   :unchecked "r02-F2: the generated fn-cdt-broken-fn-cdt-break-carries is false"))
 (local
  (fn-cdt-refused fn-cdt-broken
                  (:invariant fn-cdt-relp
                   :established ((fn-cdt-open fn-cdt-open-establishes))
                   :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                                 (fn-cdt-note fn-cdt-note-carries)
                                 (fn-cdt-reset fn-cdt-reset-carries)
                                 (fn-cdt-break fn-cdt-break-repaired (fn-cdt-open _)))
                   :trace nil)
                  :bad-transitions))
 (local
  (fn-cdt-refused fn-cdt-broken
                  (:invariant fn-cdt-relp
                   :established ((fn-cdt-open fn-cdt-open-establishes))
                   :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                                 (fn-cdt-note fn-cdt-note-carries)
                                 (fn-cdt-reset fn-cdt-reset-carries)
                                 (fn-cdt-break fn-cdt-break-repaired
                                               :result (fn-cdt-open _)))
                   :trace nil)
                  "never declared"))
 ; and with no row, the raw declaration has nothing to resolve
 (local
  (must-fail-checked
   (definterface fn-cdt-break :class :common-lisp-compliant
     :raw-with (:carried fn-cdt-broken))
   :unchecked "no carried invariant fn-cdt-broken")))

; r09-F2: an establishing point whose theorem is about the repaired open.
(encapsulate ()
 (local
  (defun r09-bad-open (fn-cdt-st)
    (declare (xargs :stobjs fn-cdt-st))
    (update-fn-cdt-n 0 fn-cdt-st)))
 (local
  (defthm r09-bad-open-repaired
    (fn-cdt-relp (fn-cdt-open (r09-bad-open fn-cdt-st)))))
 (local (definterface r09-bad-open :class :common-lisp-compliant))
 (local
  (fn-cdt-refused r09-bad-establishment
                  (:invariant fn-cdt-relp
                   :established ((fn-cdt-open fn-cdt-open-establishes)
                                 (r09-bad-open r09-bad-open-repaired))
                   :transitions #.*fn-cdt-complete*
                   :trace nil)
                  r09-bad-establishment-r09-bad-open-establishes))
 (local
  (must-fail-checked
   (def-carried r09-bad-establishment
     :invariant fn-cdt-relp
     :established ((fn-cdt-open fn-cdt-open-establishes)
                   (r09-bad-open r09-bad-open-repaired))
     :transitions #.*fn-cdt-complete*
     :trace nil)
   :unchecked "r09-F2: the generated r09-bad-establishment-r09-bad-open-establishes is false"))
 (local
  (fn-cdt-refused r09-bad-establishment
                  (:invariant fn-cdt-relp
                   :established ((fn-cdt-open fn-cdt-open-establishes)
                                 (r09-bad-open r09-bad-open-repaired (fn-cdt-open _)))
                   :transitions #.*fn-cdt-complete*
                   :trace nil)
                  :bad-established)))

; r09-F1: a value row may declare a repairing :result -- the row records it
; and the generated statement is about it -- but a value row backs no raw
; dispatch; without the repair the generated statement is false.
(encapsulate ()
 (local (defun fn-cdt-wp (s) (declare (xargs :guard t)) (equal s '(1))))
 (local (defun fn-cdt-wrepair (s) (declare (xargs :guard t) (ignore s)) (cons 1 nil)))
 (local (defun fn-cdt-wbad (s) (declare (xargs :guard (fn-cdt-wp s)) (ignore s)) nil))
 (local (defthm fn-cdt-wopen (fn-cdt-wp (fn-cdt-wrepair s))))
 (local (defthm fn-cdt-wbad-carries
          (implies (fn-cdt-wp s) (fn-cdt-wp (fn-cdt-wrepair (fn-cdt-wbad s))))))
 (local
  (fn-cdt-refused fn-cdt-wbad-row
                  (:invariant fn-cdt-wp
                   :established ((fn-cdt-wrepair fn-cdt-wopen))
                   :transitions ((fn-cdt-wbad fn-cdt-wbad-carries :state 0))
                   :complete-by (:enumeration "one transition") :trace nil)
                  fn-cdt-wbad-row-fn-cdt-wbad-carries))
 (local
  (fn-cdt-refused fn-cdt-wbad-row
                  (:invariant fn-cdt-wp
                   :established ((fn-cdt-wrepair fn-cdt-wopen))
                   :transitions ((fn-cdt-wbad fn-cdt-wbad-carries :result (fn-cdt-wrepair _)))
                   :complete-by (:enumeration "one transition") :trace nil)
                  "say which formal"))
 (local
  (def-carried fn-cdt-wrepaired
    :invariant fn-cdt-wp
    :established ((fn-cdt-wrepair fn-cdt-wopen))
    :transitions ((fn-cdt-wbad fn-cdt-wbad-carries :state 0 :result (fn-cdt-wrepair _)))
    :complete-by (:enumeration "one transition; the declared result repairs, recorded")
    :trace nil))
 (local
  (assert-event
   (equal (fn-cd-get :transitions
                     (cdr (assoc-eq 'fn-cdt-wrepaired (table-alist 'fn-carried (w state)))))
          '((fn-cdt-wbad fn-cdt-wbad-carries
                         :name fn-cdt-wrepaired-fn-cdt-wbad-carries :hyps nil
                         :state 0 :result (fn-cdt-wrepair _))))))
 (local
  (assert-event
   (search "value-state carried rows"
           (car (cdr (assoc #\2 (cdr (fn-di-raw-with-problem
                                      'fn-cdt-wbad
                                      '(:class :common-lisp-compliant
                                        :raw-with (:carried fn-cdt-wrepaired))
                                      (w state))))))))))

; r14-F1: a bridge theorem about the repaired result.  The generated bridge
; is about the SAME state, (implies (r14-r x) (r14-p x)), false, refused by
; name; without a bridge, raw dispatch is refused for the uncovered conjunct.
(encapsulate ()
 (local
  (encapsulate ()
   (defstobj r14-st (r14-n :type (integer 0 *) :initially 0))
   (defun r14-r (r14-st) (declare (xargs :stobjs r14-st)) (< 0 (r14-n r14-st)))
   (defun r14-p (r14-st) (declare (xargs :stobjs r14-st)) (equal (r14-n r14-st) 1))
   (defun r14-q (r14-st) (declare (xargs :stobjs r14-st)) (not (equal (r14-n r14-st) 0)))
   (defun r14-open (r14-st) (declare (xargs :stobjs r14-st)) (update-r14-n 1 r14-st))
   (defun r14-break-p (r14-st)
     (declare (xargs :stobjs r14-st :guard (and (r14-r r14-st) (r14-p r14-st))))
     (update-r14-n 2 r14-st))
   (defun r14-good (r14-st)
     (declare (xargs :stobjs r14-st :guard (and (r14-r r14-st) (r14-q r14-st))))
     (update-r14-n 3 r14-st))
   (defthm r14-open-r (r14-r (r14-open r14-st)))
   (defthm r14-break-r (implies (r14-r r14-st) (r14-r (r14-break-p r14-st))))
   (defthm r14-good-r (implies (r14-r r14-st) (r14-r (r14-good r14-st))))
   (defthm r14-repaired-bridge
     (implies (r14-r r14-st) (r14-p (r14-open (r14-break-p r14-st))))
     :rule-classes nil)
   (defthm r14-same-state-bridge (implies (r14-r r14-st) (r14-q r14-st)))
   (definterface r14-open :class :common-lisp-compliant)
   (definterface r14-break-p :class :common-lisp-compliant)
   (definterface r14-good :class :common-lisp-compliant)
   (fn-cdt-refused r14-carried
                   (:invariant r14-r
                    :established ((r14-open r14-open-r))
                    :transitions ((r14-break-p r14-break-r) (r14-good r14-good-r))
                    :concludes ((r14-p r14-repaired-bridge))
                    :trace nil)
                   r14-carried-r14-p-bridge)
   (must-fail-checked
    (def-carried r14-carried
      :invariant r14-r
      :established ((r14-open r14-open-r))
      :transitions ((r14-break-p r14-break-r) (r14-good r14-good-r))
      :concludes ((r14-p r14-repaired-bridge))
      :trace nil)
    :unchecked "r14-F1: the generated r14-carried-r14-p-bridge is false")
   ; the honest row: R carried, Q bridged on the same state, P not
   (def-carried r14-with-bridge
     :invariant r14-r
     :established ((r14-open r14-open-r))
     :transitions ((r14-break-p r14-break-r) (r14-good r14-good-r))
     :concludes ((r14-q r14-same-state-bridge))
     :trace nil)
   (assert-event
    (equal (getpropc 'r14-with-bridge-r14-q-bridge 'theorem nil (w state))
           '(implies (r14-r r14-st) (r14-q r14-st))))
   (definterface r14-good :class :common-lisp-compliant
     :raw-with (:carried r14-with-bridge))
   (assert-event
    (let ((problem (fn-di-raw-with-problem
                    'r14-break-p '(:class :common-lisp-compliant
                                   :raw-with (:carried r14-with-bridge)) (w state))))
      (and (search "guard conjunct ~x2 is neither the" (car problem))
           (equal (cdr (assoc #\2 (cdr problem))) '(r14-p r14-st)))))
   (must-fail-checked
    (definterface r14-break-p :class :common-lisp-compliant
      :raw-with (:carried r14-with-bridge))
    :unchecked "r14-p has no generated bridge"))))

; ---------------------------------------------------------------------------
; 1. Accepted.

(def-carried fn-cdt-carried
  :invariant fn-cdt-relp
  :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                (fn-cdt-note fn-cdt-note-carries)
                (fn-cdt-reset fn-cdt-reset-carries))
  :concludes ((fn-cdt-nonzerop fn-cdt-relp-nonzero)))

(assert-event
 (equal (cdr (assoc-eq 'fn-cdt-carried (table-alist 'fn-carried (w state))))
        '(:invariant fn-cdt-relp
          :state fn-cdt-st
          :established ((fn-cdt-open fn-cdt-open-establishes
                                     :name fn-cdt-carried-fn-cdt-open-establishes :hyps nil))
          :transitions ((fn-cdt-bump fn-cdt-bump-carries
                                     :name fn-cdt-carried-fn-cdt-bump-carries :hyps nil)
                        (fn-cdt-note fn-cdt-note-carries
                                     :name fn-cdt-carried-fn-cdt-note-carries :hyps nil)
                        (fn-cdt-reset fn-cdt-reset-carries
                                      :name fn-cdt-carried-fn-cdt-reset-carries :hyps nil))
          :concludes ((fn-cdt-nonzerop fn-cdt-relp-nonzero
                                       :name fn-cdt-carried-fn-cdt-nonzerop-bridge))
          :complete-by nil
          :trace t)))

; The generated statements, literally: R and the world's guard to R of the
; state the world says the entry returns; the bridge from the guards.
(assert-event
 (equal (getpropc 'fn-cdt-carried-fn-cdt-bump-carries 'theorem nil (w state))
        '(implies (if (fn-cdt-relp fn-cdt-st)
                      (if (fn-cdt-stp fn-cdt-st)
                          (if (natp n) (fn-cdt-relp fn-cdt-st) 'nil)
                        'nil)
                    'nil)
                  (fn-cdt-relp (fn-cdt-bump n fn-cdt-st)))))
(assert-event
 (equal (getpropc 'fn-cdt-carried-fn-cdt-note-carries 'theorem nil (w state))
        '(implies (if (fn-cdt-relp fn-cdt-st)
                      (if (fn-cdt-stp fn-cdt-st)
                          (if (fn-cdt-relp fn-cdt-st) (fn-cdt-nonzerop fn-cdt-st) 'nil)
                        'nil)
                    'nil)
                  (fn-cdt-relp (mv-nth '1 (fn-cdt-note x fn-cdt-st))))))
(assert-event
 (equal (getpropc 'fn-cdt-carried-fn-cdt-open-establishes 'theorem nil (w state))
        '(implies (fn-cdt-stp fn-cdt-st) (fn-cdt-relp (fn-cdt-open fn-cdt-st)))))
(assert-event
 (equal (getpropc 'fn-cdt-carried-fn-cdt-nonzerop-bridge 'theorem nil (w state))
        '(implies (fn-cdt-relp fn-cdt-st) (fn-cdt-nonzerop fn-cdt-st))))

(def-carried-check fn-cdt-carried)
(must-fail-checked (def-carried-check fn-cdt-nope)
                   :unchecked "no such carried invariant")

; A redeclaration is refused before any event (no name collision masks it).
(fn-cdt-refused fn-cdt-carried
                (:invariant fn-cdt-relp
                 :established ((fn-cdt-open fn-cdt-open-establishes))
                 :transitions #.*fn-cdt-complete* :trace nil)
                "is already a carried invariant")

; The trace theorem, its statement pinned, and instances at literal events.
(assert-event
 (equal (getpropc 'fn-cdt-carried-run-carries 'theorem nil (w state))
        '(implies (if (fn-cdt-relp s) (fn-cdt-carried-run-okp s es) 'nil)
                  (fn-cdt-relp (fn-cdt-carried-run s es)))))

(defthm fn-cdt-trace-witness
  (implies (and (fn-cdt-relp s) (fn-cdt-stp s))
           (fn-cdt-relp (fn-cdt-carried-run
                         s '((fn-cdt-bump 3) (fn-cdt-note x) (fn-cdt-reset)))))
  :hints (("Goal" :use ((:instance fn-cdt-carried-run-carries
                                   (es '((fn-cdt-bump 3) (fn-cdt-note x) (fn-cdt-reset)))))
           :in-theory (e/d (fn-cdt-carried-run-okp fn-cdt-carried-okp
                            fn-cdt-carried-step fn-cdt-relp-nonzero)
                           (fn-cdt-carried-run-carries fn-cdt-carried-run)))))

; Reachable positive witnesses, evaluated from the open: each generated
; statement's complete antecedent, then its conclusion.
(defun fn-cdt-witness-open ()
  (declare (xargs :guard t))
  (with-local-stobj fn-cdt-st
    (mv-let (ok fn-cdt-st)
      (let* ((before (fn-cdt-stp fn-cdt-st))
             (fn-cdt-st (fn-cdt-open fn-cdt-st)))
        (mv (and before (fn-cdt-relp fn-cdt-st)) fn-cdt-st))
      ok)))
(assert-event (fn-cdt-witness-open) :msg "fn-cdt-carried-fn-cdt-open-establishes: witness")

(defun fn-cdt-witness-bump ()
  (declare (xargs :guard t))
  (with-local-stobj fn-cdt-st
    (mv-let (ok fn-cdt-st)
      (let* ((fn-cdt-st (fn-cdt-open fn-cdt-st))
             (before (and (fn-cdt-relp fn-cdt-st) (fn-cdt-stp fn-cdt-st) (natp 3)))
             (fn-cdt-st (fn-cdt-bump 3 fn-cdt-st)))
        (mv (and before (fn-cdt-relp fn-cdt-st) (equal (fn-cdt-n fn-cdt-st) 4)) fn-cdt-st))
      ok)))
(assert-event (fn-cdt-witness-bump) :msg "fn-cdt-carried-fn-cdt-bump-carries: witness")

(defun fn-cdt-witness-note ()
  (declare (xargs :guard t))
  (with-local-stobj fn-cdt-st
    (mv-let (ok fn-cdt-st)
      (let* ((fn-cdt-st (fn-cdt-open fn-cdt-st))
             (before (and (fn-cdt-relp fn-cdt-st) (fn-cdt-stp fn-cdt-st)
                          (fn-cdt-nonzerop fn-cdt-st))))
        (mv-let (x fn-cdt-st)
          (fn-cdt-note 'x fn-cdt-st)
          (mv (and before (eq x 'x) (fn-cdt-relp fn-cdt-st)) fn-cdt-st)))
      ok)))
(assert-event (fn-cdt-witness-note) :msg "fn-cdt-carried-fn-cdt-note-carries: witness")

(defun fn-cdt-witness-reset ()
  (declare (xargs :guard t))
  (with-local-stobj fn-cdt-st
    (mv-let (ok fn-cdt-st)
      (let* ((fn-cdt-st (fn-cdt-open fn-cdt-st))
             (fn-cdt-st (fn-cdt-bump 5 fn-cdt-st))
             (before (and (fn-cdt-relp fn-cdt-st) (fn-cdt-stp fn-cdt-st)))
             (fn-cdt-st (fn-cdt-reset fn-cdt-st)))
        (mv (and before (fn-cdt-relp fn-cdt-st)) fn-cdt-st))
      ok)))
(assert-event (fn-cdt-witness-reset) :msg "fn-cdt-carried-fn-cdt-reset-carries: witness")

(defun fn-cdt-witness-bridge ()
  (declare (xargs :guard t))
  (with-local-stobj fn-cdt-st
    (mv-let (ok fn-cdt-st)
      (let ((fn-cdt-st (fn-cdt-open fn-cdt-st)))
        (mv (and (fn-cdt-relp fn-cdt-st) (fn-cdt-nonzerop fn-cdt-st)) fn-cdt-st))
      ok)))
(assert-event (fn-cdt-witness-bridge) :msg "fn-cdt-carried-fn-cdt-nonzerop-bridge: witness")

; Hypothesis removal, CORRUPTED INPUT STATE (n = -5 is no reachable state):
; omit (fn-cdt-relp st) from bump's generated statement; the retained
; (fn-cdt-stp st) and (natp 0) hold, the omitted one fails, and so does the
; conclusion.  The same state fails the bridge's hypothesis and conclusion.
(thm
 (let ((st '(-5 nil)))
   (and (fn-cdt-stp st) (natp 0) (not (fn-cdt-relp st))
        (not (fn-cdt-relp (fn-cdt-bump 0 st)))
        (fn-cdt-nonzerop (fn-cdt-bump 0 st)))))
(defun fn-cdt-witness-zero ()
  (declare (xargs :guard t))
  (with-local-stobj fn-cdt-st
    (mv-let (ok fn-cdt-st)
      (let ((fn-cdt-st (update-fn-cdt-n 0 fn-cdt-st)))
        (mv (and (not (fn-cdt-relp fn-cdt-st)) (not (fn-cdt-nonzerop fn-cdt-st)))
            fn-cdt-st))
      ok)))
(assert-event (fn-cdt-witness-zero)
              :msg "bridge without (fn-cdt-relp st): conclusion fails")

; The D40 resolution: generated names only, for a transition only.
(assert-event
 (equal (fn-cd-raw-with 'fn-cdt-carried 'fn-cdt-bump (w state))
        '(fn-cdt-carried-fn-cdt-bump-carries fn-cdt-carried-fn-cdt-nonzerop-bridge)))
(assert-event (null (fn-cd-raw-with 'fn-cdt-carried 'fn-cdt-open (w state))))
(assert-event (null (fn-cd-raw-with 'fn-cdt-carried 'fn-cdt-peek (w state))))
(assert-event (null (fn-cd-raw-with 'fn-cdt-nope 'fn-cdt-bump (w state))))
(assert-event
 (equal (fn-di-raw-with-theorems 'fn-cdt-note '(:raw-with (:carried fn-cdt-carried)) (w state))
        '(fn-cdt-carried-fn-cdt-note-carries fn-cdt-carried-fn-cdt-nonzerop-bridge)))

; Accepted raw declarations.
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

; ---------------------------------------------------------------------------
; 4 (cont.). What r15 is asked: a statement other than the generated forms.

; A hand-written table row (no def-carried) naming TRUE theorems about other
; terms -- and even the user's own preservation theorem -- as the "generated"
; names: every name's formula is compared with the statement regenerated
; from the world, so :raw-with refuses it.
(encapsulate ()
 (local
  (table fn-carried 'fn-cdt-forged
         '(:invariant fn-cdt-relp :state fn-cdt-st
           :established ((fn-cdt-open fn-cdt-open-establishes
                                      :name fn-cdt-carried-fn-cdt-open-establishes :hyps nil))
           :transitions ((fn-cdt-bump fn-cdt-bump-carries
                                      :name fn-cdt-bump-carries-shifted :hyps nil)
                         (fn-cdt-note fn-cdt-note-carries
                                      :name fn-cdt-carried-fn-cdt-note-carries :hyps nil)
                         (fn-cdt-reset fn-cdt-reset-carries
                                       :name fn-cdt-carried-fn-cdt-reset-carries :hyps nil))
           :concludes nil :complete-by nil :trace nil)))
 (local
  (assert-event
   (search "is not the generated statement in this world"
           (car (cdr (assoc #\0 (cdr (cdr (assoc #\2 (cdr (fn-di-raw-with-problem
                                                          'fn-cdt-bump
                                                          '(:class :common-lisp-compliant
                                                            :kinds ((n natp))
                                                            :raw-with (:carried fn-cdt-forged))
                                                          (w state))))))))))))
 (local
  (must-fail-checked
   (definterface fn-cdt-bump :class :common-lisp-compliant :kinds ((n natp))
     :raw-with (:carried fn-cdt-forged))
   :unchecked "the forged row's transition names a theorem about (bump (+ 1 n))"))
 (local
  (table fn-carried 'fn-cdt-forged-own
         '(:invariant fn-cdt-relp :state fn-cdt-st
           :established ((fn-cdt-open fn-cdt-open-establishes
                                      :name fn-cdt-carried-fn-cdt-open-establishes :hyps nil))
           :transitions ((fn-cdt-bump fn-cdt-bump-carries
                                      :name fn-cdt-bump-carries :hyps nil)
                         (fn-cdt-note fn-cdt-note-carries
                                      :name fn-cdt-carried-fn-cdt-note-carries :hyps nil)
                         (fn-cdt-reset fn-cdt-reset-carries
                                       :name fn-cdt-carried-fn-cdt-reset-carries :hyps nil))
           :concludes nil :complete-by nil :trace nil)))
 (local
  (must-fail-checked
   (definterface fn-cdt-bump :class :common-lisp-compliant :kinds ((n natp))
     :raw-with (:carried fn-cdt-forged-own))
   :unchecked "the user's theorem is not the generated statement")))

; A row with a declared hypothesis anywhere backs no raw dispatch: the host
; does not check a declared premise.
(encapsulate ()
 (local
  (def-carried fn-cdt-hyped
    :invariant fn-cdt-relp
    :established ((fn-cdt-open fn-cdt-open-establishes :hyps ((natp (fn-cdt-n fn-cdt-st)))))
    :transitions #.*fn-cdt-complete*
    :trace nil))
 (local
  (assert-event
   (search "beyond its guard"
           (car (cdr (assoc #\2 (cdr (fn-di-raw-with-problem
                                      'fn-cdt-bump
                                      '(:class :common-lisp-compliant :kinds ((n natp))
                                        :raw-with (:carried fn-cdt-hyped))
                                      (w state))))))))))

; A guard conjunct (R t) with t another term over the state cannot arise:
; stobj discipline makes the stobj variable the only argument a guard may
; pass R.  fn-cd-uncovered-conjunct still requires (R s) literally.

; A value-typed state: completeness cannot be derived, so the form must
; say :complete-by; the transition must say :state.
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
(fn-cdt-refused fn-cdt-vx (:invariant fn-cdt-vp
                           :established ((fn-cdt-vopen fn-cdt-vopen-establishes))
                           :transitions ((fn-cdt-vbump fn-cdt-vbump-carries :state 1)))
                "is a value, not a stobj")
(fn-cdt-refused fn-cdt-vx (:invariant fn-cdt-vp
                           :established ((fn-cdt-vopen fn-cdt-vopen-establishes))
                           :transitions ((fn-cdt-vbump fn-cdt-vbump-carries :state 2))
                           :complete-by (:enumeration "x"))
                "is none of them")
(fn-cdt-refused fn-cdt-vx (:invariant fn-cdt-vp
                           :established ((fn-cdt-vopen fn-cdt-vopen-establishes))
                           :transitions ((fn-cdt-vbump fn-cdt-vbump-carries :state 1
                                                       :result (car k)))
                           :complete-by (:enumeration "x"))
                "is not a term over")
(def-carried fn-cdt-vcarried
  :invariant fn-cdt-vp
  :established ((fn-cdt-vopen fn-cdt-vopen-establishes))
  :transitions ((fn-cdt-vbump fn-cdt-vbump-carries :state 1))
  :complete-by (:enumeration "a value this test threads; fn-cdt-vbump is its one transition"))
(assert-event
 (equal (getpropc 'fn-cdt-vcarried-fn-cdt-vbump-carries 'theorem nil (w state))
        '(implies (if (fn-cdt-vp x) (if (natp k) (fn-cdt-vp x) 'nil) 'nil)
                  (fn-cdt-vp (fn-cdt-vbump k x)))))
(thm
 (let ((s (fn-cdt-vopen 1)) (e '(fn-cdt-vbump 2 nil)))
   (and (fn-cdt-vp s) (fn-cdt-vcarried-okp s e)
        (equal (fn-cdt-vcarried-step s e) '(3))
        (fn-cdt-vp (fn-cdt-vcarried-run s (list e e)))))
 :hints (("Goal" :in-theory (disable fn-cdt-vcarried-step-carries
                                     fn-cdt-vcarried-run-carries))))

; ---------------------------------------------------------------------------
; 5. definterface's `:raw-with (:carried NAME)' refusals.

(must-fail-checked
 (definterface fn-cdt-open :class :common-lisp-compliant
   :raw-with (:carried fn-cdt-carried))
 :unchecked "fn-cdt-open establishes the invariant; it is not a transition")
(must-fail-checked
 (definterface fn-cdt-bump :class :common-lisp-compliant :kinds ((n natp))
   :raw-with (:carried fn-cdt-nope))
 :unchecked "no carried invariant fn-cdt-nope in this world")
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

; r02-F3: completeness bites after the row: an entry returning the stobj
; declared later refuses def-carried-check and a new :raw-with acceptance.
(defun fn-cdt-zap (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (update-fn-cdt-n 0 fn-cdt-st))
(definterface fn-cdt-zap :class :common-lisp-compliant)
(assert-event
 (eq (cdr (assoc #\0 (cdr (fn-cd-problem
                           'fn-cdt-carried
                           (cdr (assoc-eq 'fn-cdt-carried
                                          (table-alist 'fn-carried (w state))))
                           t (w state)))))
     'fn-cdt-zap))
(must-fail-checked (def-carried-check fn-cdt-carried)
                   :unchecked "fn-cdt-zap returns the carried state and has no theorem")
(must-fail-checked
 (definterface fn-cdt-reset :class :common-lisp-compliant
   :raw-with (:carried fn-cdt-carried))
 :unchecked "the row is no longer complete in this world: fn-cdt-zap is owed")
