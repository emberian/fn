; must-fail-checked: a must-fail whose body must first TRANSLATE.
;
; std/testing/must-fail succeeds when its form fails for ANY reason, output
; suppressed.  A body that no longer translates -- a call at a stale arity, an
; undefined function, a theorem name already taken -- therefore "fails" and
; the tooth passes while biting nothing (keystone audit 2026-09-27: 41 forms
; in two test books, after the arena flip changed argument counts).
;
; (must-fail-checked FORM [:expected ..] [:with-output-off ..] [:check-expansion ..])
; first runs a check event on FORM, then the ordinary must-fail.  The check
; reaches the claim FORM makes, stripping local, with-output,
; with-prover-step-limit and with-prover-time-limit, evaluating a make-event's
; expansion form, and expanding any other macro, until it is one of:
;   defthm/defthmd NAME TERM ...  NAME is new, TERM translates as a theorem
;                                 and :hints translate (translate-hints+);
;   thm TERM ...                  TERM and :hints translate;
;   assert-event X / assert! X    X translates for evaluation;
;   verify-guards NAME ...        NAME is a function and :hints translate
;                                 (admit the defun with :verify-guards nil
;                                 first, so its translation is checked).
; Any other event (a defun, an encapsulate, ...) cannot be checked for
; translation apart from admitting it, so it is REFUSED unless the call
; declares why its failure is the claim:
;   (must-fail-checked FORM :unchecked "reason")
; which is also the form for a failure that IS a translation-time refusal
; (a macro that must reject malformed input).  tools/must_fail_check.py
; refuses a bare must-fail anywhere in tests/acl2.
;
; Step limit.  FORM runs under (with-prover-step-limit N FORM), N =
; *fn-mfc-default-step-limit* unless the call says :step-limit N (a larger
; number, or nil for none).  A false theorem otherwise grinds without end:
; arena-store-2's ground 744 subgoals past proof_repl's 600 s load timeout
; (2026-09-27).  The limit changes no green verdict: a FORM that fails now
; fails sooner.  What it costs: a TRUE claim that needs more than N steps
; fails too, so a tooth whose failure is expected to take long says so with
; :step-limit, and a failed proof search is never a counterexample
; (AGENTS.md); the tooth's claim is "this does not prove within N steps".
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(program)
(set-state-ok t)

(defun fn-mfc-kwarg (key args)
  ; the value after KEY in a keyword tail, or nil
  (cond ((or (atom args) (atom (cdr args))) nil)
        ((eq (car args) key) (cadr args))
        (t (fn-mfc-kwarg key (cddr args)))))

(defun fn-mfc-check-term (term ctx wrld state)
  (er-progn (translate term t t t ctx wrld state)
            (value :ok)))

(defun fn-mfc-check-hints (name hints ctx wrld state)
  (if (null hints)
      (value :ok)
    (er-progn (translate-hints+ name hints nil ctx wrld state)
              (value :ok))))

(defun fn-mfc-check (form depth ctx state)
  ; (mv erp :ok state): erp non-nil (with the error printed) when FORM does
  ; not reach a translatable claim.
  (let ((wrld (w state)))
    (cond
     ((zp depth)
      (er soft ctx "must-fail-checked: gave up expanding ~x0." form))
     ((or (atom form) (not (symbolp (car form))))
      (er soft ctx "must-fail-checked: ~x0 is not an event form; declare ~
                    :unchecked with a reason if its failure is the claim."
          form))
     (t
      (case (car form)
        (local (fn-mfc-check (cadr form) (1- depth) ctx state))
        ((with-output with-prover-step-limit with-prover-time-limit)
         (fn-mfc-check (car (last form)) (1- depth) ctx state))
        ((defthm defthmd)
         (let ((name (cadr form)) (term (caddr form)))
           (cond
            ((not (symbolp name))
             (er soft ctx "must-fail-checked: bad theorem name in ~x0." form))
            ((not (new-namep name wrld))
             (er soft ctx "must-fail-checked: the name ~x0 is already in use, so ~
                           the defthm fails for that and not for its claim."
                 name))
            (t (er-progn
                (fn-mfc-check-term term ctx wrld state)
                (fn-mfc-check-hints name (fn-mfc-kwarg :hints (cdddr form))
                                    ctx wrld state))))))
        (thm
         (er-progn
          (fn-mfc-check-term (cadr form) ctx wrld state)
          (fn-mfc-check-hints 'thm (fn-mfc-kwarg :hints (cddr form))
                              ctx wrld state)))
        ((assert-event assert!)
         (er-progn (translate (cadr form) t nil t ctx wrld state)
                   (value :ok)))
        (verify-guards
         (let ((name (cadr form)))
           (if (and (symbolp name) (function-symbolp name wrld))
               (fn-mfc-check-hints name (fn-mfc-kwarg :hints (cddr form))
                                   ctx wrld state)
             (er soft ctx "must-fail-checked: ~x0 is not a function, so the ~
                           verify-guards fails for that and not for its claim."
                 name))))
        (make-event
         (er-let* ((pair (trans-eval (cadr form) ctx state t)))
           ; pair = (stobjs-out . replaced-val)
           (let* ((stobjs-out (car pair))
                  (val (cdr pair)))
             (cond ((equal stobjs-out '(nil nil state))
                    (if (car val)
                        (er soft ctx "must-fail-checked: the make-event's form ~
                                      returned an error.")
                      (fn-mfc-check (cadr val) (1- depth) ctx state)))
                   ((equal stobjs-out '(nil))
                    (fn-mfc-check val (1- depth) ctx state))
                   (t (er soft ctx "must-fail-checked: cannot read the expansion ~
                                    of ~x0." form))))))
        (otherwise
         (if (and (getpropc (car form) 'macro-body nil wrld)
                  (not (member-eq (car form) (primitive-event-macros))))
             (er-let* ((exp (macroexpand1 form ctx state)))
               (fn-mfc-check exp (1- depth) ctx state))
           (er soft ctx "must-fail-checked: ~x0 is an event whose translation ~
                         cannot be checked apart from admitting it; declare ~
                         :unchecked with the reason its failure is the claim."
               (car form)))))))))

(logic)

; Generous next to the teeth the tree carries (a must-fail that does its work
; costs thousands of steps), small next to a runaway (millions per minute).
(defconst *fn-mfc-default-step-limit* 300000)

(defmacro must-fail-translates (form)
  `(make-event
    (er-progn (fn-mfc-check ',form 20 'must-fail-checked state)
              (value '(value-triple :must-fail-translates)))
    :check-expansion nil))

(defun fn-mfc-drop-kwarg (key args)
  ; ARGS without KEY and its value
  (declare (xargs :guard (true-listp args)))
  (cond ((or (atom args) (atom (cdr args))) args)
        ((equal (car args) key) (cddr args))
        (t (list* (car args) (cadr args) (fn-mfc-drop-kwarg key (cddr args))))))

(defun fn-mfc-limited (form limit)
  (declare (xargs :guard t))
  (if limit
      `(with-prover-step-limit ,limit ,form)
    form))

(defmacro must-fail-checked (form &rest args)
  (let* ((unchecked (fn-mfc-kwarg :unchecked args))
         (limit (if (member-eq :step-limit args)
                    (fn-mfc-kwarg :step-limit args)
                  '*fn-mfc-default-step-limit*))
         (rest (fn-mfc-drop-kwarg :step-limit (fn-mfc-drop-kwarg :unchecked args)))
         (limited (fn-mfc-limited form limit)))
    (cond ((not (or (null limit) (natp limit) (eq limit '*fn-mfc-default-step-limit*)))
           (er hard 'must-fail-checked ":step-limit is a number of prover steps ~
                                   or nil, not ~x0." limit))
          ((member-eq :unchecked args)
           (if (and (stringp unchecked) (< 0 (length unchecked)))
               `(must-fail ,limited ,@rest)
             (er hard 'must-fail-checked ":unchecked needs a non-empty reason ~
                                     string.")))
          (t `(progn (must-fail-translates ,form)
                     (must-fail ,limited ,@rest))))))

; The limit binds: a true theorem that needs more than a handful of steps
; fails under :step-limit 10, and the default leaves a cheap one alone.
(local (defun fn-mfc-witness-len (x)
         (if (consp x) (+ 1 (fn-mfc-witness-len (cdr x))) 0)))
(local (must-fail-checked
        (defthm fn-mfc-witness-append-len
          (equal (fn-mfc-witness-len (append x y))
                 (+ (fn-mfc-witness-len x) (fn-mfc-witness-len y))))
        :step-limit 10))
(local (defthm fn-mfc-witness-append-len
         (equal (fn-mfc-witness-len (append x y))
                (+ (fn-mfc-witness-len x) (fn-mfc-witness-len y)))))
(local (must-fail-checked (assert-event (equal 1 2))))
