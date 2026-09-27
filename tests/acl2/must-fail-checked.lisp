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
;   assert-event X / assert! X    X translates for evaluation.
; Any other event (a defun, an encapsulate, ...) cannot be checked for
; translation apart from admitting it, so it is REFUSED unless the call
; declares why its failure is the claim:
;   (must-fail-checked FORM :unchecked "reason")
; which is also the form for a failure that IS a translation-time refusal
; (a macro that must reject malformed input).  tools/must_fail_check.py
; refuses a bare must-fail anywhere in tests/acl2.
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

(defmacro must-fail-translates (form)
  `(make-event
    (er-progn (fn-mfc-check ',form 20 'must-fail-checked state)
              (value '(value-triple :must-fail-translates)))
    :check-expansion nil))

(defmacro must-fail-checked (form &rest args)
  (let* ((unchecked (fn-mfc-kwarg :unchecked args))
         (rest (if (member-eq :unchecked args)
                   (let ((tail (member-eq :unchecked args)))
                     (append (take (- (len args) (len tail)) args)
                             (cddr tail)))
                 args)))
    (cond ((member-eq :unchecked args)
           (if (and (stringp unchecked) (< 0 (length unchecked)))
               `(must-fail ,form ,@rest)
             (er hard 'must-fail-checked ":unchecked needs a non-empty reason ~
                                     string.")))
          (t `(progn (must-fail-translates ,form)
                     (must-fail ,form ,@rest))))))
