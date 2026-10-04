; The owner's WRITER census over a loaded world (planning/design/owner-carrier-
; 2026-10-04.md section 5a; lane carrier2).  Program-only inspection, no proof
; claim.  world.lisp computes the TOUCHER closure thread.py threads (readers
; included); this file computes the conservative WRITER closure the owed-writer
; disposition rests on.
;
; F is a writer iff its closure (unnormalized bodies, guards and attachments)
; reaches one of these ROUTES:
;   (1) put-global / makunbound-global with key 'fn-owner or
;       'fn-owner-retain-carry, or with a key that is not a quoted constant;
;   (2) an evaluator over a form or a function computed at run time
;       (*fn-ocw-evaluators*); apply$/ev$ are excluded by rule: they run only
;       badged functions, which cannot take state;
;   (3) return-last whose first argument is not one of ACL2's built-in keys
;       (*fn-ocw-safe-return-last-keys*): raw code under a trust tag;
;   (4) a function with no unnormalized-body that is neither a primitive nor
;       constrained-without-attachment (an attached constrained function is
;       followed through its attachment).
; Every route counts whatever it does at run time.  A function this census
; clears cannot write the owner's globals by any ACL2 route; the raw host
; reaches them only through dispatched entries (tools/raw_dispatch_rule.py).
(in-package "ACL2")
(program)
(set-state-ok t)

(defconst *fn-ocw-writer-globals* '(fn-owner fn-owner-retain-carry))

(defconst *fn-ocw-evaluators*
  '(trans-eval trans-eval-default-warning trans-eval-no-warning trans-eval0
    simple-translate-and-eval simple-translate-and-eval-error-double
    ev ev-w ev-rec ev-fncall ev-fncall-w ev-fncall! ev-fncall-rec
    ev-fncall-w-body magic-ev-fncall ld-fn ld-fn0 ld-fn1 ld-fn-body
    eval-event-lst))

(defconst *fn-ocw-safe-return-last-keys*
  '(progn mbe1-raw ec-call1-raw with-guard-checking1-raw time$1-raw
    with-prover-time-limit1-raw with-prover-step-limit1-raw
    with-fast-alist-raw with-stolen-alist-raw fast-alist-free-on-exit-raw
    with-local-stobj-raw prog2$ throw-nonexec-error
    with-global-stobj-raw))

(mutual-recursion
 (defun fn-ocw-route (term)
   ; the first route TERM itself contains (not through callees), or nil
   (cond ((or (variablep term) (fquotep term)) nil)
         ((flambda-applicationp term)
          (or (fn-ocw-route (lambda-body (ffn-symb term)))
              (fn-ocw-route-list (fargs term))))
         (t (let ((fn (ffn-symb term)) (args (fargs term)))
              (or (and (member-eq fn '(put-global makunbound-global))
                       (consp args)
                       (if (fquotep (car args))
                           (and (member-eq (unquote (car args)) *fn-ocw-writer-globals*)
                                (list fn (unquote (car args))))
                         (list fn :non-literal-key)))
                  (and (member-eq fn *fn-ocw-evaluators*) (list :evaluator fn))
                  (and (eq fn 'return-last)
                       (consp args)
                       (not (and (fquotep (car args))
                                 (member-eq (unquote (car args))
                                            *fn-ocw-safe-return-last-keys*)))
                       (list :return-last (car args)))
                  (fn-ocw-route-list args))))))
 (defun fn-ocw-route-list (terms)
   (and (consp terms)
        (or (fn-ocw-route (car terms))
            (fn-ocw-route-list (cdr terms))))))

(defun fn-ocw-attachment (fn wrld)
  ; the function attached to FN, or nil.  The 'attachment property is the
  ; attached function, or (for a group) an alist on the group's first member
  ; and that member's name on the others.
  ; (:attachment-disallowed . why) and keywords mean none.
  (let ((att (getpropc fn 'attachment nil wrld)))
    (cond ((and (consp att) (eq (car att) :attachment-disallowed)) nil)
          ((consp att) (and (alistp att) (cdr (assoc-eq fn att))))
          ((and att (symbolp att) (not (keywordp att)))
           (let ((lead (getpropc att 'attachment nil wrld)))
             (if (and (consp lead) (alistp lead) (assoc-eq fn lead))
                 (cdr (assoc-eq fn lead))
               att)))
          (t nil))))

(defun fn-ocw-own-route (fn wrld)
  ; FN's own route (its body and guard), the unknown-body route, or nil
  (let ((body (getpropc fn 'unnormalized-body nil wrld))
        (g (getpropc fn 'guard *t* wrld)))
    (cond (body (or (fn-ocw-route body) (fn-ocw-route g)))
          ((assoc-eq fn *primitive-formals-and-guards*) nil)
          ((getpropc fn 'constrainedp nil wrld) nil) ; followed via attachment
          ((member-eq fn *fn-ocw-writer-globals*) nil)
          (t (list :no-body fn)))))

(defun fn-ocw-edges (fn wrld)
  (let* ((body (getpropc fn 'unnormalized-body nil wrld))
         (g (getpropc fn 'guard *t* wrld))
         (calls (fn-ocw-callees g (if body (fn-ocw-callees body nil) nil)))
         (att (fn-ocw-attachment fn wrld)))
    (if att (add-to-set-eq att calls) calls)))

(defun fn-ocw-reach (pending seen wrld)
  ; the call closure of PENDING, as a list
  (if (endp pending) seen
    (let ((fn (car pending)))
      (if (member-eq fn seen) (fn-ocw-reach (cdr pending) seen wrld)
        (fn-ocw-reach (append (fn-ocw-edges fn wrld) (cdr pending))
                      (cons fn seen) wrld)))))

(defun fn-ocw-seed (fns wrld acc)
  ; alist fn -> route for the functions of FNS with their own route
  (if (endp fns) acc
    (let ((r (fn-ocw-own-route (car fns) wrld)))
      (fn-ocw-seed (cdr fns) wrld (if r (acons (car fns) (list r) acc) acc)))))

(defun fn-ocw-first-writer (calls writers)
  (cond ((endp calls) nil)
        ((assoc-eq (car calls) writers) (car calls))
        (t (fn-ocw-first-writer (cdr calls) writers))))

(defun fn-ocw-grow (fns writers wrld changed)
  ; one pass: F becomes a writer when a callee is, with the callee as witness
  (if (endp fns) (mv writers changed)
    (let ((fn (car fns)))
      (if (assoc-eq fn writers) (fn-ocw-grow (cdr fns) writers wrld changed)
        (let ((hit (fn-ocw-first-writer (fn-ocw-edges fn wrld) writers)))
          (fn-ocw-grow (cdr fns)
                       (if hit (acons fn (cons hit (cdr (assoc-eq hit writers))) writers)
                         writers)
                       wrld (or changed (and hit t))))))))

(defun fn-ocw-fix (fuel fns writers wrld)
  (if (zp fuel) writers
    (mv-let (next changed) (fn-ocw-grow fns writers wrld nil)
      (if changed (fn-ocw-fix (1- fuel) fns next wrld) next))))

(defun fn-ocw-classify (names writers wrld)
  ; each name: (name :writer path) / (name :clear) / (name :undefined)
  (if (endp names) nil
    (let* ((fn (car names))
           (row (cond ((not (function-symbolp fn wrld)) (list fn :undefined))
                      ((assoc-eq fn writers)
                       (list fn :writer (symbol-class fn wrld)
                             (cons fn (cdr (assoc-eq fn writers)))))
                      (t (list fn :clear (symbol-class fn wrld))))))
      (cons row (fn-ocw-classify (cdr names) writers wrld)))))

(defun fn-ocw-function-symbols (names wrld)
  (cond ((endp names) nil)
        ((function-symbolp (car names) wrld)
         (cons (car names) (fn-ocw-function-symbols (cdr names) wrld)))
        (t (fn-ocw-function-symbols (cdr names) wrld))))

(defun fn-ocw-writer-census (names state)
  ; the census of NAMES in the loaded world
  (let* ((wrld (w state))
         (fns (fn-ocw-reach (fn-ocw-function-symbols names wrld) nil wrld))
         (writers (fn-ocw-fix (len fns) fns (fn-ocw-seed fns wrld nil) wrld)))
    (fn-ocw-classify names writers wrld)))

