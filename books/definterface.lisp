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
;     [:direct "why"])              ; the raw host applies it directly, not
;                                   ; through fnn-call's entry guard
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
;     the logic functions it runs).
;
; and then records the declaration in the table `fn-interfaces'.  A failed
; check is a soft error naming the entry and the check.  The registry half
; is tools/interface_emit.py, which reads the same forms without evaluating
; them and generates planning/interfaces.json and tools/extract/roots.sh; its
; host-binding check reads the raw host itself (a declared entry the host
; never dispatches is stale; see that tool).
;
; This book has no include-book and leaves no rule: its helpers are
; :program mode.  *fn-entry-guard-kinds* is read from the world
; (books/payload-kinds.lisp), not included, so the file that holds the
; declarations decides what is loaded.

(in-package "ACL2")

(defconst *fn-di-keys* '(:class :kinds :exempt :keystones :root :direct :delegates))

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
     (t nil))))

(defun fn-di-refusal-text (reason)
  (declare (xargs :mode :program))
  (case (car reason)
    (:bad-class (msg ":class ~x0 is not one of ~&1." (cadr reason) *fn-di-classes*))
    (:unknown-keyword (msg "unknown keyword(s) ~&0; the keywords are ~&1."
                           (cdr reason) *fn-di-keys*))
    (:bad-root (msg ":root ~x0 is not :extract or :extract-extra." (cadr reason)))
    (:bad-delegates (msg ":delegates ~x0 is not a function name." (cadr reason)))
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
