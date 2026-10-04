;;; tools/runtime_floor/extract.lisp -- export the executable definitions of a
;;; native image's full world as a plain Common Lisp system (lane
;;; runtime-floor, 2026-09-27).  A measurement/prototype: never loaded by a
;;; release build.
;;;
;;; Loaded into the DEVELOPER image's core (full world) started without ACL2's
;;; loop, in package ACL2.  The source of every exported definition is the
;;; form ACL2 itself installed in raw Lisp: the world's CLTL-COMMAND triples
;;; (add-trip's `(defun . def)', interface-raw.lisp 7251) for every event, and
;;; for the ACL2 system functions with #-acl2-loop-only code the raw branch of
;;; ACL2's own source files.  Macros are expanded here, in the session whose
;;; raw macros ACL2 used, so the target compiles CL special forms and CL
;;; macros only.  Nothing is rewritten by hand; what cannot be exported is
;;; listed (the inventory) and supplied by the target's runtime shim.
(in-package "ACL2")
(declaim (optimize (safety 3) (debug 1) (speed 0)))

(defvar *rf-defs* (make-hash-table :test 'eq))      ; name -> (defun name formals . body)
(defvar *rf-def-origin* (make-hash-table :test 'eq)) ; name -> :world | :source | :stobj
(defvar *rf-stobjs* nil)                            ; cltl defstobj/defabsstobj commands
(defvar *rf-log* nil)
(defvar *rf-inline* nil)

(defun rf-note (&rest args) (push args *rf-log*))

;;; ---------------------------------------------------------------------------
;;; 1. The world's raw definitions.

(defun rf-scan-world ()
  (let ((n 0) (seen-stobj (make-hash-table :test 'eq)))
    (dolist (trip (w *the-live-state*))
      (when (and (eq (car trip) 'cltl-command) (eq (cadr trip) 'global-value)
                 (consp (cddr trip)))
        (let ((cmd (cddr trip)))
          (case (car cmd)
            (defuns
             (let ((ignorep (caddr cmd)))
               (dolist (def (cdddr cmd))
                 ;; newest first: keep the first seen
                 (unless (or (gethash (car def) *rf-defs*)
                             (and ignorep (not (eq ignorep 'reclassifying))
                                  (not (and (consp ignorep) (eq (car ignorep) 'defstobj)))))
                   (incf n)
                   (setf (gethash (car def) *rf-defs*) (cons 'defun def)
                         (gethash (car def) *rf-def-origin*) :world)))))
            ((defstobj defabsstobj)
             (unless (gethash (cadr cmd) seen-stobj)
               (setf (gethash (cadr cmd) seen-stobj) t)
               (push cmd *rf-stobjs*)
               (when (eq (car cmd) 'defstobj)
                 (dolist (def (nth 4 cmd))
                   (let ((inl (member-equal *stobj-inline-declare* def)))
                     (unless (gethash (car def) *rf-defs*)
                       (when inl (push (car def) *rf-inline*))
                       (setf (gethash (car def) *rf-defs*)
                             (cons 'defun (if inl (remove-stobj-inline-declare def) def))
                             (gethash (car def) *rf-def-origin*) :stobj)))))))))))
    n))

;;; ---------------------------------------------------------------------------
;;; 2. ACL2's own raw definitions (the #-acl2-loop-only branch of its sources).

(defparameter *rf-acl2-source-files*
  '("axioms" "hons" "memoize" "serialize" "basis-a" "basis-b" "parallel"
    "translate" "type-set-a" "linear-a" "type-set-b" "linear-b" "non-linear"
    "tau" "rewrite" "simplify" "bdd" "other-processes" "induct" "prove"
    "defuns" "proof-builder-a" "history-management" "defthm" "other-events"
    "ld" "proof-builder-b" "proof-builder-pkg" "apply-prim" "apply-constraints"
    "apply" "interface-raw" "acl2-fns" "acl2-init" "hons-raw" "memoize-raw"
    "serialize-raw" "float-raw" "defpkgs" "boot-strap-pass-2-a"
    "boot-strap-pass-2-b" "futures-raw" "parallel-raw" "multi-threading-raw"
    "boot-strap-pass-2" "apply-raw" "file-system-support" "hons-raw"
    "fncall-raw" "type-set-a"))

(defparameter *rf-def-heads*
  '(defun defun-one-output defabbrev defun-inline defn defund defun-with-guard-check
    defun-overrides))

(defvar *rf-source-defs* (make-hash-table :test 'eq))

(defun rf-collect-source-form (form file)
  (when (consp form)
    (case (car form)
      ((progn eval-when when unless progn! let)
       (dolist (f (if (eq (car form) 'eval-when) (cddr form) (cdr form)))
         (rf-collect-source-form f file)))
      ((defun defun-one-output defabbrev)
       (when (symbolp (cadr form))
         ;; the LAST raw definition read wins, as loading would make it
         (setf (gethash (cadr form) *rf-source-defs*) (cons file form))))
      (t nil))))

(defun rf-read-acl2-sources (dir)
  (let ((*features* (remove :acl2-loop-only *features*))
        (*package* (find-package "ACL2"))
        (*read-eval* t) (count 0))
    (dolist (name (remove-duplicates *rf-acl2-source-files* :test 'equal))
      (let ((path (concatenate 'string dir name ".lisp")))
        (when (probe-file path)
          (with-open-file (in path :external-format :latin-1)
            (let ((*package* (find-package "ACL2")))
              (handler-case
                  (loop for form = (read in nil in)
                        until (eq form in)
                        do (incf count)
                           (when (and (consp form) (eq (car form) 'in-package))
                             (setq *package* (find-package (cadr form))))
                           (rf-collect-source-form form name))
                (error (c) (rf-note :source-read-error name (princ-to-string c)))))))))
    count))

;;; ---------------------------------------------------------------------------
;;; 3. The expander.  Non-CL macros are expanded in this session; CL special
;;; forms and CL macros are walked by their syntax; calls are recorded.

(defvar *rf-calls* nil)       ; hash: callee -> t, for the def being walked
(defvar *rf-globals* (make-hash-table :test (quote eq)))
(defvar *rf-nonportable* (make-hash-table :test (quote eq)))

(defun rf-cl-symbol-p (s)
  (and (symbolp s) (eq (symbol-package s) (find-package "COMMON-LISP"))))

(defun rf-sb-symbol-p (s)
  (and (symbolp s) (symbol-package s)
       (let ((p (package-name (symbol-package s))))
         (and (>= (length p) 3) (string= "SB-" p :end2 3)))))

(defun rf-note-var (s)
  (when (and (symbolp s) s (not (eq s t)) (not (keywordp s))
             (or (boundp s) (constantp s))
             (not (rf-cl-symbol-p s)))
    (setf (gethash s *rf-globals*) t)))

(defun rf-walk-body (forms) (mapcar #'rf-walk forms))

(defun rf-walk-decl (d)
  ;; (declare ...) : drop ACL2-only declaration kinds
  (if (and (consp d) (eq (car d) 'declare))
      (cons 'declare
            (remove-if (lambda (x) (and (consp x) (member (car x) '(xargs type-prescription))))
                       (cdr d)))
      (rf-walk d)))

(defun rf-walk-body-decls (forms)
  (mapcar (lambda (f) (if (and (consp f) (eq (car f) 'declare)) (rf-walk-decl f) (rf-walk f)))
          forms))

(defun rf-walk-lambda-list (ll)
  (mapcar (lambda (p) (if (and (consp p) (consp (cdr p)))
                          (list* (car p) (rf-walk (cadr p)) (cddr p))
                          p))
          ll))

(defun rf-walk-lambda (lam) ; (lambda ll . body)
  (list* (car lam) (rf-walk-lambda-list (cadr lam)) (rf-walk-body-decls (cddr lam))))

(defun rf-walk-bindings (bs)
  (mapcar (lambda (b) (if (consp b) (list* (car b) (mapcar #'rf-walk (cdr b))) b)) bs))

(defun rf-walk-fn-bindings (bs)
  (mapcar (lambda (b) (list* (car b) (rf-walk-lambda-list (cadr b)) (rf-walk-body-decls (cddr b)))) bs))

(defun rf-walk (form)
  (cond
    ((symbolp form) (rf-note-var form) form)
    ((atom form) form)
    ((and (consp (car form)) (eq (caar form) 'lambda))
     (cons (rf-walk-lambda (car form)) (rf-walk-body (cdr form))))
    ((not (symbolp (car form)))
     (rf-note :bad-head form) form)
    (t
     (let ((h (car form)))
       (case h
         (quote form)
         (function (if (and (consp (cadr form)) (eq (car (cadr form)) 'lambda))
                       (list 'function (rf-walk-lambda (cadr form)))
                       (progn (when (symbolp (cadr form)) (setf (gethash (cadr form) *rf-calls*) t))
                              form)))
         ((let let*) (list* h (rf-walk-bindings (cadr form)) (rf-walk-body-decls (cddr form))))
         ((flet labels) (list* h (rf-walk-fn-bindings (cadr form)) (rf-walk-body-decls (cddr form))))
         ((block return-from) (list* h (cadr form) (rf-walk-body (cddr form))))
         ((the) (list 'the (cadr form) (rf-walk (caddr form))))
         ((tagbody) (cons h (mapcar (lambda (f) (if (atom f) f (rf-walk f))) (cdr form))))
         ((go) form)
         ((declare) (rf-walk-decl form))
         ((locally) (cons h (rf-walk-body-decls (cdr form))))
         ((eval-when) (list* h (cadr form) (rf-walk-body (cddr form))))
         ((setq psetq) (cons h (loop for (v x) on (cdr form) by #'cddr
                                     do (rf-note-var v)
                                     append (list v (rf-walk x)))))
         ((macrolet symbol-macrolet)
          (rf-note :macrolet form)
          form)
         ((cond) (cons h (mapcar #'rf-walk-body (cdr form))))
         ((case ecase ccase typecase etypecase ctypecase)
          (list* h (rf-walk (cadr form))
                 (mapcar (lambda (c) (cons (car c) (rf-walk-body (cdr c)))) (cddr form))))
         ((multiple-value-bind destructuring-bind)
          (list* h (cadr form) (rf-walk (caddr form)) (rf-walk-body-decls (cdddr form))))
         ((dolist dotimes)
          (list* h (list* (car (cadr form)) (rf-walk-body (cdr (cadr form))))
                 (rf-walk-body-decls (cddr form))))
         ((do do*)
          (list* h (mapcar (lambda (b) (if (consp b) (cons (car b) (rf-walk-body (cdr b))) b)) (cadr form))
                 (rf-walk-body (caddr form))
                 (rf-walk-body-decls (cdddr form))))
         ((loop)
          (cons h (mapcar (lambda (x) (if (consp x) (rf-walk x) x)) (cdr form))))
         ((declaim proclaim check-type) form)
         (t
          (cond
            ((special-operator-p h)
             ;; if progn unwind-protect catch throw multiple-value-call
             ;; multiple-value-prog1 load-time-value progv ...
             (cons h (rf-walk-body (cdr form))))
            ((and (rf-cl-symbol-p h) (macro-function h))
             ;; when unless and or prog1 prog2 return incf decf push pop setf ...
             (unless (member h '(when unless and or prog1 prog2 return incf decf push pop
                                 setf psetf multiple-value-list multiple-value-setq
                                 nth-value assert error ignore-errors handler-case
                                 with-output-to-string))
               (rf-note :cl-macro h))
             (cons h (rf-walk-body (cdr form))))
            ((and (rf-sb-symbol-p h) (string= (symbol-name h) "QUASIQUOTE"))
             (rf-walk (macroexpand-1 form)))
            ((rf-sb-symbol-p h)
             (setf (gethash h *rf-nonportable*) t)
             (if (macro-function h)
                 (cond ((string= (symbol-name h) "TRULY-THE")
                        (list 'the (cadr form) (rf-walk (caddr form))))
                       (t (cons h (rf-walk-body (cdr form)))))
                 (progn (setf (gethash h *rf-calls*) t)
                        (cons h (rf-walk-body (cdr form))))))
            ((macro-function h)
             (rf-walk (macroexpand-1 form)))
            (t (setf (gethash h *rf-calls*) t)
               (cons h (rf-walk-body (cdr form)))))))))))

(defun rf-expand-def (def)
  ;; def = (defun name formals . body)
  (let ((*rf-calls* (make-hash-table :test 'eq)))
    (let ((out (list* 'defun (cadr def) (rf-walk-lambda-list (caddr def))
                      (rf-walk-body-decls (cdddr def)))))
      (values out (loop for k being the hash-keys of *rf-calls* collect k)))))

;;; ---------------------------------------------------------------------------
;;; 4. The closure from the roots, cut at the shimmed runtime.

(defparameter *rf-cut*
  ;; The error path, the evaluator, wormholes, printing: supplied by the
  ;; target runtime shim (they reach the prover statically, image-anatomy s.1).
  '(hard-error illegal er-cmp-fn error1 error1-safe interface-er
    throw-raw-ev-fncall throw-nonexec-error wormhole wormhole1 wormhole-eval
    wormhole-er fmt fms fmx fmt1 fmt-to-comment-window fmt-to-comment-window!
    fmt-to-comment-window+ fmt-to-comment-window!+ cw-print-base-radix
    ev-fncall ev-fncall-rec ev-fncall-w trans-eval translate translate1
    er-hard-val er-soft-val er-progn-fn print-call-history
    standard-co standard-oi record-error
    ;; wormhole undo (acts only inside a wormhole) and the error printer's
    ;; stobj renaming: shimmed
    push-wormhole-undo-formi replace-live-stobjs-in-list
    ;; hons and fast alists: shimmed by their logical definitions plus an
    ;; index (the values are the same alists); the memo tables (none of fn's
    ;; functions is memoized) and the world
    hons-acons hons-get hons-equal hons-assoc-equal fast-alist-free hons-copy
    hons memoize-flush1 w))

(defvar *rf-closure* (make-hash-table :test 'eq))  ; name -> expanded def
(defvar *rf-missing* (make-hash-table :test 'eq))  ; name -> first caller
(defvar *rf-cutmet* (make-hash-table :test 'eq))
(defvar *rf-star1* (make-hash-table :test 'eq))
(defvar *rf-parent* (make-hash-table :test 'eq))

(defun rf-predefined-p (name)
  (getpropc name 'predefined nil (w *the-live-state*)))

(defun rf-why (name)
  (loop for n = name then (gethash n *rf-parent*) while n collect n))

(defun rf-star1-p (s)
  (and (symbolp s) (symbol-package s)
       (let ((p (package-name (symbol-package s))))
         (and (> (length p) 9) (string= "ACL2_*1*_" p :end2 9)))))

(defun rf-raw-def (name)
  (let ((src (gethash name *rf-source-defs*)))
    (cond
      ((and src
            (or (member name (f-get-global 'logic-fns-with-raw-code *the-live-state*))
                (member name (f-get-global 'program-fns-with-raw-code *the-live-state*))
                (not (gethash name *rf-defs*))))
       (setf (gethash name *rf-def-origin*) (intern (string-upcase (car src)) "KEYWORD"))
       (let ((f (cdr src)))
         (if (eq (car f) 'defabbrev)
             (list* 'defun (cadr f) (caddr f) (cdddr f))
             (list* 'defun (cdr f)))))
      (t (gethash name *rf-defs*)))))

(defun rf-closure (roots)
  (let ((queue (copy-list roots)))
    (loop while queue do
      (let ((name (pop queue)))
        (unless (or (gethash name *rf-closure*) (gethash name *rf-missing*)
                    (gethash name *rf-cutmet*))
          (cond
            ((keywordp name) nil)
            ((member name *rf-cut*) (setf (gethash name *rf-cutmet*) t))
            ((rf-cl-symbol-p name) nil)
            ((rf-sb-symbol-p name) (setf (gethash name *rf-nonportable*) t))
            ((rf-star1-p name) (setf (gethash name *rf-star1*) t))
            (t
             (let ((def (rf-raw-def name)))
               (if (null def)
                   (setf (gethash name *rf-missing*) t)
                   (multiple-value-bind (out callees)
                       (handler-case (rf-expand-def def)
                         (error (c) (rf-note :expand-error name (princ-to-string c))
                           (values nil nil)))
                     (setf (gethash name *rf-closure*) (or out :failed))
                     (dolist (c callees)
                       (unless (gethash c *rf-parent*) (setf (gethash c *rf-parent*) name))
                       (push c queue))))))))))
    (hash-table-count *rf-closure*)))

;;; ---------------------------------------------------------------------------
;;; 5. Roots: every ACL2-package function symbol named in the host's raw
;;; Lisp (host/native/*.lisp), a token scan as lane image-anatomy's shake.

(defun rf-host-tokens (files)
  (let ((tokens (make-hash-table :test 'equal)))
    (dolist (f files)
      (with-open-file (in f :external-format :latin-1)
        (let ((buf (make-string-output-stream)))
          (flet ((flush ()
                   (let ((s (get-output-stream-string buf)))
                     (when (> (length s) 0) (setf (gethash (string-upcase s) tokens) t)))))
            (loop for ch = (read-char in nil nil) while ch do
              (if (or (alphanumericp ch) (find ch "-*$<>=/+!?%&_.")) (write-char ch buf) (flush)))
            (flush)))))
    tokens))

(defun rf-roots (files)
  (let ((roots nil) (tokens (rf-host-tokens files)))
    (loop for tok being the hash-keys of tokens do
      (let ((s (find-symbol tok "ACL2")))
        (when (and s (fboundp s) (not (macro-function s)) (not (rf-cl-symbol-p s))
                   (not (rf-predefined-p s))
                   (gethash s *rf-defs*))
          (push s roots))))
    roots))

;;; ---------------------------------------------------------------------------
;;; 6. Emission.  Every symbol is printed with its home package (*package* is
;;; a package that uses nothing), so the target defines packages by name.

(defvar *rf-print-package* (or (find-package "RF-PRINT") (make-package "RF-PRINT" :use nil)))

(defun rf-print (form stream)
  (let ((*package* *rf-print-package*)
        (*print-readably* t) (*print-circle* nil) (*print-pretty* nil)
        (*print-length* nil) (*print-level* nil) (*print-case* :upcase)
        (*print-base* 10) (*print-radix* nil) (*read-default-float-format* 'single-float))
    (prin1 form stream)
    (terpri stream)))

(defun rf-symbols-in (form acc)
  (cond ((symbolp form) (when (and form (symbol-package form)) (setf (gethash form acc) t)))
        ((consp form) (rf-symbols-in (car form) acc) (rf-symbols-in (cdr form) acc))
        ((and (vectorp form) (not (stringp form)))
         (loop for x across form do (rf-symbols-in x acc))))
  acc)

(defun rf-global-value-form (s)
  ;; a defconst or defvar/defparameter value, quoted
  (list 'quote (symbol-value s)))

;;; ---------------------------------------------------------------------------
;;; 7. The whole export.

(defun rf-attachment-roots ()
  ;; A constrained function's raw body funcalls the value of its *1* symbol
  ;; (the attachment, throw-or-attach): the attached functions are roots.
  (let ((roots nil))
    (loop for g being the hash-keys of *rf-globals*
          do (when (and (rf-star1-p g) (boundp g))
               (let ((v (symbol-value g)))
                 (when (and v (symbolp v) (fboundp v)) (push v roots)))))
    roots))

(defvar *rf-stobj-inits* nil) ; (live-name . expanded init form)

(defun rf-stobj-init-roots ()
  (let ((roots nil))
    (dolist (cmd *rf-stobjs*)
      (let ((*rf-calls* (make-hash-table :test 'eq)))
        (push (cons (nth 2 cmd) (rf-walk (nth 3 cmd))) *rf-stobj-inits*)
        (loop for k being the hash-keys of *rf-calls* do (push k roots))))
    roots))

(defvar *rf-star1-wrappers* (make-hash-table :test 'eq)) ; *1*f -> wrapper def

(defun rf-base-of-star1 (s)
  (let ((p (package-name (symbol-package s))))
    (find-symbol (symbol-name s) (subseq p 9))))

(defun rf-star1-wrapper (f)
  ;; The executable counterpart as the host's fnn-call and ACL2's ec-call see
  ;; it at the boundary: the declared guard, evaluated raw, then the raw
  ;; definition.  (ACL2's *1* runs the logic body instead of the raw one for
  ;; a function that is not guard-verified; that difference is named in the
  ;; inventory.)
  (let* ((wrld (w *the-live-state*))
         (formals (formals f wrld))
         (g (guard f nil wrld))
         (body (if (equal g *t*)
                   (cons f formals)
                   `(if ,g (,f ,@formals) (rf-guard-violation ',f (list ,@formals))))))
    (let ((*rf-calls* (make-hash-table :test 'eq)))
      (let ((def (list* 'defun (*1*-symbol f) formals
                        (list 'declare (list* 'ignorable formals))
                        (list (rf-walk body)))))
        (values def (loop for k being the hash-keys of *rf-calls* collect k))))))

(defun rf-quoted-star1 (form acc)
  (cond ((and (consp form) (eq (car form) 'quote) (symbolp (cadr form)) (rf-star1-p (cadr form)))
         (pushnew (cadr form) acc))
        ((consp form) (setq acc (rf-quoted-star1 (car form) acc)) (rf-quoted-star1 (cdr form) acc))
        (t acc)))

(defun rf-add-star1-wrappers (names)
  (let ((new-roots nil))
    (dolist (f names)
      (let ((s1 (*1*-symbol f)))
        (unless (or (gethash s1 *rf-star1-wrappers*)
                    (eq (getpropc f 'formals :none (w *the-live-state*)) :none))
          (handler-case
              (multiple-value-bind (def callees) (rf-star1-wrapper f)
                (setf (gethash s1 *rf-star1-wrappers*) def)
                (setq new-roots (append callees new-roots)))
            (error (c) (rf-note :star1-error f (princ-to-string c)))))))
    new-roots))

(defun rf-boundary-names (files)
  ;; every name the host can hand fnn-call: a token of host/native with an
  ;; executable counterpart, not ACL2's own
  (let ((names nil) (tokens (rf-host-tokens files)))
    (loop for tok being the hash-keys of tokens do
      (let ((s (find-symbol tok "ACL2")))
        (when (and s (not (rf-predefined-p s)) (not (rf-cl-symbol-p s))
                   (fboundp (*1*-symbol s)))
          (push s names))))
    names))

(defun rf-quoted-tokens (files)
  ;; tokens written 'NAME in the host's raw Lisp (fnn-core 'NAME ...)
  (let ((tokens (make-hash-table :test 'equal)))
    (dolist (f files)
      (with-open-file (in f :external-format :latin-1)
        (let ((prev nil) (buf nil))
          (loop for ch = (read-char in nil nil) while ch do
            (cond (buf (if (or (alphanumericp ch) (find ch "-*$<>=/+!?%&_."))
                           (vector-push-extend ch buf)
                           (progn (setf (gethash (string-upcase buf) tokens) t) (setq buf nil))))
                  ((and (eql prev #\') (or (alphanumericp ch) (find ch "-*$")))
                   (setq buf (make-array 1 :element-type 'character :adjustable t :fill-pointer 1
                                           :initial-element ch))))
            (setq prev ch)))))
    tokens))

(defun rf-predefined-boundary (files)
  (let ((names nil))
    (loop for tok being the hash-keys of (rf-quoted-tokens files) do
      (let ((s (find-symbol tok "ACL2")))
        (when (and s (rf-predefined-p s) (not (rf-cl-symbol-p s))
                   (fboundp (*1*-symbol s))
                   (eq (getpropc s 'symbol-class nil (w *the-live-state*)) :common-lisp-compliant))
          (push s names))))
    names))

(defvar *rf-boundary* nil)

(defun rf-host-constants (files)
  ;; the defconsts host/native's raw Lisp names itself (e.g. *fn-lg-genesis*)
  (let ((n 0))
    (loop for tok being the hash-keys of (rf-host-tokens files) do
      (let ((s (find-symbol tok "ACL2")))
        (when (and s (boundp s) (not (rf-cl-symbol-p s))
                   ;; fn's own (a token in a comment can name ACL2's xdoc)
                   (> (length tok) 4) (string= "*FN-" tok :end2 4)
                   (getpropc s 'const nil (w *the-live-state*)))
          (incf n)
          (setf (gethash s *rf-globals*) t))))
    n))

(defun rf-full-closure (roots)
  (rf-closure roots)
  (rf-closure (rf-add-star1-wrappers *rf-boundary*))
  (loop
    (let ((before (hash-table-count *rf-closure*)))
      (rf-closure (append (rf-attachment-roots) (rf-stobj-init-roots)))
      (let ((targets nil))
        (loop for v being the hash-values of *rf-closure*
              do (when (consp v) (setq targets (rf-quoted-star1 v targets))))
        (rf-closure (rf-add-star1-wrappers (remove nil (mapcar #'rf-base-of-star1 targets)))))
      (setq *rf-stobj-inits* (remove-duplicates *rf-stobj-inits* :key #'car :from-end t))
      (when (= before (hash-table-count *rf-closure*)) (return))))
  ;; the wrappers are definitions like any other
  (maphash (lambda (k v) (setf (gethash k *rf-closure*) v (gethash k *rf-def-origin*) :star1))
           *rf-star1-wrappers*)
  (hash-table-count *rf-closure*))

(defun rf-size (x limit)
  ;; objects reachable (tree walk, no sharing check), stopping past LIMIT
  (let ((n 0))
    (labels ((walk (y)
               (when (> n limit) (return-from rf-size n))
               (incf n)
               (cond ((consp y) (walk (car y)) (walk (cdr y)))
                     ((and (arrayp y) (not (stringp y)) (eq (array-element-type y) t))
                      (loop for z across (make-array (array-total-size y) :displaced-to y) do (walk z))))))
      (walk x))
    n))

(defun rf-printable-p (v)
  (when (> (rf-size v 2000000) 2000000)
    (rf-note :huge-global)
    (return-from rf-printable-p nil))
  (handler-case (progn (let ((*print-readably* t) (*print-circle* t) (*package* *rf-print-package*))
                         (prin1-to-string v))
                       t)
    (error () nil)))

(defun rf-emit-to (path forms)
  (with-open-file (out path :direction :output :if-exists :supersede :external-format :latin-1)
    (let ((*package* *rf-print-package*)
          ;; not *print-readably*: SBCL writes base strings as #A((n) BASE-CHAR . "s")
          (*print-readably* nil) (*print-escape* t) (*print-circle* t) (*print-pretty* nil)
          (*print-array* t)
          (*print-length* nil) (*print-level* nil) (*print-case* :upcase)
          (*print-base* 10) (*print-radix* nil))
      (format out ";;; generated by tools/runtime_floor/extract.lisp; do not edit~%")
      ;; ACL2's own compilation policy (acl2.lisp *acl2-optimize-form*), per
      ;; file so that every target compiles the definitions as ACL2 did
      (format out "(COMMON-LISP:DECLAIM (COMMON-LISP:OPTIMIZE (COMMON-LISP:COMPILATION-SPEED 0) (COMMON-LISP:SPEED 3) (COMMON-LISP:SPACE 1) (COMMON-LISP:SAFETY 0)))~%")
      (dolist (f forms) (prin1 f out) (terpri out)))))

(defun rf-emit (dir &key (chunk 300))
  (let* ((defs (sort (loop for k being the hash-keys of *rf-closure* using (hash-value v)
                           when (consp v) collect v)
                     #'string< :key (lambda (d) (symbol-name (cadr d)))))
         (syms (make-hash-table :test 'eq))
         (globals nil) (unprintable nil) (packages nil))
    ;; globals: defconsts, defvars, attachment variables, live stobjs
    (loop for g being the hash-keys of *rf-globals* do
      (unless (or (member g '(*the-live-state*)) (not (boundp g))
                  (member g *rf-stobj-inits* :key #'car))
        (if (progn (format t "~&RF-GLOBAL ~s~%" g) (finish-output) (rf-printable-p (symbol-value g)))
            ;; rf-fresh: a runtime copy of any array in the value (ACL2's
            ;; raw globals such as *inside-absstobj-update* are mutated in
            ;; place; a quoted literal would be a constant, read-only once a
            ;; core is saved)
            (push (list 'defparameter g (list 'rf-fresh (list 'quote (symbol-value g)))) globals)
            (progn (push g unprintable)
                   (push (list 'defvar g) globals)))))
    (dolist (d defs) (rf-symbols-in d syms))
    ;; state globals the code names (f-get-global expands to the global symbol)
    (loop for s being the hash-keys of syms
          do (when (and (symbol-package s)
                        (let ((p (package-name (symbol-package s))))
                          (and (> (length p) 12) (string= "ACL2_GLOBAL_" p :end2 12)))
                        (boundp s))
               (if (rf-printable-p (symbol-value s))
                   (push (list 'defparameter s (list 'quote (symbol-value s))) globals)
                   (push s unprintable))))
    (dolist (g globals) (rf-symbols-in g syms))
    (dolist (i *rf-stobj-inits*) (rf-symbols-in i syms))
    (loop for s being the hash-keys of syms
          do (let ((p (symbol-package s)))
               (when p (pushnew (package-name p) packages :test 'equal))))
    (setq packages (sort (remove-if (lambda (p) (member p '("COMMON-LISP" "KEYWORD") :test 'equal)) packages)
                         #'string<))
    ;; 00: packages, then each ACL2 package's imports of the symbols we use
    (rf-emit-to (concatenate 'string dir "00-packages.lisp")
                (append
                 (mapcar (lambda (p) `(unless (find-package ,p) (make-package ,p :use nil))) packages)
                 (loop for p in packages
                       for entry = (assoc-equal p (known-package-alist *the-live-state*))
                       when entry
                         collect `(import ',(package-entry-imports entry) ,p))
                 (let ((imports nil))
                   (loop for s being the hash-keys of syms
                         do (dolist (p packages)
                              (unless (equal p (package-name (symbol-package s)))
                                (multiple-value-bind (found how) (find-symbol (symbol-name s) p)
                                  (when (and (eq found s) (member how '(:internal :external)))
                                    (push `(import ',s ,p) imports))))))
                   imports)))
    ;; ACL2's own function-type proclamations (add-trip's declaim-p: the
    ;; ftype ACL2 proclaims for a definition with type declarations), so
    ;; the target compiles callers with the same knowledge ACL2's did
    (let ((ftypes nil))
      (dolist (d defs)
        (let ((f (cadr d)))
          (when (eq (sb-int:info :function :where-from f) :declared)
            (push `(declaim (ftype ,(sb-kernel:type-specifier (sb-int:info :function :type f)) ,f))
                  ftypes))))
      (format t "~&RF-EMIT ftype proclamations ~d~%" (length ftypes))
      (rf-emit-to (concatenate 'string dir "01-ftypes.lisp") (nreverse ftypes)))
    ;; ACL2's inline proclamations (install-defs-for-add-trip: a name ending
    ;; in $INLINE is proclaimed inline, $NOTINLINE notinline; a stobj's
    ;; inline accessors), and the inline definitions compiled first, so that
    ;; every caller is compiled with the expansion as ACL2's were
    (let* ((inl (remove-duplicates
                 (append (remove-if-not (lambda (n) (gethash n *rf-closure*)) *rf-inline*)
                         (loop for d in defs
                               for n = (symbol-name (cadr d))
                               when (and (> (length n) 7) (string= "$INLINE" n :start2 (- (length n) 7)))
                                 collect (cadr d)))))
           (notinl (loop for d in defs
                         for n = (symbol-name (cadr d))
                         when (and (> (length n) 10) (string= "$NOTINLINE" n :start2 (- (length n) 10)))
                           collect (cadr d))))
      (format t "~&RF-EMIT inline ~d notinline ~d~%" (length inl) (length notinl))
      (rf-emit-to (concatenate 'string dir "01-inline.lisp")
                  (append (list `(declaim (inline ,@inl)) `(declaim (notinline ,@notinl)))
                          (remove-if-not (lambda (d) (member (cadr d) inl)) defs)))
      (setq defs (remove-if (lambda (d) (member (cadr d) inl)) defs)))
    (rf-emit-to (concatenate 'string dir "01-globals.lisp")
                (append (list)
                        (reverse globals)))
    (loop for i from 0
          for start from 0 by chunk
          while (< start (length defs))
          do (rf-emit-to (format nil "~a02-defs-~3,'0d.lisp" dir i)
                         (subseq defs start (min (length defs) (+ start chunk)))))
    ;; the boundary's STOBJS-IN (host/native/io.lisp fnn-trailing-kind reads
    ;; it from the world, which the plain system does not have)
    (rf-emit-to (concatenate 'string dir "01-stobjs-in.lisp")
                (list `(defparameter *rf-stobjs-in*
                         ',(loop for f in *rf-boundary*
                                 collect (cons f (stobjs-in f (w *the-live-state*)))))))
    (rf-emit-to (concatenate 'string dir "03-stobjs.lisp")
                (append
                 (mapcar (lambda (i) `(defparameter ,(car i) ,(cdr i))) (reverse *rf-stobj-inits*))
                 (list `(defparameter *rf-user-stobj-alist*
                          (list ,@(mapcar (lambda (p) `(cons ',(car p) ,(let ((cmd (find (car p) *rf-stobjs* :key #'cadr)))
                                                                           (nth 2 cmd))))
                                          (user-stobj-alist *the-live-state*)))))))
    (format t "~&RF-EMIT defs ~d globals ~d unprintable ~d packages ~d~%" (length defs) (length globals)
            (length unprintable) (length packages))
    (format t "~&RF-EMIT unprintable: ~{~s ~}~%" unprintable)
    (length defs)))
