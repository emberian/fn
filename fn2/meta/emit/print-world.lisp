; fn2/meta/emit/print-world.lisp: the printer of fn2's ACL2 world for the Lean side.
; Raw Lisp, loaded after the books are included and the loop is left (:q); never a
; certifying event (the pattern of fn2/tools/owed-export.lsp). Its one entry point,
; META-PRINT-WORLD, writes one S-expression with two parts:
;
;  (:registry ...)  every declaration table the forms write, row for row, in declaration
;                   order; the bulky keys whose values are event text (:generated
;                   :signature :reuse :definition) are printed as (:elided N) so the key stays
;                   visible to the emitter's key rule;
;  (:embed ...)     the closed subset (LEAN-METATHEORY section -1, item 2): for every kind
;                   declared in the step language, its arms with every expression AS
;                   DECLARED (the Lean side reads them itself, Fn2.Arms.readExpr, independently
;                   of the generator's rewrite fn2-arms-expr: LEAN-METATHEORY section 12,
;                   decision 7), each phase's value and every constant the arms name; the
;                   declared operations they name with their callees' signatures; and the
;                   function closure of the generated arm functions, the callees and the row
;                   readers and setters, each function's translated body, guard and measure. The closure is cut at the natives the
;                   Lean side implements (META-NATIVES); a function with no body that is not
;                   native is listed under :refused by name.
(in-package "ACL2")

(defvar *meta-w* (w *the-live-state*))
(defvar *meta-errors* nil)
; The world includes the assembly (reference.lisp): core-form kinds are printed, and the core
; children's initialisers translated (both name functions the assembly defines). A world short of
; it, such as a kind's own book, prints child-form kinds only and core children untranslated.
(defvar *meta-assembled* t)

(defparameter *meta-natives*
  '(if return-last equal cons car cdr consp integerp acl2-numberp rationalp symbolp stringp characterp coerce
    < binary-+ binary-* unary-- binary-logand binary-logior binary-logxor binary-logeqv lognot
    logorc1 floor mod evenp nonnegative-integer-quotient expt len nth mv-nth update-nth
    member-equal acl2-count))

(defun meta-err (fmt &rest args)
  (push (apply #'format nil fmt args) *meta-errors*)
  nil)

(defun meta-translate (x)
  (multiple-value-bind (erp val)
      (translate x '(nil) nil t 'fn2-meta *meta-w* *the-live-state*)
    (if erp (meta-err "translate failed on ~s" x) val)))

; ---------------------------------------------------------------- registry tables

(defparameter *meta-tables*
  '((:columns fn2-columns) (:machine-kinds fn2-machine-kinds) (:operation-sets fn2-operation-sets)
    (:core-children fn2-core-children) (:squares fn2-squares) (:correspondences fn2-correspondences)
    (:commands fn2-commands) (:costs fn2-costs) (:schemas fn2-schemas) (:ports fn2-ports)
    (:waits fn2-waits) (:layouts fn2-layouts) (:arm-contracts fn2-machine-arm-contracts)
    (:owed fn2-owed) (:core-instance fn2-core-instance)))
(defparameter *meta-elided* '(:generated :signature :reuse :definition))

(defun meta-elide (plist)
  (if (and (consp plist) (keywordp (car plist)) (consp (cdr plist)))
      (list* (car plist)
             (if (member (car plist) *meta-elided*)
                 (list :elided (if (true-listp (cadr plist)) (length (cadr plist)) 1))
               (cadr plist))
             (meta-elide (cddr plist)))
    plist))

; Terms where the vocabulary is closed: a row value that is an ACL2 term is printed translated,
; (:term T), so the Lean side carries a term, never printed text. A machine's :initial entry is
; (:function F) when it names an initialiser function, else the translated value.
(defun meta-translate-any (x)
  (handler-case
      (multiple-value-bind (erp val)
          (translate x t nil t 'fn2-meta *meta-w* *the-live-state*)
        (if erp (meta-err "translate failed on ~s" x) val))
    (cl:error (c) (meta-err "translate signalled on ~s: ~a" x c))))

(defun meta-term (x) (list :term (meta-translate-any x)))

(defun meta-put (key f plist)
  (if (and (consp plist) (consp (cdr plist)))
      (list* (car plist) (if (eq (car plist) key) (funcall f (cadr plist)) (cadr plist))
             (meta-put key f (cddr plist)))
    plist))

(defun meta-row-terms (key row)
  (case key
    (:machine-kinds
     (meta-put :capacity #'meta-term
       (meta-put :initial
                 (lambda (inits)
                   (loop for (field v) in inits
                         collect (list field (if (and (symbolp v) (function-symbolp v *meta-w*))
                                                 (list :function v)
                                               (meta-term v)))))
                 row)))
    (:core-children (if *meta-assembled* (meta-put :init #'meta-term (meta-put :profilep #'meta-term row)) row))
    (:costs (meta-put :bytes #'meta-term (meta-put :steps #'meta-term (meta-put :descriptors #'meta-term row))))
    (:squares (meta-put :translated (lambda (x) (list :term x)) row))
    (otherwise row)))

(defun meta-registry ()
  (cons :registry
        (loop for (key table) in *meta-tables*
              collect (list key (loop for (name . row) in (reverse (table-alist table *meta-w*))
                                      collect (cons name (meta-elide (meta-row-terms key row))))))))

; ---------------------------------------------------------------- step language

; An expression and a phase form are printed as the declaration writes them; the generator has
; already checked them (a kind certifies only if fn2-arms-expr accepts every one).
(defun meta-expr (e env) (declare (ignore env)) (list :raw e))

(defun meta-next (n env) (declare (ignore env)) (list :raw n))

(defun meta-kw (key plist) (let ((e (member key plist))) (and e (cadr e))))

(defun meta-split (args)
  ; (positional . keyword plist), as fn2-arms-split-call
  (if (or (atom args) (keywordp (car args))) (cons nil args)
    (let ((rest (meta-split (cdr args)))) (cons (cons (car args) (car rest)) (cdr rest)))))

(defun meta-call (call env)
  (let ((split (meta-split (cdr call))))
    (list :op (car call)
          :args (loop for a in (car split) collect (meta-expr a env))
          :keys (loop for (k v) on (cdr split) by #'cddr collect (list k (meta-expr v env))))))

(defun meta-charge-keys (args env keys)
  (loop for k in keys when (member k args) append (list k (meta-expr (meta-kw k args) env))))

(defun meta-steps (steps env)
  (loop for s in steps collect (meta-step s env)))

(defun meta-step (s env)
  (let ((args (cdr s)))
    (case (car s)
      (:let (list :let (car args) (meta-expr (cadr args) env)))
      (:set (cons :set (loop for (f e) in args collect (list f (meta-expr e env)))))
      (:next (list :next (meta-next (car args) env)))
      (:do
       (let* ((vars (car args)) (call (cadr args)) (opts (cddr args))
              (cases (meta-kw :case opts)))
         (append (list :do :vars vars) (meta-call call env)
                 (list :accept-given (and (member :accept opts) t) :accept (meta-kw :accept opts)
                       :effects (meta-kw :effects opts)
                       :when (let ((c (meta-kw :when opts))) (and c (meta-expr c env)))
                       :else (loop for e in (meta-kw :else opts) collect (list :raw e))
                       :case (loop for c in cases
                                   collect (cons (car c) (meta-steps (cdr c) env)))))))
      (:issue
       (append (list :issue) (meta-call (car args) env)
               (list :ok (meta-steps (meta-kw :ok (cdr args)) env)
                     :refused (meta-steps (meta-kw :refused (cdr args)) env))))
      (:repeat (list :repeat :n (meta-expr (car args) env) :steps (meta-steps (cadr args) env)
                     :until (meta-expr (meta-kw :until (cddr args)) env)))
      (:wake-row (list :wake-row (meta-expr (car args) env)))
      (:if (list :if (meta-expr (car args) env) (meta-steps (cadr args) env) (meta-steps (caddr args) env)))
      (:cond (cons :cond (loop for c in args
                               collect (cons (meta-expr (car c) env) (meta-steps (cdr c) env)))))
      (:case (list* :case (meta-expr (car args) env)
                    (loop for c in (cdr args) collect (cons (car c) (meta-steps (cdr c) env)))))
      (:charge (cons :charge (meta-charge-keys args env '(:bytes :steps :descriptors :runnable))))
      (:wait (list* :wait (car args) (meta-charge-keys (cdr args) env '(:bytes :steps))))
      (:park
       (let* ((wait (car args)) (argp (member wait '(:admission :pool :taken)))
              (rest (if argp (cddr args) (cdr args))))
         (list* :park wait
                (cond ((eq wait :taken) (list :kind (cadr args)))
                      (argp (list :arg (meta-expr (cadr args) env))))
                (meta-charge-keys rest env '(:steps)))))
      (:stop (list* :stop (car args) (meta-charge-keys (cdr args) env '(:steps))))
      ((:halt :idle :yield :wake :nowake) (list (car s)))
      (:goto (list :goto (car args)))
      (otherwise (meta-err "unknown step ~s" s)))))

(defun meta-sig (fn)
  ; a child-form function's (TAKES RETURNS RESULT-COUNT), when the generator narrowed it
  ; (machine-arms.lisp, fn2-arms-child-sigs); nil: it takes and returns the kind's whole tuple
  (cdr (assoc-eq fn (table-alist 'fn2-arms-child-sigs *meta-w*))))

(defun meta-entries (kind entries observe subs children)
  ; an arm table in child form (the arm over its children) or core form (over fn2-core)
  (loop for e in entries
        collect (multiple-value-bind (from refusal steps) (fn2-arms-options (cdr e))
                  (let ((env (fn2-arms-env kind (car e) observe refusal subs children *meta-w*))
                        (fn (fn2-arms-fn-name kind (if observe "-ON-" "-RUN-") (car e))))
                    (list (car e) :from from
                          :on-refusal (meta-steps refusal env)
                          :steps (meta-steps steps env)
                          :function (if children (fn2-arms-child-name fn) fn)
                          :sig (meta-sig (if children (fn2-arms-child-name fn) fn)))))))

(defun meta-sub-entries (kind entries children)
  (loop for e in entries
        collect (multiple-value-bind (from refusal steps) (fn2-arms-options (cdr e))
                  (declare (ignore from))
                  (let ((env (fn2-arms-env kind nil nil refusal nil children *meta-w*))
                        (fn (fn2-arms-fn-name kind "-SUB-" (car e))))
                    (list (car e) :from nil
                          :on-refusal (meta-steps refusal env)
                          :steps (meta-steps steps env)
                          :function (if children (fn2-arms-child-name fn) fn)
                          :sig (meta-sig (if children (fn2-arms-child-name fn) fn)))))))

(defun meta-child-form-p (kind)
  ; declared in the step language and its arms defined in child form in this world
  (let ((arms (fn2-machine-declared kind :arms *meta-w*)))
    (and arms
         (function-symbolp (fn2-arms-child-name (fn2-arms-fn-name kind "-RUN-" (caar arms))) *meta-w*))))

(defun meta-kind (kind)
  ; a kind declared in the step language: its arms in child form when the world defines them so,
  ; else in core form (whose functions take fn2-core: printed, never interpreted)
  (let ((children (meta-child-form-p kind)))
    (list kind
          :form (if children :children :core)
          :tuple (if children (fn2-arms-kind-tuple kind *meta-w*) '(fn2-core))
          :states (fn2-machine-property kind :states *meta-w*)
          :phases (loop for p in (fn2-machine-property kind :states *meta-w*)
                        collect (let ((v (getpropc (fn2-arms-phase-constant kind p) 'const nil *meta-w*)))
                                  (if (and (consp v) (integerp (cadr v))) (list p (cadr v))
                                    (meta-err "~s's phase ~s has no constant" kind p))))
          :columns (fn2-machine-property kind :columns *meta-w*)
          :table (fn2-machine-property kind :table *meta-w*)
          :stops (fn2-machine-declared kind :stops *meta-w*)
          :budget (fn2-machine-property kind :budget *meta-w*)
          :subarms (meta-sub-entries kind (fn2-machine-declared kind :subarms *meta-w*) children)
          :arms (meta-entries kind (fn2-machine-declared kind :arms *meta-w*) nil nil children)
          :observes (meta-entries kind (fn2-machine-declared kind :observe-arms *meta-w*) t nil children))))

; ---------------------------------------------------------------- operations

(defun meta-ops-in (x acc)
  ; every declared operation an arm names: :do, :issue and :park calls and pure calls in expressions
  (cond ((atom x) acc)
        ((and (symbolp (car x)) (fn2-arms-op-row (car x) *meta-w*))
         (meta-ops-in (cdr x) (adjoin (car x) acc)))
        (t (meta-ops-in (cdr x) (meta-ops-in (car x) acc)))))

(defun meta-op (op)
  (let* ((row (fn2-arms-op-row op *meta-w*)) (callee (fn2-decl-get :child row)))
    (list op :callee callee
          :formals (and callee (getpropc callee 'formals nil *meta-w*))
          :stobjs-in (and callee (getpropc callee 'stobjs-in nil *meta-w*))
          :stobjs-out (and callee (getpropc callee 'stobjs-out nil *meta-w*))
          :answers (fn2-decl-get :answers row) :descriptors (fn2-decl-get :descriptors row)
          :effects (fn2-decl-get :effects row) :own-writes (fn2-decl-get :own-writes row))))

; ---------------------------------------------------------------- the function closure

(defun meta-fns-of (x acc)
  (cond ((or (atom x) (eq (car x) 'quote)) acc)
        ((consp (car x)) (meta-fns-of-list (cdr x) (meta-fns-of (caddr (car x)) acc)))
        (t (meta-fns-of-list (cdr x) (adjoin (car x) acc)))))
(defun meta-fns-of-list (xs acc)
  (if (atom xs) acc (meta-fns-of-list (cdr xs) (meta-fns-of (car xs) acc))))

(defun meta-measure (f)
  (and (getpropc f 'recursivep nil *meta-w*)
       (access justification (getpropc f 'justification nil *meta-w*) :measure)))

(defun meta-closure (roots)
  ; (mv translated refused) in dependency order, callees first
  (let ((seen nil) (order nil) (refused nil))
    (labels ((visit (f)
               (unless (or (member f seen) (member f *meta-natives*))
                 (push f seen)
                 (let ((body (getpropc f 'unnormalized-body nil *meta-w*)))
                   (if (null body) (push f refused)
                     (progn
                       (dolist (g (meta-fns-of body nil)) (visit g))
                       (dolist (g (meta-fns-of (meta-measure f) nil)) (visit g))
                       (push f order)))))))
      (dolist (r roots) (visit r))
      ;; guards close over the same vocabulary; their functions join the closure
      (let ((more t))
        (loop while more do
          (setq more nil)
          (dolist (f order)
            (dolist (g (meta-fns-of (getpropc f 'guard nil *meta-w*) nil))
              (unless (or (member g seen) (member g *meta-natives*))
                (setq more t) (visit g)))))))
    (values (reverse order) (reverse refused))))

(defun meta-fn (f)
  (list f :formals (getpropc f 'formals nil *meta-w*)
        :body (getpropc f 'unnormalized-body nil *meta-w*)
        :guard (getpropc f 'guard nil *meta-w*)
        :measure (meta-measure f)
        :recursive (getpropc f 'recursivep nil *meta-w*)
        :stobjs-in (getpropc f 'stobjs-in nil *meta-w*)
        :stobjs-out (getpropc f 'stobjs-out nil *meta-w*)))

(defun meta-column-fns (stobj cols)
  (loop for (field) in cols
        append (list (fn2-columns-col-name stobj field)
                     (fn2-columns-col-name (fn2-columns-sym stobj "-SET") field))))

(defun meta-arm-functions (entries)
  (loop for e in entries collect (meta-kw :function (cdr e))))

(defun meta-constants (prefixes)
  (let ((out nil))
    (do-symbols (s (find-package "ACL2"))
      (when (and (eq (symbol-package s) (find-package "ACL2"))
                 (some (lambda (p) (let ((n (symbol-name s))) (and (>= (length n) (length p)) (string= p n :end2 (length p))))) prefixes)
                 (getpropc s 'const nil *meta-w*))
        (let ((v (getpropc s 'const nil *meta-w*)))
          (when (and (consp v) (eq (car v) 'quote) (integerp (cadr v)))
            (push (cons s (cadr v)) out)))))
    (sort out #'string< :key (lambda (p) (symbol-name (car p))))))

(defun meta-arm-constants (x acc)
  ; every *C* an arm names that the world defines as an integer constant
  (cond ((consp x) (meta-arm-constants (cdr x) (meta-arm-constants (car x) acc)))
        ((and (symbolp x) (not (keywordp x)) (eq (symbol-package x) (find-package "ACL2")))
         (let ((n (symbol-name x)) (v (getpropc x 'const nil *meta-w*)))
           (if (and (> (length n) 2) (char= (char n 0) #\*) (char= (char n (1- (length n))) #\*)
                    (consp v) (integerp (cadr v)) (not (assoc x acc)))
               (cons (cons x (cadr v)) acc)
             acc)))
        (t acc)))

(defun meta-embed ()
  (let* ((stepped (loop for (k) in (reverse (table-alist 'fn2-machine-kinds *meta-w*))
                        when (and (fn2-machine-declared k :arms *meta-w*)
                                  (or *meta-assembled* (meta-child-form-p k)))
                        collect k))
         (kinds (remove-if-not #'meta-child-form-p stepped))
         (kds (mapcar #'meta-kind stepped))
         (ops (let ((acc nil))
                (dolist (k stepped)
                  (setq acc (meta-ops-in (list (fn2-machine-declared k :subarms *meta-w*)
                                               (fn2-machine-declared k :arms *meta-w*)
                                               (fn2-machine-declared k :observe-arms *meta-w*))
                                         acc)))
                ;; the operations the generator calls without naming them in a step: the parks an
                ;; :issue's exhaustion or a (:park ...) reaches, and the declared waits' parkers
                (dolist (o (append '(fn2-machine-park fn2-machine-park-admission)
                                   (loop for (nil . row) in (table-alist 'fn2-waits *meta-w*)
                                         when (fn2-decl-get :park row) collect (fn2-decl-get :park row))
                                   (loop for (k) in (table-alist 'fn2-machine-kinds *meta-w*)
                                         when (fn2-machine-property k :taken *meta-w*)
                                         collect (fn2-columns-sym 'fn2-machine-park-taken- (symbol-name k)))))
                  (when (fn2-arms-op-row o *meta-w*) (setq acc (adjoin o acc))))
                (sort acc #'string< :key #'symbol-name)))
         (op-rows (mapcar #'meta-op ops))
         (roots (append
                 (loop for kd in kds
                       when (eq (meta-kw :form (cdr kd)) :children)
                       append (append (meta-arm-functions (meta-kw :subarms (cdr kd)))
                                      (meta-arm-functions (meta-kw :arms (cdr kd)))
                                      (meta-arm-functions (meta-kw :observes (cdr kd)))
                                      (meta-column-fns (car kd) (meta-kw :table (cdr kd)))))
                 (meta-column-fns 'fn2-machines *fn2-machine-directory-fields*)
                 (loop for o in op-rows when (meta-kw :callee (cdr o)) collect (meta-kw :callee (cdr o)))
                 '(fn2-control-record-stop fn2-control-record-kind-stop fn2-machines-park-pool
                   fn2-machines-wake-row fn2-machines-rows)
                 (loop for k in kinds collect (fn2-columns-sym k "-ROWS")))))
    (multiple-value-bind (order refused) (meta-closure roots)
      (list :embed
            (list :kinds kds)
            (list :operations op-rows)
            (list :natives *meta-natives*)
            (list :refused refused)
            (list :constants
                  (let ((cs (meta-constants '("*FN2-STOP-REASON-" "*FN2-WAIT-" "*FN2-WORK-" "*FN2-NONE*"))))
                    (dolist (k stepped)
                      (dolist (c (meta-arm-constants (list (fn2-machine-declared k :subarms *meta-w*)
                                                           (fn2-machine-declared k :arms *meta-w*)
                                                           (fn2-machine-declared k :observe-arms *meta-w*))
                                                     nil))
                        (unless (assoc (car c) cs) (push c cs))))
                    (sort cs #'string< :key (lambda (p) (symbol-name (car p))))))
            (list :functions (mapcar #'meta-fn order))
            ;; ACL2's own definitions of the natives that have one: the Lean side states that its
            ;; native agrees with each (Fn2.ACL2.Faithful)
            (list :native-definitions
                  (loop for f in *meta-natives*
                        when (getpropc f 'unnormalized-body nil *meta-w*) collect (meta-fn f)))))))

(defun meta-print-world (path)
  (setq *meta-errors* nil)
  (let* ((world (list :fn2-world (meta-registry) (meta-embed))))
    (if *meta-errors*
        (progn (dolist (e (reverse *meta-errors*)) (format t "~&META ERROR ~a~%" e))
               (format t "~&FN2-META-PRINT-WORLD FAILED~%"))
      (with-open-file (out path :direction :output :if-exists :supersede)
        (let ((*package* (find-package "ACL2")) (*print-case* :upcase) (*print-pretty* nil)
              (*print-length* nil) (*print-level* nil) (*print-escape* t) (*print-readably* nil)
              (*print-base* 10) (*print-radix* nil))
          (prin1 world out) (terpri out))
        (format t "~&FN2-META-PRINT-WORLD PASS ~a~%" path)))))
