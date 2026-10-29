; One carrier-parameterised emitter, below columns and machines.
(in-package "ACL2")
(include-book "declare")

(defun fn2-operation-find (name rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (or (cdr (assoc-eq name (fn2-decl-get :callbacks (cdar rows))))
        (fn2-operation-find name (cdr rows)))))
(defun fn2-operation-row (name world)
  (declare (xargs :verify-guards nil))
  (fn2-operation-find name (fn2-decl-all-rows world)))
(defun fn2-operation-register (owner name row events world)
  (declare (xargs :verify-guards nil))
  (let* ((row (if (eq (fn2-decl-get :returns row) :infer)
                   (fn2-decl-set :returns (getpropc name 'stobjs-out nil world) row) row))
         (old (fn2-decl-row owner world))
         (manifest (fn2-decl-manifests events :exported world))
         (artifact (fn2-decl-find-artifact name manifest)))
    `(table ,(fn2-decl-table (car owner)) ',(cadr owner)
       ',(fn2-decl-set :generated
           (append (list (list* (car artifact) name
                          (fn2-decl-set :section (fn2-decl-get :section row) (cddr artifact))))
                   (fn2-decl-get :generated old))
           (fn2-decl-set :callbacks
             (acons name row (fn2-decl-get :callbacks old)) old)))))
(defun fn2-operation-reuse (owner name world)
  (declare (xargs :verify-guards nil))
  (let ((row (fn2-decl-row owner world)))
    `(table ,(fn2-decl-table (car owner)) ',(cadr owner)
       ',(fn2-decl-set :reuse (cons (list :callback name) (fn2-decl-get :reuse row)) row))))
(defun fn2-operation-events (owner name carrier args returns row-vars section declaration body laws contracts)
  (declare (xargs :verify-guards nil))
  (let* ((formals (append args row-vars (list carrier)))
         (events `((defun ,name ,formals ,declaration ,@body) ,@laws))
         (row (list :args args :declared-returns returns :returns returns :row-bindings row-vars
                    :calling-convention formals :carrier carrier :owner owner
                    :writes (or (fn2-decl-get :writes contracts) :unchecked)
                    :cost (or (fn2-decl-get :cost contracts) :unchecked)
                    :refusal (or (fn2-decl-get :refusal contracts) :unchecked)
                    :section section :definition events)))
    `(make-event
      (let ((old (fn2-operation-row ',name (w state))))
        (cond ((not (fn2-decl-row ',owner (w state)))
               (er soft 'fn2-operation "Missing operation owner ~x0 for ~x1." ',owner ',name))
              (old (if (equal (fn2-decl-set :returns ',returns old) ',row) (value (fn2-operation-reuse ',owner ',name (w state)))
                     (er soft 'fn2-operation "Conflicting callback ~x0." ',name)))
              ((fn2-decl-conflicts ',events (fn2-decl-all-rows (w state)) (w state))
               (er soft 'fn2-operation "Conflicting definition ~x0." ',name))
              (t (value '(progn ,@events
                   (make-event
                    (value (fn2-operation-register ',owner ',name ',row ',events (w state))))))))))))
(defmacro fn2-defoperation (owner section returns definition)
  (let* ((formals (caddr definition)) (carrier (car (last formals))))
    (fn2-operation-events owner (cadr definition) carrier (butlast formals 1)
      returns nil section (cadddr definition) (cddddr definition) nil nil)))
