; Opt-in carrier facets over the actual function's typed readonly inputs.
(in-package "ACL2")
(include-book "columns-guard-hints")
(fn2-book-layer :b)

(defun fn2-columns-readonly-type-hyps (args inputs outputs world)
 (declare (xargs :verify-guards nil))
 (if (atom args) nil
  (append
   (if (and (car inputs) (not (member-eq (car inputs) outputs)))
       (if (fn2-decl-row (list :columns (car inputs)) world)
           (list (list (fn2-columns-sym (car inputs) "P") (car args)))
         (er hard 'defcolumns-carrier-contracts
             "Readonly input ~x0 has no column metadata." (car inputs)))
     nil)
   (fn2-columns-readonly-type-hyps (cdr args) (cdr inputs) outputs world))))

(defun fn2-columns-contract-carriersp (carriers args inputs outputs world)
 (declare (xargs :verify-guards nil))
 (if (atom carriers) (null carriers)
  (let* ((table (caar carriers)) (position (cadar carriers))
         (at (if position position 0)))
   (and (consp (car carriers)) (natp at)
        (if position (< at (len outputs)) (equal (len outputs) 1))
        (eq table (nth at outputs))
        (member-eq table inputs) (member-eq table args)
        (fn2-decl-row (list :columns table) world)
        (not (member-eq table (strip-cars (cdr carriers))))
        (fn2-columns-contract-carriersp (cdr carriers) args inputs outputs world)))))

(defun fn2-columns-inherit-carrier-hints (carriers hints)
 (declare (xargs :verify-guards nil))
 (if (atom carriers) nil
  (cons (if (or (not hints) (member-eq :hints (cddar carriers)))
            (car carriers)
          (append (car carriers) (list :hints hints)))
        (fn2-columns-inherit-carrier-hints (cdr carriers) hints))))

(defun fn2-columns-type-predicates (tables)
 (declare (xargs :verify-guards nil))
 (if (atom tables) nil
  (cons (fn2-columns-sym (car tables) "P")
        (fn2-columns-type-predicates (cdr tables)))))

(defun fn2-columns-readonly-type-specs (specs predicates hyps)
 (declare (xargs :verify-guards nil))
 (if (atom specs) nil
  (cons
   (if (member-eq (cadar specs) predicates)
       (append (list (concatenate 'string (caar specs) "-UNDER-READONLY-TYPES")
                     (cadar specs) (caddar specs))
               (cdddar specs) (list :hyps hyps))
     (car specs))
   (fn2-columns-readonly-type-specs (cdr specs) predicates hyps))))

(defun fn2-columns-carrier-contract-events (name carriers typed-readonly hints world)
 (declare (xargs :verify-guards nil))
 (let* ((args (getpropc name 'formals :missing world))
        (inputs (getpropc name 'stobjs-in nil world))
        (outputs (getpropc name 'stobjs-out nil world)))
  (if (or (eq args :missing)
          (eq (getpropc name 'symbol-class nil world) :program)
          (not carriers)
          (not (fn2-columns-contract-carriersp carriers args inputs outputs world))
          (not (subsetp-eq typed-readonly (strip-cars carriers))))
      (er hard 'defcolumns-carrier-contracts
          "Carrier projections do not match actual function ~x0." name)
   (let* ((readonly (fn2-columns-readonly-type-hyps args inputs outputs world))
          (hyps (fn2-columns-carrier-hyps carriers))
          (specs (fn2-columns-carrier-specs
                  (fn2-columns-inherit-carrier-hints carriers hints)))
          (typed (fn2-columns-type-predicates typed-readonly)))
    (if (and typed (not readonly))
        (er hard 'defcolumns-carrier-contracts
            "Function ~x0 has no readonly input type domain." name)
     (fn2-columns-preserves
      (caar carriers) name args nil hyps
      (fn2-columns-readonly-type-specs specs typed (append hyps readonly))
      "-PRESERVES" t t hints t nil nil nil nil))))))

(defmacro defcolumns-carrier-contracts
 (name &key carriers typed-readonly hints)
 `(make-event
   (value (fn2-columns-carrier-contract-events
           ',name ',carriers ',typed-readonly ',hints (w state)))))
