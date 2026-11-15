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

; Guarded producer interfaces use the stored logical guard (including its
; implicit input stobj predicates). Every emitted fact still requires proof.
; Optional row frames are unconditional, as in the underlying constructor.
(defun fn2-columns-guard-domain-specs (specs)
 (declare (xargs :verify-guards nil))
 (if (atom specs) nil
  (cons (cons (concatenate 'string (caar specs) "-UNDER-GUARD")
              (cdar specs))
        (fn2-columns-guard-domain-specs (cdr specs)))))
(defun fn2-columns-carrier-row-specs (carriers)
 (declare (xargs :verify-guards nil))
 (if (atom carriers) nil
  (cons (list (concatenate 'string
                (or (fn2-decl-get :prefix (cddar carriers)) "") "-ROWS")
              (fn2-columns-sym (caar carriers) "-ROWS") (cadar carriers)
              :frame (caar carriers))
        (fn2-columns-carrier-row-specs (cdr carriers)))))
(defun fn2-columns-guarded-contract-events (name carriers hints rows world)
 (declare (xargs :verify-guards nil))
 (let* ((args (getpropc name 'formals :missing world))
        (inputs (getpropc name 'stobjs-in nil world))
        (outputs (getpropc name 'stobjs-out nil world))
        (guard (getpropc name 'guard :missing world)))
  (if (or (eq args :missing) (eq guard :missing)
          (eq (getpropc name 'symbol-class nil world) :program)
          (not carriers)
          (not (fn2-columns-contract-carriersp carriers args inputs outputs world)))
      (er hard 'defcolumns-guarded-contracts
          "No logical guarded carrier projection for ~x0." name)
   (let* ((hyps (remove-duplicates-equal
                  (append (fn2-columns-carrier-hyps carriers)
                    (fn2-columns-readonly-type-hyps args inputs nil world)
                    (list guard))))
          (specs (fn2-columns-guard-domain-specs
                   (fn2-columns-carrier-specs
                    (fn2-columns-inherit-carrier-hints carriers hints)))))
    (fn2-columns-preserves
     (caar carriers) name args nil hyps
     (append specs (and rows (fn2-columns-carrier-row-specs carriers)))
     "-PRESERVES" t t hints t nil nil nil nil)))))
(defmacro defcolumns-guarded-contracts (name &key carriers hints rows)
 `(make-event
   (value (fn2-columns-guarded-contract-events
           ',name ',carriers ',hints ',rows (w state)))))

; Scalar metadata observations must see existing raw NTH frame rules, while
; scalar updaters stay named so their public TYPE/WFP/ROWS rules can fire.
(defun fn2-columns-scalar-extra-runes (fields writers)
 (declare (xargs :verify-guards nil))
 (if (atom fields) nil
  (append
   (and (not (fn2-columns-arrayp (car fields)))
        (fn2-columns-numeric-fieldp (car fields))
        (list (if writers (fn2-columns-pre "UPDATE-" (caar fields))
                (caar fields))))
   (fn2-columns-scalar-extra-runes (cdr fields) writers))))
(defun fn2-columns-table-scalar-runes (tables writers world)
 (declare (xargs :verify-guards nil))
 (if (atom tables) nil
  (append
   (fn2-columns-scalar-extra-runes
    (fn2-decl-get :extra-fields (fn2-decl-row (list :columns (car tables)) world))
    writers)
   (fn2-columns-table-scalar-runes (cdr tables) writers world))))
(defun fn2-columns-scalar-frame-hint (tables producers opaque world)
 (declare (xargs :verify-guards nil))
 (fn2-columns-guard-hint tables
  (append opaque (fn2-columns-type-predicates tables)
          (fn2-columns-table-scalar-runes tables t world))
  (append producers (fn2-columns-table-scalar-runes tables nil world)) world))
