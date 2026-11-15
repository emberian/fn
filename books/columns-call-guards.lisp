; Call-derived guard proof boundaries over public column interfaces.
(in-package "ACL2")
(include-book "columns-guard-hints")
(fn2-book-layer :b)

; A guard proof knows its actual admitted signature and translated body. Use
; that boundary rather than maintaining a reader list at every call site.
(defun fn2-columns-input-tables (inputs world)
 (declare (xargs :verify-guards nil))
 (if (atom inputs) nil
  (append (and (car inputs)
               (fn2-decl-row (list :columns (car inputs)) world)
               (list (car inputs)))
          (fn2-columns-input-tables (cdr inputs) world))))
(defun fn2-columns-framed-callees (callees tables world)
 (declare (xargs :verify-guards nil))
 (if (atom callees) nil
  (let ((fn (car callees)))
   (append
    (and (intersectp-eq tables (getpropc fn 'stobjs-out nil world))
         (getpropc (fn2-columns-sym fn "-PRESERVES-TYPE") 'theorem nil world)
         (getpropc (fn2-columns-sym fn "-PRESERVES-WFP") 'theorem nil world)
         (list fn))
    (fn2-columns-framed-callees (cdr callees) tables world)))))
; A read after a public setter needs the getter open so the existing setter
; -NTH frame and raw-reader NATP/BOUND rules can meet. Do not emit a quadratic
; getter/setter theorem matrix or open every reader used by the caller.
(defun fn2-columns-observation-interfaces-1 (table columns world)
 (declare (xargs :verify-guards nil))
 (if (atom columns) nil
  (let* ((reader (fn2-columns-col-name table (caar columns)))
         (writer (fn2-columns-col-name table (fn2-columns-pre "SET-" (caar columns)))))
   (append
    (and (getpropc reader 'unnormalized-body nil world)
         (getpropc writer 'unnormalized-body nil world)
         (not (eq (getpropc reader 'symbol-class nil world) :program))
         (not (eq (getpropc writer 'symbol-class nil world) :program))
         (equal (getpropc reader 'stobjs-in :missing world) (list nil table))
         (equal (getpropc reader 'stobjs-out :missing world) '(nil))
         (equal (getpropc writer 'stobjs-in :missing world) (list nil nil table))
         (equal (getpropc writer 'stobjs-out :missing world) (list table))
         (getpropc (fn2-columns-sym writer "-NTH") 'theorem nil world)
         (list (list reader writer table)))
    (fn2-columns-observation-interfaces-1 table (cdr columns) world)))))
(defun fn2-columns-observation-interfaces (tables world)
 (declare (xargs :verify-guards nil))
 (if (atom tables) nil
  (append (fn2-columns-observation-interfaces-1 (car tables)
           (fn2-decl-get :columns (fn2-decl-row (list :columns (car tables)) world)) world)
          (fn2-columns-observation-interfaces (cdr tables) world))))
(defun fn2-columns-observation-writer (fn interfaces)
 (declare (xargs :verify-guards nil))
 (if (atom interfaces) nil
  (if (eq fn (cadar interfaces)) (caddar interfaces)
   (fn2-columns-observation-writer fn (cdr interfaces)))))

; Track only table provenance, not copied terms. Translated LET/MV bindings
; are lambda applications; retain lexical shadowing without beta-expanding
; potentially large state expressions. Unknown producers yield no provenance.
(mutual-recursion
 (defun fn2-columns-observation-scan (term bindings interfaces fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (cond ((zp fuel) (mv nil nil))
        ((atom term) (mv nil (cdr (assoc-eq term bindings))))
        ((eq (car term) 'quote) (mv nil nil))
        (t
         (mv-let (readers arguments)
          (fn2-columns-observation-scan-list (cdr term) bindings interfaces (1- fuel))
          (cond
           ((and (consp (car term)) (eq (caar term) 'lambda)
                 (equal (len (car term)) 3)
                 (equal (len (cadar term)) (len arguments)))
            (mv-let (more result)
             (fn2-columns-observation-scan (caddar term)
              (append (pairlis$ (cadar term) arguments) bindings) interfaces (1- fuel))
             (mv (union-eq readers more) result)))
           ((consp (car term)) (mv readers nil))
           (t
            (let* ((reader (assoc-eq (car term) interfaces))
                   (writer (fn2-columns-observation-writer (car term) interfaces))
                   (selected (and reader (equal (len arguments) 2)
                              (member-eq (caddr reader) (cadr arguments)))))
             (mv (if selected (union-eq (list (car term)) readers) readers)
                 (cond ((and writer (equal (len arguments) 3)) (list writer))
                       ((and (eq (car term) 'if) (equal (len arguments) 3))
                        (union-eq (cadr arguments) (caddr arguments)))
                       (t nil))))))))))
 (defun fn2-columns-observation-scan-list (terms bindings interfaces fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (atom terms)) (mv nil nil)
   (mv-let (readers first)
    (fn2-columns-observation-scan (car terms) bindings interfaces (1- fuel))
    (mv-let (more rest)
     (fn2-columns-observation-scan-list (cdr terms) bindings interfaces (1- fuel))
     (mv (union-eq readers more) (cons first rest)))))))
(defun fn2-columns-postwrite-readers (name tables world)
 (declare (xargs :verify-guards nil))
 (mv-let (readers provenance)
  (fn2-columns-observation-scan (getpropc name 'unnormalized-body nil world)
   nil (fn2-columns-observation-interfaces tables world) 10000)
  (declare (ignore provenance)) readers))

; RAW-NTH facts state the row bound using (nth ROWS-INDEX table). Pair a
; selected observer with its own ROWS definition so an opaque (< i (ROWS
; table)) hypothesis matches that public frame interface. Other tables' ROWS
; stay closed. A missing scalar ABI is not guessed.
(defun fn2-columns-observation-row-runes (readers interfaces world)
 (declare (xargs :verify-guards nil))
 (if (atom readers) nil
  (let* ((table (caddr (assoc-eq (car readers) interfaces)))
         (rows (and table (fn2-columns-sym table "-ROWS"))))
   (union-eq
    (and rows
         (equal (getpropc rows 'stobjs-in :missing world) (list table))
         (equal (getpropc rows 'stobjs-out :missing world) '(nil))
         (list rows))
    (fn2-columns-observation-row-runes (cdr readers) interfaces world)))))
(defun fn2-columns-postwrite-runes (name tables opaque world)
 (declare (xargs :verify-guards nil))
 (let ((readers (set-difference-eq
                 (fn2-columns-postwrite-readers name tables world) opaque)))
  (union-eq readers
   (fn2-columns-observation-row-runes readers
    (fn2-columns-observation-interfaces tables world) world))))

(defun fn2-columns-call-guard-hint (name opaque enables world)
 (declare (xargs :verify-guards nil))
 (let* ((args (getpropc name 'formals :missing world))
        (tables (remove-duplicates-equal
                  (fn2-columns-input-tables
                   (getpropc name 'stobjs-in nil world) world))))
  (if (or (eq args :missing) (not tables)
          (eq (getpropc name 'symbol-class nil world) :program))
      (er hard 'fn2-columns-call-guard-hint
          "No logical column-input signature for ~x0." name)
   (fn2-columns-guard-hint tables
    (append opaque
     (remove-eq name
      (fn2-columns-framed-callees
       (all-fnnames (getpropc name 'unnormalized-body nil world)) tables world)))
    (union-eq enables
     (set-difference-eq (fn2-columns-postwrite-runes name tables opaque world) opaque)) world))))
