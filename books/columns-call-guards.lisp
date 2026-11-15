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
    enables world))))
