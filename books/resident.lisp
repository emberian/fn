;; The resident-measure generator of T10 (owed-d.lisp), as a library: it
;; includes only the core-child registry, so the served assembly (owed-d.lisp)
;; and the separate test instance (tests/owed-d-coverage.lisp) both expand it
;; over their own registries.
(in-package "ACL2")
(include-book "core-children")
(fn2-book-layer :d)

(defun fn2-resident-type-bits (type)
  (declare (xargs :verify-guards nil))
  (cond ((and (consp type) (member-eq (car type) '(unsigned-byte signed-byte)) (posp (cadr type))) (cadr type))
        ((and (consp type) (eq (car type) 'integer) (integerp (cadr type)) (integerp (caddr type)))
         (+ (integer-length (max (abs (cadr type)) (abs (caddr type)))) (if (< (cadr type) 0) 1 0)))
        ((eq type 'bit) 1)
        (t nil)))
(defun fn2-resident-bytes (bits) (declare (xargs :verify-guards nil)) (ceiling (max 1 bits) 8))

; One defstobj field spec (NAME :type T ...) of child STOBJ as a measure term
; over the bound child, or (:refuse NAME) when unmeasurable.
(defun fn2-resident-field-term (spec)
  (declare (xargs :verify-guards nil))
  (let* ((name (car spec)) (type (cadr (member-eq :type (cdr spec)))))
    (cond ((and (consp type) (eq (car type) 'array) (fn2-resident-type-bits (cadr type)))
           `(* ,(fn2-resident-bytes (fn2-resident-type-bits (cadr type))) (,(fn2-columns-sym name "-LENGTH") stobj)))
          ((fn2-resident-type-bits type) (fn2-resident-bytes (fn2-resident-type-bits type)))
          (t (list :refuse name)))))

(defun fn2-resident-column-terms (stobj cols)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
    (cons `(* ,(fn2-resident-bytes (fn2-columns-width (cadar cols)))
              (,(fn2-columns-sym (fn2-columns-sym (fn2-columns-col-name stobj (caar cols)) "$A") "-LENGTH") stobj))
          (fn2-resident-column-terms stobj (cdr cols)))))
(defun fn2-resident-extra-terms (extras)
  (declare (xargs :verify-guards nil))
  (if (atom extras) nil
    (cons (fn2-resident-field-term (car extras)) (fn2-resident-extra-terms (cdr extras)))))
(defun fn2-resident-refusals (terms)
  (declare (xargs :verify-guards nil))
  (if (atom terms) nil
    (append (and (consp (car terms)) (eq (caar terms) :refuse) (list (cadar terms)))
            (fn2-resident-refusals (cdr terms)))))
(defun fn2-resident-measurable (terms)
  (declare (xargs :verify-guards nil))
  (if (atom terms) nil
    (append (and (not (and (consp (car terms)) (eq (caar terms) :refuse))) (list (car terms)))
            (fn2-resident-measurable (cdr terms)))))

; Per child: its measure function: the rows scalar (sized by :rows-bound),
; every column array, every extra field.
(defun fn2-resident-child-events (entries world)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (let* ((field (caar entries)) (stobj (fn2-core-child-property (car entries) :stobj))
           (why (fn2-core-child-property (car entries) :why))
           (row (fn2-decl-row (list :columns stobj) world))
           (terms (append (list (fn2-resident-bytes (integer-length (max 1 (- (nfix (fn2-decl-get :rows-bound row)) 1)))))
                          (fn2-resident-column-terms stobj (fn2-decl-get :columns row))
                          (fn2-resident-extra-terms (fn2-decl-get :extra-fields row))))
           (refused (fn2-resident-refusals terms)))
      (if (and refused (not (search "bound" why)))
          (er hard 'fn2-resident-measure-events
              "Child ~x0 (~x1) has fields the generator cannot measure, ~x2, and its :why states no bound."
              field stobj refused)
        (cons `(defun ,(fn2-columns-sym field "-RESIDENT") (fn2-core)
                 (declare (xargs :stobjs fn2-core :verify-guards nil))
                 (stobj-let ((,stobj (,field fn2-core)))
                   (n) (+ 0 ,@(subst stobj 'stobj (fn2-resident-measurable terms)))
                   n))
              (fn2-resident-child-events (cdr entries) world))))))
;; Fields left out of the measure because the child's :why states their bound.
(defun fn2-resident-refused-all (entries world)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (let* ((stobj (fn2-core-child-property (car entries) :stobj))
           (row (fn2-decl-row (list :columns stobj) world))
           (refused (fn2-resident-refusals (fn2-resident-extra-terms (fn2-decl-get :extra-fields row)))))
      (append (and refused (list (cons (caar entries) refused)))
              (fn2-resident-refused-all (cdr entries) world)))))
(defun fn2-resident-sum (entries)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (cons `(,(fn2-columns-sym (caar entries) "-RESIDENT") fn2-core) (fn2-resident-sum (cdr entries)))))
(defun fn2-resident-breakdown (entries)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (cons `(list ',(caar entries) (,(fn2-columns-sym (caar entries) "-RESIDENT") fn2-core))
          (fn2-resident-breakdown (cdr entries)))))

; The generator: expanded once per assembled instance (here, and in the test
; instance of tests/core-child-assembly-* by the evidence book).
(defmacro fn2-resident-measure-events ()
  '(make-event
    (let* ((entries (fn2-core-child-registry (w state))))
      (value `(progn ,@(fn2-resident-child-events entries (w state))
                (defconst *fn2-resident-children* ',(strip-cars entries))
                (defconst *fn2-resident-refused* ',(fn2-resident-refused-all entries (w state)))
                (defun fn2-core-resident-measure (fn2-core)
                  (declare (xargs :stobjs fn2-core :verify-guards nil))
                  (+ 0 ,@(fn2-resident-sum entries)))
                (defun fn2-core-resident-breakdown (fn2-core)
                  (declare (xargs :stobjs fn2-core :verify-guards nil))
                  (list ,@(fn2-resident-breakdown entries))))))))

