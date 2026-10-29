; Open core-child registry. Forms are expansion-time data, never resident values.
(in-package "ACL2")
(include-book "machines")

(defun fn2-core-child-property (entry key)
  (declare (xargs :verify-guards nil))
  (cadr (member-eq key (cdr entry))))
(defun fn2-core-child-order (entries order)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (append (and (eq (fn2-core-child-property (car entries) :order) order)
                 (list (car entries)))
            (fn2-core-child-order (cdr entries) order))))
(defun fn2-core-child-registry (world)
  (declare (xargs :verify-guards nil))
  (let ((entries (fn2-decl-rows :core-child world)))
    (append (fn2-core-child-order entries :foundation)
            (fn2-core-child-order entries :machine)
            (fn2-core-child-order entries :extension))))
(defun fn2-core-child-types (entries)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (cons (fn2-core-child-property (car entries) :stobj)
          (fn2-core-child-types (cdr entries)))))
(defmacro defcorechild (field stobj &key init profilep why
                              (reference ':state) (order ':extension))
  (if (and (symbolp stobj) stobj init profilep
           (stringp why) (< 0 (length why))
           (member-eq reference '(:state :environment))
           (member-eq order '(:foundation :machine :extension)))
      `(make-event
        (if (or (table-alist 'fn2-core-instance (w state))
                (member-eq ',stobj (fn2-core-child-types
                  (remove-assoc-eq ',field (fn2-decl-rows :core-child (w state))))))
            (er soft 'defcorechild "Child registration requires an open assembly and unique stobj: ~x0 / ~x1." ',field ',stobj)
          (value (fn2-declare '(:core-child ,field)
                   '(:stobj ,stobj :init ,init :profilep ,profilep
                     :reference ,reference :order ,order :why ,why)
                   '((:declaration (:columns ,stobj))) nil))))
    (er hard 'defcorechild "Invalid child ~x0: init, profilep and nonempty why are required." field)))
(defun fn2-core-registered-pairs (entries)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (cons (list (caar entries) (fn2-core-child-property (car entries) :stobj))
          (fn2-core-registered-pairs (cdr entries)))))
(defun fn2-core-registered-forms (entries key)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (cons (fn2-core-child-property (car entries) key)
          (fn2-core-registered-forms (cdr entries) key))))
(defun fn2-core-registered-inits (entries)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (cons (list (fn2-core-child-property (car entries) :stobj)
                (fn2-core-child-property (car entries) :init))
          (fn2-core-registered-inits (cdr entries)))))
(defun fn2-core-reference-entries (entries)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (append (and (not (eq (fn2-core-child-property (car entries) :reference) :environment))
                 (list (car entries)))
            (fn2-core-reference-entries (cdr entries)))))
(defun fn2-core-register-machine-children (names world base)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let ((capacity `(nfix ,(fn2-machine-property (car names) :capacity world))))
      (cons `(defcorechild ,(fn2-columns-sym (car names) "-TABLE") ,(car names)
               :init (,(fn2-columns-sym (car names) "-PREPARE")
                       ,capacity ,base (fn2-profile-generation-start profile) ,(car names))
               :profilep (< (+ ,base ,capacity) 4294967296)
               :order :machine :why "Persistent declared machine state across yields.")
            (fn2-core-register-machine-children (cdr names) world `(+ ,base ,capacity))))))
