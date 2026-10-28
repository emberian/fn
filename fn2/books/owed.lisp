(in-package "ACL2")

; Forward references name unit/checker functions: production books do not
; include their tests. fn2-assert-owed-teeth resolves and runs them there.
(defun fn2-owed-teethp (names)
  (if (atom names) (null names)
    (and (symbolp (car names)) (car names)
         (not (eq (car names) t)) (not (keywordp (car names)))
         (fn2-owed-teethp (cdr names)))))

; Translation checks the statement without admitting any theorem.
(defmacro defthm-owed (name vars formula &key teeth doc)
  (if (and (consp teeth) (fn2-owed-teethp teeth))
      (let ((statement (intern-in-package-of-symbol
                        (concatenate 'string (symbol-name name) "$OWED") name)))
        `(progn
           (defun-nx ,statement ,vars ,formula)
           (table fn2-owed ',name
                  '(:vars ,vars :formula ,formula :teeth ,teeth
                    :doc ,doc :status :owed))))
    (er hard 'defthm-owed
        "~x0 requires :teeth to name evaluating functions, not prose or forms." name)))

(defun fn2-owed-names (world)
  (declare (xargs :guard (plist-worldp world)))
  (let ((entries (table-alist 'fn2-owed world)))
    (if (alistp entries) (strip-cars entries) nil)))

(defun fn2-owed-tooth-events (teeth world)
  (declare (xargs :verify-guards nil))
  (if (atom teeth) nil
    (if (and (getpropc (car teeth) 'symbol-class nil world)
             (equal (getpropc (car teeth) 'formals :missing world) nil))
        (cons `(assert-event (equal (,(car teeth)) t))
              (fn2-owed-tooth-events (cdr teeth) world))
      (er hard 'fn2-assert-owed-teeth
          "Tooth ~x0 must name an existing zero-argument evaluating function."
          (car teeth)))))
(defun fn2-owed-check-events (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let ((entry (assoc-eq (car names) (table-alist 'fn2-owed world))))
      (if entry
          (append (fn2-owed-tooth-events (cadr (member-eq :teeth (cdr entry))) world)
                  (fn2-owed-check-events (cdr names) world))
        (er hard 'fn2-assert-owed-teeth "Unknown obligation ~x0." (car names))))))
(defmacro fn2-assert-owed-teeth (&rest names)
  `(make-event
    (value (cons 'progn (fn2-owed-check-events ',names (w state))))))
