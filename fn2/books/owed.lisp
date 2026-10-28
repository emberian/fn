(in-package "ACL2")

; An obligation is translated but never admitted as a theorem.  In particular,
; an unknown function or wrong arity is an error in the generated defun-nx.
(defmacro defthm-owed (name vars formula &key teeth doc)
  (let ((statement (intern-in-package-of-symbol
                    (concatenate 'string (symbol-name name) "$OWED") name)))
    `(progn
       (defun-nx ,statement ,vars ,formula)
       (table fn2-owed ',name
              '(:vars ,vars :formula ,formula :teeth ,teeth :doc ,doc)))))

(defun fn2-owed-names (world)
  (declare (xargs :guard (plist-worldp world)))
  (let ((entries (table-alist 'fn2-owed world)))
    (if (alistp entries) (strip-cars entries) nil)))

(assert-event (eq (symbol-class 'fn2-owed-names (w state)) :common-lisp-compliant))

(defthm-owed fn2-owed-sample (x)
  (implies (natp x) (<= 0 x))
  :teeth "x=1 satisfies the antecedent and conclusion; x=-1 falsifies both."
  :doc "Translation/registration fixture; not a theorem.")

(assert-event (member-eq 'fn2-owed-sample (fn2-owed-names (w state))))
(assert-event (and (natp 1) (<= 0 1)))
(assert-event (and (not (natp -1)) (not (<= 0 -1))))
(assert-event (not (getpropc 'fn2-owed-sample 'theorem nil (w state))))
