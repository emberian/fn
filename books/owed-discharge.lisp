; Exact-formula evidence registration shared independently of pool storage.
(in-package "ACL2")
(include-book "owed")

(defmacro fn2-owed-discharge (name thm)
  `(make-event
    (let ((row (fn2-decl-row '(:square ,name) (w state))))
      (if (not (and row (equal (fn2-decl-get :proof row) '(:owed))))
          (er soft 'fn2-owed-discharge "~x0 is not an owed obligation." ',name)
        (value (list 'table 'fn2-squares '',name
                     (list 'quote (fn2-decl-set :proof '(:proved ,thm) row))))))))
