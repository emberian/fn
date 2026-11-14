; On-demand projections of the actual initializer chain. One selected
; child needs N small wrapper laws, not a rectangular N-by-N init matrix.
(in-package "ACL2")
(include-book "core-product-lowering")

(defun fn2-core-init-projection-name (target initializer)
  (declare (xargs :verify-guards nil))
  (fn2-columns-sym target
    (concatenate 'string "-OF-" (symbol-name initializer) "-BY-DEFINITION")))
(defun fn2-core-init-projection-expected (target entry world)
  (declare (xargs :verify-guards nil))
  (if (eq target (car entry))
      (fn2-lower-substitute (fn2-core-child-property entry :init)
        (list (cons (fn2-core-child-property entry :stobj) (list target 'fn2-core))) world)
    (list target 'fn2-core)))
(defun fn2-core-init-wrapper-projection-events (target entries world)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (let* ((field (caar entries))
           (initializer (fn2-columns-pre "INIT-" field))
           (reader-law (fn2-columns-sym target
                         (concatenate 'string "-OF-"
                           (symbol-name (fn2-product-writer field)))))
           (name (fn2-core-init-projection-name target initializer)))
      (append
       (if (or (not (function-symbolp initializer world))
               (not (getpropc reader-law 'theorem nil world)))
           `((make-event (er soft 'fn2-core-init-projection-events
               "Missing actual initializer ~x0 or read/write law ~x1."
               ',initializer ',reader-law)))
         (and (not (getpropc name 'theorem nil world))
              `((defthm ,name
                  (equal (,target (,initializer profile fn2-core))
                         ,(fn2-core-init-projection-expected target (car entries) world))
                  :hints (("Goal" :in-theory
                           (union-theories '(,initializer ,reader-law)
                                           (theory 'minimal-theory))))))))
       (fn2-core-init-wrapper-projection-events target (cdr entries) world)))))
(defun fn2-core-init-projection-runes (target entries)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (cons (fn2-core-init-projection-name target (fn2-columns-pre "INIT-" (caar entries)))
          (fn2-core-init-projection-runes target (cdr entries)))))
(defun fn2-core-init-projection-events (target world)
  (declare (xargs :verify-guards nil))
  (let* ((entries (fn2-core-child-registry world))
         (entry (assoc-eq target entries))
         (name (fn2-core-init-projection-name target 'fn2-core-init)))
    (if (or (not entry) (not (function-symbolp 'fn2-core-init world)))
        `((make-event (er soft 'fn2-core-init-projection-events
            "Unknown core target ~x0 or actual core initializer missing." ',target)))
      (append
       (fn2-core-init-wrapper-projection-events target entries world)
       (and (not (getpropc name 'theorem nil world))
            `((defthm ,name
                (equal (,target (fn2-core-init profile fn2-core))
                       ,(fn2-core-init-projection-expected target entry world))
                :hints (("Goal" :in-theory
                         (union-theories
                          '(fn2-core-init ,@(fn2-core-init-projection-runes target entries))
                          (theory 'minimal-theory)))))))))))
