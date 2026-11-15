; Opt-in guard proofs consume public column facts, not their list layout.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :b)

(defun fn2-columns-extra-getters (fields)
 (declare (xargs :verify-guards nil))
 (if (atom fields) nil
  (append (if (fn2-columns-arrayp (car fields))
              (list (fn2-columns-sym (caar fields) "I")
                    (fn2-columns-sym (caar fields) "-LENGTH"))
            (list (caar fields)))
          (fn2-columns-extra-getters (cdr fields)))))
(defun fn2-columns-getter-runes (tables world)
 (declare (xargs :verify-guards nil))
 (if (atom tables) nil
  (let* ((table (car tables))
         (row (fn2-decl-row (list :columns table) world)))
   (append (fn2-columns-projection-readers table (fn2-decl-get :columns row))
           (list (fn2-columns-sym table "-ROWS"))
           (fn2-columns-extra-getters (fn2-decl-get :extra-fields row))
           (fn2-columns-getter-runes (cdr tables) world)))))
(defun fn2-columns-guard-tablesp (tables world)
 (declare (xargs :verify-guards nil))
 (if (atom tables) (null tables)
  (and (fn2-decl-row (list :columns (car tables)) world)
       (fn2-columns-guard-tablesp (cdr tables) world))))
(defun fn2-columns-guard-hint (tables opaque enables world)
 (declare (xargs :verify-guards nil))
 (if (not (fn2-columns-guard-tablesp tables world))
     (er hard 'fn2-columns-guard-hint "No column metadata for ~x0." tables)
  (let ((closed (set-difference-equal
                 (remove-duplicates-equal
                  (append '(nth) opaque (fn2-columns-getter-runes tables world)))
                 enables)))
   ; This changes only the current proof theory. Original guards, public
   ; NATP/BOUND/frame theorems, and explicit reader opt-ins stay intact.
   `(:in-theory (e/d ,enables ,closed)))))
