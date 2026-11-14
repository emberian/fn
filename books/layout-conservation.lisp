; Pool conservation for the existing layout compiler and its generated exports.
; These proofs inspect declarations and prove the actual emitted functions.
(in-package "ACL2")
(include-book "layout")
(defthm fn2-codec-emit-fixed-pool-semantic
 (implies (fn2-pool-semanticp fn2-pool)
  (fn2-pool-semanticp (mv-nth 2 (fn2-codec-emit-fixed n v slot gen next okind oslot ogen fn2-pool))))
 :hints (("Goal" :induct (fn2-codec-emit-fixed n v slot gen next okind oslot ogen fn2-pool)
          :in-theory (e/d (fn2-codec-emit-fixed) (fn2-pool-semanticp fn2-pool-write fn2-pool-read)))))
(defthm fn2-codec-emit-varint-pool-semantic
 (implies (fn2-pool-semanticp fn2-pool)
  (fn2-pool-semanticp (mv-nth 2 (fn2-codec-emit-varint v slot gen next okind oslot ogen fn2-pool))))
 :hints (("Goal" :induct (fn2-codec-emit-varint v slot gen next okind oslot ogen fn2-pool)
          :in-theory (e/d (fn2-codec-emit-varint) (fn2-pool-semanticp fn2-pool-write fn2-pool-read)))))
(defthm fn2-codec-emit-be-pool-semantic
 (implies (fn2-pool-semanticp fn2-pool)
  (fn2-pool-semanticp (mv-nth 2 (fn2-codec-emit-be n v slot gen next okind oslot ogen fn2-pool))))
 :hints (("Goal" :induct (fn2-codec-emit-be n v slot gen next okind oslot ogen fn2-pool)
          :in-theory (e/d (fn2-codec-emit-be) (fn2-pool-semanticp fn2-pool-write fn2-pool-read)))))
(defthm fn2-layout-copy-loop-pool-semantic
 (implies (fn2-pool-semanticp fn2-pool)
  (fn2-pool-semanticp (mv-nth 1 (fn2-layout-copy-loop src-slot src-gen src-off dst-slot dst-gen dst-off len okind oslot ogen fn2-pool))))
 :hints (("Goal" :induct (fn2-layout-copy-loop src-slot src-gen src-off dst-slot dst-gen dst-off len okind oslot ogen fn2-pool)
          :in-theory (e/d (fn2-layout-copy-loop) (fn2-pool-semanticp fn2-pool-write fn2-pool-read)))))
(defthm fn2-layout-copy-pool-semantic
 (implies (fn2-pool-semanticp fn2-pool)
  (fn2-pool-semanticp (mv-nth 1 (fn2-layout-copy src-slot src-gen src-off dst-slot dst-gen dst-off len okind oslot ogen fn2-pool))))
 :hints (("Goal" 
          :in-theory (e/d (fn2-layout-copy) (fn2-pool-semanticp fn2-pool-write fn2-pool-read)))))

(defun fn2-codec-conservation-emitter-events (name layout)
 (declare (xargs :verify-guards nil))
 (if (atom layout) nil
  (let* ((fn (fn2-codec-emitter-name name (caar layout)))
         (tail (and (consp (cdr layout))
                    (fn2-codec-symbol (fn2-codec-emitter-name name (caadr layout)) "-POOL-SEMANTIC"))))
   (append (fn2-codec-conservation-emitter-events name (cdr layout))
    `((defthm ,(fn2-codec-symbol fn "-POOL-SEMANTIC")
       (implies (fn2-pool-semanticp fn2-pool)
        (fn2-pool-semanticp (mv-nth 2 (,fn base slot gen off next okind oslot ogen fn2-fields fn2-pool))))
       :hints (("Goal" :in-theory (union-theories
                  '(,fn ,@(and tail (list tail))
                    mv-nth car-cons cdr-cons
                    fn2-codec-emit-fixed-pool-semantic fn2-codec-emit-varint-pool-semantic
                    fn2-codec-emit-be-pool-semantic fn2-layout-copy-pool-semantic)
                  (theory 'minimal-theory))))))))))
(defun fn2-codec-conservation-events (name row)
 (declare (xargs :verify-guards nil))
 (let* ((fn (fn2-decl-get :encode row)) (layout (fn2-decl-get :layout row))
        (first (fn2-codec-symbol (fn2-codec-emitter-name name (caar layout)) "-POOL-SEMANTIC")))
  (append (fn2-codec-conservation-emitter-events name layout)
   `((defthm ,(fn2-codec-symbol fn "-POOL-SEMANTIC")
      (implies (fn2-pool-semanticp fn2-pool)
       (fn2-pool-semanticp (mv-nth 2 (,fn base slot gen off okind oslot ogen fn2-fields fn2-pool))))
      :hints (("Goal" :in-theory (union-theories '(,fn ,first mv-nth car-cons cdr-cons)
                                                    (theory 'minimal-theory)))))))))

(defun fn2-codec-conservation-schema-layouts (rows)
 (declare (xargs :verify-guards nil))
 (if (atom rows) nil
  (append (take 2 (fn2-decl-get :layouts (cdar rows)))
          (fn2-codec-conservation-schema-layouts (cdr rows)))))
(defun fn2-codec-conservation-layout-events (names layouts)
 (declare (xargs :verify-guards nil))
 (if (atom names) nil
  (append (fn2-codec-conservation-events (car names) (cdr (assoc-eq (car names) layouts)))
          (fn2-codec-conservation-layout-events (cdr names) layouts))))
(defun fn2-codec-conservation-export-runes (names)
 (declare (xargs :verify-guards nil))
 (if (atom names) nil
  (cons (fn2-codec-symbol (fn2-codec-symbol (car names) "-ENCODE") "-POOL-SEMANTIC")
        (fn2-codec-conservation-export-runes (cdr names)))))
