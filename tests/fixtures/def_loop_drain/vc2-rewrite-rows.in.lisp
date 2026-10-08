(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-orc-rewrite-rows-loop (rows ctx acc fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp rows)
      (fn-orc-rewrite-rows-loop (cdr rows) ctx
                                (cons (fn-orc-rewrite-row (car rows) ctx fn-arena) acc)
                                fn-arena)
    (fn-ag-rev-onto acc nil)))

(defun fn-orc-rewrite-rows (rows ctx fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (mbe :logic (if (consp rows)
                  (cons (fn-orc-rewrite-row (car rows) ctx fn-arena)
                        (fn-orc-rewrite-rows (cdr rows) ctx fn-arena))
                nil)
       :exec (fn-orc-rewrite-rows-loop rows ctx nil fn-arena)))

(defthm fn-orc-rewrite-rows-loop-is-rev-onto
  (equal (fn-orc-rewrite-rows-loop rows ctx acc fn-arena)
         (fn-ag-rev-onto acc (fn-orc-rewrite-rows rows ctx fn-arena)))
  :hints (("Goal" :induct (fn-orc-rewrite-rows-loop rows ctx acc fn-arena)
                  :in-theory (disable fn-orc-rewrite-row))))

(verify-guards fn-orc-rewrite-rows
  :hints (("Goal" :in-theory (disable fn-orc-rewrite-row))))
