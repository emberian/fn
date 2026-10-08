; Length-only first pass of the history image builder. No encoded octets
; are retained or constructed here.
(in-package "ACL2")
(include-book "store-tree-codec-program-guards")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-scc-program-len (x acc)
  (declare (xargs :guard (and (fn-scc-treep x) (acl2-numberp acc))
                  :measure (acl2-count x)
                  :guard-hints (("Goal" :in-theory (enable fn-scc-treep fn-scc-octets-valuep)))))
  (cond ((fn-scc-octets-valuep x)
         (+ acc 1 (len (fn-scc-nat-octets (len x))) (len x)))
        ((consp x)
         (fn-scc-program-len (cdr x) (+ 1 (fn-scc-program-len (car x) acc))))
        (t (+ acc (len (fn-scc-atom-octets x))))))

(local (defthm fn-scc-length-append
  (equal (len (append a b)) (+ (len a) (len b)))))

(defthm fn-scc-program-len-is-encode-len
  (equal (fn-scc-program-len x acc) (+ acc (len (fn-scc-encode x))))
  :hints (("Goal" :induct (fn-scc-program-len x acc)
           :in-theory (e/d (fn-scc-program-len fn-scc-program fn-scc-encode-is-program)
                           (fn-scc-octets-valuep fn-scc-nat-octets fn-scc-atom-octets fn-scc-encode))))
  :rule-classes nil)
