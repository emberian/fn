; fn: the two operator-data walks of the configuration table execute by loops,
; and the loop is the walk (PRF-383).
;
; books/config.lisp fn-cfg-rows-with-key and books/peer-config.lisp
; fn-cfg-peer-names walk the whole peer table (D27: no row cap), so each is
; (mbe :logic <its recursion> :exec <a loop onto an accumulator>) and runs in
; constant control stack.  The def-loop bridge is local to its book; these
; are its exported statements for the two walks the host calls
; (host/owner-host.lisp fn-cu-plans; the open's configuration replay): the
; loop with accumulator ACC is ACC reversed onto the walk, for every ACC, so
; the executed loop at the empty accumulator IS the logical walk.
(in-package "ACL2")
(include-book "peer-config")

(local (in-theory (enable fn-cfg-rows-with-key-loop fn-cfg-peer-names-loop)))

(local
 (defthm fn-cfg-walk-append-snoc
   (equal (append (append x (list y)) z) (append x (cons y z)))))

(defthm fn-cfg-rows-with-key-loop-is-revappend-of-the-walk
  (equal (fn-cfg-rows-with-key-loop rows a acc)
         (revappend acc (fn-cfg-rows-with-key rows a)))
  :hints (("Goal" :induct (fn-cfg-rows-with-key-loop rows a acc)
           :in-theory (enable fn-cfg-rows-with-key))))

(defthm fn-cfg-peer-names-loop-is-revappend-of-the-walk
  (equal (fn-cfg-peer-names-loop peers acc)
         (revappend acc (fn-cfg-peer-names peers)))
  :hints (("Goal" :induct (fn-cfg-peer-names-loop peers acc)
           :in-theory (enable fn-cfg-peer-names))))
