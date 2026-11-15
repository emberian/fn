(in-package "ACL2")
(include-book "assembly-core")
(include-book "core-init-projections")
(include-book "ops-conservation")

; Operations accounting is initialized by the actual registered child initializer.
; This supplies a missing reachable-entry conjunct without assuming its result.
(make-event
 (value (cons 'progn
   (fn2-core-init-projection-events 'fn2-core-ops (w state)))))
(defthm fn2-env-reach-core-ops-type
 (implies (fn2-corep c) (fn2-opsp (fn2-core-ops c)))
 :hints (("Goal" :in-theory (enable fn2-corep fn2-core-ops))))
(defthm fn2-env-reach-core-init-ops-semantic
 (implies (and (fn2-corep c) (fn2-core-profilep profile))
  (fn2-ops-semanticp (fn2-core-ops (fn2-core-init profile c))))
 :hints (("Goal"
  :use ((:instance fn2-ops-init-conservation (fn2-ops (fn2-core-ops c)))
        (:instance init-fn2-core-ops-profile))
  :in-theory (union-theories
   '(fn2-env-reach-core-ops-type
     fn2-core-ops-of-fn2-core-init-by-definition)
   (theory 'minimal-theory)))))
