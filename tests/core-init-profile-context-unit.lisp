; A child's initializer guard uses its profile projection, not unrelated
; assembled account/CNS predicates. This is the actual trace init obligation.
(in-package "ACL2")
(include-book "machine-budget-core-fixture")
(include-book "std/testing/must-fail" :dir :system)

(local (in-theory (disable fn2-profile-trace-boolean)))
(must-fail
 (defthm fn2-init-trace-missing-projection-control
  (implies (fn2-core-profilep profile)
   (and (unsigned-byte-p 32 (fn2-profile-trace-capacity profile))
        (booleanp (fn2-profile-trace profile))))
  :hints (("Goal" :use init-fn2-core-trace-profile
           :in-theory (disable fn2-core-profilep fn2-profilep)))))

(defthm fn2-init-trace-closed-profile-guard
 (implies (fn2-core-profilep profile)
  (and (unsigned-byte-p 32 (fn2-profile-trace-capacity profile))
       (booleanp (fn2-profile-trace profile))))
 :hints (("Goal" :use (init-fn2-core-trace-profile fn2-profile-trace-boolean)
          :in-theory (e/d (fn2-profile-trace-boolean)
                          (fn2-core-profilep fn2-profilep)))))

; Arbitrary profile input cannot satisfy this initializer guard.
(assert-event
 (not (booleanp (fn2-profile-trace
                 (put-assoc-equal :trace 7 *fn2-profile-tiny*)))))

; Exercise the shared generator, including its closed fallback, under a
; fresh name. No duplicate initializer implementation is maintained here.
(make-event
 (let* ((entries (fn2-core-child-registry (w state)))
        (trace (assoc-eq 'fn2-core-trace entries))
        (events (fn2-core-init-child-events
                  '((fn2-core-trace fn2-trace))
                  (fn2-core-registered-inits (list trace)) entries)))
  (value
   (cons 'progn
    (sublis '((init-fn2-core-trace . fn2-test-init-trace)
              (init-fn2-core-trace-profile . fn2-test-init-trace-profile)
              (init-fn2-core-trace-type . fn2-test-init-trace-type))
            events)))))
