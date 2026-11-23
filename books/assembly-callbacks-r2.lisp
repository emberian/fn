; The commit kind's second section, second half: install, publish,
; settlement, drop and the drain's operations, then the kind's arms
; (commit-arms.lisp, generated here) and its run (split from
; assembly-callbacks-r under the one-minute rule).
(in-package "ACL2")

(include-book "commit-arms")
(make-event
 (let* ((body (fn2-commit-event-forms-2b))
        (pos (position-equal '(fn2-checkpoint-retirement-install-events) body))
        (wrapped
         '(encapsulate ()
            (local
             (in-theory (enable
                         (:forward-chaining fn2-checkpoint-construction-wfp-of-fn2-core-checkpoint-construction)
                         (:forward-chaining fn2-checkpoint-bytes-wfp-of-fn2-core-checkpoint-bytes)
                         (:forward-chaining fn2-ops-wfp-of-fn2-core-ops))))
            (local
             (defthm fn2-checkpoint-builder-claimp-bounds-fc
               (implies (fn2-checkpoint-builder-claimp c token okind oslot ogen fn2-checkpoints)
                        (and (natp c)
                             (< c (fn2-checkpoints-rows fn2-checkpoints))
                             (posp token)))
               :rule-classes :forward-chaining
               :hints (("Goal" :in-theory (enable fn2-checkpoint-builder-claimp)))))
            (make-event
             (value `(local (in-theory (disable nth
                       remove-weak-inequalities-one
                       remove-weak-inequalities-two
                       fn2-core-wfp
                       fn2-checkpoint-builder-claimp
                       fn2-checkpoint-allocation-install
                       fn2-checkpoint-install
                       fn2-format-allocation-decode
                       fn2-format-checkpoint-installation-decode
                       ,@(fn2-columns-getter-runes
                           '(fn2-extents fn2-checkpoint-construction fn2-retirement-control
                             fn2-checkpoint-future fn2-checkpoint-future-windows
                             fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                             fn2-fields fn2-pool fn2-alloc-edges fn2-ops)
                           (w state)))))))
            (fn2-checkpoint-retirement-install-events))))
   (if pos
       (value (append (take pos body) (cons wrapped (nthcdr (+ 1 pos) body))))
     (er soft 'assembly-callbacks-r2 "Could not locate (fn2-checkpoint-retirement-install-events) in fn2-commit-event-forms-2b."))))
