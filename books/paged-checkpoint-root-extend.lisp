; Root-only extension: no prefix record copy and no event-index traversal.
; This is the value refinement, NOT the requested O(delta) cost result.
; fn-sco-cpr-resume still validates the configured node once. Do not add a
; host interface until its carried invariant/cost obligation is discharged.
(in-package "ACL2")
(include-book "paged-checkpoint")

(defun fn-pck-root-extend (roots s configs delta f plen)
  (declare (xargs :guard t))
  (list (fn-sco-cpr-resume (fn-sco-at 0 roots) configs delta)
        (fn-replay-identity-loop delta (fn-sco-at 1 roots))
        (fn-sco-consumer-resume (fn-sco-at 2 roots) delta s)
        (fn-th-prefix-loop (fn-sco-at 3 roots) delta)
        f plen))

(local
 (defthm pck-root-len-fix
   (equal (len (true-list-fix x)) (len x))
   :hints (("Goal" :in-theory (enable true-list-fix)))))

(defthm fn-pck-root-extend-is-the-capture-root
  (implies (and (equal roots (list (fn-sco-cpr c) (fn-sco-identity c)
                                  (fn-sco-consumer c) (fn-sco-topic c)))
                (equal s (len (fn-sco-records c))))
           (equal (fn-pck-root-extend roots s configs delta f plen)
                  (fn-pck-root-tree-of-capture
                   (fn-sco-extend c configs delta) f plen)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-pck-root-extend fn-pck-root-tree-of-capture fn-sco-extend
              fn-sco-make fn-sco-cpr fn-sco-identity fn-sco-consumer fn-sco-topic
              fn-sco-at nth car-cons cdr-cons pck-root-len-fix
              (:executable-counterpart zp) (:executable-counterpart binary-+))
            (theory 'minimal-theory)))))
