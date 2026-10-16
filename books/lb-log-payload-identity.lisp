; Payload identity from the temporary adapter's byte-preserving wire encoding.
(in-package "ACL2")
(include-book "lb-log-model")

(local (defun-nx fn-lbpi-pair-induct (a b startp)
 (declare (xargs :measure (acl2-count a)))
 (if (and (consp a) (consp b))
  (fn-lbpi-pair-induct (cdr a) (cdr b) (eql (car a) 10))
  (list a b startp))))

(local (defthm fn-lbpi-wire-consp
 (equal (consp (fn-lb-log-model-wire xs startp)) (consp xs))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lb-log-model-wire xs startp))
 :in-theory (union-theories (theory 'ground-zero) '(binary-append))))))

(local (defthm fn-lbpi-wire-car
 (implies (consp xs)
 (equal (car (fn-lb-log-model-wire xs startp)) (car xs)))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lb-log-model-wire xs startp))
 :in-theory (union-theories (theory 'ground-zero) '(binary-append))))))

(local (defthm fn-lbpi-equal-wire-heads
 (implies (and (consp a) (consp b)
 (equal (fn-lb-log-model-wire a startp) (fn-lb-log-model-wire b startp)))
 (equal (car a) (car b)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-lbpi-wire-car (xs a))
                      (:instance fn-lbpi-wire-car (xs b)))
 :in-theory (theory 'minimal-theory)))))

(defthm fn-lb-log-model-wire-is-injective
 (implies (and (true-listp a) (true-listp b)
 (equal (fn-lb-log-model-wire a startp) (fn-lb-log-model-wire b startp)))
 (equal a b))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lbpi-pair-induct a b startp)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbpi-pair-induct fn-lb-log-model-wire fn-lbpi-wire-consp
 true-listp binary-append)))
 ("Subgoal *1/1" :use ((:instance fn-lbpi-equal-wire-heads)))
 ("Subgoal *1/2" :use ((:instance fn-lbpi-equal-wire-heads)))
 ("Subgoal *1/3" :use ((:instance fn-lbpi-equal-wire-heads)))))
