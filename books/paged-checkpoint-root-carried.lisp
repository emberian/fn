; PRF-1362: root extension from the carried CPR cursor. The owner base keeps
; this tuple beside its SSR context; no prefix records are arguments.
(in-package "ACL2")
(include-book "paged-checkpoint-root-extend")
(include-book "paged-checkpoint-cursor")

(defun fn-pck-root-extend-carried (roots ix rest s delta f plen)
  (declare (xargs :guard (fn-sfi-cpr-carriedp (fn-sco-at 0 roots) ix)
                  :verify-guards nil))
  (let ((out (fn-pck-cpr-resume-from (fn-sco-at 0 roots) rest delta ix)))
    (list (list (car out)
                (fn-replay-identity-loop delta (fn-sco-at 1 roots))
                (fn-sco-consumer-resume (fn-sco-at 2 roots) delta s)
                (fn-th-prefix-loop (fn-sco-at 3 roots) delta)
                f plen)
          (cadr out) (caddr out))))

(verify-guards fn-pck-root-extend-carried)

(defthm fn-pck-root-extend-carried-is-the-capture-root
  (implies (and (equal roots (list (fn-sco-cpr c) (fn-sco-identity c)
                                  (fn-sco-consumer c) (fn-sco-topic c)))
                (equal s (len (fn-sco-records c)))
                (fn-pck-cpr-cursorp (fn-sco-cpr c) ix rest configs))
           (equal (car (fn-pck-root-extend-carried roots ix rest s delta f plen))
                  (fn-pck-root-tree-of-capture
                   (fn-sco-extend c configs delta) f plen)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-pck-root-extend-is-the-capture-root)
                 (:instance fn-pck-cpr-resume-from-is-sco-cpr-resume
                            (r (fn-sco-cpr c)) (events delta)))
           :in-theory
           (union-theories
            '(fn-pck-root-extend-carried fn-pck-root-extend fn-sco-at
              nth car-cons cdr-cons (:executable-counterpart zp)
              (:executable-counterpart binary-+))
            (theory 'minimal-theory)))))
