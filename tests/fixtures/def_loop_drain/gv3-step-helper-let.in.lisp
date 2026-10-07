(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-ncfg-listener-plan-step (x rest)
  (declare (xargs :guard t))
  (let ((r (fn-ncfg-listener-element (fn-ncfg-trim x))))
    (if (equal (fn-ncfg-first r) :refused)
        r
      (cond ((equal (fn-ncfg-first rest) :refused) rest)
            ((fn-ncfg-memberp (fn-ncfg-second r) (fn-ncfg-second rest))
             (list :refused :listener-duplicate))
            (t (list :ok (cons (fn-ncfg-second r)
                               (fn-ncfg-second rest))))))))

(defun fn-ncfg-listener-plan-loop (rev acc)
  (declare (xargs :guard t))
  (if (consp rev)
      (fn-ncfg-listener-plan-loop (cdr rev) (fn-ncfg-listener-plan-step (car rev) acc))
    acc))

(defun fn-ncfg-listener-plan (elements)
  ; (:ok PROJECTIONS) in the written order, or the first address's refusal.
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp elements)
           (let ((r (fn-ncfg-listener-element (fn-ncfg-trim (car elements)))))
             (if (equal (fn-ncfg-first r) :refused)
                 r
               (let ((rest (fn-ncfg-listener-plan (cdr elements))))
                 (cond ((equal (fn-ncfg-first rest) :refused) rest)
                       ((fn-ncfg-memberp (fn-ncfg-second r) (fn-ncfg-second rest))
                        (list :refused :listener-duplicate))
                       (t (list :ok (cons (fn-ncfg-second r)
                                          (fn-ncfg-second rest))))))))
         (list :ok nil))
       :exec (fn-ncfg-listener-plan-loop (fn-ag-rev-onto elements nil) (list :ok nil))))

(defthm fn-ncfg-listener-plan-loop-of-rev-onto
  (equal (fn-ncfg-listener-plan-loop (fn-ag-rev-onto elements zs) (list :ok nil))
         (fn-ncfg-listener-plan-loop zs (fn-ncfg-listener-plan elements)))
  :hints (("Goal" :induct (fn-ag-rev-onto elements zs)
                  :in-theory (union-theories
                              '(fn-ncfg-listener-plan-loop fn-ncfg-listener-plan fn-ncfg-listener-plan-step fn-ag-rev-onto
                                car-cons cdr-cons)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

(verify-guards fn-ncfg-listener-plan
  :hints (("Goal" :use ((:instance fn-ncfg-listener-plan-loop-of-rev-onto (zs nil)))
                  :in-theory (union-theories
                              '(fn-ncfg-listener-plan-loop fn-ncfg-listener-plan)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))
