; The transaction kind's operations and continuations (D5,
; books/txn.lisp), after the upload's: their own book keeps each layer D section under the one-minute rule.
(in-package "ACL2")
(include-book "assembly-callbacks-d")
(fn2-txn-op-events)

(defun fn2-txn-patch-tree (x old new)
  (declare (xargs :mode :program))
  (cond ((equal x old) new)
        ((atom x) x)
        (t (cons (fn2-txn-patch-tree (car x) old new)
                 (fn2-txn-patch-tree (cdr x) old new)))))

(make-event
 (let* ((old-c (fn2-decl-row '(:cost fn2-claim-state-core) (w state)))
        (new-c (fn2-decl-set :effects :per-use old-c))
        (old-m (fn2-decl-row '(:machine fn2-txn) (w state)))
        (new-m (fn2-txn-patch-tree
                old-m
                '((equal s *fn2-claim-state-held*)
                  (:next :lookup)
                  (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                '((equal s *fn2-claim-state-held*)
                  (:do (s2) (fn2-claim-state-core row-slot) :effects ((:acquire (:identity-reservation))))
                  (:next :lookup)
                  (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t)))))
   (value `(progn (table fn2-costs 'fn2-claim-state-core ',new-c)
                  (table fn2-machine-kinds 'fn2-txn ',new-m)))))

(fn2-txn-events)
