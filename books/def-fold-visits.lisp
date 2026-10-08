; Invocation counts derived from executed fold bodies. This extends def-cost's
; term machinery with a separate metric: one per invocation of an enrolled
; fold, including its terminal invocation. It is NOT a CPU/heap tariff.
; Unenrolled nonprimitive calls remain named leaves outside this metric.
(in-package "ACL2")
(include-book "def-cost")

(defun fn-fv-name (fn)
  (declare (xargs :mode :program))
  (packn-pos (list fn '-fold-visits) fn))

(mutual-recursion
 (defun fn-fv-term (term self w)
   (declare (xargs :mode :program))
   (cond
    ((or (atom term) (quotep term)) (mv ''0 nil))
    ((consp (car term))
     (mv-let (ac au) (fn-fv-terms (cdr term) self w)
       (mv-let (bc bu) (fn-fv-term (car (last (car term))) self w)
         (mv (fn-cost-plus ac (fn-cost-bind-body (cadar term) (cdr term) bc))
             (union-eq au bu)))))
    ((eq (car term) 'if)
     (mv-let (cc cu) (fn-fv-term (cadr term) self w)
       (mv-let (ac au) (fn-fv-term (caddr term) self w)
         (mv-let (bc bu) (fn-fv-term (cadddr term) self w)
           (mv (fn-cost-plus cc (list 'if (cadr term) ac bc))
               (union-eq cu (union-eq au bu)))))))
    ((eq (car term) 'return-last)
     (if (equal (cadr term) ''mbe1-raw)
         (fn-fv-term (caddr term) self w)
       (fn-fv-terms (cddr term) self w)))
    (t
     (mv-let (ac au) (fn-fv-terms (cdr term) self w)
       (let* ((fn (car term))
              (row (assoc-eq fn (table-alist 'fn-fold-visits w))))
         (cond
          ((eq fn self)
           (mv (fn-cost-plus ac (cons (fn-fv-name fn) (cdr term))) au))
          (row
           (mv (fn-cost-plus ac (cons (fn-fv-name fn) (cdr term)))
               (union-eq au (cadr (cdr row)))))
          ((assoc-eq fn *fn-cost-contracts*) (mv ac au))
          (t (mv ac (add-to-set-eq fn au)))))))))
 (defun fn-fv-terms (terms self w)
   (declare (xargs :mode :program))
   (if (atom terms) (mv ''0 nil)
     (mv-let (c u) (fn-fv-term (car terms) self w)
       (mv-let (cs us) (fn-fv-terms (cdr terms) self w)
         (mv (fn-cost-plus c cs) (union-eq u us)))))))

(defun fn-fv-event (fn leaves hints w)
  (declare (xargs :mode :program))
  (let* ((body (getpropc fn 'unnormalized-body nil w))
         (args (getpropc fn 'formals nil w))
         (j (getpropc fn 'justification nil w))
         (recursive (fn-cost-recursivep fn w)))
    (if (or (not body) (eq (symbol-class fn w) :program)
            (remove-eq nil (getpropc fn 'stobjs-in nil w)))
        (mv "expected a logic function without stobjs" nil)
      (mv-let (cost unknown) (fn-fv-term body fn w)
        (if (not (and (subsetp-eq unknown leaves) (subsetp-eq leaves unknown)))
            (mv (msg "derived leaves ~x0 differ from declared leaves ~x1" unknown leaves) nil)
          (mv nil
              `(progn
                 (defun ,(fn-fv-name fn) ,args
                   (declare ,@(and args `((ignorable ,@args)))
                            (xargs :verify-guards nil :ruler-extenders :all
                                   ,@(and hints (list :hints hints))
                                   ,@(and recursive
                                          (list :measure (access justification j :measure)
                                                :well-founded-relation (access justification j :rel)))))
                   ,(fn-cost-plus ''1 cost))
                 (table fn-fold-visits ',fn ',(list body unknown)))))))))

(defmacro def-fold-visits (fn &key leaves hints)
  `(make-event
    (mv-let (problem event) (fn-fv-event ',fn ',leaves ',hints (w state))
      (if problem (er soft 'def-fold-visits "~x0: ~@1" ',fn problem)
        (value event)))))

(defmacro def-fold-visits-check (fn)
  `(make-event
    (let* ((row (cdr (assoc-eq ',fn (table-alist 'fn-fold-visits (w state)))))
           (body (getpropc ',fn 'unnormalized-body nil (w state))))
      (mv-let (cost leaves) (fn-fv-term body ',fn (w state))
        (declare (ignore cost))
        (if (and row (equal body (car row))
                 (subsetp-eq leaves (cadr row)) (subsetp-eq (cadr row) leaves))
            (value '(value-triple :fold-visits-current))
          (er soft 'def-fold-visits-check "~x0: body or leaf set changed" ',fn))))))
