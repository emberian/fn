; Protected calendar services are dispatched from the declaration registry.
(in-package "ACL2")
(include-book "executor-access")

(defun fn2-service-core-bindings (bindings)
  (declare (xargs :verify-guards nil))
  (if (atom bindings) nil
    (cons (list (caar bindings) (list (cadar bindings) 'fn2-core))
          (fn2-service-core-bindings (cdr bindings)))))
(defun fn2-service-ready-terms (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (let* ((props (cdar rows)) (bindings (fn2-resource-get :children props)))
      (cons `(stobj-let ,(fn2-service-core-bindings bindings)
               (ready) (,(fn2-resource-get :ready props) ,@(strip-cars bindings)) ready)
            (fn2-service-ready-terms (cdr rows))))))
(defun fn2-service-dispatch-arms (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (let* ((props (cdar rows)) (bindings (fn2-resource-get :children props))
           (children (strip-cars bindings))
           (steps (fn2-resource-get :steps (fn2-resource-get :bound props))))
      (cons `((equal service ,(fn2-resource-get :slot props))
              (stobj-let ,(fn2-service-core-bindings bindings)
                (steps ,@children)
                (if (,(fn2-resource-get :ready props) ,@children)
                    (mv-let (result ,@children) (,(fn2-resource-get :step props) ,@children)
                      (declare (ignore result)) (mv ,steps ,@children))
                  (mv 0 ,@children))
                (mv steps fn2-core)))
            (fn2-service-dispatch-arms (cdr rows))))))
(defun fn2-services-work-max (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) 0
    (max (nfix (fn2-resource-get :steps (fn2-resource-get :bound (cdar rows))))
         (fn2-services-work-max (cdr rows)))))
(make-event
 (let ((rows (reverse (table-alist 'fn2-services (w state)))))
   (value
    `(progn
       (defconst *fn2-services-work-max* ,(fn2-services-work-max rows))
       (defun fn2-exec-services-ready-p (fn2-core)
         (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
         (or ,@(fn2-service-ready-terms rows)))
       (defun fn2-exec-run-services (service fn2-core)
         (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
         (cond ,@(fn2-service-dispatch-arms rows)
               (t (let ((fn2-core (fn2-exec-clear-service service fn2-core))) (mv 0 fn2-core)))))))))
(fn2-core-preserves fn2-exec-run-services (service fn2-core) :position 1 :rows nil :prefix "")
(defthm fn2-exec-run-services-work-natp
  (natp (mv-nth 0 (fn2-exec-run-services service fn2-core)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn2-exec-run-services))))
(defthm fn2-exec-run-services-work-bound
  (<= (mv-nth 0 (fn2-exec-run-services service fn2-core)) *fn2-services-work-max*)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn2-exec-run-services))))
(in-theory (disable fn2-exec-run-services fn2-exec-services-ready-p))
