; Actual evaluator arithmetic-object join, subordinate to whole admission.
(in-package "ACL2")
(include-book "connection-operation-operand-domain")
(include-book "assumptions-selected-runtime-immediate-arithmetic")
(defun fn-srco-event-primary (event coordinate)
 (fn-assume-srif-primary-object-octets
  (fn-atsc-at 0 event) (fn-atsc-at 0 (fn-atsc-at 1 event))
  (fn-atsc-at 1 (fn-atsc-at 1 event)) coordinate))
(defun fn-srco-trace-primary (ops coordinate)
 (if (consp ops) (+ (fn-srco-event-primary (car ops) coordinate)
                    (fn-srco-trace-primary (cdr ops) coordinate)) 0))
(defthm fn-srco-source-event-establishes-immediate-domain
 (implies (and (fn-copod-operationp event domain)
               (<= domain 4611686018427387903)
               (equal coordinate *fn-srif-coordinate*))
  (fn-srif-domain-p (fn-atsc-at 0 event)
   (fn-atsc-at 0 (fn-atsc-at 1 event))
   (fn-atsc-at 1 (fn-atsc-at 1 event)) coordinate))
 :hints (("Goal" :in-theory (enable fn-copod-operationp fn-copod-fits
             fn-srif-domain-p fn-srif-immediatep fn-srif-result)))
 :rule-classes nil)
(local (defthm fn-srco-source-event-primary-zero
 (implies (and (fn-copod-operationp event domain)
               (<= domain 4611686018427387903)
               (equal coordinate *fn-srif-coordinate*))
  (equal (fn-srco-event-primary event coordinate) 0))
 :hints (("Goal" :use (fn-srco-source-event-establishes-immediate-domain
   (:instance fn-assume-srif-primary-object-zero
    (op (fn-atsc-at 0 event)) (x (fn-atsc-at 0 (fn-atsc-at 1 event)))
    (y (fn-atsc-at 1 (fn-atsc-at 1 event)))))
  :in-theory (enable fn-srco-event-primary)))))
(defthm fn-srco-source-trace-primary-zero
 (implies (and (fn-copod-operationsp ops domain)
               (<= domain 4611686018427387903)
               (equal coordinate *fn-srif-coordinate*))
  (equal (fn-srco-trace-primary ops coordinate) 0))
 :hints (("Goal" :induct (fn-srco-trace-primary ops coordinate)
                 :in-theory (e/d (fn-copod-operationsp) (fn-copod-operationp fn-srco-event-primary))))
 :rule-classes nil)
; Complete actual five-result observation is retained; only the ordered
; material arithmetic primary-object component is assigned zero. Comparisons,
; source/model trace construction, machine lowering, caller/creator frames,
; refusal/fault, first-use, collector and retained lifetime remain separate.
(defthm fn-srco-actual-evaluator-arithmetic-component-by-definition
 (implies (and (<= (fn-omk-at 4 installation) 4611686018427387903)
               (equal coordinate *fn-srif-coordinate*))
  (and (equal (fn-atsc-value
               (fn-copc-evaluate installation kind family address peer depth))
              (fn-cop-evaluate installation kind family address peer depth))
       (equal (fn-srco-trace-primary
                (fn-atsc-ops (fn-copc-evaluate installation kind family address peer depth))
                coordinate) 0)))
 :hints (("Goal" :use (fn-copc-evaluate-observes-complete-actual-result
                fn-copod-evaluate-material-operators-fit
                (:instance fn-srco-source-trace-primary-zero
                 (ops (fn-atsc-ops (fn-copc-evaluate installation kind family address peer depth)))
                 (domain (fn-omk-at 4 installation))))
            :in-theory (disable fn-copc-evaluate fn-cop-evaluate
              fn-atsc-value fn-atsc-ops fn-srco-trace-primary fn-copod-operationsp)))
 :rule-classes nil)
