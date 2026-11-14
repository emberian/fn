; Native posts a clock before every actual turn. These controls retain the
; full supported-profile and initialized-core antecedent; no mock dispatcher.
(in-package "ACL2")
(include-book "../books/host-boundary")

(defun fn2-progress-sched-view (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-sched (fn2-core-sched fn2-core))) (view)
    (list (fn2-sched-cursor fn2-sched) (fn2-sched-queued fn2-sched)) view))

(defun fn2-progress-clock-turn (clockp fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((before (fn2-progress-sched-view fn2-core))
       (hyps (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                  (not (fn2-core-stopped-p fn2-core))
                  (< 0 (cadr before)) (fn2-exec-credit-p fn2-core)
                  (not (fn2-exec-observation-p fn2-core))))
       (fn2-core (if clockp (fn2-host-post-clock 1 1 1 fn2-core) fn2-core))
       ((mv status obs visits actions fn2-core) (fn2-turn fn2-core)))
    (mv (list hyps status obs visits actions before
              (fn2-progress-sched-view fn2-core)
              (not (fn2-core-stopped-p fn2-core))) fn2-core)))

(defun fn2-progress-clock-turns (left fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix left)))
  (if (zp left) (mv nil fn2-core)
    (mv-let (result fn2-core) (fn2-progress-clock-turn t fn2-core)
      (mv-let (rest fn2-core) (fn2-progress-clock-turns (- left 1) fn2-core)
        (mv (cons result rest) fn2-core)))))

(defun fn2-progress-clock-witness (h clockp rounds fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((profile (put-assoc-equal :h h
                  (put-assoc-equal :trace nil
                    (put-assoc-equal :pool-classes '((8 . 4096) (4 . 65536))
                                     *fn2-profile-tiny*))))
       (supported (fn2-core-profilep profile))
       (fn2-core (fn2-init-executor profile :echo nil fn2-core)))
    (if clockp
        (mv-let (results fn2-core) (fn2-progress-clock-turns rounds fn2-core)
          (mv (list supported results) fn2-core))
      (mv-let (result fn2-core) (fn2-progress-clock-turn nil fn2-core)
        (mv (list supported (list result)) fn2-core)))))
(defun fn2-progress-clock-test (h clockp rounds)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core) (fn2-progress-clock-witness h clockp rounds fn2-core)
      result)))

; The supported H=1 profile remains runnable and solvent for an entire
; calendar's worth of host iterations, yet receives no scheduler visits.
; Every row asserts the full initialized type/WFP/resource antecedent.
(assert-event
 (equal (fn2-progress-clock-test 1 t 8)
        (list t (make-list 8 :initial-element
                         '(t :more 1 0 0 (0 2) (0 2) t)))))
; Removing the clock load or increasing only H distinguishes the cause.
(assert-event
 (equal (fn2-progress-clock-test 2 t 1)
        '(t ((t :more 1 8 1 (0 2) (0 1) t)))))
(assert-event
 (equal (fn2-progress-clock-test 1 nil 1)
        '(t ((t :more 0 8 1 (0 2) (0 1) t)))))
