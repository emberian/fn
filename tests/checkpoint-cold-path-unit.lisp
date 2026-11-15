; Connected source fixture: actual image create -> ordinary prefix -> actual
; maintenance publication -> ordinary suffix -> simulated process death ->
; selected cold boot -> held final epoch Fence -> actual completion.
; UNEXECUTED. Assertions below target the actual final epoch/resource join.
; Catalog entry is test-only, parent-authorized: activation remains NIL and
; this makes no scheduler-reachability claim for automatic maintenance.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-cold-path-producer-support")


(defun fn2-ccp-body (fault fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* ((fn2-core (fn2-init-executor *fn2-ccp-profile* :null nil fn2-core))
      (fn2-sim (fn2-sim-init 1 :none "checkpoint-cold-path" *fn2-ccp-profile* fn2-sim))
      (fn2-own (fn2-own-init *fn2-ccp-profile* fn2-own))
      ((mv started fn2-core) (fn2-boot-start t *fn2-ccp-image-size* fn2-core))
      ((mv created fn2-core fn2-sim fn2-own) (fn2-ccp-drive 200000 nil fn2-core fn2-sim fn2-own))
      ((unless (and (eq started :ok) (eq created :ready)))
       (mv (list :create started created) fn2-core fn2-sim fn2-own))
      ((mv published prefix suffix fn2-core fn2-sim fn2-own) (fn2-ccp-prefix-and-publication fn2-core fn2-sim fn2-own))
      ((unless (eq published :complete)) (mv (list :publication published) fn2-core fn2-sim fn2-own))
      ((mv restarted fn2-core fn2-sim fn2-own) (fn2-ccp-restart *fn2-ccp-profile* *fn2-ccp-image-size* fn2-core fn2-sim fn2-own))
      ((mv held fn2-core fn2-sim fn2-own) (fn2-ccp-drive 600000 t fn2-core fn2-sim fn2-own))
      ((unless (and (eq restarted :ok) (eq held :epoch-held) (fn2-ccp-before-open-p prefix suffix fn2-core)))
       (mv (list :selected restarted held) fn2-core fn2-sim fn2-own))
      (boot (fn2-machine-kind-base *fn2-boot-kind* fn2-core))
      (owner-generation (fn2-machine-generation boot fn2-core))
      (root-slot (fn2-machine-root-slot boot fn2-core)) (root-gen (fn2-machine-root-gen boot fn2-core))
      (closed-epoch (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (epoch)
                     (fn2-alloc-current-epoch fn2-extents) epoch))
      ((mv posted fn2-core fn2-sim fn2-own) (fn2-ccp-complete-epoch fault fn2-core fn2-sim fn2-own))
      ((mv finished fn2-core fn2-sim fn2-own) (fn2-ccp-drive 200000 nil fn2-core fn2-sim fn2-own))
      ((mv phase begun epoch window rebindable)
       (stobj-let ((fn2-extents (fn2-core-extents fn2-core)) (fn2-pool (fn2-core-pool fn2-core))
                   (fn2-checkpoint-payload (fn2-core-checkpoint-payload fn2-core))) (phase begun epoch window rebindable)
        (mv (fn2-alloc-freeze-phase fn2-extents) (fn2-alloc-epoch-begun fn2-extents)
            (fn2-alloc-current-epoch fn2-extents)
            (fn2-pool-workspace-code root-slot root-gen *fn2-boot-kind* boot owner-generation fn2-pool)
            (fn2-checkpoint-payload-rebindablep fn2-checkpoint-payload))
        (mv phase begun epoch window rebindable)))
      (open (if (and (= phase 0) (= begun 1) (< closed-epoch epoch)
                     (member-eq window '(:stale :state)) rebindable) t nil)))
  (mv (list posted finished open prefix suffix (list phase begun epoch window rebindable closed-epoch)) fn2-core fn2-sim fn2-own)))

(defun fn2-ccp-test (fault)
 (declare (xargs :verify-guards nil))
 (fn2-run-with-local (fn2-core fn2-sim fn2-own)
  (fn2-ccp-body fault fn2-core fn2-sim fn2-own)))
; Each assertion constructs its own image, publication, suffix and crash. No
; previous synthetic terminal fixture or saved READY core supplies authority.
(assert-event
 (let* ((result (fn2-ccp-test *fn2-fault-none*)) (facts (nth 5 result)))
  (and (eq (car result) :posted) (eq (cadr result) :ready) (eq (nth 2 result) t)
       (posp (nth 3 result)) (< (+ 1 (nth 3 result)) (nth 4 result))
       (= (len facts) 6) (= (nth 0 facts) 0) (= (nth 1 facts) 1)
       (< (nth 5 facts) (nth 2 facts)) (member-eq (nth 3 facts) '(:stale :state))
       (nth 4 facts))))
(assert-event
 (let* ((result (fn2-ccp-test *fn2-fault-flush-io*)) (facts (nth 5 result)))
  (and (eq (car result) :posted) (eq (cadr result) :failed) (not (nth 2 result))
       (posp (nth 3 result)) (< (+ 1 (nth 3 result)) (nth 4 result))
       (= (len facts) 6) (= (nth 0 facts) 4) (= (nth 1 facts) 0)
       (= (nth 2 facts) (nth 5 facts)) (eq (nth 3 facts) :ok) (nth 4 facts))))
