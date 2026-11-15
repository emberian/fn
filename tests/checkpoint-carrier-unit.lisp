; Actual RETAIN boundary controls; no served function or guard changes.
(in-package "ACL2")
(include-book "../books/checkpoint")
(include-book "std/testing/must-fail" :dir :system)

(assert-event
 (let ((world (w state)))
  (equal
   (fn2-columns-readonly-type-hyps
    (getpropc 'fn2-checkpoint-retain 'formals nil world)
    (getpropc 'fn2-checkpoint-retain 'stobjs-in nil world)
    (getpropc 'fn2-checkpoint-retain 'stobjs-out nil world) world)
   '((fn2-checkpointsp fn2-checkpoints)
     (fn2-checkpoint-bytesp fn2-checkpoint-bytes) (fn2-opsp fn2-ops)))))
(assert-event
 (and (not (logical-namep 'fn2-checkpoint-retain-edges-type (w state)))
      (logical-namep
       'fn2-checkpoint-retain-edges-type-under-readonly-types (w state))
      (logical-namep 'fn2-checkpoint-retain-refs-type (w state))
      (logical-namep 'fn2-checkpoint-retain-refs-wfp (w state))
      (logical-namep 'fn2-checkpoint-retain-extents-type (w state))
      (logical-namep 'fn2-checkpoint-retain-extents-wfp (w state))
      (logical-namep 'fn2-checkpoint-retain-edges-wfp (w state))))

; A stale output projection is rejected before any theorem can be emitted.
(must-fail
 (defcolumns-carrier-contracts fn2-checkpoint-retain
  :carriers ((fn2-alloc-edges 1 :prefix "-WRONG"))
  :typed-readonly (fn2-alloc-edges))
 :expected :soft :check-expansion t)

; Absent WFP hints inherit; explicit nil and explicit overrides remain exact.
(assert-event
 (equal
  (fn2-columns-inherit-carrier-hints
   '((fn2-checkpoint-refs 1) (fn2-extents 2 :hints nil)
     (fn2-alloc-edges 3 :hints (("Goal" :do-not-induct t))))
   '(("Goal" :do-not '(generalize))))
  '((fn2-checkpoint-refs 1 :hints (("Goal" :do-not '(generalize))))
    (fn2-extents 2 :hints nil)
    (fn2-alloc-edges 3 :hints (("Goal" :do-not-induct t))))))

; The ACCOUNT strategy observes scalar frames without exposing the record
; predicate, indexed NTH implementation, or raw updater bodies.
(assert-event
 (let* ((hint (fn2-columns-scalar-frame-hint
                '(fn2-extents) '(fn2-alloc-account)
                '(fn2-alloc-adjust fn2-alloc-adjust-okp fn2-alloc-reason)
                (w state)))
        (theory (cadr hint)) (opened (cadr theory)) (closed (caddr theory)))
  (and (member-eq 'fn2-alloc-total-free opened)
       (member-eq 'fn2-alloc-total-reserved opened)
       (member-eq 'update-fn2-alloc-total-free closed)
       (member-eq 'fn2-extentsp closed) (member-eq 'nth closed)
       (not (member-eq 'fn2-extents-state opened)))))

; Unreachable-in-composition: the bad readonly holder violates the served
; guard's implicit checkpoint type. It satisfies the ENTIRE retired premise.
(defthm fn2-checkpoint-retain-readonly-type-removal-witness
 (let* ((cps (fn2-checkpoints-init 1 (create-fn2-checkpoints)))
        (cps (fn2-checkpoints-set-state 0 *fn2-checkpoint-state-checked* cps))
        (cps (fn2-checkpoints-set-checkpoint 0 -1 cps))
        (refs (fn2-checkpoint-refs-init 6 (create-fn2-checkpoint-refs)))
        (bytes (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (ext (fn2-alloc-columns-init 1 (create-fn2-extents)))
        (ext (fn2-extents-set-state 0 *fn2-extent-state-reserved* ext))
        (edges (fn2-alloc-edges-init 9 (create-fn2-alloc-edges)))
        (ops (create-fn2-ops))
        (edge (fn2-checkpoint-edge 0 0 ext ops))
        (out (fn2-checkpoint-retain 0 0 edge cps refs bytes ext edges ops)))
  (and
   ; Entire existing footer antecedent, not merely the dropped hypothesis.
   (fn2-checkpoint-refsp refs) (fn2-checkpoint-refs-wfp refs)
   (fn2-extentsp ext) (fn2-extents-wfp ext)
   (fn2-alloc-edgesp edges) (fn2-alloc-edges-wfp edges)
   ; Other readonly state is typed; isolate only the checkpoint holder type.
   (fn2-checkpoint-bytesp bytes) (fn2-checkpoint-bytes-wfp bytes)
   (fn2-opsp ops) (fn2-ops-wfp ops)
   (fn2-checkpoints-wfp cps) (not (fn2-checkpointsp cps))
   (fn2-checkpoint-slotp 0 cps refs bytes)
   (equal edge 8)
   (equal (car out) :ok)
   (equal (fn2-alloc-edges-holder edge (mv-nth 3 out)) -1)
   (not (fn2-alloc-edgesp (mv-nth 3 out)))))
 :rule-classes nil
 :hints (("Goal"
  :in-theory (e/d (create-fn2-ops fn2-checkpoint-retain fn2-alloc-edge-add) (fn2-checkpointsp fn2-alloc-edgesp))
  :use ((:instance fn2-checkpoints-checkpoint-natp (i 0) (fn2-checkpoints (fn2-checkpoints-set-checkpoint 0 -1 (fn2-checkpoints-set-state 0 *fn2-checkpoint-state-checked* (fn2-checkpoints-init 1 (create-fn2-checkpoints))))))
        (:instance fn2-alloc-edges-holder-natp (i 8) (fn2-alloc-edges (mv-nth 3 (fn2-checkpoint-retain 0 0 (fn2-checkpoint-edge 0 0 (fn2-extents-set-state 0 *fn2-extent-state-reserved* (fn2-alloc-columns-init 1 (create-fn2-extents))) (create-fn2-ops)) (fn2-checkpoints-set-checkpoint 0 -1 (fn2-checkpoints-set-state 0 *fn2-checkpoint-state-checked* (fn2-checkpoints-init 1 (create-fn2-checkpoints)))) (fn2-checkpoint-refs-init 6 (create-fn2-checkpoint-refs)) (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)) (fn2-extents-set-state 0 *fn2-extent-state-reserved* (fn2-alloc-columns-init 1 (create-fn2-extents))) (fn2-alloc-edges-init 9 (create-fn2-alloc-edges)) (create-fn2-ops)))))))))

(defthm fn2-checkpoint-retain-typed-readonly-positive
 (let* ((cps (fn2-checkpoints-init 1 (create-fn2-checkpoints)))
        (cps (fn2-checkpoints-set-state 0 *fn2-checkpoint-state-checked* cps))
        (cps (fn2-checkpoints-set-checkpoint 0 1 cps))
        (refs (fn2-checkpoint-refs-init 6 (create-fn2-checkpoint-refs)))
        (bytes (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (ext (fn2-alloc-columns-init 1 (create-fn2-extents)))
        (ext (fn2-extents-set-state 0 *fn2-extent-state-reserved* ext))
        (edges (fn2-alloc-edges-init 9 (create-fn2-alloc-edges)))
        (ops (create-fn2-ops))
        (edge (fn2-checkpoint-edge 0 0 ext ops))
        (out (fn2-checkpoint-retain 0 0 edge cps refs bytes ext edges ops)))
  (and
   ; Entire existing footer antecedent, not merely the dropped hypothesis.
   (fn2-checkpoint-refsp refs) (fn2-checkpoint-refs-wfp refs)
   (fn2-extentsp ext) (fn2-extents-wfp ext)
   (fn2-alloc-edgesp edges) (fn2-alloc-edges-wfp edges)
   ; Other readonly state is typed; isolate only the checkpoint holder type.
   (fn2-checkpoint-bytesp bytes) (fn2-checkpoint-bytes-wfp bytes)
   (fn2-opsp ops) (fn2-ops-wfp ops)
   (fn2-checkpoints-wfp cps) (fn2-checkpointsp cps)
   (fn2-checkpoint-slotp 0 cps refs bytes)
   (equal edge 8)
   (equal (car out) :ok)
   (equal (fn2-alloc-edges-holder edge (mv-nth 3 out)) 1)
   (fn2-alloc-edgesp (mv-nth 3 out))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable create-fn2-ops fn2-checkpoint-retain fn2-alloc-edge-add))))
