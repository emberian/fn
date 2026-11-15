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

; The actual stored entry guard already supplies the readonly typing that
; generated core faces lift. This control uses no manually added premise.
(make-event
 (let* ((world (w state)) (name 'fn2-checkpoint-retain)
        (args (getpropc name 'formals nil world))
        (guard (getpropc name 'guard :missing world)))
  (if (eq guard :missing)
      (er soft 'checkpoint-carrier-unit "Missing actual RETAIN guard.")
    (value
     `(defthm fn2-checkpoint-retain-edge-type-for-verified-callers
       (implies ,guard
        (fn2-alloc-edgesp (mv-nth 3 (,name ,@args))))
       :rule-classes nil
       :hints (("Goal" :in-theory (disable fn2-checkpoint-retain))))))))

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

; Unreachable under the served row guard. The entire original carrier H
; holds, but the actual CHECK-STEP result refutes CHECKER TYPE and WFP.
(defthm fn2-checkstep-checker-row-counterterm
 (let* ((cps (fn2-checkpoints-init 1 (create-fn2-checkpoints)))
        (cps (fn2-checkpoints-set-state 0 *fn2-checkpoint-state-preparing* cps))
        (refs (fn2-checkpoint-refs-init 6 (create-fn2-checkpoint-refs)))
        (bytes (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fc (fn2-fc-init 0 (create-fn2-fc)))
        (ctx (fn2-fc-context-init 2 (create-fn2-fc-context)))
        (ctx (fn2-fc-context-set-page-kind 1 *page-kind-checkpoint-descriptor* ctx))
        (b3 (create-fn2-b3))
        (fields (fn2-fields-init 0 (create-fn2-fields)))
        (pool (create-fn2-pool))
        (digests (fn2-digests-init 1 (create-fn2-digests)))
        (out (fn2-checkpoint-check-step 0 1 0 0 0 0 0 0 0 0 1
                      cps refs bytes fc ctx b3 fields pool digests)))
  (and
   (fn2-checkpointsp cps) (fn2-checkpoints-wfp cps)
   (fn2-checkpoint-refsp refs) (fn2-checkpoint-refs-wfp refs)
   (fn2-checkpoint-bytesp bytes) (fn2-checkpoint-bytes-wfp bytes)
   (fn2-fcp fc) (fn2-fc-wfp fc)
   (fn2-b3p b3) (fn2-b3-wfp b3)
   (fn2-fieldsp fields) (fn2-fields-wfp fields)
   (fn2-poolp pool) (fn2-pool-wfp pool)
   (fn2-digestsp digests) (fn2-digests-wfp digests)
   (fn2-fc-contextp ctx) (fn2-fc-context-wfp ctx)
   (not (< 1 (fn2-fc-rows fc)))
   (fn2-checkpoint-slotp 0 cps refs bytes)
   (fn2-checkpoint-hash-matchesp 0 0 0 digests bytes)
   (equal (car out) :state)
   (equal (fn2-fc-rows (mv-nth 4 out)) 0)
   (equal (fn2-fc-phase 0 (mv-nth 4 out)) nil)
   (not (fn2-fcp (mv-nth 4 out)))
   (not (fn2-fc-wfp (mv-nth 4 out)))))
 :rule-classes nil :hints (("Goal"
  :in-theory (enable fn2-fc-word-byte fn2-digest-word
                    fn2-format-run fn2-fc-step fn2-fc-run-bytes
                    fn2-fc-advance fn2-fc-byte fn2-fc-reset
                    fn2-fcp fn2-fc-wfp)
  :expand (
    (fn2-checkpoint-hash-matchesp 0 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 1 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 2 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 3 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 4 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 5 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 6 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 7 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 8 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 9 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 10 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 11 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 12 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 13 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 14 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 15 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 16 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 17 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 18 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 19 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 20 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 21 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 22 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 23 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 24 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 25 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 26 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 27 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 28 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 29 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 30 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 31 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))))))

; Positive for the original H plus valid checker row. This does not assert
; the full stored entry guard; the full guard positive is a separate control.
(defthm fn2-checkstep-checker-row-positive
 (let* ((cps (fn2-checkpoints-init 1 (create-fn2-checkpoints)))
        (cps (fn2-checkpoints-set-state 0 *fn2-checkpoint-state-preparing* cps))
        (refs (fn2-checkpoint-refs-init 6 (create-fn2-checkpoint-refs)))
        (bytes (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fc (fn2-fc-init 2 (create-fn2-fc)))
        (ctx (fn2-fc-context-init 2 (create-fn2-fc-context)))
        (ctx (fn2-fc-context-set-page-kind 1 *page-kind-checkpoint-descriptor* ctx))
        (b3 (create-fn2-b3))
        (fields (fn2-fields-init 0 (create-fn2-fields)))
        (pool (create-fn2-pool))
        (digests (fn2-digests-init 1 (create-fn2-digests)))
        (out (fn2-checkpoint-check-step 0 1 0 0 0 0 0 0 0 0 1
                      cps refs bytes fc ctx b3 fields pool digests)))
  (and
   (fn2-checkpointsp cps) (fn2-checkpoints-wfp cps)
   (fn2-checkpoint-refsp refs) (fn2-checkpoint-refs-wfp refs)
   (fn2-checkpoint-bytesp bytes) (fn2-checkpoint-bytes-wfp bytes)
   (fn2-fcp fc) (fn2-fc-wfp fc)
   (fn2-b3p b3) (fn2-b3-wfp b3)
   (fn2-fieldsp fields) (fn2-fields-wfp fields)
   (fn2-poolp pool) (fn2-pool-wfp pool)
   (fn2-digestsp digests) (fn2-digests-wfp digests)
   (fn2-fc-contextp ctx) (fn2-fc-context-wfp ctx)
   (< 1 (fn2-fc-rows fc))
   (fn2-checkpoint-slotp 0 cps refs bytes)
   (fn2-checkpoint-hash-matchesp 0 0 0 digests bytes)
   (equal (car out) :bounds)
   (equal (fn2-fc-rows (mv-nth 4 out)) 2)
   (equal (fn2-fc-phase 0 (mv-nth 4 out)) *fn2-fc-phase-idle*)
   (fn2-fcp (mv-nth 4 out))
   (fn2-fc-wfp (mv-nth 4 out))))
 :rule-classes nil :hints (("Goal"
  :in-theory (e/d
   (fn2-fc-word-byte fn2-digest-word fn2-format-run fn2-fc-step
    fn2-fc-run-bytes fn2-fc-advance fn2-fc-byte fn2-fc-reset
    fn2-layout-range-code fn2-pool-readable-code fn2-pool-handle-code
    fn2-pool-rows create-fn2-pool)
   (fn2-checkpointsp fn2-checkpoints-wfp fn2-checkpoint-refsp fn2-checkpoint-refs-wfp fn2-checkpoint-bytesp fn2-checkpoint-bytes-wfp fn2-fcp fn2-fc-wfp fn2-fc-contextp fn2-fc-context-wfp fn2-b3p fn2-b3-wfp fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp fn2-digestsp fn2-digests-wfp))
  :expand (
    (fn2-checkpoint-hash-matchesp 0 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 1 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 2 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 3 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 4 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 5 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 6 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 7 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 8 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 9 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 10 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 11 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 12 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 13 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 14 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 15 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 16 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 17 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 18 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 19 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 20 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 21 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 22 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 23 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 24 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 25 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 26 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 27 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 28 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 29 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 30 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 31 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))))))

; Classify every output at the exact row counterexample. The other seven
; outputs are typed/WFP here; this is not a universal claim about them.
(defthm fn2-checkstep-row-output-carrier-classification
 (let* ((cps (fn2-checkpoints-init 1 (create-fn2-checkpoints)))
        (cps (fn2-checkpoints-set-state 0 *fn2-checkpoint-state-preparing* cps))
        (refs (fn2-checkpoint-refs-init 6 (create-fn2-checkpoint-refs)))
        (bytes (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fc (fn2-fc-init 0 (create-fn2-fc)))
        (ctx (fn2-fc-context-init 2 (create-fn2-fc-context)))
        (ctx (fn2-fc-context-set-page-kind 1 *page-kind-checkpoint-descriptor* ctx))
        (b3 (create-fn2-b3))
        (fields (fn2-fields-init 0 (create-fn2-fields)))
        (pool (create-fn2-pool))
        (digests (fn2-digests-init 1 (create-fn2-digests)))
        (out (fn2-checkpoint-check-step 0 1 0 0 0 0 0 0 0 0 1
                      cps refs bytes fc ctx b3 fields pool digests)))
  (and
   (fn2-checkpointsp cps) (fn2-checkpoints-wfp cps)
   (fn2-checkpoint-refsp refs) (fn2-checkpoint-refs-wfp refs)
   (fn2-checkpoint-bytesp bytes) (fn2-checkpoint-bytes-wfp bytes)
   (fn2-fcp fc) (fn2-fc-wfp fc)
   (fn2-b3p b3) (fn2-b3-wfp b3)
   (fn2-fieldsp fields) (fn2-fields-wfp fields)
   (fn2-poolp pool) (fn2-pool-wfp pool)
   (fn2-digestsp digests) (fn2-digests-wfp digests)
   (fn2-fc-contextp ctx) (fn2-fc-context-wfp ctx)
   (not (< 1 (fn2-fc-rows fc)))
   (fn2-checkpoint-slotp 0 cps refs bytes)
   (fn2-checkpoint-hash-matchesp 0 0 0 digests bytes)
   (equal (car out) :state)
   (equal (fn2-fc-rows (mv-nth 4 out)) 0)
   (equal (fn2-fc-phase 0 (mv-nth 4 out)) nil)
   (fn2-checkpointsp (mv-nth 1 out)) (fn2-checkpoints-wfp (mv-nth 1 out))
   (fn2-checkpoint-refsp (mv-nth 2 out)) (fn2-checkpoint-refs-wfp (mv-nth 2 out))
   (fn2-checkpoint-bytesp (mv-nth 3 out)) (fn2-checkpoint-bytes-wfp (mv-nth 3 out))
   (fn2-b3p (mv-nth 5 out)) (fn2-b3-wfp (mv-nth 5 out))
   (fn2-fieldsp (mv-nth 6 out)) (fn2-fields-wfp (mv-nth 6 out))
   (fn2-poolp (mv-nth 7 out)) (fn2-pool-wfp (mv-nth 7 out))
   (fn2-digestsp (mv-nth 8 out)) (fn2-digests-wfp (mv-nth 8 out))
   (not (fn2-fcp (mv-nth 4 out)))
   (not (fn2-fc-wfp (mv-nth 4 out)))))
 :rule-classes nil
  :hints (("Goal"
  :in-theory (enable fn2-fc-word-byte fn2-digest-word
                    fn2-format-run fn2-fc-step fn2-fc-run-bytes
                    fn2-fc-advance fn2-fc-byte fn2-fc-reset
                    fn2-fcp fn2-fc-wfp)
  :expand (
    (fn2-checkpoint-hash-matchesp 0 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 1 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 2 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 3 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 4 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 5 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 6 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 7 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 8 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 9 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 10 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 11 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 12 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 13 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 14 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 15 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 16 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 17 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 18 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 19 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 20 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 21 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 22 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 23 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 24 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 25 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 26 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 27 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 28 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 29 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 30 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
    (fn2-checkpoint-hash-matchesp 31 0 0
     (fn2-digests-init 1 (create-fn2-digests))
     (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))))))

(assert-event
 (and (not (logical-namep 'fn2-checkpoint-check-step-checker-type (w state)))
      (not (logical-namep 'fn2-checkpoint-check-step-checker-wfp (w state)))
      (logical-namep 'fn2-checkpoint-check-step-checker-type-under-guard (w state))
      (logical-namep 'fn2-checkpoint-check-step-checker-wfp-under-guard (w state))))
