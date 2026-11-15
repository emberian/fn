; Descriptor-reader controls. HASHER obligations remain unresolved.
(in-package "ACL2")
(include-book "../books/checkpoint-descriptor-read")


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

; Whole actual stored entry guard, all original carrier premises and a real
; FORMAT-RUN bounds path. This is the positive for the guarded replacement.
(make-event
 (let ((guard (getpropc 'fn2-checkpoint-check-step 'guard :missing (w state))))
  (if (eq guard :missing)
      (er soft 'fn2-checkstep-full-guard-positive "Missing actual CHECK-STEP guard.")
   (value
    `(defthm fn2-checkstep-checker-full-guard-positive
      (let* ((c 0) (row 1) (slot 0) (gen 0) (off 0) (len 0) (base 0)
             (okind 0) (oslot 0) (ogen 0) (budget 1)
             (fn2-checkpoints (fn2-checkpoints-init 1 (create-fn2-checkpoints)))
             (fn2-checkpoints (fn2-checkpoints-set-state c *fn2-checkpoint-state-preparing* fn2-checkpoints))
             (fn2-checkpoint-refs (fn2-checkpoint-refs-init 6 (create-fn2-checkpoint-refs)))
             (fn2-checkpoint-bytes (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
             (fn2-fc (fn2-fc-init 2 (create-fn2-fc)))
             (fn2-fc-context (fn2-fc-context-init 2 (create-fn2-fc-context)))
             (fn2-fc-context (fn2-fc-context-set-page-kind row *page-kind-checkpoint-descriptor* fn2-fc-context))
             (fn2-fc-context (fn2-fc-context-set-hash row (fn2-digest-slot row *fn2-fc-hash*) fn2-fc-context))
             (fn2-fc-context (fn2-fc-context-set-geometry row (fn2-digest-slot row *fn2-fc-geometry*) fn2-fc-context))
             (fn2-fc-context (fn2-fc-context-set-previous-seal row (fn2-digest-slot row *fn2-fc-previous-seal*) fn2-fc-context))
             (fn2-b3 (fn2-b3-table-init 2 (create-fn2-b3)))
             (fn2-fields (fn2-fields-init *fn2-format-sealed-batch-num-fields* (create-fn2-fields)))
             (fn2-pool (create-fn2-pool))
             (fn2-digests (fn2-digests-init (* 2 *fn2-digest-stride*) (create-fn2-digests)))
             (out (fn2-checkpoint-check-step c row slot gen off len base okind oslot ogen budget
                     fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                     fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
       (and
        ; Complete original eight-carrier H.
        (fn2-checkpointsp fn2-checkpoints) (fn2-checkpoints-wfp fn2-checkpoints)
        (fn2-checkpoint-refsp fn2-checkpoint-refs) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs)
        (fn2-checkpoint-bytesp fn2-checkpoint-bytes) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes)
        (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc)
        (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
        (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
        (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
        (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
        (fn2-fc-contextp fn2-fc-context)
        ,guard
        ; Reach the real checker, rather than its invalid-state/context exits.
        (fn2-checkpoint-slotp c fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
        (fn2-checkpoint-hash-matchesp 0 0 (fn2-digest-slot row *fn2-fc-hash*) fn2-digests fn2-checkpoint-bytes)
        (equal (car out) :bounds)
        (fn2-fcp (mv-nth 4 out)) (fn2-fc-wfp (mv-nth 4 out))
        (equal (fn2-fc-rows (mv-nth 4 out)) 2)))
      :rule-classes nil
      :hints (("Goal"
       :in-theory (e/d
        (fn2-checkpoint-check-step fn2-fc-word-byte fn2-digest-word
         fn2-format-run fn2-fc-step fn2-fc-run-bytes fn2-fc-advance
         fn2-fc-byte fn2-fc-reset fn2-layout-range-code
         fn2-pool-readable-code fn2-pool-handle-code fn2-pool-rows
         create-fn2-pool fn2-b3-ready fn2-digest-workspacep fn2-digest-rowp)
        (fn2-checkpointsp fn2-checkpoints-wfp fn2-checkpoint-refsp fn2-checkpoint-refs-wfp fn2-checkpoint-bytesp fn2-checkpoint-bytes-wfp fn2-fcp fn2-fc-wfp fn2-fc-contextp fn2-fc-context-wfp fn2-b3p fn2-b3-wfp fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp fn2-digestsp fn2-digests-wfp))
       :expand (
        (fn2-checkpoint-hash-matchesp 0 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 1 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 2 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 3 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 4 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 5 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 6 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 7 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 8 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 9 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 10 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 11 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 12 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 13 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 14 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 15 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 16 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 17 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 18 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 19 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 20 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 21 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 22 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 23 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 24 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 25 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 26 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 27 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 28 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 29 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 30 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-checkpoint-hash-matchesp 31 0 ,(fn2-digest-slot 1 *fn2-fc-hash*)
         (fn2-digests-init ,(* 2 *fn2-digest-stride*) (create-fn2-digests))
         (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))))))))))
