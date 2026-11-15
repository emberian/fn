; Logical controls for original CHECK-STEP carrier claims and its actual guard.
; Source only until the ground theorems are admitted. Never execute an
; out-of-bounds typed stobj through raw Lisp; DEFUN-NX selects logical calls.
(in-package "ACL2")
(include-book "../books/checkpoint")
(include-book "../books/commit-geometry")

(defun-nx fn2-checkpoint-reader-scalar-domain-check (which)
 (let* ((row (if (eq which :checker) 2 1))
        (fc-n (if (eq which :checker) 1 (+ 1 row)))
        (b3-n (if (eq which :hasher) 0 (+ 1 row)))
        (digest-n (if (eq which :digests) 1 (* *fn2-digest-stride* (+ 1 row))))
        (fn2-checkpoints (fn2-checkpoints-init 1 (create-fn2-checkpoints)))
        (fn2-checkpoints (fn2-checkpoints-put 0 (state *fn2-checkpoint-state-preparing*)
                           (checkpoint 1) (history 1) (incarnation 1)))
        (fn2-checkpoint-refs (fn2-checkpoint-refs-init 6 (create-fn2-checkpoint-refs)))
        (fn2-checkpoint-refs (fn2-checkpoint-refs-put 0 (encoded-length *fn2-commit-unit-bytes*)
                              (writer-epoch 1) (allocation 1)))
        (fn2-checkpoint-bytes (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-fc (fn2-fc-init fc-n (create-fn2-fc)))
        (fn2-fc-context (fn2-fc-context-init (+ 1 row) (create-fn2-fc-context)))
        (fn2-fc-context (fn2-fc-context-put row (location 0) (allocation 1)
                          (history 1) (incarnation 1) (writer-epoch 1)
                          (page-kind *page-kind-checkpoint-descriptor*)
                          (encoded-length *fn2-commit-unit-bytes*)
                          (hash 0) (geometry 0) (previous-seal 0)))
        (fn2-b3 (fn2-b3-table-init b3-n (create-fn2-b3)))
        (fn2-fields (fn2-fields-init *fn2-format-sealed-batch-num-fields* (create-fn2-fields)))
        (fn2-pool (fn2-pool-columns-init 1 (create-fn2-pool)))
        (fn2-pool (resize-fn2-pool-data *fn2-commit-unit-bytes* fn2-pool))
        ; The resized octets are zero-initialized. This is a logical typed
        ; input, not a claimed authenticated page or fabricated source receipt.
        (fn2-pool (fn2-pool-put 0 (state *fn2-pool-state-workspace*)
                     (cap *fn2-commit-unit-bytes*) (fill *fn2-commit-unit-bytes*)))
        (fn2-digests (fn2-digests-init digest-n (create-fn2-digests)))
        (whole-h
         (and (fn2-checkpointsp fn2-checkpoints) (fn2-checkpoints-wfp fn2-checkpoints)
              (fn2-checkpoint-refsp fn2-checkpoint-refs) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs)
              (fn2-checkpoint-bytesp fn2-checkpoint-bytes) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes)
              (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc)
              (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
              (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
              (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
              (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)))
        (typed-readonly (and (fn2-fc-contextp fn2-fc-context)
                             (fn2-fc-context-wfp fn2-fc-context)))
        (base 0) (off 0) (len *fn2-commit-unit-bytes*)
        (whole-guard (and (fn2-fc-guard) (fn2-checkpoints-wfp fn2-checkpoints)
                          (fn2-checkpoint-refs-wfp fn2-checkpoint-refs)
                          (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes)))
        (answer (fn2-checkpoint-check-step 0 row 0 0 off len base 0 0 0 1
                  fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                  fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
  (and whole-h typed-readonly
   (fn2-checkpoint-slotp 0 fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
   (fn2-checkpoint-hash-matchesp 0 0 0 fn2-digests fn2-checkpoint-bytes)
   (case which
    (:checker
     (and (not (< row (fn2-fc-rows fn2-fc))) (not whole-guard)
          (eq (car answer) :state)
          (not (fn2-fcp (mv-nth 4 answer)))
          (not (fn2-fc-wfp (mv-nth 4 answer)))))
    (:hasher
     (and (< row (fn2-fc-rows fn2-fc))
          (not (< row (fn2-b3-rows fn2-b3))) (not whole-guard)
          (eq (car answer) :more)
          (not (fn2-b3p (mv-nth 5 answer)))
          (not (fn2-b3-wfp (mv-nth 5 answer)))))
    (:digests
     (and (< row (fn2-fc-rows fn2-fc)) (< row (fn2-b3-rows fn2-b3))
          (not (fn2-digest-workspacep row fn2-digests)) (not whole-guard)
          (eq (car answer) :more)
          (not (fn2-digestsp (mv-nth 8 answer)))
          (not (fn2-digests-wfp (mv-nth 8 answer)))))
    (otherwise
     ; A genuine initial checker visit, not an unchanged refusal. This is a
     ; carrier/guard control; no descriptor authenticity is asserted here.
     (and whole-guard (eq (car answer) :more)
          (equal (fn2-fc-phase row (mv-nth 4 answer)) *fn2-fc-phase-decode*)
          (fn2-checkpointsp (mv-nth 1 answer)) (fn2-checkpoints-wfp (mv-nth 1 answer))
          (fn2-checkpoint-refsp (mv-nth 2 answer)) (fn2-checkpoint-refs-wfp (mv-nth 2 answer))
          (fn2-checkpoint-bytesp (mv-nth 3 answer)) (fn2-checkpoint-bytes-wfp (mv-nth 3 answer))
          (fn2-fcp (mv-nth 4 answer)) (fn2-fc-wfp (mv-nth 4 answer))
          (fn2-b3p (mv-nth 5 answer)) (fn2-b3-wfp (mv-nth 5 answer))
          (fn2-fieldsp (mv-nth 6 answer)) (fn2-fields-wfp (mv-nth 6 answer))
          (fn2-poolp (mv-nth 7 answer)) (fn2-pool-wfp (mv-nth 7 answer))
          (fn2-digestsp (mv-nth 8 answer)) (fn2-digests-wfp (mv-nth 8 answer))))))))

 ; Keep raw stobj operators out of an intentionally off-guard logical gate.
; Select them from their actual ACL2 input/output metadata, not a second
; accessor list or a raw-array execution convention.
(local (defun fn2-checkpoint-scalar-table-execs (runes world)
 (declare (xargs :verify-guards nil))
 (if (atom runes) nil
  (let* ((rune (car runes)) (fn (cadr rune))
         (tables '(fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                   fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
   (if (and (consp rune) (eq (car rune) :executable-counterpart)
            (intersectp-eq tables
             (append (getpropc fn 'stobjs-in nil world)
                     (getpropc fn 'stobjs-out nil world))))
       (cons rune (fn2-checkpoint-scalar-table-execs (cdr runes) world))
     (fn2-checkpoint-scalar-table-execs (cdr runes) world))))))
(local (defun fn2-checkpoint-scalar-ground-hint (functions execs minimal world)
 (declare (xargs :verify-guards nil))
 (list :in-theory
  (set-difference-theories
   (union-theories functions (union-theories execs minimal))
   (cons '(:executable-counterpart fn2-checkpoint-reader-scalar-domain-check)
         (fn2-checkpoint-scalar-table-execs execs world))))))

; All four source questions are UNRUN. The negative predicates establish the
; whole ORIGINAL H plus a false TYPE/WFP conclusion only if actually proved.
; The positive predicate asserts the whole stored guard and all eight results.
(defthm fn2-checkpoint-reader-checker-scalar-domain-ground
 (fn2-checkpoint-reader-scalar-domain-check :checker)
 :rule-classes nil
 :hints ((fn2-checkpoint-scalar-ground-hint
          (function-theory :here) (executable-counterpart-theory :here)
          (theory 'minimal-theory) world)))
(defthm fn2-checkpoint-reader-hasher-scalar-domain-ground
 (fn2-checkpoint-reader-scalar-domain-check :hasher)
 :rule-classes nil
 :hints ((fn2-checkpoint-scalar-ground-hint
          (function-theory :here) (executable-counterpart-theory :here)
          (theory 'minimal-theory) world)))
(defthm fn2-checkpoint-reader-digests-scalar-domain-ground
 (fn2-checkpoint-reader-scalar-domain-check :digests)
 :rule-classes nil
 :hints ((fn2-checkpoint-scalar-ground-hint
          (function-theory :here) (executable-counterpart-theory :here)
          (theory 'minimal-theory) world)))
(defthm fn2-checkpoint-reader-positive-scalar-domain-ground
 (fn2-checkpoint-reader-scalar-domain-check :positive)
 :rule-classes nil
 :hints ((fn2-checkpoint-scalar-ground-hint
          (function-theory :here) (executable-counterpart-theory :here)
          (theory 'minimal-theory) world)))
