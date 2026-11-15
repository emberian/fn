; Real guarded execution of the actual member, not a packer clone.
(in-package "ACL2")
(include-book "../books/checkpoint-member")
(include-book "std/util/bstar" :dir :system)

; Freeze the whole stored guard from the admitted function. Readonly stobj
; recognizers are checked explicitly as well, and H is saved before mutation.
(make-event
 (let* ((name 'fn2-checkpoint-installation-pack-member)
        (args (getpropc name 'formals :missing (w state)))
        (guard (getpropc name 'guard :missing (w state))))
  (if (or (eq guard :missing)
          (not (equal args '(c base slot gen okind oslot ogen
                 fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields fn2-pool))))
      (er soft 'checkpoint-member-positive "Actual member signature/guard changed.")
    (value
     `(defun fn2-checkpoint-member-positive-run
        (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields fn2-pool)
       (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields fn2-pool)
                       :verify-guards nil))
       (let* ((c 0) (base 0) (slot 0) (gen 0) (okind 0) (oslot 0) (ogen 0)
        (fn2-checkpoints (fn2-checkpoints-init 1 fn2-checkpoints))
        (fn2-checkpoints (fn2-checkpoints-set-state 0 *fn2-checkpoint-state-checked* fn2-checkpoints))
        (fn2-checkpoints (fn2-checkpoints-set-checkpoint 0 1 fn2-checkpoints))
        (fn2-checkpoint-refs (fn2-checkpoint-refs-init 6 fn2-checkpoint-refs))
        (fn2-checkpoint-bytes (fn2-checkpoint-bytes-init 192 fn2-checkpoint-bytes))
        (fn2-fields (fn2-fields-init
                     (+ *fn2-format-txn-record-num-fields* *fn2-format-checkpoint-installation-num-fields*) fn2-fields))
        (fn2-pool (fn2-pool-columns-init 1 fn2-pool))
        (fn2-pool (resize-fn2-pool-data (fn2-checkpoint-installation-member-capacity) fn2-pool))
        (fn2-pool (fn2-pool-set-cap 0 (fn2-checkpoint-installation-member-capacity) fn2-pool))
        (fn2-pool (fn2-pool-set-state 0 *fn2-pool-state-workspace* fn2-pool)))
        (let ((whole-h
               (and ,guard
                    (fn2-checkpointsp fn2-checkpoints) (fn2-checkpoints-wfp fn2-checkpoints)
                    (fn2-checkpoint-refsp fn2-checkpoint-refs) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs)
                    (fn2-checkpoint-bytesp fn2-checkpoint-bytes) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes)
                    ; The whole old carrier H is included, not just the new guard.
                    (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
                    (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                    (fn2-checkpoint-slotp c fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
                    (eq (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool) :ok))))
         (mv-let (code length fn2-fields fn2-pool)
          (fn2-checkpoint-installation-pack-member c base slot gen okind oslot ogen
           fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields fn2-pool)
          (mv (and whole-h (eq code :ok) (posp length)
                   (equal (fn2-pool-fill slot fn2-pool) length)
                   (equal (fn2-fields-value
                           (+ *fn2-format-txn-record-num-fields* *fn2-format-checkpoint-installation-field-checkpoint*)
                           fn2-fields) 1)
                   (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
                   (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
           fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields fn2-pool)))))))))

(defun fn2-checkpoint-member-fields-type-positive-check ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-checkpoints
   (mv-let (answer fn2-checkpoints)
    (with-local-stobj fn2-checkpoint-refs
   (mv-let (answer fn2-checkpoints fn2-checkpoint-refs)
    (with-local-stobj fn2-checkpoint-bytes
   (mv-let (answer fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
    (with-local-stobj fn2-fields
   (mv-let (answer fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields)
    (with-local-stobj fn2-pool
   (mv-let (answer fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields fn2-pool)
    (fn2-checkpoint-member-positive-run fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields fn2-pool)
    (mv answer fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields)))
    (mv answer fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)))
    (mv answer fn2-checkpoints fn2-checkpoint-refs)))
    (mv answer fn2-checkpoints)))
    answer)))
(assert-event (equal (fn2-checkpoint-member-fields-type-positive-check) t))
