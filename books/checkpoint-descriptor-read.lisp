; Cold descriptor authentication and capture, separate from checkpoint construction.
; These existing carrier obligations remain active; extraction does not discharge them.
(in-package "ACL2")
(include-book "checkpoint-reader-interfaces")
(include-book "columns-carrier-contracts")
(include-book "owed")
(fn2-book-layer :b)

(defun fn2-checkpoint-check-step (c row slot gen off len base okind oslot ogen budget
                                fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                                fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                          fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
  :guard-hints ((fn2-columns-guard-hint
    '(fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
      fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
    '(fn2-format-run fn2-checkpoint-decode fn2-checkpoint-capture-roots
      fn2-checkpoint-hash-matchesp) nil world))
  :guard (and (fn2-fc-guard) (fn2-checkpoints-wfp fn2-checkpoints)
              (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes))))
 (b* (((unless (and (fn2-checkpoint-slotp c fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
                     (equal (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-preparing*)
                     (unsigned-byte-p 32 off) (unsigned-byte-p 32 len)))
       (mv :state fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests))
      (r (* 6 c))
      ((unless (and (equal (fn2-fc-context-location row fn2-fc-context) (fn2-checkpoint-refs-physical-unit r fn2-checkpoint-refs))
                     (equal (fn2-fc-context-allocation row fn2-fc-context) (fn2-checkpoint-refs-allocation r fn2-checkpoint-refs))
                     (equal (fn2-fc-context-writer-epoch row fn2-fc-context) (fn2-checkpoint-refs-writer-epoch r fn2-checkpoint-refs))
                     (equal (fn2-fc-context-history row fn2-fc-context) (fn2-checkpoints-history c fn2-checkpoints))
                     (equal (fn2-fc-context-incarnation row fn2-fc-context) (fn2-checkpoints-incarnation c fn2-checkpoints))
                     (equal (fn2-fc-context-page-kind row fn2-fc-context) *page-kind-checkpoint-descriptor*)
                     (equal len (fn2-checkpoint-refs-encoded-length r fn2-checkpoint-refs))
                     (equal len (fn2-fc-context-encoded-length row fn2-fc-context))
                     (fn2-checkpoint-hash-matchesp 0 (* 32 r) (fn2-fc-context-hash row fn2-fc-context) fn2-digests fn2-checkpoint-bytes)))
       (mv :context fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv code fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-format-run :page nil row slot gen off len base okind oslot ogen budget
                       fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((unless (eq code :ok))
       (mv code fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv code fn2-fields) (fn2-checkpoint-decode base slot gen off len okind oslot ogen fn2-fields fn2-pool))
      ((unless (and (eq code :ok)
                     (equal (fn2-fields-value (+ base *fn2-format-checkpoint-descriptor-field-checkpoint*) fn2-fields)
                            (fn2-checkpoints-checkpoint c fn2-checkpoints))))
       (mv :descriptor fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv code fn2-checkpoint-refs fn2-checkpoint-bytes)
       (fn2-checkpoint-capture-roots 0 c base slot gen okind oslot ogen
                                   fn2-fields fn2-pool fn2-checkpoint-refs fn2-checkpoint-bytes))
      ((unless (eq code :ok))
       (mv code fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests))
      (fn2-checkpoints (fn2-checkpoints-set-cut-commit c (fn2-fields-value (+ base *fn2-format-checkpoint-descriptor-field-cut-commit*) fn2-fields) fn2-checkpoints))
      (fn2-checkpoints (fn2-checkpoints-set-cut-event c (fn2-fields-value (+ base *fn2-format-checkpoint-descriptor-field-cut-event*) fn2-fields) fn2-checkpoints))
      (fn2-checkpoints (fn2-checkpoints-set-state c *fn2-checkpoint-state-checked* fn2-checkpoints)))
  (mv :ok fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)))

(local (defun fn2-checkpoint-reader-partition-contracts (args specs facts)
 (declare (xargs :verify-guards nil))
 (if (atom specs) nil
  (let* ((fact (car facts)) (position (caddar specs))
         (negative (cdr (assoc-equal position
                       '((4 . fn2-checkpoint-reader-checker-domain-removal-check)
                         (5 . fn2-checkpoint-reader-hasher-domain-removal-check)
                         (8 . fn2-checkpoint-reader-digests-domain-removal-check))))))
   (cons (if negative
          `(defthm-owed ,(cadr fact) ,args ,(caddr fact)
            :teeth (fn2-checkpoint-reader-guard-positive-check ,negative)
            :layer :b
            :doc "Original unrestricted carrier formula. Its exact closed-instance refutation and distinct stored-guard interface are in the reader refutation unit; this obligation is never discharged by that replacement.")
          fact)
         (fn2-checkpoint-reader-partition-contracts
          args (cdr specs) (cdr facts)))))))

(make-event
 (let* ((world (w state)) (name 'fn2-checkpoint-check-step)
        (args (getpropc name 'formals :missing world))
        (expected-args '(c row slot gen off len base okind oslot ogen budget fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
    fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
        (carriers '((fn2-checkpoints 1 :prefix "-CANDIDATES" :type-hints ((append
 (fn2-columns-guard-hint
  '(fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-fc-context
    fn2-b3 fn2-fields fn2-pool fn2-digests)
  '(fn2-format-run fn2-checkpoint-decode fn2-checkpoint-capture-roots fn2-checkpoint-hash-matchesp)
  '(fn2-checkpoint-check-step) world)
 '(:use ((:instance fn2-checkpoint-decode-ok-room-by-definition
 (fn2-fields (mv-nth 3 (fn2-format-run :page nil row slot gen off len base okind oslot ogen budget
                       fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
 (fn2-pool (mv-nth 4 (fn2-format-run :page nil row slot gen off len base okind oslot ogen budget
                       fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))))
(:instance fn2-checkpoint-decode-fields-domain-value-type (i (+ base 1))
 (fn2-fields (mv-nth 3 (fn2-format-run :page nil row slot gen off len base okind oslot ogen budget
                       fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
 (fn2-pool (mv-nth 4 (fn2-format-run :page nil row slot gen off len base okind oslot ogen budget
                       fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))))
(:instance fn2-checkpoint-decode-fields-domain-value-type (i (+ base 2))
 (fn2-fields (mv-nth 3 (fn2-format-run :page nil row slot gen off len base okind oslot ogen budget
                       fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
 (fn2-pool (mv-nth 4 (fn2-format-run :page nil row slot gen off len base okind oslot ogen budget
                       fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))))))))
            (fn2-checkpoint-refs 2 :prefix "-REFS") (fn2-checkpoint-bytes 3 :prefix "-BYTES")
            (fn2-fc 4 :prefix "-CHECKER") (fn2-b3 5 :prefix "-HASHER")
            (fn2-fields 6 :prefix "-FIELDS") (fn2-pool 7 :prefix "-POOL") (fn2-digests 8 :prefix "-DIGESTS")))
        (hints '((fn2-columns-guard-hint
    '(fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-fc-context
      fn2-b3 fn2-fields fn2-pool fn2-digests)
    '(fn2-format-run fn2-checkpoint-decode fn2-checkpoint-capture-roots fn2-checkpoint-hash-matchesp)
    '(fn2-checkpoint-check-step) world)))
        (hyps (fn2-columns-carrier-hyps carriers))
        (specs (fn2-columns-carrier-specs carriers))
        (facts (fn2-columns-preservation-facts name (cons name args) specs hyps hints)))
  (if (or (not (equal args expected-args))
          (not (fn2-columns-contract-carriersp carriers args
                (getpropc name 'stobjs-in nil world)
                (getpropc name 'stobjs-out nil world) world))
          (not (equal (len facts) 16)))
      (er soft 'checkpoint-reader-contract "Actual descriptor reader metadata changed.")
    (value `(progn
      ,@(fn2-checkpoint-reader-partition-contracts args specs facts)
      (in-theory (disable fn2-checkpoint-check-step)))))))

(defcolumns-guarded-contracts fn2-checkpoint-check-step
 :carriers ((fn2-fc 4 :prefix "-CHECKER") (fn2-b3 5 :prefix "-HASHER")
            (fn2-digests 8 :prefix "-DIGESTS"))
 :hints ((fn2-columns-guard-hint
    '(fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-fc-context
      fn2-b3 fn2-fields fn2-pool fn2-digests)
    '(fn2-format-run fn2-checkpoint-decode fn2-checkpoint-capture-roots fn2-checkpoint-hash-matchesp)
    '(fn2-checkpoint-check-step) world)))
