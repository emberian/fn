; Actual fresh table constructors cannot claim a selected source. This is a
; complete typed-domain/refusal frame control, not a phase-seeded positive
; checkpoint/recovery witness. Positive byte-to-source composition is owed
; through the actual producer/boot path, not fabricated here.
(in-package "ACL2")
(include-book "../books/checkpoint-restore-release-inventory-reader")
(include-book "../books/runs-page")
(include-book "column-snapshot-support")
(defconst *fn2-rir-children* '(fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-reader fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests fn2-checkpoint-restore-release-inventory fn2-checkpoint-restore-release-entries fn2-extents))
(defun fn2-rir-snapshot-events (children world)
 (declare (xargs :verify-guards nil))
 (if (atom children) nil
  (append (fn2-test-column-snapshot-events (car children) world)
          (fn2-rir-snapshot-events (cdr children) world))))
(make-event (cons 'progn (fn2-rir-snapshot-events *fn2-rir-children* (w state))))
(defun fn2-rir-snapshot-calls (children)
 (declare (xargs :verify-guards nil))
 (if (atom children) nil
  (cons (list (fn2-columns-sym 'fn2-test-table-snapshot- (symbol-name (car children))) (car children))
        (fn2-rir-snapshot-calls (cdr children)))))
(make-event
 (value `(defmacro fn2-rir-frame () '(list ,@(fn2-rir-snapshot-calls *fn2-rir-children*)))))
(make-event
 (value
 `(defun fn2-rir-body (,@*fn2-rir-children*)
  (declare (xargs :stobjs ,*fn2-rir-children* :verify-guards nil))
  (b* ((typed (and ,@(fn2-columns-carrier-hyps (fn2-checkpoint-release-carriers *fn2-rir-children* 0))))
       (before (fn2-rir-frame))
       ((mv capture fn2-checkpoint-restore-release-inventory)
        (fn2-checkpoint-restore-release-inventory-capture fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-reader fn2-checkpoint-restore-events fn2-fc fn2-fields fn2-pool fn2-checkpoint-restore-release-inventory))
       ((mv begin fn2-checkpoint-restore-reader fn2-checkpoint-restore-release-inventory fn2-pool)
        (fn2-checkpoint-restore-release-inventory-begin fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-reader fn2-checkpoint-restore-events fn2-pool fn2-checkpoint-restore-release-inventory fn2-checkpoint-restore-release-entries))
       ((mv page fn2-checkpoint-restore-reader fn2-checkpoint-restore-reach fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
        (fn2-checkpoint-restore-release-inventory-page-step 4096 fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-reader fn2-checkpoint-restore-release-inventory fn2-extents fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
       ((mv entry fn2-checkpoint-restore-reader fn2-checkpoint-restore-release-inventory fn2-checkpoint-restore-release-entries fn2-checkpoint-restore-reach fn2-fields)
        (fn2-checkpoint-restore-release-inventory-entry fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-reader fn2-checkpoint-restore-release-inventory fn2-checkpoint-restore-release-entries fn2-fields fn2-pool fn2-checkpoint-restore-events-work))
       ((mv finish fn2-checkpoint-restore-release-inventory)
        (fn2-checkpoint-restore-release-inventory-finish fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-reader fn2-checkpoint-restore-release-inventory fn2-checkpoint-restore-release-entries)))
   (mv (and typed (eq capture :source) (eq begin :source) (eq page :source) (eq entry :source) (eq finish :source)
            (equal before (fn2-rir-frame))
            (not (fn2-checkpoint-restore-release-inventory-complete-p fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-reader fn2-checkpoint-restore-release-inventory fn2-checkpoint-restore-release-entries)))
       ,@*fn2-rir-children*)))))
(make-event
 (value `(defun fn2-rir-test ()
  (declare (xargs :verify-guards nil))
  (fn2-run-with-local ,*fn2-rir-children* (fn2-rir-body ,@*fn2-rir-children*)))))
(assert-event (fn2-rir-test))
