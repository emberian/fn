; Cold descriptor authentication and capture, separate from checkpoint construction.
; These existing carrier obligations remain active; extraction does not discharge them.
(in-package "ACL2")
(include-book "checkpoint")
(fn2-book-layer :b)

(defun fn2-checkpoint-check-step (c row slot gen off len base okind oslot ogen budget
                                fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                                fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                          fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
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

(fn2-checkpoints-preserves fn2-checkpoint-check-step
 (c row slot gen off len base okind oslot ogen budget fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
    fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 :carriers ((fn2-checkpoints 1 :prefix "-CANDIDATES")
            (fn2-checkpoint-refs 2 :prefix "-REFS") (fn2-checkpoint-bytes 3 :prefix "-BYTES")
            (fn2-fc 4 :prefix "-CHECKER") (fn2-b3 5 :prefix "-HASHER")
            (fn2-fields 6 :prefix "-FIELDS") (fn2-pool 7 :prefix "-POOL") (fn2-digests 8 :prefix "-DIGESTS")))
