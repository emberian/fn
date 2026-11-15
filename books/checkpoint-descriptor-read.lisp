; Cold descriptor reader. The unresolved obligations remain active here.
(in-package "ACL2")
(include-book "checkpoint")
(include-book "format-check-read-contracts")
(fn2-book-layer :b)

(defun fn2-checkpoint-check-step (c row slot gen off len base okind oslot ogen budget
                                fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                                fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                          fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
  :guard-hints ((fn2-columns-guard-hint
                 '(fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                   fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
                 '(fn2-checkpoint-decode fn2-checkpoint-hash-matchesp
                   fn2-checkpoint-capture-roots fn2-b3-ready fn2-digest-rowp)
                 nil world))
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

(make-event
 (let* ((world (w state)) (name 'fn2-checkpoint-check-step)
        (args (getpropc name 'formals :missing world))
        (inputs (getpropc name 'stobjs-in nil world))
        (outputs (getpropc name 'stobjs-out nil world))
        (guard (getpropc name 'guard :missing world))
        (carriers '((fn2-checkpoints 1 :prefix "-CANDIDATES" )
            (fn2-checkpoint-refs 2 :prefix "-REFS" ) (fn2-checkpoint-bytes 3 :prefix "-BYTES" )
            (fn2-fc 4 :prefix "-CHECKER" ) (fn2-b3 5 :prefix "-HASHER" )
            (fn2-fields 6 :prefix "-FIELDS" ) (fn2-pool 7 :prefix "-POOL" ) (fn2-digests 8 :prefix "-DIGESTS" )))
        (hints '((append (fn2-columns-guard-hint
                 '(fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                   fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
                 '(fn2-checkpoint-decode fn2-checkpoint-hash-matchesp
                   fn2-checkpoint-capture-roots fn2-b3-ready fn2-digest-rowp)
                 '(fn2-checkpoint-check-step) world)
          '(:use ((:instance fn2-checkpoint-decode-ok-room-by-definition)
                  (:instance fn2-checkpoint-decode-value-type (i (+ base 1)))
                  (:instance fn2-checkpoint-decode-value-type (i (+ base 2))))))))
        (hyps (fn2-columns-carrier-hyps carriers))
        (specs (fn2-columns-carrier-specs
                 (fn2-columns-inherit-carrier-hints carriers hints)))
        (domain (remove-duplicates-equal
                 (append hyps
                  (fn2-columns-readonly-type-hyps args inputs nil world)
                  (list guard))))
        (checker (fn2-columns-guard-domain-specs (take 2 (nthcdr 6 specs))))
        (guarded (list (append (car checker) (list :hyps domain))
                       (append (cadr checker) (list :hyps domain)))))
  (if (or (eq args :missing) (eq guard :missing)
          (eq (getpropc name 'symbol-class nil world) :program)
          (not (fn2-columns-contract-carriersp carriers args inputs outputs world))
          (not (equal (nth 3 carriers) '(fn2-fc 4 :prefix "-CHECKER"))))
      (er soft 'checkpoint-carrier-domain "Actual CHECK-STEP carrier metadata changed.")
    (value
     (fn2-columns-preserves (caar carriers) name args nil hyps
      (append (take 6 specs) guarded (nthcdr 8 specs))
      "-PRESERVES" t t hints t nil nil nil nil)))))
