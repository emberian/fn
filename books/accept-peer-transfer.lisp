; The terminal cell and the observation latch use the same peer record.
(in-package "ACL2")
(include-book "vocab")

(defthm fn2-accept-latch-copies-slot
  (implies (fn2-op-slotp slot fn2-ops)
           (equal (fn2-ops-observed-peer (fn2-ops-latch-peer 0 slot fn2-ops))
                  (fn2-op-peer slot fn2-ops)))
  :hints ((fn2-columns-guard-hint
           '(fn2-ops) '(fn2-op-slotp update-nth)
           (append '(fn2-ops-observed-peer fn2-ops-latch-peer fn2-op-peer)
                   (fn2-columns-getter-runes '(fn2-ops) world)
                   (fn2-columns-table-scalar-runes '(fn2-ops) t world)) world)))

; A submitted Accept has one free terminal cell and space for its FIFO entry.
; The check reads the ring cursor even on a structurally valid operations table.
(defun fn2-accept-postable-p (slot gen fn2-ops)
  (declare (xargs :stobjs fn2-ops :guard (fn2-ops-wfp fn2-ops)))
  (and (fn2-op-slotp slot fn2-ops)
       (equal (fn2-ops-kind slot fn2-ops) *fn2-action-accept*)
       (fn2-post-eligiblep 0 slot gen fn2-ops)
       (< (fn2-ops-post-tail fn2-ops) (fn2-ops-posted-fifo-length fn2-ops))
       (< (fn2-ops-post-count fn2-ops) (fn2-ops-posted-fifo-length fn2-ops))
       (< (fn2-ops-post-count fn2-ops) *fn2-u60-max*)
       (< (fn2-ops-posted-fifo-length fn2-ops) (expt 2 60))))

(local
 (defun fn2-accept-column-writes (cols)
   (declare (xargs :verify-guards nil))
   (if (atom cols) nil
     (let ((name (fn2-columns-col-name 'fn2-ops (caar cols))))
       (list* (fn2-columns-col-name 'fn2-ops (fn2-columns-pre "SET-" (caar cols)))
              (fn2-columns-pre "UPDATE-" (fn2-columns-sym name "$AI"))
              (fn2-accept-column-writes (cdr cols)))))))

(local
 (defun fn2-accept-transfer-hint (opens opaque world)
   (declare (xargs :verify-guards nil))
   (fn2-columns-guard-hint
    '(fn2-ops) (append '(update-nth fn2-opsp fn2-ops-wfp fn2-ring-next) opaque)
    (append opens (fn2-columns-getter-runes '(fn2-ops) world)
            (fn2-columns-table-scalar-runes '(fn2-ops) t world)
            '(update-fn2-ops-posted-fifoi)
            (fn2-accept-column-writes
             (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-ops) world))))
    world)))

(defthm fn2-accept-post-stores-record
  (implies (and (fn2-accept-postable-p slot gen fn2-ops)
                (fn2-peer-recordp *fn2-outcome-done* family port w0 w1 w2 w3))
           (let ((posted (fn2-post-accept-result slot gen *fn2-outcome-done*
                          *fn2-reason-none* 5 9 family port w0 w1 w2 w3 fn2-ops)))
             (and (equal (fn2-op-peer slot posted) (list family port w0 w1 w2 w3))
                  (equal (fn2-ops-c0-aux0 slot posted) 5)
                  (equal (fn2-ops-c0-aux1 slot posted) 9)
                  (equal (fn2-ops-stray posted) (fn2-ops-stray fn2-ops))
                  (equal (fn2-ops-post-count posted) (+ 1 (fn2-ops-post-count fn2-ops))))))
  :hints ((fn2-accept-transfer-hint
           '(fn2-accept-postable-p fn2-post-accept-result fn2-post-result
             fn2-post-eligiblep fn2-op-handle-code fn2-op-slotp fn2-op-peer
             fn2-post-payloadp fn2-terminal-event)
           '(fn2-peer-recordp) world)))

(local (include-book "arithmetic-5/top" :dir :system))
(local
 (defthm fn2-accept-terminal-index
   (implies (integerp slot)
            (and (equal (floor (* 2 slot) 2) slot)
                 (equal (mod (* 2 slot) 2) 0)))))

(defthm fn2-accept-post-is-next-in-empty-ring
  (implies (and (fn2-accept-postable-p slot gen fn2-ops)
                (equal (fn2-ops-post-count fn2-ops) 0)
                (natp (fn2-ops-post-head fn2-ops))
                (equal (fn2-ops-post-head fn2-ops) (fn2-ops-post-tail fn2-ops))
                (fn2-peer-recordp *fn2-outcome-done* family port w0 w1 w2 w3))
           (equal (fn2-ops-peek-posted
                   (fn2-post-accept-result slot gen *fn2-outcome-done* *fn2-reason-none*
                                           5 9 family port w0 w1 w2 w3 fn2-ops))
                  (list t slot 0)))
  :hints ((fn2-accept-transfer-hint
           '(fn2-accept-postable-p fn2-post-accept-result fn2-post-result
             fn2-post-eligiblep fn2-op-handle-code fn2-op-slotp
             fn2-post-payloadp fn2-terminal-event fn2-ops-peek-posted fn2-completion-phasep)
           '(fn2-peer-recordp floor mod) world)))

(defthm fn2-accept-harvest-delivers-record
  (implies (and (equal (fn2-ops-peek-posted fn2-ops) (list t slot 0))
                (fn2-op-slotp slot fn2-ops))
           (let ((after (mv-nth 4 (fn2-harvest-next fn2-ops))))
             (and (equal (fn2-ops-observed-peer after) (fn2-op-peer slot fn2-ops))
                  (equal (fn2-ops-c0-aux0 slot after) (fn2-ops-c0-aux0 slot fn2-ops))
                  (equal (fn2-ops-c0-aux1 slot after) (fn2-ops-c0-aux1 slot fn2-ops)))))
  :rule-classes nil
  :hints ((fn2-accept-transfer-hint
           '(fn2-harvest-next fn2-op-slotp fn2-ops-latch-peer fn2-ops-observed-peer fn2-op-peer)
           '(fn2-ops-peek-posted fn2-op-harvest-phase) world)))

(defthm fn2-accept-post-remains-in-table
  (implies (fn2-accept-postable-p slot gen fn2-ops)
           (fn2-op-slotp slot
            (fn2-post-accept-result slot gen *fn2-outcome-done* *fn2-reason-none*
                                    5 9 family port w0 w1 w2 w3 fn2-ops)))
  :hints (("Goal" :in-theory (e/d (fn2-accept-postable-p fn2-op-slotp fn2-ops-rows)
                                  (fn2-post-accept-result)))))

(defthm fn2-accept-post-and-harvest
  (implies (and (fn2-accept-postable-p slot gen fn2-ops)
                (equal (fn2-ops-post-count fn2-ops) 0)
                (natp (fn2-ops-post-head fn2-ops))
                (equal (fn2-ops-post-head fn2-ops) (fn2-ops-post-tail fn2-ops))
                (fn2-peer-recordp *fn2-outcome-done* family port w0 w1 w2 w3))
           (let* ((posted (fn2-post-accept-result slot gen *fn2-outcome-done* *fn2-reason-none*
                                                  5 9 family port w0 w1 w2 w3 fn2-ops))
                  (after (mv-nth 4 (fn2-harvest-next posted))))
             (and (equal (fn2-ops-stray posted) (fn2-ops-stray fn2-ops))
                  (equal (fn2-ops-c0-aux0 slot after) 5)
                  (equal (fn2-ops-c0-aux1 slot after) 9)
                  (equal (fn2-ops-observed-peer after) (list family port w0 w1 w2 w3)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn2-accept-harvest-delivers-record
                  (fn2-ops (fn2-post-accept-result slot gen *fn2-outcome-done* *fn2-reason-none*
                                                   5 9 family port w0 w1 w2 w3 fn2-ops))))
           :in-theory '(fn2-accept-post-remains-in-table fn2-accept-post-stores-record
                        fn2-accept-post-is-next-in-empty-ring))))
