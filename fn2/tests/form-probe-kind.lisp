; MACHINE-FORM 6.5 P2/P3 probe (Astra 6.8, last point): an arm-shaped
; function over the children it touches (the kind's own table, the pool, the
; ops), defined and proved without fn2-core existing. This book includes no
; assembly book.
(in-package "ACL2")
(include-book "../books/machines-a")
(include-book "../books/pool")
(include-book "../books/vocab")

; The echo :reply reset shape: reset the row's window in the pool, then
; write the row's off/length in its own table (one batched write).
(defun fn2-probe-echo-reset (slot pslot pgen okind oslot ogen fn2-echo fn2-pool)
  (declare (xargs :stobjs (fn2-echo fn2-pool)
                  :guard (and (fn2-echo-wfp fn2-echo) (fn2-pool-wfp fn2-pool) (natp slot)
                              (< slot (fn2-echo-rows fn2-echo)))))
  (mv-let (code fn2-pool) (fn2-pool-reset pslot pgen okind oslot ogen fn2-pool)
    (let* ((fn2-echo (fn2-echo-set-off slot 0 fn2-echo))
           (fn2-echo (fn2-echo-set-length slot 0 fn2-echo)))
      (mv code fn2-echo fn2-pool))))
(defthm fn2-probe-echo-reset-shape
  (implies (and (fn2-echop fn2-echo) (fn2-echo-wfp fn2-echo) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                (natp slot) (< slot (fn2-echo-rows fn2-echo)))
           (let ((r (fn2-probe-echo-reset slot pslot pgen okind oslot ogen fn2-echo fn2-pool)))
             (and (fn2-echop (mv-nth 1 r)) (fn2-echo-wfp (mv-nth 1 r))
                  (equal (fn2-echo-rows (mv-nth 1 r)) (fn2-echo-rows fn2-echo))
                  (fn2-poolp (mv-nth 2 r)) (fn2-pool-wfp (mv-nth 2 r))))))

; A child-level issue's first half: an op reservation (ops) beside a pool
; reset (pool), three stobjs returned.
(defun fn2-probe-issue-half (slot pslot pgen kind okind oslot ogen principal fn2-echo fn2-pool fn2-ops)
  (declare (xargs :stobjs (fn2-echo fn2-pool fn2-ops)
                  :guard (and (fn2-echo-wfp fn2-echo) (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops)
                              (natp slot) (< slot (fn2-echo-rows fn2-echo)))))
  (mv-let (code opslot opgen fn2-ops) (fn2-op-reserve kind okind oslot ogen principal 0 fn2-ops)
    (declare (ignore opslot opgen))
    (if (not (eq code :ok)) (mv code fn2-echo fn2-pool fn2-ops)
      (mv-let (code fn2-echo fn2-pool) (fn2-probe-echo-reset slot pslot pgen okind oslot ogen fn2-echo fn2-pool)
        (let ((fn2-echo (fn2-echo-set-pending slot 1 fn2-echo)))
          (mv code fn2-echo fn2-pool fn2-ops))))))
(defthm fn2-probe-issue-half-shape
  (implies (and (fn2-echop fn2-echo) (fn2-echo-wfp fn2-echo) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops) (natp slot) (< slot (fn2-echo-rows fn2-echo)))
           (let ((r (fn2-probe-issue-half slot pslot pgen kind okind oslot ogen principal fn2-echo fn2-pool fn2-ops)))
             (and (fn2-echop (mv-nth 1 r)) (fn2-echo-wfp (mv-nth 1 r))
                  (fn2-poolp (mv-nth 2 r)) (fn2-pool-wfp (mv-nth 2 r))
                  (fn2-opsp (mv-nth 3 r)) (fn2-ops-wfp (mv-nth 3 r))))))
