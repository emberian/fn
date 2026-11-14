; Initializer geometry and free-chain evidence for the existing pool loops.
(in-package "ACL2")
(include-book "pool")
(local
 (defun fn2-pool-init-column-runes (cols)
   (declare (xargs :verify-guards nil))
   (if (atom cols) nil
     (let* ((read (fn2-columns-col-name 'fn2-pool (caar cols)))
            (write (fn2-columns-col-name 'fn2-pool (fn2-columns-pre "SET-" (caar cols))))
            (raw (fn2-columns-sym read "$AI")))
       (list* read write raw (fn2-columns-pre "UPDATE-" raw)
              (fn2-pool-init-column-runes (cdr cols)))))))
(make-event
 (let ((cols (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-pool) (w state)))))
  (value
   `(defthm fn2-pool-initial-row-write-snapshot
      (implies (and (natp r) (natp slot))
       (and (equal (fn2-pool-rows (let ((fn2-pool p)) (fn2-pool-put slot (gen gen) (base base) (cap cap) (state *fn2-pool-state-free*)
             (owner-kind 0) (owner-slot 0) (owner-gen 0)
             (lease-op-slot 0) (lease-op-gen 0) (lease-off 0) (lease-len 0)
             (out-count 0) (fill 0) (hand-to-kind 0) (hand-to-slot 0) (hand-to-gen 0)
             (next-free next) (class class)))) (fn2-pool-rows p))
            (equal (fn2-pool-row-snapshot r (let ((fn2-pool p)) (fn2-pool-put slot (gen gen) (base base) (cap cap) (state *fn2-pool-state-free*)
             (owner-kind 0) (owner-slot 0) (owner-gen 0)
             (lease-op-slot 0) (lease-op-gen 0) (lease-off 0) (lease-len 0)
             (out-count 0) (fill 0) (hand-to-kind 0) (hand-to-slot 0) (hand-to-gen 0)
             (next-free next) (class class))))
                   (if (equal r slot)
                       (list gen base cap *fn2-pool-state-free* 0 0 0 0 0 0 0 0 0 0 0 0 next class)
                     (fn2-pool-row-snapshot r p)))))
      :hints (("Goal" :cases ((equal r slot))
               :in-theory (e/d (fn2-pool-row-snapshot fn2-pool-rows
                                ,@(fn2-pool-init-column-runes cols) nth-update-nth)
                               (nth update-nth))))))))

(make-event
 (let ((cols (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-pool) (w state)))))
   (value
    `(defthm fn2-pool-carve-slots-snapshot
       (implies (and (natp left) (natp slot) (natp r) (natp base) (posp cap)
                     (<= (+ slot left) (fn2-pool-rows p))
                     (<= (+ base (* left cap)) 1152921504606846976))
                (equal (fn2-pool-row-snapshot r (fn2-pool-carve-slots left slot base cap class gen p))
                       (if (and (<= slot r) (< r (+ slot left)))
                           (list gen (+ base (* (- r slot) cap)) cap *fn2-pool-state-free*
                                 0 0 0 0 0 0 0 0 0 0 0 0
                                 (if (< (+ 1 r) (+ slot left)) (+ 1 r) *fn2-none*) class)
                         (fn2-pool-row-snapshot r p))))
       :hints (("Goal" :induct (fn2-pool-carve-slots left slot base cap class gen p)
                :nonlinearp t
                :in-theory (e/d (fn2-pool-carve-slots fn2-pool-initial-row-write-snapshot)
                                (fn2-pool-row-snapshot fn2-pool-rows
                                 ,@(fn2-pool-init-column-runes cols) nth update-nth))))))))
