; Real pre-reserved journal identities. No free-row or caller-chosen handle
; can become a ticket; the construction reservation adapter creates the ledger.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-construction")
(include-book "commit-format")
(fn2-book-layer :b)
(defun fn2-checkpoint-construction-ownerp (extent fn2-checkpoint-construction fn2-extents)
 (declare (xargs :stobjs (fn2-checkpoint-construction fn2-extents)
  :guard (and (fn2-checkpoint-construction-wfp fn2-checkpoint-construction)
              (fn2-extents-wfp fn2-extents))))
 (and (fn2-alloc-slotp extent fn2-extents)
      (< extent (fn2-checkpoint-construction-rows fn2-checkpoint-construction))
      (= (fn2-checkpoint-construction-live extent fn2-checkpoint-construction) 1)
      (posp (fn2-alloc-freeze-token fn2-extents))
      (equal (fn2-checkpoint-construction-token extent fn2-checkpoint-construction)
             (fn2-alloc-freeze-token fn2-extents))
      (equal (fn2-checkpoint-construction-owner-kind extent fn2-checkpoint-construction)
             (fn2-alloc-freeze-owner-kind fn2-extents))
      (equal (fn2-checkpoint-construction-owner-slot extent fn2-checkpoint-construction)
             (fn2-alloc-freeze-owner-slot fn2-extents))
      (equal (fn2-checkpoint-construction-owner-gen extent fn2-checkpoint-construction)
             (fn2-alloc-freeze-owner-gen fn2-extents))))

; One physical row per call, preserving the planned ticket ordinal even when
; free-list order differs from physical row order. :more is bounded progress;
; exhaustion under a closed construction plan is an explicit shape failure.
(defun fn2-checkpoint-ticket-take (batch fn2-checkpoint-construction fn2-extents)
 (declare (xargs :stobjs (fn2-checkpoint-construction fn2-extents)
  :guard (and (fn2-checkpoint-construction-wfp fn2-checkpoint-construction)
              (fn2-extents-wfp fn2-extents))))
 (b* (((unless (and (posp batch) (unsigned-byte-p 60 batch)))
       (mv :shape 0 0 0 fn2-checkpoint-construction))
      ((unless (equal (fn2-alloc-freeze-phase fn2-extents) 2))
       (mv :exhausted 0 0 0 fn2-checkpoint-construction))
      (e (fn2-construction-ticket-scan fn2-checkpoint-construction))
      (ordinal (fn2-construction-next-ticket fn2-checkpoint-construction))
      ((unless (and (fn2-alloc-slotp e fn2-extents)
                     (equal (fn2-checkpoint-construction-rows fn2-checkpoint-construction)
                            (fn2-extents-rows fn2-extents))
                     (unsigned-byte-p 32 (+ 1 e)) (unsigned-byte-p 60 (+ 1 ordinal))))
       (mv :shape 0 0 0 fn2-checkpoint-construction))
      ((unless (and (fn2-checkpoint-construction-ownerp e fn2-checkpoint-construction fn2-extents)
                     (= (fn2-checkpoint-construction-role e fn2-checkpoint-construction) 6)
                     (= (fn2-checkpoint-construction-ordinal e fn2-checkpoint-construction) ordinal)))
       (let ((fn2-checkpoint-construction
              (update-fn2-construction-ticket-scan (+ 1 e) fn2-checkpoint-construction)))
        (mv :more 0 0 0 fn2-checkpoint-construction)))
      (epoch (fn2-checkpoint-construction-epoch e fn2-checkpoint-construction))
      (counter (fn2-checkpoint-construction-counter e fn2-checkpoint-construction))
      ((unless (and (= (fn2-checkpoint-construction-ticket-claimed e fn2-checkpoint-construction) 0)
                     (= (fn2-checkpoint-construction-intended-bytes e fn2-checkpoint-construction)
                        (* *fn2-commit-write-resources* *fn2-commit-unit-bytes*))
                     (eq (fn2-alloc-handle-code e epoch counter fn2-extents) :ok)
                     (= (fn2-extents-state e fn2-extents) *fn2-extent-state-reserved*)))
       (mv :shape 0 0 0 fn2-checkpoint-construction))
      (fn2-checkpoint-construction (fn2-checkpoint-construction-put e (ticket-claimed 1) (ticket-batch batch)))
      (fn2-checkpoint-construction (update-fn2-construction-next-ticket (+ 1 ordinal) fn2-checkpoint-construction))
      (fn2-checkpoint-construction (update-fn2-construction-ticket-scan 0 fn2-checkpoint-construction)))
  (mv :ok e epoch counter fn2-checkpoint-construction)))
(fn2-checkpoint-construction-preserves fn2-checkpoint-ticket-take
 (batch fn2-checkpoint-construction fn2-extents) :position 4)

; The ticket wrapper temporarily changes only the freeze scalar.  Keep the
; allocator's unconditional row frame available even after ROWS has unfolded
; to its raw NTH accessor; TYPE/WFP hypotheses do not justify this frame.
(local
 (defthm fn2-checkpoint-ticket-account-raw-rows
  (equal (nth *fn2-extents-rows*
              (fn2-alloc-account i old-state old-reason fn2-extents))
         (nth *fn2-extents-rows* fn2-extents))
  :hints (("Goal" :in-theory (enable fn2-alloc-account)))))
(local
 (defthm fn2-checkpoint-ticket-commit-allocation-raw-rows
  (equal (nth *fn2-extents-rows*
              (mv-nth 1 (fn2-alloc-commit-allocation
                         i epoch counter owner-kind owner-id fn2-extents)))
         (nth *fn2-extents-rows* fn2-extents))
  :hints (("Goal" :in-theory (enable fn2-alloc-commit-allocation)))))

; Existing journal installation commits its own exact ticket allocation. This
; call is atomic: the normal allocator primitive is reused with its generic
; gate locally open, and the retained gate is restored on every result. There
; are no callbacks or issue/yield boundaries inside the operation.
(defun fn2-checkpoint-ticket-install (e epoch counter batch owner-kind fn2-checkpoint-construction fn2-extents)
 (declare (xargs :stobjs (fn2-checkpoint-construction fn2-extents)
  :guard (and (fn2-checkpoint-construction-wfp fn2-checkpoint-construction)
              (fn2-extents-wfp fn2-extents) (unsigned-byte-p 8 owner-kind)
              (unsigned-byte-p 60 batch))))
 (if (not (and (unsigned-byte-p 8 owner-kind) (unsigned-byte-p 60 batch)
               (equal (fn2-alloc-freeze-phase fn2-extents) 2)
               (fn2-checkpoint-construction-ownerp e fn2-checkpoint-construction fn2-extents)
               (= (fn2-checkpoint-construction-role e fn2-checkpoint-construction) 6)
               (= (fn2-checkpoint-construction-ticket-claimed e fn2-checkpoint-construction) 1)
               (equal batch (fn2-checkpoint-construction-ticket-batch e fn2-checkpoint-construction))
               (equal epoch (fn2-checkpoint-construction-epoch e fn2-checkpoint-construction))
               (equal counter (fn2-checkpoint-construction-counter e fn2-checkpoint-construction))))
     (mv :frozen fn2-extents)
  (let ((fn2-extents (update-fn2-alloc-freeze-phase 0 fn2-extents)))
   (mv-let (code fn2-extents)
    (fn2-alloc-commit-allocation e epoch counter owner-kind batch fn2-extents)
    (let ((fn2-extents (update-fn2-alloc-freeze-phase 2 fn2-extents)))
     (mv code fn2-extents))))))
(fn2-extents-preserves fn2-checkpoint-ticket-install
 (e epoch counter batch owner-kind fn2-checkpoint-construction fn2-extents) :position 1)
