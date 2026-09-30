; Concrete once-only scheduling turns, separate from connection lifetimes.
; INTERNAL joins only: no runtime installer or public supplied-body boundary.
; All calls run under the same extent/pool exclusion. A raw escape fences;
; it does not call finish in an unconditional unwind-protect.
(in-package "ACL2")
(include-book "allocation-epoch-collection-request")

; Five fields, frozen independently of the ten-field shared pool. Only the
; installation constructor resizes; served operations directly index SLOT.
; Phase tags are immediate: idle=0 entry-intent=1 gate-owned=2 body-owned=3
; finishing=4 leave-intent=5 faulted=6. Last nonce survives return to idle.
(defstobj fn-allocation-turn-slots
 (fn-ats-association :initially nil)
 (fn-ats-count :type (integer 0 *) :initially 0)
 (fn-ats-kinds :type (array t (1)) :initially nil :resizable t)
 (fn-ats-nonces :type (array (integer 0 *) (1)) :initially 0 :resizable t)
 (fn-ats-phases :type (array (integer 0 6) (1)) :initially 0 :resizable t)
 :inline t)

(defun fn-ats-slotp (slot fn-allocation-turn-slots)
 (declare (xargs :stobjs fn-allocation-turn-slots :guard t))
 (and (natp slot) (< slot (fn-ats-count fn-allocation-turn-slots))
      (< slot (fn-ats-kinds-length fn-allocation-turn-slots))
      (< slot (fn-ats-nonces-length fn-allocation-turn-slots))
      (< slot (fn-ats-phases-length fn-allocation-turn-slots))))

(defun fn-ats-associatedp (fn-allocation-turn-slots fn-page-read-pool)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool) :guard t))
 (and (fn-ats-association fn-allocation-turn-slots)
      (equal (fn-ats-association fn-allocation-turn-slots)
             (fn-aec-at 1 (fn-prp-alloc-installation fn-page-read-pool)))))

(defun fn-ats-owned-phasep (phase)
 (declare (xargs :guard t))
 (or (eql phase 2) (eql phase 3) (eql phase 4)))

(defun fn-ats-matchingp (slot nonce fn-allocation-turn-slots fn-page-read-pool)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool) :guard t))
 (and (fn-ats-slotp slot fn-allocation-turn-slots)
      (fn-ats-associatedp fn-allocation-turn-slots fn-page-read-pool)
      (natp nonce) (equal nonce (fn-ats-noncesi slot fn-allocation-turn-slots))
      (fn-ats-owned-phasep (fn-ats-phasesi slot fn-allocation-turn-slots))))

(local (defthm fn-ats-len-of-resize-list
 (implies (natp n) (equal (len (resize-list xs n init)) n))))

; Representation construction only. The actual installer still owes the
; profile-supported capacity, native references and paid constructor baseline.
; It is deliberately absent from every public/served call map.
(defun fn-ats-install-kinds-internal (kinds slot fn-allocation-turn-slots)
 (declare (xargs :stobjs fn-allocation-turn-slots
  :guard (and (true-listp kinds) (natp slot)
              (<= (+ slot (len kinds)) (fn-ats-kinds-length fn-allocation-turn-slots))
              (<= (+ slot (len kinds)) (fn-ats-nonces-length fn-allocation-turn-slots))
              (<= (+ slot (len kinds)) (fn-ats-phases-length fn-allocation-turn-slots)))
  :measure (len kinds)))
 (if (endp kinds) fn-allocation-turn-slots
   (let* ((fn-allocation-turn-slots
           (update-fn-ats-kindsi slot (car kinds) fn-allocation-turn-slots))
          (fn-allocation-turn-slots (update-fn-ats-noncesi slot 0 fn-allocation-turn-slots))
          (fn-allocation-turn-slots (update-fn-ats-phasesi slot 0 fn-allocation-turn-slots)))
    (fn-ats-install-kinds-internal (cdr kinds) (+ 1 slot) fn-allocation-turn-slots))))

(defun fn-ats-construct-internal (kinds fn-allocation-turn-slots fn-page-read-pool)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool)
  :guard (and (true-listp kinds))))
 (let ((count (len kinds)))
  (if (not (and (not (fn-ats-association fn-allocation-turn-slots))
                (equal (fn-ats-count fn-allocation-turn-slots) 0)
                (posp count) (fn-aec-at 1 (fn-prp-alloc-installation fn-page-read-pool))
                (eq (fn-prp-alloc-mode fn-page-read-pool) :active)
                (equal (fn-prp-alloc-active-turns fn-page-read-pool) 0)
                (natp (fn-aec-at 2 (fn-prp-alloc-installation fn-page-read-pool)))
                (<= count (fn-aec-at 2 (fn-prp-alloc-installation fn-page-read-pool)))))
      (mv :unsupported-slots fn-allocation-turn-slots)
   (let* ((fn-allocation-turn-slots (resize-fn-ats-kinds count fn-allocation-turn-slots))
          (fn-allocation-turn-slots (resize-fn-ats-nonces count fn-allocation-turn-slots))
          ; Clear the phase backing before resize, including an old malformed
          ; fixture prefix. This allocation is installation-only baseline work.
          (fn-allocation-turn-slots (resize-fn-ats-phases 0 fn-allocation-turn-slots))
          (fn-allocation-turn-slots (resize-fn-ats-phases count fn-allocation-turn-slots))
          (fn-allocation-turn-slots (fn-ats-install-kinds-internal kinds 0 fn-allocation-turn-slots))
          (fn-allocation-turn-slots (update-fn-ats-count count fn-allocation-turn-slots))
          (fn-allocation-turn-slots
           (update-fn-ats-association (fn-aec-at 1 (fn-prp-alloc-installation fn-page-read-pool))
                                    fn-allocation-turn-slots)))
    (mv :constructed fn-allocation-turn-slots)))))

(local
 (defthm fn-ats-enter-funded-pool
  (implies (and (fn-aec-pool-statep pool)
                (eq (mv-nth 0 (fn-aec-pool-enter-internal nil pool)) :prepaid))
   (let ((next (mv-nth 1 (fn-aec-pool-enter-internal nil pool))))
    (and (fn-aec-pool-statep next)
         (eq (fn-prp-alloc-mode next) :active)
         (posp (fn-prp-alloc-active-turns next)))))
  :hints (("Goal"
    :in-theory (disable fn-aec-statep fn-aec-installationp fn-aec-ceiling fn-aec-at)
    :use ((:instance fn-aec-pool-entry-preserves-allocation-state (cleanup nil)))))))

(local
 (defthm fn-ats-issued-natp
  (implies (eq (mv-nth 0 (fn-aec-collection-issue ledger domain)) :issued)
           (natp (mv-nth 1 (fn-aec-collection-issue ledger domain))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-prs-issue) (fn-prs-fundedp fn-prs-plus fn-prs-vectorp fn-aec-nats-below fn-aed-add-roomp fn-aed-ordinary-roomp))))))

; Entry intent is retained BEFORE scalar Qgate and active-count mutation.
; Generic PRS checks/ledger reconstruction run only after that prepayment.
; No holder binding row is made, searched or removed. ROLE is internal actual
; endpoint dispatch authority, never a public cleanup-kind selector.
(defun fn-ats-enter-internal (slot role fn-allocation-turn-slots fn-page-read-pool)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool)
                 :guard (fn-aec-pool-statep fn-page-read-pool)
  :guard-hints (("Goal" :in-theory
    (disable fn-aec-pool-statep fn-aec-statep fn-aec-pool-enter-internal
             fn-aec-pool-consumed-turn-internal fn-aec-collection-issue
             fn-owner-page-read-keep-ledger fn-aec-at)
   :use ((:instance fn-ats-enter-funded-pool (pool fn-page-read-pool))
         (:instance fn-ats-issued-natp
          (ledger (fn-owner-page-read-ledger
                    (mv-nth 1 (fn-aec-pool-enter-internal nil fn-page-read-pool))))
          (domain (fn-aec-at 2 (fn-prp-alloc-installation
                    (mv-nth 1 (fn-aec-pool-enter-internal nil fn-page-read-pool)))))))))))
 (cond
  ((not (and (fn-ats-slotp slot fn-allocation-turn-slots)
             (fn-ats-associatedp fn-allocation-turn-slots fn-page-read-pool)
             role (symbolp role) (symbolp (fn-ats-kindsi slot fn-allocation-turn-slots))
             (eq role (fn-ats-kindsi slot fn-allocation-turn-slots))))
   (mv :unsupported-slots 0 fn-allocation-turn-slots fn-page-read-pool))
  ((not (eql (fn-ats-phasesi slot fn-allocation-turn-slots) 0))
   (mv (if (fn-ats-owned-phasep (fn-ats-phasesi slot fn-allocation-turn-slots))
           :busy :recovery-required) 0 fn-allocation-turn-slots fn-page-read-pool))
  (t
   (let ((fn-allocation-turn-slots (update-fn-ats-phasesi slot 1 fn-allocation-turn-slots)))
    (mv-let (gate fn-page-read-pool) (fn-aec-pool-enter-internal nil fn-page-read-pool)
     (if (not (eq gate :prepaid))
         (let ((fn-allocation-turn-slots (update-fn-ats-phasesi slot 0 fn-allocation-turn-slots)))
          (mv gate 0 fn-allocation-turn-slots fn-page-read-pool))
      (mv-let (word issued ledger)
       (fn-aec-collection-issue (fn-owner-page-read-ledger fn-page-read-pool)
         (fn-aec-at 2 (fn-prp-alloc-installation fn-page-read-pool)))
       (if (not (eq word :issued))
           ; Definite refusal consumes this retained temporary turn once.
           ; Qgate stays in A. Neither PRS NEXT nor spent IDs is refunded.
           (mv-let (left fn-page-read-pool)
            (fn-aec-pool-consumed-turn-internal fn-page-read-pool)
            (declare (ignore left))
            (let ((fn-allocation-turn-slots (update-fn-ats-phasesi slot 0 fn-allocation-turn-slots)))
             (mv word 0 fn-allocation-turn-slots fn-page-read-pool)))
         (let* ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool))
                (fn-allocation-turn-slots (update-fn-ats-noncesi slot issued fn-allocation-turn-slots))
                (fn-allocation-turn-slots (update-fn-ats-phasesi slot 2 fn-allocation-turn-slots)))
          (mv :gate-owned issued fn-allocation-turn-slots fn-page-read-pool))))))))))

; INTERNAL source seam; callers must join their ACTUAL evaluator before this
; can be exposed. BODY is not a public request input. No cleanup bypass exists.
; Already body-owned continuation returns :prepaid without paying twice,
; including during draining; its outer epilogue is part of the original BODY.
(defun fn-ats-prepay-body-internal (slot nonce body fn-allocation-turn-slots fn-page-read-pool)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool)
  :guard (and (fn-aec-pool-statep fn-page-read-pool) (natp body))))
 (cond ((not (fn-ats-matchingp slot nonce fn-allocation-turn-slots fn-page-read-pool))
        (mv :stale fn-allocation-turn-slots fn-page-read-pool))
       ((not (member-eq (fn-prp-alloc-mode fn-page-read-pool) '(:active :draining)))
        (mv :recovery-required fn-allocation-turn-slots fn-page-read-pool))
       ((eql (fn-ats-phasesi slot fn-allocation-turn-slots) 3)
        (mv :prepaid fn-allocation-turn-slots fn-page-read-pool))
       ((not (eql (fn-ats-phasesi slot fn-allocation-turn-slots) 2))
        (mv :stale fn-allocation-turn-slots fn-page-read-pool))
       (t
        (mv-let (word fn-page-read-pool) (fn-aec-pool-body-internal body nil fn-page-read-pool)
         (let ((fn-allocation-turn-slots
                (if (eq word :prepaid) (update-fn-ats-phasesi slot 3 fn-allocation-turn-slots)
                  fn-allocation-turn-slots)))
          (mv word fn-allocation-turn-slots fn-page-read-pool))))))

; Actual receipt-consuming authority. Stale/duplicate/old reused-slot nonce
; changes neither slots, allocation nor active count, even with another slot
; active. Retained intent phases cannot decrement. No new identity is needed.
(defun fn-ats-finish-owned (slot nonce fn-allocation-turn-slots fn-page-read-pool)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool)
                 :guard (fn-aec-pool-statep fn-page-read-pool)))
 (cond ((not (fn-ats-matchingp slot nonce fn-allocation-turn-slots fn-page-read-pool))
        (mv :stale fn-allocation-turn-slots fn-page-read-pool))
       ((not (and (member-eq (fn-prp-alloc-mode fn-page-read-pool) '(:active :draining))
                  (posp (fn-prp-alloc-active-turns fn-page-read-pool))))
        (mv :recovery-required fn-allocation-turn-slots fn-page-read-pool))
       (t
        (let ((fn-allocation-turn-slots (update-fn-ats-phasesi slot 5 fn-allocation-turn-slots)))
         (mv-let (word fn-page-read-pool) (fn-aec-pool-consumed-turn-internal fn-page-read-pool)
          (let ((fn-allocation-turn-slots (update-fn-ats-phasesi slot 0 fn-allocation-turn-slots)))
           (mv word fn-allocation-turn-slots fn-page-read-pool)))))))

; Called on a raw escape before any ordinary resumption. Keep the exact intent,
; roots, nonces and A/count; recovery must inspect the failed transition.
(defun fn-ats-uncertain-internal (fn-allocation-turn-slots fn-page-read-pool)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool)
  :guard (and (fn-aec-pool-statep fn-page-read-pool)
              (not (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled)))))
 (let ((fn-page-read-pool (fn-aec-pool-uncertain-internal fn-page-read-pool)))
  (mv :recovery-required fn-allocation-turn-slots fn-page-read-pool)))

; Proof-only cardinality projection: never called on entry/finish/collection.
; Leave-intent/faulted retain the issued turn; entry-intent raw escapes are
; recovery events outside the normally-returned correspondence theorem.
(defun fn-ats-live-phasep (phase)
 (declare (xargs :guard t))
 (or (fn-ats-owned-phasep phase) (eql phase 5) (eql phase 6)))
(defun fn-ats-owned-count (phases)
 (declare (xargs :guard t))
 (if (consp phases)
     (+ (if (fn-ats-live-phasep (car phases)) 1 0)
        (fn-ats-owned-count (cdr phases)))
   0))
(defun-nx fn-ats-correspondencep (slots pool)
 (and (fn-ats-associatedp slots pool)
      (equal (fn-prp-alloc-active-turns pool) (fn-ats-owned-count (nth 4 slots)))))

(local
 (defthm fn-ats-count-update-nth
  (implies (and (natp slot) (< slot (len phases)))
   (equal (fn-ats-owned-count (update-nth slot phase phases))
          (+ (fn-ats-owned-count phases)
             (if (fn-ats-live-phasep phase) 1 0)
             (- (if (fn-ats-live-phasep (nth slot phases)) 1 0)))))
  :hints (("Goal" :induct (update-nth slot phase phases)))))

; PRF-1156: the actual concrete finish subject consumes the exact receipt.
; These are decision teeth, not a scalar helper asserting caller ownership.
(defthm fn-ats-finish-matching-consumes-once
 (implies
  (and (fn-ats-matchingp slot nonce slots pool)
       (member-eq (fn-prp-alloc-mode pool) '(:active :draining))
       (posp (fn-prp-alloc-active-turns pool)))
  (mv-let (word next-slots next-pool) (fn-ats-finish-owned slot nonce slots pool)
   (and (eq word :left)
        (equal (fn-prp-alloc-active-turns next-pool)
               (- (fn-prp-alloc-active-turns pool) 1))
        (equal (fn-prp-alloc-allocated next-pool) (fn-prp-alloc-allocated pool))
        (equal (fn-ats-phasesi slot next-slots) 0)
        (equal (fn-ats-noncesi slot next-slots) nonce)
        (not (fn-ats-matchingp slot nonce next-slots next-pool)))))
 :hints (("Goal" :in-theory (disable fn-aec-statep fn-aec-installationp fn-aec-at
                                   fn-aec-ceiling fn-ats-owned-count)))
 :rule-classes nil)

(defthm fn-ats-finish-stale-keeps-other-turns-by-definition
 (implies (not (fn-ats-matchingp slot nonce slots pool))
  (equal (fn-ats-finish-owned slot nonce slots pool) (mv :stale slots pool)))
 :rule-classes nil)

(defthm fn-ats-finish-preserves-slot-count-correspondence
 (implies (fn-ats-correspondencep slots pool)
  (mv-let (word next-slots next-pool) (fn-ats-finish-owned slot nonce slots pool)
   (declare (ignore word))
   (fn-ats-correspondencep next-slots next-pool)))
 :hints (("Goal" :in-theory (disable fn-ats-owned-count fn-aec-statep
                                   fn-aec-installationp fn-aec-at fn-aec-ceiling)))
 :rule-classes nil)

(defthm fn-ats-entry-preserves-slot-count-correspondence
 (implies (fn-ats-correspondencep slots pool)
  (mv-let (word nonce next-slots next-pool) (fn-ats-enter-internal slot role slots pool)
   (declare (ignore word nonce))
   (fn-ats-correspondencep next-slots next-pool)))
 :hints (("Goal" :in-theory
   (disable fn-ats-owned-count fn-aec-statep fn-aec-installationp fn-aec-at
            fn-aec-ceiling fn-aec-collection-issue)))
 :rule-classes nil)

(defthm fn-ats-body-preserves-slot-count-correspondence
 (implies (fn-ats-correspondencep slots pool)
  (mv-let (word next-slots next-pool) (fn-ats-prepay-body-internal slot nonce body slots pool)
   (declare (ignore word))
   (fn-ats-correspondencep next-slots next-pool)))
 :hints (("Goal" :in-theory
   (disable fn-ats-owned-count fn-aec-statep fn-aec-installationp fn-aec-at
            fn-aec-ceiling fn-aec-body)))
 :rule-classes nil)

(defthm fn-ats-body-prepaid-continuation-retains-accounting-by-definition
 (implies
  (and (fn-ats-matchingp slot nonce slots pool)
       (member-eq (fn-prp-alloc-mode pool) '(:active :draining))
       (equal (fn-ats-phasesi slot slots) 3))
  (equal (fn-ats-prepay-body-internal slot nonce body slots pool) (mv :prepaid slots pool)))
 :rule-classes nil)

(defthm fn-ats-raw-uncertainty-retains-receipts
 (mv-let (word next-slots next-pool) (fn-ats-uncertain-internal slots pool)
  (and (eq word :recovery-required) (equal next-slots slots)
       (equal (fn-prp-alloc-mode next-pool) :recovery)
       (equal (fn-prp-alloc-active-turns next-pool) (fn-prp-alloc-active-turns pool))
       (equal (fn-prp-alloc-allocated next-pool) (fn-prp-alloc-allocated pool))
       (equal (fn-owner-page-read-ledger next-pool) (fn-owner-page-read-ledger pool))))
 :rule-classes nil)

; The successful entry's two scalar receipt coordinates come from the actual
; shared PRS namespace. No connection holder row grants finish authority.
(defthm fn-ats-enter-owns-actual-shared-nonce
 (implies (eq (mv-nth 0 (fn-ats-enter-internal slot role slots pool)) :gate-owned)
  (mv-let (word nonce next-slots next-pool) (fn-ats-enter-internal slot role slots pool)
   (declare (ignore word))
   (and (natp nonce)
        (equal nonce (fn-prl-nth 2 (fn-owner-page-read-ledger pool)))
        (equal (fn-prl-nth 2 (fn-owner-page-read-ledger next-pool)) (+ 1 nonce))
        (equal (fn-prl-nth 3 (fn-owner-page-read-ledger next-pool))
               (fn-prl-nth 3 (fn-owner-page-read-ledger pool)))
        (equal (fn-prp-alloc-active-turns next-pool)
               (+ 1 (fn-prp-alloc-active-turns pool)))
        (equal (fn-prp-alloc-allocated next-pool)
               (+ (fn-prp-alloc-allocated pool)
                  (fn-aec-at 9 (fn-prp-alloc-installation pool))))
        (fn-ats-matchingp slot nonce next-slots next-pool)
        (equal (fn-ats-phasesi slot next-slots) 2))))
 :hints (("Goal" :in-theory
   (e/d (fn-prs-issue fn-prs-plus fn-prl-nth fn-prl-build)
        (fn-aec-statep fn-aec-installationp fn-aec-at fn-aec-ceiling
         fn-prs-fundedp fn-prs-vectorp fn-aec-nats-below fn-aed-add-roomp
         fn-aed-ordinary-roomp fn-ats-owned-count))))
 :rule-classes nil)

(local
 (defthm fn-ats-zero-count-update-zero
  (implies (equal (fn-ats-owned-count phases) 0)
           (equal (fn-ats-owned-count (update-nth slot 0 phases)) 0))
  :hints (("Goal" :induct (update-nth slot 0 phases)))))
(local
 (defthm fn-ats-zero-count-resize
  (equal (fn-ats-owned-count (resize-list nil count 0)) 0)))
(local
 (defthm fn-ats-install-kinds-keeps-zero-count
  (implies (equal (fn-ats-owned-count (nth 4 slots)) 0)
   (equal (fn-ats-owned-count (nth 4 (fn-ats-install-kinds-internal kinds slot slots))) 0))
  :hints (("Goal" :induct (fn-ats-install-kinds-internal kinds slot slots)
           :in-theory (disable fn-ats-owned-count)))))
(local (defthm fn-ats-resize-zero (equal (resize-list xs 0 value) nil)))
(defthm fn-ats-construction-establishes-slot-count-correspondence
 (implies
  (eq (mv-nth 0 (fn-ats-construct-internal kinds slots pool)) :constructed)
  (fn-ats-correspondencep (mv-nth 1 (fn-ats-construct-internal kinds slots pool)) pool))
 :hints (("Goal" :in-theory (disable fn-ats-owned-count fn-aec-installationp fn-aec-ceiling
                                   fn-aec-at fn-ats-install-kinds-internal nth update-nth resize-list)))
 :rule-classes nil)
