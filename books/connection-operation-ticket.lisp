; Narrow actual STATE ticket completion callbacks. Installation and the
; outer native closure are separate producers; no owner or MIO bootstrap.
(in-package "ACL2")
(include-book "allocation-turn-raw-bridge")
(include-book "snapshot-source-token")
(include-book "state-globals")
(include-book "definterface")

(local
 (defthm fn-cop-fixed-ticket-true-list
  (implies (fn-omk-widthp x n) (true-listp x))
  :hints (("Goal" :in-theory (enable fn-omk-widthp)))))

(local
 (defthm fn-cop-update-nth-idempotent
  (equal (update-nth n value (update-nth n value xs)) (update-nth n value xs))
  :hints (("Goal" :induct (update-nth n value xs) :in-theory (enable update-nth)))))

(defun fn-owner-connection-operation-ticket (state)
 (declare (xargs :stobjs state :guard t))
 (if (f-boundp-global 'fn-owner-connection-operation-ticket state)
     (f-get-global 'fn-owner-connection-operation-ticket state) nil))

(defun fn-owner-connection-operation-installation (state)
 (declare (xargs :stobjs state :guard t))
 (if (f-boundp-global 'fn-owner-connection-operation-installation state)
     (f-get-global 'fn-owner-connection-operation-installation state) nil))

; Definite no-body refusal owns a gate receipt. Consume it here so native does
; not infer receipt liveness from a returned nonce. Ambiguous outcomes retain it.
(defun fn-owner-index-connection-refuse-internal
 (slot nonce reason fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
  :guard (fn-aec-pool-statep fn-page-read-pool) :verify-guards nil))
 (mv-let (finished fn-allocation-turn-slots fn-page-read-pool)
  (fn-ats-finish-owned slot nonce fn-allocation-turn-slots fn-page-read-pool)
  (if (eq finished :left)
      (mv nil reason nil fn-allocation-turn-slots fn-page-read-pool state)
    (mv nil :recovery-required nonce fn-allocation-turn-slots fn-page-read-pool state))))

; Only the actual outer closure calls this, AFTER custody/open/definite abort
; and the entire prepaid epilogue. Logical holder release is unrelated.
(defun fn-owner-index-connection-finish
 (slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
  :guard (fn-aec-pool-statep fn-page-read-pool) :verify-guards nil))
 (let ((ticket (fn-owner-connection-operation-ticket state)))
  (if (not (and ticket (fn-omk-widthp ticket 16)
                     (eq (fn-omk-at 0 ticket) :connection-operation-ticket)
                     (equal slot (fn-omk-at 7 ticket))
                     (equal nonce (fn-omk-at 8 ticket))
                     (member-eq (fn-omk-at 1 ticket) '(:prepaid :started :refused))))
      (mv nil :recovery-required fn-allocation-turn-slots fn-page-read-pool state)
   (let ((state (if ticket
                   (f-put-global 'fn-owner-connection-operation-ticket
                                  (update-nth 1 :finish-intent ticket) state) state)))
    (mv-let (word fn-allocation-turn-slots fn-page-read-pool)
     (fn-ats-finish-owned slot nonce fn-allocation-turn-slots fn-page-read-pool)
     ; Keep completed roots across a raw escape between core return and native
     ; receipt. A later gate may retire them; fault never clears them.
     (let ((state (if (and ticket (eq word :left))
                     (f-put-global 'fn-owner-connection-operation-ticket
                                    (update-nth 1 :finished ticket) state) state)))
      (mv nil word fn-allocation-turn-slots fn-page-read-pool state)))))))

(defun fn-owner-index-connection-fault
 (fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
  :guard (and (fn-aec-pool-statep fn-page-read-pool)
              (not (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled)))
  :verify-guards nil))
 (mv-let (word fn-allocation-turn-slots fn-page-read-pool)
  (fn-ats-uncertain-internal fn-allocation-turn-slots fn-page-read-pool)
  (mv nil word fn-allocation-turn-slots fn-page-read-pool state)))

(verify-guards fn-owner-index-connection-refuse-internal)
(verify-guards fn-owner-index-connection-finish
 :hints (("Goal" :in-theory
          (disable fn-ats-finish-owned fn-aec-pool-statep
                   fn-owner-connection-operation-ticket fn-omk-widthp))))
(verify-guards fn-owner-index-connection-fault)

(defthm fn-owner-index-connection-fault-is-idempotent
 (let ((once (fn-owner-index-connection-fault slots pool state)))
  (equal (fn-owner-index-connection-fault
           (mv-nth 2 once) (mv-nth 3 once) (mv-nth 4 once)) once))
 :hints (("Goal" :in-theory
          (e/d (fn-owner-index-connection-fault fn-ats-uncertain-internal
                fn-aec-pool-uncertain-internal) (fn-aec-pool-statep))))
 :rule-classes nil)

(defthm fn-owner-index-connection-finish-preserves-carried-pool
 (implies (fn-aec-pool-statep pool)
  (fn-aec-pool-statep
    (mv-nth 3 (fn-owner-index-connection-finish slot nonce slots pool state))))
 :hints (("Goal" :in-theory
          (disable fn-ats-finish-owned fn-aec-pool-statep
                   fn-owner-connection-operation-ticket fn-omk-at fn-omk-widthp)
          :use ((:instance fn-atsh-finish-preserves-carried-pool-state
                   (fn-allocation-turn-slots slots) (fn-page-read-pool pool)))))
 :rule-classes nil)

(defthm fn-owner-index-connection-fault-preserves-carried-pool
 (implies (and (fn-aec-pool-statep pool)
               (not (eq (fn-prp-alloc-mode pool) :uninstalled)))
  (let ((next (mv-nth 3 (fn-owner-index-connection-fault slots pool state))))
   (and (fn-aec-pool-statep next)
        (not (eq (fn-prp-alloc-mode next) :uninstalled)))))
 :hints (("Goal" :in-theory (disable fn-aec-installationp fn-aec-at fn-aec-ceiling)
          :use ((:instance fn-atsh-uncertain-preserves-carried-pool-state
                  (fn-allocation-turn-slots slots) (fn-page-read-pool pool)))))
 :rule-classes nil)

(defthm fn-owner-index-connection-fault-retains-roots
 (let ((next (fn-owner-index-connection-fault slots pool state)))
  (and (equal (mv-nth 2 next) slots) (equal (mv-nth 4 next) state)
       (equal (fn-prp-alloc-installation (mv-nth 3 next)) (fn-prp-alloc-installation pool))
       (equal (fn-prp-alloc-epoch (mv-nth 3 next)) (fn-prp-alloc-epoch pool))
       (equal (fn-prp-alloc-allocated (mv-nth 3 next)) (fn-prp-alloc-allocated pool))
       (equal (fn-prp-alloc-active-turns (mv-nth 3 next)) (fn-prp-alloc-active-turns pool))))
 :rule-classes nil)

(defthm fn-owner-index-connection-finish-retains-installed-roots
 (let ((next (fn-owner-index-connection-finish slot nonce slots pool state)))
  (and (equal (fn-ats-association (mv-nth 2 next)) (fn-ats-association slots))
       (equal (fn-prp-alloc-installation (mv-nth 3 next)) (fn-prp-alloc-installation pool))
       (equal (fn-prp-alloc-epoch (mv-nth 3 next)) (fn-prp-alloc-epoch pool))
       (equal (fn-prp-alloc-allocated (mv-nth 3 next)) (fn-prp-alloc-allocated pool))))
 :hints (("Goal" :in-theory
          (disable nth update-nth fn-aec-pool-statep
                   fn-owner-connection-operation-ticket fn-omk-at fn-omk-widthp)))
 :rule-classes nil)

(defthm fn-owner-index-connection-finish-raw-with
 (implies (fn-aec-pool-statep fn-page-read-pool)
  (fn-aec-pool-statep
   (mv-nth 3 (fn-owner-index-connection-finish slot nonce fn-allocation-turn-slots fn-page-read-pool state))))
 :hints (("Goal" :in-theory (disable fn-owner-index-connection-finish fn-aec-pool-statep)
  :use ((:instance fn-owner-index-connection-finish-preserves-carried-pool
          (slots fn-allocation-turn-slots) (pool fn-page-read-pool)))))
 :rule-classes nil)

(defthm fn-owner-index-connection-fault-raw-with
 (implies (and (fn-aec-pool-statep fn-page-read-pool)
               (not (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled)))
  (let ((next (mv-nth 3 (fn-owner-index-connection-fault fn-allocation-turn-slots fn-page-read-pool state))))
   (and (fn-aec-pool-statep next) (not (eq (fn-prp-alloc-mode next) :uninstalled)))))
 :hints (("Goal" :in-theory (disable fn-owner-index-connection-fault fn-aec-pool-statep)
  :use ((:instance fn-owner-index-connection-fault-preserves-carried-pool
          (slots fn-allocation-turn-slots) (pool fn-page-read-pool)))))
 :rule-classes nil)

(defthm fn-owner-index-connection-finish-consumes-one
 (implies (eq (mv-nth 1 (fn-owner-index-connection-finish slot nonce slots pool state)) :left)
  (let ((next (mv-nth 3 (fn-owner-index-connection-finish slot nonce slots pool state))))
   (and (equal (fn-prp-alloc-active-turns next) (- (fn-prp-alloc-active-turns pool) 1))
        (equal (fn-prp-alloc-allocated next) (fn-prp-alloc-allocated pool)))))
 :hints (("Goal" :in-theory
          (disable nth update-nth fn-aec-pool-statep
                   fn-owner-connection-operation-ticket fn-omk-at fn-omk-widthp)))
 :rule-classes nil)


(defthm fn-owner-index-connection-fault-raw-pool
 (implies (and (fn-aec-pool-statep fn-page-read-pool)
               (not (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled)))
  (fn-aec-pool-statep
   (mv-nth 3 (fn-owner-index-connection-fault fn-allocation-turn-slots fn-page-read-pool state))))
 :hints (("Goal" :in-theory (disable fn-owner-index-connection-fault fn-aec-pool-statep)
  :use fn-owner-index-connection-fault-raw-with))
 :rule-classes nil)


