; Charged full-identity decoded job admission. DEMAND must be derived by
; the selected-runtime producer; a supplied vector alone is not adequacy.
(in-package "ACL2")
(include-book "decoded-window-descriptor")
(include-book "page-read-ledger")
(include-book "page-window-lease") ; fn-prw-phase

(defun fn-pwz-admit (ledger descriptor demand)
  (declare (xargs :guard t))
  (let* ((budget (fn-prl-nth 0 ledger)) (charged (fn-prl-nth 1 ledger))
         (next (fn-prl-nth 2 ledger)) (file (fn-pwz-nth 0 descriptor)))
    (mv-let (word next1 charged1)
      (if (and (fn-pwz-descriptorp descriptor)
               (equal (fn-prl-nth 1 (cdr (fn-prl-binding (list :incarnation file)
                                                        (fn-prl-nth 3 ledger)))) :incarnation)
               (fn-prs-vectorp demand) (equal (fn-prl-nth 3 demand) 1)
               (equal (fn-prl-nth 4 demand) 1))
          (fn-prs-issue budget (fn-prl-baseline ledger) '(0 0 0 0 0)
                        charged next (fn-prl-nth 4 budget) demand)
        (mv :invalid-decoded-window-demand next charged))
      (if (not (equal word :admitted)) (mv word nil ledger)
        (let ((token (cons :decoded-window (cons next descriptor))))
          (mv :admitted token
              (fn-prl-build budget charged1 next1
                (cons (cons token (list demand :window :running)) (fn-prl-nth 3 ledger))
                (fn-prl-nth 4 ledger))))))))

(defthm fn-pwz-admit-preserves-pool-funding
  (implies (equal (mv-nth 0 (fn-pwz-admit ledger descriptor demand)) :admitted)
           (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger) '(0 0 0 0 0)
             (fn-prl-nth 1 (mv-nth 2 (fn-pwz-admit ledger descriptor demand)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-admit fn-prl-nth fn-prl-build)
           :use ((:instance fn-prs-issue-preserves-static-rescue
                    (budget (fn-prl-nth 0 ledger)) (used (fn-prl-baseline ledger))
                    (rescue '(0 0 0 0 0)) (charged (fn-prl-nth 1 ledger))
                    (next (fn-prl-nth 2 ledger))
                    (limit (fn-prl-nth 4 (fn-prl-nth 0 ledger))))))))

(defthm fn-pwz-admitted-window-holds-file
  (implies (equal (mv-nth 0 (fn-pwz-admit ledger descriptor demand)) :admitted)
           (equal (fn-prl-close-preview (mv-nth 2 (fn-pwz-admit ledger descriptor demand))
                                        (fn-pwz-nth 0 descriptor)) :read-file-held))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-admit fn-prl-nth fn-prl-build
                                    fn-prl-close-preview fn-prl-file-heldp fn-pwz-nth))))

; ---------------------------------------------------------------------------
; The verified-window cache's lease for a decoded window (lane w-window,
; 2026-10-04; the raw window's is books/page-window-lease.lisp fn-prw-cache).
; A returned decoded window whose publication was read keeps its private
; window buffer in the realizer's window cache instead of freeing it.  Its
; row becomes a :cached row charged KEEP -- the buffer's own resident octets,
; no worker slot, no descriptor, no identity -- and the rest of its demand is
; released.  A decoded job reuses the persistent worker's backing, so its
; DEMAND carries no storage of its own (fn-dwb-reused-window-vector): the kept
; buffer is a NEW charge, drawn against the pool and refused when the pool
; cannot fund it (the caller then releases the job and caches nothing).
; The :cached row is the legacy cache's shape: fn-prl-evict releases KEEP on
; actual eviction and fn-prl-file-heldp keeps the file incarnation open until
; then.
(local
 (defthm fn-pwz-plus-true-listp
   (true-listp (fn-prs-plus a b))
   :hints (("Goal" :in-theory (enable fn-prs-plus)))))

(local
 (defthm fn-pwz-nats-are-a-true-list
   (implies (fn-prs-nats-p x) (true-listp x))
   :hints (("Goal" :in-theory (enable fn-prs-nats-p)))))

(defun fn-pwz-keep-okp (keep)
  (declare (xargs :guard t))
  (and (fn-prs-vectorp keep)
       (equal (fn-prl-nth 1 keep) 0) (equal (fn-prl-nth 2 keep) 0)
       (equal (fn-prl-nth 3 keep) 0) (equal (fn-prl-nth 4 keep) 0)))

(defun fn-pwz-cache-lease (ledger token keep)
  (declare (xargs :guard t))
  (let* ((row (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))
         (charged (fn-prl-nth 1 ledger)) (demand (fn-prl-nth 0 row)))
    (if (not (and (fn-pwz-tokenp token)
                  (equal (fn-prw-phase ledger token) :returned)
                  (true-listp charged) (true-listp demand) (fn-pwz-keep-okp keep)
                  (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger) '(0 0 0 0 0)
                                  (fn-prs-plus (fn-prs-release-reusable charged demand) keep))))
        (mv :uncached ledger)
      (mv :cached
          (fn-prl-build (fn-prl-nth 0 ledger)
                        (fn-prs-plus (fn-prs-release-reusable charged demand) keep)
                        (fn-prl-nth 2 ledger)
                        (cons (cons token (list keep :cached nil))
                              (fn-prl-remove token (fn-prl-nth 3 ledger)))
                        (fn-prl-nth 4 ledger))))))

; KEYSTONE (the decoded cache's lease).  Only a returned decoded window is
; cached; its row becomes exactly (KEEP :cached nil), charged no worker slot,
; descriptor or identity; the charge is the demand released and KEEP added,
; and the pool is still funded under it (the new charge was admitted, never
; assumed); the identity counter is untouched.
(defthm fn-pwz-cache-lease-keeps-only-the-buffer-and-stays-funded
  (implies (equal (mv-nth 0 (fn-pwz-cache-lease ledger token keep)) :cached)
           (let* ((ledger1 (mv-nth 1 (fn-pwz-cache-lease ledger token keep)))
                  (demand (fn-prl-nth 0 (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))))
             (and (fn-pwz-tokenp token)
                  (equal (fn-prw-phase ledger token) :returned)
                  (fn-pwz-keep-okp keep)
                  (equal (cdr (fn-prl-binding token (fn-prl-nth 3 ledger1)))
                         (list keep :cached nil))
                  (equal (fn-prl-nth 1 ledger1)
                         (fn-prs-plus (fn-prs-release-reusable (fn-prl-nth 1 ledger) demand) keep))
                  (fn-prs-fundedp (fn-prl-nth 0 ledger1) (fn-prl-baseline ledger1) '(0 0 0 0 0)
                                  (fn-prl-nth 1 ledger1))
                  (equal (fn-prl-nth 2 ledger1) (fn-prl-nth 2 ledger)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-cache-lease fn-prl-build fn-prl-nth fn-prl-binding
                                     fn-prl-baseline))))

; A window that is not returned, or whose KEEP the pool cannot fund, is not
; cached and the ledger is unchanged.
(defthm fn-pwz-uncached-window-leaves-the-ledger
  (implies (not (equal (mv-nth 0 (fn-pwz-cache-lease ledger token keep)) :cached))
           (equal (mv-list 2 (fn-pwz-cache-lease ledger token keep)) (list :uncached ledger)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-cache-lease))))

; A cached decoded window holds its file incarnation until eviction
; (retirement evicts first: host/native/extent.lisp fnn-extent-close).
(defthm fn-pwz-cached-window-holds-file
  (implies (and (equal (mv-nth 0 (fn-pwz-cache-lease ledger token keep)) :cached)
                (consp token) (consp (cdr token)) (consp (cddr token)))
           (equal (fn-prl-close-preview (mv-nth 1 (fn-pwz-cache-lease ledger token keep))
                                        (fn-prl-nth 2 token)) :read-file-held))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-cache-lease fn-prl-build fn-prl-nth
                                     fn-prl-close-preview fn-prl-file-heldp))))

; Eviction releases exactly KEEP and removes the row.
(defthm fn-pwz-cached-window-evicts-its-keep
  (implies (equal (mv-nth 0 (fn-pwz-cache-lease ledger token keep)) :cached)
           (let ((ledger1 (mv-nth 1 (fn-pwz-cache-lease ledger token keep))))
             (and (equal (mv-nth 0 (fn-prl-evict ledger1 token)) :evicted)
                  (equal (fn-prl-nth 1 (mv-nth 1 (fn-prl-evict ledger1 token)))
                         (fn-prs-release-reusable (fn-prl-nth 1 ledger1) keep)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-cache-lease fn-prl-evict fn-prl-build fn-prl-nth
                                     fn-prl-binding fn-pwz-keep-okp fn-prs-vectorp))))

(in-theory (disable fn-pwz-admit fn-pwz-keep-okp fn-pwz-cache-lease))
