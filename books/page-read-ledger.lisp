; P12 cold resource pool. The whole Store rescue contract is separate.
; The pool is installed only after its heap/native allowances have passed
; the launcher. Admission carries its invariant; it never scans all issued
; rows to revalidate the pool. A row binds the entire immutable read token
; to its charge, so a timeout, forged coordinate or duplicate completion
; cannot refund another read. Cancellation performs no ledger transition.
(in-package "ACL2")
(include-book "page-read-resources")

; Ledger = (budget charged next bindings [permanent-baseline]). CHARGED is
; reusable/job demand C; the optional fifth field is permanent installed U.
; The old four-field logical model has U=0. Parameters are established by
; supported-profile installation. NEXT is the single ownership ID counter.
(defun fn-prl-make (budget)
  (declare (xargs :guard t))
  (list budget '(0 0 0 0 0) 0 nil))

(defun fn-prl-nth (n x)
  (declare (xargs :guard (natp n)))
  (if (consp x) (if (zp n) (car x) (fn-prl-nth (- n 1) (cdr x))) nil))

(defun fn-prl-baseline (ledger)
  (declare (xargs :guard t))
  (or (fn-prl-nth 4 ledger) '(0 0 0 0 0)))

(defun fn-prl-build (budget charged next bindings baseline)
  (declare (xargs :guard t))
  (if baseline (list budget charged next bindings baseline)
    (list budget charged next bindings)))

(defun fn-prl-make-baseline (budget baseline)
  (declare (xargs :guard t))
  (if (fn-prs-fundedp budget baseline '(0 0 0 0 0) '(0 0 0 0 0))
      (mv :installed (fn-prl-build budget '(0 0 0 0 0) 0 nil baseline))
    (mv :invalid-resource-profile nil)))

(defun fn-prl-token (id cid file eoff elen trailer)
  (declare (xargs :guard t))
  (list id cid file eoff elen trailer))

(defun fn-prl-binding (token rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (consp (car rows)) (equal token (caar rows)))
          (car rows) (fn-prl-binding token (cdr rows))) nil))

(defun fn-prl-remove-aux (token rows rev)
  (declare (xargs :guard (true-listp rev) :measure (acl2-count rows)))
  (if (consp rows)
      (fn-prl-remove-aux token (cdr rows)
                         (if (and (consp (car rows)) (equal token (caar rows)))
                             rev (cons (car rows) rev)))
    (revappend rev rows)))

(defun fn-prl-remove (token rows)
  (declare (xargs :guard t))
  (fn-prl-remove-aux token rows nil))

; One descriptor credit belongs to a registered incarnation, not to each
; reader. Reservation precedes opening; open failure closes this lease.
(defun fn-prl-register (ledger file demand)
  (declare (xargs :guard t))
  (let* ((key (list :incarnation file))
         (bindings (fn-prl-nth 3 ledger))
         (budget (fn-prl-nth 0 ledger))
         (charged (fn-prl-nth 1 ledger)))
    (cond ((fn-prl-binding key bindings) (mv :registered ledger))
          ((not (and (posp file)
                     (fn-prs-fundedp budget (fn-prl-baseline ledger) '(0 0 0 0 0) charged)
                     (fn-prs-vectorp demand)
                     (equal (fn-prl-nth 2 demand) 1)
                     (equal (fn-prl-nth 3 demand) 0)
                     (equal (fn-prl-nth 4 demand) 0)
                     (fn-prs-fundedp budget (fn-prl-baseline ledger) '(0 0 0 0 0)
                                     (fn-prs-plus charged demand))))
           (mv :read-resources-unavailable ledger))
          (t (mv :registered
                 (fn-prl-build budget (fn-prs-plus charged demand)
                       (fn-prl-nth 2 ledger)
                       (cons (cons key (list demand :incarnation nil)) bindings)
                       (fn-prl-nth 4 ledger)))))))

(defun fn-prl-file-heldp (file rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (let* ((entry (car rows))
             (key (if (consp entry) (car entry) nil))
             (row (if (consp entry) (cdr entry) nil)))
        (or (and (member-equal (fn-prl-nth 1 row) '(:issued :cached :discovery))
                 (equal (fn-prl-nth 2 key) file))
            (fn-prl-file-heldp file (cdr rows)))) nil))

; Retirement also owes the independently carried extent/read-pin verdict.
; This boundary rejects outstanding charged reads and cached buffers itself.
; Preview allocates no changed ledger and authorizes no refund. The host
; physically closes only :closable; ambiguous close fences before fn-prl-close.
(defun fn-prl-close-preview (ledger file)
  (declare (xargs :guard t))
  (let* ((key (list :incarnation file))
         (bindings (fn-prl-nth 3 ledger))
         (entry (fn-prl-binding key bindings))
         (row (if (consp entry) (cdr entry) nil)))
    (cond ((fn-prl-file-heldp file bindings) :read-file-held)
          ((not (and (equal (fn-prl-nth 1 row) :incarnation)
                     (true-listp (fn-prl-nth 1 ledger))
                     (true-listp (fn-prl-nth 0 row)))) :stale)
          (t :closable))))

(defun fn-prl-close (ledger file)
  (declare (xargs :guard t))
  (let* ((key (list :incarnation file))
         (bindings (fn-prl-nth 3 ledger))
         (entry (fn-prl-binding key bindings))
         (row (if (consp entry) (cdr entry) nil))
         (demand (fn-prl-nth 0 row))
         (charged (fn-prl-nth 1 ledger)))
    (cond ((fn-prl-file-heldp file bindings) (mv :read-file-held ledger))
          ((not (and (equal (fn-prl-nth 1 row) :incarnation)
                     (true-listp charged) (true-listp demand))) (mv :stale ledger))
          (t (mv :closed (fn-prl-build (fn-prl-nth 0 ledger)
                              (fn-prs-release-reusable charged demand)
                              (fn-prl-nth 2 ledger)
                              (fn-prl-remove key bindings) (fn-prl-nth 4 ledger)))))))

(defun fn-prl-admit (ledger cid file eoff elen trailer demand native-demand)
  (declare (xargs :guard t))
  (let* ((budget (fn-prl-nth 0 ledger))
         (charged (fn-prl-nth 1 ledger))
         (next (fn-prl-nth 2 ledger)))
    (mv-let (verdict next1 charged1)
      (if (and (posp file) (natp cid) (natp eoff) (natp elen) (natp trailer)
               (equal (fn-prl-nth 1
                       (cdr (fn-prl-binding (list :incarnation file)
                                            (fn-prl-nth 3 ledger)))) :incarnation)
               (fn-prs-vectorp demand) (fn-prs-vectorp native-demand)
               (equal (fn-prl-nth 3 demand) 1)
               (equal (fn-prl-nth 4 demand) 1)
               (equal (fn-prl-nth 4 native-demand) 0)
               (fn-prs-below native-demand demand))
          (fn-prs-issue budget (fn-prl-baseline ledger) '(0 0 0 0 0) charged
                    next (fn-prl-nth 4 budget) demand)
        (mv :invalid-read-demand next charged))
      (if (not (equal verdict :admitted))
          (mv verdict nil ledger)
        (let ((token (fn-prl-token next cid file eoff elen trailer)))
          (mv :admitted token
              (fn-prl-build budget charged1 next1
                    (cons (cons token (list demand :issued native-demand)) (fn-prl-nth 3 ledger))
                    (fn-prl-nth 4 ledger))))))))

; Completion's caller must already have settled the matching issued I/O
; row. This operation authorizes no cancellation refund. Stale input leaves
; the ledger byte-for-byte unchanged, including the monotone ID counter.
(defun fn-prl-settle (ledger token cachedp)
  (declare (xargs :guard t))
  (let* ((bindings (fn-prl-nth 3 ledger))
         (entry (fn-prl-binding token bindings))
         (row (if (consp entry) (cdr entry) nil))
         (demand (fn-prl-nth 0 row))
         (native-demand (fn-prl-nth 2 row))
         (charged (fn-prl-nth 1 ledger)))
    (if (not (and (equal (fn-prl-nth 1 row) :issued)
                  (true-listp charged) (true-listp demand)
                  (true-listp native-demand)))
        (mv :stale ledger)
      (let* ((release (if cachedp native-demand demand))
             (remaining (fn-prs-release-reusable demand native-demand))
             (rest (fn-prl-remove token bindings)))
        (mv :settled
           (fn-prl-build (fn-prl-nth 0 ledger)
                 (fn-prs-release-reusable charged release)
                 (fn-prl-nth 2 ledger)
                 (if cachedp (cons (cons token (list remaining :cached nil)) rest) rest)
                 (fn-prl-nth 4 ledger)))))))

; Buffer credit follows the actual cached vector until eviction. Physical
; publication/eviction and this core transition are serialized owner->extent.
(defun fn-prl-evict (ledger token)
  (declare (xargs :guard t))
  (let* ((entry (fn-prl-binding token (fn-prl-nth 3 ledger)))
         (row (if (consp entry) (cdr entry) nil))
         (demand (fn-prl-nth 0 row))
         (charged (fn-prl-nth 1 ledger)))
    (if (not (and (equal (fn-prl-nth 1 row) :cached)
                  (true-listp charged) (true-listp demand)))
        (mv :stale ledger)
      (mv :evicted (fn-prl-build (fn-prl-nth 0 ledger)
                         (fn-prs-release-reusable charged demand)
                         (fn-prl-nth 2 ledger)
                         (fn-prl-remove token (fn-prl-nth 3 ledger))
                         (fn-prl-nth 4 ledger))))))

; Refusal is a real operational branch, not a hypothetical continuation.
(defthm fn-prl-admit-refused-keeps-ledger-by-definition
  (implies (not (equal (mv-nth 0 (fn-prl-admit ledger cid file eoff elen trailer demand native-demand))
                       :admitted))
           (equal (mv-nth 2 (fn-prl-admit ledger cid file eoff elen trailer demand native-demand)) ledger)))

(defthm fn-prl-admit-preserves-pool-funding
  (implies (equal (mv-nth 0 (fn-prl-admit ledger cid file eoff elen trailer demand native-demand))
                  :admitted)
           (fn-prs-fundedp
            (fn-prl-nth 0 ledger) (fn-prl-baseline ledger) '(0 0 0 0 0)
            (fn-prl-nth 1 (mv-nth 2 (fn-prl-admit ledger cid file eoff elen trailer demand native-demand)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-prs-issue-preserves-static-rescue
                         (budget (fn-prl-nth 0 ledger))
                         (used (fn-prl-baseline ledger)) (rescue '(0 0 0 0 0))
                         (charged (fn-prl-nth 1 ledger))
                         (next (fn-prl-nth 2 ledger))
                         (limit (fn-prl-nth 4 (fn-prl-nth 0 ledger))))))))

(defthm fn-prl-settle-never-reuses-identity
  (equal (fn-prl-nth 2 (mv-nth 1 (fn-prl-settle ledger token cachedp)))
         (fn-prl-nth 2 ledger)))

(local
 (defthm fn-prl-revappend-no-binding
   (implies (and (not (fn-prl-binding token a))
                 (not (fn-prl-binding token b)))
            (not (fn-prl-binding token (revappend a b))))
   :hints (("Goal" :induct (revappend a b)))))

(local
 (defthm fn-prl-remove-aux-no-binding
   (implies (not (fn-prl-binding token rev))
            (not (fn-prl-binding token (fn-prl-remove-aux token rows rev))))
   :hints (("Goal" :induct (fn-prl-remove-aux token rows rev)))))

(local
 (defthm fn-prl-removed-binding-is-absent
   (not (fn-prl-binding token (fn-prl-remove token rows)))))

(defthm fn-prl-completion-refunds-at-most-once
  (equal (mv-list 2 (fn-prl-settle
                    (mv-nth 1 (fn-prl-settle ledger token cachedp)) token cachedp))
         (list :stale (mv-nth 1 (fn-prl-settle ledger token cachedp))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prl-settle fn-prl-nth fn-prl-binding fn-prl-remove fn-prl-evict))))

(defthm fn-prl-stale-completion-keeps-ledger-by-definition
  (implies (not (fn-prl-binding token (fn-prl-nth 3 ledger)))
           (equal (mv-list 2 (fn-prl-settle ledger token cachedp)) (list :stale ledger))))

; Every successful lifecycle transition retains the installed non-job
; baseline. Settlement can release a job lease, never an idle executor.
(defthm fn-prl-lifecycle-preserves-baseline
  (and (equal (fn-prl-baseline (mv-nth 1 (fn-prl-register ledger file demand)))
              (fn-prl-baseline ledger))
       (equal (fn-prl-baseline (mv-nth 2 (fn-prl-admit ledger cid file eoff elen trailer demand native-demand)))
              (fn-prl-baseline ledger))
       (equal (fn-prl-baseline (mv-nth 1 (fn-prl-settle ledger token cachedp)))
              (fn-prl-baseline ledger))
       (equal (fn-prl-baseline (mv-nth 1 (fn-prl-evict ledger token)))
              (fn-prl-baseline ledger))
       (equal (fn-prl-baseline (mv-nth 1 (fn-prl-close ledger file)))
              (fn-prl-baseline ledger)))
  :rule-classes nil)

(in-theory (disable fn-prl-make fn-prl-baseline fn-prl-build fn-prl-make-baseline fn-prl-nth fn-prl-token fn-prl-admit fn-prl-settle
                    fn-prl-binding fn-prl-remove fn-prl-remove-aux fn-prl-evict fn-prl-register
                    fn-prl-file-heldp fn-prl-close-preview fn-prl-close))
