; PRF-1080: a persistent worker's reusable job incarnation.
; Native stacks belong to the installed baseline until shutdown; this row
; owns one job, not the thread's storage. Resource admission precedes assign.
; Actual return means the worker relinquished its private result; commit
; also requires exact settled I/O before releasing the charged job slot.
(in-package "ACL2")
(include-book "page-read-ownership")

(local
 (defthm fn-pxe-ledger-nth-unfolds
   (implies (natp n) (equal (fn-prl-nth n x) (nth n x)))
   :hints (("Goal" :induct (fn-prl-nth n x) :in-theory (enable fn-prl-nth nth)))))

 ; A served cold command needs a funded retainable result. Disabling the
; cache for a diagnostic run never authorizes synchronous unfunded I/O.
(defun fn-pxe-cache-mode (enabledp)
  (declare (xargs :guard (booleanp enabledp)))
  (if enabledp :ready :read-resources-unavailable))

; Worker = (slot last-read-id phase token). Last remains after idle so an
; old job cannot be assigned again to this physical worker incarnation.
(defun fn-pxe-new (slot)
  (declare (xargs :guard (natp slot)))
  (list slot nil :idle nil))

(defun fn-pxe-rowp (w)
  (declare (xargs :guard t))
  (and (true-listp w) (equal (len w) 4) (natp (nth 0 w))
       (or (null (nth 1 w)) (natp (nth 1 w)))
       (if (equal (nth 2 w) :idle)
           (null (nth 3 w))
         (and (member-equal (nth 2 w) '(:running :returned))
              (fn-pio-rowp (fn-pio-own-admitted-token (nth 3 w)))
              (equal (nth 1 w) (fn-prl-nth 0 (nth 3 w))))) t))

(defun fn-pxe-assign (w token)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-prl-nth fn-pio-rowp fn-pio-own-admitted-token)))))
  (cond ((not (and (fn-pxe-rowp w) (fn-pio-rowp (fn-pio-own-admitted-token token))))
         (mv :invalid-worker-job w))
        ((not (equal (fn-prl-nth 2 w) :idle)) (mv :worker-busy w))
        ((and (fn-prl-nth 1 w) (<= (fn-prl-nth 0 token) (fn-prl-nth 1 w)))
         (mv :stale-job w))
        (t (mv :assigned (list (fn-prl-nth 0 w) (fn-prl-nth 0 token) :running token)))))

 ; Assign the exact charged token once. The optional fourth issued binding
; field owns its worker slot; other ledger projections keep their meanings.
(defun fn-pxe-acquire (ledger w token)
  (declare (xargs :guard t))
  (let* ((bindings (fn-prl-nth 3 ledger))
         (binding (fn-prl-binding token bindings))
         (row (if (consp binding) (cdr binding) nil)))
    (if (and (equal (fn-prl-nth 1 row) :issued) (null (fn-prl-nth 3 row)))
        (mv-let (word w1) (fn-pxe-assign w token)
          (if (equal word :assigned)
              (mv :assigned w1
                  (fn-prl-build (fn-prl-nth 0 ledger) (fn-prl-nth 1 ledger) (fn-prl-nth 2 ledger)
                                (cons (cons token (list (fn-prl-nth 0 row) :issued (fn-prl-nth 2 row)
                                                        (fn-prl-nth 0 w)))
                                      (fn-prl-remove token bindings))
                                (fn-prl-nth 4 ledger)))
            (mv word w ledger)))
      (mv :stale-job w ledger))))

(defun fn-pxe-return (w token)
  (declare (xargs :guard t))
  (if (and (fn-pxe-rowp w) (equal (fn-prl-nth 2 w) :running)
           (equal token (fn-prl-nth 3 w)))
      (mv :returned (list (fn-prl-nth 0 w) (fn-prl-nth 1 w) :returned token))
    (mv :stale-job w)))

; The physical cache transfer/eviction and this transition are serialized
; with the I/O row under owner->extent. CACHEDP records actual retention.
(defun fn-pxe-commit (w io token ledger cachedp)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-pio-rowp fn-prl-nth)))))
  (if (and (fn-pxe-rowp w) (equal (fn-prl-nth 2 w) :returned)
           (equal token (fn-prl-nth 3 w))
           (equal (fn-prl-nth 3 (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))
                  (fn-prl-nth 0 w))
           (fn-pio-rowp io) (equal (fn-prl-nth 6 io) :settled)
           (equal token (fn-pio-token io)))
      (mv-let (word ledger1) (fn-prl-settle ledger token cachedp)
        (if (equal word :settled)
            (mv :committed (list (fn-prl-nth 0 w) (fn-prl-nth 1 w) :idle nil) ledger1)
          (mv :stale-job w ledger)))
    (mv :stale-job w ledger)))

(defthm fn-pxe-new-establishes-idle-worker
  (implies (natp slot) (fn-pxe-rowp (fn-pxe-new slot))))

(defthm fn-pxe-assignment-preserves-row
  (implies (fn-pxe-rowp w) (fn-pxe-rowp (mv-nth 1 (fn-pxe-assign w token))))
  :hints (("Goal" :in-theory (enable fn-prl-nth fn-pio-rowp fn-pio-own-admitted-token))))

(defthm fn-pxe-return-preserves-row
  (implies (fn-pxe-rowp w) (fn-pxe-rowp (mv-nth 1 (fn-pxe-return w token))))
  :hints (("Goal" :in-theory (enable fn-prl-nth))))

(defthm fn-pxe-commit-preserves-row
  (implies (fn-pxe-rowp w) (fn-pxe-rowp (mv-nth 1 (fn-pxe-commit w io token ledger cachedp))))
  :hints (("Goal" :in-theory (enable fn-prl-nth))))

(defthm fn-pxe-assignment-requires-idle-and-fresh-job
  (implies (equal (mv-nth 0 (fn-pxe-assign w token)) :assigned)
           (and (fn-pxe-rowp w) (equal (fn-prl-nth 2 w) :idle)
                (fn-pio-rowp (fn-pio-own-admitted-token token))
                (or (null (fn-prl-nth 1 w)) (< (fn-prl-nth 1 w) (fn-prl-nth 0 token)))
                (equal (fn-prl-nth 0 (mv-nth 1 (fn-pxe-assign w token))) (fn-prl-nth 0 w))
                (equal (fn-prl-nth 2 (mv-nth 1 (fn-pxe-assign w token))) :running)
                (equal (fn-prl-nth 3 (mv-nth 1 (fn-pxe-assign w token))) token)))
  :hints (("Goal" :in-theory (enable fn-prl-nth)))
  :rule-classes nil)

(defthm fn-pxe-stale-completion-cannot-return-a-reused-worker
  (implies (not (equal token (fn-prl-nth 3 w)))
           (and (equal (mv-nth 0 (fn-pxe-return w token)) :stale-job)
                (equal (mv-nth 1 (fn-pxe-return w token)) w)))
  :rule-classes nil)

(defthm fn-pxe-commit-requires-returned-settled-exact-job
  (implies (equal (mv-nth 0 (fn-pxe-commit w io token ledger cachedp)) :committed)
           (and (fn-pxe-rowp w) (equal (fn-prl-nth 2 w) :returned)
                (equal token (fn-prl-nth 3 w))
                (fn-pio-rowp io) (equal (fn-prl-nth 6 io) :settled)
                (equal token (fn-pio-token io))
                (equal (mv-nth 0 (fn-prl-settle ledger token cachedp)) :settled)
                (equal (fn-prl-nth 2 (mv-nth 1 (fn-pxe-commit w io token ledger cachedp))) :idle)
                (equal (fn-prl-nth 0 (mv-nth 1 (fn-pxe-commit w io token ledger cachedp)))
                       (fn-prl-nth 0 w))
                (equal (mv-nth 2 (fn-pxe-commit w io token ledger cachedp))
                       (mv-nth 1 (fn-prl-settle ledger token cachedp)))))
  :hints (("Goal" :in-theory (enable fn-prl-nth)))
  :rule-classes nil)

(defthm fn-pxe-unsettled-io-cannot-refund-a-job
  (implies (not (equal (fn-prl-nth 6 io) :settled))
           (and (equal (mv-nth 0 (fn-pxe-commit w io token ledger cachedp)) :stale-job)
                (equal (mv-nth 1 (fn-pxe-commit w io token ledger cachedp)) w)
                (equal (mv-nth 2 (fn-pxe-commit w io token ledger cachedp)) ledger)))
  :rule-classes nil)

(defthm fn-pxe-acquire-preserves-permanent-baseline
  (equal (fn-prl-nth 4 (mv-nth 2 (fn-pxe-acquire ledger w token)))
         (fn-prl-nth 4 ledger))
  :hints (("Goal" :in-theory (enable fn-prl-build fn-prl-nth))))

(defthm fn-pxe-acquired-token-cannot-own-a-second-worker
  (implies (equal (mv-nth 0 (fn-pxe-acquire ledger w token)) :assigned)
           (equal (mv-list 3 (fn-pxe-acquire (mv-nth 2 (fn-pxe-acquire ledger w token)) other token))
                  (list :stale-job other (mv-nth 2 (fn-pxe-acquire ledger w token)))))
  :hints (("Goal" :in-theory (enable fn-prl-binding fn-prl-nth fn-prl-build)))
  :rule-classes nil)

(in-theory (disable fn-pxe-new fn-pxe-rowp fn-pxe-assign fn-pxe-acquire fn-pxe-return fn-pxe-commit))
