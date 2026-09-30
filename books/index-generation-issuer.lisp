; Internal unpublished generation issuance. The source/runtime admission
; producer supplies the operation-derived demand; this book neither exports
; a native vector argument nor infers constructor adequacy from its shape.
(in-package "ACL2")
(logic)
(include-book "index-backing-writer")
(include-book "page-read-pool-state")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-igr-candidate (fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let ((free (fn-ibp-generation-free fn-index-backing))
       (high (fn-ibp-generation-highwater fn-index-backing))
       (capacity (fn-ibp-pool-capacity fn-index-backing)))
  (cond ((consp free)
         (if (and (natp (car free)) (< (car free) high)
                  (< (car free) (* 64 capacity)))
             (mv :recycled (car free)) (mv :recovery-required nil)))
        ((not (null free)) (mv :recovery-required nil))
        ((< high (* 64 capacity)) (mv :fresh high))
        (t (mv :unavailable nil)))))

; Builder reservation keeps the exact PC and old publication references.
; Candidate ownership changes only after definite child registration; until
; then the outstanding builder makes another reserve busy. Identity debit is
; committed before constructing any retained builder/receipt metadata.
(defun fn-igr-reserve (pc demand fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool) :guard t))
 (if (fn-ibp-builder fn-index-backing)
     (mv :busy nil fn-index-backing fn-page-read-pool)
   (mv-let (kind ordinal) (fn-igr-candidate fn-index-backing)
    (if (not (and (member-eq kind '(:fresh :recycled)) (natp ordinal)))
        (mv kind nil fn-index-backing fn-page-read-pool)
      (let* ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
             (budget (fn-prl-nth 0 ledger)) (charged (fn-prl-nth 1 ledger))
             (next (fn-prl-nth 2 ledger))
             (current (fn-ibp-current fn-index-backing)))
       (cond
        ((not (and (fn-prs-vectorp demand) (equal (fn-prl-nth 4 demand) 1)))
         (mv :unsupported-runtime nil fn-index-backing fn-page-read-pool))
        ((not (and (natp (fn-pc-expected pc))
                   (or (and (null current) (equal (fn-pc-expected pc) 0))
                       (and (fn-omk-widthp current 3)
                            (eq (fn-omk-at 0 current) :installed-publication)
                            (fn-ibp-generation-tokenp (fn-omk-at 1 current))
                            (equal (fn-pc-expected pc)
                                   (fn-ipub-count (fn-omk-at 2 current)))))))
         (mv :recovery-required nil fn-index-backing fn-page-read-pool))
        (t
         (mv-let (word issued next-charge)
          (fn-prs-issue budget (fn-prl-baseline ledger) '(0 0 0 0 0)
                        charged next (fn-prl-nth 4 budget) demand)
          (if (not (and (eq word :admitted) (posp issued)))
              (mv word nil fn-index-backing fn-page-read-pool)
            (let* ((fn-page-read-pool
                     (fn-owner-page-read-keep-ledger
                      (fn-prl-build budget next-charge issued (fn-prl-nth 3 ledger)
                                    (fn-prl-baseline ledger)) fn-page-read-pool))
                   (token (list :index-generation issued (+ 1 (floor ordinal 64)) (mod ordinal 64)))
                   (receipt (list :generation-reservation next issued ordinal kind demand pc current))
                   (builder (list :index-builder :reserved token (fn-omk-at 1 current)
                                  nil nil (fn-pc-expected pc) (fn-pc-token pc) (fn-pc-held pc)
                                  nil nil nil nil nil nil nil nil nil nil receipt))
                   (fn-index-backing (update-fn-ibp-builder builder fn-index-backing)))
             (mv :reserved token fn-index-backing fn-page-read-pool)))))))))))

; Register only an already constructed, stamped fixed segment. Missing
; nodes/segments never invoke a default creator. Construction is a separate
; admitted operation; registering a row is not proof of that operation.
(defun fn-igr-node-register (token receipt fuel address depth fn-ibp-node)
 (declare (xargs :stobjs fn-ibp-node :measure (nfix depth) :verify-guards nil
                 :guard (and (natp fuel) (natp address) (natp depth))))
 (cond ((<= fuel depth) (mv :yield fuel fn-ibp-node))
       ((zp depth)
        (if (not (and (zp address)
                      (fn-ibp-node-children-boundp 'fn-ibp-generation-segment fn-ibp-node)))
            (mv :unavailable fuel fn-ibp-node)
          (stobj-let ((fn-ibp-generation-segment
                       (fn-ibp-node-children-get 'fn-ibp-generation-segment fn-ibp-node
                                                 (create-fn-ibp-generation-segment))))
           (status fn-ibp-generation-segment)
           (fn-ibp-generation-begin token receipt fn-ibp-generation-segment)
           (mv status (- fuel 1) fn-ibp-node))))
       ((evenp address)
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
            (mv :unavailable fuel fn-ibp-node)
          (stobj-let ((fn-ibp-node-left
                       (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                                 (create-fn-ibp-node-left))))
           (status remaining fn-ibp-node-left)
           (fn-igr-node-register token receipt (- fuel 1) (floor address 2) (- depth 1) fn-ibp-node-left)
           (mv status remaining fn-ibp-node))))
       (t
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
            (mv :unavailable fuel fn-ibp-node)
          (stobj-let ((fn-ibp-node-right
                       (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                                 (create-fn-ibp-node-right))))
           (status remaining fn-ibp-node-right)
           (fn-igr-node-register token receipt (- fuel 1) (floor address 2) (- depth 1) fn-ibp-node-right)
           (mv status remaining fn-ibp-node))))))
(verify-guards fn-igr-node-register)

(defthm fn-igr-node-register-preserves-shape
 (implies (fn-ibp-nodep fn-ibp-node)
  (fn-ibp-nodep (mv-nth 2 (fn-igr-node-register token receipt fuel address depth fn-ibp-node))))
 :hints (("Goal" :expand ((fn-igr-node-register token receipt fuel address depth fn-ibp-node))
          :in-theory (disable fn-igr-node-register fn-ibp-nodep fn-ibp-node-children-put))))

(defun fn-igr-register (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel) :verify-guards nil))
 (let* ((builder (fn-ibp-builder fn-index-backing))
        (token (fn-omk-at 2 builder)) (receipt (fn-omk-at 19 builder))
        (ordinal (fn-omk-at 3 receipt)) (kind (fn-omk-at 4 receipt))
        (free (fn-ibp-generation-free fn-index-backing))
        (high (fn-ibp-generation-highwater fn-index-backing))
        (depth (fn-ibp-slot-depth fn-index-backing)))
  (cond
   ((not (and (fn-omk-widthp builder 20) (true-listp builder)
              (eq (fn-omk-at 0 builder) :index-builder)
              (fn-ibp-generation-tokenp token))) (mv :stale fuel fn-index-backing))
   ((eq (fn-omk-at 1 builder) :registered) (mv :registered fuel fn-index-backing))
   ((not (and (eq (fn-omk-at 1 builder) :reserved)
              (fn-omk-widthp receipt 8) (eq (fn-omk-at 0 receipt) :generation-reservation)
              (equal (fn-omk-at 2 receipt) (nth 1 token))
              (natp ordinal) (< ordinal (* 64 (fn-ibp-pool-capacity fn-index-backing)))
              (equal ordinal (+ (* 64 (- (nth 2 token) 1)) (nth 3 token)))
              (if (eq kind :fresh) (equal ordinal high)
                (and (eq kind :recycled) (consp free) (equal ordinal (car free))))))
    (mv :recovery-required fuel fn-index-backing))
   ((<= fuel depth) (mv :yield fuel fn-index-backing))
   (t
    (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
     (status remaining fn-ibp-node)
     (fn-igr-node-register token receipt fuel (- (nth 2 token) 1) depth fn-ibp-node)
     (if (not (eq status :reserved))
         (mv status remaining fn-index-backing)
       (let* ((fn-index-backing
                (if (eq kind :fresh)
                    (update-fn-ibp-generation-highwater (+ 1 high) fn-index-backing)
                  (update-fn-ibp-generation-free (cdr free) fn-index-backing)))
              (fn-index-backing
               (update-fn-ibp-builder (update-nth 1 :registered builder) fn-index-backing)))
        (mv :registered remaining fn-index-backing))))))))

(verify-guards fn-igr-register
 :hints (("Goal" :in-theory (disable fn-igr-node-register fn-ibp-nodep fn-ibp-node-children-put))))
