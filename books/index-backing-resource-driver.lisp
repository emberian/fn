; Atomic indexed resource transitions over the ONE shared actual pool.
; Internal admission/promotion operands still require operation-derived
; adequacy/installed ownership; no D40 host admission vector is authorized.
(in-package "ACL2")
(logic)
(include-book "index-backing-provider")
(include-book "index-query-resources")
(include-book "page-read-pool-state")

(defun fn-ibp-query-resource-token (token capture context)
  (declare (xargs :guard t))
  (let ((payload (fn-omk-at 5 context)))
    (list :query-grant (fn-omk-at 1 token) (fn-omk-at 2 token)
          (fn-omk-at 3 token) (fn-omk-at 4 token)
          (fn-ibp-capture-table-root-id capture) (fn-ibp-capture-row-root-id capture)
          (fn-ibp-capture-count capture) (fn-ibp-capture-frontier capture)
          (fn-omk-at 4 token) (fn-omk-at 4 payload) (fn-omk-at 5 payload))))

(defun fn-ibp-query-slot-resource (token operation operand settlement ledger fn-ibp-query-segment)
  (declare (xargs :stobjs fn-ibp-query-segment :guard t))
  (if (not (fn-ibp-query-slot-livep token fn-ibp-query-segment))
      (mv :stale nil ledger fn-ibp-query-segment)
    (let* ((slot (nth 3 token))
           (capture (fn-ibp-qs-capturesi slot fn-ibp-query-segment))
           (context (fn-ibp-qs-inputsi slot fn-ibp-query-segment))
           (claim (fn-ibp-query-resource-token token capture context))
           (row (fn-ibp-qs-admissionsi slot fn-ibp-query-segment)))
      (mv-let (status grant next-row next-ledger)
        (case operation
          (:admit (fn-iqr-admit ledger claim row operand))
          (:cancel (mv-let (word next-row next-ledger) (fn-iqr-cancel claim row ledger)
                     (mv word nil next-row next-ledger)))
          (:release (mv-let (word next-row next-ledger) (fn-iqr-release claim row settlement ledger)
                      (mv word nil next-row next-ledger)))
          (:promote (if (not (fn-iqr-livep claim row))
                        (mv :stale nil row ledger)
                      (mv-let (word next-row next-ledger)
                        (fn-iqr-promote-installed-capacity claim row operand ledger)
                        (mv word nil next-row next-ledger))))
          (otherwise (mv :recovery-required nil row ledger)))
        (let ((fn-ibp-query-segment
               (if (member-eq status '(:admitted :retained :released :promoted))
                   (update-fn-ibp-qs-admissionsi slot next-row fn-ibp-query-segment)
                 fn-ibp-query-segment)))
          (mv status grant next-ledger fn-ibp-query-segment))))))

(defun fn-ibp-node-resource (token operation operand settlement ledger fuel slot depth fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :measure (nfix depth)
                  :guard (and (natp fuel) (natp slot) (natp depth)) :verify-guards nil))
  (cond ((<= fuel depth) (mv :yield nil ledger fuel fn-ibp-node))
        ((zp depth) (if (not (fn-ibp-node-children-boundp 'fn-ibp-query-segment fn-ibp-node))
        (mv :unavailable nil ledger fuel fn-ibp-node)
      (stobj-let ((fn-ibp-query-segment
                   (fn-ibp-node-children-get 'fn-ibp-query-segment fn-ibp-node
                                             (create-fn-ibp-query-segment))))
        (status grant next-ledger fn-ibp-query-segment)
        (fn-ibp-query-slot-resource token operation operand settlement ledger fn-ibp-query-segment)
        (mv status grant next-ledger (- fuel 1) fn-ibp-node))))
        ((equal (mod slot 2) 0) (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
        (mv :unavailable nil ledger fuel fn-ibp-node)
      (stobj-let ((fn-ibp-node-left
                   (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                             (create-fn-ibp-node-left))))
        (status grant next-ledger fuel-left fn-ibp-node-left)
        (fn-ibp-node-resource token operation operand settlement ledger (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-left)
        (mv status grant next-ledger fuel-left fn-ibp-node))))
        (t (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
        (mv :unavailable nil ledger fuel fn-ibp-node)
      (stobj-let ((fn-ibp-node-right
                   (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                             (create-fn-ibp-node-right))))
        (status grant next-ledger fuel-left fn-ibp-node-right)
        (fn-ibp-node-resource token operation operand settlement ledger (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-right)
        (mv status grant next-ledger fuel-left fn-ibp-node))))))
(verify-guards fn-ibp-node-resource)


(defun fn-ibp-resource-transition (token operation operand settlement fuel fn-index-backing fn-page-read-pool)
  (declare (xargs :stobjs (fn-index-backing fn-page-read-pool)
                  :guard (natp fuel)))
  (let ((capacity (fn-ibp-pool-capacity fn-index-backing))
        (depth (fn-ibp-slot-depth fn-index-backing)))
    (if (or (not (fn-ibp-query-tokenp token))
            (>= (- (nth 2 token) 1) capacity))
        (mv :stale nil fuel fn-index-backing fn-page-read-pool)
      (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
        (status grant next-ledger fuel-left fn-ibp-node)
        (fn-ibp-node-resource token operation operand settlement
                             (fn-owner-page-read-ledger fn-page-read-pool)
                             fuel (- (nth 2 token) 1) depth fn-ibp-node)
        (let ((fn-page-read-pool
               (if (member-eq status '(:admitted :retained :released :promoted))
                   (fn-owner-page-read-keep-ledger next-ledger fn-page-read-pool)
                 fn-page-read-pool)))
          (mv status grant fuel-left fn-index-backing fn-page-read-pool))))))

(defun fn-miq-resource-transition (token operation operand settlement fuel fn-mio$c fn-page-read-pool)
  (declare (xargs :stobjs (fn-mio$c fn-page-read-pool) :guard (natp fuel)))
  (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
    (status grant fuel-left fn-index-backing fn-page-read-pool)
    (fn-ibp-resource-transition token operation operand settlement fuel fn-index-backing fn-page-read-pool)
    (mv status grant fuel-left fn-mio$c fn-page-read-pool)))

(defun fn-ibp-query-slot-lifecycle (token operation fn-ibp-query-segment)
  (declare (xargs :stobjs fn-ibp-query-segment :guard t))
  (if (not (fn-ibp-query-slot-livep token fn-ibp-query-segment))
      (mv :stale fn-ibp-query-segment)
    (let* ((slot (nth 3 token)) (query (fn-ibp-qs-controlsi slot fn-ibp-query-segment)))
      (cond
       ((eq operation :cancel)
        (let* ((fn-ibp-query-segment
                (if (fn-ibp-control-kindp :mid query)
                    (update-fn-ibp-qs-controlsi slot
                      (fn-miq-with-progress query (fn-miq-cursor query)
                        (fn-miq-pending query) (fn-miq-best query) :cancelled)
                      fn-ibp-query-segment)
                  fn-ibp-query-segment)))
          ; Cancelled admission/control forbids new work. Preserve the actual
          ; in-flight borrow descriptor and prior roots until true settlement.
          (mv :cancelled fn-ibp-query-segment)))
       ((and (eq operation :release)
             (eq (fn-omk-at 2 (fn-ibp-qs-admissionsi slot fn-ibp-query-segment)) :released)
             (< 0 (fn-ibp-qs-active fn-ibp-query-segment)))
        (let* ((fn-ibp-query-segment (update-fn-ibp-qs-controlsi slot nil fn-ibp-query-segment))
               (fn-ibp-query-segment (update-fn-ibp-qs-capturesi slot nil fn-ibp-query-segment))
               (fn-ibp-query-segment (update-fn-ibp-qs-inputsi slot nil fn-ibp-query-segment))
               (fn-ibp-query-segment (update-fn-ibp-qs-borrowsi slot nil fn-ibp-query-segment))
               (fn-ibp-query-segment (update-fn-ibp-qs-ticketsi slot 0 fn-ibp-query-segment))
               (fn-ibp-query-segment (update-fn-ibp-qs-active (- (fn-ibp-qs-active fn-ibp-query-segment) 1) fn-ibp-query-segment)))
          (mv :released fn-ibp-query-segment)))
       (t (mv :recovery-required fn-ibp-query-segment))))))

(defun fn-ibp-node-lifecycle (token operation fuel slot depth fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :measure (nfix depth)
                  :guard (and (natp fuel) (natp slot) (natp depth)) :verify-guards nil))
  (cond ((<= fuel depth) (mv :yield fuel fn-ibp-node))
        ((zp depth) (if (not (fn-ibp-node-children-boundp 'fn-ibp-query-segment fn-ibp-node))
        (mv :unavailable fuel fn-ibp-node)
      (stobj-let ((fn-ibp-query-segment
                   (fn-ibp-node-children-get 'fn-ibp-query-segment fn-ibp-node
                                             (create-fn-ibp-query-segment))))
        (status fn-ibp-query-segment)
        (fn-ibp-query-slot-lifecycle token operation fn-ibp-query-segment)
        (mv status (- fuel 1) fn-ibp-node))))
        ((equal (mod slot 2) 0) (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
        (mv :unavailable fuel fn-ibp-node)
      (stobj-let ((fn-ibp-node-left
                   (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                             (create-fn-ibp-node-left))))
        (status fuel-left fn-ibp-node-left)
        (fn-ibp-node-lifecycle token operation (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-left)
        (mv status fuel-left fn-ibp-node))))
        (t (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
        (mv :unavailable fuel fn-ibp-node)
      (stobj-let ((fn-ibp-node-right
                   (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                             (create-fn-ibp-node-right))))
        (status fuel-left fn-ibp-node-right)
        (fn-ibp-node-lifecycle token operation (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-right)
        (mv status fuel-left fn-ibp-node))))))
(verify-guards fn-ibp-node-lifecycle)



(defun fn-ibp-node-payload-transition (token expected operation settlement fuel slot depth fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :measure (nfix depth)
                  :guard (and (natp fuel) (natp slot) (natp depth)) :verify-guards nil))
  (cond ((<= fuel depth) (mv :yield fuel fn-ibp-node))
        ((zp depth) (if (not (fn-ibp-node-children-boundp 'fn-query-payload-grants fn-ibp-node))
        (mv :unavailable fuel fn-ibp-node)
      (stobj-let ((fn-query-payload-grants
                   (fn-ibp-node-children-get 'fn-query-payload-grants fn-ibp-node
                                             (create-fn-query-payload-grants))))
        (status fn-query-payload-grants)
        (if (not (and (fn-qpg-livep token fn-query-payload-grants)
                      (< (fn-qpg-slot token) 64)
                      (equal (fn-omk-at 1 (fn-qpg-rowsi (fn-qpg-slot token) fn-query-payload-grants)) expected)))
            (mv :recovery-required fn-query-payload-grants)
          (if (eq operation :cancel)
              (fn-qpg-cancel token fn-query-payload-grants)
            (mv-let (word ignored fn-query-payload-grants)
              (fn-qpg-release token settlement fn-query-payload-grants)
              (declare (ignore ignored))
              (mv word fn-query-payload-grants))))
        (mv status (- fuel 1) fn-ibp-node))))
        ((equal (mod slot 2) 0) (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
        (mv :unavailable fuel fn-ibp-node)
      (stobj-let ((fn-ibp-node-left
                   (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                             (create-fn-ibp-node-left))))
        (status fuel-left fn-ibp-node-left)
        (fn-ibp-node-payload-transition token expected operation settlement (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-left)
        (mv status fuel-left fn-ibp-node))))
        (t (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
        (mv :unavailable fuel fn-ibp-node)
      (stobj-let ((fn-ibp-node-right
                   (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                             (create-fn-ibp-node-right))))
        (status fuel-left fn-ibp-node-right)
        (fn-ibp-node-payload-transition token expected operation settlement (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-right)
        (mv status fuel-left fn-ibp-node))))))
(verify-guards fn-ibp-node-payload-transition)



; Shallow stobj shape facts support composition guards; they are not the
; operational registry/content carry or the shared debt conservation theorem.
(defthm fn-ibp-node-children-put-preserves-shape
  (implies (fn-ibp-nodep node)
           (fn-ibp-nodep (fn-ibp-node-children-put key child node)))
  :hints (("Goal" :in-theory (enable fn-ibp-nodep fn-ibp-node-children-put))))
(defthm fn-ibp-node-resource-preserves-shape
  (implies (fn-ibp-nodep fn-ibp-node)
           (fn-ibp-nodep (mv-nth 4 (fn-ibp-node-resource token operation operand settlement ledger fuel slot depth fn-ibp-node))))
  :hints (("Goal" :expand ((fn-ibp-node-resource token operation operand settlement ledger fuel slot depth fn-ibp-node))
                  :in-theory (disable fn-ibp-node-resource fn-ibp-nodep fn-ibp-node-children-put))))
(defthm fn-ibp-node-lifecycle-preserves-shape
  (implies (fn-ibp-nodep fn-ibp-node)
           (fn-ibp-nodep (mv-nth 2 (fn-ibp-node-lifecycle token operation fuel slot depth fn-ibp-node))))
  :hints (("Goal" :expand ((fn-ibp-node-lifecycle token operation fuel slot depth fn-ibp-node))
                  :in-theory (disable fn-ibp-node-lifecycle fn-ibp-nodep fn-ibp-node-children-put))))
(defthm fn-ibp-node-payload-transition-preserves-shape
  (implies (fn-ibp-nodep fn-ibp-node)
           (fn-ibp-nodep (mv-nth 2 (fn-ibp-node-payload-transition token expected operation settlement fuel slot depth fn-ibp-node))))
  :hints (("Goal" :expand ((fn-ibp-node-payload-transition token expected operation settlement fuel slot depth fn-ibp-node))
                  :in-theory (disable fn-ibp-node-payload-transition fn-ibp-nodep fn-ibp-node-children-put))))

; Four complete registered-tree actions are reserved before mutation. Grant
; cancellation keeps both debts; final joined release clears BOTH authorities
; and retires the exact query slot, retaining spent nonces in their rows.
(defun fn-ibp-coupled-internal (token operation settlement fuel slot depth active ledger fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :verify-guards nil
                  :guard (and (fn-ibp-query-tokenp token) (natp fuel)
                              (natp slot) (natp depth) (natp active))))
  (let ((cost (+ 1 depth)))
    (mv-let (auth payload claim after-read)
      (fn-ibp-node-query-grant-read token (if (eq operation :release) :release :settle) fuel slot depth fn-ibp-node)
      (cond
       ((not (eq auth :authorized)) (mv auth ledger 0 after-read fn-ibp-node))
       ((not (and (fn-qpg-tokenp payload) (natp after-read) (<= after-read fuel)
                  (<= (+ (* 3 cost) 1) after-read) (< 0 active)
                  (member-eq operation '(:cancel :release))))
        (mv :recovery-required ledger 0 after-read fn-ibp-node))
       (t
        (let ((reserve (+ (* 2 cost) 1)))
          (mv-let (grant-word after-grant fn-ibp-node)
            (fn-ibp-node-payload-transition payload claim operation settlement
                                            (- after-read reserve) slot depth fn-ibp-node)
            (cond
             ((not (and (natp after-grant) (<= after-grant (- after-read reserve))))
              (mv :recovery-required ledger (if (eq grant-word :released) 1 0)
                  0 fn-ibp-node))
             ((not (or (eq grant-word :released)
                       (and (eq operation :cancel) (eq grant-word :retained))))
              (mv grant-word ledger 0 (+ after-grant reserve) fn-ibp-node))
             (t
              (mv-let (resource-word ignored next-ledger after-resource fn-ibp-node)
                (fn-ibp-node-resource token operation nil settlement ledger
                                      (+ after-grant cost) slot depth fn-ibp-node)
                (declare (ignore ignored))
                (cond
                 ((not (and (natp after-resource) (<= after-resource (+ after-grant cost))))
                  (mv :recovery-required next-ledger (if (eq grant-word :released) 1 0)
                      0 fn-ibp-node))
                 ((not (or (and (eq operation :release) (eq resource-word :released))
                           (and (eq operation :cancel) (eq resource-word :retained))))
                  (mv :recovery-required next-ledger (if (eq grant-word :released) 1 0)
                      (+ after-resource cost) fn-ibp-node))
                 (t
                  (mv-let (end-word after-end fn-ibp-node)
                    (fn-ibp-node-lifecycle token operation (+ after-resource cost) slot depth fn-ibp-node)
                    (mv end-word next-ledger (if (eq grant-word :released) 1 0)
                        after-end fn-ibp-node))))))))))))))
(verify-guards fn-ibp-coupled-internal
  :hints (("Goal" :in-theory (disable fn-ibp-node-resource fn-ibp-node-lifecycle
                                    fn-ibp-node-payload-transition fn-ibp-node-query-grant-read
                                    fn-ibp-nodep))))

(defthm fn-ibp-coupled-internal-preserves-shape
  (implies (fn-ibp-nodep fn-ibp-node)
           (fn-ibp-nodep (mv-nth 4 (fn-ibp-coupled-internal token operation settlement fuel slot depth active ledger fn-ibp-node))))
  :hints (("Goal" :in-theory (e/d (fn-ibp-coupled-internal)
    (fn-ibp-node-resource fn-ibp-node-lifecycle fn-ibp-node-payload-transition
     fn-ibp-node-query-grant-read fn-ibp-nodep)))))

(defun fn-ibp-coupled-transition (token operation settlement fuel fn-index-backing fn-page-read-pool)
  (declare (xargs :stobjs (fn-index-backing fn-page-read-pool)
                  :guard (natp fuel) :verify-guards nil))
  (let* ((capacity (fn-ibp-pool-capacity fn-index-backing))
         (depth (fn-ibp-slot-depth fn-index-backing))
         (active (fn-ibp-payload-active fn-index-backing)))
    (cond
     ((or (not (fn-ibp-query-tokenp token)) (>= (- (nth 2 token) 1) capacity))
      (mv :stale fuel fn-index-backing fn-page-read-pool))
     ((< fuel (+ (* 4 (+ 1 depth)) 1)) (mv :yield fuel fn-index-backing fn-page-read-pool))
     (t
      (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
        (status next-ledger delta fuel-left fn-ibp-node)
        (fn-ibp-coupled-internal token operation settlement fuel (- (nth 2 token) 1)
                                 depth active (fn-owner-page-read-ledger fn-page-read-pool) fn-ibp-node)
        (let* ((fn-index-backing
                (if (and (equal delta 1) (< 0 active))
                    (update-fn-ibp-payload-active (- active 1) fn-index-backing)
                  fn-index-backing))
               (fn-page-read-pool
                (if (or (equal delta 1) (eq status :cancelled))
                    (fn-owner-page-read-keep-ledger next-ledger fn-page-read-pool)
                  fn-page-read-pool)))
          (mv status fuel-left fn-index-backing fn-page-read-pool)))))))

(verify-guards fn-ibp-coupled-transition
  :hints (("Goal" :in-theory (disable fn-ibp-coupled-internal fn-ibp-nodep))))

(defun fn-miq-cancel (token fuel fn-mio$c fn-page-read-pool)
  (declare (xargs :stobjs (fn-mio$c fn-page-read-pool) :guard (natp fuel)))
  (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
    (status fuel-left fn-index-backing fn-page-read-pool)
    (fn-ibp-coupled-transition token :cancel nil fuel fn-index-backing fn-page-read-pool)
    (mv status fuel-left fn-mio$c fn-page-read-pool)))

(defun fn-miq-release (token settlement fuel fn-mio$c fn-page-read-pool)
  (declare (xargs :stobjs (fn-mio$c fn-page-read-pool) :guard (natp fuel)))
  (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
    (status fuel-left fn-index-backing fn-page-read-pool)
    (fn-ibp-coupled-transition token :release settlement fuel fn-index-backing fn-page-read-pool)
    (mv status fuel-left fn-mio$c fn-page-read-pool)))
