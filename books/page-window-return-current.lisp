; Actual registered activation-return predecessor. No last-borrow receipt.
(in-package "ACL2")
(include-book "page-window-return-continuation")
(include-book "page-window-worker-storage")
(include-book "page-read-binding-revision")

; This scalar is the existing installed domain's representation. Its shape is
; not installation provenance or an operation allowance. The selected caller
; must carry genuine installation and exclude every legacy DATA5 writer.
(defun fn-pwrt-revision-roomp (revision fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard t))
 (let ((domain (fn-prl-nth 2 (fn-prp-alloc-installation fn-page-read-pool))))
  (and (natp revision) (integerp domain) (< 1 domain) (< revision (- domain 1)))))

; CURRENT source, original pending I/O and original worker remain in the
; continuation. It is never reconstructed from a host returned/joined flag.
(defun fn-pwrt-current-step (token fuel fn-pww-carry fn-page-read-pool)
 (declare (xargs :stobjs (fn-pww-carry fn-page-read-pool)
                 :guard (and (fn-pwx-tokenp token) (natp fuel)) :verify-guards nil))
 (let* ((phase (fn-pww-phase fn-pww-carry))
        (pending (fn-pww-pending-action fn-pww-carry))
        (ledger (fn-owner-page-read-ledger fn-page-read-pool))
        (revision (fn-owner-page-read-binding-revision fn-page-read-pool)))
  (cond
   ((not (equal token (fn-pww-token fn-pww-carry)))
    (mv :stale-worker nil fuel fn-pww-carry fn-page-read-pool))
   ((member-eq phase '(:returned :cancelled-returned))
    (mv :already-returned nil fuel fn-pww-carry fn-page-read-pool))
   ((zp fuel) (mv :yield nil fuel fn-pww-carry fn-page-read-pool))
   ((member-eq phase '(:running :cancelled-running))
    (let* ((worker (list (fn-pww-id fn-pww-carry) (fn-prl-nth 1 token) phase token))
           (source (list (fn-pww-root fn-pww-carry) pending
                         (fn-pww-source-incarnation fn-pww-carry)))
           (cursor (fn-pwrt-start token worker revision (fn-prl-nth 3 ledger) source))
           (fn-pww-carry (update-fn-pww-pending-action cursor fn-pww-carry))
           (fn-pww-carry (update-fn-pww-phase :return-scanning fn-pww-carry)))
     (mv :yield nil (- fuel 1) fn-pww-carry fn-page-read-pool)))
   ((not (eq phase :return-scanning))
    ; An unresolved publication intent is not retried or settled.
    (mv :worker-fenced nil fuel fn-pww-carry fn-page-read-pool))
   ((not (and (eq (fn-prl-nth 0 pending) :window-return)
              (equal token (fn-prl-nth 1 pending))
              (equal revision (fn-prl-nth 3 pending))))
    (mv :stale-bindings nil fuel fn-pww-carry fn-page-read-pool))
   ((not (eq (fn-prl-nth 9 pending) :ready))
    (mv-let (cursor left) (fn-pwrt-run pending fuel)
     (let ((fn-pww-carry (update-fn-pww-pending-action cursor fn-pww-carry)))
      (mv :yield nil left fn-pww-carry fn-page-read-pool))))
   ((not (fn-pwrt-revision-roomp revision fn-page-read-pool))
    (mv :return-domain-unavailable nil fuel fn-pww-carry fn-page-read-pool))
   (t
    (mv-let (word worker next-ledger)
     (fn-pwrt-resolved-return ledger (fn-prl-nth 2 pending) token
                             (fn-prl-nth 8 pending) (fn-prl-nth 7 pending))
     (if (not (eq word :returned))
      (mv word nil fuel fn-pww-carry fn-page-read-pool)
      (let* ((data (fn-prp-data fn-page-read-pool))
             ; Intent first. A raw escape keeps source/cursor/proposed results
             ; and :return-publishing; consumers refuse that phase.
             (intent (list :window-return-publishing pending worker next-ledger))
             (fn-pww-carry (update-fn-pww-pending-action intent fn-pww-carry))
             (fn-pww-carry (update-fn-pww-phase :return-publishing fn-pww-carry))
             (fn-page-read-pool
              (update-fn-prp-data
               (list next-ledger (fn-prl-nth 1 data) (fn-prl-nth 2 data)
                     (fn-prl-nth 3 data) (fn-prl-nth 4 data) (+ 1 revision))
               fn-page-read-pool))
             ; Original source and all original pending aliases survive.
             (fn-pww-carry
              (update-fn-pww-pending-action
               (list :window-return-published pending worker) fn-pww-carry))
             (fn-pww-carry (update-fn-pww-phase (fn-prl-nth 2 worker) fn-pww-carry)))
       (mv :returned worker (- fuel 1) fn-pww-carry fn-page-read-pool))))))))

(defun fn-pwrt-node-step (token worker address fuel fn-pww-node fn-page-read-pool)
 (declare (xargs :stobjs (fn-pww-node fn-page-read-pool)
  :guard (and (fn-pwx-tokenp token) (natp worker) (natp address) (natp fuel))
  :measure (nfix fuel) :verify-guards nil))
 (cond
  ((zp fuel) (mv :yield nil fuel fn-pww-node fn-page-read-pool))
  ((zp address)
   (if (not (fn-pww-children-boundp 'fn-pww-carry fn-pww-node))
    (mv :worker-unavailable nil (- fuel 1) fn-pww-node fn-page-read-pool)
    (stobj-let
     ((fn-pww-carry (fn-pww-children-get 'fn-pww-carry fn-pww-node (create-fn-pww-carry))))
     (word row left fn-pww-carry fn-page-read-pool)
     (if (not (equal worker (fn-pww-id fn-pww-carry)))
      (mv :stale-worker nil (- fuel 1) fn-pww-carry fn-page-read-pool)
      (fn-pwrt-current-step token (- fuel 1) fn-pww-carry fn-page-read-pool))
     (mv word row left fn-pww-node fn-page-read-pool))))
  ((equal (mod address 2) 0)
   (if (not (fn-pww-children-boundp 'fn-pww-left fn-pww-node))
    (mv :worker-unavailable nil (- fuel 1) fn-pww-node fn-page-read-pool)
    (stobj-let
     ((fn-pww-left (fn-pww-children-get 'fn-pww-left fn-pww-node (create-fn-pww-left))))
     (word row left fn-pww-left fn-page-read-pool)
     (fn-pwrt-node-step token worker (floor address 2) (- fuel 1) fn-pww-left fn-page-read-pool)
     (mv word row left fn-pww-node fn-page-read-pool))))
  (t
   (if (not (fn-pww-children-boundp 'fn-pww-right fn-pww-node))
    (mv :worker-unavailable nil (- fuel 1) fn-pww-node fn-page-read-pool)
    (stobj-let
     ((fn-pww-right (fn-pww-children-get 'fn-pww-right fn-pww-node (create-fn-pww-right))))
     (word row left fn-pww-right fn-page-read-pool)
     (fn-pwrt-node-step token worker (floor address 2) (- fuel 1) fn-pww-right fn-page-read-pool)
     (mv word row left fn-pww-node fn-page-read-pool))))
))

; Called by the actual returned activation dispatcher under the extent lock.
; The native row is its retained assignment; all authorization/identity and
; replacement decisions come from the registered CURRENT carry and binding.
(defun fn-owner-page-window-return-step (worker token fuel fn-page-window-workers fn-page-read-pool)
 (declare (xargs :stobjs (fn-page-window-workers fn-page-read-pool)
  :guard (and (fn-pwx-rowp worker) (fn-pwx-tokenp token) (natp fuel)) :verify-guards nil))
 (stobj-let
  ((fn-pww-node (fn-pww-registry fn-page-window-workers)))
  (word row left fn-pww-node fn-page-read-pool)
  (fn-pwrt-node-step token (fn-prl-nth 0 worker) (fn-prl-nth 0 worker)
                    fuel fn-pww-node fn-page-read-pool)
  (mv word row left fn-page-window-workers fn-page-read-pool)))

; Actual CURRENT stobj boundary: under the maintained original-binding carry
; and current captured revision/root, successful publication has the COMPLETE
; original FnPWXReturn result. The carry predicate is proof-only, not served.
(defthm fn-pwrt-current-ready-refines-pwx-return
 (let* ((cursor (fn-pww-pending-action fn-pww-carry))
        (ledger (fn-owner-page-read-ledger fn-page-read-pool))
        (expected (fn-pwx-return ledger (fn-prl-nth 2 cursor) token))
        (actual (fn-pwrt-current-step token fuel fn-pww-carry fn-page-read-pool)))
  (implies
   (and (fn-pwx-tokenp token) (natp fuel) (< 0 fuel)
        (equal token (fn-pww-token fn-pww-carry))
        (eq (fn-pww-phase fn-pww-carry) :return-scanning)
        (eq (fn-prl-nth 0 cursor) :window-return)
        (equal token (fn-prl-nth 1 cursor))
        (equal (fn-owner-page-read-binding-revision fn-page-read-pool) (fn-prl-nth 3 cursor))
        (fn-pwrt-revision-roomp (fn-prl-nth 3 cursor) fn-page-read-pool)
        (fn-pwrt-carryp cursor) (eq (fn-prl-nth 9 cursor) :ready)
        (equal (fn-prl-nth 4 cursor) (fn-prl-nth 3 ledger))
        (eq (mv-nth 0 expected) :returned))
   (and (eq (mv-nth 0 actual) :returned)
        (equal (mv-nth 1 actual) (mv-nth 1 expected))
        (equal (fn-owner-page-read-ledger (mv-nth 4 actual)) (mv-nth 2 expected))
        (equal (fn-pww-phase (mv-nth 3 actual)) (fn-prl-nth 2 (mv-nth 1 expected)))
        (equal (fn-pww-root (mv-nth 3 actual)) (fn-pww-root fn-pww-carry))
        (equal (fn-pww-borrow-phase (mv-nth 3 actual)) (fn-pww-borrow-phase fn-pww-carry)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pwrt-ready-refines-complete-return
                        (cursor (fn-pww-pending-action fn-pww-carry))
                        (ledger (fn-owner-page-read-ledger fn-page-read-pool))))
                  :in-theory (e/d (fn-pwrt-current-step fn-owner-page-read-ledger
                                   fn-owner-page-read-binding-revision fn-prb-data-revision
                                   fn-prl-nth)
                                  (fn-pwrt-resolved-return fn-pwx-return fn-pwrt-carryp)))))

(verify-guards fn-pwrt-current-step)
(verify-guards fn-pwrt-node-step)
(verify-guards fn-owner-page-window-return-step
 :hints (("Goal" :in-theory (enable fn-pwx-rowp fn-prl-nth))))
