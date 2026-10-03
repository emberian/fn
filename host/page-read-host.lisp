; Owner-serialized cold pool adapter over a dedicated ACL2 stobj.
; No new owner state-global side channel. Native callers provide identities
; and observed lifetime events; all admission/refund choices are ACL2's.
; Supported-profile/launcher installation is a separate boundary obligation.
(in-package "ACL2")
(include-book "../books/page-read-ownership")
(include-book "../books/page-discovery-ledger")
(include-book "../books/cold-read-layout")
(include-book "../books/cold-guard-bootstrap")
(include-book "../books/incoming-octet-holder")
(include-book "../books/incoming-buffer-carrier")
(include-book "../books/page-read-pool-state")
(include-book "../books/page-read-binding-revision")
(include-book "../books/page-read-budget-growth")

 ; A served recovery is selected explicitly before Store open. Opening an
; offline Store supplies a separate context; absence alone grants no I/O.
(defun fn-owner-page-read-enter-mode (mode fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (and (not (and (eq mode :offline)
                     (fn-prp-alloc-installation fn-page-read-pool)))
           (not (and (eq mode :served)
                     (fn-prp-alloc-installation fn-page-read-pool)
                     (not (fn-prp-data fn-page-read-pool))))
           (member-eq mode '(:offline :served))
           (or (equal (fn-prp-mode fn-page-read-pool) :uninitialized)
               (equal (fn-prp-mode fn-page-read-pool) mode)))
      (let ((fn-page-read-pool (update-fn-prp-mode mode fn-page-read-pool)))
        (mv mode fn-page-read-pool))
    (mv :invalid-resource-mode fn-page-read-pool)))

(defun fn-owner-page-read-open-context (fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (equal (fn-prp-mode fn-page-read-pool) :uninitialized)
      (fn-owner-page-read-enter-mode :offline fn-page-read-pool)
    (mv (fn-prp-mode fn-page-read-pool) fn-page-read-pool)))

(defun fn-owner-page-read-direct-mode (fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (cond ((and (equal (fn-prp-mode fn-page-read-pool) :offline)
              (null (fn-prp-alloc-installation fn-page-read-pool))) :offline)
        ((and (equal (fn-prp-mode fn-page-read-pool) :served)
              (fn-prp-data fn-page-read-pool)) :funded-pool)
        (t :read-resources-unavailable)))

; DATA = (ledger bookkeeping native-octets fd-bookkeeping file-limit).
(defun fn-owner-page-read-install (budget bookkeeping native-octets fd-bookkeeping file-limit fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (cond ((fn-prp-data fn-page-read-pool) (mv :already-installed fn-page-read-pool))
        ((equal (fn-prp-mode fn-page-read-pool) :offline) (mv :invalid-resource-mode fn-page-read-pool))
        ((not (and (fn-prs-vectorp budget) (natp bookkeeping)
                   (natp native-octets) (natp fd-bookkeeping) (posp file-limit)))
         (mv :invalid-resource-profile fn-page-read-pool))
        (t (let ((fn-page-read-pool
                  (update-fn-prp-data (list (fn-prl-make budget) bookkeeping
                                            native-octets fd-bookkeeping file-limit) fn-page-read-pool)))
             (let ((fn-page-read-pool (update-fn-prp-mode :served fn-page-read-pool)))
               (mv :installed fn-page-read-pool))))))

; Persistent executors are funded before any native thread/table allocation.
; BASELINE is never passed to per-job settlement; the job owns only a slot.
(defun fn-owner-page-read-install-baseline (budget baseline bookkeeping fd-bookkeeping file-limit fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (cond ((fn-prp-data fn-page-read-pool) (mv :already-installed fn-page-read-pool))
        ((equal (fn-prp-mode fn-page-read-pool) :offline) (mv :invalid-resource-mode fn-page-read-pool))
        ((not (and (natp bookkeeping) (natp fd-bookkeeping) (posp file-limit)))
         (mv :invalid-resource-profile fn-page-read-pool))
        (t
         (mv-let (word ledger) (fn-prl-make-baseline budget baseline)
           (if (not (equal word :installed)) (mv word fn-page-read-pool)
             (let ((fn-page-read-pool
                    (update-fn-prp-data (list ledger bookkeeping 0 fd-bookkeeping file-limit)
                                        fn-page-read-pool)))
               (let ((fn-page-read-pool (update-fn-prp-mode :served fn-page-read-pool)))
               (mv :installed fn-page-read-pool))))))))





 ; Explicit offline registration is distinct from an unfunded served start.
(defun fn-owner-page-read-registration-mode (fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (let ((mode (fn-owner-page-read-direct-mode fn-page-read-pool)))
    (if (equal mode :offline) :unfunded-offline mode)))

(defun fn-owner-page-read-close-preview (file fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (fn-prp-data fn-page-read-pool)) (fn-owner-page-read-registration-mode fn-page-read-pool)
    (fn-prl-close-preview (fn-owner-page-read-ledger fn-page-read-pool) file)))

(defun fn-owner-page-file-issue (next fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (fn-prp-data fn-page-read-pool)
      (fn-pio-file-issue-with-limit next (fn-prl-nth 4 (fn-prp-data fn-page-read-pool)))
    (if (equal (fn-owner-page-read-direct-mode fn-page-read-pool) :offline)
        (mv-let (word next1 id) (fn-pio-file-issue next)
          (if (equal word :issued) (mv :unfunded-offline next1 id)
            (mv word next1 id)))
      (mv :read-resources-unavailable next nil))))

(defun fn-owner-page-read-register (file fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (fn-prp-data fn-page-read-pool))
      (mv :read-resources-unavailable fn-page-read-pool)
    (mv-let (word ledger)
      (fn-prl-register (fn-owner-page-read-ledger fn-page-read-pool) file
                       (fn-prs-incarnation-demand (fn-prl-nth 3 (fn-prp-data fn-page-read-pool))))
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
        (mv word fn-page-read-pool)))))

; Native supplies the actual path string. ACL2 computes its target-layout
; charge; no canonical-cwd length guess or independent host calculation.
(defun fn-owner-page-read-register-path (file path fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (fn-prp-data fn-page-read-pool))
      (mv :read-resources-unavailable fn-page-read-pool)
    (mv-let (word ledger)
      (fn-prl-register (fn-owner-page-read-ledger fn-page-read-pool) file
                       (fn-prs-incarnation-path-demand
                        (fn-prl-nth 3 (fn-prp-data fn-page-read-pool)) path))
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
        (mv word fn-page-read-pool)))))

(defun fn-owner-page-read-admit (cid file eoff elen trailer fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (fn-prp-data fn-page-read-pool))
      (mv :read-resources-unavailable nil fn-page-read-pool)
    (let* ((data (fn-prp-data fn-page-read-pool))
           (native (nfix (fn-prl-nth 2 data)))
           (demand (fn-prs-worker-demand
                    elen (+ (nfix (fn-prl-nth 1 data))
                            (fn-crl-token-integer-octets
                             (fn-prl-nth 2 (fn-owner-page-read-ledger fn-page-read-pool))
                             cid file eoff elen trailer)) 0 native)))
      (mv-let (word token ledger)
        (fn-prl-admit (fn-owner-page-read-ledger fn-page-read-pool)
                      cid file eoff elen trailer demand (list native 0 0 1 0))
        (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
          (mv word token fn-page-read-pool))))))

; After private activation return/unwind or observed death + actual join.
(defun fn-owner-page-read-settle (token cachedp fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word ledger)
    (fn-prl-settle (fn-owner-page-read-ledger fn-page-read-pool) token cachedp)
    (if (equal word :stale) (mv word fn-page-read-pool)
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
        (mv word fn-page-read-pool)))))

(defun fn-owner-page-cache-evict (token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word ledger)
    (fn-prl-evict (fn-owner-page-read-ledger fn-page-read-pool) token)
    (if (equal word :stale) (mv word fn-page-read-pool)
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
        (mv word fn-page-read-pool)))))

(defun fn-owner-page-read-close (file fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word ledger)
    (fn-prl-close (fn-owner-page-read-ledger fn-page-read-pool) file)
    (if (equal word :stale) (mv word fn-page-read-pool)
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
        (mv word fn-page-read-pool)))))

; Unverified synchronous reads are charged before allocating any output.
; They borrow one execution slot conservatively. Native must release only
; after every derived representation has been relinquished or transferred.
(defun fn-owner-page-read-discovery-admit (file eoff elen fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (equal (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool))
      (mv :read-resources-unavailable nil fn-page-read-pool)
    (mv-let (word token ledger)
      (fn-prd-admit (fn-owner-page-read-ledger fn-page-read-pool) file eoff elen
                    (fn-prs-worker-demand
                     elen (+ (nfix (fn-prl-nth 1 (fn-prp-data fn-page-read-pool)))
                             (fn-crl-token-integer-octets
                              (fn-prl-nth 2 (fn-owner-page-read-ledger fn-page-read-pool))
                              0 file eoff elen 0)) 0 0))
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
        (mv word token fn-page-read-pool)))))

(defun fn-owner-page-read-discovery-release (token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word ledger) (fn-prd-release (fn-owner-page-read-ledger fn-page-read-pool) token)
    (if (equal word :stale) (mv word fn-page-read-pool)
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
        (mv word fn-page-read-pool)))))


; Actual carrier ABI: operational descriptor persists after row settlement.
(defun fn-owner-incoming-row (fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (fn-ibc-carrier-row (fn-prp-incoming-slot fn-page-read-pool)))
(defun fn-owner-incoming-backing (fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (fn-ibc-carrier-descriptor (fn-prp-incoming-slot fn-page-read-pool)))
(defun fn-owner-incoming-keep-row (row fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (equal row (fn-owner-incoming-row fn-page-read-pool)) fn-page-read-pool
    (update-fn-prp-incoming-slot
      (fn-ibc-carrier-with-row (fn-prp-incoming-slot fn-page-read-pool) row)
      fn-page-read-pool)))

; Exclusive incoming holder is part of THIS pool, not a second state-global
; ledger or a caller-supplied row. Serialize all these exports owner->pool.
(defun fn-owner-incoming-issue-current-row (demand fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word token ledger slot)
    (fn-ioh-admit (fn-owner-page-read-ledger fn-page-read-pool)
                  (fn-owner-incoming-row fn-page-read-pool) demand)
    (if (not (equal word :admitted)) (mv word nil fn-page-read-pool)
      (let* ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool))
             (fn-page-read-pool (fn-owner-incoming-keep-row slot fn-page-read-pool)))
        (mv word token fn-page-read-pool)))))
(defun fn-owner-incoming-reserve (demand fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (fn-ibc-descriptorp (fn-owner-incoming-backing fn-page-read-pool)))
      (mv :incoming-backing-unavailable nil fn-page-read-pool)
    (fn-owner-incoming-issue-current-row demand fn-page-read-pool)))
; Controlled backing install/import is separate from ordinary POST admission.
; This supplied-demand seam remains inactive until the actual constructor
; census and raw observation/lifetime boundary are attached.
(defun fn-owner-incoming-backing-reserve (demand fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (equal (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool))
      (mv :incoming-backing-unavailable nil fn-page-read-pool)
    (fn-owner-incoming-issue-current-row demand fn-page-read-pool)))
(defun fn-owner-incoming-backing-stage (token capacity retained fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word carrier)
    (fn-ibc-stage-backing (fn-owner-page-read-ledger fn-page-read-pool)
                          (fn-prp-incoming-slot fn-page-read-pool) token capacity retained)
    (if (not (equal word :backing-staged)) (mv word fn-page-read-pool)
      (let ((fn-page-read-pool (update-fn-prp-incoming-slot carrier fn-page-read-pool)))
        (mv word fn-page-read-pool)))))
(defun fn-owner-incoming-backing-publish (token outcome fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word ledger carrier)
    (fn-ibc-publish-backing (fn-owner-page-read-ledger fn-page-read-pool)
                           (fn-prp-incoming-slot fn-page-read-pool) token outcome)
    (if (not (member-eq word '(:backing-installed :backing-held))) (mv word fn-page-read-pool)
      (let* ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool))
             (fn-page-read-pool (update-fn-prp-incoming-slot carrier fn-page-read-pool)))
        (mv word fn-page-read-pool)))))
(defun fn-owner-incoming-mutation-allowedp (token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (let ((row (fn-owner-incoming-row fn-page-read-pool)))
    (if (and (member-eq (fn-ioh-access row token :mutate) '(:unheld :holder-setup))
             (not (fn-prl-nth 3 row))) t nil)))
(defun fn-owner-incoming-setup-begin (token total limits fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (let ((row (fn-owner-incoming-row fn-page-read-pool))
        (descriptor (fn-owner-incoming-backing fn-page-read-pool)))
    (if (not (and (fn-ibc-descriptorp descriptor) (fn-ioh-matches row token)
                  (equal (fn-prl-nth 1 row) :setup) (not (fn-prl-nth 3 row))))
        (mv :setup-unavailable fn-page-read-pool)
      (mv-let (word plan) (fn-isr-begin token total (fn-prl-nth 2 descriptor) limits)
        (if (not (equal word :setup-started)) (mv word fn-page-read-pool)
          (let ((fn-page-read-pool
                  (fn-owner-incoming-keep-row
                    (fn-ibc-row-with-job row (list :incoming-setup plan)) fn-page-read-pool)))
            (mv word fn-page-read-pool)))))))
(defun fn-owner-incoming-setup-next (token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (let* ((row (fn-owner-incoming-row fn-page-read-pool)) (job (fn-prl-nth 3 row)))
    (if (not (and (fn-ioh-matches row token) (equal (fn-prl-nth 1 row) :setup)
                  (equal (fn-prl-nth 0 job) :incoming-setup)
                  (fn-ioh-tokenp (fn-prl-nth 0 (fn-prl-nth 1 job)))
                  (equal (fn-prl-nth 0 (fn-prl-nth 1 job)) token)))
        (mv :setup-unavailable nil fn-page-read-pool)
      (mv-let (word grant plan) (fn-isr-next (fn-prl-nth 1 job))
        (if (equal plan (fn-prl-nth 1 job)) (mv word grant fn-page-read-pool)
          (let ((fn-page-read-pool
                  (fn-owner-incoming-keep-row
                    (fn-ibc-row-with-job row (list :incoming-setup plan)) fn-page-read-pool)))
            (mv word grant fn-page-read-pool)))))))
(defun fn-owner-incoming-setup-ack (token grant outcome fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (let* ((row (fn-owner-incoming-row fn-page-read-pool)) (job (fn-prl-nth 3 row)))
    (if (not (and (fn-ioh-matches row token) (equal (fn-prl-nth 1 row) :setup)
                  (equal (fn-prl-nth 0 job) :incoming-setup)
                  (fn-ioh-tokenp (fn-prl-nth 0 (fn-prl-nth 1 job)))
                  (equal (fn-prl-nth 0 (fn-prl-nth 1 job)) token)))
        (mv :setup-unavailable fn-page-read-pool)
      (mv-let (word plan) (fn-isr-ack (fn-prl-nth 1 job) grant outcome)
        (if (not (member-eq word '(:copy-recorded :copy-cancelled))) (mv word fn-page-read-pool)
          (let ((fn-page-read-pool
                  (fn-owner-incoming-keep-row
                    (list token (if (equal word :copy-cancelled) :cancelled :setup)
                          (fn-prl-nth 2 row) (list :incoming-setup plan)) fn-page-read-pool)))
            (mv word fn-page-read-pool)))))))
(defun fn-owner-incoming-seal (token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (let* ((row (fn-owner-incoming-row fn-page-read-pool)) (job (fn-prl-nth 3 row))
         (plan (fn-prl-nth 1 job)))
    (if (not (and (equal (fn-prl-nth 0 job) :incoming-setup)
                  (fn-isr-planp plan) (equal (fn-prl-nth 0 plan) token)
                  (fn-isr-sealablep plan)))
        (mv :setup-incomplete fn-page-read-pool)
      (mv-let (word slot) (fn-ioh-seal row token)
        (if (not (equal word :sealed)) (mv word fn-page-read-pool)
          (let ((fn-page-read-pool (fn-owner-incoming-keep-row slot fn-page-read-pool)))
            (mv word fn-page-read-pool)))))))
(defun fn-owner-incoming-cancel (token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word slot) (fn-ioh-cancel (fn-owner-incoming-row fn-page-read-pool) token)
    (if (not (equal word :cancelled)) (mv word fn-page-read-pool)
      (let ((fn-page-read-pool (fn-owner-incoming-keep-row slot fn-page-read-pool)))
        (mv word fn-page-read-pool)))))
(defun fn-owner-incoming-release (token joined aliases-clear fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word ledger slot)
    (fn-ioh-release (fn-owner-page-read-ledger fn-page-read-pool)
                    (fn-owner-incoming-row fn-page-read-pool) token joined aliases-clear)
    (if (not (equal word :released)) (mv word fn-page-read-pool)
      (let* ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool))
             (fn-page-read-pool (fn-owner-incoming-keep-row slot fn-page-read-pool)))
        (mv word fn-page-read-pool)))))

(defthm fn-owner-incoming-live-readonly-forbids-actual-mutation
  (implies (member-equal (fn-prl-nth 1 (fn-owner-incoming-row fn-page-read-pool))
                         '(:readonly :cancelled))
           (not (fn-owner-incoming-mutation-allowedp token fn-page-read-pool)))
  :hints (("Goal" :cases ((fn-owner-incoming-row fn-page-read-pool))
           :in-theory (enable fn-owner-incoming-mutation-allowedp))))

(defthm fn-owner-incoming-refused-release-keeps-pool
  (implies (not (equal (mv-nth 0 (fn-owner-incoming-release
                                  token joined aliases-clear fn-page-read-pool))
                       :released))
           (equal (mv-nth 1 (fn-owner-incoming-release
                              token joined aliases-clear fn-page-read-pool))
                  fn-page-read-pool))
  :hints (("Goal" :in-theory (enable fn-owner-incoming-release))))

(defthm fn-owner-incoming-release-retains-operational-backing
  (equal (fn-owner-incoming-backing
           (mv-nth 1 (fn-owner-incoming-release token joined aliases-clear fn-page-read-pool)))
         (fn-owner-incoming-backing fn-page-read-pool))
  :hints (("Goal" :in-theory (enable fn-owner-incoming-release
                                    fn-owner-incoming-backing fn-owner-incoming-keep-row
                                    fn-owner-page-read-keep-ledger
                                    fn-ibc-carrier-with-row fn-ibc-carrier-descriptor
                                    fn-ibc-carrier fn-prl-nth))))
(defthm fn-owner-incoming-actual-seal-requires-completed-setup
  (implies (equal (mv-nth 0 (fn-owner-incoming-seal token fn-page-read-pool)) :sealed)
           (let* ((job (fn-prl-nth 3 (fn-owner-incoming-row fn-page-read-pool)))
                  (plan (fn-prl-nth 1 job)))
             (and (fn-isr-planp plan)
                  (equal (fn-prl-nth 4 plan) (fn-prl-nth 1 plan))
                  (not (fn-prl-nth 5 plan)))))
  :hints (("Goal" :use ((:instance fn-isr-sealable-plan-is-completely-copied
                         (plan (fn-prl-nth 1 (fn-prl-nth 3
                                  (fn-owner-incoming-row fn-page-read-pool))))))
           :in-theory (e/d (fn-owner-incoming-seal)
                           (fn-isr-planp fn-isr-sealablep fn-owner-incoming-row)))))
(defthm fn-owner-incoming-copy-grant-within-captured-bounds
  (let* ((row (fn-owner-incoming-row fn-page-read-pool))
         (plan (fn-prl-nth 1 (fn-prl-nth 3 row)))
         (result (fn-owner-incoming-setup-next token fn-page-read-pool)))
    (implies (and (fn-isr-planp plan) (equal (mv-nth 0 result) :copy))
             (let ((grant (mv-nth 1 result)))
               (and (fn-isr-grantp grant)
                    (equal (fn-prl-nth 1 grant) token)
                    (<= (fn-prl-nth 3 grant) *fn-cbud-read-quantum*)
                    (<= (+ (fn-prl-nth 2 grant) (fn-prl-nth 3 grant))
                        (fn-prl-nth 1 plan))))))
  :hints (("Goal" :use ((:instance fn-isr-every-issued-range-within-captured-bounds
                         (plan (fn-prl-nth 1 (fn-prl-nth 3
                                  (fn-owner-incoming-row fn-page-read-pool))))))
           :in-theory (e/d (fn-owner-incoming-setup-next)
                           (fn-isr-planp fn-isr-grantp fn-isr-next
                            fn-owner-incoming-row fn-ioh-matches)))))

; Selected PRF-1143 fixed controller seam. The row binds the controller once;
; successful copy ticks update only fixed controller fields, not row/plan lists.
(include-book "../books/incoming-copy-stobj")
(defun fn-owner-incoming-copy-associatedp (token fn-input-copy fn-page-read-pool)
  (declare (xargs :stobjs (fn-input-copy fn-page-read-pool)))
  (let* ((row (fn-owner-incoming-row fn-page-read-pool))
         (job (fn-prl-nth 3 row)))
    (and (fn-ioh-matches row token)
         (equal (fn-input-copy-token fn-input-copy) token)
         (consp job) (equal (car job) :incoming-controller)
         (consp (cdr job)) (equal (cadr job) token) (null (cddr job)))))
(defun fn-owner-incoming-copy-start (token total limits fn-input-copy fn-page-read-pool)
  (declare (xargs :stobjs (fn-input-copy fn-page-read-pool)))
  (let ((row (fn-owner-incoming-row fn-page-read-pool))
        (descriptor (fn-owner-incoming-backing fn-page-read-pool)))
    (if (not (and (fn-ibc-descriptorp descriptor) (fn-ioh-matches row token)
                  (equal (fn-prl-nth 1 row) :setup) (not (fn-prl-nth 3 row))))
        (mv :setup-unavailable fn-input-copy fn-page-read-pool)
      (mv-let (word fn-input-copy)
        (fn-input-copy-open token total (fn-prl-nth 2 descriptor)
                            (fn-cbud-step-read-octets limits) fn-input-copy)
        (if (not (equal word :setup-started))
            (mv word fn-input-copy fn-page-read-pool)
          (let ((fn-page-read-pool
                  (fn-owner-incoming-keep-row
                    (fn-ibc-row-with-job row (list :incoming-controller token))
                    fn-page-read-pool)))
            (mv word fn-input-copy fn-page-read-pool)))))))
(defun fn-owner-incoming-copy-next (token fn-input-copy fn-page-read-pool)
  (declare (xargs :stobjs (fn-input-copy fn-page-read-pool)))
  (if (not (and (fn-owner-incoming-copy-associatedp token fn-input-copy fn-page-read-pool)
                (member-eq (fn-prl-nth 1 (fn-owner-incoming-row fn-page-read-pool))
                           '(:setup :readonly))))
      (mv :setup-unavailable 0 0 0 fn-input-copy fn-page-read-pool)
    (mv-let (word start count end fn-input-copy)
      (fn-input-copy-next token fn-input-copy)
      (if (and (equal word :complete)
               (equal (fn-prl-nth 1 (fn-owner-incoming-row fn-page-read-pool)) :setup))
          (mv-let (sealed row)
            (fn-ioh-seal (fn-owner-incoming-row fn-page-read-pool) token)
            (declare (ignore sealed))
            (let ((fn-page-read-pool (fn-owner-incoming-keep-row row fn-page-read-pool)))
              (mv word start count end fn-input-copy fn-page-read-pool)))
        (mv word start count end fn-input-copy fn-page-read-pool)))))
(defun fn-owner-incoming-copy-ack (token start count end outcome fn-input-copy fn-page-read-pool)
  (declare (xargs :stobjs (fn-input-copy fn-page-read-pool)))
  (if (not (and (fn-owner-incoming-copy-associatedp token fn-input-copy fn-page-read-pool)
                (equal (fn-prl-nth 1 (fn-owner-incoming-row fn-page-read-pool)) :setup)))
      (mv :stale-copy fn-input-copy fn-page-read-pool)
    (mv-let (word fn-input-copy)
      (fn-input-copy-ack token start count end outcome fn-input-copy)
      (if (equal word :copy-cancelled)
          (mv-let (cancelled fn-page-read-pool)
            (fn-owner-incoming-cancel token fn-page-read-pool)
            (declare (ignore cancelled))
            (mv word fn-input-copy fn-page-read-pool))
        (mv word fn-input-copy fn-page-read-pool)))))
(defun fn-owner-incoming-copy-stop (token joined aliases-clear fn-input-copy fn-page-read-pool)
  (declare (xargs :stobjs (fn-input-copy fn-page-read-pool)))
  (if (not (fn-owner-incoming-copy-associatedp token fn-input-copy fn-page-read-pool))
      (mv :incoming-held fn-input-copy fn-page-read-pool)
    (mv-let (word fn-page-read-pool)
      (fn-owner-incoming-release token joined aliases-clear fn-page-read-pool)
      (if (not (equal word :released))
          (mv word fn-input-copy fn-page-read-pool)
        (mv-let (closed fn-input-copy)
          (fn-input-copy-close token joined aliases-clear fn-input-copy)
          (declare (ignore closed))
          (mv word fn-input-copy fn-page-read-pool))))))

; Complete result/effect boundary for the actual fixed next callback. The
; reference is the abstract controller export, already connected to its fixed
; implementation by FN-INPUT-COPY-NEXT{CORRESPONDENCE}.
(defthm fn-owner-incoming-copy-next-controller-and-pool-boundary-by-definition
 (let* ((associated (and (fn-owner-incoming-copy-associatedp token fn-input-copy fn-page-read-pool)
                         (member-eq (fn-prl-nth 1 (fn-owner-incoming-row fn-page-read-pool))
                                    '(:setup :readonly))))
        (result (fn-owner-incoming-copy-next token fn-input-copy fn-page-read-pool))
        (reference (fn-input-copy-next token fn-input-copy)))
  (and (equal (mv-nth 0 result) (if associated (mv-nth 0 reference) :setup-unavailable))
       (equal (mv-nth 1 result) (if associated (mv-nth 1 reference) 0))
       (equal (mv-nth 2 result) (if associated (mv-nth 2 reference) 0))
       (equal (mv-nth 3 result) (if associated (mv-nth 3 reference) 0))
       (equal (mv-nth 4 result) (if associated (mv-nth 4 reference) fn-input-copy))
       (equal (mv-nth 5 result)
              (if (and associated (equal (mv-nth 0 reference) :complete)
                       (equal (fn-prl-nth 1 (fn-owner-incoming-row fn-page-read-pool)) :setup))
                  (fn-owner-incoming-keep-row
                    (mv-nth 1 (fn-ioh-seal (fn-owner-incoming-row fn-page-read-pool) token))
                    fn-page-read-pool)
                fn-page-read-pool))))
 :hints (("Goal" :in-theory (enable fn-owner-incoming-copy-next))))


(include-book "../books/page-read-startup")

; DEFAULT allowance is distinct from DATA6 binding revision and complete allocation installation.
; Bits start clear; actual native startup confirms each constructor/reserve
; before publishing that physical slot to the reusable free roster.
(defun fn-owner-page-read-install-default (plan fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard t))
 (if (not (fn-prstartup-planp plan)) (mv :invalid-default-pool-plan fn-page-read-pool)
  (mv-let (word fn-page-read-pool)
   (fn-owner-page-read-install-baseline
     (fn-prstartup-nth 1 plan) (fn-prstartup-nth 2 plan)
     (fn-prstartup-nth 3 plan) (fn-prstartup-nth 4 plan)
     (fn-prstartup-nth 5 plan) fn-page-read-pool)
   (if (not (eq word :installed)) (mv word fn-page-read-pool)
    (let ((fn-page-read-pool
      (update-fn-prp-data
        (list (fn-prl-nth 0 (fn-prp-data fn-page-read-pool))
              (fn-prl-nth 1 (fn-prp-data fn-page-read-pool))
              (fn-prl-nth 2 (fn-prp-data fn-page-read-pool))
              (fn-prl-nth 3 (fn-prp-data fn-page-read-pool))
              (fn-prl-nth 4 (fn-prp-data fn-page-read-pool))
              0 (list :default-reusable-decoded 0) (fn-prstartup-nth 6 plan)) fn-page-read-pool)))
      (mv :installed fn-page-read-pool))))))

(defun fn-owner-page-read-default-worker-reservedp (slot fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard t))
 (let* ((data (fn-prp-data fn-page-read-pool))
        (marker (fn-prl-nth 6 data)) (count (fn-prl-nth 7 data)))
  (and (eq (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool)
       (true-listp data) (equal (len data) 8)
       (true-listp marker) (equal (len marker) 2)
       (eq (fn-prl-nth 0 marker) :default-reusable-decoded)
       (natp (fn-prl-nth 1 marker)) (posp count)
       (natp slot) (< slot count))))

(defun fn-owner-page-read-default-worker-ready (slot fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard t))
 (let* ((data (fn-prp-data fn-page-read-pool))
        (marker (fn-prl-nth 6 data))
        (mask (fn-prl-nth 1 marker)))
  (if (not (fn-owner-page-read-default-worker-reservedp slot fn-page-read-pool))
      (mv :default-worker-not-reserved fn-page-read-pool)
    (if (logbitp slot mask) (mv :already-ready fn-page-read-pool)
      (let ((fn-page-read-pool
        (update-fn-prp-data
          (update-nth 6 (list :default-reusable-decoded (logior mask (ash 1 slot))) data)
           fn-page-read-pool)))
       (mv :ready fn-page-read-pool))))))

(defun fn-owner-page-read-default-worker-readyp (worker fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard t))
 (let* ((data (fn-prp-data fn-page-read-pool))
        (marker (fn-prl-nth 6 data))
        (mask (fn-prl-nth 1 marker)) (slot (fn-prl-nth 0 worker)))
  (and (eq (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool)
       (fn-owner-page-read-default-worker-reservedp slot fn-page-read-pool)
       (natp mask) (logbitp slot mask))))

(defun fn-owner-page-read-default-installedp (fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard t))
 (fn-owner-page-read-default-worker-reservedp 0 fn-page-read-pool))

; A reservation is not permission to recreate already initialized backing.
(defun fn-owner-page-read-default-worker-constructionp (slot fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard t))
 (and (fn-owner-page-read-default-worker-reservedp slot fn-page-read-pool)
      (not (logbitp slot
             (fn-prl-nth 1 (fn-prl-nth 6 (fn-prp-data fn-page-read-pool)))))))

; Actual live limit publication holds owner->extent through preview and apply.
; Permanent backing, outstanding rows and readiness metadata are untouched.
(defun fn-owner-page-read-protected-growth-preview (amount fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard t))
 (if (not (fn-owner-page-read-default-installedp fn-page-read-pool)) :at-restart
   (mv-let (word ledger)
    (fn-prl-resident-shrink amount (fn-owner-page-read-ledger fn-page-read-pool))
    (declare (ignore ledger))
    (if (eq word :protected-growth-admitted) :affordable :at-restart))))
(defun fn-owner-page-read-protected-growth (amount fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard t))
 (if (not (fn-owner-page-read-default-installedp fn-page-read-pool))
     (mv :at-restart fn-page-read-pool)
   (mv-let (word ledger)
    (fn-prl-resident-shrink amount (fn-owner-page-read-ledger fn-page-read-pool))
    (if (not (eq word :protected-growth-admitted)) (mv :at-restart fn-page-read-pool)
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
       (mv word fn-page-read-pool))))))
