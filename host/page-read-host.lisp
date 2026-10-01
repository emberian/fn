; Owner-serialized cold pool adapter over a dedicated ACL2 stobj.
; No new owner state-global side channel. Native callers provide identities
; and observed lifetime events; all admission/refund choices are ACL2's.
; Supported-profile/launcher installation is a separate boundary obligation.
(in-package "ACL2")
(include-book "../books/page-read-ownership")
(include-book "../books/page-discovery-ledger")
(include-book "../books/cold-read-layout")
(include-book "../books/cold-guard-bootstrap")

(include-book "../books/page-read-pool-state")
(include-book "../books/page-read-bindings-publish")

 ; A served recovery is selected explicitly before Store open. Opening an
; offline Store supplies a separate context; absence alone grants no I/O.
(defun fn-owner-page-read-enter-mode (mode fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (and (member-eq mode '(:offline :served))
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
  (cond ((equal (fn-prp-mode fn-page-read-pool) :offline) :offline)
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
  (cond
   ((equal (fn-owner-page-read-direct-mode fn-page-read-pool) :offline)
    (mv-let (word next1 id) (fn-pio-file-issue next)
      (if (equal word :issued) (mv :unfunded-offline next1 id)
        (mv word next1 id))))
   ((not (and (eq (fn-prp-mode fn-page-read-pool) :served)
              (member-eq (fn-prp-alloc-mode fn-page-read-pool) '(:active :draining))
              (fn-prp-data fn-page-read-pool)))
    (mv :read-resources-unavailable next nil))
   ; The old native counter is not shared issuer authority. Actual served
   ; startup uses the registered recovery-file source/PRS successor.
   (t (mv :recovery-file-source-unavailable next nil))))

(defun fn-owner-page-read-register (file fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :guard t :verify-guards nil))
 (mv-let (source-word source) (fn-owner-runtime-operation-source :page-read-register fn-page-read-pool state)
  (declare (ignore source))
  (if (not (eq source-word :runtime-operation-available))
   (mv source-word fn-page-read-pool)
   (let ((revision (fn-owner-page-read-binding-revision fn-page-read-pool)))
    (mv-let (word ledger) (fn-prl-register (fn-owner-page-read-ledger fn-page-read-pool) file (fn-prs-incarnation-demand (fn-prl-nth 3 (fn-prp-data fn-page-read-pool))))
     (if (not (equal word :registered)) (mv word fn-page-read-pool)
      (mv-let (publication fn-page-read-pool) (fn-owner-page-read-bindings-publish ledger revision fn-page-read-pool state)
       (mv (if (eq publication :published) word publication) fn-page-read-pool))))))))

(defun fn-owner-page-read-register-path (file path fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :guard t :verify-guards nil))
 (mv-let (source-word source) (fn-owner-runtime-operation-source :page-read-register fn-page-read-pool state)
  (declare (ignore source))
  (if (not (eq source-word :runtime-operation-available))
   (mv source-word fn-page-read-pool)
   (let ((revision (fn-owner-page-read-binding-revision fn-page-read-pool)))
    (mv-let (word ledger) (fn-prl-register (fn-owner-page-read-ledger fn-page-read-pool) file (fn-prs-incarnation-path-demand (fn-prl-nth 3 (fn-prp-data fn-page-read-pool)) path))
     (if (not (equal word :registered)) (mv word fn-page-read-pool)
      (mv-let (publication fn-page-read-pool) (fn-owner-page-read-bindings-publish ledger revision fn-page-read-pool state)
       (mv (if (eq publication :published) word publication) fn-page-read-pool))))))))

(defun fn-owner-page-read-admit (cid file eoff elen trailer fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (or (not (fn-prp-data fn-page-read-pool))
          (not (eq (fn-prp-mode fn-page-read-pool) :served))
          (fn-prb-fixed-widthp 6 (fn-prp-data fn-page-read-pool)))
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
  (if (or (not (eq (fn-prp-mode fn-page-read-pool) :served))
          (fn-prb-fixed-widthp 6 (fn-prp-data fn-page-read-pool)))
      (mv :runtime-operation-unavailable fn-page-read-pool)
    (mv-let (word ledger)
    (fn-prl-settle (fn-owner-page-read-ledger fn-page-read-pool) token cachedp)
    (if (equal word :stale) (mv word fn-page-read-pool)
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
        (mv word fn-page-read-pool))))))

(defun fn-owner-page-cache-evict (token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (or (not (eq (fn-prp-mode fn-page-read-pool) :served))
          (fn-prb-fixed-widthp 6 (fn-prp-data fn-page-read-pool)))
      (mv :runtime-operation-unavailable fn-page-read-pool)
    (mv-let (word ledger)
    (fn-prl-evict (fn-owner-page-read-ledger fn-page-read-pool) token)
    (if (equal word :stale) (mv word fn-page-read-pool)
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
        (mv word fn-page-read-pool))))))

(defun fn-owner-page-read-close (file fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (or (not (eq (fn-prp-mode fn-page-read-pool) :served))
          (fn-prb-fixed-widthp 6 (fn-prp-data fn-page-read-pool)))
      (mv :runtime-operation-unavailable fn-page-read-pool)
    (mv-let (word ledger)
    (fn-prl-close (fn-owner-page-read-ledger fn-page-read-pool) file)
    (if (equal word :stale) (mv word fn-page-read-pool)
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
        (mv word fn-page-read-pool))))))

; Unverified synchronous reads are charged before allocating any output.
; They borrow one execution slot conservatively. Native must release only
; after every derived representation has been relinquished or transferred.
(defun fn-owner-page-read-discovery-admit (file eoff elen fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (or (not (equal (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool))
          (fn-prb-fixed-widthp 6 (fn-prp-data fn-page-read-pool)))
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
  (if (or (not (eq (fn-prp-mode fn-page-read-pool) :served))
          (fn-prb-fixed-widthp 6 (fn-prp-data fn-page-read-pool)))
      (mv :runtime-operation-unavailable fn-page-read-pool)
    (mv-let (word ledger) (fn-prd-release (fn-owner-page-read-ledger fn-page-read-pool) token)
    (if (equal word :stale) (mv word fn-page-read-pool)
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
        (mv word fn-page-read-pool))))))

; Complete actual legacy registration entry refusal, before any binding scan.
(defthm fn-owner-page-read-register-source-unavailable-keeps-pool
 (equal (mv-list 2 (fn-owner-page-read-register file fn-page-read-pool state))
        (list :runtime-operation-unavailable fn-page-read-pool))
 :hints (("Goal" :in-theory (enable fn-owner-page-read-register fn-owner-runtime-operation-source))))
(defthm fn-owner-page-read-register-path-source-unavailable-keeps-pool
 (equal (mv-list 2 (fn-owner-page-read-register-path file path fn-page-read-pool state))
        (list :runtime-operation-unavailable fn-page-read-pool))
 :hints (("Goal" :in-theory (enable fn-owner-page-read-register-path fn-owner-runtime-operation-source))))
