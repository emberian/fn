; Owner-serialized cold pool adapter over a dedicated ACL2 stobj.
; No new owner state-global side channel. Native callers provide identities
; and observed lifetime events; all admission/refund choices are ACL2's.
; Supported-profile/launcher installation is a separate boundary obligation.
(in-package "ACL2")
(include-book "../books/page-read-ledger")

(defstobj fn-page-read-pool
  (fn-prp-data :initially nil)
  :inline t)

; DATA = (ledger bookkeeping native-octets fd-bookkeeping).
(defun fn-owner-page-read-install (budget bookkeeping native-octets fd-bookkeeping fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (cond ((fn-prp-data fn-page-read-pool) (mv :already-installed fn-page-read-pool))
        ((not (and (fn-prs-vectorp budget) (natp bookkeeping)
                   (natp native-octets) (natp fd-bookkeeping)))
         (mv :invalid-resource-profile fn-page-read-pool))
        (t (let ((fn-page-read-pool
                  (update-fn-prp-data (list (fn-prl-make budget) bookkeeping
                                            native-octets fd-bookkeeping) fn-page-read-pool)))
             (mv :installed fn-page-read-pool)))))

(defun fn-owner-page-read-ledger (fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (fn-prl-nth 0 (fn-prp-data fn-page-read-pool)))

(defun fn-owner-page-read-keep-ledger (ledger fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (let ((data (fn-prp-data fn-page-read-pool)))
    (update-fn-prp-data (list ledger (fn-prl-nth 1 data) (fn-prl-nth 2 data)
                              (fn-prl-nth 3 data)) fn-page-read-pool)))

; A missing pool is explicitly the old offline/unfunded registration mode.
; It admits no served read and proves no descriptor capacity. Supported pool
; install must precede recovery before a funded served claim is made.
(defun fn-owner-page-read-registration-mode (fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (fn-prp-data fn-page-read-pool) :funded-pool :unfunded-offline))

(defun fn-owner-page-read-close-preview (file fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (fn-prp-data fn-page-read-pool)) :unfunded-offline
    (fn-prl-close-preview (fn-owner-page-read-ledger fn-page-read-pool) file)))

(defun fn-owner-page-read-register (file fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (fn-prp-data fn-page-read-pool))
      (mv :read-resources-unavailable fn-page-read-pool)
    (mv-let (word ledger)
      (fn-prl-register (fn-owner-page-read-ledger fn-page-read-pool) file
                       (fn-prs-incarnation-demand (fn-prl-nth 3 (fn-prp-data fn-page-read-pool))))
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
        (mv word fn-page-read-pool)))))

(defun fn-owner-page-read-admit (cid file eoff elen trailer fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (fn-prp-data fn-page-read-pool))
      (mv :read-resources-unavailable nil fn-page-read-pool)
    (let* ((data (fn-prp-data fn-page-read-pool))
           (native (nfix (fn-prl-nth 2 data)))
           (demand (fn-prs-worker-demand elen (fn-prl-nth 1 data) 0 native)))
      (mv-let (word token ledger)
        (fn-prl-admit (fn-owner-page-read-ledger fn-page-read-pool)
                      cid file eoff elen trailer demand (list native 0 0 1 0))
        (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
          (mv word token fn-page-read-pool))))))

; Only after thread-dead observation + join. Cached bytes stay charged.
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
