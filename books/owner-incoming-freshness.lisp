; Actual STATE authority collector. Public request never supplies saved fields.
; Caller holds the owner exclusion and has prepaid capture/phase-write suffix.
; Query attachment and complete allocating operation installation remain separate.
(in-package "ACL2")
(include-book "incoming-authority-freshness")
(include-book "owner-incoming-context")
(include-book "owner-canonical-read-state")
(include-book "owner-config-state")
(include-book "consumer-account-state")
(include-book "store-node-files-selector")
(include-book "store-files")

(defun fn-owner-incoming-freshness-state (state)
 (declare (xargs :stobjs state :guard t))
 (and (boundp-global 'fn-owner-incoming-freshness state)
      (f-get-global 'fn-owner-incoming-freshness state)))

; Six returned values are borrowed references/scalars, not a newly allocated
; argument tuple. COUNT is actual Store count, never the account fence count.
(defun fn-owner-incoming-authority-current (fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :guard (boundp-global 'fn-owner state)))
 (let* ((context (fn-owner-incoming-context-read fn-page-read-pool state))
        (epoch (fn-owner-canonical-epoch state))
        (generation (fn-cfg-generation (fn-owner-config state)))
        (count (fn-sf-records-count (fn-sn-files (fn-owner-store state))))
        (canonical (fn-owner-canonical-state state))
        (publication (fn-owner-account-root-state state)))
  (mv (if (and context (fn-owner-canonical-availablep count state)
               (fn-iaf-octets= 32 (fn-cp-nth 1 (fn-cp-nth 9 context))
                                  (fn-cp-nth 1 (fn-cp-nth 9 context))))
          (fn-iaf-authority-status epoch generation count canonical publication)
        :authority-unavailable)
      context epoch generation canonical publication)))

(defun fn-owner-incoming-authority-capture (fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :guard (boundp-global 'fn-owner state)))
 (if (fn-owner-incoming-freshness-state state)
     (mv :freshness-pending fn-page-read-pool state)
  (mv-let (word context epoch generation canonical publication)
   (fn-owner-incoming-authority-current fn-page-read-pool state)
   (if (not (eq word :authority-available)) (mv word fn-page-read-pool state)
    (let* ((authority (fn-cp-nth 6 (fn-cp-nth 5 canonical)))
           (saved (list :incoming-freshness :awaiting-query
                    (fn-cp-nth 1 context) epoch (fn-cp-nth 1 (fn-cp-nth 9 context))
                    generation (fn-cp-nth 3 authority) (fn-cp-nth 1 authority)
                    (fn-cp-nth 4 publication) (fn-cp-nth 5 publication) context nil))
           (state (f-put-global 'fn-owner-incoming-freshness saved state)))
     (mv :authority-captured fn-page-read-pool state))))))

(defun fn-owner-incoming-authority-recheck (fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :guard (boundp-global 'fn-owner state) :verify-guards nil))
 (let ((saved (fn-owner-incoming-freshness-state state)))
  (cond ((not (eq (fn-cp-nth 0 saved) :incoming-freshness))
         (mv :freshness-unavailable fn-page-read-pool state))
        ((eq (fn-cp-nth 1 saved) :stale-recapture)
         (mv :recapture-required fn-page-read-pool state))
        (t
         (mv-let (word context epoch generation canonical publication)
          (fn-owner-incoming-authority-current fn-page-read-pool state)
          (if (not (eq word :authority-available)) (mv word fn-page-read-pool state)
           (let* ((word (fn-iaf-compare-current saved (fn-cp-nth 1 context) epoch
                          (fn-cp-nth 1 (fn-cp-nth 9 context)) generation canonical publication))
                  (state (if (eq word :recapture-required)
                             (f-put-global 'fn-owner-incoming-freshness
                                           (cons (fn-ag-car saved)
                                             (cons :stale-recapture (fn-ag-cdr (fn-ag-cdr saved)))) state)
                           state)))
            (mv word fn-page-read-pool state))))))))

(verify-guards fn-owner-incoming-authority-recheck
 :hints (("Goal" :in-theory (disable fn-owner-incoming-authority-current
                                   fn-owner-incoming-freshness-state fn-iaf-compare-current))))

; No admission, refund, new frontier or input release occurs in either branch.
(defthm fn-owner-incoming-authority-capture-preserves-pool
 (equal (mv-nth 1 (fn-owner-incoming-authority-capture fn-page-read-pool state))
        fn-page-read-pool)
 :rule-classes nil
 :hints (("Goal" :in-theory (disable fn-owner-incoming-authority-current))))
(defthm fn-owner-incoming-authority-recheck-preserves-pool
 (equal (mv-nth 1 (fn-owner-incoming-authority-recheck fn-page-read-pool state))
        fn-page-read-pool)
 :rule-classes nil
 :hints (("Goal" :in-theory (disable fn-owner-incoming-authority-current fn-iaf-compare-current))))

(defthm fn-owner-incoming-recapture-retains-original-roots
 (equal (cddr (fn-owner-incoming-freshness-state
                (mv-nth 2 (fn-owner-incoming-authority-recheck fn-page-read-pool state))))
        (cddr (fn-owner-incoming-freshness-state state)))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-owner-incoming-freshness-state)
       (fn-owner-incoming-authority-current fn-iaf-compare-current fn-cp-nth)))))

(defthm fn-owner-incoming-recheck-current-matches-live-authority
 (implies
  (equal (mv-nth 0 (fn-owner-incoming-authority-recheck fn-page-read-pool state))
         :authority-current)
  (let ((saved (fn-owner-incoming-freshness-state state))
        (authority (fn-cp-nth 6 (fn-cp-nth 5 (fn-owner-canonical-state state)))))
   (and (equal (fn-cp-nth 5 saved) (fn-cfg-generation (fn-owner-config state)))
        (equal (fn-cp-nth 7 saved) (fn-cp-nth 1 authority))
        (fn-cra-availablep (fn-cp-nth 5 (fn-owner-canonical-state state))
          (fn-owner-canonical-epoch state)
          (fn-sf-records-count (fn-sn-files (fn-owner-store state)))
          (fn-owner-account-root-state state)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-owner-incoming-authority-current fn-iaf-compare-current fn-iaf-authority-status)
       (fn-owner-incoming-freshness-state fn-owner-incoming-context-read
        fn-owner-canonical-state fn-owner-canonical-epoch fn-owner-canonical-availablep
        fn-owner-account-root-state fn-owner-config fn-owner-store fn-cfg-generation
        fn-sf-records-count fn-sn-files fn-cp-nth fn-cra-availablep
        fn-iaf-holder= fn-iaf-octets=)))))
