; Actual SAME-pool account preparation preallocation boundary.
(in-package "ACL2")
(include-book "../books/admission-preallocation-resources")
(include-book "../books/page-read-pool-state")

; Named bounded dependency of the actual account preparation producer.
; A registered request/job is custody, not allocation authority. No supplied
; source/descriptor or numeric demand authorizes construction. The real
; installed family/profile/source allowance and once-only turn receipt must
; join this exact current operation before its positive arm can be supplied.
; No new ledger copy, immutable old row, or hidden pool is accepted here.
(defun fn-owner-account-preparation-admit
 (job-source work-descriptor fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :guard t)
          (ignore job-source work-descriptor))
 (mv (if (fn-apr-owner-current state)
         :admission-busy :account-preparation-allowance-unavailable)
     fn-page-read-pool state))

(defthm fn-apr-account-preparation-refusal-keeps-shared-pool
 (equal (mv-nth 1 (fn-owner-account-preparation-admit
                   job-source work-descriptor fn-page-read-pool state))
        fn-page-read-pool))
(defthm fn-apr-account-preparation-refusal-keeps-current-state
 (equal (mv-nth 2 (fn-owner-account-preparation-admit
                   job-source work-descriptor fn-page-read-pool state)) state))
(in-theory (disable fn-owner-account-preparation-admit))
