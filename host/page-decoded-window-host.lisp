; SAME-pool decoded borrow/assignment boundary. All decisions consume the
; actual live pool ledger, never a native supplied ledger snapshot.
(in-package "ACL2")
(include-book "page-window-executor-host")
(include-book "../books/decoded-worker-assignment")

(defun fn-owner-page-decoded-window-assign
    (worker token root incarnation fn-pww-carry fn-page-read-pool)
  (declare (xargs :stobjs (fn-pww-carry fn-page-read-pool) :guard t))
  (mv-let (word fn-pww-carry)
    (fn-dwa-assign (fn-owner-page-read-ledger fn-page-read-pool)
                   worker token root incarnation fn-pww-carry)
    (mv word fn-pww-carry fn-page-read-pool)))

(defun fn-owner-page-decoded-window-byte-at
    (worker token z file eoff elen poff compressed trailer decoded dict-id i
            fn-ew-buffer fn-page-read-pool)
  (declare (xargs :stobjs (fn-ew-buffer fn-page-read-pool)
                  :guard (and (true-listp z) (true-listp (nth 1 z)))))
  (fn-pwz-byte-at (fn-owner-page-read-ledger fn-page-read-pool)
                  worker token z file eoff elen poff compressed trailer
                  decoded dict-id i fn-ew-buffer))

(defun fn-owner-page-decoded-window-outcome (worker token z fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool
                  :guard (and (true-listp z) (true-listp (nth 1 z)))))
  (fn-pwz-outcome (fn-owner-page-read-ledger fn-page-read-pool) worker token z))

(include-book "../books/decoded-worker-job")

(defun fn-owner-page-decoded-job-assign (worker token root incarnation fn-decoded-job fn-page-read-pool)
  (declare (xargs :stobjs (fn-decoded-job fn-page-read-pool) :guard t :verify-guards nil))
  (mv-let (word fn-decoded-job)
    (fn-dwj-assign (fn-owner-page-read-ledger fn-page-read-pool)
                   worker token root incarnation fn-decoded-job)
    (mv word fn-decoded-job fn-page-read-pool)))

(defun fn-owner-page-decoded-job-outcome (worker token fn-decoded-job fn-page-read-pool)
  (declare (xargs :stobjs (fn-decoded-job fn-page-read-pool) :guard t :verify-guards nil))
  (fn-dwj-outcome (fn-owner-page-read-ledger fn-page-read-pool) worker token fn-decoded-job))

(defun fn-owner-page-decoded-job-byte-at
    (worker token file eoff elen poff compressed trailer decoded dict-id i fn-decoded-job fn-page-read-pool)
  (declare (xargs :stobjs (fn-decoded-job fn-page-read-pool) :guard t :verify-guards nil))
  (fn-dwj-byte-at (fn-owner-page-read-ledger fn-page-read-pool) worker token
                 file eoff elen poff compressed trailer decoded dict-id i fn-decoded-job))

(verify-guards fn-owner-page-decoded-job-assign)
(verify-guards fn-owner-page-decoded-job-outcome)
(verify-guards fn-owner-page-decoded-job-byte-at)

; A complete producer cannot be manufactured from raw-window storage prices.
; The native issuer consumes this explicit status before any decoded buffers.
(defun fn-owner-page-decoded-window-price-status (descriptor)
  (declare (xargs :guard t))
  (if (fn-pwz-descriptorp descriptor) :unpriced-decoded-window :other-window))
