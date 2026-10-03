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

(include-book "../books/decoded-worker-backing")

; Explicit DEFAULT partial storage projection, never a complete profile price.
; The legacy publisher cannot write a modern allocation installation/DATA6.
(defun fn-owner-page-decoded-window-acquire-projected (worker descriptor fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool :guard t :verify-guards nil))
  (if (not (and (fn-owner-page-window-legacy-writablep fn-page-read-pool)
                (eq (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool)))
      (mv :unpriced-decoded-window worker nil :unpriced fn-page-read-pool)
    (mv-let (word token ledger)
      (fn-pwz-admit (fn-owner-page-read-ledger fn-page-read-pool)
                    descriptor (fn-dwb-fixed-storage-vector))
      (if (not (eq word :admitted))
          (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
            (mv word worker token (fn-dwb-coverage) fn-page-read-pool))
        (mv-let (word row ledger)
          (fn-pwx-acquire ledger worker token)
          (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
            (mv word row token (fn-dwb-coverage) fn-page-read-pool)))))))
(verify-guards fn-owner-page-decoded-window-acquire-projected)

(defun fn-owner-page-window-discovery-kind (descriptor)
  (declare (xargs :guard t))
  (cond ((fn-pwz-descriptorp descriptor) :decoded-window)
        ((fn-crw-supportedp descriptor 0) :raw-window)
        (t :legacy-entry)))
