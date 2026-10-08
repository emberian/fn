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
(include-book "../books/decoded-window-span")

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

(definterface fn-owner-page-decoded-job-assign :class :common-lisp-compliant)
(verify-guards fn-owner-page-decoded-job-outcome)

(definterface fn-owner-page-decoded-job-outcome :class :common-lisp-compliant)
(verify-guards fn-owner-page-decoded-job-byte-at)

(definterface fn-owner-page-decoded-job-byte-at :class :common-lisp-compliant)

; The span borrow of a decoded job's window (books/decoded-window-span.lisp).
(defun fn-owner-page-decoded-job-span-at
    (worker token file eoff elen poff compressed trailer decoded dict-id i j
            fn-decoded-job fn-ew-span fn-page-read-pool)
  (declare (xargs :stobjs (fn-decoded-job fn-ew-span fn-page-read-pool)
                  :guard (and (natp i) (natp j) (< i j)) :verify-guards nil))
  (fn-dwj-span-at (fn-owner-page-read-ledger fn-page-read-pool) worker token
                  file eoff elen poff compressed trailer decoded dict-id i j
                  fn-decoded-job fn-ew-span))

(verify-guards fn-owner-page-decoded-job-span-at)

(definterface fn-owner-page-decoded-job-span-at :class :common-lisp-compliant
  :kinds ((i natp) (j natp))
  :keystones ((fn-pwz-span-at-is-the-borrowed-bytes :via fn-pwz-span-at)
              (fn-pwz-span-at-answers-when-its-ends-do :via fn-pwz-span-at)))

; KEYSTONE (a decoded span is the job's scalar borrows), at the owner row.
(defthm fn-owner-page-decoded-job-span-at-is-the-scalar-borrows
  (implies (and (natp i) (natp j) (< i j) (natp k) (< k (- j i))
                (equal (mv-nth 0 (fn-owner-page-decoded-job-span-at
                                  worker token file eoff elen poff compressed trailer decoded
                                  dict-id i j fn-decoded-job fn-ew-span fn-page-read-pool))
                       :span))
           (and (equal (mv-nth 0 (fn-owner-page-decoded-job-byte-at
                                  worker token file eoff elen poff compressed trailer decoded
                                  dict-id (+ i k) fn-decoded-job fn-page-read-pool))
                       :byte)
                (equal (nth k (nth 0 (mv-nth 1 (fn-owner-page-decoded-job-span-at
                                                worker token file eoff elen poff compressed trailer
                                                decoded dict-id i j fn-decoded-job fn-ew-span
                                                fn-page-read-pool))))
                       (mv-nth 1 (fn-owner-page-decoded-job-byte-at
                                  worker token file eoff elen poff compressed trailer decoded
                                  dict-id (+ i k) fn-decoded-job fn-page-read-pool)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-owner-page-decoded-job-span-at
                                     fn-owner-page-decoded-job-byte-at)
           :use (:instance fn-dwj-span-at-is-the-borrowed-bytes
                           (ledger (fn-owner-page-read-ledger fn-page-read-pool))))))

; A complete producer cannot be manufactured from raw-window storage prices.
; The native issuer consumes this explicit status before any decoded buffers.
(defun fn-owner-page-decoded-window-price-status (descriptor)
  (declare (xargs :guard t))
  (if (fn-pwz-descriptorp descriptor) :unpriced-decoded-window :other-window))

(definterface fn-owner-page-decoded-window-price-status :class :common-lisp-compliant)

(include-book "../books/decoded-worker-backing")

; Explicit DEFAULT partial storage projection, never a complete profile price.
; The legacy publisher cannot write a modern allocation installation/DATA6.
(defun fn-owner-page-decoded-window-acquire-projected (worker descriptor fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool :guard t :verify-guards nil))
  (if (not (and (fn-owner-page-window-legacy-writablep fn-page-read-pool)
                (eq (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool)))
      (mv :unpriced-decoded-window worker nil :unpriced fn-page-read-pool)
    (if (and (fn-owner-page-read-default-installedp fn-page-read-pool)
             (not (fn-owner-page-read-default-worker-readyp worker fn-page-read-pool)))
        (mv :default-worker-not-ready worker nil (fn-dwb-coverage) fn-page-read-pool)
    (mv-let (word token ledger)
      (fn-pwz-admit (fn-owner-page-read-ledger fn-page-read-pool)
                    descriptor (if (fn-owner-page-read-default-worker-readyp worker fn-page-read-pool)
                                 (fn-dwb-reused-window-vector) (fn-dwb-fixed-storage-vector)))
      (if (not (eq word :admitted))
          (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
            (mv word worker token (fn-dwb-coverage) fn-page-read-pool))
        (mv-let (word row ledger)
          (fn-pwx-acquire ledger worker token)
          (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
            (mv word row token (fn-dwb-coverage) fn-page-read-pool))))))))
(verify-guards fn-owner-page-decoded-window-acquire-projected)

(definterface fn-owner-page-decoded-window-acquire-projected :class :common-lisp-compliant)

(defun fn-owner-page-window-discovery-kind (descriptor)
  (declare (xargs :guard t))
  (cond ((fn-pwz-descriptorp descriptor) :decoded-window)
        ((fn-crw-supportedp descriptor 0) :raw-window)
        (t :legacy-entry)))

(definterface fn-owner-page-window-discovery-kind :class :common-lisp-compliant)

; The live SAME pool supplies retirement authority. Native E excludes scalar
; borrowers across this call and the subsequent token settlement.
(defun fn-owner-page-decoded-job-retire (worker token fn-decoded-job fn-page-read-pool)
  (declare (xargs :stobjs (fn-decoded-job fn-page-read-pool) :guard t))
  (mv-let (word fn-decoded-job)
    (fn-dwj-retire (fn-owner-page-read-ledger fn-page-read-pool)
                   worker token fn-decoded-job)
    (mv word fn-decoded-job fn-page-read-pool)))

(definterface fn-owner-page-decoded-job-retire :class :common-lisp-compliant)

; The verified-window cache for a decoded window (lane w-window; the raw
; window's is fn-owner-page-window-executor-cache).  ONE call on the live SAME
; pool, off the owner: the returned job's controller is read from its own
; carry, a :ready job is leased into the cache (books/decoded-window-read.lisp
; fn-pwz-cache, KEEP the cached buffer's resident octets) and its authority
; retired in the same step (books/decoded-worker-job.lisp fn-dwj-cache); any
; other word leaves the job and the pool untouched, to be released as before.
(defun fn-owner-page-decoded-job-cache (worker token fn-decoded-job fn-page-read-pool)
  (declare (xargs :stobjs (fn-decoded-job fn-page-read-pool) :guard t))
  (if (not (fn-owner-page-window-legacy-writablep fn-page-read-pool))
      (mv :runtime-operation-unavailable worker fn-decoded-job fn-page-read-pool)
    (mv-let (word worker1 ledger fn-decoded-job)
      (fn-dwj-cache (fn-owner-page-read-ledger fn-page-read-pool) worker token
                    (fn-owner-page-window-cache-keep) fn-decoded-job)
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
        (mv word worker1 fn-decoded-job fn-page-read-pool)))))

;; The verified-window cache for a decoded window (books/decoded-window-read.lisp
;; fn-pwz-cache*, books/decoded-worker-job.lisp fn-dwj-cache).
(definterface fn-owner-page-decoded-job-cache :class :common-lisp-compliant
  :keystones ((fn-dwj-cache-only-a-ready-job :via fn-dwj-cache)
              (fn-dwj-cached-job-refuses-scalar-publication :via fn-dwj-cache)
              (fn-pwz-cache-lease-keeps-only-the-buffer-and-stays-funded :via fn-pwz-cache-lease)))

(defun fn-owner-page-decoded-window-cache-byte-at
    (token file eoff elen poff compressed trailer decoded dict-id i
           fn-ew-buffer fn-page-read-pool)
  (declare (xargs :stobjs (fn-ew-buffer fn-page-read-pool) :guard t))
  (fn-pwz-cache-byte-at (fn-owner-page-read-ledger fn-page-read-pool) token
                        file eoff elen poff compressed trailer decoded dict-id i
                        fn-ew-buffer))

(definterface fn-owner-page-decoded-window-cache-byte-at :class :common-lisp-compliant
  :keystones ((fn-pwz-a-hit-is-the-published-window :via fn-pwz-cache-byte-at)
              (fn-pwz-hit-requires-a-cached-exact-window :via fn-pwz-cache-byte-at)))

(defthm fn-owner-page-decoded-window-cache-byte-at-refines-pwz-by-definition
  (equal (mv-list 2 (fn-owner-page-decoded-window-cache-byte-at
                     token file eoff elen poff compressed trailer decoded dict-id i
                     fn-ew-buffer fn-page-read-pool))
         (mv-list 2 (fn-pwz-cache-byte-at (fn-owner-page-read-ledger fn-page-read-pool) token
                                          file eoff elen poff compressed trailer decoded dict-id i
                                          fn-ew-buffer))))

(defun fn-owner-page-decoded-window-cache-span-at
    (token file eoff elen poff compressed trailer decoded dict-id i j
           fn-ew-buffer fn-ew-span fn-page-read-pool)
  (declare (xargs :stobjs (fn-ew-buffer fn-ew-span fn-page-read-pool)
                  :guard (and (natp i) (natp j) (< i j))))
  (fn-pwz-cache-span-at (fn-owner-page-read-ledger fn-page-read-pool) token
                        file eoff elen poff compressed trailer decoded dict-id i j
                        fn-ew-buffer fn-ew-span))

(definterface fn-owner-page-decoded-window-cache-span-at :class :common-lisp-compliant
  :kinds ((i natp) (j natp))
  :keystones ((fn-pwz-cache-span-at-is-the-cached-bytes :via fn-pwz-cache-span-at)
              (fn-pwz-cache-span-at-answers-when-its-ends-do :via fn-pwz-cache-span-at)))

; KEYSTONE (a decoded cache span is the cache's scalar hits), at the owner row.
(defthm fn-owner-page-decoded-window-cache-span-at-is-the-cached-bytes
  (implies (and (natp i) (natp j) (< i j) (natp k) (< k (- j i))
                (equal (mv-nth 0 (fn-owner-page-decoded-window-cache-span-at
                                  token file eoff elen poff compressed trailer decoded dict-id
                                  i j fn-ew-buffer fn-ew-span fn-page-read-pool))
                       :span))
           (and (equal (mv-nth 0 (fn-owner-page-decoded-window-cache-byte-at
                                  token file eoff elen poff compressed trailer decoded dict-id
                                  (+ i k) fn-ew-buffer fn-page-read-pool))
                       :byte)
                (equal (nth k (nth 0 (mv-nth 1 (fn-owner-page-decoded-window-cache-span-at
                                                token file eoff elen poff compressed trailer
                                                decoded dict-id i j fn-ew-buffer fn-ew-span
                                                fn-page-read-pool))))
                       (mv-nth 1 (fn-owner-page-decoded-window-cache-byte-at
                                  token file eoff elen poff compressed trailer decoded dict-id
                                  (+ i k) fn-ew-buffer fn-page-read-pool)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-owner-page-decoded-window-cache-span-at
                                     fn-owner-page-decoded-window-cache-byte-at)
           :use (:instance fn-pwz-cache-span-at-is-the-cached-bytes
                           (ledger (fn-owner-page-read-ledger fn-page-read-pool))))))
