; Exact typed window lease and persistent worker transitions.
(in-package "ACL2")
(include-book "page-read-host")
(include-book "../books/page-window-executor")
(include-book "../books/cold-read-window")

(defun fn-owner-page-window-legacy-writablep (fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard t))
 (and (eq (fn-prp-mode fn-page-read-pool) :served)
      (not (fn-prp-alloc-installation fn-page-read-pool))
      (not (fn-prb-fixed-widthp 6 (fn-prp-data fn-page-read-pool)))))

(defun fn-owner-page-window-executor-acquire (worker token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (fn-owner-page-window-legacy-writablep fn-page-read-pool))
      (mv :runtime-operation-unavailable worker fn-page-read-pool)
    (mv-let (word worker1 ledger)
    (fn-pwx-acquire (fn-owner-page-read-ledger fn-page-read-pool) worker token)
    (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
      (mv word worker1 fn-page-read-pool)))))

(defthm fn-owner-page-window-executor-acquire-refines-pwx-by-definition
  (implies (fn-owner-page-window-legacy-writablep fn-page-read-pool)
   (equal (mv-list 3 (fn-owner-page-window-executor-acquire worker token fn-page-read-pool))
    (let ((r (mv-list 3 (fn-pwx-acquire (fn-owner-page-read-ledger fn-page-read-pool) worker token))))
      (list (nth 0 r) (nth 1 r) (fn-owner-page-read-keep-ledger (nth 2 r) fn-page-read-pool)))))
  :hints (("Goal" :in-theory (enable fn-pwx-acquire))))

(defun fn-owner-page-window-executor-return (worker token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (fn-owner-page-window-legacy-writablep fn-page-read-pool))
      (mv :runtime-operation-unavailable worker fn-page-read-pool)
    (mv-let (word worker1 ledger)
    (fn-pwx-return (fn-owner-page-read-ledger fn-page-read-pool) worker token)
    (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
      (mv word worker1 fn-page-read-pool)))))

(defthm fn-owner-page-window-executor-return-refines-pwx-by-definition
  (implies (fn-owner-page-window-legacy-writablep fn-page-read-pool)
   (equal (mv-list 3 (fn-owner-page-window-executor-return worker token fn-page-read-pool))
    (let ((r (mv-list 3 (fn-pwx-return (fn-owner-page-read-ledger fn-page-read-pool) worker token))))
      (list (nth 0 r) (nth 1 r) (fn-owner-page-read-keep-ledger (nth 2 r) fn-page-read-pool)))))
  :hints (("Goal" :in-theory (enable fn-pwx-return))))

(defun fn-owner-page-window-executor-release (worker token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (fn-owner-page-window-legacy-writablep fn-page-read-pool))
      (mv :runtime-operation-unavailable worker fn-page-read-pool)
    (mv-let (word worker1 ledger)
    (fn-pwx-release (fn-owner-page-read-ledger fn-page-read-pool) worker token)
    (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
      (mv word worker1 fn-page-read-pool)))))

(defthm fn-owner-page-window-executor-release-refines-pwx-by-definition
  (implies (fn-owner-page-window-legacy-writablep fn-page-read-pool)
   (equal (mv-list 3 (fn-owner-page-window-executor-release worker token fn-page-read-pool))
    (let ((r (mv-list 3 (fn-pwx-release (fn-owner-page-read-ledger fn-page-read-pool) worker token))))
      (list (nth 0 r) (nth 1 r) (fn-owner-page-read-keep-ledger (nth 2 r) fn-page-read-pool)))))
  :hints (("Goal" :in-theory (enable fn-pwx-release))))

(include-book "../books/page-window-read")

(defun fn-owner-page-window-byte (worker token plan i fn-ew-buffer fn-page-read-pool)
  (declare (xargs :stobjs (fn-ew-buffer fn-page-read-pool) :guard (true-listp plan)))
  (fn-pwr-byte (fn-owner-page-read-ledger fn-page-read-pool) worker token plan i fn-ew-buffer))

(defthm fn-owner-page-window-byte-refines-pwr-by-definition
  (equal (mv-list 2 (fn-owner-page-window-byte worker token plan i fn-ew-buffer fn-page-read-pool))
         (mv-list 2 (fn-pwr-byte (fn-owner-page-read-ledger fn-page-read-pool)
                               worker token plan i fn-ew-buffer))))

; Staged selected-layout admission. This consumes the core's fresh ticket;
; native allocator correspondence and primitive scratch adequacy remain open.
(defun fn-owner-page-window-executor-acquire-funded (worker descriptor fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (fn-owner-page-window-legacy-writablep fn-page-read-pool))
      (mv :runtime-operation-unavailable worker nil fn-page-read-pool)
    (let* ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
         (demand (fn-crw-job-demand descriptor (fn-prl-nth 2 ledger))))
    (if (not (equal (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool))
        (mv :read-resources-unavailable worker nil fn-page-read-pool)
      (mv-let (word token ledger1) (fn-prw-admit ledger descriptor demand)
        (if (not (equal word :admitted))
            (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger1 fn-page-read-pool)))
              (mv word worker token fn-page-read-pool))
          (mv-let (word worker1 ledger2) (fn-pwx-acquire ledger1 worker token)
            ; A refused binding remains charged and carries its token. Only
            ; exact physical return plus final relinquishment permits refund.
            (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger2 fn-page-read-pool)))
              (mv word worker1 token fn-page-read-pool)))))))))

(defthm fn-owner-page-window-executor-acquire-funded-refines-by-definition
  (implies (fn-owner-page-window-legacy-writablep fn-page-read-pool)
   (equal
   (mv-list 4 (fn-owner-page-window-executor-acquire-funded worker descriptor fn-page-read-pool))
   (let* ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
          (demand (fn-crw-job-demand descriptor (fn-prl-nth 2 ledger)))
          (admit (mv-list 3 (fn-prw-admit ledger descriptor demand)))
          (acquire (mv-list 3 (fn-pwx-acquire (nth 2 admit) worker (nth 1 admit)))))
     (if (not (equal (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool))
         (list :read-resources-unavailable worker nil fn-page-read-pool)
       (if (not (equal (nth 0 admit) :admitted))
           (list (nth 0 admit) worker (nth 1 admit)
                 (fn-owner-page-read-keep-ledger (nth 2 admit) fn-page-read-pool))
         (list (nth 0 acquire) (nth 1 acquire) (nth 1 admit)
               (fn-owner-page-read-keep-ledger (nth 2 acquire) fn-page-read-pool)))))))
  :hints (("Goal" :in-theory (enable fn-prw-admit fn-pwx-acquire))))

(defun fn-owner-page-window-byte-at (worker token plan file eoff elen poff plen trailer i fn-ew-buffer fn-page-read-pool)
  (declare (xargs :stobjs (fn-ew-buffer fn-page-read-pool) :guard (true-listp plan)))
  (fn-pwr-byte-at (fn-owner-page-read-ledger fn-page-read-pool) worker token plan
                 file eoff elen poff plen trailer i fn-ew-buffer))

(defthm fn-owner-page-window-byte-at-refines-by-definition
  (equal
   (mv-list 2 (fn-owner-page-window-byte-at worker token plan file eoff elen poff plen trailer i fn-ew-buffer fn-page-read-pool))
   (mv-list 2 (fn-pwr-byte-at (fn-owner-page-read-ledger fn-page-read-pool) worker token plan
                            file eoff elen poff plen trailer i fn-ew-buffer))))

(defun fn-owner-page-window-outcome (worker token plan fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool :guard (true-listp plan)))
  (fn-pwr-outcome (fn-owner-page-read-ledger fn-page-read-pool) worker token plan))

(defthm fn-owner-page-window-outcome-refines-by-definition
  (equal (fn-owner-page-window-outcome worker token plan fn-page-read-pool)
         (fn-pwr-outcome (fn-owner-page-read-ledger fn-page-read-pool) worker token plan)))

(defun fn-owner-page-window-executor-cancel (worker token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (fn-owner-page-window-legacy-writablep fn-page-read-pool))
      (mv :runtime-operation-unavailable worker fn-page-read-pool)
    (mv-let (word worker1 ledger)
    (fn-pwx-cancel (fn-owner-page-read-ledger fn-page-read-pool) worker token)
    (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
      (mv word worker1 fn-page-read-pool)))))

(defthm fn-owner-page-window-executor-cancel-refines-by-definition
  (implies (fn-owner-page-window-legacy-writablep fn-page-read-pool)
   (equal (mv-list 3 (fn-owner-page-window-executor-cancel worker token fn-page-read-pool))
    (let ((r (mv-list 3 (fn-pwx-cancel (fn-owner-page-read-ledger fn-page-read-pool) worker token))))
      (list (nth 0 r) (nth 1 r) (fn-owner-page-read-keep-ledger (nth 2 r) fn-page-read-pool)))))
  :hints (("Goal" :in-theory (enable fn-pwx-cancel))))

(defun fn-owner-page-window-executor-settle-cancelled (worker token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (fn-owner-page-window-legacy-writablep fn-page-read-pool))
      (mv :runtime-operation-unavailable worker fn-page-read-pool)
    (mv-let (word worker1 ledger)
    (fn-pwx-settle-cancelled (fn-owner-page-read-ledger fn-page-read-pool) worker token)
    (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
      (mv word worker1 fn-page-read-pool)))))

(defthm fn-owner-page-window-executor-settle-cancelled-refines-by-definition
  (implies (fn-owner-page-window-legacy-writablep fn-page-read-pool)
   (equal (mv-list 3 (fn-owner-page-window-executor-settle-cancelled worker token fn-page-read-pool))
    (let ((r (mv-list 3 (fn-pwx-settle-cancelled (fn-owner-page-read-ledger fn-page-read-pool) worker token))))
      (list (nth 0 r) (nth 1 r) (fn-owner-page-read-keep-ledger (nth 2 r) fn-page-read-pool)))))
  :hints (("Goal" :in-theory (enable fn-pwx-settle-cancelled))))

(defun fn-owner-page-window-work-permittedp (worker token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (fn-pwx-work-permittedp (fn-owner-page-read-ledger fn-page-read-pool) worker token))

(include-book "../books/payload-arena")

; Caller authorization comes from the captured provider row and live logical
; holder. This getter alone never grants authority to an arbitrary handle.
(defun fn-owner-page-window-current-octet (h i fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp h) (< h (fn-arena-count fn-arena))
                              (natp i) (< i (fn-arena-payload-len h fn-arena)))))
  (fn-arena-get h i fn-arena))

(defthm fn-owner-page-window-current-octet-refines-arena-by-definition
  (equal (fn-owner-page-window-current-octet h i fn-arena)
         (fn-arena-get h i fn-arena)))

(defun fn-owner-page-window-current-octet-fenced (h i fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (and (natp h) (< h (fn-arena-count fn-arena))
           (natp i) (< i (fn-arena-payload-len h fn-arena)))
      (mv :byte (fn-arena-get h i fn-arena))
    (mv :invalid-current-byte nil)))
(defthm fn-owner-page-window-current-fence-refines-arena-by-definition
  (implies (and (natp h) (< h (fn-arena-count fn-arena))
                (natp i) (< i (fn-arena-payload-len h fn-arena)))
    (equal (mv-list 2 (fn-owner-page-window-current-octet-fenced h i fn-arena))
           (list :byte (fn-arena-get h i fn-arena))))
  :rule-classes nil)

(defun fn-owner-page-window-decoded-refusal ()
  (declare (xargs :guard t))
  :decoded-window-unavailable)
