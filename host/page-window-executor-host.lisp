; Exact typed window lease and persistent worker transitions.
(in-package "ACL2")
(include-book "page-read-host")
(include-book "../books/page-window-executor")
(include-book "../books/cold-read-window")
(include-book "../books/page-read-counter-transaction") ; fn-prb-fixed-widthp

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
  ;; Its own theory (as the funded acquire below): the wrapper opened, the
  ;; subject fn-pwx-acquire kept closed; in the image's ld world opening it cost
  ;; up to 274 s.
  :hints (("Goal" :in-theory '(fn-owner-page-window-executor-acquire mv-list mv-nth nth
                               (:executable-counterpart binary-+)
                               (:executable-counterpart zp)
                               (:type-prescription fn-owner-page-window-legacy-writablep))
           :expand ((:free (x) (mv-nth 1 x)) (:free (x) (mv-nth 2 x))
                    (:free (x) (nth 1 x)) (:free (x) (nth 2 x))))))

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
  ;; Its own theory (as the funded acquire below): the wrapper opened, the
  ;; subject fn-pwx-return kept closed; in the image's ld world opening it cost
  ;; up to 274 s.
  :hints (("Goal" :in-theory '(fn-owner-page-window-executor-return mv-list mv-nth nth
                               (:executable-counterpart binary-+)
                               (:executable-counterpart zp)
                               (:type-prescription fn-owner-page-window-legacy-writablep))
           :expand ((:free (x) (mv-nth 1 x)) (:free (x) (mv-nth 2 x))
                    (:free (x) (nth 1 x)) (:free (x) (nth 2 x))))))

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
  ;; Its own theory (as the funded acquire below): the wrapper opened, the
  ;; subject fn-pwx-release kept closed; in the image's ld world opening it cost
  ;; up to 274 s.
  :hints (("Goal" :in-theory '(fn-owner-page-window-executor-release mv-list mv-nth nth
                               (:executable-counterpart binary-+)
                               (:executable-counterpart zp)
                               (:type-prescription fn-owner-page-window-legacy-writablep))
           :expand ((:free (x) (mv-nth 1 x)) (:free (x) (mv-nth 2 x))
                    (:free (x) (nth 1 x)) (:free (x) (nth 2 x))))))

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
  ;; Its own theory: the runes the proof uses, so the image's ld world (whose
  ;; global theory made this a failing 15.7M-step search) proves it as the book does.
  :hints (("Goal" :in-theory (union-theories
                              (theory 'minimal-theory)
                              '(fn-owner-page-read-direct-mode fn-owner-page-read-keep-ledger
                                fn-owner-page-read-ledger fn-owner-page-window-executor-acquire-funded
                                fn-owner-page-window-legacy-writablep fn-prp-alloc-installation
                                fn-prp-data fn-prp-mode fn-prw-admit fn-pwx-acquire
                                mv-list mv-nth not nth update-fn-prp-data update-nth
                                (:executable-counterpart cdr) (:executable-counterpart cons)
                                (:executable-counterpart equal)
                                (:executable-counterpart fn-prb-fixed-widthp)
                                (:executable-counterpart fn-prl-baseline)
                                (:executable-counterpart fn-prl-binding)
                                (:executable-counterpart fn-prl-nth)
                                (:executable-counterpart fn-pwx-tokenp)
                                (:executable-counterpart not) (:executable-counterpart nth)
                                (:executable-counterpart zp)
                                nth-0-cons nth-add1 (:type-prescription fn-prs-issue))))))

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
  ;; Its own theory (as the funded acquire below): the wrapper opened, the
  ;; subject fn-pwx-cancel kept closed; in the image's ld world opening it cost
  ;; up to 274 s.
  :hints (("Goal" :in-theory '(fn-owner-page-window-executor-cancel mv-list mv-nth nth
                               (:executable-counterpart binary-+)
                               (:executable-counterpart zp)
                               (:type-prescription fn-owner-page-window-legacy-writablep))
           :expand ((:free (x) (mv-nth 1 x)) (:free (x) (mv-nth 2 x))
                    (:free (x) (nth 1 x)) (:free (x) (nth 2 x))))))

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
  ;; Its own theory (as the funded acquire below): the wrapper opened, the
  ;; subject fn-pwx-settle-cancelled kept closed; in the image's ld world opening it cost
  ;; up to 274 s.
  :hints (("Goal" :in-theory '(fn-owner-page-window-executor-settle-cancelled mv-list mv-nth nth
                               (:executable-counterpart binary-+)
                               (:executable-counterpart zp)
                               (:type-prescription fn-owner-page-window-legacy-writablep))
           :expand ((:free (x) (mv-nth 1 x)) (:free (x) (mv-nth 2 x))
                    (:free (x) (nth 1 x)) (:free (x) (nth 2 x))))))

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

(defun fn-owner-page-window-decoded-refusal ()
  (declare (xargs :guard t))
  :decoded-window-unavailable)
