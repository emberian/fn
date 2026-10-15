; LC complete-cleaning model. Capture is independent of the completion
; predicate. A work quantum yields; a later invocation captures the remaining
; victim rows. Reclaiming payloads stop at the missing LB A1 boundary.
(in-package "ACL2")
(include-book "log-cleaning-move")

(defun fn-lc-victim-rows-from (i n victim fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)
   :measure (nfix n) :verify-guards nil))
 (if (or (zp (nfix n)) (<= (fn-lbc-count fn-lbc) (nfix i))) nil
  (let ((rest (fn-lc-victim-rows-from (+ 1 (nfix i)) (1- (nfix n)) victim fn-lbc)))
   (if (equal (fn-lbc-loc0 (nfix i) fn-lbc) victim) (cons (nfix i) rest) rest))))
(defun fn-lc-any-row-names-segment (victim fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (if (consp (fn-lc-victim-rows-from 0 (fn-lbc-count fn-lbc) victim fn-lbc)) t nil))

; Completion is a cursor/ack ledger, never a post-state locator assertion.
(defun fn-lc-clean-receipt-indices (receipts)
 (declare (xargs :guard t))
 (if (consp receipts)
  (cons (fn-lc-at 1 (car receipts)) (fn-lc-clean-receipt-indices (cdr receipts))) nil))
(defun fn-lc-clean-receipts-okp (receipts victim)
 (declare (xargs :guard t))
 (if (consp receipts)
  (and (equal (fn-lc-head (car receipts)) :lc-move-durable)
       (not (equal (fn-lc-at 2 (car receipts)) victim))
       (equal (fn-lc-head (fn-lc-at 3 (car receipts))) :log-write)
       (equal (fn-lc-at 4 (car receipts)) '(:log-fdatasync))
       (fn-lc-clean-receipts-okp (cdr receipts) victim)) t))
(defun fn-lc-segment-moves-completep (out victim)
 (declare (xargs :guard t))
 (let* ((ledger (fn-lc-at 4 out)) (capture (fn-lc-at 0 ledger))
        (receipts (fn-lc-at 1 ledger)) (pending (fn-lc-at 2 ledger)))
  (and (equal (fn-lc-head out) :ok)
       (equal (fn-lc-head capture) :lc-clean-capture)
       (equal (fn-lc-at 1 capture) victim)
       (null pending)
       (equal (fn-lc-clean-receipt-indices receipts) (fn-lc-at 3 capture))
       (fn-lc-clean-receipts-okp receipts victim))))

(defun fn-lc-clean-work (work fuel victim header k r mode disk segs outcome fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)
   :measure (len work) :verify-guards nil
   :hints (("Goal" :in-theory
     (disable fn-lc-clean fn-lc-plan-move fn-lc-bound-row fn-lb-log-payload
              fn-lc-last-segment-id fn-lc-ordered-segments fn-rcl-tombstonep)))))
 (cond ((atom work) (mv :ok fn-lbc disk segs (list nil nil)))
       ((zp (nfix fuel)) (mv :yield fn-lbc disk segs (list nil work)))
       ((equal (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) victim)
        (mv :needs-segment-reservation fn-lbc disk segs (list nil work)))
       (t
        (let* ((i (nfix (car work)))
               (row (ec-call (fn-lc-bound-row i fn-lbc segs)))
               (payload (ec-call (fn-lb-log-payload row segs))))
         (if (fn-rcl-tombstonep payload)
             ; Both newly reclaimed and existing tombstone arms are LB A1.
             (mv :reclaim-pending fn-lbc disk segs (list nil work))
          (let ((move (fn-lc-plan-move i header k r mode segs fn-lbc)))
           (mv-let (answer fn-lbc nextdisk nextsegs trace)
             (fn-lc-clean move disk segs outcome fn-lbc)
            (if (not (equal answer :ok))
                (mv answer fn-lbc nextdisk nextsegs (list nil work))
             (mv-let (answer fn-lbc finaldisk finalsegs ledger)
               (fn-lc-clean-work (cdr work) (1- (nfix fuel)) victim header k r mode
                                  nextdisk nextsegs (fn-lc-drop 2 outcome) fn-lbc)
               (mv answer fn-lbc finaldisk finalsegs
                   (list (cons (list :lc-move-durable i (fn-lc-move-loc0 move)
                                     (fn-lc-head trace) (fn-lc-at 1 trace))
                               (fn-lc-at 0 ledger))
                         (fn-lc-at 1 ledger))))))))))))

; PROFILE's work quantum is scheduling, not a cap on resident row count.
; CONTEXT = (ROOT MODE HEADER K); publications/reservations are separate steps.
(defun fn-lc-clean-segment (victim profile context disk segs outcome fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (let* ((work (fn-lc-victim-rows-from 0 (fn-lbc-count fn-lbc) victim fn-lbc))
        (capture (list :lc-clean-capture victim (fn-lbc-count fn-lbc) work)))
  (mv-let (answer fn-lbc afterdisk aftersegs ledger)
   (fn-lc-clean-work work (fn-lc-at 0 profile) victim (fn-lc-at 2 context)
                      (fn-lc-at 3 context) (fn-lc-at 0 context) (fn-lc-at 1 context)
                      disk segs outcome fn-lbc)
   (mv answer fn-lbc afterdisk aftersegs
       (list capture (fn-lc-at 0 ledger) (fn-lc-at 1 ledger))))))

(verify-guards fn-lc-victim-rows-from)
(verify-guards fn-lc-any-row-names-segment)

(verify-guards fn-lc-clean-work
 :hints (("Goal" :in-theory
  (disable fn-lbc-p fn-lc-clean fn-lc-plan-move fn-lc-last-segment-id
   fn-lc-ordered-segments fn-lc-bound-row fn-lb-log-payload))))
(verify-guards fn-lc-clean-segment
 :hints (("Goal" :in-theory (disable fn-lbc-p fn-lc-clean-work fn-lc-victim-rows-from))))
