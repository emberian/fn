; Whole-claim SAT, two removals and the inverted-victim mutation.
; Registration follows the universal theorem; no theorem is claimed here.
(in-package "ACL2")
(include-book "lc-cleaning-model-tests")

(defun lcm-complete-seed (fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (ec-call (fn-lbc-open-rebuild (lcm-test-rows 1)
                   (fn-lc-at 1 (lcm-test-input 1)) fn-lbc)))

(defun lcm-complete-pre-tooth (segs fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (mv (ec-call (fn-lc-locators-resolve fn-lbc segs)) fn-lbc))

(defun lcm-complete-ack-tooth (victim profile context disk segs outcome fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (mv-let (answer fn-lbc afterdisk aftersegs ledger)
  (fn-lc-clean-segment victim profile context disk segs outcome fn-lbc)
  (declare (ignore afterdisk aftersegs))
  (mv (fn-lc-segment-moves-completep (list answer nil nil nil ledger) victim) fn-lbc)))

(defun lcm-complete-post-tooth (victim profile context disk segs outcome fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (mv-let (answer fn-lbc afterdisk aftersegs ledger)
  (fn-lc-clean-segment victim profile context disk segs outcome fn-lbc)
  (declare (ignore answer afterdisk ledger))
  (mv (and (not (fn-lc-any-row-names-segment victim fn-lbc))
           (ec-call (fn-lc-locators-resolve fn-lbc aftersegs))) fn-lbc)))

(defun lcm-complete-inverted-tooth (victim profile context disk segs outcome fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (mv-let (answer fn-lbc afterdisk aftersegs ledger)
  (fn-lc-clean-segment victim profile context disk segs outcome fn-lbc)
  (declare (ignore answer afterdisk aftersegs ledger))
  (mv (fn-lc-any-row-names-segment victim fn-lbc) fn-lbc)))

(defun lcm-complete-controls (victim quantum missing fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (let* ((input (lcm-test-input 1)) (disk (fn-lc-at 0 input))
        (segs (if missing nil (fn-lc-at 1 input)))
        (context (list :lc :eager (fn-lc-at 2 input) 1))
        (profile (list quantum)) (outcome '(:ok :ok))
        (fn-lbc (lcm-complete-seed fn-lbc)))
  (mv-let (pre fn-lbc) (lcm-complete-pre-tooth segs fn-lbc)
   (mv-let (complete fn-lbc)
    (lcm-complete-ack-tooth victim profile context disk segs outcome fn-lbc)
    (let ((fn-lbc (lcm-complete-seed fn-lbc)))
     (mv-let (post fn-lbc)
      (lcm-complete-post-tooth victim profile context disk segs outcome fn-lbc)
      (let ((fn-lbc (lcm-complete-seed fn-lbc)))
       (mv-let (mutant fn-lbc)
        (lcm-complete-inverted-tooth victim profile context disk segs outcome fn-lbc)
        (mv (list pre complete post mutant) fn-lbc)))))))))

(defun lcm-complete-controls-fixture (victim quantum missing)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (out fn-lbc) (lcm-complete-controls victim quantum missing fn-lbc) out)))

(verify-guards lcm-complete-controls-fixture)

(assert-event (equal (lcm-complete-controls-fixture 1 1 nil) '(t t t nil)))

(assert-event (equal (lcm-complete-controls-fixture 2 1 t) '(nil t nil nil)))

(assert-event (equal (lcm-complete-controls-fixture 1 0 nil) '(t nil nil t)))
