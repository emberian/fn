; Number of rows the circular scan skips on the way to P. An out-of-range
; cursor restarts at zero, just as fn2-account-grant-scan does.
(in-package "ACL2")
(include-book "accounts")

(defun fn2-account-grant-distance (cursor p rows)
  (declare (xargs :guard (and (natp cursor) (natp p) (natp rows) (< p rows))))
  (let ((i (if (< (nfix cursor) (nfix rows)) (nfix cursor) 0)))
    (if (<= i (nfix p)) (- (nfix p) i) (+ (- (nfix rows) i) (nfix p)))))

(defthm fn2-account-grant-distance-bound
  (implies (and (natp p) (natp rows) (< p rows))
           (< (fn2-account-grant-distance cursor p rows) rows))
  :rule-classes :linear)

; If the full scan can reach a fitting P, its first fitting principal is
; either P or one whose successor is strictly closer to P.
(defthm fn2-account-grant-scan-progress
  (let* ((rows (nfix (fn2-accounts-rows fn2-accounts)))
         (chosen (fn2-account-grant-scan k i fn2-accounts)))
    (implies (and (natp p) (< p rows) (<= rows *fn2-none*)
                  (not (equal (fn2-accounts-wait-head p fn2-accounts) *fn2-none*))
                  (fn2-account-fits p *fn2-account-request-dim* 1 fn2-accounts)
                  (< (fn2-account-grant-distance i p rows) (nfix k)))
             (and (not (equal chosen *fn2-none*))
                  (or (equal chosen p)
                      (< (fn2-account-grant-distance (+ 1 chosen) p rows)
                         (fn2-account-grant-distance i p rows))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-account-grant-scan k i fn2-accounts)
           :in-theory (e/d (fn2-account-grant-scan fn2-account-grant-distance)
                           (fn2-accounts-rows fn2-accounts-wait-head fn2-account-fits)))))

(defthm fn2-account-grant-next-progress
  (let* ((rows (fn2-accounts-rows fn2-accounts))
         (chosen (fn2-account-grant-next fn2-accounts)))
    (implies (and (fn2-accountsp fn2-accounts) (fn2-accounts-wfp fn2-accounts)
                  (natp p) (< p rows)
                  (not (equal (fn2-accounts-wait-head p fn2-accounts) *fn2-none*))
                  (fn2-account-fits p *fn2-account-request-dim* 1 fn2-accounts))
             (and (not (equal chosen *fn2-none*))
                  (or (equal chosen p)
                      (< (fn2-account-grant-distance (+ 1 chosen) p rows)
                         (fn2-account-grant-distance
                          (fn2-account-grant-cursor fn2-accounts) p rows))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-account-grant-scan-progress
                         (i (fn2-account-grant-cursor fn2-accounts))
                         (k (fn2-accounts-rows fn2-accounts))))
           :in-theory (e/d (fn2-account-grant-next)
                           (fn2-account-grant-distance fn2-account-grant-cursor
                            fn2-accounts-wait-head fn2-account-fits
                            fn2-accounts-rows fn2-accountsp fn2-accounts-wfp)))))
