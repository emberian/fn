; Private decoded worker assignment after SAME-pool typed admission. Native
; construction/lifetime correspondence and full allocation tariff are PRF1288.
(in-package "ACL2")
(include-book "decoded-worker-controller")
(include-book "decoded-window-lease")
(include-book "decoded-window-read")

(defun fn-dwa-assign (ledger worker token root incarnation fn-pww-carry)
  (declare (xargs :stobjs fn-pww-carry :guard t :verify-guards nil))
  (if (not (and (fn-pwz-tokenp token)
                (fn-pwx-boundp ledger worker token :running)
                (consp root) incarnation
                (eq (fn-pww-phase fn-pww-carry) :uninstalled)))
      (mv :decoded-assignment-unavailable fn-pww-carry)
    (let* ((fn-pww-carry (update-fn-pww-phase :assigning fn-pww-carry))
           (fn-pww-carry (update-fn-pww-id (nfix (fn-prl-nth 0 worker)) fn-pww-carry))
           (fn-pww-carry (update-fn-pww-token token fn-pww-carry))
           (fn-pww-carry (update-fn-pww-root root fn-pww-carry))
           (fn-pww-carry (update-fn-pww-source-incarnation incarnation fn-pww-carry))
           (fn-pww-carry (update-fn-pww-borrow-phase :owned fn-pww-carry))
           (fn-pww-carry (update-fn-pww-input-capacity 64 fn-pww-carry))
           (fn-pww-carry (update-fn-pww-storage-receipt
                          (list :constructing token) fn-pww-carry))
           (fn-pww-carry (update-fn-pww-phase :assigned fn-pww-carry)))
      (mv :decoded-assigned fn-pww-carry))))

; Scalar getters do not expose any buffer child. Native holds all private
; concrete children through actual activation return and final scalar borrow.
(defun fn-dwa-controller (fn-pww-carry)
  (declare (xargs :stobjs fn-pww-carry :guard t))
  (fn-pww-controller fn-pww-carry))

(defun fn-dwa-revision (fn-pww-carry)
  (declare (xargs :stobjs fn-pww-carry :guard t))
  (fn-pww-action-revision fn-pww-carry))

(verify-guards fn-dwa-assign)
