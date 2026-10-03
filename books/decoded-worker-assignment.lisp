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

; PRF-1298. Called only after the native worker returned and the final scalar
; borrower left the extent critical section. This does not infer physical
; return from a timeout, nor refund the permanently retained scratch backing.
(defun fn-dwa-retire (ledger worker token fn-pww-carry)
  (declare (xargs :stobjs fn-pww-carry :guard t :verify-guards nil))
  (if (not (and (fn-pwz-tokenp token)
                (equal token (fn-pww-token fn-pww-carry))
                (or (fn-pwx-boundp ledger worker token :returned)
                    (fn-pwx-boundp ledger worker token :cancelled-returned))
                (member-eq (fn-pww-phase fn-pww-carry) '(:assigned :running))
                (eq (fn-pww-borrow-phase fn-pww-carry) :owned)
                (null (fn-pww-pending-action fn-pww-carry))))
      (mv :decoded-retirement-unavailable fn-pww-carry)
    (let* ((fn-pww-carry (update-fn-pww-token nil fn-pww-carry))
           (fn-pww-carry (update-fn-pww-root nil fn-pww-carry))
           (fn-pww-carry (update-fn-pww-source-incarnation nil fn-pww-carry))
           (fn-pww-carry (update-fn-pww-controller nil fn-pww-carry))
           (fn-pww-carry (update-fn-pww-pending-action nil fn-pww-carry))
           (fn-pww-carry (update-fn-pww-storage-receipt nil fn-pww-carry))
           (fn-pww-carry (update-fn-pww-observation nil fn-pww-carry))
           (fn-pww-carry (update-fn-pww-id 0 fn-pww-carry))
           (fn-pww-carry (update-fn-pww-input-capacity 0 fn-pww-carry))
           (fn-pww-carry (update-fn-pww-action-revision 0 fn-pww-carry))
           (fn-pww-carry (update-fn-pww-borrow-phase :none fn-pww-carry))
           (fn-pww-carry (update-fn-pww-phase :uninstalled fn-pww-carry)))
      (mv :reusable fn-pww-carry))))
(verify-guards fn-dwa-retire)

(local (include-book "std/lists/update-nth" :dir :system))

(defthm fn-dwa-retirement-revokes-prior-authority
  (implies (equal (mv-nth 0 (fn-dwa-retire ledger worker token carry)) :reusable)
    (let ((next (mv-nth 1 (fn-dwa-retire ledger worker token carry))))
      (and (equal (fn-pww-token next) nil)
           (equal (fn-pww-root next) nil)
           (equal (fn-pww-source-incarnation next) nil)
           (equal (fn-pww-controller next) nil)
           (equal (fn-pww-pending-action next) nil)
           (equal (fn-pww-storage-receipt next) nil)
           (equal (fn-pww-borrow-phase next) :none)
           (equal (fn-pww-phase next) :uninstalled))))
  :hints (("Goal" :in-theory (disable fn-pwz-tokenp fn-pwx-boundp))))

(defthm fn-dwa-refused-retirement-preserves-carry
  (implies (not (equal (mv-nth 0 (fn-dwa-retire ledger worker token carry)) :reusable))
           (equal (mv-nth 1 (fn-dwa-retire ledger worker token carry)) carry)))
