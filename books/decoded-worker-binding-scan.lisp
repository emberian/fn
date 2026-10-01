; Internal CURRENT predecessor for actual decoded admission. No public issuer.
(in-package "ACL2")
(include-book "page-window-worker-storage")
(include-book "page-read-ledger")

; Scan8 retains captured source and original binding root across every yield.
; REVISION is the actual pool binding revision captured by the future parent.
(defun fn-dwb-scan (file revision original remaining found phase source)
 (declare (xargs :guard t))
 (list :decoded-binding-scan file revision original remaining found phase source))

(defun fn-dwb-start (file revision rows source)
 (declare (xargs :guard t))
 (fn-dwb-scan file revision rows rows nil :scan source))

; One actual binding inspection, no recursion or whole-root comparison.
; The key has fixed2 cells; FILE scalar width is a supported-domain obligation.
(defun fn-dwb-one (scan)
 (declare (xargs :guard t))
 (let* ((file (fn-prl-nth 1 scan)) (revision (fn-prl-nth 2 scan))
        (original (fn-prl-nth 3 scan)) (remaining (fn-prl-nth 4 scan))
        (found (fn-prl-nth 5 scan)) (phase (fn-prl-nth 6 scan))
        (source (fn-prl-nth 7 scan)))
  (if (not (eq phase :scan)) scan
   (if (consp remaining)
    (let ((row (car remaining)))
     (if (and (natp file) (consp row) (equal (car row) (list :incarnation file)))
      (fn-dwb-scan file revision original (cdr remaining) row :resolved source)
      (fn-dwb-scan file revision original (cdr remaining) found :scan source)))
    (fn-dwb-scan file revision original remaining found
                 (if remaining :malformed :absent) source)))))

; Internal parent receives only a word; no supplied found row can be installed.
; Even a resolved incarnation is not constructor/runtime permission.
(defun fn-dwb-word (scan)
 (declare (xargs :guard t))
 (case (fn-prl-nth 6 scan)
  (:scan :yield)
  (:resolved (if (and (consp (fn-prl-nth 5 scan))
                     (eq (fn-prl-nth 1 (cdr (fn-prl-nth 5 scan))) :incarnation))
                :binding-resolved :binding-stale))
  (:absent :binding-absent)
  (otherwise :binding-stale)))

; CURRENT cursor is persisted in the same retained worker carry. This child
; action is invoked only by the serialized token/source-selected parent; that
; parent and its installed operation allowance are not supplied by this book.
(defun fn-dwb-node-one (fn-pww-node)
 (declare (xargs :stobjs fn-pww-node :guard t :verify-guards nil))
 (if (not (fn-pww-children-boundp 'fn-pww-carry fn-pww-node))
  (mv :worker-unavailable fn-pww-node)
  (stobj-let
   ((fn-pww-carry (fn-pww-children-get 'fn-pww-carry fn-pww-node (create-fn-pww-carry))))
   (word fn-pww-carry)
   (let ((scan (fn-pww-pending-action fn-pww-carry)))
    (if (not (and (eq (fn-pww-phase fn-pww-carry) :admission-scanning)
                  (true-listp scan) (equal (len scan) 8)
                  (eq (car scan) :decoded-binding-scan)))
     (mv :binding-stale fn-pww-carry)
     (let* ((next (fn-dwb-one scan))
            (fn-pww-carry (update-fn-pww-pending-action next fn-pww-carry)))
      (mv (fn-dwb-word next) fn-pww-carry))))
   (mv word fn-pww-node))))

(defthm fn-dwb-one-retains-captured-authority
 (let ((next (fn-dwb-one scan)))
  (and (equal (fn-prl-nth 1 next) (fn-prl-nth 1 scan))
       (equal (fn-prl-nth 2 next) (fn-prl-nth 2 scan))
       (equal (fn-prl-nth 3 next) (fn-prl-nth 3 scan))
       (equal (fn-prl-nth 7 next) (fn-prl-nth 7 scan))))
 :hints (("Goal" :in-theory (enable fn-dwb-one fn-dwb-scan fn-prl-nth))))
