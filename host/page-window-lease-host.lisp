; Exact window resource ownership; demand comes from the selected runtime
; allocator model. Native window activation awaits the authenticated stream.
(in-package "ACL2")
(include-book "page-read-host")
(include-book "../books/page-window-lease")

(defun fn-owner-page-window-admit (descriptor demand fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (equal (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool))
      (mv :read-resources-unavailable nil fn-page-read-pool)
    (mv-let (word token ledger)
      (fn-prw-admit (fn-owner-page-read-ledger fn-page-read-pool) descriptor demand)
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
        (mv word token fn-page-read-pool)))))

(defun fn-owner-page-window-return (token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word ledger) (fn-prw-return (fn-owner-page-read-ledger fn-page-read-pool) token)
    (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
      (mv word fn-page-read-pool))))

(defun fn-owner-page-window-release (token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word ledger) (fn-prw-release (fn-owner-page-read-ledger fn-page-read-pool) token)
    (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
      (mv word fn-page-read-pool))))

(defthm fn-owner-page-window-admit-refines-prw-by-definition
  (equal (mv-list 3 (fn-owner-page-window-admit descriptor demand fn-page-read-pool))
    (if (not (equal (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool))
        (list :read-resources-unavailable nil fn-page-read-pool)
      (let ((r (mv-list 3 (fn-prw-admit (fn-owner-page-read-ledger fn-page-read-pool) descriptor demand))))
        (list (mv-nth 0 r) (mv-nth 1 r) (fn-owner-page-read-keep-ledger (mv-nth 2 r) fn-page-read-pool)))))
  :hints (("Goal" :in-theory '(fn-owner-page-window-admit mv-list mv-nth nth
                               (:executable-counterpart binary-+)
                               (:executable-counterpart zp))
           :expand ((:free (x) (mv-nth 1 x)) (:free (x) (nth 1 x)) (:free (x) (mv-nth 2 x)) (:free (x) (nth 2 x))))))

(defthm fn-owner-page-window-return-refines-prw-by-definition
  (equal (mv-list 2 (fn-owner-page-window-return token fn-page-read-pool))
    (let ((r (mv-list 2 (fn-prw-return (fn-owner-page-read-ledger fn-page-read-pool) token))))
      (list (mv-nth 0 r) (fn-owner-page-read-keep-ledger (mv-nth 1 r) fn-page-read-pool))))
  :hints (("Goal" :in-theory '(fn-owner-page-window-return mv-list mv-nth nth
                               (:executable-counterpart binary-+)
                               (:executable-counterpart zp))
           :expand ((:free (x) (mv-nth 1 x)) (:free (x) (nth 1 x))))))

(defthm fn-owner-page-window-release-refines-prw-by-definition
  (equal (mv-list 2 (fn-owner-page-window-release token fn-page-read-pool))
    (let ((r (mv-list 2 (fn-prw-release (fn-owner-page-read-ledger fn-page-read-pool) token))))
      (list (mv-nth 0 r) (fn-owner-page-read-keep-ledger (mv-nth 1 r) fn-page-read-pool))))
  :hints (("Goal" :in-theory '(fn-owner-page-window-release mv-list mv-nth nth
                               (:executable-counterpart binary-+)
                               (:executable-counterpart zp))
           :expand ((:free (x) (mv-nth 1 x)) (:free (x) (nth 1 x))))))