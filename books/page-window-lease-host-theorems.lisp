; Moved from host/page-window-lease-host.lisp by tools/host_theorems.py; this book is their source now.
; They only restate that host book's definitions, which it keeps.
(in-package "ACL2")
(include-book "../host/page-window-lease-host")

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