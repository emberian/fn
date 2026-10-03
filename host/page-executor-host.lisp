; Persistent physical workers carry one exact resource binding until the
; worker relinquishes its result and the owner settles that I/O incarnation.
(in-package "ACL2")
(include-book "page-read-host")
(include-book "../books/page-read-executor")
(include-book "../books/page-read-direct") ; the unfunded cold line (host/native/extent.lisp)

(defun fn-owner-page-executor-acquire (worker token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word worker1 ledger)
    (fn-pxe-acquire (fn-owner-page-read-ledger fn-page-read-pool) worker token)
    (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
      (mv word worker1 fn-page-read-pool))))

(defun fn-owner-page-executor-commit (worker io token cachedp fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word worker1 ledger)
    (fn-pxe-commit worker io token (fn-owner-page-read-ledger fn-page-read-pool) cachedp)
    (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
      (mv word worker1 fn-page-read-pool))))

; Representation boundaries, not keystones: exact answers and pool effects.
; Open only the adapter and multiple-value projections.  Expanding the ledger
; or its executor here repeats the implementation inside each result slot;
; none of that reasoning is needed to establish this wrapper equality.
(defthm fn-owner-page-executor-acquire-refines-pxe-by-definition
  (equal (mv-list 3 (fn-owner-page-executor-acquire worker token fn-page-read-pool))
         (list (mv-nth 0 (fn-pxe-acquire (fn-owner-page-read-ledger fn-page-read-pool) worker token))
               (mv-nth 1 (fn-pxe-acquire (fn-owner-page-read-ledger fn-page-read-pool) worker token))
               (fn-owner-page-read-keep-ledger
                (mv-nth 2 (fn-pxe-acquire (fn-owner-page-read-ledger fn-page-read-pool) worker token))
                fn-page-read-pool)))
  :hints (("Goal" :in-theory '(fn-owner-page-executor-acquire mv-list mv-nth nth
                               (:executable-counterpart binary-+)
                               (:executable-counterpart zp))
           :expand ((:free (x) (mv-nth 1 x)) (:free (x) (mv-nth 2 x))
                    (:free (x) (nth 1 x)) (:free (x) (nth 2 x))))))

(defthm fn-owner-page-executor-commit-refines-pxe-by-definition
  (equal (mv-list 3 (fn-owner-page-executor-commit worker io token cachedp fn-page-read-pool))
         (list (mv-nth 0 (fn-pxe-commit worker io token (fn-owner-page-read-ledger fn-page-read-pool) cachedp))
               (mv-nth 1 (fn-pxe-commit worker io token (fn-owner-page-read-ledger fn-page-read-pool) cachedp))
               (fn-owner-page-read-keep-ledger
                (mv-nth 2 (fn-pxe-commit worker io token (fn-owner-page-read-ledger fn-page-read-pool) cachedp))
                fn-page-read-pool)))
  :hints (("Goal" :in-theory '(fn-owner-page-executor-commit mv-list mv-nth nth
                               (:executable-counterpart binary-+)
                               (:executable-counterpart zp))
           :expand ((:free (x) (mv-nth 1 x)) (:free (x) (mv-nth 2 x))
                    (:free (x) (nth 1 x)) (:free (x) (nth 2 x))))))
