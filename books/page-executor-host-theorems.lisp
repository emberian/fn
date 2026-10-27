; Moved from host/page-executor-host.lisp by tools/host_theorems.py; this book is their source now.
; They only restate that host book's definitions, which it keeps.
(in-package "ACL2")
(include-book "../host/page-executor-host")

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
