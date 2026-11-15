; LF counts come from bytes the one feed worker actually emitted.
; Pool-only control: no upload row or controller phase is planted.
(in-package "ACL2")
(include-book "upload-feed-unit")

(defconst *fn2-ufl-source* '(46 120 13 10 122 13 10))
(defun fn2-ufl-run (raw budget stale)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-pool
  (mv-let (result fn2-pool)
   (b* ((fn2-pool (fn2-pool-init '((1 . 128) (1 . 128)) 1 1000 fn2-pool))
        ((mv rx-code rx rg fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool))
        ((mv dst-code dst dg fn2-pool) (fn2-pool-reserve 1 2 2 2 fn2-pool))
        (wire (if raw *fn2-ufl-source* '(46 46 120 13 10 122 13 10 46 13 10)))
        (fn2-pool (fn2-ufu-put wire rx rg fn2-pool))
        ((mv first i mode discard copied lines fn2-pool)
         (fn2-upload-feed-counted budget 0 (len wire) 0 nil raw rx (if stale (+ 1 rg) rg)
                                  1 1 1 dst dg 2 2 2 128 nil fn2-pool))
        ((mv second end mode2 discard2 copied2 lines2 fn2-pool)
         (if (eq first :budget)
             (fn2-upload-feed-counted 100 i (len wire) mode discard raw rx rg
                                      1 1 1 dst dg 2 2 2 128 nil fn2-pool)
           (mv :none i mode discard 0 0 fn2-pool))))
    (mv (list rx-code dst-code first i copied lines second end copied2 lines2
              mode2 discard2 (fn2-ufu-read 0 (fn2-gram-fill dst fn2-pool) dst dg fn2-pool))
        fn2-pool))
   result)))

(assert-event
 (and (equal (fn2-ufl-run nil 100 nil)
             (list :ok :ok :terminator 11 7 2 :none 11 0 0 *fn2-feed-bol* nil *fn2-ufl-source*))
      (equal (fn2-ufl-run t 100 nil)
             (list :ok :ok :need-more 7 7 2 :none 7 0 0 *fn2-feed-bol* nil *fn2-ufl-source*))
      (equal (fn2-ufl-run nil 5 nil)
             (list :ok :ok :budget 5 4 1 :terminator 11 3 1 *fn2-feed-bol* nil *fn2-ufl-source*))
      (equal (fn2-ufl-run nil 100 t)
             (list :ok :ok :fault 0 0 0 :none 0 0 0 *fn2-feed-bol* nil nil))
      (= (fn2-feed-emitted-lf 1 10) 1)
      (= (fn2-feed-emitted-lf 1 120) 0)
      (= (fn2-feed-emitted-lf 2 120) 1)))
