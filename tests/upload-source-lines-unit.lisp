; Actual shared checked LF counter controls. These do not claim upload
; storage, window reuse, EOF verdict or complete POST execution.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "upload-feed-unit")
(defun fn2-usl-run ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-pool
  (mv-let (ok fn2-pool)
   (b* ((fn2-pool (fn2-pool-init '((1 . 4096)) 1 1000 fn2-pool))
        ((mv reserve slot gen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool))
        ;; CR and LF straddle the counted spans. Folded header + blank line
        ;; have three LFs; the body has two, without a trailing-line guess.
        (bytes '(65 13 10 32 66 13 10 13 10 120 13 10 121 13 10))
        (fn2-pool (fn2-ufu-put bytes slot gen fn2-pool))
        ((mv first a) (fn2-txn-count-loop 2 slot gen 0 0 1 1 1 fn2-pool))
        ((mv second b) (fn2-txn-count-loop (- (len bytes) 2) slot gen 2 a 1 1 1 fn2-pool))
        ((mv whole c) (fn2-txn-count-loop (len bytes) slot gen 0 0 1 1 1 fn2-pool))
        ((mv refused kept) (fn2-txn-count-loop (len bytes) slot gen 0 19 1 1 2 fn2-pool)))
    (mv (and (eq reserve :ok) (eq first :ok) (eq second :ok) (eq whole :ok)
             (= a 0) (= b 5) (= c b) (= (- b (+ 2 1)) 2)
             (eq refused :bounds) (= kept 19) (fn2-pool-wfp fn2-pool)) fn2-pool)) ok)))
(assert-event (fn2-usl-run))
