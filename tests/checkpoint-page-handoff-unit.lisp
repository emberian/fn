; UNEXECUTED pool-transit control. This is not an actual C-cut, physical-page
; completion, machine-resource accounting or composed handoff proof witness.
(in-package "ACL2")
(include-book "../books/checkpoint-page-worker")

(defun fn2-checkpoint-page-transit-body (fn2-checkpoint-page fn2-pool)
 (declare (xargs :stobjs (fn2-checkpoint-page fn2-pool) :verify-guards nil))
 (b* ((fn2-checkpoint-page (fn2-checkpoint-page-init 1 fn2-checkpoint-page))
      (fn2-pool (fn2-pool-init '((1 . 4096)) 1 100 fn2-pool))
      ((mv reserved slot gen fn2-pool) (fn2-pool-reserve 0 3 0 7 fn2-pool))
      ((unless (eq reserved :ok)) (mv nil fn2-checkpoint-page fn2-pool))
      (fn2-checkpoint-page (fn2-checkpoint-page-put 0 (slot slot) (gen gen)))
      ((mv written fn2-pool) (fn2-pool-write slot gen 0 77 3 0 7 fn2-pool))
      ((mv handed fn2-pool) (fn2-pool-hand slot gen 3 0 7 4 1 9 fn2-pool))
      (transit (and (eq written :ok) (eq handed :ok)
                    (fn2-checkpoint-page-handedp 4 1 9 3 0 7 fn2-checkpoint-page fn2-pool)
                    (not (fn2-checkpoint-page-handedp 4 1 8 3 0 7 fn2-checkpoint-page fn2-pool))))
      ((mv blocked fn2-pool) (fn2-pool-write slot gen 0 88 3 0 7 fn2-pool))
      ((mv foreign fn2-pool) (fn2-pool-accept-hand slot gen 4 1 8 fn2-pool))
      ((mv accepted fn2-pool) (fn2-pool-accept-hand slot gen 4 1 9 fn2-pool))
      ((mv source-blocked fn2-pool) (fn2-pool-write slot gen 0 99 3 0 7 fn2-pool))
      ((mv read byte) (fn2-pool-read slot gen 0 4 1 9 fn2-pool))
      (owned (and transit (eq blocked :state) (eq foreign :owner) (eq accepted :ok)
                  (eq source-blocked :owner) (eq read :ok) (equal byte 77)))
      ; Direct pool return tests the other transit direction only; it does not
      ; assert the physical-completion gate required by the actual worker.
      ((mv returned fn2-pool) (fn2-pool-hand slot gen 4 1 9 3 0 7 fn2-pool))
      (return-transit (and (eq returned :ok)
                          (fn2-checkpoint-page-handedp 3 0 7 4 1 9 fn2-checkpoint-page fn2-pool)))
      ((mv old-blocked fn2-pool) (fn2-pool-write slot gen 0 100 4 1 9 fn2-pool))
      ((mv restored fn2-pool) (fn2-pool-accept-hand slot gen 3 0 7 fn2-pool))
      ((mv reread same-byte) (fn2-pool-read slot gen 0 3 0 7 fn2-pool)))
  (mv (and owned return-transit (eq old-blocked :state) (eq restored :ok)
           (eq reread :ok) (equal same-byte 77)) fn2-checkpoint-page fn2-pool)))

(defun fn2-checkpoint-page-transit-control ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-checkpoint-page
  (mv-let (ok fn2-checkpoint-page)
   (with-local-stobj fn2-pool
    (mv-let (ok fn2-checkpoint-page fn2-pool)
     (fn2-checkpoint-page-transit-body fn2-checkpoint-page fn2-pool)
     (mv ok fn2-checkpoint-page))) ok)))
(assert-event (fn2-checkpoint-page-transit-control))
