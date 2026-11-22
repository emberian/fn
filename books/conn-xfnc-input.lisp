; The NNTP connection owns both command and counted-body spans.
(in-package "ACL2")
(include-book "xfnc-ops")
(include-book "xfnc-rx")
(include-book "c-snapshot")

(fn2-csnapshot-op fn2-conn-xfnc-input (conn gen discard pos left request-max discard-max) 4
 (b* (((mv code row) (fn2-xfnc-fc-row conn fn2-core))
      ((unless (eq code :ok)) (mv :capacity 0 0 0 fn2-core))
      (slot (fn2-conn-row-rx-slot conn fn2-core))
      (rgen (fn2-conn-row-rx-gen conn fn2-core)))
   (stobj-let ((fn2-fields (fn2-core-fields fn2-core)) (fn2-digests (fn2-core-digests fn2-core))
               (fn2-b3 (fn2-core-b3 fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
     (code next remaining verb fn2-fields fn2-digests fn2-b3)
     (fn2-xfnc-rx-step (* 128 (nfix row)) row slot rgen *fn2-conn-kind* conn gen
                       (equal discard 1) pos left request-max discard-max nil
                       fn2-fields fn2-digests fn2-b3 fn2-pool)
     (if (and (unsigned-byte-p 32 next) (unsigned-byte-p 32 remaining))
         (mv code next remaining (case verb (:register 1) (:read 2) (otherwise 0)) fn2-core)
       (mv :capacity 0 0 0 fn2-core)))))
(defcost fn2-conn-xfnc-input :answers t :bytes 2048
 :tables (fn2-core-fields fn2-core-digests fn2-core-b3)
 :doc "Consume a bounded discard step or validate the exact held request in this connection's private format row.")
(in-theory (disable fn2-conn-xfnc-input))
