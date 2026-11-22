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

;; A taken cursor is still in :select on this non-yielding connection turn.
;; Mark it before either actor runs. The body span comes from :taken; it is
;; interpreted as FNCT only in the peer phase.
(fn2-csnapshot-op fn2-xfnc-bind-cursor (cursor generation conn cgen) 1
 (if (and (fn2-conn-cursor-live-p cursor generation fn2-core)
          (equal (fn2-cursor-row-phase cursor fn2-core) *fn2-cursor-state-select*)
          (equal (fn2-cursor-row-conn-kind cursor fn2-core) *fn2-conn-kind*)
          (equal (fn2-cursor-row-conn cursor fn2-core) conn)
          (equal (fn2-cursor-row-conn-gen cursor fn2-core) cgen)
          (eq (fn2-conn-snapshot-read-code conn fn2-core) :ok)
          (equal (fn2-machine-generation conn fn2-core) cgen)
          (equal (fn2-conn-row-phase conn fn2-core) *fn2-conn-state-query*))
     (mv :ok (fn2-cursor-put-core cursor (phase *fn2-cursor-state-peer*) (tag *fn2-nntp-command-xfnc*)))
   (mv :state fn2-core)))
(in-theory (disable fn2-xfnc-bind-cursor))
(defcost fn2-xfnc-bind-cursor :answers (:ok :state) :tables (fn2-cursor-table)
 :doc "Bind the freshly reserved query row to the generation and counted frame of its protected connection.")
