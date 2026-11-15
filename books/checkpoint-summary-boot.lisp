; The real boot path captures one authenticated directory entry on a separate
; turn before DFS consumes it. It never takes caller-supplied decoded rows.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "boot-kind")
(include-book "checkpoint-restore-semantic-boot")
(include-book "checkpoint-summary-catalog")
(fn2-book-layer :c)
(defcost fn2-boot-checkpoint-summary-capture :child fn2-checkpoint-summary-capture :answers t
 :bytes *fn2-checkpoint-restore-semantic-entry-bytes*
 :tables (fn2-core-checkpoint-summary fn2-core-checkpoint-summary-sources fn2-core-fields))
(defcost fn2-boot-checkpoint-summary-close :child fn2-checkpoint-summary-close :answers t
 :tables (fn2-core-checkpoint-summary))
(defcost fn2-boot-checkpoint-summary-begin :answers t :bytes 128
 :tables (fn2-core-checkpoint-summary fn2-core-checkpoint-restore-semantic fn2-core-fc fn2-core-pool))
(defmacro fn2-boot-checkpoint-summary-operations ()
 '(progn
  (make-event (value (cons 'progn
   (append (fn2-arms-op-face-events 'fn2-boot-checkpoint-summary-capture 'fn2-checkpoint-summary-capture (w state))
           (fn2-arms-op-face-events 'fn2-boot-checkpoint-summary-close 'fn2-checkpoint-summary-close (w state))))))
  (defun fn2-boot-checkpoint-summary-begin (id ogen fn2-core)
   (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
   (b* (((mv code fn2-core) (fn2-boot-checkpoint-semantic-begin id ogen fn2-core))
        ((unless (eq code :read)) (mv code fn2-core))
        ((mv code fn2-core)
         (stobj-let ((fn2-checkpoint-summary (fn2-core-checkpoint-summary fn2-core))
                     (fn2-checkpoint-cbase-holds (fn2-core-checkpoint-cbase-holds fn2-core))
                     (fn2-checkpoints (fn2-core-checkpoints fn2-core)) (fn2-checkpoint-refs (fn2-core-checkpoint-refs fn2-core))
                     (fn2-checkpoint-bytes (fn2-core-checkpoint-bytes fn2-core))
                     (fn2-checkpoint-restore-map (fn2-core-checkpoint-restore-map fn2-core))
                     (fn2-checkpoint-restore-map-control (fn2-core-checkpoint-restore-map-control fn2-core))
                     (fn2-checkpoint-restore-semantic (fn2-core-checkpoint-restore-semantic fn2-core)))
          (code fn2-checkpoint-summary)
          (fn2-checkpoint-summary-begin fn2-checkpoint-summary fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
           fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-semantic fn2-checkpoint-cbase-holds)
          (mv code fn2-core))))
    (mv (if (eq code :ok) :read code) fn2-core)))
  (fn2-core-preserves fn2-boot-checkpoint-summary-begin (id ogen fn2-core) :position 1 :rows nil)))
