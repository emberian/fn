;;; Test-only initialization, loaded after tests/seeded-store.lsp.
(in-package "ACL2")

(defvar *fn2-n-seed-store* nil "Writes of this harness's seeded memory fixture.")

(defun fn2-n-make-seeded-host (profile seeds &key (control-fd -1) (trace-capacity 0) (kill-at 0))
  (let ((core (fn2-n-live-core)))
    (fn2-init-executor profile :echo nil core)
    (multiple-value-bind (code store) (fn2-cs-seed-all seeds 1 core)
      (unless (eq code :ok)
        (error "fn2 native fixture: seed refused: ~(~a~)" code))
      (setf *fn2-n-seed-store* store)
      (fn2-n-open-host profile core :control-fd control-fd :trace-capacity trace-capacity
                       :kill-at kill-at :memory-store store))))
