; Protocol helpers for COMPRESS; transport ownership is generated separately.
(in-package "ACL2")
(include-book "compress-kind")
(include-book "conn-answer")
(fn2-book-layer :d)
(defcost fn2-compress-render-handoff :bytes 512 :answers (:ok :bounds) :tables (fn2-core-pool)
 :doc "Render admitted COMPRESS206 at the old-carrier reply barrier.")
(defcost fn2-compress-enabled-p :doc "The supported profile's pinned compression enablement.")
(defmacro fn2-compress-op-events ()
 '(progn
(defun fn2-compress-render-handoff (mask slot gen oslot ogen fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (code fn2-pool)
  (fn2-answer-say *fn2-nntp-command-compress* *fn2-nntp-reply-compress-started*
                 mask 0 slot gen *fn2-conn-kind* oslot ogen fn2-pool)
  (mv code fn2-core)))
(fn2-core-preserves fn2-compress-render-handoff (mask slot gen oslot ogen fn2-core) :position 1 :rows nil
 :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-compress-enabled-p (fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (stobj-let ((fn2-compress-config (fn2-core-compress-config fn2-core))) (enabled)
  (and (< 0 (fn2-compress-config-rows fn2-compress-config))
       (equal (fn2-compress-config-enabled 0 fn2-compress-config) 1)) enabled))
(in-theory (disable fn2-compress-render-handoff fn2-compress-enabled-p))))
