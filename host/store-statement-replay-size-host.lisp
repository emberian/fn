; Same selected-checkpoint seed for actual suffix recovery. Parallel metadata
; is retained from the one summary load; this grants no owner readiness.
(in-package "ACL2")
(include-book "store-checkpoint-context-host")
(include-book "../books/statement-recover-sized")
(include-book "../books/store-checkpoint-size-reader")

; Existing production seed, moved without changing its body or native ABI.
(defun fn-store-statement-replay-seed (state)
 (declare (xargs :stobjs state :mode :program))
 (let ((checkpoint (fn-store-sco-current state)))
  (value (fn-ssr-seed (if checkpoint (fn-sco-identity checkpoint)
                           (fn-stxk-initial-context 0))))))

(defun fn-store-srs-seed (checkpoint info)
 (declare (xargs :guard t))
 (if checkpoint
  (mv-let (metadata root fields) (fn-sctsr-original-context-carries info)
   (declare (ignore root))
   (fn-ssrs-seed (fn-sco-identity checkpoint)
                 (if (eq metadata :ready) fields nil)))
  ; The public no-checkpoint seed is this exact empty original context.
  ; Its six carries come from the guarded constructor, not a summary scan.
  (mv-let (ctx fields) (fn-ics-begin 0)
   (fn-ssrs-seed ctx fields))))

(defthm fn-store-srs-seed-original-result-unfolds
 (equal (mv-nth 0 (fn-store-srs-seed checkpoint info))
        (fn-ssr-seed (if checkpoint (fn-sco-identity checkpoint)
                         (fn-stxk-initial-context 0))))
 :hints (("Goal" :in-theory (e/d (fn-store-srs-seed fn-ssrs-seed fn-ics-begin)
                     (fn-sctsr-original-context-carries fn-ssr-seed)))))

(defun fn-store-statement-replay-seed-sized (state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((checkpoint (fn-store-sco-current state))
        (selected (fn-store-sco-original-context-info state))
        (info (if (eq (car selected) :summary) (caddr selected) nil)))
  (mv-let (acc fields metadata) (fn-store-srs-seed checkpoint info)
   (value (list acc fields metadata)))))
