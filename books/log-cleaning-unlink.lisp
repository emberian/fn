; LC unlink model. The existing decision checks both root observations,
; pins and tail before issuing an unlink; directory persistence is separate.
(in-package "ACL2")
(include-book "log-cleaning")
(include-book "log-checkpoint-publication")
(include-book "log-checkpoint-independent-guards")

(defun fn-lc-unlink (seg disk r fn-lc-pins tail segs outcome fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (if (not (ec-call (fn-lc-unlink-allowedp seg disk r fn-lc-pins tail)))
     (mv :referenced fn-lbc disk segs nil)
  (let* ((program (list (list :unlink :segment seg) '(:directory-fsync)))
         (done (fn-lc-outcome-ok-count outcome 2))
         (trace (fn-lc-take (min 2 (+ 1 done)) program))
         ; Even an uncertain unlink may have removed the file. Retain that
         ; possible persistent effect instead of inventing a rollback.
         (after (ec-call (fn-lb-log-model-recycle seg segs))))
   (mv (if (equal done 2) :ok :uncertain) fn-lbc disk after trace))))

(verify-guards fn-lc-unlink)
