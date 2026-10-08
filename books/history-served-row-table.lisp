; A full visibility rebuild makes one row table, rather than one scan per article.
(in-package "ACL2")
(include-book "def-loop-history-fold")
(include-book "control-visible")

(def-loop-history-fold fn-hist-control-row-table fn-ctl-row-table
 (let* ((row (fn-ctl-event-row event)) (m (and row (fn-record-msgid row))))
  (if (and m (not (hons-get m acc))) (hons-acons m event acc) acc)))
