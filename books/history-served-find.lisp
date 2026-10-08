; First-match fallbacks and key redecision read the carried history columns.
(in-package "ACL2")
(include-book "def-loop-history-find")
(include-book "key-statements")
(include-book "control-visible")
(include-book "history-columns-relation")

(def-loop-history-find fn-hist-key-statement (msgid) fn-ks-find-statement
  (and (fn-ks-pending event) (equal (fn-ks-msgid event) msgid)))

(def-loop-history-find fn-hist-control-event (msgid) fn-ctl-row-event
  (let ((row (fn-ctl-event-row event)))
    (and msgid row (equal (fn-record-msgid row) msgid))))

(defthm fn-hist-key-statement-is-store-reader
  (implies (fn-hist-of-storep hist s)
           (equal (fn-hist-key-statement msgid hist)
                  (fn-ks-find-statement msgid (fn-sf-records (fn-sn-files s)))))
  :hints (("Goal" :in-theory (enable fn-hist-of-storep))))

(defthm fn-hist-control-event-is-store-reader
  (implies (fn-hist-of-storep hist s)
           (equal (fn-hist-control-event msgid hist)
                  (fn-ctl-row-event msgid (fn-sf-records (fn-sn-files s)))))
  :hints (("Goal" :in-theory (enable fn-hist-of-storep))))
