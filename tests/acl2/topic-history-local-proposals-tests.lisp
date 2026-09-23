(in-package "ACL2")
(include-book "../../books/topic-history-local-proposals")
(include-book "topic-history-store-node-tests")
(include-book "std/testing/must-fail" :dir :system)

(assert-event
 (equal (fn-th-local-propose-install
         (fn-sn-topic *thsn-root-accepted*) 2 501 *thla-id*)
        (fn-stmt-ok *thsn-install*)))
(assert-event
 (equal (fn-th-local-propose-anchor
         (fn-sn-topic *thsn-installed*) 3 1 501 2)
        (fn-stmt-ok *thsn-anchor*)))
(assert-event
 (equal (fn-th-local-propose-report
         (fn-sn-topic *thsn-report-accepted*) 5 4)
        (fn-stmt-ok *thsn-admit*)))
(assert-event
 (equal (fn-th-local-propose-anchor
         (fn-sn-topic *thsn-installed*) 3 1 502 2)
        (fn-stmt-error :administrator)))
(assert-event
 (equal (fn-th-local-propose-anchor
         (fn-sn-topic *thsn-installed*) 3 99 501 2)
        (fn-stmt-error :missing-historical-authorship)))
(assert-event
 (equal (fn-th-local-propose-report
         (fn-sn-topic *thsn-report-accepted*) 5 99)
        (fn-stmt-error :missing-historical-authorship)))
(must-fail
 (assert-event
  (fn-stmt-okp
   (fn-th-local-propose-anchor
    (fn-sn-topic *thsn-installed*) 3 99 501 2))))
