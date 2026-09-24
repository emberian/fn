(in-package "ACL2")
(include-book "../../books/topic-history-local-proposals")
(include-book "topic-history-store-node-tests")
(include-book "std/testing/must-fail" :dir :system)

(assert-event
 (equal (fn-th-local-propose-install
         (fn-sn-topic *thsn-root-accepted*) 2 501 *thla-id*)
        (fn-stmt-ok *thsn-install*)))
(assert-event
 (equal (fn-th-local-propose :install (fn-sn-topic *thsn-root-accepted*)
                             2 nil 501 *thla-id* nil)
        (fn-stmt-ok *thsn-install*)))
(assert-event
 (equal (fn-th-local-propose-anchor
         (fn-sn-topic *thsn-installed*) 3 1 501 2)
        (fn-stmt-ok *thsn-anchor*)))
(assert-event
 (equal (fn-th-local-propose :anchor (fn-sn-topic *thsn-installed*)
                             3 1 501 nil 2)
        (fn-stmt-ok *thsn-anchor*)))
(assert-event
 (equal (fn-th-local-propose-report
         (fn-sn-topic *thsn-report-accepted*) 5 4)
        (fn-stmt-ok *thsn-admit*)))
(assert-event
 (equal (fn-th-local-propose :report (fn-sn-topic *thsn-report-accepted*)
                             5 4 nil nil nil)
        (fn-stmt-ok *thsn-admit*)))
(assert-event
 (let* ((projection (fn-sn-topic *thsn-admitted*))
        (anchor (fn-th-find-anchor *thad-topic* (fn-th-at 4 projection)))
        (prior (car (fn-th-anchor-reports anchor))))
   (and (equal (fn-th-local-propose :report projection 6 4 nil nil nil)
               (list :replayed-historical prior))
        (equal (fn-th-at 8 anchor) 1)
        (equal (fn-th-at 1 projection) 6))))
(must-fail
 (assert-event
  (equal (car (fn-th-local-propose
               :report (fn-sn-topic *thsn-report-accepted*)
               5 4 nil nil nil))
         :replayed-historical)))
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
(assert-event
 (equal (fn-th-local-propose :report (fn-sn-topic *thsn-report-accepted*)
                             5 99 nil nil nil)
        (fn-stmt-error :missing-historical-authorship)))
(must-fail
 (assert-event
  (fn-stmt-okp
   (fn-th-local-propose-anchor
    (fn-sn-topic *thsn-installed*) 3 99 501 2))))
