(in-package "ACL2")
(include-book "../../books/topic-history-identity-disjoint")
(include-book "topic-history-store-events-tests")
(include-book "std/testing/must-fail" :dir :system)

; Reachable events of all three topic forms take the identity-neutral arm.
(assert-event (and (fn-th-topic-eventp *thla-install*)
                   (fn-th-topic-eventp *thad-anchor-event*)
                   (fn-th-topic-eventp *thad-report-event*)
                   (not (fn-stxk-p *thla-install*))
                   (not (fn-stxe-p *thad-anchor-event*))
                   (not (fn-stxa-p *thad-report-event*))))

; The topic premise matters: a real keyring event is an identity event.
(must-fail
 (defthm thid-all-events-are-identity-neutral
   (not (fn-stxk-p event))))
