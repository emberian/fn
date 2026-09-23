(in-package "ACL2")
(include-book "../../books/store-events")
(include-book "topic-history-store-events-tests")

(assert-event (fn-store-event-p *thad-anchor-event*))
(assert-event (fn-store-event-p *thad-report-event*))
(assert-event (equal (fn-store-event-kind *thad-anchor-event*) :topic-anchor))
(assert-event (equal (fn-store-event-kind *thad-report-event*) :topic-admit))
(assert-event (equal (fn-store-event-sequence *thad-anchor-event*) 8))
(assert-event (equal (fn-store-event-txid *thad-report-event*) 12))
(assert-event (equal (fn-store-event-generation *thad-report-event*) 13))
(assert-event (equal (fn-store-publication-ceiling :topic-anchor) 1024))
(assert-event (equal (fn-store-publication-ceiling :topic-admit) 1024))
(assert-event
 (equal (fn-store-event-encode *thad-anchor-event*)
        *thae-anchor-octets*))
(assert-event
 (equal (fn-store-event-encode *thad-report-event*)
        *thae-report-octets*))
(assert-event
 (equal (fn-store-event-decode-exact *thae-anchor-octets*)
        (fn-stmt-ok *thad-anchor-event*)))
(assert-event
 (equal (fn-store-event-decode-exact *thae-report-octets*)
        (fn-stmt-ok *thad-report-event*)))
