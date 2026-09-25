; Witnesses and teeth for books/bp-route-jobs (spike/bp).
(in-package "ACL2")
(include-book "../../books/bp-route-jobs")
(include-book "std/testing/must-fail" :dir :system)

(defconst *rjt-a* (fn-bprt-route 100 "dtn://receiver/*" "via-a" "dtn://relay-a/" 4556))
(defconst *rjt-b* (fn-bprt-route 50 "dtn://receiver/*" "via-b" "dtn://relay-b/" 4557))
(defconst *rjt-nocontact* (fn-bprt-route 10 "dtn://receiver/*" "dark" "dtn://dark/" 0))
(defconst *rjt-queued*
  (list :route (fn-record-string-octets "127.0.0.1") 9999
        (fn-record-string-octets "dtn://sender/") 30 1024 1048576))

; Queue time: the routed hop's contact, the queued session parameters kept.
(assert-event
 (equal (fn-bprt-job-route "dtn://receiver/" (list *rjt-a*)
                           (fn-record-string-octets "dtn://sender/") 30 1024 1048576)
        (list :route (fn-record-string-octets "127.0.0.1") 4556
              (fn-record-string-octets "dtn://sender/") 30 1024 1048576)))
(assert-event (null (fn-bprt-job-route "dtn://receiver/" nil 0 30 1024 1048576)))

; Contact time: the table changed since queueing (a better route to via-b):
; the job is offered to via-b's port, which must announce relay-b; never to
; the queued port 9999 or to via-a.
(assert-event
 (equal (fn-bprt-send-decision *rjt-queued* "dtn://receiver/" (list *rjt-a* *rjt-b*))
        (list :send
              (list :route (fn-record-string-octets "127.0.0.1") 4557
                    (fn-record-string-octets "dtn://sender/") 30 1024 1048576)
              "via-b" "dtn://relay-b/")))
(must-fail
 (assert-event
  (equal (caddr (fn-bprt-send-decision *rjt-queued* "dtn://receiver/"
                                       (list *rjt-a* *rjt-b*)))
         "via-a")))
; Route removed: held, no-route.
(assert-event
 (equal (fn-bprt-send-decision *rjt-queued* "dtn://receiver/" nil) '(:held :no-route)))
; Only a boundary without a contact routes it: held, no live hop.
(assert-event
 (equal (fn-bprt-send-decision *rjt-queued* "dtn://receiver/" (list *rjt-nocontact*))
        '(:held :no-live-hop)))
; Another destination is not routed by a receiver pattern.
(must-fail
 (assert-event
  (equal (car (fn-bprt-send-decision *rjt-queued* "dtn://other/" (list *rjt-a*)))
         :send)))
