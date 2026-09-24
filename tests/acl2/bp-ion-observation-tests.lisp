(in-package "ACL2")
(include-book "bp-outbound-tests")
(include-book "../../books/bp-ion-observation")

(defconst *bpio-line* "observed-v1|dtn://destination/|ipn:2.1|ipn:1.1|843544024799|4
")
(defconst *bpio-bound*
  (fn-bpio-bound-observation
   *bpo-state* "work:out" "attempt:out" 0 "ipn:2.1" "ipn:1.1"
   *bpio-line*))

; The application peer and BP destination are separate identities.
(assert-event
 (equal *bpio-bound*
        '(:ok (:ion-observed "work:out" "attempt:out" 0
                             "dtn://destination/" "ipn:2.1" "ipn:1.1"
                             843544024799 4))))
(assert-event (fn-bpio-bound-recordp *bpo-state* (cadr *bpio-bound*)))
(assert-event (equal (fn-bpio-decode *bpio-line*)
                     '("dtn://destination/" "ipn:2.1" "ipn:1.1"
                       843544024799 4)))

; Every binding factor matters, including the attempt generation and route.
(assert-event (equal (car (fn-bpio-bound-observation
                            *bpo-state* "work:out" "attempt:stale" 0
                            "ipn:2.1" "ipn:1.1" *bpio-line*)) :error))
(assert-event (equal (car (fn-bpio-bound-observation
                            *bpo-state* "work:out" "attempt:out" 1
                            "ipn:2.1" "ipn:1.1" *bpio-line*)) :error))
(assert-event (equal (car (fn-bpio-bound-observation
                            *bpo-state* "work:out" "attempt:out" 0
                            "ipn:9.1" "ipn:1.1" *bpio-line*)) :error))
(assert-event (equal (car (fn-bpio-bound-observation
                            *bpo-state* "work:out" "attempt:out" 0
                            "ipn:2.1" "ipn:9.1" *bpio-line*)) :error))
(assert-event (equal (car (fn-bpio-bound-observation
                            *bpo-state* "work:out" "attempt:out" 0
                            "ipn:2.1" "ipn:1.1"
                            "observed-v1|dtn://other/|ipn:2.1|ipn:1.1|843544024799|4
")) :error))

; Missing/malformed observations do not establish that no send happened.
(assert-event (null (fn-bpio-decode
                     "observed-v1|dtn://destination/|ipn:2.1|ipn:1.1|01|4
")))
(assert-event (null (fn-bpio-decode
                     "observed-v1|dtn://destination/|ipn:2.1|ipn:1.1|1|4")))
(assert-event (null (fn-bpio-decode
                     "observed-v1|dtn://destination/|ipn:2.1|ipn:1.1|18446744073709551616|4
")))
(assert-event (null (fn-bpio-decode
                     "observed-v1|dtn://destination/|ipn:2.1|ipn:1.1|1|4294967296
")))
(assert-event (null (fn-bpio-decode 7)))
