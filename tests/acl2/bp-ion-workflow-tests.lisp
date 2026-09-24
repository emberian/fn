(in-package "ACL2")
(include-book "bp-ion-observation-tests")
(include-book "../../books/bp-ion-workflow")

(defconst *bpiw-route*
  '(:ion-route "work:out" "attempt:out" 0
               "dtn://destination/" "ipn:2.1" "ipn:1.1"))
(assert-event
 (equal (fn-bpiw-attempt-record
         (nth 1 *bpo-enqueued*) 11 0 "work:out" "attempt:out")
        *bpo-attempt-record*))
(assert-event
 (equal (fn-bpiw-route-record
         *bpo-state* (fn-bpiw-initial) "work:out" "attempt:out" 0
         "ipn:2.1" "ipn:1.1")
        *bpiw-route*))
(defconst *bpiw-routed*
  (fn-bpiw-apply *bpo-state* (fn-bpiw-initial) *bpiw-route*))
(assert-event (car *bpiw-routed*))
(assert-event
 (equal (car (fn-bpiw-status (nth 3 *bpiw-routed*)
                              "work:out" "attempt:out" 0)) :uncertain))
(assert-event (equal (nth 1 *bpiw-routed*) *bpo-state*))
(assert-event (null (nth 2 *bpiw-routed*)))

(defconst *bpiw-observed*
  (fn-bpiw-apply *bpo-state* (nth 3 *bpiw-routed*)
                 (cadr *bpio-bound*)))
(assert-event (car *bpiw-observed*))
(assert-event
 (equal (car (fn-bpiw-status (nth 3 *bpiw-observed*)
                              "work:out" "attempt:out" 0)) :observed))
(assert-event
 (equal (fn-bpiw-observation-record
         *bpo-state* (nth 3 *bpiw-routed*) "work:out" "attempt:out" 0
         "ipn:2.1" "ipn:1.1" *bpio-line*)
        (cadr *bpio-bound*)))
(assert-event (equal (nth 1 *bpiw-observed*) *bpo-state*))
(assert-event (equal (fn-bpiw-find-key
                      '("work:out" "attempt:out" 0)
                      (fn-bpiw-observations (nth 3 *bpiw-observed*)))
                     (cadr *bpio-bound*)))

; A missing route, a second ID for one attempt, and a route substitution
; cannot turn transport evidence into a different durable attempt.
(assert-event
 (not (car (fn-bpiw-apply *bpo-state* (fn-bpiw-initial)
                           (cadr *bpio-bound*)))))
(assert-event
 (not (car (fn-bpiw-apply *bpo-state* (nth 3 *bpiw-observed*)
                           (cadr *bpio-bound*)))))
(assert-event
 (not (car (fn-bpiw-apply
            *bpo-state* (fn-bpiw-initial)
            '(:ion-route "work:out" "attempt:out" 0
                         "dtn://wrong/" "ipn:2.1" "ipn:1.1")))))
(assert-event
 (not (car (fn-bpiw-apply
            *bpo-state* (nth 3 *bpiw-routed*)
            '(:ion-observed "work:out" "attempt:out" 0
                            "dtn://destination/" "ipn:3.1" "ipn:1.1"
                            843544024799 4)))))

; Recovery reconstructs the observation only after replaying the durable
; attempt and route. A second observation for that attempt faults the image.
(defconst *bpiw-prefix*
  (list *bpo-config-record* *bpo-enqueue-record*
        '(:outcome 10 0 :ordinary :durable)
        *bpo-attempt-record*
        '(:outcome 11 0 :ordinary :durable)
        *bpiw-route* (cadr *bpio-bound*)))
(defconst *bpiw-recovered*
  (fn-bpiw-replay-journal *bpo-node* *bpiw-prefix*))
(assert-event (car *bpiw-recovered*))
(assert-event
 (equal (fn-bpiw-find-key
         '("work:out" "attempt:out" 0)
         (fn-bpiw-observations (nth 3 *bpiw-recovered*)))
        (cadr *bpio-bound*)))
(assert-event
 (equal (car (fn-bpiw-status (nth 3 *bpiw-recovered*)
                              "work:out" "attempt:out" 0)) :observed))
(assert-event
 (not (car (fn-bpiw-replay-journal
            *bpo-node* (append *bpiw-prefix* (list (cadr *bpio-bound*)))))))
