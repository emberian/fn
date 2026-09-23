; Executable mixed-history recovery: article -> forwarding pin -> release ->
; article, followed by a fresh replay (the logical reopen boundary).
(in-package "ACL2")
(include-book "../../books/replay")
(include-book "../../books/codec-attach")

(defconst *fn-ser-article-1*
  (fn-record-make 0 0 0 "<one@example.invalid>" '(1 2 3) '("g")
                  "archive-1" "subject-1" "post-1" 3 841000000))
(defconst *fn-ser-undertake*
  (fn-store-retention-event-make :undertake 1 1 1
                                 "forward-1" "subject-1" "forward-proof" 5))
(defconst *fn-ser-release*
  (fn-store-retention-event-make :release 2 2 2
                                 "forward-1" "subject-1" "forward-proof" 0))
(defconst *fn-ser-article-2*
  (fn-record-make 3 3 3 "<two@example.invalid>" '(4 5 6) '("g")
                  "archive-2" "subject-2" "post-2" 4 841000000))
(defconst *fn-ser-history*
  (list *fn-ser-article-1* *fn-ser-undertake* *fn-ser-release*
        *fn-ser-article-2*))
(defconst *fn-ser-open* (fn-replay '("g") 32 *fn-ser-history*))

(assert-event (equal (fn-replay-result-kind *fn-ser-open*) :ok))
(assert-event (equal (fn-replay-result-sequence *fn-ser-open*) 4))
(assert-event
 (equal (len (fn-state-articles
              (fn-node-acceptance (fn-replay-result-node *fn-ser-open*))))
        2))
(assert-event
 (equal (fn-retain-find-id
         "forward-1"
         (fn-retain-pins
          (fn-node-retention (fn-replay-result-node *fn-ser-open*))))
        nil))
(assert-event
 (consp (fn-retain-find-id
         "archive-1"
         (fn-retain-pins
          (fn-node-retention (fn-replay-result-node *fn-ser-open*))))))
(assert-event
 (consp (fn-retain-find-id
         "archive-2"
         (fn-retain-pins
          (fn-node-retention (fn-replay-result-node *fn-ser-open*))))))

; Reopening from the same immutable bytes is deterministic and does not
; resurrect the released forwarding pin.
(assert-event
 (equal (fn-replay '("g") 32 *fn-ser-history*) *fn-ser-open*))

; Consumer metadata occupies the same dense journal sequence and allocator
; txid stream.  This node replay arm is deliberately acceptance-neutral: it
; cannot by itself claim that a registration or ack projection was reopened.
(defconst *fn-ser-consumer-history*
  (list (fn-cpe-make 0 0 0 '(:bootstrap (1) (2)))
        (fn-cpe-make 1 1 1 '(:register (3) (4) (5) 1 1 1))
        (fn-record-make 2 2 2 "<after-consumer@example.invalid>" '(9)
                        '("g") "archive-c" "subject-c" "post-c" 1 :legacy)))
(defconst *fn-ser-consumer-open*
  (fn-replay '("g") 32 *fn-ser-consumer-history*))
(assert-event (equal (fn-replay-result-kind *fn-ser-consumer-open*) :ok))
(assert-event (equal (fn-replay-result-sequence *fn-ser-consumer-open*) 3))
(assert-event
 (equal (fn-state-next-txid
         (fn-node-acceptance (fn-replay-result-node *fn-ser-consumer-open*)))
        3))
(assert-event
 (equal (len (fn-state-articles
              (fn-node-acceptance (fn-replay-result-node *fn-ser-consumer-open*))))
        1))
(assert-event (equal (fn-replay '("g") 32 *fn-ser-consumer-history*)
                     *fn-ser-consumer-open*))
