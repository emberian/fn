; Executable integration scenarios for acceptance plus retention.
(in-package "ACL2")
(include-book "../../books/node")

(defconst *node-groups* '("fn.letters" "fn.test"))
(defconst *node-payload* '(72 105 13 10))
(defconst *node-empty* (fn-node-initial-state *node-groups* 8))
(assert-event (fn-node-statep *node-empty*))

; A resource refusal changes neither the acceptance nor retention component.
(assert-event
 (equal (fn-node-prepare *node-empty* 9 "<a@example.invalid>" *node-payload*
                         *node-groups* "archive-a" "content-a" "release-a" 9)
        *node-empty*))

; The successful preparation stages both sides but publishes neither groups nor
; a committed archive pin.  The archive subject is not the Message-ID.
(defconst *node-prepared*
  (fn-node-prepare *node-empty* 9 "<a@example.invalid>" *node-payload*
                   *node-groups* "archive-a" "content-a" "release-a" 5))
(assert-event (fn-node-statep *node-prepared*))
(assert-event (equal (fn-state-articles
                      (fn-node-acceptance *node-prepared*)) nil))
(assert-event (equal (fn-retain-reserved
                      (fn-node-retention *node-prepared*)) 0))
(assert-event (equal (fn-retain-reserved
                      (fn-node-stage-retention (fn-node-stage *node-prepared*)))
                     5))
(assert-event
 (equal (fn-node-stage-subject (fn-node-stage *node-prepared*)) "content-a"))

; The reservation blocks competing work before durable completion.
(assert-event
 (equal (fn-node-prepare *node-prepared* 9 "<b@example.invalid>" *node-payload*
                         '("fn.letters") "archive-b" "content-b" "release-b" 4)
        *node-prepared*))

; Wrong transaction/generation cannot publish either component.
(assert-event
 (equal (fn-node-complete *node-prepared* 1 9 :durable) *node-prepared*))
(assert-event
 (equal (fn-node-complete *node-prepared* 0 10 :durable) *node-prepared*))

; A caller cannot swap a content subject into the staged prospective retention
; state: the correlated stage is not a node state and therefore cannot publish.
(defconst *node-subject-mismatch*
  (fn-node-make-state
   (fn-node-acceptance *node-prepared*)
   (fn-node-retention *node-prepared*)
   (fn-node-make-stage "<a@example.invalid>" 9 "archive-a" "other-content"
                       "release-a" 5
                       (fn-node-stage-retention (fn-node-stage *node-prepared*)))
   (fn-node-bindings *node-prepared*)))
(assert-event (not (fn-node-statep *node-subject-mismatch*)))
(assert-event
 (equal (fn-node-complete *node-subject-mismatch* 0 9 :durable)
        *node-subject-mismatch*))

; Matching durable completion publishes both local memberships atomically and
; commits exactly the staged pin.
(defconst *node-committed* (fn-node-complete *node-prepared* 0 9 :durable))
(assert-event (fn-node-statep *node-committed*))
(assert-event (fn-statep (fn-node-acceptance *node-committed*)))
(assert-event (fn-retain-statep (fn-node-retention *node-committed*)))
(assert-event (equal (len (fn-state-articles
                           (fn-node-acceptance *node-committed*)) ) 1))
(assert-event (equal (fn-retain-reserved
                      (fn-node-retention *node-committed*)) 5))
(assert-event (equal (len (fn-retain-pins
                           (fn-node-retention *node-committed*))) 1))
(assert-event (equal (fn-node-stage *node-committed*) nil))

; A lost success/retry is a duplicate and cannot allocate another pin.
(assert-event
 (equal (fn-node-prepare *node-committed* 9 "<a@example.invalid>" *node-payload*
                         *node-groups* "archive-retry" "other-subject"
                         "other-release" 1)
        *node-committed*))

; A known abort releases the staged capacity and consumes the acceptance txid.
(defconst *node-abort-prepared*
  (fn-node-prepare *node-committed* 9 "<b@example.invalid>" *node-payload*
                   '("fn.letters") "archive-b" "content-b" "release-b" 2))
(defconst *node-aborted* (fn-node-complete *node-abort-prepared* 1 9 :aborted))
(assert-event (equal (fn-retain-reserved (fn-node-retention *node-aborted*)) 5))
(assert-event (equal (fn-state-next-txid (fn-node-acceptance *node-aborted*)) 2))
(assert-event (equal (fn-node-stage *node-aborted*) nil))

; An indeterminate result fences both ordinary submission and finalization;
; recovery alone chooses whether to promote or discard the staged archive pin.
(defconst *node-uncertain-prepared*
  (fn-node-prepare *node-aborted* 9 "<b@example.invalid>" *node-payload*
                   '("fn.letters") "archive-b" "content-b" "release-b" 2))
(defconst *node-uncertain*
  (fn-node-complete *node-uncertain-prepared* 2 9 :indeterminate))
(assert-event (equal (fn-state-fenced (fn-node-acceptance *node-uncertain*)) t))
(assert-event (consp (fn-node-stage *node-uncertain*)))
(assert-event
 (equal (fn-node-prepare *node-uncertain* 9 "<c@example.invalid>" *node-payload*
                         '("fn.test") "archive-c" "content-c" "release-c" 1)
        *node-uncertain*))
(defconst *node-recovered-absent*
  (fn-node-recover *node-uncertain* 2 9 :absent))
(assert-event (fn-node-statep *node-recovered-absent*))
(assert-event (equal (fn-retain-reserved
                      (fn-node-retention *node-recovered-absent*)) 5))
(assert-event (equal (fn-node-stage *node-recovered-absent*) nil))

; The committed recovery branch installs both the article and the exact staged
; archive pin, never a caller-supplied mismatch.
(defconst *node-recovered-committed*
  (fn-node-recover *node-uncertain* 2 9 :committed))
(assert-event (fn-node-statep *node-recovered-committed*))
(assert-event (equal (len (fn-state-articles
                           (fn-node-acceptance *node-recovered-committed*))) 2))
(assert-event (equal (fn-retain-reserved
                      (fn-node-retention *node-recovered-committed*)) 7))
(assert-event (equal (fn-retain-obligation-subject
                      (fn-retain-find-id
                       "archive-b"
                       (fn-retain-pins
                        (fn-node-retention *node-recovered-committed*))))
                     "content-b"))

; Recognizer boundaries: the two proposals exist together, and each committed
; article has its own charged archive obligation and unique Message-ID binding.
(assert-event
 (not (fn-node-statep
       (fn-node-make-state (fn-node-acceptance *node-prepared*)
                           (fn-node-retention *node-prepared*) nil nil))))
(assert-event
 (not (fn-node-statep
       (fn-node-make-state (fn-node-acceptance *node-empty*)
                           (fn-node-retention *node-empty*)
                           (fn-node-stage *node-prepared*) nil))))
(assert-event
 (not (fn-node-statep
       (fn-node-make-state
        (fn-node-acceptance *node-recovered-committed*)
        (fn-node-retention *node-recovered-committed*) nil
        (list (fn-node-make-binding "<a@example.invalid>" "content-a" "archive-a")
              (fn-node-make-binding "<b@example.invalid>" "content-a" "archive-a"))))))
(assert-event
 (not (fn-node-statep
       (fn-node-make-state
        (fn-node-acceptance *node-committed*)
        (fn-node-retention *node-committed*) nil
        (append (fn-node-bindings *node-committed*)
                (fn-node-bindings *node-committed*))))))
(assert-event
 (not (fn-node-statep
       (fn-node-make-state
        (fn-node-acceptance *node-empty*)
        (fn-node-retention *node-empty*) nil
        (list (fn-node-make-binding "<orphan@example.invalid>" "content" "pin"))))))
(assert-event
 (not (fn-node-binding-listp
       (list (fn-node-make-binding "<same>" "content-a" "archive-a")
             (fn-node-make-binding "<same>" "content-b" "archive-b")))))
(assert-event
 (not (fn-node-binding-listp
       (list (fn-node-make-binding "<a>" "content-a" "same-pin")
             (fn-node-make-binding "<b>" "content-a" "same-pin")))))
