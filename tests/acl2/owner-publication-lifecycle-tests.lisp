; Teeth for books/owner-publication-lifecycle.lisp (ledger RL-02): each
; keystone has a reachable positive witness asserting its whole antecedent and
; conclusion, an affirmative witness for each hypothesis it removes, and a
; must-fail statement with the hypothesis dropped.
(in-package "ACL2")
(include-book "../../books/owner-publication-lifecycle")
(include-book "must-fail-checked")

; --- the classification ------------------------------------------------------
(assert-event (equal (fn-opl-classify '(:unencodable))
                     '(:blocked :blocked-unencodable-history)))
(assert-event (equal (fn-opl-classify '(:image-refused (:refused :pending-suffix)))
                     '(:await-change :retry-on-history-advance-image-suffix)))
(assert-event (equal (fn-opl-classify '(:image-refused (:refused :suffix)))
                     '(:await-change :retry-on-history-advance-image-suffix)))
(assert-event (equal (fn-opl-classify '(:image-refused (:refused :image-count)))
                     '(:blocked :blocked-history-image-refused)))
(assert-event (equal (fn-opl-classify '(:io-refusal))
                     '(:backoff :retry-after-backoff-store-io-refusal)))
(assert-event (equal (fn-opl-classify '(:job-failure :os-error))
                     '(:backoff :retry-after-backoff-job-failure)))
; an outcome nobody classified is retried under the backoff, never taken as
; permanent and never for free
(assert-event (equal (fn-opl-classify '(:something-new))
                     '(:backoff :retry-after-backoff-unclassified)))
(assert-event (equal (fn-opl-classify nil)
                     '(:backoff :retry-after-backoff-unclassified)))

; --- the backoff ---------------------------------------------------------------
(assert-event (equal (fn-opl-delay 1) 30000))
(assert-event (equal (fn-opl-delay 2) 60000))
(assert-event (equal (fn-opl-delay 5) 480000))
(assert-event (equal (fn-opl-delay 6) 900000))
(assert-event (equal (fn-opl-delay 1000000) 900000))
(assert-event (equal (fn-opl-delay nil) 30000))

; --- KEYSTONE fn-opl-settle-releases-the-holder, positive witness: a
; publication that captured at count 64 holds the slot; nothing else does.
(assert-event (fn-opl-holdsp 64 nil 64))
(assert-event (fn-opl-holdsp 64 :dry-run 64))
(assert-event
 (equal (fn-opl-settle 64 '(:unencodable) 1000 nil 64 nil)
        (list nil nil
              '(:deferred :blocked-unencodable-history 1 30000 :blocked 1 0 64))))
; the run of abandonments is counted and the next one waits longer
(assert-event
 (equal (fn-opl-settle 65 '(:io-refusal) 2000 nil 65
                       '(:deferred :retry-after-backoff-store-io-refusal 1 30000 :backoff 1 31000 64))
        (list nil nil
              '(:deferred :retry-after-backoff-store-io-refusal 2 60000 :backoff 2 62000 65))))

; --- KEYSTONE fn-opl-settle-never-touches-another-capture: the hypothesis
; (not holdsp) removed, affirmatively: a late settlement of A (count 64) while B
; (count 80) holds the slot changes nothing, and its deferral stands
(assert-event (not (fn-opl-holdsp 64 nil 80)))
(assert-event
 (equal (fn-opl-settle 64 '(:unencodable) 3000 nil 80 '(:deferred :x 1 2 :backoff 1 5 6))
        (list nil 80 '(:deferred :x 1 2 :backoff 1 5 6))))
; the slot held by nobody: nothing to settle
(assert-event (not (fn-opl-holdsp 64 nil nil)))
(assert-event (equal (fn-opl-settle 64 '(:unencodable) 3000 nil nil nil) (list nil nil nil)))
; a writing reclaim pass holds the slot at the same count: the publication's
; settlement releases nothing of the pass's
(assert-event (not (fn-opl-holdsp 64 :reclaim 64)))
(assert-event (equal (fn-opl-settle 64 '(:unencodable) 3000 :reclaim 64 nil)
                     (list :reclaim 64 nil)))

; --- KEYSTONE fn-opl-settle-is-once: the second settlement is the identity
(assert-event
 (let ((r (fn-opl-settle 64 '(:unencodable) 1000 nil 64 nil)))
   (equal (fn-opl-settle 64 '(:io-refusal) 9000 (car r) (cadr r) (caddr r)) r)))

; --- the due decision after a settlement: the slot is free; with the deferral
; standing the decision is :blocked, and with nothing standing the rule's
(assert-event (equal (fn-ock-publication-next 0 64 128 64 nil t) :blocked))
(assert-event (equal (fn-ock-publication-next 0 64 128 64 64 t) :inflight))
(assert-event (not (equal (fn-ock-publication-next 0 64 128 nil nil t) :inflight)))

; --- eligibility.  :blocked: never, at any count or time
(assert-event
 (let ((d (fn-opl-record '(:unencodable) 64 1000 nil)))
   (and (not (fn-opl-eligiblep d 64 1000))
        (not (fn-opl-eligiblep d 1000000 100000000))
        (fn-opl-blockedp d 0 nil 1000000 100000000))))
; :backoff: by the clock alone.  Recorded at 1000 with a 30000 backoff.
(assert-event
 (let ((d (fn-opl-record '(:io-refusal) 64 1000 nil)))
   (and (equal (nth 6 d) 31000)
        (not (fn-opl-eligiblep d 64 30999))
        (not (fn-opl-eligiblep d 100000 30999))      ; a thousand POSTs do not help
        (fn-opl-eligiblep d 64 31000)
        (fn-opl-eligiblep d 64 900000000)
        (fn-opl-blockedp d 0 nil 100000 30999)
        (not (fn-opl-blockedp d 0 nil 64 31000)))))
; :await-change: both the history advanced past the capture and the backoff over
(assert-event
 (let ((d (fn-opl-record '(:image-refused (:refused :pending-suffix)) 64 1000 nil)))
   (and (equal (nth 4 d) :await-change)
        (not (fn-opl-eligiblep d 64 900000))         ; time without the dependency
        (not (fn-opl-eligiblep d 65 30999))          ; the dependency without the time
        (fn-opl-eligiblep d 65 31000))))
; a clock that could not be read never makes a record eligible
(assert-event (not (fn-opl-eligiblep (fn-opl-record '(:io-refusal) 64 1000 nil) 64 nil)))

; --- a deferral that is not an abandonment keeps the old decision
(assert-event (equal (fn-opl-blockedp '(:deferred :exceeds-budget 900 800) 800 nil 0 0) t))
(assert-event (equal (fn-opl-blockedp '(:deferred :exceeds-budget 900 800) 1000 nil 0 0) nil))
(assert-event (equal (fn-opl-blockedp nil 800 nil 0 0) nil))

; --- the record is read as a deferral by what reads one: health holds it
(assert-event (equal (car (fn-opl-record '(:unencodable) 64 1000 nil)) :deferred))

; --- must-fail: each hypothesis dropped
(must-fail-checked
 (defthm opl-settle-touches-any-capture
   (equal (fn-opl-settle count outcome now pass inflight deferred)
          (list pass nil (fn-opl-record outcome count now deferred)))
   :rule-classes nil))
(must-fail-checked
 (defthm opl-backoff-eligibility-reads-the-clock-only-for-blocked
   (implies (equal (nth 4 d) :await-change)
            (equal (fn-opl-eligiblep d c1 now) (fn-opl-eligiblep d c2 now)))
   :rule-classes nil))
(must-fail-checked
 (defthm opl-await-change-is-eligible-after-the-cap-alone
   (implies (and (natp now) (natp later) (natp count)
                 (<= (+ now *fn-opl-backoff-cap-ms*) later)
                 (equal (nth 4 (fn-opl-record outcome c0 now prev)) :await-change))
            (fn-opl-eligiblep (fn-opl-record outcome c0 now prev) count later))
   :rule-classes nil))
(must-fail-checked
 (defthm opl-settle-is-once-without-the-holder-test
   (equal (fn-opl-settle count o1 now pass inflight deferred)
          (fn-opl-settle count o2 now pass inflight deferred))
   :rule-classes nil))
