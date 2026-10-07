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

;; --- KEYSTONE fn-opl-settle-releases-the-holder, positive witness: the
; publication that captured at count 64 as capture 7 holds the slot while the
; owner's serial is 7; nothing else does.
(assert-event (fn-opl-holdsp 64 7 nil 64 7))
(assert-event (fn-opl-holdsp 64 7 :dry-run 64 7))
(assert-event
 (equal (fn-opl-settle 64 7 '(:unencodable) 1000 nil 64 7 nil)
        (list nil nil
              '(:deferred :blocked-unencodable-history 1 0 :blocked 1 0 64))))
; the run of abandonments is counted and the next one waits longer
(assert-event
 (equal (fn-opl-settle 65 8 '(:io-refusal) 2000 nil 65 8
                       '(:deferred :retry-after-backoff-store-io-refusal 1 30000 :backoff 1 31000 64))
        (list nil nil
              '(:deferred :retry-after-backoff-store-io-refusal 2 60000 :backoff 2 62000 65))))

; --- KEYSTONE fn-opl-settle-never-touches-another-capture: the hypothesis
; (not holdsp) removed, affirmatively: a late settlement of A (count 64) while B
; (count 80) holds the slot changes nothing, and its deferral stands
(assert-event (not (fn-opl-holdsp 64 7 nil 80 8)))
(assert-event
 (equal (fn-opl-settle 64 7 '(:unencodable) 3000 nil 80 8 '(:deferred :x 1 2 :backoff 1 5 6))
        (list nil 80 '(:deferred :x 1 2 :backoff 1 5 6))))
; --- KEYSTONE fn-opl-late-settlement-of-a-cannot-release-b: B retried A's
; count 64 (a :backoff retry with no commit between); A's serial 7 is not the
; owner's serial 8, so A's late settlement releases nothing of B's
(assert-event (not (fn-opl-holdsp 64 7 nil 64 (fn-opl-next-serial 7))))
(assert-event
 (equal (fn-opl-settle 64 7 '(:unencodable) 3000 nil 64 (fn-opl-next-serial 7)
                       '(:deferred :retry-after-backoff-store-io-refusal 1 30000 :backoff 1 31000 64))
        (list nil 64 '(:deferred :retry-after-backoff-store-io-refusal 1 30000 :backoff 1 31000 64))))
; ... while B itself, serial 8, does
(assert-event (fn-opl-holdsp 64 8 nil 64 (fn-opl-next-serial 7)))
; the slot held by nobody: nothing to settle
(assert-event (not (fn-opl-holdsp 64 7 nil nil 7)))
(assert-event (equal (fn-opl-settle 64 7 '(:unencodable) 3000 nil nil 7 nil) (list nil nil nil)))
; a writing reclaim pass holds the slot at the same count: the publication's
; settlement releases nothing of the pass's
(assert-event (not (fn-opl-holdsp 64 7 :reclaim 64 7)))
(assert-event (equal (fn-opl-settle 64 7 '(:unencodable) 3000 :reclaim 64 7 nil)
                     (list :reclaim 64 nil)))

; --- KEYSTONE fn-opl-settle-is-once: the second settlement is the identity
(assert-event
 (let ((r (fn-opl-settle 64 7 '(:unencodable) 1000 nil 64 7 nil)))
   (equal (fn-opl-settle 64 7 '(:io-refusal) 9000 (car r) (cadr r) 7 (caddr r)) r)))

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
   (equal (fn-opl-settle count serial outcome now pass inflight current deferred)
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
   (equal (fn-opl-settle count serial o1 now pass inflight current deferred)
          (fn-opl-settle count serial o2 now pass inflight current deferred))
   :rule-classes nil))
(must-fail-checked
 (defthm opl-late-settlement-releases-nothing-without-the-serial
   (implies (natp a)
            (equal (fn-opl-settle count a outcome now pass inflight current deferred)
                   (list pass inflight deferred)))
   :rule-classes nil))

; --- the due path.  KEYSTONE fn-opl-backoff-is-retried-without-a-commit,
; positive witness: K=128, nothing durable, capture 7 at count 64 (due:
; 2*64 >= 128) abandoned on an I/O refusal at t=1000.  At t=900999 (the cap
; less one) no commit has come: before the backoff (31000) the decision is
; :blocked; from 31000 on it is :due at the SAME count 64.
(assert-event
 (let* ((r (fn-opl-settle 64 7 '(:io-refusal) 1000 nil 64 7 nil))
        (d (caddr r)))
   (and (equal (cadr r) nil)
        (fn-ock-publication-duep 0 64 128 nil)
        (not (fn-ock-publication-duep 0 64 128 64))
        (equal (fn-ock-publication-next 0 64 128 (fn-opl-attempted d 64 64 30999) nil
                                        (fn-opl-blockedp d 0 nil 64 30999))
               :blocked)
        (equal (fn-ock-publication-next 0 64 128 (fn-opl-attempted d 64 64 31000) nil
                                        (fn-opl-blockedp d 0 nil 64 31000))
               :due)
        (equal (fn-ock-publication-next 0 64 128 (fn-opl-attempted d 64 64 901000) nil
                                        (fn-opl-blockedp d 0 nil 64 901000))
               :due))))
; the hypothesis removed: without the attempted override (the old rule) the
; same record, eligible, never captures count 64 again
(assert-event
 (let ((d (fn-opl-record '(:io-refusal) 64 1000 nil)))
   (equal (fn-ock-publication-next 0 64 128 64 nil (fn-opl-blockedp d 0 nil 64 901000))
          :idle)))
; a budget deferral keeps the rule's ATTEMPTED: no same-count retry
(assert-event (equal (fn-opl-attempted '(:deferred :exceeds-budget 900 800) 64 64 901000) 64))
; KEYSTONE fn-opl-blocked-is-never-due: at any count and time
(assert-event
 (let ((d (fn-opl-record '(:unencodable) 64 1000 nil)))
   (and (equal (fn-ock-publication-next 0 64 128 (fn-opl-attempted d 64 64 1000) nil
                                        (fn-opl-blockedp d 0 nil 64 1000))
               :blocked)
        (equal (fn-ock-publication-next 0 100000 128 (fn-opl-attempted d 64 100000 900000000) nil
                                        (fn-opl-blockedp d 0 nil 100000 900000000))
               :blocked))))
; KEYSTONE fn-opl-backoff-is-not-hastened-by-commits: 100000 records later,
; before the backoff, still :blocked; the same count at the backoff, :due
(assert-event
 (let ((d (fn-opl-record '(:io-refusal) 64 1000 nil)))
   (and (equal (fn-ock-publication-next 0 100000 128 (fn-opl-attempted d 64 100000 30999) nil
                                        (fn-opl-blockedp d 0 nil 100000 30999))
               :blocked)
        (equal (fn-ock-publication-next 0 100000 128 (fn-opl-attempted d 64 100000 31000) nil
                                        (fn-opl-blockedp d 0 nil 100000 31000))
               :due))))
(must-fail-checked
 (defthm opl-backoff-is-retried-whatever-the-class
   (implies (and (fn-opl-holdsp count serial pass count current)
                 (natp now) (natp later)
                 (<= (+ now *fn-opl-backoff-cap-ms*) later)
                 (fn-ock-publication-duep durable count k nil))
            (let* ((r (fn-opl-settle count serial outcome now pass count current deferred))
                   (d (caddr r)))
              (equal (fn-ock-publication-next durable count k
                                              (fn-opl-attempted d count count later)
                                              (cadr r)
                                              (fn-opl-blockedp d budget space count later))
                     :due)))
   :rule-classes nil))
(must-fail-checked
 (defthm opl-backoff-is-retried-before-the-cap
   (implies (and (fn-opl-holdsp count serial pass count current)
                 (natp now) (natp later)
                 (equal (car (fn-opl-classify outcome)) :backoff)
                 (fn-ock-publication-duep durable count k nil))
            (let* ((r (fn-opl-settle count serial outcome now pass count current deferred))
                   (d (caddr r)))
              (equal (fn-ock-publication-next durable count k
                                              (fn-opl-attempted d count count later)
                                              (cadr r)
                                              (fn-opl-blockedp d budget space count later))
                     :due)))
   :rule-classes nil))
