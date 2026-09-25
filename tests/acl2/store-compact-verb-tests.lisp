; Witnesses and teeth for books/store-compact-verb.
(in-package "ACL2")
(include-book "../../books/store-compact-verb")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/codec-attach")

; A reachable five-event history (the one checkpoint-compaction-preservation
; tests): a record, an undertaking, its release, an identity event and an
; enrollment, at txids 0..4 under frontier 6.
(defconst *cvt-a0*
  (fn-record-make 0 0 0 "<compact@example.invalid>" '(65 13 10)
                  '("fn.letters") "archive-0" "subject-0" "evidence-0" 3 841000000))
(defconst *cvt-e1*
  (fn-store-retention-event-make :undertake 1 1 1
                                 "forward-1" "subject-1" "evidence-1" 2))
(defconst *cvt-e2*
  (fn-store-retention-event-make :release 2 2 2
                                 "forward-1" "subject-1" "receipt-1" 0))
(defconst *cvt-i3*
  (fn-stxe-make 3 3 3 "<compact@example.invalid>" :unverified
                '(117 110 118 101 114 105 102 105 101 100) 7 '(116 101 115 116)))
(defconst *cvt-k4*
  (fn-stxk-make 4 4 4 7 '(116 101 115 116) '(1 2 3 4)))
(make-event `(defconst *cvt-records*
               ',(list (fn-store-event-encode *cvt-a0*)
                       (fn-store-event-encode *cvt-e1*)
                       (fn-store-event-encode *cvt-e2*)
                       (fn-store-event-encode *cvt-i3*)
                       (fn-store-event-encode *cvt-k4*))))
(make-event `(defconst *cvt-names*
               ',(list (fn-bs-txn-name 0) (fn-bs-txn-name 1) (fn-bs-txn-name 2)
                       (fn-bs-txn-name 3) (fn-bs-txn-name 4))))
(defconst *cvt-dev* *fn-bs-profile-development*)
(defconst *cvt-footprint* '(212 150 150 180 170))

(assert-event (fn-cc-octet-event-listp *cvt-records* 0 0 6))

; Reachable, non-degenerate: a fresh development store with five
; transaction files and no pack packs, selects, reclaims and retires.  The
; pack the capture produces fits the budget with the files beside it.
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 0 *cvt-names* nil nil *cvt-footprint*)
        (list :compact *fn-cverb-pack-steps*)))
(assert-event (equal (car (fn-cc-capture *cvt-records* 6)) :ok))
(assert-event
 (<= (+ (fn-cverb-octet-sum *cvt-footprint*)
        (len (fn-cc-encode (fn-cc-nth 1 (fn-cc-capture *cvt-records* 6))))
        *fn-frame-trailer-octets*)
     (fn-bs-profile-max-history-octets *cvt-dev*)))
; The accounted pack octets are an upper bound of the real payload, and
; close to it: the real encoding is at most 32 + 5 per event smaller.
(assert-event
 (let ((real (len (fn-cc-encode (fn-cc-nth 1 (fn-cc-capture *cvt-records* 6)))))
       (accounted (fn-cc-event-octets-size *cvt-records*)))
   (and (<= real accounted) (<= accounted (+ real 32 25)))))

; Resume: after a cut at or after the selection (pack generation 1 selected,
; generation 0 an older one) the verb reclaims and retires and writes no
; pack; once both are done it is refused as already compact.
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 5 *cvt-names* '(0 1) 1 nil)
        (list :compact *fn-cverb-resume-steps*)))
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 5 nil '(0 1) 1 nil)
        (list :compact *fn-cverb-resume-steps*)))
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 5 *cvt-names* '(1) 1 nil)
        (list :compact *fn-cverb-resume-steps*)))
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 5 nil '(1) 1 nil)
        '(:refused :already-compact)))
; A partly compacted store with new records past the pack packs again.
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 3
                         (list (fn-bs-txn-name 3) (fn-bs-txn-name 4)) '(0) 0 '(300 300 400))
        (list :compact *fn-cverb-pack-steps*)))
; The other refusals, each by name.
(assert-event (equal (fn-cverb-decide *cvt-dev* nil 0 nil nil nil nil)
                     '(:refused :empty-history)))
(assert-event (equal (fn-cverb-decide '(7 1 2 3 4 5) *cvt-records* 0 *cvt-names* nil nil nil)
                     '(:refused :profile)))
(assert-event (equal (fn-cverb-decide *cvt-dev* *cvt-records* 6 *cvt-names* nil nil nil)
                     '(:refused :observation)))

; Temporary space: the same store beside 24 MiB of other history is refused
; before a byte is written.
(defconst *cvt-full* (list (- (fn-bs-profile-max-history-octets *cvt-dev*) 100)))
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 0 *cvt-names* nil nil *cvt-full*)
        '(:refused :temporary-space)))
; Tooth for fn-cverb-pack-fits-the-profile-budget (its one hypothesis):
; without the pack decision the conclusion fails at this footprint.
(local
 (must-fail
  (defthm cvt-budget-without-decision
    (<= (+ (fn-cverb-octet-sum *cvt-full*)
           (len (fn-cc-encode (fn-cc-nth 1 (fn-cc-capture *cvt-records* 6))))
           *fn-frame-trailer-octets*)
        (fn-bs-profile-max-history-octets *cvt-dev*)))))

; The compaction unit: 4097 events (one over the pack's event limit) of a
; valid history.  The decision refuses it by name and so does the capture.
(defun cvt-many (i n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil
    (cons (fn-store-event-encode
           (fn-record-make i i i "<many@example.invalid>" '(65)
                           '("fn.letters") "a" "s" "e" 1 841000000))
          (cvt-many (1+ i) (1- n)))))
(make-event `(defconst *cvt-4097* ',(cvt-many 0 4097)))
(assert-event (fn-cc-octet-event-listp *cvt-4097* 0 0 4097))
(assert-event (equal (fn-cverb-decide *cvt-dev* *cvt-4097* 0 nil nil nil nil)
                     '(:refused :exceeds-compaction-unit)))
(assert-event (not (equal (car (fn-cc-capture *cvt-4097* 4097)) :ok)))

; Teeth for fn-cverb-pack-decision-capture-succeeds, one per hypothesis.
; Without the pack decision: the 4097-event history, with a uint32 frontier
; and the exact-event list both holding, is not captured.
(local
 (must-fail
  (defthm cvt-capture-without-decision
    (equal (car (fn-cc-capture *cvt-4097* 4097)) :ok))))
; Without a uint32 frontier: the decision packs and the event list holds
; under frontier 2^32, and the capture refuses.
(assert-event (fn-cc-octet-event-listp *cvt-records* 0 0 4294967296))
(local
 (must-fail
  (defthm cvt-capture-without-uint32-frontier
    (equal (car (fn-cc-capture *cvt-records* 4294967296)) :ok))))
; Without the exact-event list: bytes that are no Store event are packed by
; the decision (it reads sizes only) and refused by the capture.
(assert-event
 (equal (fn-cverb-decide *cvt-dev* '((1 2 3)) 0 (list (fn-bs-txn-name 0)) nil nil nil)
        (list :compact *fn-cverb-pack-steps*)))
(local
 (must-fail
  (defthm cvt-capture-without-event-list
    (equal (car (fn-cc-capture '((1 2 3)) 6)) :ok))))

; Tooth for fn-cverb-preset-count-within-pack-events: a valid operator
; profile that is not a preset -- the D27 defaults -- names more transactions
; than a pack holds, so under it the pack's event limit can be the refusal.
(assert-event (fn-bs-profile-validp *fn-bs-profile-defaults*))
(assert-event (< *fn-cc-max-events*
                 (fn-bs-profile-max-transactions *fn-bs-profile-defaults*)))
(local
 (must-fail
  (defthm cvt-count-without-preset
    (implies (fn-bs-profile-validp profile)
             (<= (fn-bs-profile-max-transactions profile) *fn-cc-max-events*)))))
(assert-event (equal (fn-cverb-decide '(7 1048576 32768 805306368 5000 1)
                                      *cvt-records* 0 *cvt-names* nil nil nil)
                     '(:refused :profile)))

; Finding 3.  The newest record lost and the newest reservation abandoned
; are one observation.  The five-event history at frontier 5 and its
; four-event prefix at the same frontier are both admitted by the open's
; history gate; the prefix is also exactly what the store holds when
; record 4's reservation advanced the frontier to 5 and the process died
; before the record was written (books/replay.lisp, a known-aborted gap).
(defconst *cvt-history* (list *cvt-a0* *cvt-e1* *cvt-e2* *cvt-i3* *cvt-k4*))
(assert-event (fn-sn-observed-historyp 5 *cvt-history*))
(assert-event (fn-sn-observed-historyp 5 (list *cvt-a0* *cvt-e1* *cvt-e2* *cvt-i3*)))
; The namespace gate the same: the five names and the four without the
; newest are both valid observations under the development bound.
(assert-event (not (equal (fn-profile-txn-observation *cvt-names* 128 0) :invalid)))
(assert-event (not (equal (fn-profile-txn-observation (butlast *cvt-names* 1) 128 0)
                          :invalid)))
; Tooth for fn-cverb-open-history-gate-admits-a-lost-suffix (true-listp):
; an improper prefix whose append is the one-event history is not admitted.
(local (defthm cvt-improper-prefix-appends-to-one-event
         (equal (append (cons *cvt-a0* 7) nil) (list *cvt-a0*))))
(assert-event (fn-sn-observed-historyp 5 (list *cvt-a0*)))
(local
 (must-fail
  (defthm cvt-gate-without-true-list
    (fn-sn-observed-historyp 5 (cons *cvt-a0* 7)))))
