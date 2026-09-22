; Witnesses and hypothesis teeth for ordered keyring/verdict replay.
(in-package "ACL2")
(include-book "../../books/store-events")
(include-book "../../books/codec-attach")

(defconst *stxk-profile* '(111 112 97 113 117 101 45 118 49))
(defconst *stxk-one* (fn-stxk-make 0 10 20 7 *stxk-profile* '(1 2 3 4)))
(defconst *stxk-same* (fn-stxk-make 1 11 21 7 *stxk-profile* '(1 2 3 4)))
(defconst *stxk-conflict* (fn-stxk-make 1 11 21 7 *stxk-profile* '(1 2 3 5)))
(defconst *stxk-two* (fn-stxk-make 2 12 22 8 *stxk-profile* '(9 8 7)))
(defconst *stxk-duplicate-one-late*
  (fn-stxk-make 3 13 23 7 *stxk-profile* '(1 2 3 4)))
(defconst *stxk-fresh-older*
  (fn-stxk-make 3 13 23 6 *stxk-profile* '(6 6 6)))
(defconst *stxk-verdict*
  (fn-stxe-make 1 11 21 "<ordered@example.invalid>" :verified
                '(115 105 103 110 97 116 117 114 101) 7 *stxk-profile*))

(assert-event (fn-stxk-p *stxk-one*))
(assert-event
 (equal (fn-stmt-value (fn-stxk-decode-exact (fn-stxk-encode *stxk-one*)))
        *stxk-one*))
(assert-event
 (equal (fn-stxk-snapshot
         (fn-stmt-value (fn-stxk-decode-exact (fn-stxk-encode *stxk-one*))))
        '(1 2 3 4)))

; The advertised snapshot boundary is executable: its canonical encoding is
; larger than the legacy generic CBOR whole-input limit and still round-trips
; through the actual Store-event decoder.
(defconst *stxk-large-snapshot*
  (make-list *fn-stxk-max-snapshot* :initial-element 90))
(defconst *stxk-large*
  (fn-stxk-make 0 10 20 7 *stxk-profile* *stxk-large-snapshot*))
(assert-event (< *fn-cbor-max-input* (len (fn-stxk-encode *stxk-large*))))
(assert-event
 (equal (fn-stmt-value
         (fn-store-event-decode-exact (fn-stxk-encode *stxk-large*)))
        *stxk-large*))

; A verdict naming generation 7 is refused before its snapshot.
(defconst *stxk-missing*
  (fn-stxk-apply-verdict (fn-stxk-initial-context 1) *stxk-verdict*))
(assert-event (equal (fn-stxk-context-kind *stxk-missing*) :fault))
(assert-event (equal (fn-stxk-context-tail *stxk-missing*)
                     :missing-keyring-generation))

; Snapshot then verdict succeeds in the one Store order.
(defconst *stxk-after-one*
  (fn-stxk-apply-snapshot (fn-stxk-initial-context 0) *stxk-one*))
(defconst *stxk-after-verdict*
  (fn-stxk-apply-verdict *stxk-after-one* *stxk-verdict*))
(assert-event (equal (fn-stxk-context-kind *stxk-after-verdict*) :ok))
(assert-event (equal (fn-stxk-context-next *stxk-after-verdict*) 2))
(assert-event (equal (fn-stxk-context-verdicts *stxk-after-verdict*)
                     (list *stxk-verdict*)))

; Repeating identical generation bytes is idempotent; changing them faults.
(assert-event
 (equal (len (fn-stxk-context-snapshots
              (fn-stxk-apply-snapshot *stxk-after-one* *stxk-same*)))
        1))
(defconst *stxk-conflicted*
  (fn-stxk-apply-snapshot *stxk-after-one* *stxk-conflict*))
(assert-event (equal (fn-stxk-context-kind *stxk-conflicted*) :fault))
(assert-event (equal (fn-stxk-context-tail *stxk-conflicted*)
                     :conflicting-keyring-generation))

; Rotation changes only current context.  It never rewrites the recorded
; historical verdict, and unsupported profiles produce no current authority.
(defconst *stxk-rotated*
  (fn-stxk-apply-snapshot *stxk-after-verdict* *stxk-two*))
(assert-event (equal (fn-stxk-context-current-generation *stxk-rotated*) 8))
(assert-event (equal (fn-stxk-context-verdicts *stxk-rotated*)
                     (list *stxk-verdict*)))
(assert-event (equal (fn-stxe-keyring-generation
                      (car (fn-stxk-context-verdicts *stxk-rotated*))) 7))
(assert-event (equal (fn-stxk-current-trust *stxk-rotated*) nil))

; G7 -> G8 -> exact duplicate G7 is a retry, not a rotation back to G7.
(defconst *stxk-duplicate-old*
  (fn-stxk-apply-snapshot *stxk-rotated* *stxk-duplicate-one-late*))
(assert-event (equal (fn-stxk-context-kind *stxk-duplicate-old*) :ok))
(assert-event (equal (fn-stxk-context-current-generation
                      *stxk-duplicate-old*) 8))
(assert-event (equal (fn-stxk-context-verdicts *stxk-duplicate-old*)
                     (list *stxk-verdict*)))

; A previously unseen older generation cannot rotate current trust backward.
(defconst *stxk-fresh-old-fault*
  (fn-stxk-apply-snapshot *stxk-rotated* *stxk-fresh-older*))
(assert-event (equal (fn-stxk-context-kind *stxk-fresh-old-fault*) :fault))
(assert-event (equal (fn-stxk-context-tail *stxk-fresh-old-fault*)
                     :keyring-generation-order))
(assert-event (equal (fn-stxk-context-current-generation
                      *stxk-fresh-old-fault*) 8))

; The monotonicity theorem's sole hypothesis has teeth.  Without the carried
; natural-number generation, the transition cannot apply successor ordering:
; this malformed context reaches a lower numeric generation.
(defconst *stxk-nonnatural-context*
  (fn-stxk-context :ok 0 nil nil 17/2 nil))
(defconst *stxk-from-nonnatural*
  (fn-stxk-apply-snapshot *stxk-nonnatural-context*
                          (fn-stxk-make 0 1 1 1 *stxk-profile* '(1))))
(assert-event
 (not (<= (fn-stxk-context-current-generation *stxk-nonnatural-context*)
          (fn-stxk-context-current-generation *stxk-from-nonnatural*))))

; A verdict is historical evidence about one concrete snapshot profile.
(defconst *stxk-wrong-profile-verdict*
  (fn-stxe-make 1 11 21 "<ordered@example.invalid>" :verified
                '(115 105 103) 7 '(111 116 104 101 114)))
(defconst *stxk-profile-fault*
  (fn-stxk-apply-verdict *stxk-after-one* *stxk-wrong-profile-verdict*))
(assert-event (equal (fn-stxk-context-kind *stxk-profile-fault*) :fault))
(assert-event (equal (fn-stxk-context-tail *stxk-profile-fault*)
                     :keyring-profile-mismatch))

; Sequence ordering has teeth independently of generation references.
(defconst *stxk-out-of-order*
  (fn-stxk-apply-snapshot (fn-stxk-initial-context 0) *stxk-two*))
(assert-event (equal (fn-stxk-context-kind *stxk-out-of-order*) :fault))
(assert-event (equal (fn-stxk-context-tail *stxk-out-of-order*) :sequence))
