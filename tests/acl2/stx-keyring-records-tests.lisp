; Witnesses and hypothesis teeth for ordered keyring/verdict replay.
(in-package "ACL2")
(include-book "../../books/stx-keyring-records")

(defconst *stxk-profile* '(111 112 97 113 117 101 45 118 49))
(defconst *stxk-one* (fn-stxk-make 0 10 20 7 *stxk-profile* '(1 2 3 4)))
(defconst *stxk-same* (fn-stxk-make 1 11 21 7 *stxk-profile* '(1 2 3 4)))
(defconst *stxk-conflict* (fn-stxk-make 1 11 21 7 *stxk-profile* '(1 2 3 5)))
(defconst *stxk-two* (fn-stxk-make 2 12 22 8 *stxk-profile* '(9 8 7)))
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

; Sequence ordering has teeth independently of generation references.
(defconst *stxk-out-of-order*
  (fn-stxk-apply-snapshot (fn-stxk-initial-context 0) *stxk-two*))
(assert-event (equal (fn-stxk-context-kind *stxk-out-of-order*) :fault))
(assert-event (equal (fn-stxk-context-tail *stxk-out-of-order*) :sequence))
