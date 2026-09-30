(in-package "ACL2")
(include-book "../../books/replay-identity-continuation")
(defmacro rpx-test-next2 (s) `(mv-let (word next) (fn-rpx-step ,s) (declare (ignore word)) next))
(defmacro rpx-test-word (s) `(mv-let (word next) (fn-rpx-step ,s) (declare (ignore next)) word))
(defmacro rpx-test-public (ctx event)
 `(mv-let (ctx effect child sizes) (fn-rpe-produced-effects ,ctx ,event)
   (list ctx effect child sizes)))
(defconst *rpx-test-a* (fn-stxk-make 0 0 0 3 '(1) '(2)))
(defconst *rpx-test-b* (fn-stxk-make 1 1 1 4 '(3) '(4)))
; Actual initial snapshot completes after the existing empty-tail cursor step.
(assert-event
 (let* ((ctx (fn-stxk-initial-context 0))
        (start (fn-rpx-begin ctx *rpx-test-a* '(7 0 0 0 :identity)))
        (end (rpx-test-next2 start)))
  (and (eq (fn-rsc-at 0 start) :snapshot)
       (fn-rpx-selected-relationp start)
       (eq (fn-rsc-at 0 end) :done)
       (equal (fn-rsc-at 7 end) (rpx-test-public ctx *rpx-test-a*))
       (eq (fn-rsc-at 1 (fn-rsc-at 7 end)) :snapshot))))
; One borrowed retained cell is inspected before the missing-generation end.
(assert-event
 (let* ((ctx (fn-stxk-context :ok 1 (list *rpx-test-a*) nil 3 nil))
        (start (fn-rpx-begin ctx *rpx-test-b* '(7 1 1 1 :identity)))
        (middle (rpx-test-next2 start)) (end (rpx-test-next2 middle)))
  (and (fn-rpx-selected-relationp start)
       (eq (rpx-test-word start) :working)
       (null (fn-rsc-at 2 (fn-rsc-at 6 middle)))
       (equal (fn-rsc-at 7 end) (rpx-test-public ctx *rpx-test-b*)))))
; Existing snapshot is selected without changing the retained graph.
(assert-event
 (let* ((ctx (fn-stxk-context :ok 0 (list *rpx-test-a*) nil 3 nil))
        (end (rpx-test-next2
              (fn-rpx-begin ctx *rpx-test-a* '(7 1 0 0 :identity)))))
  (and (equal (fn-rsc-at 7 end) (rpx-test-public ctx *rpx-test-a*))
       (eq (fn-rsc-at 1 (fn-rsc-at 7 end)) :none))))
; Sequence refusal is complete before any retained selector/producer begins.
(assert-event
 (let* ((ctx (fn-stxk-initial-context 9))
        (end (fn-rpx-begin ctx *rpx-test-a* '(7 0 0 0 :identity))))
  (and (eq (fn-rsc-at 0 end) :done) (null (fn-rsc-at 6 end))
       (equal (fn-rsc-at 7 end) (rpx-test-public ctx *rpx-test-a*)))))
; Complete antecedent/conclusion of whole public result after arbitrary fuel.
(assert-event
 (let* ((ctx (fn-stxk-initial-context 0))
        (end (fn-rpx-run 1 (fn-rpx-begin ctx *rpx-test-a* '(7 0 0 0 :identity)))))
  (and (fn-rsc-typed-snapshotsp (fn-stxk-context-snapshots ctx))
       (eq (fn-rsc-at 0 end) :done)
       (equal (fn-rsc-at 7 end) (rpx-test-public ctx *rpx-test-a*)))))
; Corrupted-state removal of typed snapshot provenance, while completion holds.
; Old FIND rejects a malformed generation match; unchecked RSC would select it.
(assert-event
 (let* ((bad (update-nth 4 :bad *rpx-test-a*))
        (ctx (fn-stxk-context :ok 0 (list bad) nil 2 nil))
        (end (fn-rpx-run 1 (fn-rpx-begin ctx *rpx-test-a* '(7 1 0 0 :identity)))))
  (and (not (fn-rsc-typed-snapshotsp (fn-stxk-context-snapshots ctx)))
       (eq (fn-rsc-at 0 end) :done)
       (not (equal (fn-rsc-at 7 end) (rpx-test-public ctx *rpx-test-a*))))))
; Removal of completion: valid source and zero quantum retain pending work.
(assert-event
 (let* ((ctx (fn-stxk-initial-context 0))
        (end (fn-rpx-run 0 (fn-rpx-begin ctx *rpx-test-a* '(7 0 0 0 :identity)))))
  (and (fn-rsc-typed-snapshotsp (fn-stxk-context-snapshots ctx))
       (not (eq (fn-rsc-at 0 end) :done))
       (not (equal (fn-rsc-at 7 end) (rpx-test-public ctx *rpx-test-a*))))))
