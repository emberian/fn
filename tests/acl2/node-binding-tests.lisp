; Required transaction-stage descriptor, through the actual node entry.
(in-package "ACL2")
(include-book "../../books/node-invariants")

(defconst *nbt-binding*
  (fn-ab-make :relay-v1
    (append *fn-ab-subject-head* (make-list 32 :initial-element 7))))
(defconst *nbt-empty* (fn-node-initial-state '("fn.test") 16))
(defconst *nbt-prepared*
  (fn-node-prepare *nbt-empty* 1 "<bound@example>" 0 '("fn.test")
                   "archive" "content" "release" 4 841000000 *nbt-binding*))

; Literal full antecedent/conclusion, plus executable guards and nonempty
; prospective retention. The descriptor survives independently of subject.
(assert-event
 (and (fn-node-statep *nbt-empty*)
      (not (equal *nbt-prepared* *nbt-empty*))
      (fn-ab-p *nbt-binding*)
      (equal (fn-node-stage-binding (fn-node-stage *nbt-prepared*)) *nbt-binding*)
      (fn-node-statep *nbt-prepared*)
      (equal (len (fn-retain-pins
                   (fn-node-stage-retention (fn-node-stage *nbt-prepared*)))) 1)))

; Hypothesis removal: unchanged refusal has no staged descriptor. No other
; theorem hypothesis is retained. The actual entry guard still holds.
(assert-event
 (let ((next (fn-node-prepare *nbt-empty* 1 "<bound@example>" 0 '("fn.test")
                              "archive" "content" "release" 4 841000000 :invalid)))
   (and (fn-node-statep *nbt-empty*)
        (equal next *nbt-empty*)
        (not (and (fn-ab-p :invalid)
                  (equal (fn-node-stage-binding (fn-node-stage next)) :invalid))))))

; Corrupted-state witness: all previous stage fields remain exact; truncating
; the mandatory descriptor rejects the node rather than defaulting a profile.
(assert-event
 (let* ((stage (fn-node-stage *nbt-prepared*))
        (old-shape (take 7 stage))
        (bad (fn-node-make-state (fn-node-acceptance *nbt-prepared*)
                                 (fn-node-retention *nbt-prepared*) old-shape
                                 (fn-node-bindings *nbt-prepared*))))
   (and (equal (len stage) 8)
        (equal (take 7 stage) old-shape)
        (not (fn-node-stagep (fn-node-acceptance bad)
                             (fn-node-retention bad) old-shape))
        (not (fn-node-statep bad)))))
