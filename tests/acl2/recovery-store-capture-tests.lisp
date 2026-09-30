; Structural literal teeth for the proposed resident Store membership lemma.
; These do not establish capture authority or physical/parser correspondence.
(in-package "ACL2")
(include-book "../../books/recovery-store-capture")

(defconst *fn-rsc-test-row*
 (fn-store-retention-event-make :undertake 0 0 0 "obligation" "subject" "evidence" 1))

; Reachable logical positive: full antecedent and conclusion explicitly checked.
(assert-event
 (and (fn-sf-record-listp (list *fn-rsc-test-row*) 0 0 1)
      (member-equal *fn-rsc-test-row* (list *fn-rsc-test-row*))
      (fn-store-event-p *fn-rsc-test-row*)))

; Hypothesis-removal: retained membership, failed RecordListP, failed conclusion.
; The input is deliberately corrupted; no producer authority is inferred.
(assert-event
 (and (member-equal :invalid-row (list :invalid-row))
      (not (fn-sf-record-listp (list :invalid-row) 0 0 1))
      (not (fn-store-event-p :invalid-row))))

; Hypothesis-removal: retained RecordListP, failed membership and conclusion.
(assert-event
 (and (fn-sf-record-listp nil 0 0 1)
      (not (member-equal :invalid-row nil))
      (not (fn-store-event-p :invalid-row))))
