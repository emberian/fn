; Logical malformed-source witness, not a served caller or an execution claim.
(in-package "ACL2")
(include-book "../books/checkpoint-metadata-driver")
; This actual source carrier has 25 columns and no extras. Shape checks array
; lengths, while its generated type predicate rejects the negative enum value.
(defconst *fn2-root1-malformed-metadata*
 (append (list '(-1)) (repeat 24 '(0)) '(1)))
(assert-event
 (and (fn2-checkpoint-metadata-wfp *fn2-root1-malformed-metadata*)
      (not (fn2-checkpoint-metadatap *fn2-root1-malformed-metadata*))))
; Actual machine arm child domains supply exactly the strengthened operation
; domain, including readonly sources. Neither output claim is removed.
(assert-event
 (equal (fn2-checkpoint-root1-child-hyps *fn2-checkpoint-root1-children*)
        (fn2-arms-child-shape-hyps *fn2-checkpoint-root1-children*)))
