; Actual direct callback -> query close/flush -> independent FIFO wake.
; The complete scalar/core/FIFO correspondence remains explicitly OWED.
(in-package "ACL2")
(include-book "reference-effect-leaves")
(include-book "identity-query-callback")

(fn2-reference-effect-lower fn2-identity-decide
 :shape-leaves ((fn2-corep . fn2-ref-effect-corep-shape)
                (fn2-core-wfp . fn2-ref-effect-core-wfp-shape))
 :frame-leaves ((fn2-core-record-enqueue . fn2-ref-effect-record-enqueue-frame)))

; Exercise strict reuse of the complete generated function and live row,
; rather than re-emitting a fixture-only helper or accepting a name match.
(fn2-reference-effect-lower fn2-identity-decide
 :shape-leaves ((fn2-corep . fn2-ref-effect-corep-shape)
                (fn2-core-wfp . fn2-ref-effect-core-wfp-shape))
 :frame-leaves ((fn2-core-record-enqueue . fn2-ref-effect-record-enqueue-frame)))
(make-event
 (let* ((row (cdr (assoc-eq 'fn2-identity-decide
                         (table-alist 'fn2-reference-effect-selections (w state))))))
   (value `(assert-event
     ',(and (equal (fn2-decl-get :scope row) :direct-call)
            (eq (fn2-decl-get :whole-subject row) 'fn2-identity-decide)
            (not (fn2-decl-get :logical-stub-equality row)))))))
