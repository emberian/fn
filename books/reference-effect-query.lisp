; First actual callback slice: identity decision -> query flush -> declared
; scheduler wake. Exact guard/frame contracts admit only the named leaves.
; The whole-result rows remain OWED; definitions do not establish a proof.
(in-package "ACL2")
(include-book "reference-effect-leaves")
(include-book "assembly-callbacks-c")

(fn2-reference-effect-lower fn2-identity-decide
 :shape-leaves ((fn2-corep . fn2-ref-effect-corep-shape)
                (fn2-core-wfp . fn2-ref-effect-core-wfp-shape))
 :frame-leaves ((fn2-core-record-enqueue . fn2-ref-effect-record-enqueue-frame)))
