# Root disposition: native store guard/cost review

The [independent review](claude-native-store-guard-review.md) was produced by
Claude Code in the requested interactive tmux. Its useful experiment separates
a direct core entry from a program-mode wrapper and finds substantially growing
publish-body cost in the measured logical experiment. Its headline answer is
stronger than its evidence: the final section acknowledges that the actual
saved-image `fnn-call` chain was not measured.

The report's blanket claim that the bridge only names host wrappers is false:
`host/native/io.lisp` calls `fn-frame-trailer` directly through `fnn-core`, and
`host/native/bp-service.lisp` calls `fn-bpn-step`. Those are intentional ACL2
semantic owners. A lint banning book calls would be the wrong repair. Nor should
a lint require every wrapper to remain program mode: that would prevent future
verified wrappers without demonstrating a cost or safety property.

The source trust-boundary comment did overstate what choosing an executable
counterpart and checking `guard-checking-on` establishes. Program-mode wrappers
are not guard-verified caller proofs; proving a callee's guards does not prove
that each host-supplied argument or global state satisfies them. Corrected source
comments retain this adapter obligation. No invariant check is removed and no
new correctness theorem follows from this documentation correction.

The timing evidence remains a surrogate-model sample, not native node throughput
or a proved complexity bound. Its roughly N^1.75 per-cycle estimate comes from
two sizes only; the extrapolation to 10,000 records is unmeasured and not an
operating guarantee. A native profiling packet now owns the actual saved-image
entry, bounded profile sizes and attribution of the dominant body walks. Any
index optimization must carry an explicit correspondence; turning checks off is
not an accepted remedy. The BP lifecycle's explicit state recognizer and raw
journal recounts remain separate known cost obligations.
