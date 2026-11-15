# Actual recovery frontier continuation

The canonical recovery dispatcher now routes authenticated replay stage4 through `fn2-recovery-frontier-step` before any lifecycle/C replay. It consumes the same `fn2-event-members-step` scanner and hash/carry primitive as checkpoint event reading. The actual CHAINED candidate supplies the event interval, and the current recovery row supplies the immutable owned window and generation. Every continuation checks the shared current-unit authentication predicate, scanner ownership/range and candidate interval. It advances only after scanner EOF and exact frontier size; it never resets a selected C frontier.

`fn2-recovery-install-finish` publishes the reconstructed mapped directory terminal for the actual selected source while leaving allocator phase4 and epoch-begun0 unchanged. The full-discovery path retains its existing operation. Opening selected issuance still requires the actual later persisted boot epoch Fence and completed protection/orphan reconstruction.

Source only: parsed changed Lisp forms, scoped reread rewrite fixtures, secrets and diff checks pass. No admission, execution or whole-recovery claim. The selected candidate-adoption bridge is connected through `recovery-selected-adopt`; exact mapped allocation ownership is restored by `checkpoint-owned-projection`. These source changes have not executed in a qualified composed recovery world. Phase4 remains closed pending protection reconstruction and final epoch exclusion. The independent audit owns same-length reread substitution, stale lease and continuation controls. Runtime row0 is the reconstructed recovery frontier, not a claim that subsequent ordinary commit currently maintains that row.

## Required release and recovery connection

The existing RELEASE_ALLOCATION wire record is not yet a served release lifecycle. The allocator codec owner is connecting its strict decoder, actual journal producer and ordered replay consumer; the reclamation deputy owns the final boot opening boundary. No physical FREE or reuse is enabled by these source milestones.

A chronological RELEASE followed by a new ALLOCATION of the same extent must reconstruct ownership in that order while recovery remains closed to physical issuance. The later persisted epoch Fence establishes backend exclusion before physical use opens; it cannot be used as a reason to skip chronological replay. The shared allocator transition and its exact closed-recovery authority still require implementation and review. Unknown orphan allocations remain a refusal, not an invented identity or silent cancellation.

RELEASE_EVIDENCE contains a physical Ref. The release journal must retain the exact descriptor allocation through a typed durable obligation until an authenticated checkpoint summary replaces that dependency. Evidence capture alone does not establish protection reconstruction, and copying bank evidence does not discharge independent cold-anchor edges. Candidate disposal must close new claims before its first edge removal and retain its debt until all such owners have actually transferred or drained.

The current selected install pass still adopts all suffix physical candidates
before ordered record replay. That ordering rejects a valid later allocation
whose extent retains an older RETIRE_PENDING identity in the selected map: the
earlier release has not replayed yet. The required repair separates authenticated
journal read provenance from allocator ownership, then applies ownership at the
actual chronological commit/record boundary. Reclamation owns that driver change;
the codec owner supplies the shared release transition and RELEASE–ALLOCATION–
RELEASE control. Neither overwriting the old identity nor skipping its release is
an acceptable substitute. The full-discovery path is a separate existing scope.
