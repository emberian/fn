# OWED: the proof-debt ledger of cut/breaking

Ledger, not gate (CUT-LEAD-20261016 §5). Every theorem or book deleted or
broken on this branch gets a row: the claim it carried, where it lived, and
the replacement path (or "none: the code it was about is gone"). ACL2
certification runs for information. A book that no longer certifies and is
not on the survivors list is deleted, not repaired; a survivor book that
breaks gets a one-line hint repair when that is cheap, else a red row here
and the work continues. The 5.4 series picks this ledger up.

Rows are appended by the commit that creates the debt, one line each,
newest last. `G4` is the line `tools/cut_measure.sh` printed for that commit.

| commit | book or theorem | claim it carried | replacement path | state |
|---|---|---|---|---|
| c626d6eb7 | 5 theorem(s) cited by PRF-046, in books/bp-node-forward-resume.lisp, books/bp-request-recovery.lisp (fn-bpnp-resumed-result-clears-only-the-slot, ...) | restart resumption of stranded BP rows and request-plan recovery (progress evidence for the fn-bpn-step target) | none: tier-A books unreached from every host build (M1-a sweep); PRF-046 keeps its statement on the surviving subject | owed |
| c626d6eb7 | 2 theorem(s) cited by PRF-081, in books/bp-node-rotation-equivalence.lisp, books/bp-node-rotation-recovery.lisp (fn-bpnj-rotation-restart-succeeds-with-owed-work, ...) | BP checkpoint recovery equals full recovery and rotation restart keeps owed work | none: tier-A books unreached from every host build (M1-a sweep); PRF-081 keeps its statement on the surviving subject | owed |
| c626d6eb7 | 2 theorem(s) cited by PRF-383, in books/config-walk-loops.lisp (fn-cfg-peer-names-loop-is-revappend-of-the-walk, ...) | loop-twin lemmas in the PRF-362 rev-onto pattern | none: tier-A books unreached from every host build (M1-a sweep); PRF-383 keeps its statement on the surviving subject | owed |
| c626d6eb7 | 24 theorem(s) cited by PRF-958, in books/owner-number-bound-join.lisp (fn-onbj-arm-acar-outcome, ...) | owner number bounds joined across node and store (fn-onbj-) | none: tier-A books unreached from every host build (M1-a sweep); PRF-958 keeps its statement on the surviving subject | owed |
| c626d6eb7 | 7 theorem(s) cited by PRF-1131, in books/decoded-window-clear-trajectory.lisp, books/decoded-window-finite-output-trajectory.lisp, books/decoded-window-yield-trajectory.lisp (fn-pwf-actual-completed-finite-output-yields-match-basic-loop, ...) | the dormant fn-ewz finite-output and yield trajectories complete effects | none: tier-A books unreached from every host build (M1-a sweep); PRF-1131 keeps its statement on the surviving subject | owed |
| 249a737f0 | 1 theorem cited by PRF-123, in books/post-record-width-owner.lisp (fn-prwo-owner-post-record-is-narrow-within-the-profile; its R corollary fn-prwo-owner-post-record-is-within-r, the PKT-250 keystone) | the record the owner's two host calls (fn-pak-post-admission, then fn-owner-prepare-buffer's catalog prepare) stage is narrow within the profile and within its R | none: tier-B book reached by no host build (M1-b post-identity); PRF-123 keeps its statement on the surviving producers (books/record-width-producers.lisp) and loses this event and its two evidence paths | owed |
| 249a737f0 | PRF-1145 whole (16 books: books/post-identity-source-cursor*.lisp, the D25 virtual-byte agent and injection inverse; fn-psc-) | the bounded source-cursor agent yields incoming-derived spans and per-source K,A,B descriptors matching fn-pb-path-agent and fn-pbb-source-index | none: tier-B stack reached by no host build (M1-b post-identity); the row is retired deferred to this ledger in planning/proof-retirements.json | owed |
| 249a737f0 | PRF-1148 whole (18 books: books/post-identity-captured*.lisp, the captured-row resumable SAME authority; fn-pic-) | duplicate/conflict decisions over the captured row equal fn-rclb-same-articlep plus exact held groups after the binding gate | none: tier-B stack reached by no host build and its native caller parked and removed by M1-a (M1-b post-identity); the row is retired deferred to this ledger in planning/proof-retirements.json | owed |
