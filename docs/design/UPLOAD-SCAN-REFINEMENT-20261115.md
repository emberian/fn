# Actual upload scan refinement qualification

The actual `books/upload-scan` is qualified at
`f1c91c9dbd6f20d3d36a1d410265548aced6b21d`: the original whole public
`fn2-upload-posted-refines-naive-spec`, verdict guards and compliance all pass.
All 66 original forms remain unchanged except proof hints on that same
refinement formula; nine LOCAL proof events provide the missing prefix-state
argument. Runtime function bodies and public guards are unchanged.

The completion predicate means the remaining input finishes the prefix already
read. The generalized invariant equates the actual automaton run with that
completion or an independent naive match at a later start. Its proof covers
failed reads without assuming the entire source is readable. A finite one-step
relation and the actual next-state bounds connect the recurrence to induction;
the zero-prefix bridge recovers the original public theorem.

The final frozen whole book passed original-event limits of 2,000,000 steps and
20 seconds. Record run `certify-20261116T002305Z-2013342` qualified the exact
16-book closure: fifteen genuine parents reused, one newly certified in 3.379
seconds. ENTRY `grammar` and `upload-window-geometry` exports exactly those
fifteen parents. [The receipt](receipts/upload-scan-qualified16.json) binds
current raw sources, keys, certificate/FASL hashes, author and manifest to the
record toolchain. Effective memory was 2 GiB, swap disabled; recorded owned
processes, scope and holder are gone. Complete served POST remains outside this
claim; actual caller composition remains the next frontier.

The unchanged actual `tests/upload-scan-unit` now passes whole-event author
limits and record certification over its exact 17-book closure: sixteen genuine
parents reused and one new test certified in 1.577 seconds, run
`certify-20261116T002706Z-2017609`. Its fixtures exercise header syntax and exact
limits, required/duplicate fields, verdict precedence, Message-ID validation,
case-insensitive POSTED path rejection, and transit identity matching.
[The unit receipt](receipts/upload-scan-unit-qualified17.json) binds all current
sources/keys and qualified payloads, exported ENTRY16 and cleanup. No test or
runtime source changed. This remains the actual pool-level scanner/verdict;
complete served upload composition is still unclaimed.
