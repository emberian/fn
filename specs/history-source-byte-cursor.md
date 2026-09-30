# Tagged canonical source bytes and census

The source sum is `(:resident row)` or `(:decoded node)`. The guarded
`fn-hsrcb-begin/tick/supply` adapter uses the original resident cursor unchanged
and the single cold runtime implementation. A cold request is exactly
`(:need-byte pool-position kind child-coordinate)` and leaves its continuation
unchanged. The outer authenticated reader must establish source/root/pin,
kind/coordinate, read serial and buffer ownership before supplying a byte;
this adapter additionally checks its current requested position.

`fn-hsrcc-tick/supply` counts emitted canonical bytes in ACL2, including bytes
emitted by supply, exactly once. `fn-hct-offer/tick/supply` keeps the pending
source row until `:row-done`, then installs its padded byte count. A byte
response cannot change completed row count, padded pool count, capture or lease.

The named resident compatibility lemmas retain the old resident census proof
scope. Cold controller residual/invariant and progress remain the cold owner's
open PRF-1088 obligation; guard admission and literal fixtures do not close it.
The new supply framing lemmas concern controller state only, not real disk,
reader or resource authority. This checkpoint is source admission evidence,
not certification, native qualification, complete writer or publication.

Dependencies are imported exactly from cold runtime source `a014b6212`.
Fresh protected hbox `hctcold2` loaded 89 matching cached books and eleven
proper-local source dependencies, then all five test-root forms (driver and
three assertions). ACL2 reports 62.78 seconds and 29,210,906 prover steps
including the source closure. The archived pre-stop state is ready/error-free;
the session was stopped explicitly after harvest. See the adjacent evidence
record for source digests and the retained log.
