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

## Concrete pool and column continuation

`fn-hpe-tick/supply` shares this adapter. It packs each emitted octet using
`fn-hrcur-word-push`; authenticated supply may itself pack a word. Both calls
yield before consuming a child byte while a full page is outstanding.
`fn-hpcx-tick/supply` forwards the exact cold demand unchanged and preserves
the row token until the pool is prepared and all four columns are installed.
Only then does it return `:row-done`; the provider can advance afterward.

All original resident emitter and column theorems remain, including full
resident byte total, eighth-byte word and padded final word attribution.
A local width lemma connects an original resident byte emission to the
unchanged resident adapter branch; it makes no cold residual claim.
The fresh `hpcxcold1` source world includes the complete modified emitter
inside proper local scope and admits the complete column book. Literal tests
check string and opaque-span whole pool words, and a cold string through all
four columns, padded pool, token/count/offset and final row completion.
The committed evidence record distinguishes root loading from subsequently
sent fixture forms. Full cold semantics and the whole funded image writer
remain open.
