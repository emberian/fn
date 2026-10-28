# Sprint C/D interface

Written by Sol before C and D start. All symbols in ACL2. C owns the book
`fn2/sprint/c/runs.lisp` and the `defcolumns` stobj `fn2-sprint-c`.
Bytes always remain in `fn2-pool`; range arguments name workspace buffers and
include the existing pool owner `(okind oslot ogen)`. No byte lists cross this API.
The sprint pins stored ranges for the lifetime of its examples; this is not a
durable location mapping or object-lease implementation.

* `(fn2-sc-init capacity fn2-sprint-c)` -> `fn2-sprint-c`.
* `(fn2-sc-add group number mid-slot mid-gen mid-off mid-len body-slot body-gen body-off body-len content-tag fn2-sprint-c)`
  -> `(mv code row fn2-sprint-c)`. `:ok` or `:exhausted`; append in increasing
  `(group,number)` order; reject invalid/nonincreasing keys by name. `content-tag`
  is a sprint scalar content identity fixture, explicitly not a BLAKE3 identity.
* `(fn2-sc-lookup slot gen off len okind oslot ogen start fuel fn2-pool fn2-sprint-c)`
  -> `(mv code row next)`. Exact Message-ID comparison; `:found`, `:absent`,
  `:yield`, or pool refusal. `start=0` begins; `next` resumes a bounded scan;
  cap structural fuel at 32 and byte work at 4096 per call. Comparison can
  require continuation for long identities; C may expose an extended continuation
  function if needed, keeping this wrapper for the <=250-byte fixtures.
* `(fn2-sc-number group number start fuel fn2-sprint-c)` -> `(mv code row next)`.
  Same codes, bounded ordered-key search; row getters only after `:found`.
* `(fn2-sc-group group start fuel count low high fn2-sprint-c)`
  -> `(mv code next count low high)`. `:done` or `:yield`; initial accumulators 0.
* `(fn2-sc-cursor group after-number max-number entry-budget byte-budget fn2-sprint-c)`
  -> `(mv code first-row count resume-number bytes)`. Entries follow the stable
  exclusive `(group,after-number)` key; returns a contiguous slice of matching rows,
  at most 32 entries and 4096 modeled rendered bytes. `:done`, `:yield`, or named
  refusal. Sparse keys must seek stored rows, never walk numbers. D may use the
  number lookup for ARTICLE; C's drivers exercise cursor yield and re-seek.
* Read-only scalar getters `(fn2-sc-row-FIELD row fn2-sprint-c)` for `group`,
  `number`, `mid-slot`, `mid-gen`, `mid-off`, `mid-len`, `body-slot`, `body-gen`,
  `body-off`, `body-len`, `content-tag`; `(fn2-sc-count fn2-sprint-c)`.

C also builds bounded sealing through B's real layout/format codec and BLAKE3.
D includes `../c/runs` and calls the above directly, with `fn2-pool` obtained
through `stobj-let` if D runs with A's core. D owns its connection declaration,
parser, simulator integration and POST stand-in; no foundation changes.
Any necessary adjustment is negotiated directly between C and D and reported to
Sol, then recorded here before integration.

## Reconciled additions during the burst

Both agents explicitly use pool owner `(250,0,1)` for all retained/query ranges
and issued operations. This is a single-connection fixture owner, not a privacy
or general ownership-transfer implementation.

C's `c/page-lookup.lisp` adds:
`(fn2-sc-page-lookup qslot qgen qoff qlen page-slot page-gen start fuel okind oslot ogen fn2-fields fn2-pool)`
-> `(mv code row next content-tag fn2-fields)`. It decodes B-layout offsets and
inline Message-ID octets in a previously hash/identity-checked immutable page.
It processes at most four entries per call; `next` resumes `:yield`. Checking the
parent-held page hash remains the caller's prerequisite.

`(fn2-sc-cursor-step group after-number max-number entry-budget byte-budget lo hi phase fn2-sprint-c)`
-> `(mv code first-row count resume-number bytes next-lo next-hi next-phase)`.
Start `(lo,hi,phase)=(0,count,0)`. A zero-output yield retains binary-seek bounds;
a nonempty batch resumes by stable key with fresh seek bounds. This prevents a
large seek from consuming every quantum without progress. The short cursor
wrapper returns `:cursor-continuation-needed` if that extended continuation is
required. `bytes` is a conservative size charge for the XOVER-shaped projection,
not a rendered wire buffer.
