# Foundation gaps encountered by the C/D sprint

Entries are recorded when encountered. GC/GD identifiers retain each agent's
ownership; G identifiers belong to Sol. Coordinator originals are normative. Decision-document references below resolve
under `/Users/ember/dev/fn/build/coordinator/fn2/`; C/D brief references resolve
under `/Users/ember/dev/fn/build/coordinator/briefs/` to
`FN2-LAYER-C-ORDERED-RUNS.md` / `FN2-LAYER-D-MACHINES-NNTP.md`.
`ROUND2-ASTRA` abbreviates `EXECUTION-MODEL-ROUND2-ASTRA.md`.

Ten entries record encountered gaps/extension seams. GC2 and GD2 are separate
consumers of the same missing B3 lifecycle. GC3 records a catalogue integration
seam; the existing generic codec already supports C-owned layout data.

## G1 — A: closed machine registry and observation/dispatch seam

Needed: layer D's connection machine in the same core and simulator dispatcher,
required by EXECUTION-MODEL.md:15 (rule 1), :21 (rule 7), and layer-D brief item 3.
Missing seam: `fn2/books/machines-a.lisp:93` closes the registry;
`fn2/books/machines-a-run.lisp:14` manually routes observations, while the
run dispatcher is generated at :249. Sprint-local D integration must either
assemble its own registry/core or drive its declared table beside A's core.
Workaround: `fn2/sprint/d/machine.lisp:4` includes the closed core before
declaring the real connection table as a sidecar;
`fn2/sprint/d/connection.lisp:380` adapts the generated fallback;
`fn2/sprint/tests/d-exchange.lisp:82` drives it and routes harvested completions.
A owns the extensible registry/router seam; this scout does not duplicate core
assembly or claim that the existing `fn2-turn` reaches its connection.

## G2 — A tooling: sandbox-compatible use of the shared ACL2 slot pool

Needed: execute certification and REPL through the laptop's existing shared
slot pool, as required by the sprint's box-safety fence. The initial real
certify refused before ACL2 started because `tools/acl2_slots.py:286` opens
`~/.cache/fn-acl2-slots/slot-000` read-write; that directory is read-only in this
session. The write is diagnostic only (`:309-313`), but acquisition cannot reach
its existing error handler.
Workaround: `fn2/sprint/acl2-readonly-slot.py:22` supplies a read-only exclusive
flock hook over the SAME global files and count, then runs unchanged
`tools/acl2`. PID/label diagnostics live in build/. It refuses private slot
pools. It changes no ACL2 semantics or certification options. Set ACL2 to its
absolute path for `fn2/tools/certify.sh`; invoke it directly for REPL drivers.
The first failed certify log is `build/sprint-d-foundation.log`.

G2 operational note: D's already-started cold retry used a private lock path
before this hook existed. The sandbox rejected signalling its recorded PID
4527. Sol therefore reserved global slot 0 on that running job's behalf until
its certify command finished at 20:55:59 UTC (`build/sprint-retry-reservation.log`, reservation
PID in `build/sprint-retry-reservation.pid`). All subsequent launches use the
read-only shared-pool hook. The private path is not the prescribed launcher.

## GC1 — A: bounded pool comparison primitive
Needed exact Message-ID equality without byte-list conversion (STORAGE-DESIGN.md:6; FILTERS-2026.md:26-30; EXECUTION-MODEL.md:20, one pool). Pool exports at `fn2/books/pool.lisp:344-366` expose scalar read/write but no resumable range comparison. Sprint workaround is `fn2/sprint/c/runs.lisp:103` (`fn2-sc-compare`): at most 250 byte-pair comparisons (500 pool reads) per identity, charged against a 4096-byte lookup budget. Stored ranges and query ranges are live workspaces owned by the explicit shared sprint owner (250,0,1); no implicit owner bypass. A range primitive with two explicit owners should replace it.

## GC2 — B: commit installation and run lifecycle absent
Needed sealed run roots installed only through B's durability protocol (C brief:6-9; STORAGE-DESIGN-ASTRA.md:462-496). `fn2/books/machines-a.lisp:93` ends with scribe and closes the machine registry without a commit kind; `fn2/books/merkle.lisp:1` and `fn2/books/alloc.lisp:1` supply digest/frontier and allocation models, but no B3 commit machine, recovery, checkpoint, or cleaner exists in the checkout. `fn2/sprint/c/seal.lisp:68` builds and hashes an in-pool run page and calls its state `:sealed-volatile`; this is explicitly not durable publication. Pinned workspace handles replace physical object leases for the duration of fixtures. B3 must accept the dependency page, fence, atomically install roots, and retain retirement obligations.

## GC3 — B: run-schema catalogue integration seam
C brief:6 requires run pages and exact identity schema; STORAGE-DESIGN-ASTRA.md:343-347 requires schema header, ordered entries, offset directory and checked continuations. B's format catalogue `fn2/books/format.lisp:280-321` has page-header/membership-entry but no run schema header or identity entry layout. C owns these schemas. B owns its built-in catalogue/discovery surface; it currently has no registration seam for later schema books. Encoding itself needs no B edit: the existing generic layout interpreter accepts C-owned data layouts. Sprint `fn2/sprint/c/seal.lisp:9` declares those data layouts beside B's real page header; B's single layout interpreter encodes them. No codec or declaration macro is duplicated.

## GC4 — A: native u64 column kind not yet present
ROUND2-ASTRA.md:151-157 gives persistent identities/positions and resource widths as u64 words; the binding A-WIDTH-PER-COLUMN ruling permits a u60 interim destination until R5a. `fn2/books/columns.lisp:31-34` only recognizes u8/u16/u32/u60/bool widths. `fn2/sprint/c/runs.lisp:8-10` therefore uses u60 group/number/tag/generation columns and returns `:bounds` instead of wrapping or narrowing a value that does not fit; `fn2/sprint/c/seal.lisp:57-61` uses fixed fixture history/incarnation/epoch/allocation values 1. This is not a full-width persistent namespace implementation. R5a's native u64 columns should replace the interim destinations when the real C persistent identity schema lands.

## GD1 — A: dispatcher return shape is hardwired to A's core
Needed: the connection declared by `defmachine` must run over the connection row, C state and A core (ROUND2-ASTRA §A.1 lines 20–34; D brief item 3 line 9). Foundation `fn2/books/machines.lisp:101–105` emits an `otherwise` arm calling `(fn2-machine-refuse-phase id fn2-core)`; the existing closed core cannot contain this sprint row (Sol's G1). Workaround: `fn2/sprint/d/connection.lisp:382` macroexpands A's generated dispatch and replaces ONLY that fallback's return shape, retaining every generated state arm. The sidecar is driven by a sprint driver, not reachable from the existing `fn2-turn`.

## GD2 — B: no commit, recovery or publication machine exists
Needed: POST outcomes become uncertain at `log-write`, accepted only after persistence, and visible publication follows durability (ROUND2-ASTRA §E.2 lines 430–444; D brief item 5 line 11). Foundation `fn2/books/machines-a.lisp:93` closes a registry containing listener/echo/null/scribe only; `fn2/books/merkle.lisp:240` hashes event leaves but does not commit them. Workaround: `fn2/sprint/d/connection.lisp:48` issues actual A Write then Fence for a pinned article range, keeps uncertainty from the Write submission until the Fence completion, and appends its C overlay row only afterwards. This is a one-article persistence stand-in, NOT B's journal/recovery/root protocol; no crash-recovery claim.

GD2 workaround updated during review: each POST writes a fresh 4096-byte address interval derived from its strictly increasing command ordinal, rather than overwriting offset zero. Namespace/ordinal exhaustion must close before reuse. The D fixture explicitly selects 32 simulated 4096-byte sectors (128 KiB); the machine receives that device bound at init and checks address+length before issue. Capacity refusal before Write is refused; ambiguity after an issued Write remains uncertain. The 4096-byte spacing isolates acknowledged sources from later-sector writes.

## GD3 — A: no arm cost/frame contract or generated arm obligations
Needed: D brief item 1, `/Users/ember/dev/fn/build/coordinator/briefs/FN2-LAYER-D-MACHINES-NNTP.md:7`, requires a restricted metered arm vocabulary, outside-call cost/frame contracts, and emitted phase/budget/frame obligations; ROUND2-ASTRA B.3 (`EXECUTION-MODEL-ROUND2-ASTRA.md:197–216`) says simultaneous caps also need a scalar-work certificate. Foundation `fn2/books/machines.lisp:95–100` generates a charge function that checks declared numbers; `fn2/books/machines.lisp:107–112` stores obligation names as table data; `fn2/books/machines.lisp:114` accepts continuations with no cost/frame keyword. It cannot derive the work done by C lookup, parser scanning or ARTICLE rendering. Workaround: `fn2/sprint/d/connection.lisp:242` bounds scanning to 32 octets, `fn2/sprint/d/connection.lisp:300` slices body rendering into 1200-source-octet continuations, and `fn2/sprint/tests/d-exchange.lisp:90` checks returned simultaneous quanta. Those are conservative self-declared work records and bounded loops, not a proved scalar-operation cost certificate. `fn2/sprint/d/owed.lisp:15` records the transition/budget obligation as owed; nontrivial guards remain deferred. No second machine DSL is introduced.

## GD4 — A: no bounded retained-prefix compaction primitive
Needed: a fragmented parser must progress after consuming complete pipelined commands while retaining a partial next line (D brief item 2, `FN2-LAYER-D-MACHINES-NNTP.md:8`; simultaneous connection byte cap `EXECUTION-MODEL-ROUND2-ASTRA.md:207`). Foundation `fn2/books/pool.lisp:344`, `:353`, `:368` exports scalar read/write and whole-range reset, but no bounded prefix-drop/copy continuation. Resetting only an entirely consumed RX window leaves a full window with a retained tail unable to receive. Workaround: `fn2/sprint/d/connection.lisp:206`, function `fn2-sd-compact` uses the already-reserved TX workspace as scratch: retained RX tail to TX, reset RX, TX back to RX in at most 1024-octet copy calls. Existing `wait-reason` tags 4/5 and `seek` retain the two stages and copy offset; `scan` is rebased once. No input action or reply loan is outstanding during compaction. The test `fn2-sdt-compact-check` at `fn2/sprint/tests/d-exchange.lisp:174` forces a partial command at a full window's end and verifies resumed GROUP dispatch. An unconsumed line filling the entire window is a named framing refusal, not a retry loop.
