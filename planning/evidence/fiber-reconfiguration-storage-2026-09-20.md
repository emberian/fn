# Fiber reconfiguration-storage: v0.5, live reconfiguration and the crash model

What this strand of v0 has proved, what it has only tested, the pessimistic
numbers with the scope they cover, and what is open. Every number here is
cited to the file it came from; nothing is retyped from memory. Written by
the w9/release lane against `dev` at `52eb0db`.


## What is proved

- **Authoritative committed state with complete derived indices** (STO-001),
  **atomic acceptance including memberships and obligations** (STO-002),
  **success follows a matching durable commit** (STO-003), **uncertain
  persistence fences mutations pending recovery** (STO-004), **recovery
  preserves acknowledged commits without partial effects** (STO-005) and
  **checkpoints preserve complete future-relevant state** (STO-006) are all
  `implemented` with keystones in `planning/requirements.json`.
- **The crash model includes torn and reordered writes and explicit
  uncertainty** (FLR-001); **known abort, uncertainty and lost volatile state
  are distinct** (FLR-002). Both `implemented`.
- **Configuration is a durable record replayed by ACL2**, not a compiled file:
  `books/config.lisp` deltas with ten kinds, `books/config-records.lisp`,
  `books/node-config.lisp` (w5-config-groups, w6/peering-inbound).

## What is tested and not proved

- SIGKILL from inside an open POST gives the client ECONNRESET, the
  interrupted article is absent after recovery, and the article acknowledged
  before the kill rereads byte-for-byte through a fresh server:
  `planning/evidence/deploy-cce4b11-2026-09-20.md` rows 23 to 28.
- Recovery is idempotent across two successive recoveries and a SIGKILL in
  between (same file, rows 14, 25, 26).

## Open, with the evidence that says so

- **A durable staging orphan has no owner.** An injected uncertain publication
  (`post --inject-fault postpublish`, exit 3) leaves `staging-orphans=1
  [.stage-1745786-...]`, and `recover` reports that orphan and leaves it in
  place across two recoveries and a kill. Reported rather than collected is
  defensible; it is a durable artefact with no row in the registry.
  `planning/deputies/BOARD.md`, w5-deploy-gate note to store; STO-008's note in
  `planning/requirements.json`.
- **The v0.5 gate condition is not met**: "every crash point in the cut table
  is a transition the model expresses". The enumerated cut table is
  `tests/campaign/cuts.py`; the deploy gate exercises exactly one kill point
  and says so in its standing gaps. Under the assurance rule "every
  process-death cut is a model crash point", a cut the model cannot express is
  a fidelity defect, not a passing test.
- **Compaction and reclamation do not exist** (STO-007, RET-005, RET-006; PRF-009
  is planned with no events).
- **Corruption detection has no repair path** (STO-008). K11 of
  `planning/lanes/DESIGN-crash-model-v2-summary.md` (truncation and resize never
  validate) is a design.
- **`fn group create|retire` refuses while a service is live**, because a
  configuration record needs the exclusive writer lock; the reconfiguration
  owner event is the real fix (`planning/deputies/BOARD.md`, w5-fn-cli).

## Pessimistic numbers, each with its scope

- **Store ceiling**: 4096 articles of 1024 octets, stopped by the
  `fn-store-profile-scale-1` transaction bound of 4096 -- reached with every
  measured operation still inside its ceiling, so the bound and not the
  machine is what stopped it. 4096 committed in 9578 s. Scope: persvati, one
  writer, two groups per article.
- **Reopen at 4096 articles**: 21.812 s read-only, growing as about N^0.33
  across the measured doublings. Scope: one reopen per point on that host.
  The exponent is a fit over a handful of doublings, not a theorem.
- **Where the reopen's seconds go**: image start and `include-book` 1.4 s, then
  `fn-store-sn-recover` 12.1 s in 1 call of the 17.8 s reopen; a further
  1.81 s in 4096 `fn-store-frame-store-decode` calls and 0.93 s in 4096
  `fn-store-record-sequence` calls. Scope: one profiled reopen of the largest
  store, timed at the bridge.
- **`run_store.py recover` from the operator's side**: 22.8 s wall at that
  store, exit 0, ACL2 image start and `include-book` included, no concurrent
  load of ours.
- **Resident set at 4096 articles**: VmHWM 3,325,112 KiB (3.17 GiB) after
  posting, against the gate's 16 GiB ceiling.
- All five numbers: `planning/evidence/scale-0e9a421-2026-09-20.md`.

## Rules this record follows

- A keystone is cited only where a root that reaches it certified in a farm
  gate whose manifest is named above. A theorem admitted in a lane worktree
  and never gated is listed as open, not as proved.
- A pessimistic number carries its scope in the same sentence, and the scope
  names the host, the load and the shape of the input.
- A passing test is not a proof and a certificate is not an audit. Where the
  two disagree about a claim, the disagreement is written down rather than
  resolved in favour of the greener one.
