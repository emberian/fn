# Current work: executable components and integration

See the [evidence index](evidence-index.md) for the full batch history and
[implementation status](../docs/implementation.md) for per-component scope.
This page is current status only; it carries no counts and no narrative
history (both drift — see planning/ledger.md and the evidence index instead).

## What runs

- `make check` validates documents/registries; `make certify` certifies the
  listed ACL2 books; `python3 tools/run_simulator.py` runs a three-step
  acceptance smoke run in real ACL2; `make test` runs all three plus the
  Python suite. None substitutes for another.
- A loopback NNTP reader serves a seeded article or a replayed local store
  through the actual ACL2 core (`tools/run_reader.py`); a pinned dtn7-rs BPA
  carries fn work between two local nodes (`specs/bp-path.md`); the local CLI
  persists articles/archive obligations.

## What is proved, with scope

The [assurance-closure matrix](assurance-closure.md) is authoritative per row.
Acceptance/node one-step and finite-trace invariants hold over the actual
event type. The file-publication kernel's crash/recovery traces are proved for
finite histories under the stated crash constructor, not every crash point the
host can hit (D4/D5 in the independent review). NNTP session/cursor
preservation is proved; effect typing is not yet bounded. The derived index
and the checkpoint's frontier rejection are proved against authoritative
memberships and the consumed frontier, respectively. BP sender/receiver
invariants hold over a **fixed** Store. Every "Certified" cell names its own
hypothesis stack; none closes a requirement end to end.

## Next

The [three-cycle plan](swarm-cycles.md) sequences C1 substrate-first per the
[independent review](review-2026-09-18-independent.md) §8: repair (C1-00),
identity/causality substrate (C1-11), byte codecs into ACL2 (C1-13),
crash-model fidelity (C1-14), assumptions as encapsulates (C1-15), a teeth
ledger (C1-16), then the renumbered original C1 packets, keeping the existing
[requirement](requirements.json) and [proof-target](proofs.json) IDs. One
writer owns each area; certify only your own roots; a commit is not evidence.
