# BP composition assurance closure

This batch adds assurance for the implemented sender/receiver path. It changes
no production transition or persisted format. The sender's work binding, the
receiver's Store/context/decision relations, and five actual receiver process
deaths now have evidence separate from the earlier
[real BP exchange](2026-09-18-bp-exchange.md). The
[machine record](2026-09-18-bp-composition-assurance.json) retains exact source
digests, commands, tool versions and root certification manifests.

## Mechanized scope

`fn-bp-binding-statep` combines structural validity with actual article, subject
and archive binding for durable and pending work. Initialization, every actual
sender transition, dispatcher step and arbitrary finite event trace preserve
it. Nonempty executable witnesses include uncertain completion, restart,
recovery, stale events and a fabricated work showing that structural validity
alone does not imply binding. Outbound retains its explicit binding recheck.

The receiver proofs use the actual `fn-bpr` transitions and `fn-bprr` record
application/replay. They establish:

- Structural state preservation through acceptance, prepare, commit, record
  application and arbitrary finite replay.
- Retained contexts are backed by exact authoritative records in a valid,
  ready Store, including article/subject equality and node/archive binding.
- Pending and committed receipts agree with their retained request context.
  A replayed committed receipt has a matching typed `:committed` decision in
  the supplied journal. No receipt ADU is emitted without such a decision.
- Existing context and receipt lookups survive journal extension. An already
  emitted receipt ADU remains byte-identical through subsequent finite replay.
- Successful fresh replay satisfies the combined state, Store/context and
  committed-decision invariant.

These are inductive results over the production definitions, not a wrapper
that filters outputs to satisfy the desired property. The receiver uses a
**fixed Store snapshot**. This does not prove preservation as the Store itself
evolves, physical journal-byte correspondence, fsync behavior, or authenticity
of the journal's trusted local policy decision.

Root certified **11 scoped roots** in four batches on ACL2 8.7 / SBCL 2.6.8:
the two sender books and assertion root, and seven receiver books plus its
assertion root. Each certification records unchanged source inputs and an empty
forbidden-facility audit. This is not a new full `make certify` run. The
[41-function ADU guard closure](2026-09-18-bp-guards.md) has its own eight-root
record; 97 functions in the other six inventoried BP base books remain outside
that guard closure.

## Actual receiver process deaths

`python3 -m unittest tests.test_bp_receive_process_crash -v` passed one table
test with five independent child-process cuts in 15.112 seconds. Each child
runs the actual Python/ACL2 receiver, reports the named durable boundary over
a pipe, blocks, and is killed with `SIGKILL` as a dedicated process group:

| Durable predecessor | Interrupted next action |
| --- | --- |
| Complete FNBI request staging | Store acceptance |
| Store article/archive acceptance | FNRJ request context |
| FNRJ request context | Receipt intent |
| FNRJ receipt intent | Receipt decision; explicit recovery required |
| FNRJ committed receipt decision | BPA deletion |

Every cut checks absence of early BPA deletion, exact staged BID/request bytes,
exact article content and record/article/pin counts before and after recovery.
Retry produces one article and one archive pin. A fresh BID carrying the same
request regenerates the identical receipt without another charge. The final
cut additionally compares the receipt captured before death with the regenerated
bytes. These are process-death/cache-retention tests; the earlier seven
exception/reopen cases remain a distinct evidence set. Neither is physical
power-loss qualification.

The complete Python suite passed **133 tests** in 147.882 seconds:

```sh
python3 -m unittest discover -s tests -p 'test_*.py' -v
```

Python was 3.14.7 on macOS 26.6.1 arm64. Test/runtime inputs were unchanged
before and after the run. Subsequent integration added proof books and ACL2
assertions only; all tested source digests still match. No claim of a fresh BP
transport lab run is made: the previously recorded exchange remains the
transport evidence for unchanged runtime behavior.

## Remaining obligations

`PRF-001`, `PRF-007`, `PRF-012` and `PRF-014` remain in progress; `SCN-008`
has partial execution evidence. General FNWF/FNRJ byte/live/replay refinement,
receiver composition with an evolving Store, the remaining BP guard graphs,
concrete D01/D09 identity/authority and authenticated handoff remain open.
Physical durability and cooperative-peer behavior remain explicit assumptions.
Relay/contact-plan scheduling, carried media, LTP, fairness, persistent fragmented
progress, storage reclamation and mission qualification are separate unfinished
features with their own obligations. No complete milestone or handoff theorem
is claimed.

The updated [closure inventory](../../planning/assurance-closure.md) separates
implemented behavior with evidence, missing assurance for implemented behavior,
and future features. New behavior must bring its state, composition, durability,
codec, authority and transport obligations into that inventory in the same batch.
