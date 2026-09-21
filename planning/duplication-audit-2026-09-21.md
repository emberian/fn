# Consolidation audit: assurance and operator pleasantness

Status: active repair work, not a completed audit or release claim. The user
requested an implementation/design scan for duplication and unnecessary
complexity on 2026-09-21. Sources inspected: integration `406578c`, native
storage candidate `37ec36b`, and BP convergence candidate `52ab12d`.

The criterion is one owner of each decision, with representations and external
observations explicitly connected to it. A logical model plus a justified
concrete representation is useful, intentional separation. Two host paths that
independently decide whether a publication succeeded are competing authority.
Moving the second path from Python into Lisp does not remove that problem.

## Findings and repair assignments

### U01: BP lifecycle publication turns visibility into durability

At BP candidate `52ab12d`, `host/native/bp-service.lisp:110`
`fnn-bps-persist-record` stages, links and fences a record. Its error handler
catches failures of those operations, including `fnn-fsync-dir`, and returns
`:durable` whenever the final file is readable and byte-identical. That branch
does not repeat a successful file/directory barrier. The caller
`fnn-bps-drive-effects` feeds that result to the actual ACL2 lifecycle machine.

Concrete separating case: link succeeds, the directory barrier reports EIO,
and the new entry remains visible. Equality of readable bytes then yields
`:durable`, although durable namespace publication remains unknown. This is a
code-level defect; a live injected witness is assigned to BP convergence before
landing. The later directory barrier and cleanup failures need independent
cases too, since their completed durability prerequisites differ.

Repair: uncertain publication must stay fenced, or pass through an explicit
recovery procedure whose required barriers all succeed before reporting durable.
Do not treat an existence/equality check as that procedure. Preserve the
original failure and source-pinned evidence. Model the observation actually
supplied to the called machine; its abstract `:persist-result` does not itself
prove the host's classification.

Owner: `submission_path` (Sol, BP convergence). This blocks a positive native
lifecycle durability claim, not the frozen logical certification already running.

### U02: independent outcome aggregators disagree about uncertainty

At the same candidate, `host/native/bp.lisp:233` `fnn-bp-exit-code` checks a
positive refused tally before checking the connection's `:uncertain` outcome,
contrary to its stated uncertainty-dominates-refusal policy. Both observations
can be constructed; the lane must establish a reachable duplex-session witness
before claiming a live reproducer. `fnn-command-bp-send` supplies the tally and
the same connection to this helper after the session.

Repair: an ACL2-owned operation-result policy consumed by the host, with mixed
outcome tests. Distinguish per-article verdicts, transport outcomes, operation
summaries and host faults. `fnn-tcl-exit-code` and `fnn-bps-exit-code` have
different absent-result defaults; do not mechanically collapse them into one
severity ranking without stating their different operation contracts.

Owner: BP convergence, after its frozen gate. CLI consolidation consumes the
result contract rather than creating another mapping.

### U03: lifecycle admission is decided twice and rescans growing history

`books/bp-node-machine.lisp:369` `fn-bpn-propose` enforces the journal record
limit using the carried next token. `host/native/bp-service.lisp:120` then calls
`fnn-bps-record-names`, enumerates and sorts the whole namespace and compares its
length to the same limit before every publication. This is a second admission
decision and repeated work proportional to retained history, producing quadratic
total enumeration work over a growing journal. No runtime cost measurement is
claimed here.

Repair: establish the observed namespace/frontier correspondence during bounded
startup recovery, carry it through successful publications, and let ACL2 own
admission. Unexpected external changes still need an explicit observation/fault
contract; removing the scan without a replacement invariant is not a solution.
The host also constructs/parses `.fnb` sequence names independently. Feed the
observed names into the authoritative codec rather than retaining two grammars.

Owner: BP convergence successor. This is implemented-surface assurance and cost
debt, not an optional future feature.

### U04: publication protocols are copied rather than shared at the right level

Integration `406578c` has distinct native publication algorithms in
`fnn-publish-initial-file`, `fnn-publish`, `fnn-tcl-stage` and `fnn-bp-record`;
the BP candidate adds frontier replacement and lifecycle append. Python workflow
and receipt journals carry further copies, now development-only under D07.
The copies differ in exception classification, parent barriers, no-replace versus
replace publication, cleanup and recovery. U01 is one concrete harmful divergence.

Consolidation direction: reuse a small set of explicitly specified persistence
operations and one raw I/O interpreter. Keep immutable no-replace publication,
allocation-frontier replacement and append/prefix repair as distinct contracts.
ACL2 owns each operation's phase, admissible completion and recovery decision;
the raw host reports syscall observations. Use existing byte-store primitives
and correspondences where they fit. Do not build a universal journal framework
that obscures the different obligations or add another uncalled model.

Next design packet: inventory the actual callers and their guarantees, select
one called operation to consolidate, and prove/test that operation before moving
the others. The immediate U01 repair must not wait for this broader factoring.

## Pleasantness criteria for the native migration

- One documented operator CLI and configuration contract. The positional native
  test interface may remain internal; it must not become a competing operator UI.
- Startup diagnostics distinguish unavailable facilities, invalid configuration,
  refused work, corruption and uncertain persistence. No silent Python fallback.
- One durable submission path for CLI and NNTP with source/provenance distinctions
  explicit in the core, rather than independently implemented acceptance rules.
- Defaults, bounds and configuration keys have a single authoritative definition;
  generated documentation/projections may repeat their display, not their policy.
- Reports name the operation and its durable outcome. A transport ACK, a successful
  signature observation and an accepted retention obligation remain different.

The CLI lane is separately auditing repeated verbs/options/defaults and conflicting
operator documentation. Independent Claude review is running in the existing real
tmux against frozen `406578c`; its findings will be checked against active packet
changes before assigning repairs. Neither review runs another whole-tree gate.
