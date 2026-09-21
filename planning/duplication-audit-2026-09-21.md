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

Repair integrated through `2dab68d`: the fallback is removed, recovery repeats
the namespace barrier, and actual OS-error injections at both barriers require
uncertainty. The [native BP evidence](evidence/bp-convergence-native-2026-09-21.md)
records the certified-image runs. This closes this classification defect, not
the full lifecycle correspondence target (PRF-046).

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

Repair integrated through `2dab68d`: `fn-bpn-host-run-outcome` owns the policy,
and a reachable duplex test combines a refused article with an uncertain
transport result. Cross-session aggregation/fencing and core-fault taxonomy
remain separate receive-path obligations.

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

### U05: a stale owner article bound disagrees with the posting configuration

`books/owner.lisp` still uses the prototype `*fn-own-body-limit*` value 8192
for ordinary session framing and control submission, while
`host/owner-host.lisp` supplies the store's 32768-byte maximum in the injection
configuration. Owner convergence confirmed this is stale, not an intentional
separate policy. A valid 9 KiB article can therefore encounter different limits
depending on its entry path; the live same-node witness is being added.

Repair: derive the ordinary framing/control limit from the same ACL2 injection
configuration. Preserve an explicitly configured peer inbound override, and
keep any pre-configuration fallback out of the configured served path. The
wire line-capacity repair alone does not fix this separate total-article bound.
The correction is integrated in `e9e1da6`, including configured-limit model
tests. Frozen saved-image owner execution remains pending; the source change
and component certificates do not establish live native parity.

### U06: peer labels double as filesystem paths

Owner convergence found both development and native FNFD adapters constructing
`feed/<peer>.fnfd` directly from the configured label. The ACL2 label predicate
does not exclude separators or traversal components. Thus a valid logical peer
name can escape or collide with the intended directory; merely validating the
native caller differently would create another identity disagreement.

Repair: one ACL2-owned injective filename codec, adopted by both callers, with
explicit legacy journal handling. Preserve existing evidence and refuse ambiguous
migration rather than moving or dropping a journal by guesswork. The native
configuration lane owns the codec and coordinates actual owner adoption. This
is a confirmed code defect; traversal/collision and migration tests are pending.

### U07: normalized default paths bypass their own bounds

At native configuration candidate `b8d760f`, `fn-ncfg-string-value` validates an
explicit value but returns a missing field's default unchecked. A permitted
512-octet store path therefore generates an auth/control path beyond the claimed
512-octet limit. The semantic authority is already ACL2 here; the defect is an
incomplete normalization contract, not a host twin.

Repair: apply the same path bound to supplied and generated values. Test the
maximum store path with derived defaults and with shorter explicit overrides.
The correction is integrated through `c322da5`: both supplied and derived
paths receive the same bound, and line count is checked before parsing. The
[component handoff](lanes/HANDOFF-w14-native-config.md) records certification
and the boundary cases. Native owner/config wiring remains separate.

## Landed consolidation and its limits

Native storage candidate `7ae568b` is integrated: metadata and frontier frames,
transaction names and posting provenance now use ACL2 instead of native copies.
The [source-pinned packet](evidence/native-storage-codec-w13-2026-09-21.md)
records byte-identical committed frames and cross-open tests. It also records
staging-orphan retention and missing-staging-directory differences: removing
serialization twins has not yet established complete recovery correspondence.

## Operator and implementation criteria

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
operator documentation; its [report](lanes/native-cli-duplication-audit.md) and
native migration plan have landed. Independent Claude review in the real tmux
inspected the native I/O boundary at `406578c` and owner candidate `d47212d`.
Its [report](evidence/claude-native-io-seam-review.md) and
[root disposition](evidence/claude-native-io-seam-response.md) identify swallowed
enumeration errors, outcome subtype collapse and I/O progress differences. The
fresh-data-loss claim is narrower after checking the earlier staging barrier;
the owner uncertainty handler has already changed in its active successor.
Concrete repairs are assigned without another serial review gate.

The [operator surface audit](evidence/operator-surface-audit-2026-09-21.md)
records disabled-posting divergence between the CLI and served path, agent-label
ambiguity, inconsistent invalid-option results and port/type validation drift.
It separates executed malformed-input witnesses from source-traced policy
findings. The native operator lane consumes these as contract tests; no Python
repair alone closes D07.

Native I/O outcome/progress repair `3312778` is integrated. Raw deterministic
tests exercise the actual reader handler, preserve fault/uncertain subtypes and
ordinary refusal, and check EINTR, partial progress and zero writes. Root review
also corrected the original test helper's accidental catch of every condition.
Follow-on `28c5b90` sets nonblocking socket descriptors and returns readiness
races to the same absolute deadline. Actual socketpair backpressure/EOF tests
pass. DNS and connection establishment remain outside that deadline contract.

Initializer enumeration repair `6e1f18d` is also integrated. Its regression makes
the real directory listing return EACCES; an error merely raised before the
listing would not distinguish the former swallowing handler. Selected SIGKILL
and independent restart tests accompany the source cut map. That map remains
source-reviewed correspondence, not a whole-program or every-crash-point proof.

### BP successor obligations from the integrated carrier review

`fnn-command-bp-receive` still catches the broad store-error superclass and can
collapse a core fault to refusal; its journal-indeterminate handler does not yet
stop the enclosing receive loop. Separately, `fnn-bp-record` replaces names based
on a constant passive-session tag and session-local transfer ID, which can be
reused across connections. The BP receive successor must demonstrate and repair
cross-session evidence overwrite using one ACL2-owned durable identity and
publication contract. The source-pinned BP handoff records these limits.

FNWF/FNRJ packet `0e26c3d`, integrated through `624f16b`, moves namespace,
record bounds, admission headroom and successor accounting to `books/app-journal`.
The native adapter carries the frontier rather than rescanning on append.
`books/journal-publish` owns the shared immutable publication phases; replacement
and append/prefix-repair contracts remain distinct. Native owner/TCPCL callback
joins and store-fence checks remain pending. Root also found that two test
observers run before their successful barrier observation reaches the model;
the correction is integrated through `2f85d03`, with actual observer phase
assertions. A plain ACL2 authorization
record still relies on a trusted caller reporting ownership and absence honestly.


### U08: listener shutdown does not fence connected writers

The native owner checkpoint `02f82a1` closes its listener after uncertainty,
but `fnn-owner-handle-chunk` and connection opening do not check the stop flag
under the service mutex. An exception handler outside that mutex can also leave
a window before fencing, and main cleanup can close shared journals while
workers remain active. This is a source-confirmed concurrency defect; the
reachable two-client injected witness is assigned to owner convergence.

Repair: establish the fence inside the serialized operation's error boundary,
reject subsequent shared mutations, and drain workers before closing shared
resources. Fault and uncertainty remain different terminal outcomes. The owner
repair is integrated in `6ed4af2`/`ea1592b`, with a compiled listener assignment
fix in `76901c1`. Frozen image/runtime validation is underway. HST-005 still
requires attributable connection-local fault survival; global shutdown alone
does not meet that separate requirement.

### U09: operator plans and effects need one public result contract

Native operator packet `658cfa3` removes the diagnostic payload grammar from
public posting and normalizes malformed configuration to usage rather than
refusal. Its status/recover execution is a component; installed run/post wiring
remains pending. Root found that help still requires valid configuration and
routes to an unavailable owner callback, and outcome words are rendered by
repeated maps. The operator lane owns standalone help and one rendering path.
An accepted command plan must never be printed as accepted durable work.


The application publisher now also uses the existing `fnn-require-writer`
guard (`1556061`), rather than treating any held Store lock as exclusive
mutation authority. Read-only status/replay remain separate from mutation.
The component packet includes actual held-read-lock refusal, held-but-fenced
uncertainty, and observer-phase tests; combined native owner adoption remains
separate.


### U10: retained journal history copied only to test initialization

The [independent shared-state review](evidence/claude-native-state-composition-review.md)
found that `fnn-app-apply` appended every record to a raw retained list whose
only consumers checked whether it was empty. This created avoidable quadratic
list allocation. The repair removes that duplicate state and reads the existing
ACL2 frontier's initialization predicate; no second host counter is introduced.
The [disposition](evidence/claude-native-state-composition-response.md) also
records the owner/standalone global binding required by the pending callback.

Separately, the [actual saved-image store profile](evidence/native-store-cost-w16-2026-09-21.md)
attributes the dominant sampled commit cost to `fn-sf-history-recoverablep`.
Its timings are totals for sequential commits in a test-only scale image,
not single-post latency or a proved asymptotic bound. The active correspondence
lane must derive an incremental prepare entry from the maintained storage
relation and prove equality to the specification before actual host adoption.


### U11: bounds applied after collecting external names

The integrated BP receive-evidence adapter (`33ca412`) obtains the complete
native directory listing before comparing its size with the ACL2 maximum. This
bounds admitted state but fails to bound the allocation used to reach admission.
Use the shared bounded directory observer with the ACL2 limit before collection;
retain the logical validator for the actual namespace decision. The bounded
observer already serves native staging recovery (`9e2d159`). The BP correction is integrated in `7a0b96f`; the raw native I/O suite
passes on that integrated source, including a real directory accepted at the
policy limit and rejected on the next entry. The checkpoint
namespace is under the same audit, alongside its remaining host filename codec.

### Current component dispositions

Receive evidence now uses an ACL2-owned identity and the shared immutable
publisher; actual separate TCPCL sessions with transfer ID zero retain both
wire records. Uncertain publication exits the receive loop, and restart consumes
the visible wire-only identity after recovery barriers. See the
[receive evidence packet](evidence/bp-receive-integrity-w15-2026-09-21.md).
This closes the demonstrated overwrite path, not the pending BP-to-application
acceptance/receipt composition.

Native [checkpoint adoption](evidence/native-checkpoint-w15-2026-09-21.md)
uses the same immutable publisher for generations and a separate ACL2 marker
replacement contract. It preserves authoritative full journal replay and only
compares a checkpoint restore in private state. The host filename grammar,
uncertain-store reuse guard and optional differential-mismatch outcome remain
assigned convergence items. A checkpoint report must not call a known unequal
restore healthy merely because a developer environment switch is absent.


Safe FNFD codec and both recovery callers are integrated through `cf36789`.
The [handoff](lanes/HANDOFF-w14-fnfd-filename.md) records certified codec tests
and explicit empty-v1 crash availability debt. The recursive native observer
still needs a total width/work budget; limiting depth alone is insufficient.
That followup is assigned to the configuration lane. Combined image tests of
these actual caller changes remain pending.

Corrected anchor persistence is integrated through `47562c0`, after a bounded
Sol source review of the final composed path. It uses shared framing helpers
and an ACL2 pre-rename issue phase, then recovery barriers before reading held
state. The [anchor report](../tests/evidence/2026-09-21-native-anchor-replace.md)
separates actual EIO/restart tests from internet interoperability and build gaps.
The earlier unsafe persistence packet is retained as superseded history.
