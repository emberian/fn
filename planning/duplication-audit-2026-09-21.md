# Consolidation audit: assurance and operator pleasantness

Status: active repair work, not a completed audit or release claim. The user
requested an implementation/design scan for duplication and unnecessary
complexity on 2026-09-21. Initial sources inspected: integration `406578c`, native
storage candidate `37ec36b`, and BP convergence candidate `52ab12d`.

The criterion is one owner of each decision, with representations and external
observations explicitly connected to it. A logical model plus a justified
concrete representation is useful, intentional separation. Two host paths that
independently decide whether a publication succeeded are competing authority.
Moving the second path from Python into Lisp does not remove that problem.

## Current-source recheck (2026-09-21)

This section supersedes the owner and pending-status sentences in the historical
findings below.  It is a source audit, not new proof or runtime evidence.  The
source-pinned baseline was `90e0543`, compared with BP publisher `668130de`,
owner fast prepare `df8d191c`, owner/control `a7867753`, auth `d111ef59`, and
transaction recovery `bdd18442`. Subsequent main through `4c21171a` integrates
the publisher, owner prepare, auth receiver, and BP application/receipt join.
Line references below belong to the named baseline or candidate, not necessarily
current line numbers.

- **U01 — landed.**  The visibility-implies-durability fallback is absent from
  `host/native/bp-service.lisp:122-154`; failures in the current private
  lifecycle publisher remain uncertain.  Integrated `668130de` further routes
  this actual caller through the shared publication interpreter, but U01's
  harmful classification is already closed on current `dev`.
- **U02 — landed.**  `host/native/bp.lisp:357-367` calls the ACL2-owned
  `fn-bpn-host-run-outcome` projection in `host/bp-node-host.lisp:158-171`.
  The TCPCL and lifecycle exit helpers have different operation contracts and
  are intentional projections, not copies to collapse mechanically.
- **U03 — landed.**  `host/native/bp-service.lisp:41-69` performs one bounded
  startup observation, `:118-120` obtains canonical record names from ACL2,
  and `books/bp-node-machine-codec.lisp:75-149` owns namespace/token binding.
  `books/bp-node-machine.lisp:369-378` remains the admission owner; append no
  longer enumerates the retained namespace.
- **U04 — lifecycle consolidation landed.** The baseline private lifecycle
  classifier has been replaced. At `668130de`,
  `books/bp-node-machine-codec.lisp:177-222` authorizes the exact pending
  token/record publication and `host/native/bp-service.lisp:122-160` calls
  `fnn-immutable-publish-effect`.  This preserves authority-barrier failure as
  uncertain while treating failure of cleanup after authority as durable,
  because bounded recovery explicitly retains hidden stages.  It does not
  claim that the raw interpreter alone proves phase correspondence.
- **U05 — landed and exercised by the frozen native-owner gate.**
  `books/owner.lisp:614-626` derives the ordinary body limit from the injection
  configuration; configured session and peer-override call sites are at
  `:655-713`.  The source-pinned owner gate includes an actual 9 KiB POST and
  readback, so the historical “saved-image execution pending” sentence is
  obsolete for this finding.
- **U06 — landed in both callers.**  `books/feed-filename.lisp:66-100` owns the
  layout and one total observation budget.  Native pathname projection is in
  `host/native/feed-filename.lisp:18-71`; native recovery consumes it in
  `host/native/owner.lisp:191-281`.  The development bridge also calls this
  codec from `tools/run_owner.py:493-512`; it has no independent peer-to-path
  decision.
- **U07 — landed.**  `books/native-config.lisp:279-285` applies one bound to a
  supplied value or its default, and its actual path projections are consumed
  at `:347-361`.
- **U08 — landed for shared-state fencing.**  The current owner fences under
  the service mutex in `host/native/owner.lisp:395-442`, routes worker faults at
  `:566-607`, and joins workers before closing journals and the Store at
  `:633-675`.  HST-005 connection-local fault attribution is separate from
  this closed duplicate-owner/shared-state finding and is addressed in the
  frozen owner fault-isolation packet.
- **U09 — operator shell landed; public owner-backed post remains frozen.**
  `host/native/operator.lisp:24-48` is the current common renderer, but current
  `:111-124` still reports public `post` as owner-required.  The frozen
  owner/control packet adds the called post/control path at
  `host/native/operator.lisp:86-113,145-156`.  Integrated native auth keeps raw
  Lisp to bounded regular-file transport in `host/native/auth.lisp:12-44`,
  while `books/native-auth-profile.lisp:45-210` owns syntax, credentials,
  posting permission, and protected-transport policy.  That split is an
  intentional semantic/transport boundary, not a duplicate parser.  The same
  frozen image still registers the documented-private low-level
  `--fn owner run` at `host/native/owner.lisp:685-701`; that path invokes
  `fnn-owner-run` without the operator's auth startup hook, while the canonical
  operator path installs the hook at `host/native/operator.lisp:61-87`.  This is
  a packaged-entry/UX boundary defect.  It is not a remote authentication
  bypass: invoking either process already requires local operator authority.
- **U10 — app-history, standalone and shared-owner prepare landed.**
  The duplicate raw application history list is gone.  The Store caller uses
  `fn-spc-prepare` in `host/store-node-host.lisp:379-418`.  Baseline
  `host/owner-host.lisp:273-306` prepared through replaying
  `fn-owner-step`; integrated `df8d191c` changes the actual wrapper at
  `host/owner-host.lisp:275-313` to `fn-opc-prepare` under the maintained owner
  relation.  This is an optimized representation with a correspondence
  theorem, not a second semantic owner.
- **U11 — landed for BP receive, staging, and checkpoint namespaces.**  BP
  receive bounds collection in `host/native/bp.lisp:218-239`, staging uses the
  shared bounded observer at `host/native/io.lisp:1058-1065`, and checkpoint
  recovery bounds before collection and delegates grammar/order to ACL2 in
  `host/native/checkpoint.lisp:45-78`.  The historical statement that the
  checkpoint filename codec is still pending is obsolete.
- **U12 — remaining on current, repaired in the frozen owner/control packet.**
  Current `host/native/io.lisp:2118-2121` still exits with `:abort t` from the
  SIGTERM interrupt.  The frozen packet instead records a monotonic request and
  shuts down the captured listener descriptor at
  `host/native/io.lisp:2065-2067,2122-2136`; its owner loop consumes the request,
  stops service, drains workers, and only then closes shared state in
  `host/native/owner.lisp:836-930`.
- **U13 — remaining on current, transaction half complete in a pending packet.**
  Current `host/native/io.lisp:854-857,1034-1056` still has raw transaction
  grammar, `parse-integer`, gap policy, and an unbounded directory observation.
  Pending `bdd18442` replaces that path at `host/native/io.lisp:1053-1076` with
  a bounded observation and ACL2 transaction plan.  The neighboring config
  namespace remains raw even after that packet:
  `host/native/io.lisp:910-924` formats `~8,'0d.cfg`, suffix-filters, and lists
  without a pre-collection bound.

### Deployed-path cleanup and intentional separation

Four loaded projections had no caller at the audit baseline in source or native tests:
`fn-jpub-host-initial` and `fn-jpub-host-crash-outcome` in
`host/journal-publish-host.lisp:6-19`, and `fn-bpn-host-machine-statep` and
`fn-bpn-host-machine-max-records` in `host/bp-node-machine-host.lisp:10-11,79`.
They are safe candidates for removal after the pending BP publication packet is
integrated and its final wrapper set is known.  This finding does not include
wrappers invoked by development bridges through constructed ACL2 symbol names.

The following repeated shapes are intentional: immutable no-replace
publication versus allocation-frontier, checkpoint-marker, and anchor atomic
replacement; Store and owner fast-prepare representations connected to their
replaying specifications; and ACL2 semantic parsers paired with bounded raw
file/path transport.  They should remain separate until a named correspondence
establishes that their durability, overwrite, or recovery contracts match.

### Prerequisite-ready consolidations

1. Landed: `668130de` and its evidence tip replace the last private BP
   lifecycle classifier with the shared ACL2-owned publication contract at the
   actual `:persist` caller and retains exact token/record echo checks.
2. Integrate owner/control with the now-landed owner fast-prepare and native-auth
   packets on one reconciled ancestry.  Make the packaged production entry
   dispatch only through `operator`, or gate the raw `owner` verb into an
   explicit diagnostic build, so a shipped invocation cannot accidentally
   omit configuration and auth startup dependencies.  This closes the actual
   owner caller in U10 and the pending U09/U12 service joins; changing a verb
   name alone is not security isolation.
3. Integrate `bdd18442`, then give `fnn-config-record-names` the same pattern:
   bounded physical observation followed by an ACL2-owned canonical name and
   contiguous-generation plan.  This closes U13 without inventing another
   generic namespace framework.

After the U04 publisher is present, the next concrete publication consolidation
is the actual authored-wire call
`host/native/bp.lisp:173-186,403-405` from raw replace to an ACL2-authorized
immutable no-replace publication.  ACL2 already owns its sequence; the new
authorization must assert the exact absent final name and preserve uncertainty
from link attempt through the authority directory barrier.  Keep the mutable
sequence frontier at `host/native/bp.lisp:133-171` on its distinct replace
contract.

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


The native operator join is integrated through `67f45a3`, with source-pinned
component help/status/run and hard-I/O classification evidence. Followup
`dc57e7c` replaces an invalid-config sentinel with an explicit ACL2 command
preflight result; the host no longer induces an error to discover whether it
needs to read configuration. Public posting remains a shared-owner channel
implementation task. Its pending native entry must not reinstate the old
standalone-store fallback as an alternate acceptance path.


### U12: native process termination bypasses orderly owner shutdown

At `dc57e7c`, the SIGTERM handler in `host/native/io.lisp` calls `fnn-exit`,
which invokes `sb-ext:exit :abort t`. That bypasses the native owner's
`unwind-protect` worker-drain and cleanup path. Process death/recovery safety
is a separate contract from an orderly service stop; the development Python
service's clean SIGTERM behavior must not be attributed to this adapter.
A native successor must route a shutdown request safely, without acquiring a
possibly interrupted mutex in the asynchronous handler, and test SIGTERM
with active clients followed by independent reopen. Owner convergence tracks
this after the current guarded feed/build batch.


The total FNFD observation budget is integrated in `399d4730`. It threads one
ACL2-selected remaining allowance across root, children and siblings rather
than resetting a per-directory bound. The raw sibling-exhaustion regression
passed again on integrated source, with both journals retained. The handoff
records separate ACL2 certification; this is not a saved-image service result.

BP lifecycle namespace consolidation is integrated through `773db914`: ACL2
owns the canonical names, token binding, recovery frontier and admission;
append no longer rescans retained files. Physical enumeration is bounded before
allocation, and recovery list reversal is linear. The
[handoff](lanes/HANDOFF-w17-bp-namespace.md) pins the final component DTN build
and actual-handler tests. The remaining raw lifecycle publication algorithm
is now a separate shared-publisher adoption task; namespace consolidation does
not establish that phase correspondence.

The live store prepare correspondence is integrated through `ef6a0177`.
`fn-store-sn-prepare` now calls `fn-spc-prepare`, equated to the replaying
specification under the maintained live-history relation. The
[evidence](evidence/store-prepare-correspondence-w18-2026-09-21.md) records
the nonempty-history witness, separating stale-node counterexample, certification
and saved-image storage tests. Its cost probe uses a different platform from the
baseline and is not an absolute speedup or asymptotic claim. Adoption inside the
shared owner remains a separate caller/relation task.

### U13: transaction recovery still has a second namespace parser

Source inspected at `ef6a0177`: `fnn-transaction-files` collects the entire
transaction directory before checking the configured count bound. Its raw
`fnn-seq-name-p`, `parse-integer` and sequence-gap loop also decide namespace
validity independently of the ACL2 byte-store scan and transaction-name codec.
The comment calling the count check a physical enumeration boundary is stronger
than the implementation. No live exhaustion reproducer is claimed by this scan.

Repair: collect names with the shared bounded observer, let ACL2 validate their
canonical sequence and binding to decoded records, and preserve explicit faults
for gaps, unexpected entries and symlinks. The initializer lane owns this as a
separate successor to its current EEXIST/crash packet.

The neighboring configuration namespace also uses raw `~8d.cfg` construction,
suffix filtering and unbounded enumeration. The administration lane will share
its ACL2 filename codec with the existing builder; complete configuration
namespace recovery/budget correspondence remains an explicit successor.


### U14: control endpoint ownership differs from Store ownership

The [cross-model review](evidence/claude-control-lifecycle-review-w28.md)
found that two distinct Store roots can select the same explicit control socket
path. Their separate Store locks do not authorize unlinking that shared endpoint;
the later process can replace a live socket and receive the first operator's
submissions. A lease on the endpoint itself must precede stale-node removal.
A successful or refused connect probe alone does not serialize concurrent starts.
The native-control lane owns this correction and a two-store collision witness.

The same review identified a raw-descriptor lifetime concern: a stopping thread
must not close a descriptor while a worker may still use its cached integer.
Shutdown wakes the worker; final close belongs after that worker's last I/O.
Shutdown followed immediately by close does not eliminate descriptor reuse.
This is source-level concurrency analysis pending the lane's controlled witness,
not a claimed stress-test failure.


### U15: new BP join and feed input revalidate all retained state

At main `749dbf5b`, `fn-bpaj-apply-record` and `fn-bpaj-request-status`
call `fn-bpaj-statep` over every retained intent, context fact and receiver
entry. Intent validation decodes previous request ADUs again. These calls are
on the native request path, not just recovery. They violate the no-whole-state-
validation served-path rule and add work proportional to retained history to
each step. The native BP application successor owns replay establishment,
transition preservation and justified fast caller adoption. Lookup/index costs
are separate from removing redundant invariant checks.

Pending feed packet `3ecbc4cb` similarly calls `fn-fc-tablep` over every peer
and retained input in its dial/read/loss wrappers. Its uniqueness recognizer
repeats tail traversals. A separate pure table invariant packet will establish
initialization, put/remove preservation and selected lookup validity; the host
will validate only the selected bounded connection state. Runtime activation
also waits for bounded socket reads and worker-owned descriptor cleanup.
Neither work item is closed by an opaque host flag, an unchecked executable
branch, or a theorem assuming its own output is already well formed.


### U16: verifier shape was reported as password confidentiality

`books/auth-secret.lisp` and the AUTHINFO specification inferred secret
confidentiality from a fixed-length digest and a structured verifier. Those
facts do not establish secrecy or guessing resistance. The implementation is
one salted, tagged SHA-256 verifier, with no password work factor. The claims
are corrected in source comments and [the specification](../specs/nntp.md#the-stored-authinfo-credential).
Native administration preserves this format for compatibility; password
hardening, versioned migration and verification resource limits remain a
separate authentication-profile task. No cryptographic primitive was changed
and no proposed suite was silently selected.
