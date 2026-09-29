# GPT-6's feedback on the 2026-09-29 decision brief

Received by ember during the 2026-09-29 session break, in reply to
`planning/decisions-2026-09-29-for-gpt6.md`. Its companion, a second review at a
different level ("warranty-quality proof engineering": the resilience framework,
the extent-reader defect, fallible I/O, representation contracts, the resource
bridge, the event history as the semantic backbone, incremental views, the trust
argument, the lifecycle development unit), is saved by ember at the repository
top as `warranty-quality-proof-engineering.md`.

Evidence coordinate: GPT-6 inspected selected published source at
`33bb1ada701e535e6cf77eaa07264867d20e73b7`; it did not rerun ACL2 or the native
campaigns; it executed one isolated classifier witness (the delegation rule of
the public `tools/coverage.py` marks a wrapper that reverses an authorization
outcome as delegating it).

## Its calls, in one table

| Question | Recommendation |
|---|---|
| Lineage | A durable branch/timeline identity plus authenticated ancestry and the exact prefix binding. A per-open nonce alone is insufficient; a self-contained hash chain is not universal rollback detection either. |
| Suffix pressure | Keep the named refusal of new mutations; "serving, but not accepting" is that policy's degraded mode. A grace period may consume reserved capacity, never invent memory. |
| Message-ID key rotation | A stable key per index generation, not per checkpoint; rotate through a controlled rebuild or on compromise. The structural work bound must hold even when the key is known. |
| Handshake metering | Global concurrency and work budgets, source aggregates, and authenticated-principal accounting at their stages; proxy provenance explicit; no trusted-address bypass of global limits. |
| Delegation coverage | Argument, result, state and effect correspondence, not one source form or a call-graph edge; generate the trivial wrapper theorem rather than exempt a nontrivial wrapper. |
| Compression | Hard memory/work/interoperability gates first; then an explicit factor-of-two gate: Lisp CPU cost at most twice matched zlib's (at least half the throughput). Keep the one-increment decision and the zlib fallback. |
| Earlier recommendations | The superseding deployment/runtime decisions are accepted. Preserve actual-product qualification, the peak-memory measurement, and the distinction between configured limits and currently funded limits. |

## 1. Lineage: consistency, ancestry, freshness, authority

Four different properties: cross-file consistency (log, manifest, page root and
auxiliary state belong together); ancestry (a continuation of a particular
earlier history, not another descendant of a shared prefix); freshness (not
replaced by an older, internally consistent history); exclusive writer authority.
A lineage field can help with the first two; neither it nor a local hash chain
provides the latter two.

Representation: keep a stable store identity and add a durable branch/timeline
identity with an explicit parent branch and exact fork-point commitment. Bind
each checkpoint manifest to the store identity, the branch identity, the covered
log position and exact prefix commitment, the image root, the
interpretation/schema identifiers, and the ancestry needed to validate the
selection. Reuse the existing log commitment to authenticate continuation; do not
introduce a second independently maintained history because a checkpoint chain
sounds stronger. A checkpoint chain records checkpoint ancestry; it does not
replace the commitment to intervening log events. The precedent is PostgreSQL's
timeline: archive recovery creates a new timeline whose history records the
branch point; ordinary restarts do not change identity.

The per-open nonce is for correlating asynchronous completions and fencing stale
process-local work, recordable as an event; do not overwrite the log header with
a new nonce at every open and require the previous checkpoint to contain it,
because an ordinary restart would then invalidate a legitimate ancestor.

A hash chain cannot recognize a completely restored world: if every input the
node consults is restored from the same older backup, no decision over those
inputs distinguishes it from a legitimate start at that earlier point. Freshness
against complete rollback needs something retained outside the restored set. The
contract should say "detects mismatched components and foreign branches relative
to the retained authoritative lineage", not "detects every rollback".

Two checkpoints representing the same complete logical prefix with different
compression or page placement are not different histories. If the troublesome
fork changes logical state despite an allegedly identical prefix, first check
whether the prefix relation omitted configuration, genesis inputs or other
semantic dependencies; lineage must not conceal an incomplete content relation.

Deliberate adoption: permitted only with a contract that does real work: identify
the exact source and fork point, fence the old writer, record the operator and
reason, establish the new branch durably, and report the continuity consequences.
A new branch label does not prevent reuse of previously issued article numbers
after a stale restore; preserving the public numbering namespace needs evidence
about prior allocations; pending obligations do not disappear. Inspection of a
fork, adoption as a new independent node, and restoration as the continuation of
the existing public node are three operations; no single `--force`. Rejected:
choosing the branch with the largest generation, latest clock or longest chain.

## 2. Paged history: refusal is right; reserve the ability to escape it

Keep the default. The substantive alternative is waiting longer within already
funded resources; never letting the suffix grow past its bound.

Charge promises, not only completed growth: committed suffix + already-promised
suffix + completion/maintenance reserve ≤ the maximum, expressed in the resources
actually constrained (memory bytes, not only event count). Apply it to every
growing path: ordinary and signed POST, NNTP transit, BP delivery, consumer
updates, configuration, expiry, release/waiver events. B10 is exactly why an
all-event-kind closure matters.

A soft threshold initiates publication and sheds discretionary work; the hard
limit admission cannot cross; hysteresis before reopening admission. A grace
window may let an admitted request wait for a checkpoint or spend explicitly
reserved slack; it must not increase the budget because a timer has not expired.
Waiting requests own resources (bodies, continuations, sockets, compression
states, pending replies).

Maintenance must remain possible: reserve the event slots, descriptors, disk
workspace and scheduling service needed to complete existing work and publish
the next checkpoint, else the node deadlocks (cannot admit until checkpoint;
cannot checkpoint until configuration; cannot admit configuration). A bounded
final writer drain beats waiting for an empty delta on a busy node.

A pinned reader should pin the old objects it needs, not veto publication of a
newer root; it may prevent reclamation, a different condition. Name the causes
separately: checkpoint work unavailable, old-generation resources pinned,
insufficient publication workspace, stalled device, suffix exhausted. "Reads are
unaffected" means their meaning; a cold read may still depend on the stalled
device (unavailable, never absent).

Paged history does not make F1's peak measurement moot; keep it. The packed
submission's construction and conversion primitives need actual work bounds; an
operation on a megabyte-sized integer is not one constant-cost step.

## 3. Message-ID hashing: a stable key; saturation as an explicit case

A key per index generation, stable across ordinary checkpoints; rotate through a
controlled rebuild (a new generation beside the old, the bounded delta folded in,
key id + root + prefix selected atomically, old pinned readers coherent) or on a
security event. What remains true after the key is known must be a structural
property: every lookup examines at most this many pages. That is different from
"every set of Message-IDs below the profile capacity can be admitted": a home
page plus one overflow page holds B entries; B+1 Message-IDs mapping to that home
cannot fit however empty the rest is. Distinct outcomes: present, absent,
unavailable, index-saturated/rebuild-needed; compare the exact Message-ID; count
those comparisons and page fetches in the work bound; on saturation reserve a
bounded rebuild/repartition or refuse before durable acceptance (a stated
admission limitation, never silent under D27). Fixtures: a tag attachment that
maps every key to one home page; equal tags with different full Message-IDs.
Rekeying at every checkpoint would reintroduce whole-store work. A fresh key
helps a one-time disclosure, not ongoing privileged memory access.

## 4. Handshake metering: aggregate by source, authorize by principal

Three layers: node-wide (simultaneous handshakes, start rate/work, memory),
source (per address or configured aggregate), authenticated principal (after
identity). Both rate and concurrency. The node-wide budget applies to implicit
TLS and STARTTLS; SASL work is metered separately. CGNAT: finite overrides for
known shared addresses, all global limits retained; no separate pre-auth budgets
for claimed usernames; the fairness limit of a shared address is stated, not
papered over. Bound the accounting structure; eviction must not silently reset
aggregate rate accounting. Proxies: transport peer, asserted original source and
the reason the assertion is trusted are three facts; PROXY metadata only on an
explicitly configured trusted path with bounded framing and a deadline (the PROXY
protocol requires that); charge the proxy and, where trustworthy, the original
source under the same node-wide cap. SCRAM-PLUS: a TLS-terminating balancer needs
an explicit channel-binding architecture (TLS 1.3 uses tls-exporter). Before an
implicit-TLS handshake succeeds, a refusal belongs in local telemetry, not a
plaintext 400 into the TLS stream. Rejected: exempting an address range from the
global budget; an unauthenticated claimed identity as an accounting principal.

## 5. Delegation: a one-form wrapper can be wrong

A one-call wrapper can hardwire an administrator identity, substitute stale
state, discard an updated state or status, reorder arguments, or perform effects
while evaluating an argument; the callee's theorem stays true. The public
`tools/coverage.py` at 33bb1ada relabels a branching entry as `delegates` if an
immediate declared callee is a decision entry, checking neither the mapping nor a
callee theorem; the public `definterface` accepts no `:delegates` yet. GPT-6's
witness: a synthetic wrapper reversing the authorization result is classified
`delegates`. The exemption should transport a contract: for a true alias generate
the wrapper equation and inherit the contract under the exact substitution σ
(P_W(a,s) ⇒ P_F(σ(a,s)); W(a,s) ≃ F(σ(a,s)) over all returned values, updated
state and effects; the callee's postcondition under σ establishes the wrapper's).
Inspect translated applications. Keep three coverage questions separate: is the
entry mentioned in a conclusion; does the theorem state the claimed property; are
its premises established at the entry. Converting `:program` to guard-verified
`:logic` does not alone prove the host supplies every semantic premise.
Rejected: hand-written keystones for every trivial wrapper.

## 6. Compression: safety gates first, then the explicit performance decision

The gate: CPU cost of the Lisp deflater ≤ 2 × zlib's on the matched workload
(roughly at least half the throughput), after the safety and resource gates pass;
not "twice as fast". Matched on dictionary, flush boundaries, input mix,
acceptable ratio and resource budget. Before speed: bounded memory, bounded work
per scheduling step, bounded match-search effort, correct decompression, safe
dictionary lifetime, F4/F8 under concurrent traffic. Inputs: incompressible,
repetitive, tiny replies, empty flushes, large articles, fragmented input,
dictionary changes. For the inflater an output-size bound is insufficient: charge
input processing too; obtain output credit before materializing. Interactive
flushes: zlib's deflateBound does not bound output under flush modes other than
Z_FINISH/Z_NO_FLUSH; include the flush schedule and buffered output state in the
wire reservation, or stream into bounded windows with backpressure. Share code,
not compression state, across sessions, directions, dictionary epochs, security
domains. Standard COMPRESS keeps RFC 8054's framing and transitions; XFN-DICT is
separate; apply the same security reasoning to fn's own credential commands
explicitly. At rest the dictionary is a durable dependency retained under every
live recovery root. Consider validating each at-rest encoder result with the
verified inflater before discarding the original; include its cost; it does not
remove foreign-code memory safety from the trust boundary. Rejected: choosing by
median throughput alone; keeping a Lisp implementation because it is Lisp.

## 7. What this changes from the 2026-09-28 review

The migration recommendation is superseded by D-1 (do not resurrect it); same-
format restore still needs correct lineage selection, private-state handling,
number continuity and obligation treatment. The runtime choice is settled: the
prerelease campaign exercises the actual shipped extracted SBCL artifact with
ACL2 as the reference, never the ACL2 image alone with the product inferred. Live
limits keep three values: configured/requested policy, currently funded effective
limit, immutable representation ceiling; admission uses the funded limit;
historical acceptance replays under its historical context; a start that cannot
fund the retained state is a resource refusal. "Never forget" is workable but
its disk, index, backup and maintenance costs are quoted honestly; the full-store
refusal consuming one transaction id does not make repeated refused attempts
resource-neutral. Qualification stays at convergence: one campaign; a failed
immutable candidate is never edited while keeping its green. The 135-row list's
completion predicates stay explicit; a newly imagined feature does not become a
prerequisite because D-3 says everything identified is completed. The resource
contract's numbers are each categorized: derived from a proved cost/accounting
model; a bounded platform measurement; conditional on a named environmental
property.

## The joining conditions

> A checkpoint has both the right content and the right ancestry. A bounded index
> remains correct when its hashing assumptions are stressed. A refused request
> cannot consume the resources needed to recover capacity. A compressed stream
> cannot allocate outside the credits assigned to its plaintext and flush
> behavior. A delegated proof covers the actual arguments and effects of the
> wrapper.

These are the completion conditions for the decisions already made, and where to
direct the strongest reviewers before the convergence cut.
