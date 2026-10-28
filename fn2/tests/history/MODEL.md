# H3 observation model

This document precedes the checker implementation. The contract is:

> H3, the history observation model: Jepsen/Elle-style history checking for the consumer protocol (register/poll/ack/position/rebase/wait: at-least-once delivery, forward-only durable ack, redelivery before ack, no lost wake) and for durable acceptance under crashes (an acknowledged POST survives any crash cut); the checker consumes observation logs the simulator and the native harness both emit.

## Numbered definitions

1. **Record and order.** A history is a JSONL sequence of objects with exactly
   `process: str`, `type: invoke|ok|fail|info`, `f: str`, `value: object`,
   `time: int` (nonnegative monotonic nanoseconds), and `index: int` (strictly
   increasing, nonnegative). Time never decreases globally; equal times use
   index order. Each process has at most one outstanding invocation. The
   completion has the same f. Completion values augment invocation values;
   request scope/epoch and ack target are not replaced by response metadata.
   A response cursor belongs in `position`, a poll request in `cursor`.
   JSON values are copied on construction. Unknown f names are invalid.

2. **Outcomes.** `fail` asserts definitely not applied (effect not attempted,
   or a named refusal before mutation); `ok` asserts applied and observed;
   `info` asserts attempted, outcome unknown. An info mutation may have applied
   once or not at all, never partly or twice. Timeout, lost reply, uncertain
   persistence and a crash before reply are info, never fail. An invoke without
   completion is allowed only across an observed crash; pairing synthesizes an
   info completion at that crash. An ordinary unfinished log is a named error.
   A crash's ok completion closes every outstanding operation on its node,
   across all client processes; the nemesis itself is excluded. With no `node`
   field, the history describes one node, named `default`. Late completions
   after a crash are malformed, not evidence changing an info to ok. The native
   adapter counts late transport replies and omits those completions, retaining
   the invocation closed as info by crash pairing.

3. **Observation scope.** Every consumer value has `consumer`, `epoch`, `scope`
   and `node`. Scope is an object containing `history`, `incarnation`,
   `principal`, `query`, `query_version`, `view_version`. State is keyed by node,
   consumer, epoch and scope; rebase starts a fresh scope at zero even if its
   epoch is retained. Group names, article numbers and timestamps are NOT
   record positions. Crossposted articles can have different positions on
   different nodes. Visibility is observed under the selected version, not
   recomputed from current configuration. Scope changes are explicit. The
   test workload retains content, preserves authorization in each scope, and
   serializes mutations of each registration (different consumers and posts
   may overlap). Reads may overlap mutations; real-time precedence means
   completion index < invocation index. These are finite safety checkers,
   not a complete linearizability solver or a claim of eventual completion.

4. **Consumer values.** `register`/`rebase` return `position` (zero for a new
   registration/scope); duplicate register retains position. `unregister`
   removes the current registration. `ack` invokes with `position`.
   `position` returns `position`. `poll` and `wait` invoke with `cursor`;
   ok returns `events: [[position, message_id], ...]`, `position` (scanned
   continuation), and `more: bool`. All positions are nonnegative integers.
   Positions in a page are strictly increasing, greater than cursor, and no
   greater than continuation. A withdrawal report FNWD1 is an event naming the
   withdrawn Message-ID at its own record position; it is NOT article content.
   The same Message-ID at two positions denotes two events. `event_kinds` can
   annotate those positions as article/withdrawn; checkers key by position and
   Message-ID. Empty scan pages can advance the continuation without acking.
   A refusal carries `reason`. Wait invokes with `deadline` in the same clock.

5. **C1: forward-only durable ack.** Prior ok acks are lower bounds on any
   subsequent ok ack; equal is idempotent, lower must fail. Position after
   recovery is at least the last preceding ok ack and no greater than any
   possibly applied ack target invoked before that read completes (or the
   registration baseline). Info acks establish only possible upper bounds
   until a position confirms them. Failed acks establish no bound. A position
   increase impossible without a mutation is C6 when a poll/wait intervened;
   an ack regression/recovery bound breach is C1. Attribution prevents one
   planted poll mutation from being counted twice. Consumer spec L103-123,
   L152-157, L347-352.

6. **C2: at-least-once until ack.** A delivered event above durable ack remains
   an obligation. A later successful page may not start past it, or scan past
   its position while omitting it, without a covering ok ack. An info ack
   counts only with a later position confirming at least that target; that
   confirmation may follow the page. A covering ack overlapping the page
   may explain the omission; it must have been invoked before page completion. Finite histories ending with unacked events are not violations.
   Merely failing to repeat in a page whose continuation has not reached the
   event is not a violation. Since scans are strictly AFTER a cursor, starting
   AT an unacked event also skips it. Unavailable/reclaimed content is outside
   this retained-content profile; an explicit refusal/gap cannot be treated
   as an empty page advancing over content. Consumer spec L81-103, L347-352.

7. **C3: acked never redelivered.** A successful page may not contain an event
   at or below an ok ack completed before its invocation in the same scope
   and epoch. An overlapping page may have pinned before that ack. This is the
   consumer-from-durable-ack workload, not arbitrary historical cursor reads
   allowed by the general cursor API (consumer spec L70-75, L81-90).

8. **C4: no lost wake.** `check(history, slack_ns=0)` uses nonnegative slack.
   A post ok supplies `visible: [{consumer, epoch, scope, position}]` for each
   eligible consumer. An empty wait completing at/after its deadline is a
   lost wake if such a post completed before invoke.time + slack_ns AND before
   the deadline, its position exceeds the request cursor and preceding ack,
   and no covering ack can explain its disappearance. Equality in the time
   cutoff is excluded. Nonempty waits must return events strictly after cursor.
   C4 also reports early empty deadline returns. Page order/continuation
   violations are reported as C2 (wait cursor violations belong to C4).
   No visibility entry means unknown eligibility, not an inferred permission.
   Consumer spec CNS-007 L384-407; ROUND2 F scenarios 7-9. This is the requested
   bounded observation check; it does not prove every commit during a wait
   wakes within a scheduler bound.

9. **C5 and C6.** An ack carrying an epoch removed by an ok unregister or
   replaced by a subsequent registration must fail; ok is C5 (info alone is
   not proof of acceptance). A scope replaced by rebase is similarly fenced.
   Poll/wait never changes durable position: a later position must be a
   registration baseline or a possible ack target, not a poll continuation.
   C6 requires an intervening poll/wait witness and no intervening possible
   mutation explaining the position. Consumer spec L89-90, L109-123, L395-400.

10. **Node values and digest.** `post` has `message_id`, `digest`, `node`;
    completion `code=240` is ok, 440/480 or a definite 441 refusal is fail
    with reason, uncertain 441 is info. Digest is a comparable observer digest
    of payload body octets (CRLF, unstuffed, excluding NNTP terminator), not
    fn's content identity and not injected headers. The native adapter uses
    SHA-256; simulator values may use stable symbolic digests. `read` names
    message_id, or group+number with an explicit observed message_id binding,
    and returns code 220/221/223 or 430/423, plus digest when actually observed.
    A completed negative read is type ok: the read applied and observed absence.
    HEAD/STAT show presence but cannot supply a body digest. All checked reads
    use a fresh recovered view with unchanged authorization; a stale pin or
    denied read is not a durability counterexample (NNTP spec L791-808).
    `crash` invokes/returns `{node, cut}`; `recover` returns `{node, posture}`.
    Only ok recover with posture `ready` enables recovered-read checks.
    Extra `withdraw` operations carry message_id and `authorized: true` on ok;
    observing a withdrawal report alone does not establish authorization.

11. **D1.** For each post ok/240 completed before a crash, every completed read
    invoked after a subsequent ready recovery returns presence and the posted
    digest if available. Absence is D1, "lost acknowledged post"; a different
    digest is D1, "changed acknowledged post". Authorized withdrawal between
    acceptance and read suspends that obligation. Recovery crashes do not
    erase earlier obligations. Missing reads/digests mean missing coverage,
    not a positive durability proof. NNTP spec L734-749, L790-815.

12. **D2.** A refused fresh POST contributes nothing: later presence without
    any other possible submission of that ID is D2. Literal "a refused POST
    is never readable" conflicts with duplicate/conflict refusals (NNTP spec
    L747-764): an already stored article remains readable. Those reasons are
    excluded, as are IDs with another ok/info submission before the read.
    The workload starts with fresh IDs; external imports must be recorded as
    submissions. The checker cannot infer causality for two competing attempts
    of the same identity. This qualification is essential, not a weakening of
    the no-mutation guarantee.

13. **D3.** Following an info post, reads after ready recovery agree on absent
    or present with that digest, never both. Another possible submission or an
    authorized withdrawal ends this settlement interval (an absent uncertain
    attempt may legitimately be retried). A wrong observed digest is also D3.
    No recovery/reads leaves the operation unresolved. NNTP spec L745-749;
    consumer spec L152-157. Refused attempts cannot cause a settlement change.

14. **Fault profile.** C1 durable progress and D1-D3 assume ROUND2 E.5's honest
    persistence barriers (`A-PERSISTENCE-FENCE`), no later destruction of
    durable data, one authoritative history/incarnation, retained content,
    complete mutation observations and honest observer payload comparisons.
    Corruption, rollback and loss of every independent witness require E.5's
    separate integrity/frontier assumptions; these checkers do not establish
    those claims. Crash/recover are observations, not commands executed by a
    checker. Every checker is a pure history -> list of Anomaly(kind, ops,
    explanation); ops are contributing original indices.

## Simulator emission

Layers A-E must emit these events into this JSONL format; H3 does not implement
simulator instrumentation. A scenario's sidecar records revision, seed, profile,
fault choices, persistence assumptions, retention and quiescence bounds.

- Invoke and exactly one ok/fail/info for register, poll, wait, ack, position,
  rebase, unregister, post, read and authorized withdraw. Record request values
  BEFORE dispatch and reply values only when the client actually observes them.
- Stable process IDs per sequential client, node identity, global observation
  index and monotonic simulated ns; overlapping clients have different IDs.
- Full consumer scope and registration epoch on EVERY consumer operation;
  both request cursor and scanned continuation, every event's position and
  Message-ID, more flag, refusal reason; no truncation or guessed event lists.
- Wait deadline and the configured checker slack; post completion eligibility
  entries with scope/epoch/consumer and committed event position. Visibility
  must name the pinned authorized view, including crossposts and withdrawals.
- POST offered Message-ID and body digest, exact outcome code and reason;
  mark ambiguous persistence or lost replies info even when the simulator
  privately knows the final disk result. Record independent later read probes.
- Fresh-view read target/binding, status and body digest (when content read).
  Record authorized withdrawal explicitly; do not infer it from 430 alone.
- At EVERY process-death cut, a crash pair identifying node and named cut;
  outstanding operations become info. Record repeated recovery death cuts too.
  Restart emits recover with ready/refused/uncertain posture; read probes after
  ready recovery settle unknown posts and a position probe settles unknown ack.
- Emit unregister/re-register and rebase scope transitions, old-epoch probes,
  poll-position probes and retained-content redelivery probes. A missing probe
  is missing coverage; a checker returning [] is not a coverage certificate.

## Native adapter and evidence gaps

H3b records paired PID/counter `call` IDs, Node scratch-root `node` and `control`, and per-Client
`conn` IDs (unknown nodes use `port:N`). Correlated nested transport is consumed as evidence of its
operation; legacy signature pairing and `files` remain supported. Ambiguous legacy overlaps remain
unmapped. `adapt` returns history plus per-source-index unmapped reasons/counts; it never opens live
paths.

`send` captures full `sent_hex` through 1 MiB; above that it records the first 64 KiB, `sent_sha256`
and `sent_len`. Complete POST sends supply Message-ID and the definition-10 body digest after CRLF
dot-unstuffing and terminator removal. A truncated send's wire checksum is NOT a body digest.
Received ARTICLE blocks supply body digests; HEAD/STAT supply presence only. POST refusals before
sending an article still lack its identity. Incomplete exchanges remain info.

Node invoke/operator/store capture existing file arguments immediately before and after calls: hex
through 64 KiB, otherwise `{sha256, length}`. The adapter uses `files_after` for output
cursors/reports and `files_before` for ack targets. Cursor IDs use reversible Latin-1; empty/FNWD1
reports and JSON report identities are decoded. Native CLI still lacks `more`, and text article
reports lack a projected identity. Those pages remain observed-only with missing-evidence counts.
`history_value` remains explicit supplementary evidence: the synthetic complete `captured.jsonl`
supplies `more` this way; it is not a captured native run.

Starts retain `env_selectors`; selectors arm faults, never prove reached cuts. Node stop and
returned NativeProcess signal/finish records retain exit class, signal and declared death cut. Only
matching exit status AND captured marker name a reached cut; otherwise it is unknown. Repeated exit
observations are coalesced, clean stops are lifecycle bookkeeping, and successful starts recover.
Raw process kills without a subsequent observed finish/stop, raw send/line protocols, CLI calls
through standalone `run`/Popen, and fn_agent/fn_consumer subprocesses still bypass semantic
adaptation. Selected visibility, pinned frontier and fresh authorized read premises still require
workload evidence; connection IDs alone prove none of these. Simulator emission remains owed to A-E.
Zero anomalies or unmapped records alone cannot qualify all nine checks.
