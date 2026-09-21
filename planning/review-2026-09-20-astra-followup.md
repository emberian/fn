# Independent follow-up: fn's latest integration and assurance

Reviewed revision: `664711ef4ff971c83af5306988253980f7ade1fb`.
Baseline: `3e1b184`. Review date: 2026-09-20 America/New_York.
Claude continued working during this review. This is a frozen-source assessment,
not a verdict on unmerged work or on later commits.

Late-update check: through `0308dd4`, the subsequent fault-test work reports a
passing native served differential and repairs stale test interfaces. Those are
additional positive results, attributed to that lane rather than rerun here.
The source paths underlying F1–F4 did not change in that interval.

**There is substantial progress, but the project is not yet demonstrating a
high-assurance running news service. The recurring problem is composition:**
functions, theorem families and harnesses advance individually while the
connection between them remains unfinished. The most concerning concrete defect
is that the integration gate can observe its promised behavior failing and still
return success. That makes the development feedback loop less trustworthy.

This is not evidence that the ACL2 work is worthless or that certification was
fabricated. Several handoffs explain their counterexamples and missing premises
quite candidly. The next work should turn those discoveries into completed
vertical paths, with failures that stop the corresponding release claim.

## Findings

### F1 — High: the two-node gate downgrades exercised failures to gaps

In [scenario_feed_peer_cut](../tools/twonode_gate.py), lines 1400–1433,
failure to serve the article after the connection cut, repeated accepted
transfers, and an incorrect final group count only append to `self.gaps`.
The arrival probe uses `expect=None`. `Step.failed` in
[deploy_gate.py](../tools/deploy_gate.py), line 169, consequently does not mark
that nonzero probe result as a failure. The gate's final exit calculation at
lines 1684–1692 considers failed steps and exceptions, not these scenario
assertions. The restart scenario uses the same pattern.

**Reproduction:** [probe.py](evidence/astra-followup-2026-09-20/probe.py) invokes
the actual scenario method with simulated boundary responses. A taken cut
followed by nondelivery, duplicate acceptances, or the wrong group count leaves
no failed steps; the actual main function's exit expression consequently
selects success. [Output](evidence/astra-followup-2026-09-20/probe.json) preserves
the gate's own explanatory messages. This is a harness reproduction, not a
network or ACL2 test.

An unavailable feature can legitimately be unexercised. An exercised scenario
that violates its stated assertion must be failed. A scenario with insufficient
observation must remain inconclusive, not establish a release claim. Retain
those distinctions in machine-readable results and in the process exit status.
Do not fix this by failing every standing limitation in `gaps` indiscriminately.

**Completion condition:** inject each bad outcome into the scenario and require
a failed scenario and nonzero gate exit; an explicitly optional, unavailable
feature remains separately reported as unexercised. Run the corrected gate
against the real nodes before claiming loss-reply recovery.

### F2 — High: socket loss does not invoke the feed's retry transition

[Owner.feed_drop](../tools/run_owner.py), line 926, closes the socket and calls
`feed_connect(peer, None)`. The bridge reaches
[`fn-own-feed-connect`](../books/owner.lisp), line 1161, which only uses
`fn-feed-with-conn`. That function preserves the queue, including an in-flight
entry. It does not call [`fn-feed-lost`](../books/peer-feed.lisp), line 719,
which is the function that requeues in-flight work and applies backoff.

The next `feed_poll` only redials when there is queued work. If there is solely
an in-flight entry, it does nothing. Even if another queued article permits a
redial, `fn-feed-selection` requires the in-flight count to be zero. The
comment promising that a later observation requeues the article does not
describe this call path. Process restart is a separate recovery path, not
normal reconnect progress.

The same [probe](evidence/astra-followup-2026-09-20/probe.py) invokes the actual
Python close/poll methods with an explicitly simulated in-flight-only queue;
its event trace contains only unregister, socket close and connection reset.
The ACL2 part of the finding is established by the source call chain above,
not by pretending that the Python fixture executes the model. The existing
[feed handoff](lanes/HANDOFF-w11-twonode-feed.md) also acknowledges this defect.

**Completion condition:** make connection loss an explicit ACL2-owned event,
with the feed journal protocol preserving uncertainty and retry state across
restart. A real socket cut after article transmission must lead to re-offer
without restarting the sending service; duplicate suppression and the original
retention obligation must survive a crash during that retry transition.

### F3 — Medium: the peer path discards the listener's authentication policy

[Owner.accept_nntp_step](../tools/run_owner.py), line 635, selects `open_peer`
when the remote address matches a configured peer. Ordinary `fn-own-open`
passes the authentication configuration through. In contrast,
[`fn-own-open-peer`](../books/owner.lisp), line 667, has no authentication-config
argument, and [`fn-served-open-peer`](../books/served.lisp), line 890, explicitly
installs `fn-auth-open-config`: authentication not required, no credentials,
no STARTTLS availability.

The peer wrapper can still dispatch ordinary POST through the shared posting
machine. Thus enabling required authentication for readers is not a universal
listener guarantee: an address-classified peer takes the open policy, and a
POST can proceed subject to the ordinary injection configuration. Multiple
agents connecting from one host cannot obtain distinct authenticated posting
authority merely by sharing this source-address peer classification.

**Scope:** source-address trust is an explicit peering policy in
[specs/peering.md](../specs/peering.md), §1.1. This finding does not claim an
arbitrary remote address can impersonate a configured source, nor that all
transit must use reader AUTHINFO. It identifies a policy-composition gap:
transit privilege currently also selects an open reader authentication
configuration. The general unauthenticated-posting description in
[specs/nntp.md](../specs/nntp.md) needs this qualification.

**Completion condition:** explicitly distinguish transit authority from local
posting authority, then test both commands from a configured peer address with
reader authentication required. Preserve an intentional trusted-peer exemption
only if it is an explicit, visible policy. State the theorem over the connection
that the owner actually opens under that policy, not only over a supplied auth
session. This review source-traced the path; it did not run a fresh live
authentication session.

### F4 — Assurance blocker: byte-crash recovery is not yet composed with owner retention

The new byte-store scan work is useful. It also exposed a substantive model
problem: a newly reopened process can have no current-process success entries
while its retained ledger still names previously acknowledged records. Permitting
tail rollback solely because that success list is empty invalidates the older
owner-retention argument. This is a real counterexample, not proof-engine noise.

[`books/store-files.lisp`](../books/store-files.lisp), lines 704–752, explains
the resulting split. `fn-sf-crash-imagep` remains the stronger relation;
`fn-sf-recovery-crash-imagep` represents the broader recovery-window possibilities.
[`fn-own-reopen`](../books/owner.lisp), line 910, still gates on the former.
The byte relation also contains replay/scan obligations that have not been shown
preserved through the required concrete transitions.

The [K2 handoff](lanes/HANDOFF-w11-bytestore-k2.md), §§4–5, explicitly says the
byte-to-kernel theorem is not proved: scan clauses and K0 relation preservation
remain open. Its kernel results do not discharge those obligations. The handoff
also records that the trace generator cannot express the rollback choices.

**This is an acknowledged assurance gap, not a newly demonstrated loss of a
durably acknowledged article on a real filesystem.** Splitting predicates can
be a sound intermediate design. It does not establish the stronger crash
premise from the broader platform behavior. No whole-service survival claim
follows until that connection is made under stated filesystem assumptions.

**Completion condition:** carry or establish the information needed to distinguish
durable history from merely observed replay state; prove relation establishment
and preservation for the actual recovery sequence; map its allowed byte crash
images into the owner-retention theorem. Include the recovery-window rollback
counterexample as an executable, reachable regression. Give this work one owner
who can change the model, recovery adapter and tests together.

## What genuinely improved

The earlier assessment should not be repeated unchanged:

- Reader AUTHINFO and STARTTLS now reach the served path. Stored credentials use
  a verifier rather than a cleartext token. This does not by itself establish
  TLS security, password-hardening adequacy or the peer policy above.
- The owner feed exists, and the committed
  [two-node evidence](evidence/twonode-feed-w11-2026-09-20.md) records real
  transfers in both directions. This review did not independently rerun that lab.
- The main Python/native storage framing paths now obtain the integrity trailer
  from ACL2. This landed while the review was running; the earlier finding about
  those paths is closed by source inspection. The
  [one-owner handoff](lanes/HANDOFF-w11-one-owner.md) still names a remaining
  legacy `run_feed.py` copy and other ownership work. Its certification record
  is narrower than certification of the whole service.
- BP bundle and node definitions now exist, alongside more byte-store and
  checkpoint work. The [DTN handoff](lanes/HANDOFF-w10-dtn-3.md) still identifies
  durable bundle state, persistent creation-sequence allocation, scheduler and
  receipt integration as missing composition. BP codec/node presence is not yet
  an autonomous durable BP service.
- Session-depth checks and preserved certification manifests address actual
  sources of regressions and evidence loss. They are useful tools, not substitutes
  for exercising the assembled service.

## Is ACL2 being used effectively?

Yes, where it owns executable decisions and exposes counterexamples to the
intended invariants. The recovery counterexample is an especially valuable
result: it prevents a superficially plausible survival claim. Moving framing
semantics into the same executable definitions also reduces divergence.

Effectiveness drops when a proof is credited outside its subject or hypotheses,
or a local invariant is treated as completion of a running feature. The decisive
question is: **does the function the host actually calls preserve the promised
property under every state and failure the host can produce?** F2 and F4 explain
why a retry theorem and a retention theorem can both be useful while deployed
retry and crash assurance remain incomplete.

For fn, assurance is a chain from a user's promise through the actual protocol
path, durable decision, recovery and observable result. It combines mechanized
claims with explicit assumptions, fault experiments, interoperability tests and
operational evidence. A structural check, a passing example, a certified book
and a whole-service claim are different evidence categories.

## Evidence quality and the development loop

`make check` passes at the reviewed revision. It also explicitly skips dynamic
host loading when `FN_ACL2` is unset, reports that witness values were not
evaluated, and reports unresolved witness/subject checks. The focused Python
suite passes. Neither establishes a fresh integrated ACL2 certification or
current live NNTP behavior. Exact commands, output, source digests and limitations
are retained in the [review evidence](evidence/astra-followup-2026-09-20/evidence.json).

The evidence-manifest repair is positive, but historic LOST entries and
non-retained run logs remain an auditability limitation. Missing records do not
mean a proof never ran. Conversely, accepting a known backlog does not make it
resolved. Do not spend another cycle reconstructing every old failed probe:
supersede the deployment-critical claims with one frozen, reproducible evidence
set, retaining the logs and dependency/toolchain identity needed to inspect it.

The structural source of the apparent "gyre" is repeated partial completion:
one lane finds a real boundary defect, repairs its local part, and leaves the
cross-boundary obligation to another lane. More documentation can describe this
accurately without making the boundary work. F1 then weakens the feedback that
would force convergence. That diagnosis does not require speculating about the
author's intentions or capability.

## Recommended next batch

1. **Repair the verdicts.** Land F1's classification and gate-exit tests first,
   so subsequent failures cannot become successful release evidence.
2. **Close one running communications path.** Own posting, durable acceptance,
   feed, cut, reconnect, deduplication and restart together. Resolve F2 and the
   explicit authentication policy in F3; rerun the corrected real-node gate.
3. **Close the recovery argument.** Finish the concrete scan/relation/crash
   bridge in F4 and its matching fault experiment before adding behavior that
   depends on stronger retention claims. This can proceed independently of the
   first two steps, but must converge on the same frozen integration revision.
4. **Publish one scoped local evidence bundle.** Build the actual selected
   service image, certify its relevant closure and run its acceptance scenarios
   at that revision. Record unsupported BP/agent features separately. Review
   that coherent batch once and fix concrete failures; do not create another
   procession of review-only lanes.

For agent deployment, distinguish retained article, runner intake and completed
external action. NNTP acceptance can promise the first; it cannot promise the
other two. Agent identity and permissions must survive shared hosts and reconnects.
A runner still needs durable inbox/outbox state, idempotent attempts or explicit
uncertainty for external effects, and authority checks on received requests.
Received article text is not itself execution authority. These are separate
application obligations, not consequences of a storage theorem or BP delivery.

No runtime files or assurance registries were changed by this review. No new
ACL2 certification, live-node deployment, publication or messaging was performed.
