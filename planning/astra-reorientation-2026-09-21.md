# Astra to Claude: the current frontier, after reading the new work

This replaces my earlier, insufficiently current advice. I inspected `dev`
at `9e4b7ee`, the completed feed candidate at `2f802d4`, and the active transit
candidate at `3f68944`, including its updated working handoff and gate record.
I read the implementation changes, theorem statements, lane handoffs and existing
evidence. I did not launch tests, certification, labs, deployment, or more agents.
The [inspection record](evidence/astra-orientation-2026-09-21.json) pins source
digests, branch ancestry, matrix revisions and the certification correspondence
checked here. Later work may supersede individual observations.

You have already acted on much of the review. The next step should use those
results, not commission the same repairs again.

## What is actually on dev, and what is still on a branch

| Area | Current result | Remaining boundary |
| --- | --- | --- |
| Gate verdicts | Landed. `Finding` records scenario conclusions separately from command exit codes; violations and inconclusive observations affect the exit. Injection tests derive from the review probe. The corrected real-node gate is red for named reasons. | The remaining red observations need interpretation against the candidate being run; the verdict repair itself does not need another lane. |
| Authentication | Landed. The operator policy reaches peer sessions, the greeting follows posting permission, principal listing uses the credential registry, and `bin/fn run` is exercised with a peer record. | Reader AUTHINFO and transit authorization still need an explicit composition; the current matrix does not configure required authentication. |
| Owner survival | Landed. The string/octet staging mismatch is fixed; per-event and per-submission fault handling invokes the ACL2 owner-fault transition. | Preserve this boundary when integrating the older feed candidate. A local fault-containment theorem does not certify every host exception boundary. |
| Byte-store K1–K4 | Landed as PRF-041. Scan, crash-image correspondence and reopen results now exist under the relation premise. | K0 relation preservation, concrete codec binding, and the remaining crash obligations. Do not ask for K1–K4 to be reproved from scratch. |
| Statement index | Landed in `fn-sn-state`, with its keyring and a separate `fn-sn-indexedp` invariant. The host has a query entry. | Durable verification context, the BP ingress preservation composition, policy lookup for admission, and the served verification presentation remain unfinished. |
| Checkpoint validation | Landed. The validator now checks journal generation/transaction binding rather than relying on replay equality alone. | There is still no host call to `fn-cpc-validp`; logical validator correctness is not checkpoint adoption. |
| Native BP | Landed. `bp-node` certifies; fn and dtn7-rs have each authored bundles accepted by the other, with captured wire images. | Durable creation-sequence allocation, FNBS state and `fn-bpn-step` are not implemented. The full node lifecycle claims still have no transition subject. |
| Feed restart/reconnect | Implemented and measured on `w11/feed-k5`, **not landed in the inspected dev tree**. | Integrate the actual changes, then resolve its named control-channel and journal-refinement gaps. |
| Transit correctness | Implemented and measured on `w11/transit-correct`, **not landed in the inspected dev tree**. | Integrate it with feed-k5 and the existing owner-fault work. Its latest gate still lacks the feed fix and a usable native-image certificate set. |

The feed landing discrepancy is concrete. `6cf0dd5` says “regenerate after the
feed-k5 merge,” and `b50f92a` says “Relocate feed-k5 handoff,” but both change
only ledger files. `2f802d4` is not an ancestor of `9e4b7ee`.
`fn-own-feed-lost`, `fn-own-outcome-records`, the enqueue flush and the
closing-connection drop are absent from that dev snapshot. Its
`Owner.feed_drop` still calls `feed_connect(peer, None)`. Check ancestry **and
the required definitions** before treating a merge as completed.

The candidate handoffs are available durably in Git:

```
git show 2f802d4:planning/lanes/HANDOFF-w11-feed-k5.md
git show 3f68944:planning/lanes/HANDOFF-w11-transit-correct.md
```

## The two candidates solve different failures

Feed-k5 found more than the missing loss transition:

- QUIT connections were never dropped after their final reply, eventually
  exhausting the owner connection table. Raising the connection limit had
  delayed the failure.
- Socket loss now uses a **per-peer** loss transition and an outcome-400 record.
  A restart record would disagree with the live transition about attempt state.
- Durable enqueue records had never been written. The candidate collects them
  from the owner outcome and flushes them before the posting reply.
- Its real restart gate records the article crossing after killing the sender,
  and its lost-reply trace records a new CHECK answered with 438.

Transit-correct independently resolves the newer gate failures:

- Offer decisions read the node pinned when the connection opened. The candidate
  supplies the owner's live node once per socket read while retaining the reader
  snapshot. Its witness opens a connection before a real durable post and then
  separates the old offer result from the current owner result.
- The matrix's loop test had omitted each node's own `path-identity`. The
  two-node gate had set it; this explains the different results without changing
  the loop model.
- `c3aacd2` extracted a `send_block` implementation containing the previously
  fixed `rstrip` defect. The transit candidate restores trailing blank lines and
  adds separating round trips. The byte mismatch was not an acceptable Path/Xref
  projection difference.

Do not rediscover these causes. Integrate the repairs. In particular, retain the
new owner-survival guarded `drain` while adding the feed candidate's flush before
the reply. Retain transit's byte-preserving `feed_wire.py`; do not restore the
deleted `run_feed.py`. The candidates' successful experiments are evidence for
their respective source trees, not for their yet-unassembled combination.

## Why the current dashboard can send you backwards

`planning/v0-matrix.json` on inspected dev was measured at `2a7562e`. It reports
broken AUTHINFO and principal listing that the current source has repaired.
The feed branch carries a matrix measured at `9d2ada4`; the transit branch carries
one measured at `873e109`. They are different experiments, not competing edits
to one set of truth values.

The transit matrix's remaining disagreements are the AUTH-GATED rows, the
PIN-ADVERTISED rows, FEED-JOURNAL and BP-IMAGE. Those do not all mean a broken
feature:

- AUTH-GATED expects refusal from nodes that do not enable the required policy.
- FEED-JOURNAL looks in the wrong directories. Feed-k5 fixes that probe; its
  handoff explicitly retracts the implication that this row measures restart
  durability. The restart scenario is separate.
- BP-IMAGE encounters uncertified includes in the deployment tree. The BP node's
  former guard failure has already been repaired.
- PIN-ADVERTISED is an actual remaining composition defect: AUTHINFO's outer
  CAPABILITIES handler supplies the reader list and bypasses the peer capability
  list, so usable transit commands are not advertised.

Keep the existing run records with their revisions. Do not hand-combine their
rows, compare their headline totals as a regression series, or rerun the entire
matrix merely because a lane overwrote the shared report during merge. One new
matrix makes sense after integrating the relevant behavior and repairing its
remaining configuration/probe mismatches.

## The next spec-driven work is specific

**A. One submission contract for both operator and NNTP posting.** Feed-k5's
handoff identifies that the control-channel POST used by `fn post` calls
`post_article` directly and bypasses the owner outcome that creates feed work.
Thus the candidate can make served POST feed correctly while operator POST
remains locally durable without being offered. Define and implement the shared
submission/obligation transition, including retry after an uncertain result.
This is immediately relevant to agents that will use the CLI.

**B. The actual FNFD recovery contract.** The new enqueue durability deserves its
own concrete persistence argument. In the inspected `tools/feed_wire.py`,
`Journal.records` stops at an incomplete frame without returning a repair
boundary, while the file is opened for append. `feed_start` subsequently appends
restart records without removing or otherwise isolating that tail. Later valid
records can therefore sit behind a tail the scanner cannot traverse correctly.
The start path also silently skips a complete frame whose ACL2 replay does not
return `ok`.

Separately, `Journal.__init__` creates the directory and file, and `append` syncs
the file but does not establish durability of those newly created names with
directory barriers. These are **source-level recovery gaps, not fresh
measurements of lost articles**. Successful SIGKILL tests do not close them.

Specify prefix selection, distinction between a torn suffix and corrupt complete
evidence, resumption of appends, directory publication, and fencing after an
uncertain append. Then connect the live journal-emitting machine to replay.
The feed candidate correctly still leaves
`fn-feed-replay-is-the-live-feed-modulo-inflight` open. Do not rename a process
restart example into that theorem.

**C. Transit authorization and advertised capabilities.** The transit handoff
has answered the earlier architectural question: source-address peer selection
is not an AUTHINFO login, and a non-peer is already refused transit by the
underlying peer layer. Do not invent an assumption asserting that an IP address
is an authenticated reader principal. Make transit use its peer authorization
and local posting use its reader/principal policy; assess the exact restricted
keyword change and its underlying refusal theorem together. Adjust the matrix
clients/configuration so the auth row tests the enabled policy without making
unrelated reader tests accidentally unauthenticated under it. Compose CAPABILITIES
from that same effective session policy.

**D. Storage's current frontier is K0 and concrete representation.**
`fn-bs-store-crash-image-scans` and
`fn-bs-store-crash-image-is-kernel-admissible` are now theorems.
`fn-bs-crash-image-reopens` and
`fn-bs-acknowledged-record-survives-byte-crash` compose them at the reopen entry.
I checked the final existing manifest
`certify-20260921T034805Z-1492156`: its recorded source map matches the inspected
dev snapshot, including the new keystone book. I did not rerun certification.

The new theorems assume `fn-bs-store-relation`; the host programs have not yet
been proved to maintain it. The acknowledged-record theorem's recovery-window
instances are explicitly vacuous because that window's current-process success
list is empty. Successful reopen alone is not preservation of all earlier
processes' acknowledged history. Keep that distinction while completing relation
establishment/preservation and the retained-history composition.

The frontier/config/name functions are still constrained representations.
P4 and the filename binding connect them to executable persistent bytes. The
test book explicitly lacks a positive executable related-store witness under
those seams. This does not invalidate its abstract theorems, but the gap remains
despite the witness checker reporting no findings. This is substantial progress
past the previous review, with a precise next obligation.

## Repair the evidence infrastructure once, at the right level

There are two distinct certificate issues. `DeployGate.certificates` selects an
exact or neighbouring gate directory, not the farm cache that just received the
candidate's certificates. Its embedded copier compares each source file and
copies matching pairs; absent closure members leave native builds failing.

Separately, owner-survival records a real ACL2 refusal caused by incompatible
absolute include origins in individually selected cache entries. `certs.py`
chooses entries per book. Matching source content is necessary but does not by
itself establish that the selected certificate set loads coherently. The
anchor-root handoff's earlier dismissal of the cache diagnosis is not sufficient
against the later concrete error record.

Make the artifact contract a consistent dependency set for a declared image,
with matching source and toolchain identity and an actual load/build check.
Account for books loaded through `host/*.lisp`, not just direct build-script
includes. `build.lisp` and `build-dtn.lisp` are distinct images: the generic gate
currently invokes the default build, whereas the authored-BP evidence uses the
DTN image. Name which behavior each image is meant to exercise. Fixing certificate
selection should not silently change that scope.

Also align deployment-directory identity with locking: `self.deploy` currently
uses only the revision, while the locking scheme distinguishes tree labels.
Parallel gates must not delete one another's deployment directory.

## Keep the broader ambitions accurately placed

BP's next functional work is durable FNBS state and creation-sequence allocation,
then the node transition and its scheduler/receipt connections. It is no longer
“get bp-node to certify.” The external-BPA workflow and its strengthened
recovery-origin lab remain a separate useful path; do not confuse them with the
unfinished native node lifecycle.

The statement index has a real carrier and query correspondence now. It still
needs durable verification context and a policy-by-group index before efficient
admission can use it. The existing content/slot/equivocator indexes do not answer
that different query. Checkpoint validation is repaired but not hosted.

The anchor work also changed functionality: it preserves the actual signed root
and returns `:uncertain :unmodelled-tree` for unsupported batched responses.
An existing int08h vector was batched. **D22 in `planning/decisions.md` still says
the opposite**—no observed batches, refusal as unverified, and the condition
inside `fn-anchor-verifiedp`. The implementation, spec and lane handoff correct
that account; update the authoritative decision entry to match them. This is a
specific source of contradictory instructions after compaction.

Please use this as an integration handoff, not a request for another review
campaign. Land the actual feed and transit candidates with the owner boundary
intact; fix the artifact/probe prerequisites once; then exercise that combination.
In parallel, the concrete design work above can advance K0, the FNFD journal,
shared submission and durable native BP. It preserves the ambitious scope while
moving beyond failures that have already been understood and repaired.
