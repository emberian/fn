# Agents doing ACL2 together

fn has been a useful experiment in two things at once: building a news server
around an executable logic, and letting agents share the work of proving it.
The hard part has often been the loop around ACL2. A swarm can produce more
changes than its coordinator can integrate, or spend a night repeatedly
discovering one failure behind another without producing a usable image.

This guide explains what helped, with [case notes](case-notes.md) from the
development history. It is not a second development policy. Start a lane from
[AGENTS.md](../AGENTS.md), [how we work](../planning/how-we-work.md), and the
current step in [the trajectory plan](../planning/plan-2026-09-22-trajectory.md).
Those documents own the schedule, merge rules, resource limits, and definition
of done. The examples here were checked against the September 22 tree.

## Divide the work at a stable boundary

A feature name is not an ownership boundary. Posting, peering, statements, and
recovery can all change the same state constructor or completion function.
Assigning one agent to each feature without noticing that overlap produces
competing fixes and invalidates proofs other agents are trying to repair.

Before dispatch, inspect current definitions and tell agents who is working
nearby. The September 23 user correction matters: shared files are not a
reason to forbid useful collaboration. Agents should exchange interfaces,
lemmas, patches and evidence directly, and agree how to assemble a particular
change. Work claims are visible intentions, not exclusive file reservations.

An agent discovering that its assignment was already fixed should share that
finding and move to useful work. If two changes overlap, reconcile the whole
implementation and its proof/test closure. Splicing one agent's statement into
another's hints without checking the resulting book can leave intended
assertions unexercised; the defect is unexamined composition, not overlap itself.

The current plan starts around ten useful agents. Machine slots and proof
jobs remain separately bounded. The [coordination loop](../planning/how-we-work.md)
and [swarm board](../planning/swarm-board.md) describe peer messaging, durable
handoffs and sharing expensive runs. Measure additional progress and iteration
latency, rather than treating occupied agent slots as throughput.

## Brief the property, not just the file

A useful brief names the user-visible behavior and the exact function the host
calls. A theorem about an elegant sibling function is not evidence for that
behavior unless a correspondence theorem connects them.

Use a short brief with concrete contents:

```text
Step and contract: current plan step; requirement/proof IDs; relevant spec.
Base and collaborators: revision; expected edits; peers sharing the interface.
Called subject: host call site; function signature; proposed theorem statement.
Assurance: reachable positive witness; negative cases; guards; affected arms.
Integration: dependent books/tests; actual image scenario; known inherited reds.
Execution: assigned box; absolute worktree/run paths; toolchain; resource budget.
Handoff: source digest; ordinary certification manifest; evidence file;
         what remains unproved or unexercised.
```

Refresh this against the tree immediately before dispatch. An old branch or
compaction summary is a source of candidate work, not authority about what the
project currently needs. Put contracts and decisions in repository documents
so that a resumed agent can recover them without recreating the conversation.

## Find out whether the statement is true

When a previously useful proof stops working, first inspect the changed
machine. Did a constructor gain a field? Did a completion function gain an arm?
Does recovery now return a fault? Work a small concrete example through the
called function before searching for stronger hints.

In fn, several exported theorem statements had become false after behavior
changed beneath invariant books that were not recertified. More prover time
could not repair them. A theorem narrowed to the arms it actually covers can
be useful, but the omitted arm remains an assurance obligation. Record that
scope with the requirement; do not turn the narrower theorem into a claim
about the whole machine.

For a keystone, construct a reachable, non-degenerate witness and the negative
cases required by AGENTS.md. Check that removing each hypothesis really can
break the conclusion. If it cannot, investigate a redundant hypothesis, a
vacuous statement, or an unreachable case. A helper that merely unfolds a
definition should be named and used as a helper, not counted as the security
or durability result.

## Make proof search small and interactive

A caller that dispatches on a record kind should not need to unfold a complete
bounded CBOR decoder. Opening codec vocabularies at book scope couples small
proofs to the whole representation. When the codec grows, unrelated proofs
can start exploring enormous terms.

Instead, prove the shape fact at the representation boundary. The checkpoint
repair, for example, stated how encoding a bounded unsigned integer relates
to the argument encoder, then used that fact with the general encoder closed.
Open a decoder or recognizer only in the local hint that needs it. Inspect
rewrite direction as well: a useful shape lemma left enabled can rewrite a
term before a round-trip lemma gets the chance to match it.

Use [proof_repl.py](../tools/proof_repl.py) to load certified dependencies and
the book up to the failing event. Try one complete form at a time with the
prover time limit, read the checkpoint, and retain the successful event in the
source book. The ordinary book certification comes afterward. A form admitted
in an interactive world is not a certificate for the edited book.

This is also a coordination improvement. A lane should return a specific
obstruction—an exposed recognizer, a missing induction fact, a counterexample,
or an unresolved dependency—instead of silently spending repeated full-farm
runs on the same timeout.

## Separate discovery from certification

Ordinary certification respects the dependency graph. A failure low in that
graph can hide independent failures above it. Using a full certification run
for every proof edit makes discovery serial even with many machines available.

[triage.py](../tools/triage.py) uses provisional certification to expose those
failures in parallel. Read the actual report: independent errors, timeouts,
proved-but-blocked books, and Create failures are different findings. Some
failures can still hide others, and a substitution used for discovery changes
the assumptions. The tool's result is a diagnostic report, never a completion
claim; its artifacts do not enter the certificate cache.

Once repaired, certify the owned books, tests, and affected closure normally.
Use [green_check.py](../tools/green_check.py) at the current source bytes and
preserve the manifest, include closure, origin, toolchain, and limitations.
The existence of a `.cert` file, a process exit code, or an old successful run
does not establish that the current books certified.

Keep separate the questions that are often compressed into “proved”: was the
definition admitted, was the property proved with the stated hypotheses, were
execution guards verified, and does the host call this subject? An affirmative
answer to one does not answer the others.

## Converge batches without creating a review queue

The lane carries its behavior and invariant evidence together. Root then
checks a coherent batch and follows the convergence cadence in
[how we work](../planning/how-we-work.md), comparing failures and their forms
against the previous wave. A new regression belongs to the batch. An inherited
failure unrelated to that change must not become an indefinite hold on every
other lane.

There were two opposite mistakes in fn: landing behavior while its invariant
books were stale, then compensating with an expensive whole-tree gate on
every merge. The repair is attribution and batching, not choosing one mistake
over the other. Keep independent work moving while the shared closure is
repaired; build the image from a frozen tree when the batch is ready.

Use independent review for a precise question: does this host path reach the
proved transition, does this crash cut occur on that path, does this verdict
actually fail when delivery fails? Give the reviewer source, evidence, and a
bounded scope. Different model families can be helpful, but the value comes
from independently checking the claim. The record does not isolate model
choice as the cause of success or failure.

## Finish at the service boundary

One shared executable core is central to fn's assurance approach. Tests and
host adapters must not quietly acquire a second implementation of identity,
framing, bounds, or acceptance policy. Host code performs I/O and checks its
boundary; ACL2 owns the decisions. Python client and test tooling does not by
itself violate that boundary. Reimplementing the decision under test does.

Exercise an actual frozen image with an independent client or peer. Follow a
message through submission, the durable completion, reply, restart, and read.
Check uncertainty and refusal as carefully as acceptance. A fault selector
that kills a diagnostic store command but never reaches the served owner
tests that diagnostic path; it does not establish the served path's crash
behavior. A transport acknowledgement does not discharge an application
retention promise.

The hbox agent exercise was valuable both because letters moved and because
it found client defects. The image's broader qualification found faults that
component reports had missed. Keep those findings attached to the image; a
later source repair is not a retroactive passing result.

End a lane with enough information to resume without archaeology: what
changed, the exact subject and hypotheses, current evidence, the outstanding
obstruction, and the next concrete experiment. Preserve evidence before
removing a worktree, and account for owned local and remote processes when
stopping. The useful measure of progress is a behavior someone can exercise
and an argument whose limits they can inspect.
