# Where these lessons came from

This retrospective was assembled on September 22, 2026, against source
`097c32747e1a`, using repository records and local `cv` transcripts. It adds no
certification or runtime evidence. The episodes below distinguish recorded
observations from our recommendations. Historical timings describe particular
runs, not predicted speedups for another proof or machine.

## A night spent finding the next failure

The [proof-engineering review](../planning/review-2026-09-22-proof-engineering.md)
documents an overnight closure repair that did not produce an image. Ordinary
runs stopped at low dependencies, while long timeouts set the iteration time.
In session A, messages 718–729 and 881–885, the user challenged the lack of a
usable result and asked for interactive proof development.

The resulting tools exist: [proof_repl.py](../tools/proof_repl.py) provides
bounded per-form attempts, and [triage.py](../tools/triage.py) exposes independent
failures through provisional certification. The
[triage comparison](../planning/evidence/triage-2026-09-22.md) measured a
63-book closure: an ordinary round took 690.8 seconds and exposed one
independent failure; a provisional round took 317.3 seconds and exposed four.
That is evidence about discovery on that closure, not certification of it.
The review's original substitution proposal should not be confused with the
later tool's provisional-certification implementation.

## The codec was entering proofs that did not need it

Review F3 records a replay theorem timing out after 600 seconds, then proving
in 0.32 seconds with inappropriate recognizer expansion closed. The
[subsequent freeze record](../planning/evidence/native-freeze-dabebb84-2026-09-22.md)
explains the checkpoint repair: local encoder-shape facts allowed the
round-trip proofs to run with the general encoder and frame dispatcher closed.

These are concrete repairs, not evidence that all codec boundaries are clean.
The wider T1 seam and strict lint adoption are separate work in the trajectory
plan. Our recommendation is to expose small shape contracts before increasing
proof-search budgets.

## Changed machines made old statements false

The [earlier freeze record](../planning/evidence/native-freeze-01fbdad4-2026-09-22.md)
describes five exported statements invalidated by behavior changes beneath
uncertified invariant books. Repairing their scope left an accepted-statement
index obligation explicitly open under PRF-023. This is why the guide starts
with checking truth and new transition arms, before tuning hints.

Session A message 1129 also records a guard claim contradicted by
`:verify-guards nil` declarations. Admission, theorem proof, guards, and
runtime correspondence must remain separate claims.

## Ownership failed before the agents did

Session B messages 4787–4798 record duplicated assignments and stale briefs.
The coordinator reported that combining two agents' edits to one function
had made a test book's intended assertions inert. Several agents independently
noticed duplicate or already-completed work and withdrew it.

This supports a coordination lesson, not a ranking of model capability:
refresh dispatch against the current tree, coordinate overlapping edits,
and check the coherent combined proof. The initial response was exclusive
book ownership; the user's September 23 correction replaces that restriction
with direct peer coordination and visible intentions.

## A corrective gate became another bottleneck

Session A messages 1289–1293 record the coordinator acknowledging that repeated
whole-closure checks had held an independently certified operator change for
hours. Message 1354 sets the user's preferred five-lane arrangement and
convergence every two or three batches. Those decisions are now in
[how we work](../planning/how-we-work.md) and the
[trajectory plan](../planning/plan-2026-09-22-trajectory.md).

The lesson is to preserve lane evidence and detect new batch regressions
without demanding that unrelated inherited failures disappear before any
merge. This does not relax the requirement for a frozen, qualified image.

## A running node changed what we knew

The [agent exercise](../planning/evidence/agents-on-hbox-2026-09-22.md) records
posts, threaded replies, resumed reads, independent-client byte agreement,
and client fixes against image `dabebb84`. The
[INN exercise](../planning/evidence/inn-lab-dabebb84-2026-09-22.md) found
article projection violations. The
[crash campaign](../planning/evidence/campaign-dabebb84-2026-09-22.md) showed
that its process-death selectors reached the lower store command rather than
the served posting path, alongside additional outcome and fault-control defects.

Together these records support useful but narrower claims than “the server is
verified.” They also make the next work specific: repair the invoked path and
its argument, then repeat the relevant experiment on the new image. The
[node record](../planning/evidence/node-hbox-dabebb84-2026-09-22.md) remains
the authority for what that deployed image demonstrated.

## Process completion was mistaken for proof completion

The [67d combined run](../planning/evidence/wide-combined-67d026ad-red-2026-09-24.md)
initially received a count of 273 successful books from activity files. Its
terminal manifest instead records 263 passed and eleven failed books, including
four actual theorem failures and seven missing-certificate dependents. ACL2 can
exit zero after a failed theorem. The correction changed `farm.py status` to
label unfinished-process observations separately from terminal manifest book
verdicts. Activity records are not PID-liveness checks either.

That same batch separated two kinds of proof failure. The stamp and Store
prepare hints exposed record internals before the exported selector laws could
match; keeping those internals closed proved the unchanged statements. The BP
and byte reopen claims instead lacked the topic replay condition enforced by
the newer Store opener. Their conditional corrections leave a maintained
topic-history/crash correspondence to establish. A common failing batch does
not imply a common remedy, and a repaired conditional theorem does not close
that composition obligation.

## Finding the local transcripts

The guide paraphrases the sessions; it does not publish their contents. These
references are for a maintainer with the local `cv` history. They are not
required to read the guide; repository records above provide the public trail.
The example commands use `cv`'s zero-based, end-exclusive range convention.

- Session A: `claude:4adeee12-f8fa-4a4b-9022-ed44f2aa4077`.
- Session B: `claude:990cbaad-8018-4168-a716-1ffe2d847cfb`.

For example:

```sh
cv show claude:4adeee12-f8fa-4a4b-9022-ed44f2aa4077 --range 1289..1294
cv show claude:990cbaad-8018-4168-a716-1ffe2d847cfb --range 4787..4799
```
