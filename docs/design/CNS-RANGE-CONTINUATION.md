# Bounded XFNC read selection

The current XFNC `register :history` / `read` consumer now preserves its
actual address READ cursor when bounded selection returns `:more`. The
new `:yield` answer keeps the CNS page runnable with its input position
unchanged. Page capacity still returns `:more` to the client. This is a
source implementation milestone; ACL2 admission and execution are pending.

The claim uses the existing READ and RANGE query-owner tuple, bound to the
live CNS global ID/generation and its recomputed dedicated read-row mapping.
Resume checks both owner carriers and the fixed numeric address query. It
does not reopen the range or rewrite its keys. Invalid context cannot clear
an existing continuation. Terminal selection releases the owned range before
article lookup. Page refusal/cancellation releases it through checked cleanup.
No machine field, wire layout, authorization decision or host decision changes.

The existing FETCH descriptor copy and root retention still precede article
READ release. Source-job cleanup and CTL handback are unchanged. This change
does not add a durable history cursor, an archive-prefix reader, evidence
import or a complete catchup guarantee. Historical content may legitimately
produce GAP, as specified in e-surface section 3; normal sealer reachability
of the tall-tree fixture remains open.

## Executable gate and witness scope

`tests/cns-tall-runs-unit` builds 24 pages through the actual page writer,
seal, format check, cache installation and run installation APIs. It checks
the supported profile, WFP, current owned page handles and actual READ
continuation beyond 64 calls, followed by terminal release. This is accepted
READ API-domain evidence, not a normal sealer or authenticated client trace.

`tests/cns-range-continuation-unit` consumes the same support and real CNS
operations. It checks retained continuation, terminal/end cleanup, cancellation
and refusal after a real yield, partial-start rollback, u60 boundaries, and
full-state preservation for foreign/stale claims and mismatched query input.
CNS request metadata is explicitly constructed around a real admitted row.
No `:more` return or reader phase is fabricated to create the long traversal.

The next shared application gate must admit the changed `books/cns` consumer
and execute both named unit roots. `tests/cns-draining-teeth-unit` separately
checks the complete nine-witness counted release row. No independent broad
build has been launched; existing application qualification owns the compute.

## Integration overlap

Base: runtime candidate `0b41d24ac`, including its newer INPUT receive-cap fix.
Production edits are confined to `books/cns.lisp`: range-release cost metadata,
page selection answers, fixed-size ownership/continuation helpers, checked
page cleanup, and the initial address-selection portion of `item-next`.
The downstream FETCH capture/root-promise/article-release block is preserved;
source-core, source-kind, capture, retention, CTL and authorization files are
unchanged. The three new tall-range files and Makefile additions are isolated.

## Separate ARTICLE/work follow-up

The `63bc1792e` source donor remains frozen. Its follow-up splits address
selection, published ARTICLE lookup and item emission into separate CNS
turns. ARTICLE retains the original XL published-only visibility; it does
not substitute the broader ACTIVE/FROZEN range view. The ownership claim
uses the composed dedicated READ/XL partition and the live CNS generation,
phase and fixed article key. Arbitrary raw XL mutation is outside that claim.

Both READ-NEXT and READ-LOOKUP receive an inner work budget of one. The
schema-specific proposed charges derive from actual layout maxima, decoder
fuel, overlay probes and source geometry. ADDR selection bounds at 16,568
pool reads; ARTICLE lookup plus its atomic capture tail bounds at 14,393
pool byte operations. These are separate phases, not a claimed combined
trace. The existing CNS budget remains 32,768 bytes plus 32 steps.

`books/cns-read-work-bounds.lisp` checks the arithmetic, including a malformed
last decode. It does not prove an actual operation count. A counting/refinement
connection to the served decoder and read calls remains owed. Descriptor
issue and subsequent output processing also remain separate from the lookup
charge. The shared arm charge/goto repair must preserve preceding call costs
in actual returned scheduler charges; declaration metadata alone is insufficient.

Future focused consumers are `tests/cns-article-slice-unit` for retained lookup
and phase transitions, and the existing `tests/cns-stream-fetch-unit` for
actual APPEND/FETCH composition. New controls remain unexecuted until admitted
in the coordinated current application world. No network, deployment or
authorization activation follows from these source changes.

`tests/cns-fetch-cancel-unit` additionally pauses the real APPEND/FETCH executor
at post-capture ITEM, fails its first actual Send, withholds BorrowReleased
while checking root retention, then delivers handback and checks cleanup.
It does not fabricate a source job or claim that transport cancellation can
arrive at an idle ITEM boundary. This assertion is also unexecuted.

Changed-path review found no further composed ownership defect after checking
the dedicated READ/XL partition, generation, fixed key, retry and cancellation
paths. The actual phase registry now includes ARTICLE and ITEM; structural
controls compare it with kind/body arms and holds, including removal mutants.
All phase consumers reviewed in the draining/lifetime models use generated
state constants. Source review and these structural checks do not substitute
for actual generated-world admission.
