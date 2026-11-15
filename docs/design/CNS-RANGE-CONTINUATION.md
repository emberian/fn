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
