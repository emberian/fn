# Bounded schema-3 checkpoint writer

Selected implementation contract, not a completed implementation or proof.
This completes the outer Store checkpoint alongside the canonical history
image. It preserves the exact existing bytes, including payload references;
literal-only output or decode-equivalent output is not the target.

The source specifications are `fn-sct-program`, `fn-sct-table-programs`
and `fn-sct-file-octets` in `books/store-checkpoint-tables.lisp`. The current
`fn-ockp-setup`, estimates, whole-table recognizers and row batching hide
whole-tree work. They cannot be called as the new bounded preparation path.
The complete file order remains history image, arena run A, F, P, E, R.

## Ownership and implementation boundaries

`architecture_reorientation` owns the outer Store capture, summary,
publication and host assembly. `coordination_lessons` owns the canonical
history image writer and tagged byte/census adapter;
`history_record_cursor` owns the cold nine-cell runtime and its refinement.
The new outer codec must not duplicate those implementations or introduce
an include cycle through their existing caller books.

The Sol extracted-product owner is the proposed implementation successor
after completing the actual recursive stobj-table differential and source
packet. Until that transfer is confirmed, the new helper files have no
active implementation owner. Suggested exclusive new files are:

- `books/checkpoint-reference-cursor.lisp`: bounded equality and ordered
  candidate search, with corresponding tests.
- `books/checkpoint-table-cursor.lisp`: reference-aware row emission and
  exact residual, with corresponding tests.
- `books/checkpoint-table-controller.lisp`: lazy row offers, census,
  framing and acknowledgement, with corresponding tests.
- `books/checkpoint-table-refinement.lisp`: composition to the existing
  table-program and file specifications.

These are components of the complete writer, not replacement completion
criteria. Actual owner and offline checkpoint callers must ultimately use
the bounded implementation with matching evidence.

## Exact row machine

Use a separate `fn-sctc` cursor. Reuse existing scalar and byte primitives
and the tree-task pattern; do not pass an unchecked whole subtree to the
literal-only generic encoder. Every pending tree task retains its candidate.
Follow the precise `fn-sct-program` decision order:

1. Compare this node with the inherited candidate's reference value.
2. If equal, emit opcode 8 and the existing NAT encoding of the candidate.
3. Otherwise classify the node as a nonempty octet list and, if so, emit
   the ordinary literal-octet encoding.
4. Otherwise, for a cons, find the exact enclosing candidate, override the
   inherited candidate only for a non-NIL result, then emit car, cdr, CONS.
5. Atoms use the existing scalar cursor.

Sequence zero is a valid candidate. The known-nonoctets optimization needs
a theorem that such a node cannot equal the nonempty-octet reference
target; candidate discovery and propagation still need their exact rules.

Proposed entry shape is `fn-sctc-begin` followed by `fn-sctc-tick`, with
continue, emit, need-source, prepared and named refusal results. Final
signatures must be agreed with the actual source/provider owners before
call-site edits. Every external observation is bound to the frozen capture,
lease, pending request and source position.

## Suspended comparison and candidate lookup

`fn-scteq` compares a bounded cell/byte portion per tick. A proved identical
source can be a fast positive path; unequal handles are not unequal bytes.
Length rejection needs maintained length correspondence. A digest does not
replace equality. Retain two independent source continuations and, for
different cold sources, independently retained read buffers. An alternative
cache design must account for its actual revisits; it cannot assume
page-linear I/O while alternating a single buffer between two pages.

`fn-sctcand` reproduces `fn-sct-candidate-among`'s first-match order,
including failed comparisons. `fn-cei-trie-records` hides a complete
variable-string lookup and whole-candidate-list `true-listp`: use a bounded
character/branch continuation and a maintained proper-list invariant, or a
bounded validation phase. Borrow the candidate suffix without constructing
another list. A hashed route is only an optimization after exact key and
candidate-order correspondence is proved.

The comparison target is exactly `fn-sct-ref-get`. In a composite event,
P contains its outer carried article-record bytes; an R root can contain
the decoded inner payload. Arena remapping does not make those values
interchangeable.

## Lazy runs, census and framing

The controller offers one row at a time:

| Run | Source | Initial candidate and lookup |
| --- | --- | --- |
| F | One six-field `fn-sct-f-row` | NIL; no lookup |
| P | `fn-sct-payload-of` of each captured event | NIL; no lookup |
| E | Captured events in ordinal order | Current ordinal; captured event table |
| R | CPR, original identity context, consumer, topic | NIL; captured Message-ID trie and event table |

P is a lazy projection, never a materialized payload list. R is four borrowed
roots, never four one-shot encoding calls. F's count and NEXT come from
maintained summaries with their existing fold correspondence, not a setup
`len(records)` or `fn-sct-next-lower` scan. Ordinals and final row counts
are checked at the corresponding transitions.

Run the same reference-aware machine with a count/discard sink and then
an emission sink over the same immutable capture. All comparisons, lookup,
classification and scalar work participate in scheduling; discarded output
does not make census free. The four emitted lengths determine counts via
`fn-sccb-chunk-count` and costs via `fn-ockp-run-len`. No independent fast
estimator or whole-table encodability check substitutes for this census.

Each F/P/E/R run resets its segment index and trailer to zero/genesis.
An empty run emits one empty frame. A nonempty exact multiple of segment
size emits no additional empty frame. Headers and seals must match
`fn-scc-header` and `fn-scc-seal` exactly. The ACL2-selected segment size
and runtime allowance must cover framing/copy/hash work; otherwise those
operations also need continuations. A pending frame acknowledgement freezes
the output buffer and child consumption, and names the exact issued token.

## Funding and lifetime

Census already owns scratch, continuations and source pins. Reserve capacity
before growth; use bounded spill if the selected representation requires it.
The existing ten-field HPI growth grant funds the leading image and its
spools only. The same maintenance authority must fund A and the exact
outer runs before their allocation/write, including headers and trailers,
retained old artifacts, source buffers, private targets and cleanup.
A separate typed outer growth adapter can preserve the HPI interface.
Do not subtract image space twice through `fn-his-stream-free` plumbing.

The emission pass uses the same captured roots and its own source-pass
token. Quantum exhaustion yields without losing work; unavailable resources
defer by name. Cancellation joins outstanding work, clears cursor/buffer
aliases, releases private storage in bounded steps, then settles the exact
pins and leases. Ambiguous publication remains uncertain/recovery-required.
This codec does not itself publish SNAPSHOT.

## Evidence required

The row keystone relates emitted prefix plus logical residual to the exact
`fn-sct-program`. Comparison completion must equal logical equality;
candidate completion must equal the exact ordered logical search. Resident
and decoded sources require named independent representation relations.
Census must equal program length, lazy row offers must denote
`fn-sct-tables-of-capture`, and complete output plans must equal
`fn-sct-file-octets`, not merely decode to the same state.

Executable ticks must be guard-verified with bounded allocation/work and
preserved funding. Logical residuals, source alpha and whole-tree predicates
must not execute in runtime guards or define themselves through this writer.
Literal positive/removal witnesses cover references, candidate zero,
equal bytes from different sources, failed candidates before a winner,
composite payload distinctions, empty/exact-multiple runs, stale observations,
acknowledgement and cancellation. Final claims name the actual host-called
entries, matching manifests and composed native crash/restart evidence.
