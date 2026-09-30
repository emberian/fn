# Bounded stored DEFLATE windows (PRF-1112, SCN-1020)

The stored decoder and COMPRESS use the same resumable inflater, with
separate expansion policies. Network `fn-zin-feed` retains its existing
256 times consumed-input plus 65,536 prefix bound. Stored decoding uses
`256*C + 65,536`, where C is the declared compressed length, and requires
exactly the declared N decoded octets. C and N are untrusted descriptors:
core positional containment, supported-profile bounds and resource admission
must precede use, independently of later extent authentication.

This is an intentional change of stored acceptance policy, not an equality
between the old lookahead decoder and the network loop. The old decoder
accepted a 108-byte valid raw stream for 93,100 `A` octets that the network
loop refused at 92,672. The new policy preserves that valid success. It can
also accept valid high-ratio prefixes followed by ordinary data, and trailing
bytes contribute to declared C even if the final block ends earlier. This
broader stored domain remains subject to total output, work and integrity
bounds. No network expansion allowance changes.

A nonempty stored stream succeeds only at a final block or a complete sync
flush: `:stream-ended` in mode 13, or `:more` in mode 0 with no buffered bits
and a recorded empty non-final stored block. The marker is reset at each
new block and decoder reset; only a valid zero LEN/complement pair sets it.
A one-byte final stored header `01`, previously accepted at N=0, now refuses
as truncated. A nonempty stored block ending in bytes `00 00 ff ff` does not
impersonate a sync flush. Trailing bytes after a final block remain allowed.
The explicit empty representation C=0,N=0 remains valid.

`fn-pzw-initialize` receives a pinned shipped dictionary (the dictionary
registry permits at most 64 KiB), initializes the 65,536-byte ring/preset and
3,494-byte table, and reserves a 64-byte scratch output. Admission precedes
these fixed reserves. These are dedicated slots: reserve never shrinks a
legacy oversized vector. Scalar state is twenty boxed naturals; runtime
charges must include representations of profile-sized counters and temporary
stored credit, not assume a 20-byte state. Dictionary tails are shared until
copied into the fixed preset half. The initializer has fixed bounded buffer
work separate from a decode scheduling quantum.

`fn-pzw-stored-chunk` consumes a span of at most 64 input octets, runs at most
1,024 decoder actions and at most the caller's remaining action budget, and
returns at most 64 scratch output octets. The total is bounded by
`min(N, 256*C+65,536)+1` when starting at or below the bound. The extra octet is
a private overflow sentinel. A caller must run `fn-pzw-stored-decision` after
each call and stop on refusal rather than resume an overshot state. Quantum
exhaustion resumes; the existing total `fn-pzd-budget` remains separate.
No arbitrary payload-size ceiling or full payload allocation is introduced.

The stored allowance temporarily credits C inside the existing inflater;
`fn-pzw-stored-chunk-counts-real-input` proves that returned state restores
actual input consumption, and that output length equals the counter delta.
`fn-pzw-stored-chunk-is-resumable-run` relates every returned value and buffer
effect to the logical resumable run over precisely the given input span.
`fn-pzw-select` derives scratch source/count/private-window destination for
the requested decoded interval, bounded by 64 and 16,384 respectively.

`:decoded` is private codec completion. It grants no publication permission.
The extent controller must still scan and authenticate the complete protected
prefix, including compressed trailing bytes, compare its trailer, and match
the issued token, incarnation and lease. Physical ownership retains all
buffers until actual worker settlement and output transfer/release.

Current source includes the canonical whole decoder and pooled decoder
conversion plus the bounded component. The existing whole-payload host
realizer still allocates whole input/output and is not the completed streaming
path. Full window-selection/copy composition, authenticated publication,
physical funding, matching images/natives and performance measurements remain
open. The old lookahead fast-path timing is historical and does not qualify
this source. Literal regressions and narrow source proofs support only their
stated boundaries.

Runtime operation inventory (numeric allocator bound still open): each
`fn-zin-loop` action pulls one input octet or invokes `fn-zin-step`.
Copy/literal bulk helpers emit at most the remaining 64-byte output room
across a chunk. A table-building action has fixed work: fills touch at most
320 lengths; `fn-zin-construct` clears a 512-entry lookup, counts/places at
most 288 symbols, and walks fifteen code lengths. Its lookup fill nests at
most 288 symbols with at most 256 replicated entries each (a conservative
syntactic bound, not a claim that valid tables reach that product). Two
constructs build literal and distance tables. Tables mutate the reserved
3,494-byte slot. These helpers allocate no new vector or octet list in the
concrete path once dedicated slots are initialized.

Arithmetic includes shifts and bit operations, bounded table indices, and
profile-sized input/output/budget counters. Live magnitudes include C,
actual input at most C, temporary credited input at most 2*C, allowance
256*C+65,536, and budget 4,096+16*C+2*N. The wrapper temporarily biases the
input counter; it never represents the declared C as a C-sized allocation.
Admission must charge boxed integer temporaries, twenty natural registers,
bounded status/error conses, runtime multiple-value/control overhead and
fresh-vector replacement coexistence. Source loop/action bounds are not a
measurement or proof of those SBCL allocator costs. A positive scheduling
quantum is necessary for progress; a zero quantum merely yields.
