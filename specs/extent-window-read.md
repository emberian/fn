# Protected extent windows

Status: PRF-1109 / SCN-1018, component source proofs in progress. The served
path still uses the whole-extent realizer. This document does not claim that
P12, default funding, streaming digest or compressed realization is complete.

A descriptor `(FILE EOFF ELEN POFF PLEN TRAILER)` binds the protected prefix
`[EOFF, EOFF+ELEN)`, its following 32 trailer bytes, and a payload within it.
ELEN can include many packed records; a per-record ceiling cannot bound it.

`fn-ewp-begin` chooses the next requested payload window at OFFSET, with
length `min(16384, PLEN-OFFSET)`. This is a scheduling quantum. It neither
truncates the payload nor allocates ELEN or PLEN cells. The exact capture,
physical incarnation and resource lease accompany the ticket for the entire
scan, trailer check, private result and borrower lifetime.

The controller state is
`(phase file eoff elen woff wn expected pos ticket incarnation lease)`.
WOFF is relative to the protected prefix. `fn-ewp-effect` is either NIL or
`(ticket incarnation lease file absolute-offset count phase)`. It authorizes
at most 64 prefix bytes or the 32 trailer bytes. `fn-ewp-complete-read` accepts
only that exact effect and exact byte count. Stale effects preserve state;
short/error reads settle as `:read`; no read completion publishes a window.
Every successful scan completion advances by the exact demanded count.

`fn-ewp-window-span` selects `(input-offset count output-offset)` within the
bounded block. `fn-ewb-capture` copies this overlap into a fixed 16 KiB octet
array. Its refinement describes every output byte, including unchanged
cells outside the overlap. No logical list of the extent or requested data
is constructed on this executable path. `fn-ewp-payload-span` similarly
selects the bounded compressed-payload input for the existing inflater.

All captured bytes remain private until the entire prefix was consumed,
the trailer was read, its exact 32-byte commitment matches the descriptor,
and the actual incremental digest equals it. `fn-ewp-finish` checks the
terminal position and commitment. Its digest argument is an unfinished
composition boundary, not an integrity assertion supplied by the host.
The integrated entry must drive the concrete byte digest over precisely
the consumed bytes before invoking finish; the current component is not
an authenticated reader by itself. Digest tail handling, allocation/stack
domain, source pinning, progress and the existing frame-digest attachment
must be proved at that boundary. A-CRYPTO's pessimistic collision work is
2^128 for BLAKE3; digest equality does not prove source byte equality.

Compressed reads reuse the existing DEFLATE inflater with bounded input,
fixed history/table buffers, bounded scratch output, and a retained private
requested decoded window. Publication additionally requires the same
complete stream acceptance and exact decoded length as `fn-pzd-decode` /
`fn-lzr-lz-value`. The existing lookahead/plain-loop distinction must be
resolved by a real refinement before switching callers. A window filled
early is never evidence that the rest of the compressed stream is valid.

The native ownership adapter must fund fixed scratch, digest state, output
window, decoder pools when used, and actual worker lifetime before issuing
I/O. A cache key includes the requested window and full physical identity;
an extent-only hit cannot authorize missing bytes. Cancellation does not
refund a still-running worker or invalidate another borrow. The physical
owner maintains descriptor/file pins through actual relinquishment.

Remaining integration: byte-digest composition, compressed acceptance
refinement, native window-specific admission/cache/borrow wiring, literal
full-path witnesses, matched certification and native behavior evidence.
No new frame ceiling or fallback to whole-extent allocation is authorized.
