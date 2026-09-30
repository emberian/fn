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
`(phase file eoff elen woff wn expected pos ticket incarnation lease poff plen offset)`.
WOFF is relative to the protected prefix. The original payload offset,
length and requested offset also remain captured; phase changes preserve them. `fn-ewp-effect` is either NIL or
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

`fn-ews-begin` captures the original request and initializes the actual byte
BLAKE3 cursor. `fn-ews-effect` authorizes an input block only when the cursor
requests precisely that position and count. `fn-ews-tick` performs one internal
hash action when no input is needed. `fn-ews-read` accepts only the exact effect,
uses the actual input buffer length, assembles at most sixteen padded words,
steps the cursor and copies the selected private overlap. Stale completions
preserve all three states; its output theorem describes every window cell.

The trailer effect becomes available only when the full scan has completed
and the actual cursor is done. The completion obtains its digest directly
from `pgs-dcb-result-octets`; no host-supplied digest argument reaches the
composed entry. New publication requires exact trailer commitment and equality
to that cursor result. Rejected commitments use `:commitment`, distinct from
the pending `:trailer` phase, so a rejection cannot restart trailer reads.
The general captured-source digest trajectory, fixed-stack supported domain
and progress remain separate proof obligations; actual-cursor integrity alone
does not close them. The frame function has a concrete closed BLAKE3 definition
with an explicit bridge. A-CRYPTO's pessimistic collision work is 2^128 for
BLAKE3; digest equality does not prove source byte equality.

Compressed reads reuse the existing DEFLATE inflater with bounded input,
fixed history/table buffers, bounded scratch output, and a private requested
decoded window. The coordinator authorized a stored total-compressed-length
allowance policy and stricter real terminal detection after finding a
lookahead/prefix bomb-admission mismatch and false truncated success in the
legacy stored decoder. The codec owner proves and documents that changed
acceptance domain separately; no equality to the old defective acceptance
policy is asserted. Publication requires complete accepted decode, exact
decoded length and the same full protected-prefix integrity. A window filled
early cannot authorize publication.

The native ownership adapter must fund fixed scratch, digest state, output
window, decoder pools when used, and actual worker lifetime before issuing
I/O. A cache key includes the requested window and full physical identity;
an extent-only hit cannot authorize missing bytes. Cancellation does not
refund a still-running worker or invalidate another borrow. The physical
owner maintains descriptor/file pins through actual relinquishment.

Remaining integration: full digest trajectory and supported-domain proof,
compressed composition, native window-specific admission/cache/borrow wiring, literal
full-path witnesses, matched certification and native behavior evidence.
No new frame ceiling or fallback to whole-extent allocation is authorized.
