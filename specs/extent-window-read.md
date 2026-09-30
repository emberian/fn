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

## Stored composition (PRF-1131 / SCN-1037)

`fn-ewz-begin` retains `(mode raw-plan N decoded-offset wanted budget ip end
codec-status)`. It calls the unchanged actual raw controller with requested
raw offset C, so WN=0; original POFF/PLEN=C, protected extent and typed
ownership remain captured. The decoder uses the same private16KiB window,
fixed64-byte scratch and existing fixed history/table slots. Its returned
scratch is copied by the actual `fn-ewb-copy` through the congruent output
buffer. No second decoder, wholeC/N list or extra16KiB output is introduced.

`fn-ewz-read` first accepts and hashes the exact core-issued read, then
selects its compressed overlap. `:codec` suppresses read effects while
`fn-ewz-codec-tick` retains that input across at most1024 actions and64 output
bytes per tick. The total budget is `fn-pzd-budget(C,N)` and is carried using
`fn-pzw-budget-left`; quantum exhaustion resumes. Only `:input` with IP=END
releases that input for scanning. A valid final block enters `:drain`, which
hashes all remaining compressed/protected bytes without calling the decoder
again. At positional completion the stored decision must accept exactN and
a final/sync-flush terminal before the wrapper becomes `:decoded`. C=0
starts in `:drain`, so an empty payload after a protected prefix cannot be
prematurely treated as a truncated nonempty decoder request.

The host must dispatch `fn-ewz-next-action`: `:codec`, `:read`, `:tick`,
`:refused`, or `:ready`. `:ready` alone returns the publication tuple
`(ticket incarnation lease :decoded decoded-offset wanted)` and requires
both `:decoded` and raw publication. A raw subplan's `:verified` status
cannot expose a compressed window. Source proofs describe every copy cell,
accepted actual decoder completion, carried codec evidence under all three
transitions and newly published actual trailer integrity. The logical
invariant is carried proof evidence; the served entry does not revalidate
whole state. Literal local-stobj witnesses affirm the complete boundary
checks and distinguish removal from malformed/short/corruption regressions.

This is source component evidence. Full captured-source digest/decoded
trajectory, actual TIN<=C sequence invariant, total scheduling/action-budget
completeness, allocator/profile funding, native lifetime/dispatch/borrow
integration and matching images/natives remain open.

### Real compressed-input carry

`fn-ewz-scanned-input` derives `min(C, nfix(EOFF+POS-POFF))` from the
original captured compressed payload coordinates. The proof-only carried
`fn-ewz-input-invariantp` states real TIN=scanned during scan, and
TIN+(END-IP)=scanned while a codec quantum retains input. Drain/decoded
states preserve TIN<=scanned; trailing compressed bytes may be hashed after
a final block without being decoded. All states retain natural IP/END with
0<=IP<=END<=64. A drain also carries the actual ended codec status, so a
hash tick cannot resume a fabricated decoder continuation.

Actual BEGIN, READ, CODEC-TICK and HASH-TICK establish/preserve the carry;
its consequence is TIN<=C. No served entry traverses or validates this
logical invariant. The codec proof also covers malformed pool refusal:
those refusals consume zero input and restore the credited input counter.
The actual codec's exported input-span bound and bit-width evidence are
included from `payload-window-width`. This does not establish a numerical
SBCL allocator allowance or the whole decoded trajectory.

Literal witnesses follow the actual dispatcher before read completion,
show nonempty codec and empty-payload drain transitions, and affirm each
full antecedent and conclusion. Malformed-coordinate and corrupted-state
hypothesis-removal witnesses are labelled separately. Native integration,
full trajectory, total progress and allocation/profile funding remain open.

### Active decoded-output carry

`fn-ewz-output-invariantp` carries original C/N admission and actual
TOUT<=min(N,storedAllowance(C)) in scan, codec, drain and decoded modes.
Inactive refusal modes may retain a private overflow sentinel. Actual
BEGIN establishes the carry without hypotheses. Actual CODEC-TICK also
establishes it without a pre-call carry or pool-shape hypothesis: its
stored-decision gate excludes output overshoot before any active mode is
returned. READ and HASH-TICK preserve the carried evidence without further
coordinate hypotheses. No served entry evaluates this proof recognizer.

Literal witnesses execute nonempty scan/read/codec and final empty drain
transitions. Corrupted-state READ and scan-HASH removals check failure of
the sole carry hypothesis and of the conclusion. The codec theorem has no
hypotheses to remove. This is numerical output carry, not whole-decoder
fidelity, total scheduling completeness or a runtime allocation claim.

### Actual captured-source authentication trajectory

The proof-only `extent-window-stream-semantics` boundary connects the
concrete word assembly in actual `fn-ews-read` to the canonical block
required by the digest trajectory. The captured immutable source is an
octet-list proof parameter, not an allocated execution buffer. An honest
read completion supplies exactly `fn-shr-win(POS,demand,source)`; fixed
concrete `fn-b3x-words` then equals the first sixteen words of the digest's
truncating logical span. This handles short final blocks and distinguishes
TAKE padding from source truncation. No host-provided digest or word-list
assumption replaces that byte boundary.

Actual BEGIN establishes the imported semantic/domain/counter invariant
under natural depth<=63, source octets of length ELEN and
ceil(ELEN/8)<=128*2^depth. READ preserves it with carried evidence and the
exact source slice when in scan; refused and stale reads do not require an
honest slice. TICK preserves it with only carried evidence. A newly
published READ proves that its actual trailer equals fn-blake3(source)
and its retained descriptor commitment is that digest's packed value.
No whole-source or whole-state recognizer is run on the served path.

Literal witnesses assert complete antecedents and conclusions, including
each necessary initializer/read/tick/publication/canonical removal;
corrupted private states are labelled separately. The canonical theorem's
redundant scan-mode hypothesis was removed after proving the weaker result.
This authentication safety trajectory leaves positional tree-frontier
scheduling completeness, physical honest-source realization, full decoded
trajectory and runtime allocation/funding open. It adds no native or
image qualification claim.

## Decoded scalar cold boundary (source stage)

The actual arena scalar compressed branch uses fn-durable-realize-lz-octet,
whose logical value is exactly NTH I of the existing durable decoded value.
A singleton replacement of the whole-list boundary is invalid at nonzero I.
The separate :decoded-window token binds ticket and the complete nine-field
stored descriptor: file, extent offset/length, compressed payload offset/C,
decoded offset, trailer, N, shipped dictionary ID. The immutable shipped
lookup is canonical; unknown dictionaries refuse. Physical C63 alone does
not impose N63. Operator profile validation and runtime representation must
cover the full accepted storedAllowance(C) range.

The new lease admission accounts a supplied vector and holds the file.
Selected-runtime compressed demand adequacy, complete decoder trajectory,
shared lifecycle/publication and native activation remain open. This source
stage adds no served compressed or matching image claim.

The actual typed initializer establishes the complete captured token/plan
join. The staged scalar callback checks the full descriptor and original
index in ACL2 before private buffer supply. Its decoded-ready branch is
unreachable-in-composition under the current raw-only physical predicate;
the shared OR-kind lifecycle and full decoded/dictionary trajectory must
land before activation. The initializer join is not that semantic proof.

### Actual bounded copy trajectory component

The actual `fn-zin-copy` splits K1+K2 copied bytes into two calls with
identical final ring position, ring bytes and output. The actual mode12
`fn-ewz-codec-tick` binds complete decoder/ring/table/scratch/private-window
effects to its actual64-byte copy and ACL2-selected overlap. Its source
conditions include positive quantum, pending copy count, funded output room,
retained input span, and actual fixed history/table readiness. The stored
wrapper consumes one action for that copy fragment. Literal witnesses reach
the controller through actual initialize/hash-prime/read/codec transitions,
affirm every condition and effect, and falsify each condition separately.
The63-byte allowance witness distinguishes sentinel room from funded copy.

A251-octet repeated-match archive produces identical octets in the existing
whole stored decoder and the authenticated bounded controller. General
faithfulness still requires state/output stuttering: room-dependent copy
and literal batching changes scheduling action consumption, so equal
action-budget output splitting is not assumed. Complete decoder/dictionary
trajectory, total budget adequacy, compiler/runtime demand and native
lifecycle/consumer activation remain open. This is source component
evidence, not certification or a qualified served path.

The shared source executor accepts the distinct decoded token and retains its
full identity through actual acquire, cancellation, return and settlement.
Raw plan publication requires the raw kind and descriptor. This source join
does not install a decoded native worker/buffer holder: the native dispatcher
explicitly refuses decoded execution until exact object/view binding and
matched compressed runtime funding are supplied. See the source coordinate
in planning/evidence/decoded-window-shared-join-source-2026-09-30.md.

The typed publication source fixture now executes the actual issuer, shared
worker acquisition, typed initializer, authenticated bounded decoder, return
and scalar read on the carried buffer. Its final251-A octet agrees with the
existing whole decoder; stale ownership, mismatched request, cancellation
and release remain distinct. This fixture does not replace the general
decoder trajectory or native object/view binding obligations. See
planning/evidence/decoded-window-publication-source-2026-09-30.md.
