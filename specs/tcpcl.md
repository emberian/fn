# TCPCLv4 convergence layer

Status: all five roots certify on the w6/tcpcl-tests tree (dev 1c5b950):
`books/tcpcl-records`, `books/tcpcl-octets` (146 s), `books/tcpcl-session`
(31 s), `books/tcpcl-invariants` (840 s) in
`build/acl2/certify-20260920T173807Z-1231440` and `tests/acl2/tcpcl-tests`
(0.6 s) in `build/acl2/certify-20260920T175604Z-1409642`, both on persvati
with ACL2 8.7. The statements of sections 3, 4 and 6 are therefore theorems
proved by ACL2 on that tree, each with the hypotheses its own section states.
The native host integration is proposed in
[the lane handoff](../planning/lanes/HANDOFF-w4-tcpcl.md) and not built.
Design: [bp-design.md §2](bp-design.md). RFC: `rfc9174.txt` (RFC 9174,
TCPCLv4). No interoperability, server or flight claim follows from this
document; the labs of bp-design §3 are where those are earned.

## 1. What the books decide

fn speaks TCPCLv4 as a peer of dtn7-rs and ION. Every protocol decision is
an ACL2 definition; the host performs socket I/O and calls one served
function per received chunk, `fn-tcl-drive`, and one function per host
event (`fn-tcl-open`, `fn-tcl-send`, `fn-tcl-pump`, `fn-tcl-tick`,
`fn-tcl-terminate`, `fn-tcl-tcp-closed`). Each returns an opaque result
record `(fn-tcl-make-result session events unconsumed)`: the next session,
the events for the host in order, and the octets the host must keep and
prepend to the next chunk.

Events the host acts on: `(:send msg)` (encode with `fn-tcl-encode` and
write, in order), `(:session-up negotiated)`, `(:bundle-received xfer-id
octets)`, `(:inbound-refused xfer-id reason)`, `(:inbound-failed xfer-id)`,
`(:outbound-sent xfer-id ref)`, `(:outbound-refused xfer-id ref reason)`,
`(:outbound-failed xfer-id ref)`, `(:send-refused ref why)`,
`(:peer-terminating reason)`, `(:peer-rejected reason header)`, `(:close)`
(close the TCP connection after the writes), `(:session-down)`.

Three outcomes of an inbound transfer stay distinct all the way out:
complete (`:bundle-received`), refused (`:inbound-refused`, with the Table 6
reason), failed (`:inbound-failed`, TCP close or a decode error). A decode
returns one of `fn-tcl-parse-ok`, `fn-tcl-parse-need` or
`fn-tcl-parse-error`, never a partial record.

## 2. Octet grammar (`books/tcpcl-octets`)

Every message is an exact octet grammar over `fn-cbor-octet-listp`. Each
length field is compared with its cap before any `fn-tcl-take`: node ID
length against 1024, an extension item list against 4096 (both local
policy caps), a segment's data length against fn's own Segment MRU. A
buffer that holds no complete message yields `(fn-tcl-parse-need)` with
nothing copied. Flag octets are kept raw in the records, so canonicality is
exact; reserved bits are ignored by the session's flag predicates, as
§4.2, Table 5 and Table 8 require of a receiver.

Keystones, per decoder (`init`, `segment`, `ack`, `refuse`, `term`,
`reject`, the segment's data part, and the Contact Header) and at the
message level (`fn-tcl-decode-message`, dispatch on the type octet):

| Property | Theorem | Hypotheses | Covered scope |
| --- | --- | --- | --- |
| Round trip | `fn-tcl-decode-message-of-encode-<kind>`, `fn-tcl-decode-contact-of-encode` | `fn-tcl-messagep` of the constructed record under the decoder's MRU | one well-formed message followed by any octets decodes to itself with the rest untouched |
| Canonicality | `fn-tcl-accepted-message-is-canonical`, `fn-tcl-accepted-contact-is-canonical` | octet list; the decode accepted | every accepted octet string is the encoding of its decode followed by the returned rest, over arbitrary input |
| Well-formed decode | `fn-tcl-decode-message-yields-message` | octet list; MRU at most 2^64 - 1; accepted | the decoded record satisfies `fn-tcl-messagep` under that MRU |
| Prefix determinism | `fn-tcl-decode-message-append-ok`, `-append-error` (and per decoder) | octet list; the outcome on the left part | an accepted or rejected prefix decides the same on any extension, with the rest extended |
| Consumption and typing | `fn-tcl-decode-message-consumes`, `-rest-octet-listp` | accepted | the rest is a strictly shorter octet list |
| Exhaustive outcomes | `fn-tcl-decode-message-outcomes` | octet list | exactly one of ok, need, error |
| MRU at the decoder | `fn-tcl-segment-never-exceeds-mru`, `fn-tcl-decoded-segment-fits-mru` | eight octets of length present; length over the MRU | the error is returned before any data octet is taken; accepted data fits the MRU |
| Need bound | `fn-tcl-need-means-short-buffer` | octet list; natural MRU | a `need` is returned only for a buffer shorter than `fn-tcl-max-message` = 5145 + MRU octets |

Item lists (session and transfer extension items) have their own round
trip (`fn-tcl-decode-items-of-encode-items`), canonicality
(`fn-tcl-accepted-items-are-canonical`) and typing
(`fn-tcl-decode-items-yields-items`); an item list must exactly fill its
declared length or the message is an error (§4.6, §5.2.2).

The pessimistic number: the retained carry is below 5145 + Segment MRU
octets; the true maximum message is max(5145, 4118 + MRU) for SESS_INIT
and XFER_SEGMENT respectively, so the bound is loose by at most 1027
octets.

## 3. Session machine (`books/tcpcl-session`)

State is the opaque session record: role, phase (`:tcp-connected`,
`:contact`, `:messaging`, `:established`, `:ending`, `:closed`), own
parameters, the negotiated Enable TLS, the peer's SESS_INIT, the negotiated
parameters, at most one inbound and one outbound transfer, the Transfer ID
frontier, the monotonic milliseconds of the last message each way, and the
SESS_TERM state (`nil`, `:sent`, `:both`). `fn-tcl-sessionp` is the carried
invariant: it guards every entry point, is preserved by every transition
(`fn-tcl-step-preserves-sessionp`, `fn-tcl-drive-preserves-sessionp`,
`fn-tcl-send-`, `fn-tcl-pump-`, `fn-tcl-tick-`, `fn-tcl-terminate-`,
`fn-tcl-tcp-closed-preserves-sessionp`), and is never re-run per octet.
The inbound record carries the sum of its staged segment lengths and the
recognizer requires that sum to be the measurement of the staged list, so
the transfer MRU is a carried bound (`fn-tcl-retained-transfer-is-bounded-
by-definition`), as in `books/wire.lisp`.

Work per octet: the decoder reads each octet once and copies each data
octet once (`fn-tcl-take` under a checked bound); an inbound segment is
consed onto the staged list, concatenated once on END
(`fn-tcl-concat-rev`); an outbound transfer keeps the unsent suffix so each
`fn-tcl-pump` costs its segment. No recognizer runs over retained input on
the served path (`fn-tcl-drive`'s `mbe` check is `:exec nil`).

## 4. Keystones C1 to C4 (`books/tcpcl-invariants`)

Status (2026-09-20, w6/tcpcl-c4): C1 to C4 are proved by ACL2 and `books/tcpcl-invariants` certifies over `books/tcpcl-session` (evidence `build/acl2/certify-20260920T052819Z-3093104` on persvati; invariants 671.8 s, closure 840.9 s, ACL2 8.7). Two C4 defects were found by the proof and fixed in the statements, not the hints: `fn-tcl-no-interleaving` asserted the phase after the step is `:ending` where the session can close in that step (section 6), and it did not state the Retransmit refusal of the live transfer that section 5.2.2 requires. C2 is proved with `fn-tcl-sessionp` and every sub-recognizer closed: six local `-emits-no-bundle-received` lemmas dismiss the non-segment branches of `fn-tcl-step`, the local `fn-tcl-recv-segment-final-ack-means-every-segment` carries the content at the transition that owns it (115 subgoals, 0.3 s), and C2 lifts it to the step by `:use` at `(fn-tcl-touch-rx s now)`; the carried sum reaches the proof through the forward-chaining field facts `fn-tcl-sessionp-forward-inbound`, `fn-tcl-inboundp-forward-fields` and `fn-tcl-inboundp-forward-total`.

**C1** `fn-tcl-drive-partition-independence`. Hypotheses: `fn-tcl-sessionp`,
two octet lists, `fn-clock-timep`. Driving `(append left right)` is driving
`left`, then driving `(append unconsumed right)` from the session that
left, with the events concatenated and the final carry. Covered scope: the
served path with the host's carry, for every session and every split. The
tooth is the chunk-size sweep in `tests/acl2/tcpcl-tests.lisp` (chunks of
1, 2, 3, 7 and 64 octets over a two-segment transfer give the same result
as one chunk), plus a split inside a message. No separating value exists
for the hypotheses: outside them `fn-tcl-drive` is a no-op on both sides,
so they are the guard of the served path rather than a boundary of the
property; removing them is an open simplification.

**C2** `fn-tcl-final-ack-means-every-segment`. Hypotheses: `fn-tcl-sessionp`,
`fn-tcl-messagep` under the session's Segment MRU, `fn-clock-timep`, and a
`:bundle-received` event in the step's events. Conclusion: the message is
an XFER_SEGMENT with END for the live transfer's ID (or START and END for
a new one), the session is Established or Ending, nothing is live
afterwards, the delivered length is the carried received length plus this
segment, the emitted XFER_ACK carries exactly that length with the
segment's flags, and a declared Transfer Length equals it. With
`fn-tcl-inbound-is-created-only-by-start` (an inbound record exists only
from a START segment for its ID) and the carried-sum invariant, the ack
that completes a transfer sums every segment from START to END. Covered
scope: one `fn-tcl-step`; the lift to a stream is the fold in `fn-tcl-drive`
(C1 says the fold is chunk-independent).

**C3** `fn-tcl-tcp-close-never-completes-a-transfer` (a TCP close emits no
`:bundle-received`, emits `:inbound-failed` for the live transfer, leaves
nothing live), `fn-tcl-input-error-never-completes-a-transfer`,
`fn-tcl-step-emits-at-most-one-inbound-outcome` (at most one of
`:bundle-received`, `:inbound-refused`, `:inbound-failed` per ID per step),
`fn-tcl-live-inbound-ends-in-exactly-one-outcome` (a live transfer that is
not live after a step produced exactly one), and
`fn-tcl-tick-fails-a-live-inbound-only-when-closing`. Together: an inbound
transfer's outcome is exactly one of complete, refused, failed. Covered
scope: every transition, one step at a time.

**C4** `fn-tcl-no-interleaving` (a segment whose Transfer ID is not the
live inbound transfer's: the live transfer is refused Retransmit, MSG_REJECT
Message Unexpected is sent, no `:bundle-received` is emitted, no inbound
record survives -- so a second transfer never opens -- and the phase
afterwards is exactly `:closed` when the session's `term` is already `:both`
and nothing is outbound, `:ending` otherwise. The second case is the SESS_TERM
handshake's "Transfers Done" (RFC 9174 §6.1): clearing the live transfer is
the last condition `fn-tcl-settle` waits for, so the step that refuses the
interleaving segment also closes the session. The wave-4 statement, which
asserted `:ending` outright, was therefore not a theorem; the witness is
`*t-b-inter-both*` in `tests/acl2/tcpcl-tests.lisp` and the two cases are
separated there by `*t-b-inter*` (`:ending`) against it (`:closed`)),
`fn-tcl-ending-refuses-new-transfers` (a START in Ending is refused Session
Terminating and creates no inbound), `fn-tcl-ending-refuses-new-sends` (a
send outside Established is refused locally, state unchanged),
`fn-tcl-refused-transfer-sends-no-more-segments` (after XFER_REFUSE for the
live outbound, the outbound is gone and `fn-tcl-pump` emits nothing),
`fn-tcl-keepalive-zero-disables-both` (negotiated 0: no KEEPALIVE, no idle
timeout), `fn-tcl-negotiation-is-min-and-and` (keepalive is the minimum,
MTUs are the peer's MRUs, TLS is the conjunction, §4.3 and §4.7),
`fn-tcl-contact-tls-is-conjunction` (and a true conjunction is refused
Contact Failure in wave 4), `fn-tcl-retained-input-is-bounded` (while the
session is open the carry the served path returns is shorter than
`fn-tcl-max-message`), `fn-tcl-step-keeps-local`. The §5.2.4 MUST (refuse
only after every preceding transfer is acked or refused) holds by
structure: one inbound transfer at a time, every segment acked in the step
that accepts it, and a refusal names either the live transfer or the START
that was never accepted.

## 5. RFC 9174 clause matrix

| Clause | Status | Where / why |
| --- | --- | --- |
| §4.1 active sends CH first, passive waits, CH timeout | implemented (timeouts are the host's) | `fn-tcl-open`, `fn-tcl-recv-contact`; the host applies the ≤60 s contact timeout and calls `fn-tcl-tcp-closed` |
| §4.2 Contact Header, CAN_TLS, reserved flags ignored | implemented | `fn-tcl-decode-contact`, `fn-tcl-flag-can-tls`; CAN_TLS = 0 sent (`fn-tcl-own-contact`) |
| §4.3 magic check closes silently; version mismatch (passive: CH then SESS_TERM; active: close); Enable TLS = AND, unacceptable → Contact Failure | implemented | `fn-tcl-input-error` before contact; `fn-tcl-recv-contact` |
| §4.3 version fallback to TCPCLv3 | deferred | fn implements version 4 only; a peer's lower version is Version mismatch |
| §4.4 TLS handshake, certificates, node ID authentication | deferred (profile slot) | wave 4 sends CAN_TLS = 0 and refuses a negotiated Enable TLS of true; the session record keeps the conjunction so a host TLS primitive can be added without a state change |
| §4.5 message header; unknown type → MSG_REJECT Message Type Unknown and close | implemented | `fn-tcl-decode-message`, `fn-tcl-input-error` |
| §4.6 SESS_INIT fields; zero-length node ID; extension list must fill its length | implemented (node ID ≤ 1024 octets local cap) | `fn-tcl-decode-init`; a zero-length node ID is accepted and fails the contact-plan check when one is configured |
| §4.6 unauthenticated node ID SHOULD NOT drive routing | implemented as policy | `fn-tcl-init-acceptablep` refuses a node ID other than the configured peer (`expected-peer`); routing is the scheduler's contact plan |
| §4.7 negotiation: MTU = peer MRU, keepalive = min, unacceptable → Contact Failure | implemented | `fn-tcl-negotiate`, `fn-tcl-init-acceptablep` (a zero MRU is unacceptable) |
| §4.8 session extension items; unknown CRITICAL → Contact Failure; non-critical skipped | implemented | `fn-tcl-no-critical-items`; fn sends none |
| §5.1.1 KEEPALIVE when the interval elapsed with no transmission; idle timeout at twice the interval | implemented (resolution is the host's tick period) | `fn-tcl-tick` over `fn-clock-observationp` |
| §5.1.2 MSG_REJECT Unknown / Unsupported / Unexpected | implemented | Unknown on unknown type; Unsupported on a malformed known message; Unexpected for a message in the wrong state, an XFER_ACK for an unknown or unsent range, a stray segment |
| §5.2 one bundle per transfer; no interleaving | implemented | `fn-tcl-no-interleaving`; the host hands one bundle per `fn-tcl-send` |
| §5.2.1 IDs unique per direction, from 0 by 1; exhaustion → Resource Exhaustion | implemented | `next-xfer-id` frontier; `fn-tcl-send` |
| §5.2.2 START/END flags; extension items only on START | implemented | codec and `fn-tcl-pump` |
| §5.2.3 an XFER_ACK per segment, flags mirrored, cumulative length; sender pipelines segments | implemented | `fn-tcl-stage`, `fn-tcl-complete`; `fn-tcl-pump` emits the next segment without waiting for an ack |
| §5.2.4 XFER_REFUSE reasons; refusal after any segment; sender stops; crossing refusals; refuse only after preceding transfers settled | implemented | Table 6 codes as `*fn-tcl-refuse-*`; `fn-tcl-refused-transfer-sends-no-more-segments`; a refusal for a finished transfer is ignored |
| §5.2.5 transfer extension items; unknown CRITICAL → Extension Failure | implemented | `fn-tcl-ext-decision` |
| §5.2.5.1 Transfer Length Extension: at most once; authoritative; mismatch → Not Acceptable; over the Transfer MRU → refused | implemented | `fn-tcl-ext-decision` (duplicate → Not Acceptable, wrong width → Extension Failure, over MRU → Not Acceptable per bp-design §2.1); `fn-tcl-recv-segment` refuses a running total beyond the MRU with No Resources |
| §6.1 SESS_TERM initiation and reply with identical content; Ending accepts and starts no new transfers; in-progress transfers may finish; TCP close mid-transfer fails it | implemented | `fn-tcl-recv-term`, `fn-tcl-terminate`, `fn-tcl-settle`, `fn-tcl-tcp-closed` |
| §6.1 unclean termination (SESS_TERM then immediate close) | not used | fn always waits for the reply or the peer's silence (idle timeout in Ending closes) |
| §6.1 SESS_TERM before a CH has been sent is forbidden | implemented | `fn-tcl-terminate` closes without SESS_TERM in `:tcp-connected` |
| §6.2 idle session termination | implemented | idle timeout in `fn-tcl-tick` |
| §3.3 transfer pipelining (a new transfer while waiting for the final ack) | not implemented (a MAY) | one outbound at a time; a second `fn-tcl-send` is refused `:busy` and the node retries |
| §3.1 reception interruption by the BPA before END | not implemented | the node sees a transfer only on END; a policy refusal before END is a later host event |
| §7 security considerations | stated, not solved | bp-design §4: sessions are bound to the contact plan's peer; TLS is a slot |

Local policy choices, beyond the RFC: node ID and extension list caps
(1024 and 4096 octets); a malformed known message closes the session after
MSG_REJECT because the stream cannot be resynchronised (§8.5); a segment
that interleaves refuses the live transfer with Retransmit and terminates
Contact Failure; the transfer MRU is enforced on the running total before
a segment is staged, so at most one segment (≤ Segment MRU) is held
transiently beyond it.

## 6. Open

- The wave-4 checkpoint at `Subgoal 1082.10'` is closed. Its cause was not
  the `:do-not-induct` hint -- `fn-tcl-step` is not recursive, so induction
  was never wanted -- but the `(in-theory (enable fn-tcl-sessionp))` above
  the theorem: opening the recognizer put its eleven conjuncts, each itself
  a sub-recognizer over a record, into the clause and split it into 1082
  subgoals before the segment cases were reached. With the recognizer and
  every sub-recognizer closed the segment lemma is 115 subgoals in 0.3 s.
  C2 keeps its statement and stays `:rule-classes nil` (its equality has
  the variable `id` on its left). `fn-tcl-inbound-is-created-only-by-start`
  needed the same treatment plus six `-keeps-inbound` branch lemmas.
- The wave-4 checkpoint at `fn-tcl-no-interleaving` is closed, and it was
  not a hint problem: the theorem was false. Its fourth conjunct asserted
  the phase after the step is `:ending`, and a session in Ending whose
  SESS_TERM handshake is complete (`term` `:both`) with a live inbound and
  nothing outbound closes in that step instead -- `fn-tcl-broken-stream`
  clears the inbound, which is the last condition of `fn-tcl-settle`'s
  "Transfers Done". That state is reachable (`fn-tcl-recv-term` keeps the
  live inbound), and `*t-b-inter-both*` in `tests/acl2/tcpcl-tests.lisp`
  reaches it in four drives from the golden session. The conjunct is now the
  exact case split on `term`/`outbound` rather than a disjunction, and a
  conjunct the wave-4 statement lacked -- the `:inbound-refused` Retransmit
  of the live transfer, which is what §5.2.2 requires and what makes the
  theorem about interleaving rather than about the reject -- was added. Two
  local lemmas carry it, both with the recognizer closed:
  `fn-tcl-recv-segment-interleave-is-broken-stream` (the branch test reads no
  conjunct of `fn-tcl-sessionp`; a rewrite rule, 853 steps) and
  `fn-tcl-settle-of-broken-stream` (`:rule-classes nil`, 9944 steps), lifted
  at `(fn-tcl-touch-rx s now)` by `:use` with `fn-tcl-settle`,
  `fn-tcl-recv-segment` and `fn-tcl-broken-stream` disabled so the two
  lemmas meet the term the step builds (7265 steps, 0.02 s for C4 itself).
  The `:use` is not decoration: as a rewrite rule the settle lemma does not
  fire, because its conclusion holds the ground term
  `(fn-tcl-make-msg-reject 3 1)` while the goal holds the constant ACL2 has
  already evaluated it to (measured, `certify-20260920T050746Z` prelude run).
- `tests/acl2/tcpcl-tests` certifies (0.6 s,
  `certify-20260920T175604Z-1409642`), and every witness in it has run,
  `*t-b-term*` and `*t-b-inter-both*` included. Two defects had held it,
  both in the test book. The wave-4 XFER_SEGMENT golden vector wrote the
  transfer extension item header as `0 1 0 0 8`, the type before the flags;
  figure 25 of RFC 9174 section 5.2.5 puts Item Flags first, so
  `fn-tcl-encode` was right and the vector was wrong. The book's last form
  evaluates `fn-tcl-drive` on `42`, outside its guard, and needed
  `with-guard-checking :none`. The manifest that recorded exit 0 for the
  failed root was a runner defect, fixed in `tools/certify_books.py`: the
  driver ends in `(quit)`, which exits 0 whether or not the inner `ld`
  returned on a failed `certify-book`, so the manifest now carries a
  per-book verdict computed from that book's own log.
- `fn-tcl-retained-input-is-bounded`, the last form of the book, needed the
  two decoder need bounds of `books/tcpcl-octets` restated locally against
  the opened `fn-tcl-max-message` (`fn-tcl-need-message-under-max`,
  `fn-tcl-need-contact-under-max`): as exported, one is triggered on
  `(len buf)` with `mru` free and the other is a rewrite rule only, so
  neither reaches the linear arithmetic of the fold's two "need more
  input" subgoals. Cited with their own rules disabled, or the citation is
  rewritten to T before it can be used.
- The host integration (`host/native/tcpcl.lisp`) and lab I1 are proposed
  in the handoff, not built; the final XFER_ACK after the FNBS record is
  barriered (bp-design §2.4) is a host ordering the model states as
  "ack emitted in the step that completes", so the host must hold that ack
  until the barrier.
- C1's hypotheses have no separating witness (see §4) and could be
  dropped by proving the composition over the `mbe` no-op cases too.
- Transfer pipelining, reception interruption, TLS.
