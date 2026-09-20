# Handoff: w9/dtn-e2e — the served-path guard, and what a BP node over TCPCL still needs

Branch `w9/dtn-e2e`, worktree `build/lanes/w9-dtn-e2e`, from `dev` at `52eb0db`
and merged forward to `d50c392` (the `w6/nntp-effects` fix). Box: hbox,
`/tank/fn/lanes/w9-dtn-e2e`, ACL2 `/tank/fn/acl2-8.7/saved_acl2`, cache
`/tank/fn/certcache`.

## 1. The performance fix w8 found (landed)

`books/tcpcl-session.lisp`. The finding was
[HANDOFF-w8-tcpcl-native](HANDOFF-w8-tcpcl-native.md) "Open": `fn-tcl-drive`'s
guard was `fn-tcl-sessionp`, whose `fn-tcl-inboundp` runs `fn-tcl-octet-listsp`
and `fn-tcl-lists-len` over every octet staged so far.

**The mechanism, because the spec had it wrong.** `specs/tcpcl.md` §3 claimed
"no recognizer runs over retained input on the served path (`fn-tcl-drive`'s
`mbe` check is `:exec nil`)". The `mbe` was indeed free. The *guard* was not:
the native host reaches the machine through `fnn-call`
([host/native/io.lisp:11-18](../../host/native/io.lisp)), which applies the
ACL2 executable counterpart of a host wrapper, and an executable counterpart
checks its callee's guard on every call. One socket chunk, one walk of the
staged prefix: O(n^2/chunk) for a transfer of n octets. The claim is walked
back in the same commit.

**The fix.** `fn-tcl-session-cheapp` is `fn-tcl-sessionp` with the two staged
conjuncts removed — record shapes and carried scalars only, cost independent
of the transfer. It is now the guard of every executable entry point
(`fn-tcl-drive`, `-step`, `-decode-for`, `-recv-segment`, `-recv-ack`,
`-recv-refuse`, `-pump`, `-send`, `-tick`) and the `:logic` side of
`fn-tcl-drive`'s totality `mbe`. `fn-tcl-lists-len` and `fn-tcl-concat-rev`
became guard-total (the latter over `fn-tcl-app`, which is `append`) so that
no caller must establish the walk in order to measure or concatenate.

- **No keystone statement changed.** C1–C4 and every `-preserves-sessionp`
  lemma still hypothesise `fn-tcl-sessionp`; `fn-tcl-sessionp-is-cheap`
  (and `fn-tcl-inboundp-is-cheap`) connect the two, so a keystone and a guard
  name the same function. The staged equation is still carried, still
  preserved, and still what C2 and
  `fn-tcl-received-len-is-staged-length-by-definition` rest on.
- **The carried invariant is proved preserved per transition**, which is what
  makes the cheap guard sound to rely on: `fn-tcl-initial-session-is-cheap`
  establishes it once, then `fn-tcl-next-`, `-with-outbound-`, `-touch-rx-`,
  `-settle-`, `-open-`, `-recv-contact-`, `-recv-init-`, `-refuse-`,
  `-complete-`, `-stage-`, `-broken-stream-`, `-recv-segment-`, `-unexpected-`,
  `-recv-ack-`, `-recv-refuse-`, `-recv-term-`, `-terminate-`, `-tcp-closed-`,
  `-input-error-`, `-pump-`, `-send-`, `-tick-`, `-step-` and
  `-drive-preserves-cheapp`.
- **The two recognizers are written out, not layered.** Deliberate: no proof
  or hint in `tcpcl-session` or `tcpcl-invariants` has to open one to reach the
  other, and `fn-tcl-sessionp-is-cheap` fails if they drift.
- **Still open, with the exact obligation**: the *outbound* suffix. See
  `specs/tcpcl.md` §6 — `fn-tcl-outboundp` measures `remaining`, so a send is
  still quadratic, and closing it needs guard-total `fn-tcl-take`/`fn-tcl-drop`
  or a carried `(len remaining)`. Named, not attempted.

`tools/tcpcl_lab.py` gains a sixth scenario, `profile`: the same transfer at
64 KiB and 256 KiB, and the verdict is the *ratio* (a quadratic guard gives
about 16x for a 4x transfer; the bar is 8x), so a loaded box moves both
measurements together. `tools/twonode_gate.py`'s `tcpcl` scenario runs it.

## 2. What did not land, and what it needs

**The BP node over TCPCL did not land.** Saying why precisely, because the
gap is not where the brief assumed:

- `books/bp-node.lisp` does not exist. `fn-bpn-receive`, `fn-bpn-step` and the
  FNBS record family are [specs/bp-design.md](../../specs/bp-design.md) §1.3–1.5
  — a design with exact statements, explicitly "not a claim". So is
  `books/bp-bundle.lisp` (§1.4): **nothing in this tree encodes or decodes a
  BPv7 bundle**, only its primary block (`books/bp-primary-cbor`). The
  convergence layer therefore carries opaque octets, and `:bundle-received`
  is a file in a spool directory, not a bundle record.
- The receiver entry that does exist is `host/bp-receipt-host.lisp`
  (`fn-bpr-host-accept`, `-prepare-receipt`, `-commit-receipt`,
  `-receipt-adu`) over `books/bp-receipt`, and it is driven today by
  `tools/run_bp_receive.py` with an FNRJ journal — Python, not the image.
  Wiring it into the image means the receiver state and its journal move into
  the native host, which is the packet `host/bp-receive-host.lisp` +
  `tools/receipt_journal.py` currently stand in for.
- `books/scheduler`, `books/bp-release` and `books/relay` are certified and
  have the keystones the brief wants cited, but none of them is in the image's
  build list ([host/native/build.lisp](../../host/native/build.lisp)).

So `bp send` / `bp receive` / `bp status` are not verbs on the image. Adding
them honestly is three packets, in this order: (a) `books/bp-bundle` per
bp-design §1.4, so that a transfer's octets are a bundle and not a blob;
(b) the FNBS record family in `books/frame` and the receiver state in the
image; (c) the scheduler's contact window as the gate on `fn-tcl-host-send`.
Doing (c) alone — a contact check around the existing `tcpcl send` — would
have been a verb that looks like a BP node and is not one.

## 3. Evidence

See `planning/evidence/`. Headline: recorded in that file, not here.

## 4. dtn7 interop

dtn7-rs is built on hbox at `/tank/fn/dtn7/repo`, pinned to
`4daf02d7ea927e9293753b2a5c4497457f6e5a40` (= `tests/bp-dtn7/pin.json`),
`cargo build --release --locked`, `dtnd --version` = `dtn7-rs 0.21.0`. Its
`tcp` convergence layer is RFC 9174 (`core/dtn7/src/cla/tcp/proto.rs` has the
Table 2 message types and the CAN_TLS contact flag), so a session-level
exchange with fn is meaningful even though fn cannot yet author a BPv7
bundle. The shape of an honest one-each-way test, given that: let **dtn7**
author the bundle, have fn receive and acknowledge it, then have fn send the
same octets back — fn as a convergence-layer peer carrying a bundle it did
not write. What actually ran is in the evidence record.
