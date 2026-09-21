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

## 3. Evidence: the image builds and the layer runs

[`planning/evidence/tcpcl-dtn-w9-2026-09-20.md`](../evidence/tcpcl-dtn-w9-2026-09-20.md).
w8's record had to say "the image did not build, so none of the five
scenarios ran". On hbox, under `swarm-build`:

- `books/tcpcl-session` certifies with this change in **156.17 s**.
- **`build/fn-host-dtn` builds** — `host/native/build-dtn.lisp`, the DTN-only
  variant of the build list (no `books/served`, no `books/nntp-effects`, no
  reader or model verb), with `tools/build_native_host.sh` now taking
  `FN_NATIVE_BUILD` / `FN_NATIVE_IMAGE` / `FN_NATIVE_LOG`. Not the deployment
  image, and every claim below is bounded by that. The first attempt failed
  correctly on `Uncertified` markers for the anchor books, which no submit
  list had covered.
- **`tools/tcpcl_lab.py` is 6/6**: a bundle each way with contact, SESS_INIT,
  two segments and two acks in each direction and a clean SESS_TERM; an MRU
  refusal with nothing staged and exit 1; keepalives; `kill -9` of the
  receiver mid-transfer with the interrupted transfer absent, no partial
  name left, the acknowledged transfer durable and a reconnect landing a new
  one; the model differential; and `profile`.
- **`profile` is the measurement of §1**: 64 KiB in 0.115 s, 256 KiB in
  0.212 s, ratio **1.84 for a 4x transfer**. A quadratic guard gives about
  16x. The residue below 4x is process startup, paid once by each.
- **A receipt round trip is not among these.** `exchange`'s reverse leg is a
  second bundle, not a receipt. Section 2 says what a receipt needs.

**A finding the first run produced.** `replay` failed at
`'(:OUTBOUND-SENT 0 "passive")' != '(:SEND :MSG-REJECT 3)'`. `tcpcl replay`
folds `fn-tcl-drive` and calls nothing else, so it models a node that never
originates a transfer; a node that also sends reaches `fn-tcl-send` from the
host, not the wire, and the replay has no outbound when the ack arrives. The
machine was right; `exchange`'s trace — from a listener carrying a reply
bundle — was never a valid subject. `scenario_replay` now drives its own
receive-only listener and the differential holds exactly. Extending it to a
sending node means putting the host's aux calls in the trace: open.

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
not write.

**That ran, and it works.** `tests/bp-dtn7/run_fn_tcpcl_interop.py`, one
bundle each way, `ok: true`. dtn7 dialled fn; fn negotiated a 64,000-octet
segment and transfer MTU with TLS false, acknowledged the transfer and staged
126 octets. fn then dialled dtn7 with the same octets; dtn7 accepted the
XFER_SEGMENT, decoded them as BPv7, recognised the bundle as its own and
dispatched it. fn's `:INBOUND-REFUSED 1 6` on the last line is correct:
dtn7's epidemic router tried to forward the bundle straight back and fn had
already sent SESS_TERM, so the machine refused with Table 6 reason 6. Every
reply on both sides is in the evidence record. What it does not show is fn
*originating* a bundle — see the paragraph above; that boundary is the whole
reason the harness is shaped this way.

## 5. Where this stops, and the two commands that finish it

**`books/tcpcl-invariants` has no verdict against the new `books/tcpcl-session`.**
C1 to C4 are unchanged in statement and `books/tcpcl-session` certifies, but
the invariants book was still queued for an ACL2 slot on a box carrying six
lanes when this lane's budget ran out. It is recorded open, not passed. The
one risk it carries is narrow and named: `fn-tcl-drive`'s totality `mbe` now
tests `fn-tcl-session-cheapp`, so a proof there that opens `fn-tcl-drive` and
splits on that test needs `fn-tcl-sessionp-is-cheap`, which is exported
enabled and should close it without an edit.

```sh
ssh hbox 'cd /tank/fn/lanes/w9-dtn-e2e && FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
  FN_CERT_CACHE=/tank/fn/certcache FN_ACL2_TIMEOUT_SECONDS=3600 \
  swarm-build python3 tools/certify_books.py --jobs 2 \
  books/tcpcl-invariants tests/acl2/tcpcl-tests'
```

Its sibling, once `books/served` and `books/nntp-effects` are certified in
that directory, is the *deployment* image and the same lab against it — which
is also what makes `tools/twonode_gate.py`'s `tcpcl` scenario run for real
rather than skip:

```sh
ssh hbox 'cd /tank/fn/lanes/w9-dtn-e2e && FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
  swarm-build sh tools/build_native_host.sh \
  && swarm-build python3 tools/tcpcl_lab.py --image build/fn-host --work build/lab-full'
```

After that, §2's three packets, in that order. The one thing not to do is add
a `bp send` verb that wraps `tcpcl send` in a contact check: it would look
like a BP node and would not be one.

## 6. The regression I merged, every measurement, and the checkpoint

`books/tcpcl-invariants` went from certifying to timing out because of this
lane, and I merged it to dev before it had a verdict. The cause, the four
configurations measured, and where it stands.

### The root cause, in one sentence

`fn-tcl-drive`'s totality test used to be the literal `(fn-tcl-sessionp s)`,
which a theorem carrying that hypothesis decided by assumption at no cost;
making it `(fn-tcl-session-cheapp s)` put a *second* whole-state recognizer,
with a *second* family of rules over it, into a book
(`books/tcpcl-invariants`) that enables `fn-tcl-session-vocabulary` wholesale.

### Two diagnostics worth more than the certificate

1. **A `Time:` line with near-zero `prove` and large `other` is not the
   rewriter.** C1 measured `Time: 2386.26 seconds (prove: 0.02, print: 0.00,
   other: 2386.24)`, twice, on two different configurations. That is forward
   chaining or type reasoning running to fixpoint, not proof search, and the
   cure is a **theory change, not a hint**. I lost most of a lane reasoning
   about hints and case splits because I read the subgoal count and not that
   line. No other lane has this written down.
2. **Exporting a second forward-chaining family over a second whole-state
   recognizer costs a fixpoint pass per goal carrying either recognizer's
   term** — and once `fn-tcl-drive`'s test names the new one, that is every
   goal that opens `fn-tcl-drive`. The profile is exact:
   `FN-TCL-SESSION-CHEAPP-FACTS` **79,623 tries / 147,539 frames (ratio
   1.85)**, beside the pre-existing `FN-TCL-SESSIONP-FACTS` at **76,473
   tries**. The new family does not add work; it *doubles* it. The note is at
   the `deftheory` in `books/tcpcl-session.lisp`.

### Every configuration, with its step limit stated

| # | Configuration | Step limit | Result |
| --- | --- | --- | --- |
| 0 | as merged at `ca13c56`: cheap recognizer in the vocabulary, nothing closed | none, 3600 s cap | `fn-tcl-drive-is-a-result`: `Splitter note ... (8844 subgoals)`, book times out, 3600.175 s (`certify-20260920T182111Z-1037731`) |
| A | + `fn-tcl-session-cheapp` closed in `tcpcl-invariants` (`7517296`, **this is what dev carries**) | none, 3600 s cap | that theorem passes; book reaches C1 and times out there, 3600.175 s (`certify-20260920T193233Z-1118110`); closure all green (`tcpcl-octets` 104.8 s, `tcpcl-session` 64.2 s) |
| — | A again under `ld` | **3,000,000 steps** | **measures nothing** — aborted a theorem the certify had already passed. Recorded because I reported a finding from it and had to retract it. |
| B | bridge as `(:rewrite :forward-chaining)` | 3,000,000 steps | **measures nothing**, same abort. Retracted; and the profile later showed it pointed the wrong way, since it *adds* to the family that was the cost. |
| A′ | A + the preservation chain alone put aside | none, 2700 s cap | C1 still open: `Time: 2688.15 seconds (prove: 0.02, print: 0.00, other: 2688.13)`. The preservation lemmas were the wrong half. |
| C | the **whole** cheap rule set — facts, forward-chaining fields, preservation — under `fn-tcl-cheap-rules`, closed in `tcpcl-invariants`; bridge stays a plain rewrite | none, 3600 s cap | **did not close.** C1 times out again, 3600.173 s (`certify-20260920T220703Z-1235733`); `books/tcpcl-session` 64.7 s green, `tests/acl2/tcpcl-tests` unattempted behind it |

The profile that chose C: `python3 tools/proof_profile.py books/tcpcl-invariants
fn-tcl-drive-partition-independence --host hbox --steps 40000000 --timeout 2400`
(the profiler is only correct from dev `f730c24` onward — before that it ran
the driver at the tree root, every `include-book` failed, and it profiled an
empty world while reporting success).

### The checkpoint, if C did not close it

The tree carries configuration C. `books/tcpcl-session` certifies in every
configuration measured; only `books/tcpcl-invariants` is at issue, and
`tests/acl2/tcpcl-tests` is unattempted behind it (certify-book stops at the
first failure). Nothing in §1 to §5 depends on it: the image, the 6/6 lab,
the profile and the dtn7 interop all stand on `books/tcpcl-session`.

Three honest ways out, in the order I would try them:

1. **Finish the theory work.** The profile's top runes after the cheap family
   are all pre-existing and all from line 32 enabling the vocabulary
   wholesale: `FN-TCL-STEP` (481,747 frames / 81 tries), `FN-TCL-RECV-SEGMENT`
   (213,787 / 19), `FN-TCL-RECV-INIT` (182,438 / 19), `FN-TCL-BROKEN-STREAM`
   (130,858 / 57). C1's hint closes `fn-tcl-step` and four others by name; the
   rest of the transitions are open. Closing them is the same move that fixed
   the cheap family and would likely pay for itself independently of this lane.
2. **Revert the totality test only.** Keep the cheap **guard** — which is
   where the measured win is, §3's `profile` scenario — and give `fn-tcl-drive`
   back its `fn-tcl-sessionp` `:logic` test. This does **not** work as written
   (the `mbe`'s `:exec nil` needs the guard to imply the `:logic` branch is
   false, and the cheap guard does not imply `fn-tcl-sessionp`), so it means
   either guard-total `take`/`drop` or an explicit equating theorem between a
   `fn-tcl-drive` the host calls and the one the keystones name — the pattern
   AGENTS.md blesses, and a packet, not an edit.
3. **Revert this lane's `books/tcpcl-session` change on dev** and re-land the
   guard fix in a fresh lane together with the C1 theory work. Dev is green
   again immediately and the measurements above survive in this record. If C
   did not close, this is what I would recommend, and it is root's call.

What must not happen is weakening C1.

## 7. What this lane did about it: reverted, and why the two must land together

C did not close, so option 3 was taken. **This lane's `books/tcpcl-session`
and `books/tcpcl-invariants` changes are reverted on dev** to their state at
`698ab55` — which keeps the `deftransition` refactor that landed between this
lane's base and its merge, since only this lane's commits touched those two
files after it. Dev is green again and no other lane pays for this.

**The guard fix and the C1 theory work are one packet, not two.** That is the
real lesson, and it is why re-landing the guard change alone would repeat
this exactly. `fn-tcl-drive`'s totality test is reachable from every keystone
in `books/tcpcl-invariants`, and that book enables `fn-tcl-session-vocabulary`
wholesale; so any change that puts a *new* recognizer into that test changes
the theory every C1-to-C4 proof runs in. Closing the new family (C) was
necessary and not sufficient, because the profile's next four runes are
`FN-TCL-STEP` (481,747 frames / 81 tries), `FN-TCL-RECV-SEGMENT` (213,787 /
19), `FN-TCL-RECV-INIT` (182,438 / 19) and `FN-TCL-BROKEN-STREAM` (130,858 /
57) — all transitions left open by that wholesale enable, all pre-existing,
and all of which the cheap test now drags into goals that never saw them.
The packet is: close those transitions in `tcpcl-invariants` (C1's hint
already closes `fn-tcl-step` and four others by name, so the pattern is
established), *then* make the guard cheap, and certify the two books
together before merging either.

**What survives the revert, and what does not.** The measurements in §3 and
§4 were taken against an image built from the cheap-guard book, which is no
longer on dev — they are evidence about a configuration this record
preserves, not about dev's current tree. Everything else stands unchanged and
is independent of the guard: the image builds, the lab is 6/6, the replay
differential finding, and the dtn7 interop. The O(n^2/chunk) served-path cost
w8 found is therefore **still open on dev**, with its cause understood, its
cure measured, and the reason it could not land alone written down here.

The reverted books are measured green, not assumed: `books/tcpcl-session`
25.259 s, `books/tcpcl-invariants` 609.687 s, `tests/acl2/tcpcl-tests`
0.312 s, all exit 0 on hbox with no step limit
(`certify-20260920T230902Z-1283742`). The 609.687 s also dates the "about
672 s" baseline this lane kept quoting from another box.
