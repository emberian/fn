# Handoff: w11/bp-node — the projections closed, and what that unblocked

Branch `w11/bp-node`, worktree `build/lanes/w11-bp-node`, from `dev` at
`dbf1aa7` and merged forward to `bdf40d0` (the merge touches no book in this
cluster's closure: `books/nntp-post`, `books/owner`, `books/owner-invariants`
only). Box **hbox** throughout — `/tank/fn/lanes/w11-bp-node`, ACL2
`/tank/fn/acl2-8.7/saved_acl2`, cache `/tank/fn/certcache`, every run under
`swarm-build`. Two `ld` probes on the laptop, 1.6 s and 2.5 s.

## 1. Packet 1 — the six projections of `books/bp-primary`, withdrawn

The `enabled_projection` lint named six definition runes in that book:
`fn-bpp-flags` (`:394`), `fn-bpp-crc-type` (`:395`), `fn-bpp-source` (`:397`),
`fn-bpp-creation-time` (`:399`), `fn-bpp-sequence` (`:400`) and
`fn-bpp-result-block` (`:599`). They are now withdrawn at the end of the book
under `fn-bpp-projection-vocabulary`, beside `fn-bpp-identity-vocabulary`, and
`make check`'s warning total falls 236 → 230 with exactly those six gone.

**It was not a one-liner, and the three things it needed are the interesting
part.**

### 1.1 The accessor-of-constructor laws, stated over the cons nest

`fn-bpp-make-block` and `fn-bpp-ok` stay ENABLED — withdrawing the
constructor as well would oblige the book to export the tag, the length, the
`true-listp` and the five projections it still leaves enabled as rules of
their own, which is the opaque-record refactor (item 4 of
`planning/deputies/bp.md`) and not this lane's. With the constructor enabled
ACL2 rewrites inside out, so **a caller's goal never contains
`(fn-bpp-flags (fn-bpp-make-block ...))`**: by the time the accessor is
reached its argument is already the cons nest. Measured on
`fn-bpn-send-bundle-is-a-bundle` (K5 of `books/bp-node`), whose checkpoint was
`(INTEGERP (FN-BPP-FLAGS (LIST* :FN-BP-PRIMARY 0 0 PEER ...)))`.

So the five laws are stated over the nest:

```lisp
(defthm fn-bpp-flags-of-a-built-block
  (equal (fn-bpp-flags (cons tag (cons flags rest))) flags))
```

and the four deeper ones for `crc-type`, `source`, `creation-time` and
`sequence`, plus `fn-bpp-result-block-of-a-built-result`. Each needs an
EXPLICIT cons, so none can fire on a block that arrived from a decoder —
which is exactly what withdrawing the definition is for.

### 1.2 `books/bp-primary-invariants` opens them, in one local line

That book is the REPRESENTATION book for the primary block: both directions
of the codec take a block apart field by field and rebuild it, so a goal
there mixes `(fn-bpp-flags b)` with `(nth 8 b)` and the elementwise
comparison leaves `(equal (fn-bpp-flags b) (nth 1 b))` with nothing to close
it. Measured: with the projections closed and no such line,
`fn-bpp-value-block-of-block-value` fails at `Subgoal 106.104.53` on exactly
that literal. The cure is the idiom the book already uses twice (for
`fn-cbor-*-vocabulary` and `fn-bpp-identity-vocabulary`):
`(local (in-theory (enable fn-bpp-projection-vocabulary)))`.

**This costs the books above nothing.** ACL2 stores a theorem as written, so
every statement the book EXPORTS is still in projection vocabulary and
`books/bp-bundle`, `books/bp-node` and the rest see the projections closed.

### 1.3 The bridge in `books/bp-node` had to stop being a rewrite

Closing the accessor moved the guard obligation from `(integerp (nth 1 p))`
into `(integerp (fn-bpp-flags p))` — and **it still failed**, with the fact
"available" the whole time. `fn-bpn-decoded-primary-flags-are-a-flag-set` was
`:rule-classes (:rewrite (:forward-chaining ...))` with conclusion
`(fn-bpp-flag-setp (fn-bpp-flags p))`: the forward-chained literal is the
rule's own left-hand side, so the rewriter collapses it to `T` as it enters
the context and nothing is added. This is the BRIEF's rule about a local
`defthm` concluding a recognizer call, one layer further in — the collapse
happens to a FORWARD-CHAINED literal, not to a `:use` hypothesis, and there
is no `:rule-classes nil` escape because forward chaining is the only class
that can put a fact about a term the conclusion does not contain into the
context.

The replacement, `fn-bpn-decoded-primary-flag-test-is-guarded`, concludes
`true-listp` and arithmetic — exactly `fn-bpp-flags`'s guard and
`fn-bpp-fragmentp`'s — and carries **no rewrite class at all**.

## 2. Every theorem the closure touched, with a verdict

| where | form | verdict |
| --- | --- | --- |
| `books/bp-primary-invariants:173` | `fn-bpp-value-block-of-block-value` | the only form that FAILED; cured by the one local `in-theory` of §1.2, statement unchanged |
| `:178` `fn-bpp-value-crc-field-of-block-value`, `:186` `fn-bpp-block-crc-width` | `fn-bpp-crc-type` | unchanged |
| `:259` `fn-bpp-accepted-input-is-canonical-by-construction`, `:268` `fn-bpp-decode-yields-block`, `:278` `fn-bpp-accepted-block-has-valid-crc` | `fn-bpp-result-block` (and `fn-bpp-crc-type`) | unchanged |
| `:336` `fn-bpp-adu-key-separates-source-and-timestamp-by-definition`, `:350`/`:358` the two `fn-bpp-bundle-id-*-by-definition`, `:367` `fn-bpp-anonymous-source-is-not-identifiable-by-definition` | `fn-bpp-flags`, `-source`, `-creation-time`, `-sequence` | unchanged |
| `:456` `fn-bpp-primary-identity-ignores-destination-lifetime-and-crc-type-by-definition`, `:507` `fn-bpp-primary-identity-determines-adu-key` | four projections | unchanged |
| `books/bp-fragment:369` `fn-bpf-fragment-block`, `:390` `fn-bpf-fragmentablep` | five projections in the bodies | unchanged; book certifies in 0.33 s |
| `books/bp-fragment-invariants:442` `fn-bpf-fragment-block-sets-the-fragment-flag`, `:449` `fn-bpf-fragment-block-is-a-block`, `:458` `fn-bpf-anonymous-conformant-bundle-is-not-fragmentable` | `fn-bpp-flags` | unchanged; carried by the §1.1 laws. Book certifies in 15.5 s |
| `books/bp-bundle:565` `fn-bpb-scan-primary`, `:581` `fn-bpb-scan-primary-yields-a-block` | `fn-bpp-result-block` | unchanged; the theorem already disabled the accessor in its own hint |
| `books/bp-node:244` `fn-bpn-expiry` | `fn-bpp-creation-time` | unchanged |
| `books/bp-node:366` `fn-bpn-receive` | `fn-bpp-flags` | the guard needed the bridge of §1.3 restated; the definition and the guard statement are unchanged |
| `books/bp-node` K5 `fn-bpn-send-bundle-is-a-bundle` | `fn-bpp-flags` etc. on a CONSTRUCTED block | carried by the §1.1 laws; hint unchanged |
| `tests/acl2/bp-primary-tests`, `bp-fragment-tests`, `bp-node-tests` | `assert-event`s | unaffected in principle (they evaluate, and a theory does not change an executable counterpart) and unchanged in fact |
| `host/bp-ingress-host.lisp:142`, `:175` | `fn-bpp-result-block`, `-source`, `-creation-time`, `-sequence` | **unaffected**: the file is `ld`'d by `tools/run_bp_ingress.py` and `tools/bundle_bridge.py`, contains no `defthm`, and is not a Makefile root — it evaluates the projections |

## 2a. The three things packet 1 did NOT predict

`certify-book` stops at the first failure, so "everything else in
`books/bp-node` closes" had never been a statement about anything after
`fn-bpn-receive`. Three forms behind it had never been attempted, and each
was a distinct defect.

**K5 had to move in front of K1.** K1 is the round trip and its only route
from `fn-bpb-decode` to `fn-bpb-encode` is `fn-bpb-decode-of-encode`, whose
first hypothesis is exactly K5. With K1 first the form does not fail, it
RUNS: twenty-five minutes on hbox with no checkpoint, because the rewriter
cannot relieve that hypothesis and falls back on induction over an encoder.

**K5 itself wanted the clock OPEN and the CBOR encoder CLOSED.** Closed, it
stops at `Subgoal 12.5`, `(INTEGERP (FN-CLOCK-WALL OBS))`, with
`(FN-CLOCK-OBSERVATIONP OBS)` sitting unopened in its own hypotheses. Open,
`fn-bpc-enc` unfolds the extension blocks' data and the goal becomes
`(FN-CBOR-OCTET-LISTP (CONS 130 (APPEND (FN-CBOR-ENCODE-ARGUMENT 0 ...)
'(0))))`, which neither `fn-bpc-enc-are-octets` nor `fn-bpc-enc-length-bound`
matches any more — and both are in `fn-bpc-vocabulary` and both ship
DISABLED, so they have to be named.

**K1 needed the receiver's transfer limit as a case split.** Nothing in K1's
statement bounds the authored bundle against the RECEIVER's limit, which is
`fn-bpb-decode-of-encode`'s second hypothesis; a node configured for a
16-octet transfer refuses this very bundle and
`tests/acl2/bp-node-tests.lisp` has that witness. The theorem is true only
because the acceptance hypothesis rules that branch out, and the split is
how the prover gets to use it: above the limit
`fn-bpb-decode-refuses-overlong-input` makes the decode `:limit`, the
outcome a refusal, and the hypothesis false.

**And then the theory, which was the whole of the remaining cost.** K1's
`Time:` line read `427.20 seconds (prove: 0.43, other: 426.77)` and
`fn-bpn-receive-yields-one-of-three`'s read `371.16 (prove: 0.00, other:
371.16)` — no proof search at all, forward chaining and type reasoning over
a decoded bundle neither statement looks inside (`docs/proof-style.md` §9.1:
that shape is cured by a theory change and never by a hint). The three local
bridges exist for ONE obligation, `fn-bpn-receive`'s guard, and two of them
are forward-chaining rules triggered on
`(fn-bpb-bundle-primary (fn-cbor-result-value (fn-bpb-decode octets limit)))`
— a term every keystone below is full of. Closed once, in the book, together
with `fn-bpb-decode-yields-bundle`: **K1 then closes in 0.01 s and 2,339
prover steps.**

## 3. Per-root table

| root | verdict | run / evidence | note |
| --- | --- | --- | --- |
| `books/bp-primary` | CERTIFIED | hbox `run-20260921T005707Z-8672` / `certify-20260921T005711Z-1363238` | 5.5 s; the six projections withdrawn, six accessor-of-constructor laws added |
| `books/bp-primary-invariants` | CERTIFIED | same run | the one local `in-theory` of §1.2 |
| `books/bp-primary-cbor`, `books/cbor`, `books/cbor-invariants`, `books/clock`, `books/defrecord` | CERTIFIED | same run | unchanged, re-certified against the changed book |
| `books/bp-fragment`, `books/bp-fragment-invariants`, `tests/acl2/bp-fragment-tests` | CERTIFIED | same run | 0.33 s, 15.5 s, 10.2 s; no edit needed |
| `books/bp-bundle`, `books/bp-bundle-invariants` | CERTIFIED | same run | no edit needed |
| `tests/acl2/bp-primary-tests` | CERTIFIED | same run | no edit needed |
| the DTN image's 60-book closure | 59 of 60 CERTIFIED | hbox `run-20260921T015051Z-6596` / `certify-20260921T015101Z-1417898` | 652.0 s at `--jobs 8`; `books/bp-node` the only gap at that point |
| **`books/bp-node`** | **CERTIFIED, first time ever** | hbox `run-20260921T021131Z-1eb0` / `certify-20260921T021134Z-1437596` | **1.083 s** |
| **`tests/acl2/bp-node-tests`** | **CERTIFIED, first time ever** | same run | 0.759 s |
| `tests/acl2/bp-bundle-tests` | CERTIFIED with the dtn7-rs vector | hbox `run-20260921T021823Z-8f90` / `certify-20260921T021827Z-1443510` | 0.743 s, 68 assert-events |
| `build/fn-host-dtn` | **BUILT** | hbox, `build/native-host-build-dtn.log` | 272,527,376-octet core |
| `tools/tcpcl_lab.py --scenario adu` | **PASSED** | §4 | 1500-octet ADU into a 1589-octet bundle, both ways |
| `tests/bp-dtn7/run_fn_bp_interop.py` | **PASSED, `ok: true`** | [the evidence record](../evidence/bp-dtn7-w11-2026-09-21.md) | one bundle authored each way |

## 4. Packet 2 — the run, and which side authored what

**The standing caveat is retired.** Until tonight fn exchanged a bundle with
dtn7-rs over RFC 9174 and **dtn7 authored it in both directions**, because
nothing in the tree encoded BPv7.

- **Leg 1, dtn7-rs 0.21.0 AUTHORED**: 132 octets for `dtn://fn-b/incoming`
  from `dtn://dtn7x/`. fn decoded them with `fn-bpn-receive` —
  `BP accepted xfer=1 adu=32` — and the ADU equals the file `dtnsend` was
  given. sha256 `3ba1d435…3616df`.
- **Leg 2, FN AUTHORED**: `BP authored creation=843272138572 sequence=1
  lifetime=3600000 payload=33 octets=138`. dtn7-rs decoded it, delivered the
  ADU to its `incoming` endpoint, and `dtnrecv` printed it back. sha256
  `f6688bde…9b11b7`.

Both wire images are in `tests/bp-dtn7/golden/` with the run and the
revision that produced them. `host/native/bp.lisp` journals them itself —
inbound under `.wire` BEFORE the node decides anything, outbound before the
bundle reaches a socket — so neither is a re-derivation after the fact.

**And the obligation `w11/phantom-cites` recorded is met.** The
dtn7-authored 132 octets are inlined in `tests/acl2/bp-bundle-tests.lisp` as
`*bpb-dtn7-0-21-0*`, and the book asserts three separable things: that fn's
decoder accepts them; that the fields recovered are the ones dtn7-rs sent,
so fn agrees about what they MEAN; and that **`fn-bpb-encode` reproduces
them byte for byte**, so the deterministic spelling fn insists on is the
spelling dtn7-rs emits. The header now describes what is there and keeps the
history of what was not.

## 5. The phantom deliverables in `specs/bp-design.md` §5

`w11/phantom-cites` named three for this cluster, and none of them exists.

`specs/bp-bundle.md` **does not exist** and should not: §1.4 of
`specs/bp-design.md` is the bundle frame, and §1.4.1 and §1.4.2 are its
status.

`specs/bp-node.md` **does not exist** and should not either: §1.5 of the
same document is the processing machine, and §1.5.1 is its status.

`books/bp-node-records` **does not exist** because packet 1 has not been
started; it is an unbuilt deliverable rather than a misnamed one, and the
FNBS record family it names is item 2 of §6 below.

§5 of the spec now says all three in the table's own preamble, rather than
leaving names that resolve to nothing.

## 6. What the next lane should take

1. **A dtn7-rs capture WITH a CRC.** The bundle dtn7-rs authored carries no
   CRC at all (type 0), so `specs/bp-design.md` §1.4.1's open point — no
   foreign vector pins the canonical-block CRC — survives this lane. dtn7-rs
   can be configured to write one; one more capture closes it.
2. **The FNBS record family and the `(:bpn-sequence n)` frontier**
   (§1.3). `bp send` still takes the sequence as an argument and says in its
   own header that a restarted operator must not reuse one. This is the one
   open item that changes a claim rather than adding a feature.
3. **`fn-bpn-step`**, without which T1 to T6 of §1.6 have no subject. §1.5.1
   lists what is absent; nothing in the tree claims those theorems.
4. **The five other projections of `books/bp-primary`** (`-destination`,
   `-report-to`, `-lifetime`, `-fragment-offset`, `-total-adu-length`) and
   `fn-bpp-make-block` itself, in one step, which is the opaque-record
   refactor (item 4 of `planning/deputies/bp.md`). Doing it piecemeal only
   moves the problem; this lane closed exactly the six the lint names.
