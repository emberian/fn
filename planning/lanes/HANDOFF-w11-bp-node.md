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

## 3. Per-root table

(filled below)

## 4. Packet 2

(filled below)
