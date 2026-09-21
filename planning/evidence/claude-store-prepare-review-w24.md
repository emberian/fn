# Independent review: store prepare path (w24)

Claude Opus 5, worktree `build/lanes/w13-claude-review`, detached at
**`058aadef`**. One pass, source inspection only; nothing here is observed
behaviour. No edits, no commits.

Scope: the host-called prepare — `fnn-bridge-prepare`
(`host/native/io.lisp:684-687`) → `fn-store-sn-prepare`
(`host/store-node-host.lisp:379-418`) → `fn-spc-prepare`
(`books/store-prepare-correspondence.lisp`) — and the correspondence claim the
wrapper's comment makes at `host/store-node-host.lisp:409-414`.

## No findings

I checked the claim that comment makes, which is the one that matters here:
that the function the host actually calls is the specification, on every state
the host can reach. It holds, and the hypothesis is discharged where the host
needs it. Specifically:

**Subject.** The host calls `fn-spc-prepare` at
`host/store-node-host.lisp:414`, and the keystone
`fn-spc-prepare-equals-specification-under-relation`
(`books/store-prepare-correspondence.lisp:134-137`) is about that function, not
a sibling: `(implies (fn-snt-relation s) (equal (fn-spc-prepare s record)
(fn-sn-prepare s record)))`.

**Establishment at the host's real entry.**
`fn-spc-observed-open-run-maintains-relation` (`:279-286`) has subject
`(fn-sn-open-state (fn-sn-open-observed groups capacity frontier records))`
under hypothesis `(fn-sn-open-okp (fn-sn-open-observed ...))`. That is
syntactically the state `fn-store-sn-recover` installs at
`host/store-node-host.lisp:85-86`, under the same `fn-sn-open-okp` guard it
tests at `:82`. The other root, `fn-store-sn-reset` (`:27`), is covered by
`fn-spc-reset-establishes-relation` (`:273`).

**Preservation across everything the host can do between open and prepare.**
I enumerated every wrapper that writes the live global — `fn-store-sn-reset`
(`:27`), `-recover` (`:85`), `-io` (`:376`), `-prepare` (`:417`),
`-refuse-reservation` (`:431`), `-known-abort` (`:446`), `-finish` (`:470`) —
and matched them against `fn-spc-step` (`correspondence:220-229`), which
dispatches `:prepare`, `:io`, `:finish`, `:refuse-reservation`,
`:known-abort`, `:set-keyring`, `:sweep-staging`. The two I expected to be
missing, `refuse-reservation` and `known-abort`, are present and are used by
name in the proof of `fn-spc-step-preserves-relation` (`:244-260`, via
`fn-sn-refuse-reservation-preserves-relation` and
`fn-sn-known-abort-preserves-relation`). `fn-spc-run-preserves-relation`
(`:264`) lifts that to any finite sequence. Crash and recover are covered on
the other side at `books/store-node-traces.lisp:459` and `:474`.

So the reachable-scenario I was looking for — a prepare whose relation
hypothesis is not discharged because some earlier host mutation is unmodelled —
does not exist at this revision. In particular the sequence I considered
most likely (`fnn-command-post` refuses at `io.lisp:1563-1566`, consumes the
reservation through `fnn-bridge-refuse-reservation`, and a later prepare runs
on that state) is covered by the `:refuse-reservation` clause.

## One latent gap, explicitly unconfirmed as a defect

`fn-spc-step`'s `(otherwise s)` (`correspondence:229`) makes
`fn-spc-step-preserves-relation` and `fn-spc-run-preserves-relation` vacuously
true for any event outside the case list. The theorems' coverage of "any finite
sequence of actual live mutators" therefore rests entirely on that case list
matching the set of `f-put-global 'fn-store-sn` wrappers in
`host/store-node-host.lisp`. I checked by hand that it does today.

Nothing enforces the correspondence. A new wrapper that writes the global
without a matching `fn-spc-step` clause would be modelled as the identity, the
two preservation theorems would still certify unchanged, and the keystone's
hypothesis would be silently undischarged for every prepare after that wrapper
runs.

This is a property of how the coverage is expressed, not a defect at
`058aadef`: **no such wrapper exists**, and I am not claiming a reachable
failure. If it is worth closing, the cheap form is a static check that the set
of `f-put-global 'fn-store-sn` sites in the host file equals the `fn-spc-step`
case list plus the two roots — the same shape as the existing host lints, and
it needs no new theorem.

## Noted while reading, not findings

* `fn-store-sn-prepare` can return `:duplicate` or `:conflict` from
  `fn-store-article-match` (`host/store-node-host.lisp:398-400`), even though
  `fnn-command-post` already screened both at `io.lisp:1553-1557` via
  `fnn-bridge-existing-action`. The late return is handled correctly: it is not
  `:prepared`, so `io.lisp:1563-1567` fences, consumes the reservation and
  refuses with exit 1, which is the right outcome for a duplicate found at
  prepare.
* `fn-store-sn-refuse-reservation` derives the reserved txid as
  `(1- (fn-sf-frontier files))` (`host/store-node-host.lisp:430`) rather than
  reading a kernel-supplied candidate. It is guarded by
  `(equal (fn-sf-phase files) :reserved)` at `:432`, which makes `frontier`
  positive, and the arithmetic is inside ACL2 rather than raw Lisp. Correct as
  written; recorded only because it is the one place the wrapper computes a
  reservation value instead of projecting one.
