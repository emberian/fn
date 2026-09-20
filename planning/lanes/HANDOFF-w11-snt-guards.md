# Handoff: w11/snt-guards (the guard chain from `fn-ocfg-statep` to `fn-snt-relation`)

Branch `w11/snt-guards` from `dev` at `19f3302`. Worktree
`/Users/ember/dev/fn/build/lanes/w11-snt-guards`. Proposed by
[`HANDOFF-w10-owner-relation.md`](HANDOFF-w10-owner-relation.md) §9.2, whose
§3 measured the owner-side half and reverted it because it buys nothing
without the store-side half. Both halves land here, in one packet.

## 1. The obligation chain, enumerated before editing

Not read off by eye: `getpropc`'s `symbol-class` over the transitive callees
of `fn-own-relation`, in the world of an included `books/owner-invariants`
(driver `build/w11/drv-chain.lsp`; the walk descends only into functions that
are not already `:common-lisp-compliant`, so what it prints is exactly the
frontier). The whole frontier is **seven functions**, and everything they
call --- `fn-sf-replay-node`, `fn-sf-history-recoverablep`,
`fn-sn-record-bindsp`, `fn-node-complete`, `fn-sn-completion-enabledp`,
`fn-sf-record-phasep`, the record accessors --- was already compliant.

| link | file | was | needed | verdict |
| --- | --- | --- | --- | --- |
| `fn-ocfg-statep` | `owner-config.lisp:191` | `:guard t`, verification FAILS | its callee's guards, then one type fact | **closed**: a `local` forward-chaining `fn-cfgp` → `natp` of the generation |
| `fn-own-relation` | `owner-invariants.lisp:155` | `:ideal` | declaration only | **closed**: `(declare (xargs :guard t))`; guard conjecture "trivial to prove" |
| `fn-own-view-okp` | `owner-invariants.lisp:139` | `:ideal` | declaration only | **closed**: `:guard t` |
| `fn-own-conns-okp` | `owner-invariants.lisp:133` | `:ideal` | declaration only | **closed**: `:guard t` |
| `fn-own-conn-okp` | `owner-invariants.lisp:121` | `:ideal` | declaration only | **closed**: `:guard t` |
| `fn-own-ledger-durablep` | `owner-invariants.lisp:149` | `:ideal` | declaration only | **closed**: `:guard t` |
| `fn-snt-relation` | `store-node-traces.lisp:159` | `:ideal` | declaration + deferred `verify-guards` + a theory hint | **closed** |
| `fn-snt-pending-linkp` | `store-node-traces.lisp:145` | `:ideal` | a real GUARD (two typed hypotheses) + deferred verification | **closed** |
| `fn-snt-idle-phasep` | `store-node-traces.lisp:137` | `:ideal` | declaration only | **closed**: `:guard t`, trivial |

Read the last three rows together: they are the only links that needed more
than a declaration, and only one of them needed a guard that is not `t`.

## 2. Why `fn-snt-pending-linkp` gets hypotheses and `fn-snt-relation` does not

`fn-snt-pending-linkp` calls `fn-node-complete` (`node.lisp:207`, guarded by
`(fn-node-statep s)`) and `fn-sn-record-bindsp` (`store-node.lisp:119`, the
same guard), and it `append`s to `(fn-sf-records files)`, which owes
`true-listp`. Measured with the guard at `t`, the only residue is
`(TRUE-LISTP (FN-SF-RECORDS FILES))`. So its guard is exactly what its
callees ask for:

    :guard (and (fn-node-statep node) (fn-sf-statep files))

`fn-snt-relation` keeps `:guard t`, because its own first conjunct is
`(fn-sn-statep s)` and an `and` puts that conjunct in the hypotheses of every
later guard obligation the form generates. `fn-snt-typed-store-components`
(`store-node-traces.lisp:225`, already in the book, `:forward-chaining`)
carries `(fn-sn-statep s)` to `(fn-sf-statep (fn-sn-files s))` and
`(fn-node-statep (fn-sn-node s))`, which is the pair the call site owes. That
is why both `verify-guards` forms are DEFERRED to just after line 225 rather
than written under the `defun`s: the lemma that discharges them is between.

The `:reserved` arm's `(1- frontier)` needs `acl2-numberp`, and `(posp
frontier)` precedes it in the same `and`; nothing was added for it.

Neither proof needed a `:use`, a witness, or a profile: both are
`prove: 0.00` (234 and 681 prover steps). `tools/proof_profile.py` was not
run, because nothing here took a minute --- the rule is profile BEFORE a hint
you cannot justify in one sentence, and the only hints here are
`(disable ...)` lists that name the recognizers the goal must not open.

## 3. Is this whole-state revalidation on a served path? No, and here is the check

AGENTS.md forbids a recognizer over the whole store running per command.
`fn-snt-relation` is Θ(n) in the record history at least (it calls
`fn-sf-replay-node` over `(fn-sf-records files)`), so if anything served
called it the answer would have been "carry it in state", not "verify it".
It does not:

* `grep -rn "fn-own-relation\|fn-snt-relation" host/ tools/*.py` → **no hits**.
  No host line calls either; they are proof vocabulary.
* No `defun` in `books/` guards itself by either one (`grep` over
  `:guard` lines). `books/served`'s guard-verified `fn-served-dispatch`
  reaches `fn-peer-step`, not this.
* `fn-ocfg-statep` is the only caller of `fn-own-relation`, and it has no
  caller at all outside `books/owner-config.lisp`.

Guard verification here changes no execution: it removes an admission
blocker. The three functions stay withdrawn at their books' export theories
(`fn-snt-relation`, `fn-snt-pending-linkp` in
`store-node-traces.lisp`'s final `in-theory`), so nothing new is enabled on
include either.

## 4. `books/owner-config`: 31 `ACL2 Error` to 2, and the two that are left

With the chain closed, `ld` of the book (`:ld-error-action :continue`, so
every event is attempted rather than stopping at the first failure) reports
**2 errors, both `DEFTHM` failures; every `defun` in the book now admits and
guard verifies** (28 "compliant with Common Lisp"). The four repairs:

| defect | obligation | repair |
| --- | --- | --- |
| `fn-ocfg-statep` | `(acl2-numberp (fn-cfg-generation (fn-ocfg-config oc)))`, from the staged clause's `1+` | `local` `:forward-chaining` `fn-ocfg-configured-generation-is-natural`: `fn-cfgp` → `natp` (`config.lisp:504-508`, withdrawn at that book's export) |
| `fn-ocfg-reconfig-record` | the same term, with no state around it | `:guard (fn-cfgp (fn-ocfg-config oc))` --- the conjunct of `fn-ocfg-statep` that makes the arithmetic total, carried rather than recomputed |
| `fn-ocfg-reconfig-okp`, `fn-ocfg-reconfigure`, `fn-ocfg-reconfig-refusal` | the same, by call and by their own `1+` | the same guard |
| `fn-ocfg-repins-forp` | `(car (car events))` and `(car (cdr (car events)))` under `:guard t`: false at `events = (list 3)` | `mbe` with `fn-ag-car`/`fn-ag-cdr` in the `:exec`, `:logic` byte for byte unchanged --- the idiom the four accessors got at `7f59156`'s repair |

No logical term changed and no theorem statement changed.

**The two that are left are keystones that are false as stated**, and they
are left in the file unproved rather than weakened or deleted; each carries
its key checkpoint and its missing hypothesis as an OPEN note at the
`defthm`. Both are the same shape --- a pin-table precondition that
`fn-ocfg-statep` was written to carry and the theorem does not ask for:

1. **`fn-ocfg-open-pins-the-live-configuration`.** `fn-ocfg-pin-add` never
   overwrites, so a STALE pin at `(fn-own-next-id o)` survives the add and
   the new connection serves the stale configuration. This does NOT follow
   from `fn-ocfg-statep`: `fn-ocfg-pins-pin-conns-only` turns such a pin into
   an open connection at `next-id`, and `fn-own-relation` carries no bound
   tying a connection's id to `fn-own-next-id`. **Cross-cluster packet 1.**
2. **`fn-ocfg-advance-observes-the-live-configuration`.** `fn-ocfg-pin-set`
   replaces and never adds (it returns `nil` on an empty table), so
   `fn-ocfg-pin-find-of-pin-set-same` needs `(fn-ocfg-pin-find id ...)`.
   This one IS carried by `fn-ocfg-statep` through `fn-ocfg-conns-pinnedp`;
   the packet is one local induction, the hypothesis, and the teeth --- which
   need a `tests/acl2/owner-config-tests` book the tree does not have.
   **Packet 2**, owned by whoever takes `books/owner-config` next.

The book's own prose claimed the first of these was not needed ("with no
freshness hypothesis to discharge", at `fn-ocfg-pin-add`). That sentence is
**withdrawn in this commit**: it had never been checked, because the book had
never been admitted.

## 5. Per-root certification
