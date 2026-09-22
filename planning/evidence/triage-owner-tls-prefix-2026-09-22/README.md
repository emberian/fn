# Is `books/owner-tls-prefix` red only behind the store cascade? No.

The T7 row of [the trajectory plan](../../plan-2026-09-22-trajectory.md) says
`books/owner-tls-prefix` is "red only behind the store-node cascade (a
provisional wave shows it proved)". No record in the tree shows that, so lane
`t7/auth-teeth` measured it, twice: once on its own tree and once on `dev` as
the control, on the same box, the same toolchain and the same 800 s per-book
budget.

| tree | run | remote root | independent reds |
| --- | --- | --- | --- |
| lane `t7/auth-teeth` `2ea2706f` | `run-20260922T175556Z-6fd4` | `/home/ember/fn-gates/t7-owner-tls` | 5 |
| control, `dev` `a388826f` | `run-20260922T181335Z-702f` | `/home/ember/fn-gates/t7-owner-tls-ref` | 5, the same five |

The five, with the form each fails on, identical in both trees:

| book | failing event |
| --- | --- |
| `books/owner-invariants` | `fn-own-read-offers-against-the-live-node` |
| `books/owner-tls-prefix` | `fn-ocfg-read-tls-prefix-is-full-read` |
| `books/store-node-resolution` | `fn-sn-known-abort-is-exact-node-abort` |
| `books/store-node-traces` | `fn-snt-record-directory-preserves-relation` |
| `books/store-observed` | `fn-sn-observed-seed-is-state` |

`books/owner`, `books/owner-config` and `books/owner-fault` prove in both and
wait only on `books/store-node-traces`.

Two things follow. First, the lane's own change to `books/nntp-auth` and the
books above it introduced no red: the two independent-red sets are equal and
`books/owner-tls-prefix` fails at the same key checkpoint on `dev`, `Subgoal
13''`, whose first hypothesis is `(NOT (FN-WIRE-STATEP (FN-OWN-CONN-WIRE
(FN-OWN-FIND-CONN ID (FN-OWN-CONNS (FN-OCFG-OWNER OC))))))`: the proof needs
"a connection the owner holds has a wire state" out of `(fn-ocfg-statep oc)`
and does not get it. Second, T7's `owner-tls-prefix` green is blocked on
`books/owner-invariants` as much as on the store cascade, and neither is a
book this lane owns; `books/owner-invariants` is T5/T6's.

`lane-2ea2706f.md` is the first wave's report. **Neither is evidence of
certification**: a triage substitutes sources on the box, publishes no
certificate and archives no manifest, and `docs/proofs.md` says a claim about
the tree still comes from an ordinary run. What these two establish is that
the two trees behave the same.
