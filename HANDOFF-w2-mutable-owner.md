# Handoff: w2/mutable-owner (C1-05, the mutable service owner)

Worktree `/Users/ember/dev/fn/build/lanes/w2-mutable-owner`, branch
`w2/mutable-owner`, branched from `dev`. HEAD: see the last section (updated
at the end of the lane).

## Books

| Book | Status | Evidence |
| --- | --- | --- |
| `books/owner.lisp` | PENDING (baseline certs being installed from the remote box; certify locally after) | — |
| `books/owner-invariants.lisp` | PENDING | — |
| `tests/acl2/owner-tests.lisp` | PENDING | — |

Makefile roots are placed after `tests/acl2/nntp-teeth-tests`, not directly
after `tests/acl2/store-observed-traces-tests` as the packet said: the
certify driver runs a bare `certify-book` per root and `books/owner` includes
`books/nntp` and `books/clock`, whose roots come later in the list.

## Keystones (verbatim statements and hypothesis stacks)

See `specs/owner.md` for the property / hypotheses / covered-scope table.
Statements as written in `books/owner-invariants.lisp`:

- `fn-own-reader-sees-pinned-prefix-replay`
  hyps: `(fn-own-relation o)`, `(fn-own-find-conn id (fn-own-conns o))`
  concl: `(equal (car (fn-own-read-step o id event)) (fn-nntp-result-effects (fn-nntp-step (fn-own-conn-session conn) (fn-node-acceptance (fn-sf-replay-node groups capacity (fn-own-take (fn-own-conn-version conn) records) (fn-own-conn-frontier conn))) event)))`
  with `conn = (fn-own-find-conn id (fn-own-conns o))`, `groups/capacity/records` of `(fn-own-store o)`.
- `fn-own-reader-sees-pinned-prefix-replay-after-any-trace`: the same over `(fn-own-run o events)`; hyps `(fn-own-relation o)`, the connection exists in the final state.
- `fn-own-completion-consumed-once`: `(equal (fn-own-complete (fn-own-complete o)) (fn-own-complete o))`; no hypotheses.
  Support: `fn-own-complete-ledger-is-exact-pair` (enabled: ledger grows by exactly `(fn-sf-completion files)`, store is `fn-sn-finish`, pending nil; disabled: identity).
- `fn-own-pinned-prefix-survives-any-trace`
  hyps: `(fn-own-relation o)`, `(fn-own-find-conn id (fn-own-conns o))`
  concl: `(equal (fn-own-take version records-final) (fn-own-take version records-initial))`, `version` the connection's pin.
- `fn-own-reclaim-floor-below-every-pin`: hyps as above; concl `(<= (fn-own-reclaim-floor o) (fn-own-conn-version conn))`.
- `fn-own-connections-bounded-after-any-trace`: hyp `(fn-own-relation o)`; concl `(<= (len (fn-own-conns final)) (fn-own-max-conns o))` and `(fn-own-conns-boundedp (fn-own-conns final) (fn-sn-groups (fn-own-store final)))`.
- `fn-own-completed-post-survives-close-and-any-trace`: hyps `(fn-own-relation o)`, `(member-equal pair (fn-own-ledger o))`; concl `(fn-sf-record-has-pairp pair (fn-sf-records (fn-sn-files (fn-own-store (fn-own-run o events)))))`.
- `fn-own-run-preserves-relation`, `fn-own-run-preserves-store-relation`: hyp `(fn-own-relation o)`.
- `fn-own-open-observed-start-relation`: hyps `(fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))`, `(natp max-conns)`.
- Facts: `fn-own-every-fact-is-clock-stamped` (hyps relation, member), `fn-own-declare-group-without-clock-is-refused` (hyp: no observation), `fn-own-declared-group-is-replayed` (hyps stringp name, observation present).

## Teeth (tests/acl2/owner-tests.lisp)

Witness: `*own-trace*` from `(fn-own-start (fn-sn-initial '("fn.letters" "fn.test") 10) 4)`:
open A (v0), open B, begin B, post 1 through the nine real kernel events,
open C (v1), A and C answer `GROUP fn.letters` differently, advance A (v1),
post 2 while C stays pinned (stalled), close B, `(:reopen frontier records)`
over the exact image, open D (v2) sees `211 2 1 2 fn.letters`.
`must-fail` per hypothesis: K1 (relation: bogus archive on a v0 pin; find-conn:
unknown id), K3 (relation: pin above the history / non-natural pin; find-conn),
K4 (relation: five hand-built connections under bound 4, both conjuncts),
K5 (relation: forged ledger pair; member: never-consumed pair), root (open-okp:
malformed frontier; natp max-conns: -1), facts (no clock; nil stamp).

## Host and Python

`tools/run_owner.py` (single process, writer lock, loopback NNTP, Unix control
socket, clock from `time.monotonic_ns`/`time.time_ns` with `--clock-error-ms`),
`host/owner-host.lisp` (`:program` wrappers, one `fn-own-step` per call),
`run_store.py post --owner`, shared `post_article`. Tests: `tests/test_owner.py`
(4 tests: two readers keep pins across a post until advanced and the CLI
thin client; stalled reader does not block a post and the connection bound;
killed owner reopens with every completed post durable and a new reader sees
the newest version; clock and group facts). Python test counts: PENDING.

## Proposals

- Persist the group-fact log through the record kernel (open item in `specs/owner.md`).
- Prove `fn-nntp-step` preserves `fn-nntp-sessionp` in `nntp-invariants` to make the owner's fail-closed branch unreachable.
- Make `run_reader.py --store` a thin client of the owner once HST-002 partial-output tracking lands.
- The committed view refresh is O(records) per idle transition (`len`); carry the count in the store kernel if that ever shows in the reopen profile.
