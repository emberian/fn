# Handoff: w3/scale-profile

Branch `w3/scale-profile`, branched from `dev` at 9321344. Lane commits:
`e4ad5e9` (harness, named scale profile, measured document) and the commit that
carries this file.

## What landed

- `tests/bench/generate.py` — builds a store of N articles in G groups with P
  payload octets through the real acceptance path (`fn-store-sn-prepare`, a
  published immutable transaction file, `fn-store-sn-finish`), deterministic
  from `--seed`. Payloads are projectable articles: a random blob answers
  ARTICLE with `503 stored article framing unavailable` and measures nothing.
  `--payload-kind folded` and `--message-id-octets` drive the stress cases.
- `tests/bench/measure.py` — reopens a generated store and times GROUP,
  LISTGROUP, ARTICLE (by number at three positions and by Message-ID) and the
  OVER-equivalent enumeration against the recovered node, in the same ACL2
  process; reads `VmRSS`/`VmHWM` from `/proc`, and meters the octets the host
  writes into the bridge.
- `tests/bench/grid.sh`, `tests/bench/grid2.sh` — the exact loops that ran.
- `tools/run_store.py` — a second **named** profile, `fn-store-profile-scale-1`
  (4096 transactions), not a raised default. The development profile's
  configuration bytes are unchanged, verified against the pre-change tree in
  `/tank/fn/gates/dev-9321344`: checksum `49dd591a5988…` on both sides, so
  every existing store still opens. The scale profile's checksum is
  `37902a4bf826…`.
- `planning/scale-profile.md` — the measured tables, the environment, the five
  cliffs with file and line, what the checkpoint and index lanes do and do not
  fix, and the articles-by-reference proposal with its refinement obligation.

## The grid that actually completed

All on hbox (Linux 6.11.0-29, 24 cores, ACL2 8.7 over SBCL 2.6.8, CPython
3.12.7), load average 2.7 to 5.7, five runs per measurement point (three at
N ≥ 256).

- N ∈ {16, 32, 64, 128, 256, 512} at G=2, both groups per article, P=1024.
  N=1024 was launched with a 90-minute per-point budget; see the document for
  its outcome.
- P ∈ {512, 1024, 4096, 16384, 32768} at N=64 — the payload bound is reached
  exactly.
- G ∈ {1, 2} and groups-per-article ∈ {1, 2} at N=64. **The axis stops there**:
  `books/store-config.lisp:18` defines the group table as exactly
  `("fn.letters" "fn.test")` with its two mapping directions proved inverse, so
  the packet's G=1000 is a model change, not a configuration.
- Stress at the bounds, N=32: maximum payload (32768), maximum Message-ID (250
  octets), 120-line folded header block, and all three at once.

N=10000 was not reached and is not a matter of waiting longer — see the reopen
curve.

## Cliffs found, with numbers

- **Reopen is super-quadratic, approaching cubic.** Median reopen: 0.793 s at
  N=16, 2.718 s at N=128, 12.729 s at N=256 (three runs, min 12.540 s) for a
  store holding 256 KiB of article payload. Above the ~0.75 s fixed floor the
  replay term multiplies by 3.2, 3.2, 4.8, 6.1 across the doublings.
  Cause: `books/replay.lisp:142` checks `fn-node-statep` twice per record and
  `fn-replay-apply-record` (`:113`) calls two node operations that each check
  it again — four Θ(n² + n·P) passes per record.
- **Every served operation revalidates the whole store.**
  `books/acceptance.lisp:662`, `:695`, `:720` and `books/node.lisp:229`, `:283`
  all begin by recomputing the whole-state recognizer; `fn-statep`
  (`books/acceptance.lisp:574`) is Θ(n²) in Message-ID comparisons and Θ(n·P)
  in octet checks. This is the `AGENTS.md` D3 rule, violated in the executable
  path. The preservation theorems needed to fix it already exist
  (`books/acceptance-invariants.lisp:74/195/201`,
  `books/node-invariants.lisp:8/71`); what is missing is taking them as guards.
- **Articles are held by value.** `fn-state-articles`
  (`books/acceptance.lisp:545`) holds full payload octet lists. A 256-article
  store of 1 KiB articles peaked at 1.88 GB RSS on reopen; 32 maximum-size
  articles (1 MiB of payload) peaked at 981 MB while posting.
- **The decimal-octet bridge expands by 6.37x, measured.** Post form bytes
  against payload size from 512 to 32768 octets: 5,889 → 211,256. Recovery
  marshals the entire history as one such literal.
- **Folding is the cheapest hostile input.** At P=16384, folding the header to
  120 continuation lines took the OVER-equivalent enumeration from 0.670 ms to
  4.106 ms per article (6.1x); a 250-octet Message-ID took GROUP from 0.226 ms
  to 1.069 ms (4.7x) at N=32. Nothing refused, nothing wedged.
- **OVER does not exist.** `books/nntp.lisp:1297` admits GROUP, LISTGROUP,
  LAST, NEXT, ARTICLE, HEAD, BODY, STAT. The OVER-equivalent measured is
  LISTGROUP plus HEAD per number, and is labelled as a substitution everywhere.

## Proposal to the next model lane

Articles by reference: the article record keeps its Message-ID, groups,
memberships and pin and holds `books/identity`'s content subject instead of
payload octets; a content map (or `specs/objects.md`'s blob manifest) holds the
bytes once. Separately and independently: give the five acceptance/node
operations `:guard (fn-statep s)` under `mbe`, discharged from the preservation
theorems that already exist — that alone removes the per-command cliff without
changing the state shape.

The refinement obligation, stated so it cannot be discharged vacuously: an
inflation function to the current by-value state, a commuting theorem for each
operation the host calls, a preservation theorem for content-map closure under
every one of them, a `must-fail` sibling per hypothesis, and the collision
premise named as A-CRYPTO with `OBJ-001`'s quarantine case. Details in
`planning/scale-profile.md`.

## Open and not done here

- N=1024 and above: see the document for what completed.
- No book was edited and none needed recertification; the 28-book closure was
  certified once in `/tank/fn/scale` for the measurements.
- `tests/test_store_corruption.py` exercises the configuration refusal this
  lane touched; it needs a local ACL2 and was not run to completion on the
  development machine. The control used instead is exact: the development
  profile's configuration checksum is byte-identical to the pre-change tree.
