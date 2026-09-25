# The intent identity computed once and carried (D27 boundary 2), 2026-09-25

Design: `planning/design-2026-09-25-representation.md` §5 rank 2. The
submission's intent identity `fn-own-feed-intent-id` (books/owner-feed.lisp:
SHA-256 of the payload, then SHA-256 of the obligation preimage) was computed
four times per POST by the references in books/owner.lisp:
`fn-own-submission-intent-result` once, `fn-own-submission-intent-records`
twice (itself, and again through the result it calls), and
`fn-own-submission-resolution-records` once. It is now computed once, when
`fn-owner-take` takes the submission, and carried.

## What changed

- **books/owner-intent-carried.lisp** (new; prefix `fn-icar-`). No slot was
  added to the submission record: books/owner.lisp is unchanged (0 of its 158
  dependents move). The carry is the pair `(SUB . ID)`:
  - `fn-icar-carry-of sub` = `(cons sub (fn-own-feed-intent-id (fn-own-sub-msgid sub) (fn-own-sub-octets sub)))`.
  - `fn-icar-carryp carry` = `(or (atom carry) (equal (cdr carry) (fn-own-feed-intent-id (fn-own-sub-msgid (car carry)) (fn-own-sub-octets (car carry)))))`. It mentions no owner, so no owner step can falsify it.
  - `fn-icar-intent-id sub carry` returns `(cdr carry)` when `(car carry)` is
    `sub` (CL `EQUAL`, which is `EQ` on the object the take left in flight)
    and digests otherwise, so a stale carry costs a digest, never a wrong
    identity.
  - `fn-icar-submission-intent o carry evidence generation txid` returns
    `(result . records)` in one call (one identity, one target computation);
    `fn-icar-submission-resolution-records` is the reference with the identity
    replaced.
- **host/owner-host.lisp**: `fn-owner-take` (line 670) writes
  `(fn-icar-carry-of sub)` to the state global `fn-owner-submit-intent`; this
  is the only writer. `fn-owner-intent-carry` reads it (nil when unbound).
  `fn-owner-submission-intent` calls `fn-icar-submission-intent` (line 1036);
  `fn-owner-submission-resolution` calls
  `fn-icar-submission-resolution-records` (line 1054). The native host reaches
  both through `fnn-owner-action` (host/native/owner.lisp 1184, 1272, 1345:
  served, transit and control takes all pass through `fn-owner-take`).
- host/native/build.lisp and the Makefile book/test lists include the book;
  docs/prefixes.md registers `fn-icar-`.

## Theorems (all guard-verified at guard t; the host-called subjects are the
functions named in the conclusions)

- `fn-icar-intent-id-is-intent-id` (keystone): `(implies (fn-icar-carryp carry) (equal (fn-icar-intent-id sub carry) (fn-own-feed-intent-id (fn-own-sub-msgid sub) (fn-own-sub-octets sub))))`.
- `fn-icar-submission-intent-is-reference`: `(implies (fn-icar-carryp carry) (equal (fn-icar-submission-intent o carry evidence generation txid) (cons (fn-own-submission-intent-result o evidence generation txid) (fn-own-submission-intent-records o evidence generation txid))))`. Host line 1036.
- `fn-icar-submission-resolution-records-is-reference`: `(implies (fn-icar-carryp carry) (equal (fn-icar-submission-resolution-records o carry word evidence generation txid) (fn-own-submission-resolution-records o word evidence generation txid)))`. Host line 1054.
- The hypothesis is discharged for the host's writer by
  `fn-icar-carryp-of-carry-of` (`(fn-icar-carryp (fn-icar-carry-of sub))`, no
  hypothesis; a by-definition fact) and for the unset global by
  `fn-icar-carryp-when-atom`; `fn-icar-submission-intent-of-take-carry` and
  `fn-icar-submission-resolution-records-of-take-carry` state the two
  equalities with the take's carry substituted, with no hypothesis
  (corollaries, not registry events).

The remaining assumption is the host discipline, not an ACL2 fact: the
global `fn-owner-submit-intent` has no writer other than `fn-owner-take`
line 670 (`git grep fn-owner-submit-intent host` shows the one write and the
one read). It sits under A-HOST like every other host global.

## Teeth (tests/acl2/owner-intent-carried-tests.lisp)

- Reachable witness: owner-tests' `*own-control-fed-taken*` (a control
  submission taken by `fn-own-take-submission` into an owner with one
  outbound feed). The carried identity is a feed name equal to the digest of
  the control Message-ID and source; the carried intent is `:ready` with one
  record and equals `(cons result (own-control-intents))`; the resolution
  equals `own-control-commits` after the consumed completion, `own-control-aborts`
  on `:duplicate`, nil on `:uncertain`.
- A stale carry (a valid carry of `*own-taken*`'s served POST) and the nil
  carry both give the reference.
- One hypothesis per theorem, one `must-fail` each (the keystone, the intent,
  the resolution without `fn-icar-carryp`). The separating witness is a forged
  carry whose `car` IS the in-flight submission (so neither the atom clause
  nor the submission match separates it) holding another submission's valid
  feed-name identity: it violates `fn-icar-carryp`, and the identity, the
  intent and the commit records all differ from their references.
- All four host-called definitions are `:common-lisp-compliant`.

## Certification

- persvati, `w25/acl2-literal`, 2 jobs, 300 s, `--affected-by
  books/owner-intent-carried` (selects the book and its test only; nothing
  else includes it):
  - run-20260925T023047Z-0b84, manifest `certify-20260925T023104Z-3465520`
    at 9d63688a: the book passed (4.1 s); the test refused (a `defconst` may
    not call the SHA-256 attachment).
  - run-20260925T023245Z-daaf, manifest `certify-20260925T023302Z-3483991`
    at b6c41e57: the test passed (4.2 s).
  - run-20260925T023917Z-fb8c, manifest `certify-20260925T023933Z-3540691`
    at 544e282b (the uncalled result twin removed): book 3.6 s, test 4.1 s,
    status passed. These are the current bytes.
- `tools/green_check.py --changed-since 087f7213`: 2 changed books, 0
  books include one, 0 not green at the bytes a merge would carry.
- hbox, in place (setup2.sh: default-profile roots certified from
  `/tank/fn/certcache`, `w28/acl2-literal-4g`, 8 jobs, 900 s):
  `hbox-after-certify-20260925T023339Z-2396761.json` (after tree b6c41e57,
  includes owner-intent-carried, passed) and
  `hbox-base-certify-20260925T023339Z-2396760.json` (base tree dev 087f7213,
  passed).
- Static: `tools/host_shape_check.py` 0 findings, `tools/build_lists_check.py`
  0 findings.

## Measurement (hbox, developer images, 2026-09-25 02:33 to 02:38 UTC)

Images built in the same session by the representation lane's scripts
(`rep-intent-2026-09-25/`, scratch `/tank/fn/scratch/rep-intent/`): before =
dev `087f7213`, launcher `94f404d6…`, core `2f10785f…`; after = lane
`b6c41e57`, launcher `593526f1…`, core `18b939a1…` (`*-image.sha256`). The
after image still contained `fn-icar-submission-intent-result`, which no host
line called and 544e282b removed; the executed path is the same. Box load
1.4 to 3.5, no other tenant.

**CPU per POST at N = 120** (`prof_post.py`, 48 POSTs from 72 to 120, SBCL
sprof CPU mode at 1 ms, base and after alternated, three rounds; shares are
the graph "Total" column):

| round | before: samples (÷48) | after: samples (÷48) | before: `fn-own-feed-intent-id` | after: `fn-own-feed-intent-id` (all under `fn-icar-carry-of`) | before: `fn-sha256-of-octets` | after |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 176 (3.67) | 126 (2.62) | 18.2% | 5.6% | 34.1% | 25.4% |
| 2 | 127 (2.65) | 150 (3.12) | 15.7% | 4.7% | 31.5% | 23.3% |
| 3 | 140 (2.92) | 142 (2.96) | 15.0% | 2.1% | 34.3% | 22.5% |

- The identity's share falls from 15 to 18% to 2 to 6%, and in every after
  round its only caller is `fn-icar-carry-of` under `fn-owner-take`: the
  intent and the resolution never digest (the `EQUAL` on the carried
  submission hits). SHA-256's total share falls from 31 to 34% to 22 to 25%.
  `fn-owner-submission-intent` falls from 15 to 17% to 0.7 to 1.3%.
- **Samples per POST are not a usable absolute figure here**: the profiler
  took 2.6 to 3.7 samples per POST in both images (the representation lane's
  session read 12 to 15 on the same method), and the before/after ranges
  overlap. The shares and the tmpfs wall below are the figures.

**POST wall on tmpfs `/dev/shm`** (`msgid_measure.py`, 16 samples per point,
one run per image, medians):

| N | before: first quarter | after | before: last quarter | after | before: load | after | before: RSS after load | after |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 16 | 2.64 ms | 1.56 ms | 1.92 ms | 1.43 ms | 0.033 s | 0.024 s | 323 MiB | 320 MiB |
| 50 | 2.12 ms | 1.47 ms | 1.90 ms | 1.46 ms | 0.101 s | 0.071 s | 358 MiB | 349 MiB |
| 120 | 1.82 ms | 1.44 ms | 1.91 ms | 1.44 ms | 0.226 s | 0.173 s | 432 MiB | 411 MiB |

At N = 120 the last-quarter POST wall on tmpfs, where fsync is free and the
wall is the CPU, falls from 1.91 to 1.44 ms (−25%), and loading 120
articles from 0.226 to 0.173 s (−23%). This is one alternation of one run
per image, not three; the direction agrees with the profile shares. The
change is a constant factor per POST (three of four payload digests
removed); it changes no exponent in N.

## What remains

- The one remaining digest per POST is at take, O(L) over octet lists;
  rep-sha256 (the word stobj) reduces its cost.
- `fn-own-submission-targets` (which parses the Path through
  `fn-own-feed-path-of`) is still computed at the intent and again at the
  resolution; 1 to 4% of samples, not carried here.
- The carry's correctness rests on the host global having one writer
  (A-HOST); an ACL2-held slot in the submission record would make it a
  theorem about the owner state and costs owner.lisp's 158 dependents.
