# Evidence: w11/tcpcl-theory — the served-path guard and the invariants theory

Lane `w11/tcpcl-theory` from `dev` at `19f3302`. Everything below is one box,
one ACL2, no prover step limit; the cap is wall clock.

## Tooling

| | |
| --- | --- |
| Box | hbox, `Linux-6.11.0-29-generic-x86_64-with-glibc2.40`, load 2.22 and 21 G available at launch |
| ACL2 | `/tank/fn/acl2-8.7/saved_acl2`, `ACL2 Version 8.7`, sha256 `64030dda0b03bbb6cf50984889f5ce1e2ba867b6ce3c9a65403afc44f9b4fdb5` |
| Lisp | SBCL 2.6.8 |
| Runner | `python3 tools/certify_books.py --jobs 4`, wrapped in `swarm-build`, `FN_ACL2_TIMEOUT_SECONDS=1800`, `FN_CERT_CACHE=/tank/fn/certcache`, `FN_CERT_ORIGIN_KIND=run` |
| Tree | `/tank/fn/lanes/w11-tcpcl-theory`, mirrored by `rsync -a --delete`, certificates then installed by `tools/certs.py install --cache /tank/fn/certcache` |

`rsync --delete` removes the installed `.cert`/`.port` pairs (the tree tracks
none, deliberately), so **every mirror in this lane was followed by a
reinstall**. The first run without it failed at `include-book "deftransition":
There is no certificate`, which is what that looks like.

## Runs

| run | tree state | verdict |
| --- | --- | --- |
| `certify-20260920T230902Z-1283742` (w9/dtn-e2e, `/tank/fn/lanes/w9-dtn-e2e-fix`) | dev `19f3302` | passed; session 25.259 s, invariants 609.687 s, tests 0.312 s |
| `certify-20260920T233326Z-1303168` | + the theory work (`164f964`) | passed; 25.59 / 6.61 / 0.46 s |
| `certify-20260920T233937Z-1307933` | + the guard change (`9784cdc`) | passed; 65.30 / 7.40 / 0.48 s, wall 73.749 s, `jobs_effective` 3 |
| `certify-20260920T234831Z-1314032` | + the cheap recognizer's separating witnesses, branch head | passed; 64.27 / 7.31 / 0.47 s, wall 72.453 s |

The first run is used as this lane's baseline **without re-running it**,
because its manifest's `source_digests_sha256` equals this worktree's for
every book in the closure: `books/tcpcl-invariants.lisp`
`73ddc4e8…4700ca1`, `books/tcpcl-session.lisp` `14220c48…9d4d33e6ceb8`,
`books/tcpcl-octets.lisp` `77754db4…9a800bfe0d5`,
`tests/acl2/tcpcl-tests.lisp` `23f4d504…7bb1147c886`,
`books/tcpcl-records.lisp`, `books/clock.lisp`, `books/cbor.lisp`,
`books/deftransition.lisp` likewise. Re-measuring it would have cost ten
minutes of a shared box to reproduce a number already taken on the same box,
the same ACL2 and the same bytes.

## Limitations

- These are three roots, not the tree. Only `host/tcpcl-host.lisp`,
  `tests/acl2/tcpcl-tests` and the two native build lists include
  `books/tcpcl-session`, and the first is not a certification root.
- `certify-book` stops at the first failure, so a "passed" line is a claim
  about a whole book and a failure line is a claim only about the events
  before it. All three logs here contain zero `ACL2 Error`.
- The per-form figures quoted in `planning/lanes/HANDOFF-w11-tcpcl-theory.md`
  §2 are `Time:` lines from the runs' own `.certify.log` and from two `ld`
  probes of the book's source on the same box; an `ld` probe does not produce
  a certificate and is not offered as one.

## Transfer cost

PROFILE-PLACEHOLDER
