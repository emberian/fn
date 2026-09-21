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
| `certify-20260920T234831Z-1314032` | + the cheap recognizer's separating witnesses | passed; 64.27 / 7.31 / 0.47 s, wall 72.453 s |
| `certify-20260920T235524Z-1317872` | branch head `540dd78` | passed; 64.33 / 7.35 / 0.47 s, wall 72.561 s |

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

### The guard, measured directly

Driver, `ld`ed at `/tank/fn/lanes/w11-tcpcl-theory/books` on hbox under
`swarm-build` with `ACL2_CUSTOMIZATION=NONE ACL2_BOOK_HASH_ALISTP=NIL` and a
600 s wall-clock `timeout`, against the certified `books/tcpcl-session` of
this branch. No prover step limit; nothing here is a proof.

```lisp
(include-book "tcpcl-session")
(defun fn-x-staged (n acc) (if (zp n) acc (fn-x-staged (- n 1) (cons '(1) acc))))
(defconst *x-p* (fn-tcl-make-params 30 4096 10000000 '(100 116 110) nil nil))
(defconst *x-m* (fn-tcl-make-sess-init 30 4096 10000000 '(100 116 110) nil))
(defconst *x-n* (fn-tcl-negotiate *x-p* nil *x-m*))
(defconst *x-s20000*
  (fn-tcl-make-session :active :established *x-p* nil *x-m* *x-n*
                       (fn-tcl-make-inbound 0 (fn-x-staged 20000 nil) 20000 nil)
                       nil 1 0 0 nil))          ; and *x-s1*, *x-s1000* alike
(assert-event (fn-tcl-sessionp *x-s20000*))      ; all three, both recognizers
(assert-event (fn-tcl-session-cheapp *x-s20000*))
(defun fn-x-rep-spec  (s n) (if (zp n) 0 (+ (if (fn-tcl-sessionp s) 1 0)       (fn-x-rep-spec  s (- n 1)))))
(defun fn-x-rep-cheap (s n) (if (zp n) 0 (+ (if (fn-tcl-session-cheapp s) 1 0) (fn-x-rep-cheap s (- n 1)))))
(time$ (fn-x-rep-spec *x-s20000* 2000))          ; etc
```

The `assert-event`s matter: both recognizers return T on every session here,
so each traverses to completion and neither is being timed on an early exit.
Zero `ACL2 Error` in the log.

| staged segments | `fn-tcl-sessionp` | `fn-tcl-session-cheapp` |
| --- | --- | --- |
| 1 | 0.15 s / 200,000 calls = 0.75 µs | 0.14 s / 200,000 = 0.70 µs |
| 1,000 | 0.03 s / 2,000 = 15 µs | 0.14 s / 200,000 = 0.70 µs |
| 20,000 | 0.50 s / 2,000 = 250 µs | 0.14 s / 200,000 = 0.70 µs |

Linear in the staged list against flat, ~360× apart at 20,000 segments.
Limitation: this times the recognizers, not a transfer. It is the mechanism
`specs/tcpcl.md` §3 names — the executable counterpart checks the callee's
guard once per socket chunk — and not an end-to-end throughput claim.

### `tools/tcpcl_lab.py --scenario profile`

Run on hbox against `/tank/fn/lanes/w9-dtn-e2e/build/fn-host-dtn`, the image
w9/dtn-e2e built at 14:18 from a cheap-guard `books/tcpcl-session.lisp`
whose bytes are **not** identical to this branch's
(`22bc9b33…` there, `f7d1694b…` here, both carrying the cheap guard):

```json
{"scenario": "profile", "ok": true, "ratio": 0.53, "size_ratio": 4,
 "small_octets": 65536, "small_seconds": 0.232,
 "large_octets": 262144, "large_seconds": 0.124,
 "small": {"rc": 0, "intact": true}, "large": {"rc": 0, "intact": true}}
```

`ok` because the ratio is below the 8× bar; a quadratic guard gives about
16×. But the 256 KiB transfer was *faster* than the 64 KiB one, and w9's run
of the same scenario against the same image reported 0.115 s / 0.212 s and
ratio 1.84, so at these sizes the measurement is two process starts of a
262 MB image with the second warm. **The scenario is a pass/fail gate
separating 16× from ~1×, not an instrument for the ratio**, and this record
does not quote its ratio as one.

### Not measured

An image built from this branch. It needs the DTN closure certified on a
box; persvati `run-20260920T234237Z-8081` certified seven of its nine roots
(`store-observed-traces`, `bp-ingress`, `bp-receipt`, `bp-receipt-records`,
`bp-workflow-records`, `tcpcl-session`, `bp-bundle`) and was still on
`bp-bundle-invariants` and `bp-node` when this lane closed. Its pairs are in
persvati's cache for the next lane.
