# A signed POST's owner CPU stops growing with the history (lane signed-post-linear, 2026-09-26)

Brief: `build/coordinator/queue/done/w4-signed-post-linear.txt` (the
performance ledger's fix lane 5, row 4; PKT-330 (2)). Ids: PRF-193, SCN-122,
PKT-552 (what remains). PKT-553 not taken (no decision arose). Branch
`lane/signed-post-linear` from dev 6407de336. Nothing deployed; every run is
loopback on `/dev/shm` under `/tank/fn/scratch/signed-post-linear/` on hbox.

## What now works

A signed POST's identity prepare decides its candidate from the history's
last record instead of folding every record's txid, so the owner CPU a signed
POST costs no longer grows with N: 260.5 / 293.5 ms at N = 10,000 on dev
becomes 91.0 / 93.0 ms, the same as the lane's 67.0 / 92.5 ms at N = 1,000.
The verdict and the served bytes are unchanged: the staging is equal to the
former one on every input (`fn-pcar-stage-record-is-stage-record`, no
hypothesis), and PRF-144's keystones are re-proved over the new body with
their statements unchanged.

## 1. The profile (before any fix)

Harness `signed-post-linear-2026-09-26/prof_signed.py` (driver `prof.sh`):
`load` builds a store of N POSTs of about 2 KiB, 32 of them hybrid-signed
carriers spread evenly (measure_signed.py's history; one hybrid author
enrolled; profile `scale`), with 40 probe carriers signed by the image's own
`hybrid-sign-carrier`; `run` copies the store, opens it, warms with one
unsigned and one signed POST, then times 20 unsigned and 20 signed POSTs,
each batch on ONE connection opened before it (the greeting is not in the
figure: f314a5a3's greeting still ran `fn-statep`, 23.9 percent of a first
fresh-connection run, discarded), with the owner's CPU from /proc over each
batch and, with `--sprof`, sb-sprof `:cpu` at 1 ms over all threads for the
signed batch. Image: the perf-ledger's profiling twin of dev f314a5a3
(`/tank/fn/scratch/perf-ledger/tree/build/fn-host-developer-prof`, core
sha256 90544f4c...; nothing on the identity prepare changed between f314a5a3
and 6407de336). Store on tmpfs, box load 10 to 13.

| N | signed POST owner CPU | unsigned | samples (20 signed) | `fn-sf-next-lower` | `fn-ccar-sn-prepare-identity` |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1,000 | 86.5 ms | 3.5 ms | 1,461 | 318 (21.8 %) | 468 (32.0 %) |
| 10,000 | 249.0 ms | 5.5 ms | 4,244 | 2,965 (69.9 %) | 3,145 (74.1 %) |

The linear term (graph totals, 10,000): `fn-sf-next-lower` 69.9 percent,
called only by `fn-sf-candidatep` <- `fn-spc-stage-record` <-
`fn-ccar-sn-prepare-identity` <- `fn-ccar-ocfg-prepare-identity` <-
host/owner-host.lisp `fn-owner-prepare-identity` <- host/native/owner.lisp
`fnn-owner-identity-commit` (the kind-4 composite of every signed POST, from
`fnn-owner-attempt-transit`). Its self time is the record recognizer:
`fn-store-event-txid` dispatches through `fn-record-p`, which walks each
record's octets (`fn-record-string-octets-aux` 41.8, `fn-record-payloadp`
35.8, `fn-cbor-octet-listp` 26.8 percent in the graph). Per signed POST that
is 15.9 ms at 1,000 and 148 ms at 10,000 (x9.3 for x10): O(N x L). The top of
the flat at 10,000: `fn-record-string-octets-aux` 20.9, `fn-cbor-octet-listp`
17.9, `fn-record-payloadp` 12.3, `fn-cbor-octetp` 11.8, `SB-IMPL::APPEND2`
10.3 percent self.

Everything else is constant in N (samples at 1,000 / 10,000 over 20 signed
POSTs): `fn-article-parse-lines` 562 / 568 (its `fn-article-add-fold` is an
`append` per header line: quadratic in the header, 28 ms a POST; called by
`fn-hc-received-plan` three times, from `fn-pa-carrier-form`, the snapshot and
the revoked binding checks, and by `fn-own-feed-article-of`),
`fn-ccar-ocfg-complete` 329 / 387, `fn-replay-identity-step` 334 / 340. What
does grow besides, and is small: `fn-replay-apply-record` 60 / 134 (the node
prepare's `fn-retain-known-id-scanp` 10 / 64 and `fn-acceptedp` 1 / 18),
about 3.7 ms a POST more at 10,000: the unsigned POST's walks, which
post-identity-index (running) owns; and the D25 check on this path,
host/owner-host.lisp `fn-owner-existing-action` -> `fn-rcl-existing-action`
-> `fn-find-article`, 10 samples at 10,000 (0.5 ms a POST).

Files: `prof-flat-before1c-1000.txt` (sha256 0429f52a...),
`prof-graph-before1c-1000.txt` (06c14507...), `prof-flat-before-10000.txt`
(1465c169...), `prof-graph-before-10000.txt` (af016c40...), the runs'
JSON in `prof-run-before1c-1000.log`, `prof-run-before-10000.log`, the loads
in `prof-load-*.log`, all under planning/evidence/signed-post-linear-2026-09-26/.

## 2. The fix and its theorem (PRF-193)

books/owner-commit-carried.lisp `fn-ccar-sn-prepare-identity` stages through
`fn-pcar-stage-record` (books/owner-prepare-carried.lisp, the article
prepare's carried stage since hot-path-scans; now included by
owner-commit-carried) instead of `fn-spc-stage-record`.
`fn-pcar-candidatep` is `fn-sf-candidatep` with `fn-pcar-next-lower`, which
steps the history's spine to its last cons and computes one txid through the
concrete twin `fn-rcon-store-event-txid`; `fn-pcar-stage-record-is-stage-record`
(PRF-014) is its equality with no hypothesis. No new structure, no new
relation, no new Store field.

KEYSTONE `fn-ccar-sn-prepare-identity-stages-the-next-event-above-the-last-record`
(books/owner-commit-carried.lisp), hypothesis only that the prepare moved the
store: `(not (equal (fn-ccar-sn-prepare-identity s event) s))` implies the
result's files are `:record-staged`, the record candidate is EVENT, the
history and the node are unchanged, EVENT's sequence is `(len records)`,
`(+ 1 txid(EVENT))` is the frontier, and on a non-empty history txid(EVENT)
is above the txid of `(car (last records))`. Local lemma
`fn-ccar-next-lower-is-after-the-last-record`: the fold is one past the last
record's txid.

Host line: host/owner-host.lisp `fn-owner-prepare-identity` installs
`fn-ccar-ocfg-prepare-identity`, whose store step is the subject (comment
updated there). Re-proved over the new body, statements unchanged:
`fn-ccar-sn-prepare-identity-is-sn-prepare-identity-under-relation`,
`fn-ccar-ocfg-prepare-identity-is-ocfg-step-under-relation` (PRF-144), and
the guard verification of `fn-ccar-sn-prepare-identity`; downstream
books/owner-store-indexed.lisp `fn-osi-ccar-prepare-identity-keeps-indexed`
proves unchanged (the rewrite `fn-pcar-stage-record-is-stage-record` returns
the body to the reference stage).

Teeth (tests/acl2/store-events-carried-tests.lisp, "PRF-193"):
- Reachable positive witness: the reserved store reached by `fn-own-run`
  before the signed POST's composite (`*evct-reserved-s*`, a non-empty
  history): the prepare moves it, and every conjunct holds, the last-record
  bound included.
- Hypothesis removal (reachable): the owner's store before its four
  frontier observations (`fn-own-store *ospt-taken*`, not `:reserved`): the
  prepare leaves it unchanged (the hypothesis fails) and nothing is staged
  (the conclusion fails); and `must-fail` of the statement without its
  hypothesis.

## 3. Certification (persvati, the lane's REPL tree, w25 `acl2-literal`, 2 jobs)

Per the batch rule the lane submits no farm run. The one changed book was
admitted in the REPL (`proof_repl.py`, every event of the book), then
certified in the REPL tree so its dependents could load:
- `books/owner-commit-carried` alone, 3.0 s:
  planning/evidence/manifests/certify-20260926T154328Z-3575872.json.
- The books downstream that gain owner-prepare-carried's rules or open the
  changed function (owner-commit-ocl, owner-advance-carried,
  owner-open-carried, owner-offer-indexed, owner-recover-ocl,
  owner-checkpoint-open, owner-store-indexed), every one under 3.5 s:
  certify-20260926T154437Z-3587055.json.
- The rest of the 20 affected roots of owner-commit-carried
  (`certify_books.py --dry-run --affected-by`), the test books included
  (store-events-carried-tests with the teeth), every one under 3 s:
  certify-20260926T154510Z-3592253.json.

## 4. Native (hbox, tools/hbox_native.sh, the one module the brief names)

`tools/hbox_native.sh --label after-428ba1a5 --images developer,production
428ba1a58 tests.test_native_hybrid_author`: `OK (11 ran, 0 skipped)`,
status 0. Log sha256 0f61285c5000526b93623c31b4ea5a4c168dca8151a7e071e574e0a35d945582
(`/tank/fn/scratch/signed-post-linear/native-after-428ba1a5/logs/test-tests.test_native_hybrid_author.log`);
developer core 6a125f9c9acba0fa49813cf2ecbb04af4d153baca3b3af48e544bb579048e4a9.

## 5. Measured after (hbox, matched, interleaved)

`meas.sh`: the same two stores (N = 1,000 and 10,000, 32 signed in each), a
fresh copy per run, `prof_signed.py run` without the profiler, two rounds, in
the order before-1k, after-1k, before-10k, after-10k. Before: dev 6407de336's
developer image (`/tank/fn/scratch/throughput-gate/native-img-6407de336`,
core 8cd82dcc...; its owner-commit-carried.lisp and owner-host.lisp are
dev's byte for byte). After: 428ba1a58's developer image above. 15:52 to
15:53Z, load average 9.8 to 11.0 beside each row in `meas/summary.log`
(sha256 eb69d6ca...).

| N | image | signed owner CPU per POST (round 1 / 2) | signed median wall | unsigned owner CPU |
| ---: | --- | ---: | ---: | ---: |
| 1,000 | dev | 84.5 / 108.5 ms | 120 / 144 ms | 2.5 / 4.0 ms |
| 1,000 | lane | 67.0 / 92.5 ms | 103 / 123 ms | 3.0 / 4.0 ms |
| 10,000 | dev | 260.5 / 293.5 ms | 296 / 332 ms | 6.0 / 6.5 ms |
| 10,000 | lane | 91.0 / 93.0 ms | 126 / 128 ms | 6.5 / 6.5 ms |

(Owner CPU is /proc utime+stime at 100 Hz over 20 POSTs: 0.5 ms
resolution. The wall includes a floor of about 43 ms that the unsigned POST
shows too, on tmpfs, whose cause this lane did not examine.)

## 6. What remains (PKT-552), and PKT-330 (2)

PKT-330 (2), narrowed: the identity prepare's `fn-sf-next-lower` fold is
CLOSED (PRF-193); the article prepare had it closed by hot-path-scans'
`fn-pcar-stage-record`. Still open in (2): `fn-pcar-candidatep`'s
`(len records)` and the spine step to the last cons (pointer steps, no octet
read; under 0.1 ms at 10,000); the D25 check on the transit path
(`fn-owner-existing-action` -> `fn-rcl-existing-action` -> `fn-find-article`,
the list twin of post-identity-index's `fn-rclb-existing-action`, 0.5 ms at
10,000) and the node prepare's `fn-acceptedp` and `fn-retain-known-id-scanp`
under `fn-replay-apply-record` (about 3 ms at 10,000): post-identity-index's
subjects (2) and (3), shared, not duplicated here; and
`fn-bpi-node-record-committedp` on the BP path (not measured here).

PKT-552, the signed POST's per-request cost that is constant in N (about
65 to 90 ms owner CPU on this box), from the profile: `fn-article-parse-lines`
(28 ms a POST: `fn-article-add-fold` appends per header line, and
`fn-hc-received-plan` parses the same carrier three times, plus the feed's
`fn-own-feed-article-of`), `fn-ccar-ocfg-complete` (16 to 19 ms),
`fn-replay-identity-step` (17 ms), the rest spread thin. Not attempted:
the brief's fix was the linear term.

## Assurance chain

Native entry host/native/owner.lisp `fnn-owner-identity-commit` (from
`fnn-owner-attempt-transit`, the served POST's attempt) -> host/owner-host.lisp
`fn-owner-prepare-identity` -> executed ACL2 subject
`fn-ccar-ocfg-prepare-identity` / `fn-ccar-sn-prepare-identity`
(guard-verified under `fn-sn-statep`, which `fn-ocl-relation` carries) ->
representation: `fn-pcar-stage-record` reads the last record through the
concrete twins, equal to `fn-spc-stage-record` with no hypothesis ->
refinement `fn-ccar-sn-prepare-identity-is-sn-prepare-identity-under-relation`
and `fn-ccar-ocfg-prepare-identity-is-ocfg-step-under-relation` (PRF-144) ->
maintained relation `fn-snt-relation` (through `fn-own-relation`; established
at observed open, preserved by the owner transition family; PKT-330 (4)'s
reconfigured-owner gap is unchanged by this lane) -> behaviour: PRF-193's
keystone (what is staged and what it is compared with), PRF-117 and
`fn-sr-a-signed-retry-is-already-stored` cited unchanged -> observed: the
native module and the table above.

## Not done, and why

- No after profile: the owner CPU is flat in N within the box's noise, and
  the constant terms are named from the before profile (PKT-552).
- The throughput gate's signed row was not re-run (the batch runs the gate).
- Fixtures registered (the stores measured above, with their keys and
  probes): hbox:/tank/fn/scratch/fixtures/signed-n1000-2k-32 (SHA256SUMS
  sha256 5fc72d2c...) and signed-n10000-2k-32 (2b2f27c3...); `run` writes
  beside the store it copies, so copy the fixture directory first.
