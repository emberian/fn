# w11/durable-evidence: a certification claim a reader can check

HEAD of the lane: `w11/durable-evidence` off dev `5698648`, merged dev
`3a2640c` (after `w11/phantom-cites` landed). `make check` exits 0.

## The gap

Every certification claim in this tree cites a run directory under
`build/acl2/certify-<UTC>-<pid>/`. `build/` is ignored (`.gitignore:6`), so
the directory exists only on the machine that ran it, and each of the three
places it can live is deleted as routine housekeeping: a lane worktree under
`build/lanes/`, a farm root under `/home/ember/fn-lanes` or
`/tank/fn/lanes`, and a gate directory under `$HOME/fn-gates` or
`/tank/fn/gates`.

Swept at dev `5698648`: **314 run ids are cited in tracked files, the oldest
from 2026-09-19, and not one of them resolved in the checkout.** A reader of
this repository at any revision could not check a single certification claim
it makes. This is not a lane's failure: each one recorded its evidence
honestly and named the directory it had. Nothing kept it.

## What the manifest carries, and what it did not

`manifest.json` is the claim. It already carried the requested books
(`requested_books`, `requested_before_filter`, `affected_by`, `closure`), the
expected and observed `FN_CERTIFY_SUCCESS` markers, the per-book verdict
(`book_results`, `book_failures`, `acl2_exit_codes`) and wall seconds, the
start order and slot waits, the source and certificate SHA-256 digests before
and after, the forbidden-facility audit, the runner and reader digests, the
ACL2 executable and its digest, `acl2_version`, the host Lisp banner,
`platform`, `python`, `timeout_seconds` and the cache outcome.

It did **not** carry the run's own identity. A manifest that has left its
directory behind cannot say which run it is, on which box, of which revision.
Added at the producing end (`tools/certify_books.py`), not in a second file:

| field | why |
| --- | --- |
| `run_id` | the token every citation uses; it was only the directory name |
| `hostname` | `platform` said `Linux-6.x-x86_64`, which is both boxes |
| `tree` | which worktree, lane or gate produced it |
| `git_revision`, `git_branch`, `git_dirty` | the digests say WHAT was certified; this says where to find it. `None` when the tree is not a repository, as a mirrored farm root may not be |
| `started_utc`, `finished_utc` | the stamp was only in the directory name, and to the second of start |

The archive adds two more: `run_id` if the producer predates this lane, and
`archived_from` = `<host>:<absolute run directory>`, which is where the log
was left. **The logs are not committed**: `certify.log` is the bulk, is not
the claim, and dies with its directory. `.cert` files stay absent as before.

Still not carried, and worth someone's decision: the ACL2 *system books*
revision (`ACL2_SYSTEM_BOOKS` is recorded as `null`), and the Makefile root
list the run was selected from.

## Where manifests live and who writes them

`planning/evidence/manifests/<run-id>.json`, flat, keyed by run id alone:
no box, lane or gate in the path, because the box, the lane and the gate are
exactly the things that get deleted. 139 manifests, 864 kB packed.

Three tools write it, at the three points a manifest reaches this laptop:

- `tools/certify_books.py` — `record()` replaces every `write_json` of the
  manifest, so a refusal before ACL2 starts is archived too.
- `tools/farm.py wait` — after the evidence rsync, with `archived_from`
  naming the *remote* root, since the fetched copy under `build/` is itself
  ephemeral.
- `tools/verdict.py` — the gate manifest now travels home inside the harvest
  JSON (`manifest_json`, popped before the evidence table is rendered)
  instead of waiting on the box for a reaper. This is the most perishable
  evidence the project keeps and the one `planning/evidence/verdict-*.md`
  cites.

`planning/evidence/manifests/*.json` is ignored and a manifest is tracked
with `git add -f`, which `python3 tools/evidence_manifests.py sync --add`
does for exactly the runs a tracked file cites. **Committing a manifest and
citing its run are one act**: an exploratory run nobody cites stays out of
the history, and `git status` in a lane worktree stays readable.

`tools/evidence_manifests.py` also has `harvest --host persvati|hbox` (one
ssh, one bounded `find`, one tar stream) and `check`, which is in `make
check`. `check` compares cited ids against `git ls-files`, not the disk: an
archived-but-unstaged manifest does not answer a citation, because what a
reader can verify is what is committed.

It fails on a **newly** cited run with no committed manifest and tolerates
the recorded backlog in `planning/evidence/manifests/LOST.txt`. `--strict`
fails on those too, and is the flag to turn on once the backlog is empty.

`tools/cite_check.py` (landed on dev from `w11/phantom-cites` while this
lane ran) is the same family for repository paths and says in its own words
that it "does not read `build/`" — which is exactly where these citations
point. The two are complements, not duplicates: one asks whether a path
exists, the other whether the evidence behind a claim was ever kept. Folding
them is reasonable later; the questions are different enough that they are
two files today, as `teeth_check`/`transcribe_check`/`session_depth` are.

Tests: `tests/test_evidence_manifests.py` (10 cases), plus
`test_the_run_names_itself_and_is_filed_where_a_reader_can_open_it` in
`tests/test_certify_runner.py` and
`test_the_gate_manifest_is_filed_where_a_reader_can_see_it` in
`tests/test_verdict.py`. No ACL2, no network.

## Recovery: 139 of 316 kept, 177 gone for good

| source | cited manifests recovered |
| --- | --- |
| this laptop, `build/acl2` and `build/lanes/*/build/acl2` | 42 |
| persvati, `~/fn-lanes` and `~/fn-gates` | 57 |
| hbox, `/tank/fn/lanes` and `/tank/fn/gates` | 40 |
| **committed** | **139** |
| **gone from all three** | **177** |

(941 distinct manifests exist across the four stores; only the cited ones are
committed. 34 run ids are held in two places and every one is byte-identical
in both, so no run id collision exists today.)

**The 177 are named, one per line with the file:line that cites each, in
`planning/evidence/manifests/LOST.txt`.** No citation was edited and no claim
was softened. Each row is a claim a reader cannot check; its lane owner
re-runs the certification or walks the claim back, and deletes the row.

Nine of them are **load-bearing** in the `cite_check.py` sense — an evidence
citation inside `books/`, where a reader is deciding whether to trust a
theorem — and should be triaged first:

- `books/scheduler-invariants.lisp` lines 133, 517, 652, 766, 811, 814 cite
  `certify-20260920T011543Z-94761`, `certify-20260920T014616Z-7729`,
  `certify-20260920T024820Z-15346`, `certify-20260920T024925Z-16147`
  and `certify-20260920T024955Z-16659`, for a six-minute measurement and
  for why four rules are withdrawn. Owner: the scheduler/core cluster.
- `books/nntp-effects.lisp` lines 172, 338, 355 all cite
  `certify-20260920T010731Z-93121`. Owner: nntp.
- `books/tcpcl-octets.lisp` lines 1232, 1245 cite
  `certify-20260919T234310Z-5770` and `certify-20260920T005346Z-77003`.
  Owner: substrate/tcpcl.
- `books/nntp-overview.lisp:33` cites `certify-20260919T215431Z-1323` for an
  if-split count of 2056. Owner: nntp.

The rest are prose: 22 in `planning/deputies/BOARD.md`, 17 in
`HANDOFF-w3-reader-profile.md`, 11 in `LANEDUMP-crash-fidelity.md`, 10 in
`LANEDUMP-assurance-tooling.md`, and one to eight each across 46 other files
including `docs/implementation.md:103`,
`tests/evidence/2026-09-18-article-work.json` and
`tests/evidence/2026-09-19-wave1a.json`.

## The check has already earned its place

Merging dev `3a2640c` brought `planning/evidence/twonode-feed-w11-2026-09-20.md`,
which cites two runs at lines 80 and 131. `make check` refused the tree
within a minute of the merge. Neither run was on this laptop — the
`w11-twonode-feed` worktree had been removed here — and both were still on
persvati under `/home/ember/fn-lanes/w11-twonode-feed`.
`harvest --host persvati` brought them home and the tree went green. That is
the whole failure mode, reproduced and repaired in two commands, and it is
why the check fails rather than reports.

## What landing it cost, measured

Two merges in a row produced eight newly cited runs and the check refused
the tree both times.

| merge | new citations | where the manifest was |
| --- | --- | --- |
| dev `3a2640c` into the lane | 2, in `planning/evidence/twonode-feed-w11-2026-09-20.md` | persvati only; the lane worktree was already removed here |
| the lane into dev | 6, in `HANDOFF-w11-bytestore-k2.md` and `BOARD.md` | `build/lanes/` here; neither box had a copy |

All eight were recovered, in one command each. Both cases are the failure
mode: in the first the laptop copy was already gone, in the second the box
copies never existed. Neither would have survived the week. So `check` names,
for each missing run, whether it is still under `build/` on this laptop, and
the repair at merge time is:

    python3 tools/evidence_manifests.py sync --add
    python3 tools/evidence_manifests.py harvest --host persvati   # if needed
    python3 tools/evidence_manifests.py harvest --host hbox       # if needed

## Next global step

1. **The 177 rows belong to lanes, not to this one.** Their owners re-run the
   certification (the manifest for the re-run is archived automatically now)
   or walk the claim back. The nine inside `books/` first.
2. **Turn on `--strict`** in the Makefile once `LOST.txt` is empty. The line
   is already written with that in mind.
3. **Sweep the other harnesses.** `tools/twonode_gate.py`,
   `tools/scale_gate.py`, `tools/inn_lab.py`, `tools/deploy_gate.py` and
   `tools/tcpcl_lab.py` write evidence records under `build/` too, and
   `planning/evidence/*.md` cites those directories by path. This lane fixed
   the certification family only; the same argument applies verbatim to the
   harness family, and `cite_check.py` does not read `build/` either.
4. **Consider folding `evidence_manifests.py check` into `cite_check.py`**
   when someone owns both. The run-id sweep is 40 lines of the 300; the
   archive and the producing points are not, and should stay where they are.
5. **A box sweep before a reaper runs.** `harvest --host <box>` is cheap
   (one ssh, a few MB) and finds only manifests. Running it before a gate
   reap or a lane-root cleanup costs seconds and is the difference between
   139 and 177.
