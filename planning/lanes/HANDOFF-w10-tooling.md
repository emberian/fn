# HANDOFF w10/tooling — three tooling defects, measured before and after

Branch `w10/tooling` off dev `8da8217`, merged with dev afterwards. No ACL2
certification beyond the one small reproduction below (two runs of a 22-book
closure at `--jobs 2` on persvati, 144 s of certify wall each).

## 1. The farm cache was not seeded by a failed run

**The cause was the runner, not `wait`.** `tools/certify_books.py` published
to the certificate cache inside `if success:`, and `success` is a statement
about the whole requested batch. Every wide run on this tree exits non-zero
while any root carries an open theorem, so no wide run has ever seeded a box
during the run; `tools/farm.py wait`'s post-run sweep was the only path, and
it did not run when `wait` timed out (it returned 3 without fetching), when
the run was killed, or when nobody waited.

The board's earlier reading — that the sweep does not publish — is not what
the box shows. Running the sweep by hand under
`/home/ember/fn-lanes/w10-provenance` reports `3 manifests; published 0,
already cached 157`, and persvati's cache holds exactly 157 `run` entries for
that origin. The provenance lane's repeated `uncached 181..187` is mostly a
second thing: it was editing `books/retention.lisp` and `books/node.lisp`,
which sit in the closure of about 180 books, so those books' cache keys
changed with each edit.

Measured, isolated cache `/home/ember/fn-certcache-w10tooling` (empty per
arm), remote root `/home/ember/fn-lanes/w10-tooling-repro`, closure over
`books/byte-store-scan` (fails on dev) plus its 21 certified dependencies:

| arm | run | certified | exit | cache entries | next submit's install |
| --- | --- | --- | --- | --- | --- |
| before | `run-20260920T203028Z-d411` | 21 of 22 | 1 | 0 | `installed 0, kept 0, uncached 267` |
| after | `run-20260920T204249Z-470f` | 21 of 22 | 1 | 21 | `installed 21, kept 0, uncached 246` |

`planning/evidence/farm-cache-failed-run-2026-09-20.md`. The scratch cache
and remote root were removed from persvati afterwards.

Changed: the runner publishes a pair the moment its book certifies and
sweeps at the end whatever the verdict was; `wait` fetches and publishes on
its timeout path and says what it left running; a silent cache sweep and a
missing local manifest are reported; `submit`/`wait` take `--cache` for the
cache ON THE HOST.

**What that removed had to be replaced.** Publishing only after a wholly
successful run let the run-wide `sources_unchanged` check stand in for a
per-pair one. `certs.publish` now refuses a book whose whole include closure
no longer hashes to what the manifest recorded: a dependency edited mid-run
leaves the book's own source untouched, and the entry would have been a real
certificate filed under a key describing source it was never produced from.
A case in `tests/test_certs.py` and one in `tests/test_certify_runner.py`.

## 2. Two gate lock schemes on each box

The hand gates hold `flock` on one file for their whole certification:
`$HOME/fn-gates/.gate.lock` on persvati, `/tank/fn/gates/.lock` on hbox
(`exec 9>LOCK; flock 9` at the top of `gate.sh`). `tools/verdict.py` kept an
atomic `mkdir` on `.verdict.lock` beside the same directories, and two
schemes that cannot see each other are not a lock.

Now: the gate script `verdict.py` writes opens the same file and holds
`flock 9` across `make certify`, the suite and the publish; before launching
anything `verdict.py` asks the box (`flock -n LOCK true`) and refuses with
the holding process named. `--wait-for-lock` queues. `--force-unlock` and
`--stale-hours` are gone — a flock dies with its holder. Probed live
2026-09-20: hbox refused, naming `gate.sh 1151069 / make / python3` holding
`/tank/fn/gates/.lock`; persvati answered free. It is a CERTIFICATION lock:
farm runs and the four harness fibers do not take it.

`--reuse-gate [REV]` now reads a hand gate. It asked for `gate.done`, which
only its own gates write, so every hand gate fell through to the path that
ships a commit and certifies. It reads the shape both kinds share
(`certify.log`, `pytests.log`, `publish.log`,
`build/acl2/certify-*/manifest.json`), names any that is absent, and ships
and launches nothing.

Tables produced by reuse, neither starting a certification:

- `planning/evidence/verdict-reuse-persvati-dev-909e055-2026-09-20.md`
  — 232 of 257 roots, suite FAILED of 490 (f=17 e=66).
- `planning/evidence/verdict-reuse-hbox-dev-d50c392-2026-09-20.md`
  — 223 of 238 roots, suite FAILED of 444 (f=14 e=74).

hbox's `dev-2505a8f` was still certifying at 17:12 UTC. When it finishes:
`python3 tools/verdict.py <commit> --host hbox --only gate --reuse-gate 2505a8f`.

**A third defect found while testing that**: the per-root row came from
`acl2_exit_codes`, and the certify driver ends in `(quit)`, which ACL2
reaches whether or not the inner `ld` returned on a failed `certify-book`.
On `dev-909e055` the exit codes name 1 failing root and `book_results` names
25 — the table said "256 of 257 certified" for a gate that certified 232.
Fixed to read `book_results` with a fallback, recording which it used. The
gate row's pass condition also compared `status` to `"certified"`, a word
nothing writes, so a perfect gate would have reported `fail`. **Every
verdict table written before today is wrong in the same direction and should
be re-read with `--reuse-gate`.**

## 3. Evidence written into the wrong checkout

The cause is neither a `git rev-parse` nor a hard-coded path:
`ROOT = Path(__file__).resolve().parents[1]` reaching the evidence path via
`--repo default=str(ROOT)`. That answers where the SCRIPT lives, so running
the main checkout's copy of a harness writes into the main checkout whatever
tree you are working in; a relative `--evidence` was worse and followed the
process's working directory.

`deploy_gate.repo_root()` answers `git rev-parse --show-toplevel` from the
working directory — from a secondary worktree, that worktree — checked to be
an fn tree and falling back to the harness file's own tree.
`deploy_gate.evidence_path()` anchors the default name and a relative
`--evidence` on it; an absolute path is still taken as given and `--repo`
still overrides. Applied to `deploy_gate.py`, `twonode_gate.py`,
`inn_lab.py`, `scale_gate.py`, `verdict.py`, `tcpcl_lab.py` (`--image`, an
input read from the wrong tree) and `tests/campaign/campaign.py` (`--json`).
`inn_lab` also shelled out to `ROOT / "tools/farm.py"`, and `farm.py` mirrors
the worktree IT lives in, so the main checkout's copy would have certified
the main checkout while the lane waited for its own books.

`tests/test_deploy_gate.py::RepoRootTests` builds a real repository with a
real secondary `git worktree` and resolves from inside it, and refuses a
reintroduced `--repo default=str(ROOT)` in any of the five gates.

## Found and not fixed

- **`--closure` re-certifies its whole dependency list unconditionally.**
  `certify_books.with_dependencies` has no skip for a book whose installed
  certificate is current, so the 21 pairs item 1 now caches save a
  `--closure` run nothing today; they save a run that names roots WITHOUT
  `--closure`, whose dependencies must already carry certificates. Making
  the skip safe means recording a skipped book distinctly in the manifest
  (it is `cached`, not `passed`) — a separate change with its own evidence.
- **`tests/test_inn_lab.py` errors in `setUpClass`** (`inn_start` parses no
  `pid=` out of the fake nnrpd). It does the same on dev at `8da8217`; this
  lane did not touch that path.
- **A Python test that runs `git commit` blocks on the 1Password signing
  agent** under the developer's global `commit.gpgsign`, with output
  swallowed and no timeout. The new fixture passes
  `-c commit.gpgsign=false` and a 60 s timeout. The same agent refused this
  lane's own commits (`1Password: failed to fill whole buffer`), so two of
  the three are unsigned.

## What ran

`make check` before every commit (`Scaffold OK`). Narrow suites:
`tests.test_farm` (22), `tests.test_certs` (30), `tests.test_certify_runner`
(25), `tests.test_verdict` (15, new), `tests.test_deploy_gate` (16),
`tests.test_twonode_gate`, `tests.test_scale_gate`. No suite-wide run and no
`make certify`.
