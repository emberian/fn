# Deputy report: assurance tooling

HEAD at start: `0a16592` (dev). Branch `dep/tooling`, worktree
`build/lanes/dep-tooling`. No book was touched. No ACL2 process was started by
this lane.

## What shipped

**`tools/certs.py`** (reworked on `dep/tooling2` after the cache was
poisoned; the first version keyed on the book's own content and trusted any
`.cert` beside a book). `publish` now caches a pair **only** against a
certification manifest (`--manifest PATH`, else every
`build/acl2/certify-*/manifest.json` under `--root`): the source must still
hash to that run's `source_digests_sha256` (and `_after` when recorded) and
the certificate to its `certificate_digests_sha256`, from a manifest whose
status is `passed`. There is no other publish path, so a stale certificate
beside a freshly merged source is `unverified`, never cached. The key is the
**closure hash**: sha256 over the sorted `<path>:<sha256>` listing of the book
and its whole local include closure (`include-book` resolved relative to the
including file, `:dir :system` ignored), so a changed dependency changes the
key of an unchanged book and the cache cannot report a hit ACL2 would refuse.
Each entry also records `origin_root`, the absolute worktree the run happened
in, because a certificate names its sub-books by absolute path: `install`
takes this worktree's own entry, else one whose origin does not exist on this
machine, else refuses (`foreign-local`) and removes a local pair that is
provably one of the refused ones. `farm.py submit --remote-root` plus `wait`
publishes under the remote path, which is the relocatable case.
`install` computes the same key and keeps a byte-identical local certificate;
`status` prints coverage; `valid_looking` accepts both ACL2 8.7's serialized
`#Z` format and the textual one; no rule anywhere depends on mtime. Entry meta
records the closure listing and the evidence directory. `certify_books.py`
publishes against its own in-memory manifest. Targets: `make certs-install`,
`make certs-publish` (`FN_CERT_REMOTE=hbox` also mirrors).
Tests (`tests/test_certs.py`, 19): `ClosureKeyTests` (a changed dependency
changes an unchanged book's key; `:dir :system` excluded; a missing dependency
raises), `PublishTests` (no manifest, edited source, replaced certificate,
failed manifest and a recorded closure error each publish nothing; both
certificate formats), `InstallTests` (whole-closure match, no false hit on a
changed dependency, a differing local pair replaced, a stale `.port` removed),
`StatusAndRemoteTests`.

**`certify_books.py --affected-by BOOK [--dry-run]`** — keeps only the
requested roots that are, or transitively include, a named book, in requested
(Makefile) order, through the ledger's include graph. An unknown target is
refused rather than silently selecting nothing. On this tree `--affected-by
books/policy.lisp` selects 3 of 181 roots, `books/cbor.lisp` selects 124.
Tests (`tests/test_certify_runner.py::AffectedByTests`): dry-run order, a deep
change selecting every root above it, only the affected books certified, an
unknown target refused.

**`tools/acl2_slots.py`** — a machine-wide cap. Every ACL2 the runner starts,
the version probe included, holds an exclusive `flock` on a file under
`~/.cache/fn-acl2-slots` (`FN_ACL2_SLOTS`, default 4 on darwin and 16 on
linux; `FN_ACL2_SLOT_DIR` for a private pool). A full pool waits and logs once
a minute; the manifest records `acl2_slots` and every `slot_wait_seconds`. The
lock is on the open file description, so a killed run leaks no slot.
Tests (`SlotTests`): one slot serialises four jobs with a fake ACL2 that
sleeps, and the waits are recorded; a pool above the job count does not
constrain the schedule.

**`tools/farm.py`** — `submit <host>` mirrors the worktree (excluding
`build/`, `.git/`) to the same absolute path and starts the runner detached
with its own log and status file, wrapped in `swarm-build` on hbox; `wait
<host> <run-id>` polls every 30 s, prints progress, gives up at a bound, then
rsyncs back the evidence directory and every new pair and publishes them
locally; `status <host>` lists runs. Tests (`tests/test_farm.py`) read the
exact commands through the `RUN`/`SLEEP` seams: `SubmitTests`, `WaitTests`
(including `test_wait_is_bounded_and_sleeps_between_polls`), `StatusTests`.

**Two ledger lints**, WARN in `ledger.py --check` and so in `make check`,
failing under `--strict`, counted in the generated ledger and listed under
`lints` in `ledger.json`. Current tree: **67 export-hygiene**, **24
teeth-form**, 91 total. Export hygiene flags an enabled equality between two
*different* one-argument applications, or a `consp`/`len` conclusion
backchained to a `len` hypothesis; `local`, `defthmd`, `:rule-classes nil` and
a non-local closing `in-theory (disable ...)` exempt. Teeth form flags a
`must-fail` whose `thm`/`defthm` statement mentions no constant. Tests
(`tests/test_ledger.py`): `ExportHygieneLintTests`, `TeethFormLintTests`,
`LintReportingTests`.

## Evidence

`python3 tools/ledger.py --write`; `make check` green (91 lint warnings);
`python3 -m unittest tests.test_certify_runner tests.test_ledger
tests.test_certs tests.test_farm -v` — 74 tests, OK, 13.5 s, no ACL2.
One file outside this lane changed: `specs/node-functionality.md` linked into
`build/lanes/w2-mutable-owner/specs/owner.md`, so `make check` passed only in
a checkout where that lane's worktree still existed. Unlinked the same way
`ce3301f` unlinked its siblings.

## Proposals (cross-cluster; not taken alone)

1. **`DEFAULT_BOOKS` in `certify_books.py` is a stale second copy of the
   Makefile's `ACL2_BOOKS`** — 118 entries against 181, missing `assumptions`,
   every `*-teeth-tests`, and the whole bp cluster. A bare
   `python3 tools/certify_books.py` therefore certifies a subset nobody chose.
   The runner already reads the Makefile through `ledger.makefile_roots()`.
   Owner: root. One-line change, but it changes what a bare invocation does.
2. **Slots for the long-lived hosts.** `tools/run_store.py` and
   `tools/run_reader.py` start ACL2 as a per-test server. They are the other
   half of "every ACL2-spawning tool", but several host tests start several
   servers at once, so capping them at 4 would deadlock those suites rather
   than pace them. They need either their own pool size or a test harness that
   knows the cap. Owner: whoever owns the host test suites.
3. **`--strict` as the gate for a cleaned cluster.** The two lints are WARN
   because 91 findings cannot be fixed by one lane. A cluster that has been
   cleaned could be listed in a per-book allowlist so its findings fail, which
   is what stops a cleaned book from silently regressing. Owner: root, with
   the deputy-scholar cycle.
4. **Publish from the farm, not only from the laptop.** `farm.py` sets
   `FN_CERT_CACHE` on the host, so a farm run fills that box's cache and
   `wait` fills this one, but nothing yet syncs persvati's cache to hbox's. A
   `certs.py pull <host>` is the missing half.
