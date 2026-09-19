# w3/parallel-certify

Branch `w3/parallel-certify`, branched from `dev` at `9321344`.
The work is one commit, `8548afc`; this line is the only thing after it.

## What changed

`tools/certify_books.py` gained `--jobs N` (default 1, env `FN_CERTIFY_JOBS`).
It certifies books concurrently subject to their local `include-book`
dependencies. `make certify` honours `FN_CERTIFY_JOBS` (`FN_CERTIFY_JOBS ?= 1`
in the Makefile, passed as `--jobs`).

### One reader, not two

`local_include_books` no longer uses a regular expression. It calls
`ledger.analyze_book`, the same s-expression reader that generates the ledger,
so the schedule and the ledger cannot disagree about what a book includes.
`tools/` is not a package, so the runner puts its own directory on `sys.path`.
Before the swap I checked both extractors over all 162 book sources in the tree:
identical results, so the source closure and therefore `source_digests_sha256`
are unchanged. The reader is stricter in the cases where they could differ (an
`include-book` inside a string or comment, an `:dir` spelled across a line), and
an unreadable source now fails the run instead of being silently skipped.

Because the closure now depends on a second file, the manifest records
`reader_sha256` and `runner_unchanged` covers both files.

### The schedule

- `local_closure` walks every book reachable through local `include-book`;
  a missing, escaping or unreadable include raises, and that failure path is the
  existing manifest-plus-exit-2 one. `:dir` includes are system books and are
  never in the closure.
- `cycle_through` refuses a cycle before any ACL2 starts, naming the path.
- `dependency_graph` maps each requested book to the requested books it must
  follow. An unrequested book is not an edge (nothing is writing its
  certificate this run) but is traversed, so a requested book reached only
  through unrequested intermediates is still an edge.
- `run_schedule` keeps at most `jobs` ACL2 processes alive in a
  `ThreadPoolExecutor`, picking ready books in requested order and submitting at
  most `jobs` at a time so a book that becomes ready never queues behind work
  that was merely ready earlier.

Why independent books do not race: each ACL2 writes only artifacts named for the
book it certifies (`<book>.cert`, `<book>.port`, the compiled file,
`<book>@expansion.lsp`), and a repeated book is now refused at argument parsing,
so no two processes write one path. Two books that both include the same
certified dependency only *read* that dependency's certificate and compiled
file; the scheduler already waited for the writing process to exit, and
concurrent readers of a file nobody is writing do not race.

A failed dependency still releases its dependents, because the sequential runner
also ran every requested book after an earlier failure and that keeps its
diagnostics. The dependents then fail on their own evidence — the first
measurement run below shows exactly this, an `ACL2 Error ... There is no
certificate on file` — and the pass rule is unchanged: one fresh nonce-tagged
marker and one certificate for every requested book.

### Evidence is unchanged

Markers, the combined log and the exit-code map are assembled in *requested*
order, never completion order, so the schedule cannot move them. Per-book logs,
drivers, the per-book timeout, digests before and after, certificate digests,
the forbidden-facility audit and the final pass/fail rule are untouched. New
manifest fields only: `jobs`, `jobs_effective`, `reader_sha256`, `start_order`,
`book_wall_seconds`, `certify_wall_seconds`. With `--jobs 1` the scheduler
starts books in exactly the requested order (the Makefile list is a topological
order — checked: 162 roots, no duplicates, no out-of-order edge).

## Tests

`tests/test_certify_runner.py` gained a `FakeRepository` harness: a throwaway
repository of generated books plus `FAKE_ACL2`, a shell script standing in for
the executable that echoes the driver's own success marker, writes the `.cert`,
and appends `start <book>` / `end <book>` to an event log. The real `main()`
runs in process against it with `ROOT`/`BUILD_ROOT` patched.

- `test_dependencies_finish_before_dependents_start_under_four_jobs` — every
  dependent's `start` follows its dependency's `end`, peak concurrency is
  above 1 and at most 4.
- `test_dependency_through_an_unrequested_book_still_orders_the_run`
- `test_include_book_cycle_is_refused_before_any_acl2_runs` — exit 2, no events.
- `test_a_failing_book_fails_the_parallel_run`
- `test_manifest_records_jobs_start_order_and_per_book_wall_time`
- `test_one_job_keeps_the_requested_order_and_the_same_manifest_fields`

`python3 -m unittest discover -s tests -p test_certify_runner.py`: 10 tests, OK
(4 pre-existing, 6 new). `make check` green.

## Measured

ACL2 8.7 on SBCL 2.6.8, 12-core laptop, all 162 Makefile roots,
`FN_ACL2_TIMEOUT_SECONDS=1800 FN_CERTIFY_JOBS=8 make certify`, this worktree.

I could not use a measured sequential baseline: a sequential run would take over
an hour and forty minutes and would fail on the same book. The comparison below
is the manifest's own per-book wall times summed — each certification is
single-threaded, so that sum is what one ACL2 at a time spends. It is a proxy,
not a stopwatch on a `--jobs 1` run.

| Scope | Sum of per-book wall | `--jobs 8` wall | Ratio |
| --- | --- | --- | --- |
| 160 roots, excluding the evolving-store pair | 4473 s (1 h 15 m) | 1263 s (21 m) | 3.5x |
| All 162 roots | 6273 s (1 h 45 m) | 3063 s (51 m) | 2.1x |

Two runs, reported honestly:

- `build/acl2/certify-20260919T143918Z-40457`: started at **load average 119**
  with other lanes running. Wall 4023 s, sum of per-book wall 11132 s.
- `build/acl2/certify-20260919T154722Z-89314`: started once the box was quiet,
  **load average 12.6** during (that is largely my own 8 ACL2 processes) and 6.5
  after. Wall 3063 s. This is the row in `docs/implementation.md`.

Both runs **failed**, both for the same single reason, and it is not this lane's
change: `books/bp-receiver-evolving-store-invariants` hit the 1800 s per-book
timeout in both, still advancing subgoals when killed, and on the quiet box
every other book roughly halved while that one stayed pinned at the ceiling.
A single book's proof is single-threaded and unaffected by `--jobs`, so this
batch cannot pass at `--jobs 1` either. 160 of 162 roots certified cleanly with
fresh markers and certificates under `--jobs 8`, which is the useful evidence
that the schedule does not change results. The prompt's 40-minute sequential
figure predates this book.

The failure mode is worth keeping: the dependent `tests/acl2/bp-receiver-evolving-tests`
ran after its dependency failed, as the sequential runner would have, and failed
on its own evidence with `ACL2 Error ... There is no certificate on file`. No
false green anywhere in the manifest.

## Open

- `books/bp-receiver-evolving-store-invariants` is by far the critical path and
  is the reason a `--jobs 8` gate cannot approach `wall = total / 8`. It is also
  the only book near the per-book timeout. Splitting it would help the gate more
  than more jobs would.
- The default `FN_ACL2_TIMEOUT_SECONDS` is still 600, which that book exceeds.
  That predates this lane; the runs here used 1800.
- `run_dir` is `certify-<second-resolution stamp>-<pid>` with
  `mkdir(exist_ok=False)`, so two runs in one second from one pid collide.
  Pre-existing; the tests avoid it with a per-run `BUILD_ROOT`.
