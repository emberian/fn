# w11/fault-tests — the two unowned clusters of the 2026-09-20 gate

Branch `w11/fault-tests` from `dev` `3a2640c`. Source of the work:
`~/fn-gates/dev-e4fb8bc/pytests.log` on persvati (601 tests, 9 failures, 11
errors, 13 skipped, 23m51s). No assertion was weakened; every expected value
below was printed by the real host and then written down.

## 1. Verdict per test: the test was wrong, the machine was right

Four distinct drifts, all of the same shape — a producer changed and the
consumer that spells the producer's interface **in a Python literal** was not
reached by the change.

| test | who was wrong | the drift |
| --- | --- | --- |
| `test_workflow_faults` ×3 | the test | `4ec3541` made `decode_inbound` a 3-tuple; three expected values stayed at two |
| `test_served_differential` ×7 | the test | `d484e9a` gave `fn-served-open` a 7th formal; the model side's call is a string |
| `test_deploy_gate.DryRunTests` | the test | a revision fallback for a tree whose `git archive` cannot run |
| `test_four_node_lab` budget | neither | a `.get` default that reads as a budget overrun |

### 1.1 The three durability cuts (`tests/test_workflow_faults.py`)

`4ec3541` ("Key inbound staging by ACL2 bundle identity") added the identity
field to the FNBI frame. Its diff updated the expected tuple in
`test_exact_inbound_retry_after_delete_failure_is_idempotent` **and** the
3-element unpack of `inbound_items` in the other three, and left those three
expected `decode_inbound` values at two elements. One file, both shapes, one
of them passing — which is what says test drift rather than a recovery defect,
before anything is run.

Re-derived by a probe that reproduces each cut's own setup (kept in the
session scratchpad, not committed; it is the three `setUp` bodies plus
`print`). At all three cuts the host rediscovers **exactly one** inbox item,
replays nothing (`open()` → `()`), and keeps the identity:

```
lost BPA-delete reply    ('bid-restart', <IDENTITY>, b'restart-payload')
fsync_dir error at link  ('bid-link',    <IDENTITY>, b'linked')
SIGKILL-equivalent cut   ('bid-crash',   <IDENTITY>, b'crash-payload')
      (`os._exit(93)` inside `fsync_dir`, after the link and before the
       directory barrier; `exitcode == 93` observed)
```

The assertions now carry that **and** the identity that `inbound_items`
returns, which all three discarded as `_identity`: rediscovering the exact
durable frame includes rediscovering the key reconciliation compares on, so
the fix is strictly stronger than what drifted. `tests.test_workflow_faults`
10/10 in 18.1 s.

**No recovery defect was found.** The claim these three encode — a process
killed at a named barrier rediscovers what was durable and nothing more —
holds on the current host, byte for byte.

### 1.2 The served differential (`tests/test_served_differential.py`)

Seven ERRORs, all `FN-SERVED-OPEN takes 7 arguments ... it is given 6`.
`d484e9a` gave `fn-served-open` a trailing AUTHINFO policy and updated its two
Lisp callers (`host/reader-host.lisp:137`, `host/native/reader-model-host.lisp:34`);
the model side of the differential spells the same call in a Python string, so
no Lisp-side change reaches it. The model form is now `fn-reader-reset` spelled
out, `(fn-auth-open-config)` included. 7/7 in 6.4 s,
`test_whole_transcript_agrees` sees `211 1 1 1 fn.letters` again.

**This mattered more than seven counts.** An arity error in a differential is
indistinguishable from the two sides disagreeing, which is the one thing it
exists to detect; the bridge host and `books/served` had no divergence check
running from `d484e9a` (2026-09-20) until now.

### 1.3 The native differential RUNS: 7/7, and `books/bp-node` was not why

**Outcome: it runs.** `tests.test_native_served_differential` is 7/7 in
**1.7 s** against a `build/fn-host` built in this worktree — the native host's
production listener and `fn-served-run` agree byte for byte on all seven
transcripts, including the bytewise partition and the UTF-8 split, and
`test_whole_transcript_agrees` sees `211 1 1 1 fn.letters`. This is the first
run of that module on this tree; it had been skipping.

Before the image existed it did **not** error either. It skipped in
`setUpClass`, naming the image and the script:
`native host image missing: <root>/build/fn-host (tools/build_native_host.sh)`.

The premise that `books/bp-node` blocks it is wrong for this test.
`tools/build_native_host.sh` defaults to `host/native/build.lisp`, which has no
`books/bp-node` line; only `host/native/build-dtn.lisp:44` includes it, and
nothing in `tools/`, `tests/`, `bin/` or the Makefile selects that variant
(`FN_NATIVE_BUILD` is set by hand, in two evidence records). So
`w11/bp-node`'s open guard conjecture blocks `build/fn-host-dtn` and not
`build/fn-host`.

What blocked it was certificates. Of `host/native/build.lisp`'s 16
`include-book` roots, 13 installed from the cache and **`books/nntp`,
`books/served`, `books/nntp-effects` did not** — the `w10/auth-served` change
rebuilt their closure keys. Certifying just those three fails at their own
dependencies (`nntp-responses`, `nntp-invariants`, `nntp-post` had no
certificate either): `build/acl2/certify-20260921T015314Z-72542`, the failed
attempt, manifest filed.

**The recipe, which is what this lane then did** (30 minutes end to end, of
which the laptop did about ten):

```sh
python3 tools/farm.py submit persvati --jobs 6 \
    --remote-root /home/ember/fn-lanes/w11-fault-tests --closure \
    books/nntp books/served books/nntp-effects
    # -> run-20260921T020155Z-a78d: installed 121, kept 68, uncached 88
python3 tools/farm.py wait persvati run-20260921T020155Z-a78d   # exit 0
python3 tools/certs.py install        # the three land; --remote-root does not
                                      # exist on the laptop, so they install
python3 tools/certify_books.py books/frame-trailer   # new from w11/one-owner,
                                      # reached through host/*-host.lisp, not
                                      # through build.lisp's include list
tools/build_native_host.sh                           # 279 M core
python3 -m unittest tests.test_native_served_differential -v   # 7/7, 1.7 s
```

`books/frame-trailer` is the trap to remember: `tools/build_native_host.sh`
refuses on an uncertified book, and the host files it `ld`s pull in books that
appear in **no** `include-book` line of `build.lisp` — `frame-trailer`,
`anchor-invariants`, `crypto-attach`, `peer-config`, `provenance-codec`,
`store-sweep`. Certify by `grep -h include-book host/*.lisp host/native/*.lisp`,
not by the build script's own list. (The BOARD's `w9/dtn-e2e` note says the
same thing about the anchor books; this is the general form.)

## 2. Two findings handed to owners, not patched here

### 2.1 A gate tree has no repository, and two harnesses shell out to git

`~/fn-gates/<tree>-<rev>` on persvati is a `git archive` extract. Reproduced
exactly, by extracting this branch to a scratch directory and running the two
modules there.

* **`tools/deploy_gate.py` `LocalHost.deploy`** pipes `git archive <commit>`
  into tar, so the dry run cannot ship anything from such a tree. The fixture's
  fallback to the literal `0123456789abcdef0123456789abcdef01234567` was
  written for this case and never worked: it produced
  `CalledProcessError(128, ['git','archive','0123…01234567'])` in `setUpClass`.
  **Fixed here, test-side:** a loud skip on the structural condition (no
  repository at `ROOT`), never on a failure string, so a real checkout never
  skips. Verified: skips in the extract, 17/17 in a checkout.
  *For the deploy-gate owner:* whether the dry run should be able to ship a
  worktree at all is yours. It ships a **commit** today, which is the right
  default; a `--from-worktree` would be a real semantic change.

* **`tests/bp-dtn7/run_four_node_lab.py:422`** — `subprocess.check_output(
  ["git","rev-parse","HEAD"], cwd=ROOT)`, unguarded, inside `run_lab`'s
  `report.update({...})`. It is the **single** root cause of all six four-node
  failures and two errors of that gate: the lab dies before it runs, and eight
  tests then report `KeyError: 'articles'`, `{} is not true`, `0 != 1` and so
  on. Reproduced in 0.085 s in the extract.
  *For the lab's owner, the exact form asked for:* the revision is provenance
  for `evidence.json` and must not become `"unknown"`, so take it from the
  caller when git cannot answer — the gate knows the commit, it is in the
  directory name — e.g. an optional `--revision` / `FN_GATE_REVISION` read
  before the `git rev-parse`, and a refusal naming the missing revision when
  neither is available. **Not a skip:** `tests/test_four_node_lab.py:56-62`
  records why that file has no blessed failure, and this lane respected it.

### 2.2 The budget is right; 300.0 was a default, not a measurement

`test_the_mock_bpa_run_fits_the_five_minute_budget` failed as
`300.0 not less than 300.0`, which reads as a run that outgrew its budget.
It was `self.report.get("seconds", LAB_BUDGET_SECONDS)` returning its own
default because the lab (above) produced no report at all.

**Measured on a real checkout, laptop, this branch:**
`python3 tests/bp-dtn7/run_four_node_lab.py` →
`{"status": "passed", "seconds": 74.0}` — four times the headroom, not none.
The module is 9/9 in 152.3 s. The assertion now asserts `"seconds"` is present
first and prints the lab's `error` when it is not, so the two are never again
confused. Neither the budget nor the path is wrong.

## 3. Ran, and evidence

| what | where | result |
| --- | --- | --- |
| `tests.test_workflow_faults` | this worktree | 10/10, 18.1 s |
| `tests.test_served_differential` | this worktree | 7/7, 6.4 s |
| both of the above, after merging `dev` `664711e` | this worktree | 17/17, 12.1 s |
| `tests.test_native_served_differential` | before the image | skipped 1, loudly |
| `tests.test_native_served_differential` | against `build/fn-host` | **7/7, 1.7 s** |
| `books/frame-trailer` certify | this worktree | passed, `certify-20260921T020920Z-2417` |
| `tools/build_native_host.sh` | this worktree | `built build/fn-host (279M core)` |
| farm closure, 88 uncached books | persvati | `run-20260921T020155Z-a78d`, exit 0 |
| `tests.test_deploy_gate` | this worktree | 17/17, 33.7 s |
| `tests.test_deploy_gate` | `git archive` extract | 10 ran, DryRunTests skipped loudly |
| `tests.test_four_node_lab` | this worktree | 9/9, 152.3 s (1 optional skip) |
| `tests.test_four_node_lab` | `git archive` extract | 6 failures, 2 errors, one cause |
| four-node lab, direct | this worktree | `passed`, `seconds: 74.0` |
| `make check` | this worktree | exit 0 |
| `tools/ledger.py --write` | this worktree | no count changed |

The four files this lane changed are Python tests. The one book it certified,
`books/frame-trailer`, it certified to build an image and not to close a
proof; nothing here changed a definition or a theorem.

## 4. One measurement worth carrying

The four-node lab is **not concurrency-safe against another ACL2 user on the
same laptop**. Run once beside `make check` it died with
`tools.run_store.StoreError: ACL2 bridge call marker did not precede its
prompt`; run alone, immediately after, it passed in 74.0 s. If a gate ever
runs it beside anything else, that is the failure to expect, and it is not the
lab's logic.
