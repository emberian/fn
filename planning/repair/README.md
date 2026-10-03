# The repair ledger

One JSON file per item in `items/`; `repair.py` reads and writes them. `STATUS.md` is generated (`repair.py report`).
Sources of the findings are in `sources/`; each item's `detail` names its source section, and sweep items carry the
quoted `evidence`, the failure `scenario`, the proposed `fix` and the `reviewer` note.

## Working an item (especially for burn-down lanes)
1. `repair.py show ID` and re-read the cited code. Wrong or already fixed: `repair.py set ID state=refuted note="why"`.
2. `repair.py claim ID --files 'path/one.lisp,tests/test_x.py' --test 'python3 -m unittest tests.test_x' --harness 'tests/test_x.py' --expect-failure 'tests.test_x.Case.test_behavior' --failure-message 'exact assertion message'`
   (the files the fix may touch, and a test that fails before the fix; `--native MODULE` if it changes runtime
   behavior, so the runner's batch native run covers it).
3. Fix, commit with the item id in the message.
4. `repair.py verify ID --base <the commit you started from>`: refuses changes outside the scope, the forbidden zones
   (`forbidden.txt`), diffs over the budget (60 lines unless the item sets `budget`), a missing item id in the commit
   messages, or a regression without the designated assertion failure at base and clean execution at head.
   Fix or revise the claim until it exits 0.
5. `repair.py set ID note="READY <sha>"`; during dev stabilization the integrator merges directly onto dev and records `landed` with its source receipt. The earlier `ready`-on-next state remains historical. Record outstanding native/proof work separately; source landing is not completion of that work.

## Runnable defect witnesses

`verify` runs one verifier-owned unittest observer at both immutable revisions.
It copies the declared `--harness` files from head into both throwaway worktrees,
so a new regression runs against the old implementation too. Every executed test
source must be declared; add test helper files to the harness when needed.
Harness files must be regular tracked files under `tests/`; product code is
never transplanted. Name unittest modules, classes or methods explicitly in the
command; shell commands and discovery are not accepted by this observer.

Base must produce exactly one assertion failure with the claimed test ID and
exact message. Both runs must execute the same test IDs and source bytes, and
head must pass them all. An import/API error, unavailable tool, timeout, skip,
expected failure, zero tests or a different assertion cannot supply defect red.
For example, write an assertion describing an absent API's intended behavior
instead of relying on the resulting AttributeError. `--timeout SECONDS` defaults
to 1800 and can be lowered for the regression.

For a trivial prose correction use `--doc-only 'reason'` instead of test options.
This exemption accepts only documentation paths (under `docs/` or `planning/`,
or the named top-level project guides), with document suffixes and no executable
or symlink mode changes. Code and test fixtures still need a runnable regression.
Scope, forbidden paths, line budget and commit-ID checks apply to both kinds.

The item records `semantic_ok`, the immutable revisions, harness/observer hashes,
the expected assertion and full base/head observations. These bytes are archived
and indexed under `planning/evidence/repair/`; `verify.evidence` gives the path
and hash. An archive outage is `evidence_outcome=unavailable` and prevents `ok`
without changing the semantic verdict. Commit the item and evidence index receipt.
Source `landed` receipts record ancestry; native/proof completion remains
separately evidenced. A passing observer still requires review that its assertion
actually describes the item's defect.
