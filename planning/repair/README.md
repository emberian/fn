# The repair ledger

One JSON file per item in `items/`; `repair.py` reads and writes them. `STATUS.md` is generated (`repair.py report`).
Sources of the findings are in `sources/`; each item's `detail` names its source section, and sweep items carry the
quoted `evidence`, the failure `scenario`, the proposed `fix` and the `reviewer` note.

## Working an item (especially for burn-down lanes)
1. `repair.py show ID` and re-read the cited code. Wrong or already fixed: `repair.py set ID state=refuted note="why"`.
2. `repair.py claim ID --files 'path/one.lisp,tests/test_x.py' --test 'python3 -m unittest tests.test_x'`
   (the files the fix may touch, and a test that fails before the fix; `--native MODULE` if it changes runtime
   behavior, so the runner's batch native run covers it).
3. Fix, commit with the item id in the message.
4. `repair.py verify ID --base <the commit you started from>`: refuses changes outside the scope, the forbidden zones
   (`forbidden.txt`), diffs over the budget (60 lines unless the item sets `budget`), a missing item id in the commit
   messages, or a test that does not fail at the base and pass at the head. Fix or escalate until it exits 0.
5. `repair.py set ID note="READY <sha>"`; the runner sets `ready` on merging into origin/next and `landed` on dev.
