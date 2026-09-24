# Lane check-ratchet: handoff

Branch `lane/check-ratchet`, from dev 46f2660d.

## Files changed

- `tools/proof_cost.py`: ten-second ratchet (`--baseline`, `--write-baseline`,
  `--allow-regression`); unfiltered history mode exits 1 on failure;
  `--manifest` and `--host`/`--toolchain` views never fail.
- `planning/proof-cost-baseline.json` (new, generated with
  `--write-baseline --allow-regression` from the current history).
- `tools/certified_claims.py`: exit 1 on any warning; new manifest-citation
  failures; `--explain PRF-xxx`; exit 2 (was 0) when evidence is unreadable.
- `tests/test_proof_cost.py` (+3 tests), `tests/test_certified_claims.py`
  (+5 tests: no citation, absent citation, matching manifest passes (and a
  cited run that failed the book does not), stale digest, explain).
- `planning/proofs.json`: PRF-032, PRF-035, PRF-043 cite
  `planning/evidence/manifests/certify-20260924T070931Z-1040432.json`;
  PRF-043's progress note now says its old citation has a stale digest.
- `docs/proofs.md` (two paragraphs), `Makefile` (comments in `check`).

## Rules as implemented

- proof_cost: the baseline is keyed by book; the figure is the book's WORST
  current measurement over all hosts and toolchains (newest per
  book/host/toolchain at the current include closure). The check fails when a
  book is over 10 s and either not in the baseline or over its figure by more
  than 25%. A baseline book now under 10 s, or no longer in the root closure, is
  reported "improved; remove from baseline". A baseline book with no current
  measurement stays in the baseline. Without `--allow-regression`,
  `--write-baseline` drops improved books and lowers figures, keeps a figure
  (does not raise it) when the new number is within the 25% tolerance, and
  refuses to write at all (exit 1, printing each FAIL line) when a book would be
  added or would go past tolerance.
- certified_claims: a `certified` row must cite, in its `evidence` list, at
  least one `planning/evidence/manifests/*.json`; every cited file must exist;
  and for each event book some cited manifest must record `book_results[book]
  == "passed"` with `source_digests_sha256[book.lisp]` equal to the current
  digest AND no include-closure drift (`certs.closure_drift`). The last clause
  goes beyond the brief's "current digest" wording. All current rows meet it.

## Baseline

37 books. The three largest:
- books/store-node-invariants 124.853 s (hbox, certify-20260924T070931Z-1040432)
- books/bp-node-progress-guards 119.645 s (hbox, same run, verdict failed)
- books/consumer-event-index-store-invariants 95.203 s (hbox, same run)

1 current book is unmeasured (tests/acl2/consumer-event-index-tests, installed
only), which stays a warning.

## Certified rows (4 at 46f2660d; PRF-034 is no longer `certified`)

- PRF-032: cited no manifest. It now cites certify-20260924T070931Z-1040432
  (archived, hbox), which records books/store-files-invariants passed at its
  current digest and include closure. No farm run.
- PRF-035: cited no manifest. It now cites the same run for books/frame-trailer.
- PRF-043: its cited certify-20260921T062242Z-1643977 recorded books/feed-journal
  at digest 84ba8c34bfd1; the current digest is 4c7badb0de75. The old citation
  is kept and the same 070931 run is added (feed-journal and its test book pass
  there at current digest and closure).
- PRF-052: already passed through its own cited manifests.
- No row was downgraded. No farm run was needed, so none was submitted.
  The 070931 manifest's overall status is `failed` because of
  books/bp-node-progress-guards; the rule reads the per-book verdict.

## make check

`make check` in this worktree: exit 0.
certified-claims: 4 targets, 6 event books, 0 warnings, 0 citation failures.
ratchet: baseline=37, failing=0, improved=0, unmeasured=1.
No `tools/ledger.py --write` was needed; the ledger check passed unchanged.

Unit tests: tests.test_certified_claims and tests.test_proof_cost, 22 tests,
OK. tests.test_green_check: OK. tests.test_evidence_manifests: 5 errors, all
from `git commit` in the fixtures' temporary repositories failing on
"1Password: failed to fill whole buffer" (commit signing on this laptop, which
those fixtures inherit); they do not read the files this lane changed.

Negative control (a scratch copy of the baseline passed with `--baseline`, with
books/records removed and books/replay's figure lowered to 60 s): exit 1 with
exactly two FAIL lines, "books/records ... not in baseline" and
"books/replay: worst=90.775s > baseline 60.000s +25% = 75.000s".

## Next concrete experiment

Take books/store-node-invariants (124.9 s) from the top of the baseline, split
its slowest events (per-event timing is unavailable in the archived logs, so
the first step is one scoped certify that keeps its .certify.log), and run
`--write-baseline` to see the list shrink by one book.
