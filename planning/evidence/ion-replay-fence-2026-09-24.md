# ION workflow replay fence (lane ion-replay-fence, 2026-09-24)

Source: branch `lane/ion-replay-fence` from dev `0e4b318e`; fix, theorem and
teeth in `99bd7966`.

## The defect

`fn-bpiw-replay-records` (`books/bp-ion-workflow.lisp`, then lines 123-134)
applied every record with live semantics (`fn-bpiw-apply`) and restarted only
after the last record. A `:recovery` outcome needs a fenced pending
(`fn-bp-recover`); mid-history the pending was unfenced, the outcome was a
no-op, and a no-op counts as refusal. So `fn-workflow-preflight-history`
refused every recovery outcome and a journal holding one could not be
reopened, while live `fn-workflow-apply-record` accepted it
([M4 finding 4](m4-app-receipt-2026-09-24.md)). Reproduced in a REPL on the
unfixed book: `[config, enqueue]` opens fenced, live apply of
`(:outcome 10 0 :recovery :committed)` is `T`, replay of the appended journal
is `NIL`.

## The fix

`fn-bpiw-replay-fence` completes a matching unfenced pending `:indeterminate`
immediately before a recovery outcome (identity otherwise), the fence
`fn-bp-replay-records` already reconstructs. `fn-bpiw-replay-records` applies
each record to the fenced image.

## The theorem

`fn-bpiw-reopen-after-live-recovery-is-the-live-image-restarted`
(`books/bp-ion-workflow-replay.lisp`): if `fn-bpiw-replay-journal node records`
succeeds, `r` is a recovery outcome, and `fn-bpiw-apply` accepts `r` on the
opened image and ION state, then `fn-bpiw-replay-journal node (append records
(list r))` succeeds, its BP image is `fn-bp-restart` of the live image, and its
ION state is the live ION state. Subject: `fn-bpiw-replay-journal`, called by
`host/workflow-host.lisp:13` (`fn-workflow-install-replay`) and `:107`
(`fn-workflow-preflight-history`); live side `fn-bpiw-apply` as `:112`
(`fn-workflow-apply-record`) calls it. The BP step is
`fn-bpiw-fenced-recovery-restarts-as-live` (no state hypothesis).

Scope: one recovery outcome applied right after an open. No correspondence is
claimed for later live records in general: a new attempt on a
`:restart-observed` attempt is accepted live and refused by the history (the
host's history gate requires a journaled retry request first).

## Teeth (`tests/acl2/bp-ion-workflow-replay-tests.lisp`)

- Reachable witnesses: enqueue cut with `:committed` and with `:absent`;
  attempt cut with both; an ION-carrying cut (route and observation durable,
  policy retry, new attempt intent cut) with `:committed`, the ION state kept.
- The unfenced durable fold refuses the recovery outcome; the fenced one
  accepts it.
- must-fail without `(fn-bpiw-recovery-outcomep r)`: the live re-attempt above.
- must-fail without `(car live)`: a recovery outcome for txid 99.
- `(car open)` has no separating witness: a failed open's image holds no
  fence and refuses every recovery outcome live; the book asserts that refusal.

## Certification

hbox farm `run-20260924T221130Z-176e`, manifest
`certify-20260924T221143Z-2009005` (archived in
[manifests/](manifests/certify-20260924T221143Z-2009005.json)); ACL2 8.7,
`/tank/fn/toolchains/w28/acl2-literal-4g` (toolchain identity `d5f2b9f0...`),
`--jobs 2 --timeout-seconds 300 --affected-by books/bp-ion-workflow`, cache
`/tank/fn/certcache`, 4 roots (every Makefile root whose closure holds
`books/bp-ion-workflow`), status passed. Seconds per root:
`books/bp-ion-workflow` 1.7, `books/bp-ion-workflow-replay` 4.0,
`tests/acl2/bp-ion-workflow-replay-tests` 1.9,
`tests/acl2/bp-ion-workflow-tests` 1.7. `green_check --changed-since 0e4b318e`:
3 changed and 1 dependent, 0 not green.

## Mock four-node lab

`python3 tests/bp-dtn7/run_four_node_lab.py --run-base
/tank/fn/scratch/ion-replay-lab/four-mock --revision
lane-ion-replay-fence-99bd7966` on hbox (mock BPA, Python host, no image),
tree = this worktree at `99bd7966` with certificates installed from
`/tank/fn/certcache`; `FN_ACL2` as above. Result: `passed`, 202.4 s, exit 0,
22 of 22 assertions true, among them
`relay_a_journal_is_usable_after_recovery`,
`relay_a_onward_obligation_recoverable_after_kill` and
`relay_a_archival_receipts_unchanged_by_recovery`. The same lab stopped at
relay-a's recovery with `JournalError` before this change.

- [`four-mock.out`](ion-replay-fence-2026-09-24/four-mock.out) sha256
  `c20a080cdc2abb621ad8ce991182d71f84109818f201681d389a21135e826948`
- [`four-mock-evidence.json`](ion-replay-fence-2026-09-24/four-mock-evidence.json)
  sha256 `65b12c39433b8bf37086e9a15ea757b6e5d5855ec58cfecbe64c4430b5771720`

Limitations: the mock BPA is a laboratory scheduler, not BPv7; the dtn7 and
native runs were not repeated here.
