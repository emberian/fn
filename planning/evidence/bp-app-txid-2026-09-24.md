# BP application txid after restart (2026-09-24)

Lane `bp-app-txid`, branch `lane/bp-app-txid` from dev `3fd3758b`. Fix commit
`3ab7ab03`. Logs and the runner are in [`bp-app-txid-2026-09-24/`](bp-app-txid-2026-09-24/)
with [`SHA256SUMS`](bp-app-txid-2026-09-24/SHA256SUMS).

## Defect

Three `tests.test_bp_node_native` restart cases exited 4 with
`store: ACL2 returned a non-natural` on the 1a9dd747 developer image
(failure 9 of [native subsets](native-subsets-1a9dd747-2026-09-24.md)):
`test_ambiguous_fnrj_decision_fences_until_cold_replay`,
`test_death_after_fnrj_receipt_decision_replays_one_article`,
`test_request_retry_queues_distinct_receipt_carriers_and_releases_pin`.

Cause, confirmed by the fix below and not only by reading:
`fn-owner-app-plan-install`'s branch for a request FNRJ has already bound
(status `:committed`, `:context` or `:pending-receipt`,
`host/bp-native-app-host.lisp:122-127` at `3fd3758b`) set the generation but
never `fn-owner-app-txid`, and `fnn-bpapp-accept-locked` coerced that global
with `fnn-nat` before dispatch (`host/native/bp-app.lisp:97`). In a restarted
process the global is `nil`, and `fnn-nat` faults (`host/native/io.lisp:623`).
In a long-lived process the same branch left the previous request's txid and
planned result in place. Neither file changed between `1a9dd747` and
`3fd3758b`.

## Where the txid comes from

The decision is already ACL2's. A new request's txid is
`fn-state-next-txid` of the owner acceptance state; a request with a durable
intent carries the intent's txid, read by `fn-bpaj-request-planned-txid`
(`books/bp-native-app.lisp`, guard `t`) over `fn-bpaj-state`, the joined
FNRJ state replayed from the journal at open. Intents are never removed by
`fn-bpaj-apply-record` once a context binds them, so the bound request's
intent is still in the recovered state. No book function was missing, and
no book changed.

## Fix (`3ab7ab03`)

- `host/bp-native-app-host.lisp`: the bound branch sets
  `fn-owner-app-txid` from `fn-bpaj-request-planned-txid` and
  `fn-owner-app-planned-result` from `fn-bpaj-request-planned-result`, both
  over the recovered joined state.
- `host/native/bp-app.lisp`: the adapter no longer coerces the txid before
  dispatch; `fnn-bpapp-planned-txid` checks it only in the two actions that
  consume it, `:persist-intent` and `:submit`. `fn-bpaj-dispatch-fast` answers
  the bound statuses with `:return-receipt`, `:prepare-receipt` and
  `:resolve-absent` (case table; `fn-bpaj-dispatch-committed-never-retries`
  covers `:committed` over `fn-bpaj-dispatch`, bridged by
  `fn-bpaj-dispatch-fast-is-checked`). A historical `:request-context`
  admitted before any intent has no planned txid and is never asked for one.
- `planning/ledger.json` regenerated (host line shifts only).

## Image

The dev closure at `3fd3758b` has no complete cached artifact set
(`proof_artifacts.py acquire` found none), and no book changed, so no farm
run was made. The developer image was built from a `git archive` of
`1a9dd747` with the two fixed host files from `3ab7ab03` overlaid; their
SHA-256 in the build tree equal `git show 3ab7ab03:<file>`
(`20ac5770…` `host/bp-native-app-host.lisp`, `678feb99…`
`host/native/bp-app.lisp`). Built on hbox in
`/tank/fn/scratch/bp-app-txid/fix/tree` with the w28 wrapper, OpenSSL 3.5.8,
`FN_NATIVE_PROFILE=developer`, under `swarm-build`; artifact set
`1d8ea88bfbcca218…` (275 books, composed, rejected 0).

| artifact | SHA-256 |
| --- | --- |
| `build/fn-host-developer` | `86c9fbf06157db58d6b4c90a6f5a6c5f6c8d88e5866b99ee9221d09a835c87fb` |
| `build/fn-host-developer.core` | `985c0216b824ea1b7011d768ea565b2bdda41b0a8c16f67c103c6fa93666ef25` |
| `build/native-build-developer.log` | `02c8fe1a2bbf8794b495006b5ea4728ee14026da878cdffccf9ab352a7c79ae3` |

## Runs

Each run is `python3 -m unittest -v <id>` via [`runcase.sh`](bp-app-txid-2026-09-24/runcase.sh)
(env header and `# rc=` footer in each log).

| run | image | result | log SHA-256 |
| --- | --- | --- | --- |
| repro `test_ambiguous_fnrj_decision_fences_until_cold_replay` | 1a9dd747 developer | FAIL `4 != 0 : b'store: ACL2 returned a non-natural\n'` | `b3acf383…07ed1` |
| repro `test_death_after_fnrj_receipt_decision_replays_one_article` | 1a9dd747 developer | FAIL, same line | `329e68bd…44511` |
| repro `test_request_retry_queues_distinct_receipt_carriers_and_releases_pin` | 1a9dd747 developer | FAIL, same line (second dispatch) | `4a9acf2a…8b522` |
| `test_ambiguous_fnrj_decision_fences_until_cold_replay` | fixed | OK | `9528ae7a…e8619` |
| `test_death_after_fnrj_receipt_decision_replays_one_article` | fixed | OK | `8c666426…b9798` |
| `test_request_retry_queues_distinct_receipt_carriers_and_releases_pin` | fixed | OK | `092c0e67…459e` |
| module `tests.test_bp_node_native` (16) | fixed | 15 pass, 1 fail, 404 s | `7f1e4c48…2a01` |

The one module failure is `test_older_mru_wait_allows_younger_forward_and_replays`,
`6 != 7`, which is failure 10 of the native-subsets record, unchanged; the
other twelve cases that passed on 1a9dd747 still pass.

## Limitations

- The image is 1a9dd747 plus this fix, not dev head: other dev changes since
  1a9dd747 are not in it.
- No theorem states that a bound request stays bound across the records the
  adapter publishes inside one callback (`:resolve-absent` then
  `:prepare-receipt`), which is what makes the unused txid safe; that
  persistence of `fn-bpr-find-context` under `fn-bpaj-apply-record-fast` is
  open.
- `make check` green at `3ab7ab03` plus this record.
