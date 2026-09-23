# Store corruption suite triage during T2a integration

The optional `tests.test_store_corruption` run in `build/store-python-trial.log`
was interrupted after the failure pattern became clear; it is not a complete
suite verdict.  The six preceding `StoreNodeHostTests` passed.  In the
corruption suite, filename mismatch, final-name collision, malformed record
frame, and uncertain-tail replay cases passed.  The failures clustered in the
configuration and allocator metadata fixtures.

| Cases in the partial run | Observed failure | Fixture contract conflict |
| --- | --- | --- |
| `config-checksum`, `frontier-checksum` | `json.loads(path.read_bytes())` raised `UnicodeDecodeError` before the store was opened | `Store.initialize` writes binary FNSM frames, not JSON |
| `config-profile` | `run_store.config_with_checksum` is absent | The helper was removed with JSON metadata |
| `frontier-behind-history`, `frontier-bool` | `Store._frontier_with_checksum` is absent | The allocator is an ACL2-authored binary frame |
| `frontier-truncated` (recover/status/inspect/post), `metadata_checked_then_frontier_changes` (same four verbs) | The image is refused with `legacy JSON allocator is retained in place; explicit offline migration is required`, not the expected `invalid durable allocation frontier` | The fixture overwrites the first byte with `{`, which deliberately selects the legacy-JSON diagnostic |

The inherited mismatch is demonstrated by source at the exact T2a base
`24a5df6b`: `tools/run_store.py` already calls `metadata_config_frame` and
`metadata_frontier_frame` in `Store.initialize` and explicitly rejects a
`{`-prefixed allocator; `tests/test_store_corruption.py` already uses the
JSON helpers, JSON decode, and old diagnostic listed above.  A current-source
initialization probe produced `config.json` prefix `464e534d0101000000570015`
and `allocation-frontier.json` prefix `464e534d01020000000100bd`; both raised
`UnicodeDecodeError` in `json.loads`.  A focused `{` allocator probe returned
exit 4 and the legacy-JSON diagnostic quoted above.  The pre-T2 test was not
executed against the pre-T2 source, so this is a source-and-current-runtime
demonstration of an inherited fixture conflict, not a historical passing/failing
baseline measurement.

No completed corruption case demonstrated a T2-specific Store regression.
The interrupted matrix and the still-stale metadata fixtures remain open as
optional test maintenance; this triage does not count them as passing.
