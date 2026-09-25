# Python store under format 8 (lane python-store-f8, 2026-09-25)

Base: dev a7756b67. Laptop (darwin), ACL2 8.7 through the Python bridge's
pooled ACL2 (`tools/run_store.py` `Acl2Store`), Python 3.14.7. No book
changed; no farm run. `host/store-host.lisp` changed (a host file, outside
the Makefile root closure); the tests below load it.

## Cause

`group_codes` (tools/run_store.py) compared `store.config["format"]`, which
`_config_from_metadata` built in Python as `"fn-store-8"` for ACL2's 8, with
`fn-store-format-id`, which is still `*fn-store-format-id*` =
`"fn-store-experiment-7"` (books/store-config.lisp:28). Every store `init`
wrote after P1 is format 8, so every post, checkpoint and corruption setup
was refused "store was written under a different store format". Test side:
`test_bp_receive_faults` read a `"capacity"` key the format-8 config does
not have, and five corruption subtests called `run_store.canonical_json`
(absent since 2026-09-19) plus one wrote `{` expecting a frame refusal.

## Fix (commit 29115649)

- Format: the check is ACL2's admission, `fn-bs-profile-admittedp` over the
  decoded profile, at open (`Store._config_from_metadata`), as the native
  owner does at install (`fn-owner-install-profile`). `config["format"]` is
  ACL2's number from `fn-store-profile-summary`; nothing compares it.
  `frame_bridge.format_id` and the host wrapper `fn-store-format-id` (Python
  was its only caller) are deleted. `*fn-store-format-id*` in
  books/store-config.lisp is now named by nothing but the spec history; its
  removal is a book change left to a book batch.
- Profile names: `run_store.py init --profile WORD` sends WORD's octets to
  `fn-store-metadata-config-frame-for-word`, which reads them with the
  native operator's `fn-nop-profile-preset-word` (development, scale,
  default) and frames `fn-bs-config-frame-for-profile`; no word is
  `fn-bs-initial-config-octets` (development, the native `store init`
  entry's default). An unknown word is ACL2's NIL, refused before anything
  is written. `store-host.lisp` includes `books/native-operator`.
- Bounds: the owner's transaction gate is `fn-sbud-verdict` through
  `publication_admissible` over the owner's own ACL2 (the CLI post already
  asked it), replacing `records >= max_transactions`; the replay bound in
  `durable_records` is `fn-profile-replay-within-boundp` per record
  (`fn-store-profile-replay-within-bound`), replacing
  `aggregate > max_recovery_record_bytes`.

Measured on this image (one bridge session, boot 15 s): the frame for no
word and for `development` decodes to (8, T 128, H 25 165 824, R 17 138 486,
A 32 768); `scale` to (8, 4096, 805 306 368, 17 138 486, 32 768); `default`
to (8, 4 294 967 295, 1 099 511 627 776, 67 108 864, 16 777 216); `bogus`
and `(evil)` are refused; all three presets are admitted; `[]` is not.

## Suite, one module at a time

`python3 -m unittest -v tests.<module>`, sequential, `timeout 1500` per
module (a second pass at `timeout 3600` for the three modules the first
pass cut). Another agent's unittest run shared the laptop during both.

| module | before (dev a7756b67) | after |
|---|---|---|
| test_store_config | 6 run, 2 failures (850 s) | 6 run, OK (1356 s) |
| test_store | 21 run, 13 failures, 3 errors (1048 s) | 15 ok in pass 1 (cut at 1500 s, no failure); the other 9 in pass 2: 6 ok, 1 failure and 2 errors, all an ACL2 boot or call hitting `ACL2 prompt timeout` / `init returned 1` at `(include-book "books/replay")` under a second agent's concurrent ACL2 tests |
| test_acl2_bridge | 16 run, OK (15 s) | 16 run, OK (15 s) |
| test_checkpoint | 7 run, 12 errors (subtests) (540 s) | 4 ok in pass 1 (cut at 1500 s); the other 3 in pass 2 failed at `init` with the same boot timeout at `(include-book "books/replay")`, before any store code |
| test_store_corruption | 7 run, 16 failures (483 s) | pass 2: 7 run, 4 failures, all one subtest family, `test_metadata_checked_then_frontier_changes_is_a_fenced_fault` writing JSON-era `{` into the frontier (legacy-JSON refusal, not a frame refusal); fixed after the run (commit 2) to truncate the frame, not rerun |
| test_media | 20 run, OK (554 s) | 20 run, OK (574 s) |
| test_bp_receive_faults | 10 run, 1 error (KeyError 'capacity') (1324 s) | 10 run, OK (1438 s) |

Every before failure and error but the `capacity` KeyError is the format
refusal. The coordinator's earlier `test_acl2_bridge` error
(`test_call_timeout_grows_with_form_size_and_bounds_the_recorded_reopen`)
did not reproduce here, before or after.

`make check`: fails only on rows this lane did not touch — REP-007 (spec
anchor, registry definition, scenario), PRF-080 reciprocity, and the stale
ledger (not edited, per the brief).

## What remains of the Python host's own values

- Read bounds before consuming bytes, sized from ACL2's fields: the owner's
  `length > max_payload_bytes` before reading a POST body
  (run_owner.py), `transaction_files` stopping one past `max_transactions`
  before ACL2's observation verdict, and the BP receive/ingress pre-checks
  `len(article) > max_payload_bytes` (run_bp_receive.py, run_bp_ingress.py),
  which ACL2's post boundary decides again. These are work bounds on
  untrusted input; the value is ACL2's, the comparison is Python's.
- Slice constants checked against ACL2 at session start
  (`_check_host_constants`: MAGIC, TRAILER_BYTES, journal caps), the read
  caps CONFIG_RECORD_BYTES and ANCHOR_RECORD_BYTES, MAX_STAGING_REPORT.
- `metadata`'s `b"unsigned-legacy-v0"` provenance label (open item).
- `*fn-store-format-id*` in books/store-config.lisp is dead and should go
  with the next book batch that touches it.

## Not yet shown green

After commit 2, not rerun: `test_store_corruption` (the one fixed subtest
family), and the 3 test_checkpoint and 3 test_store cases that timed out
booting ACL2. The timeouts are at the first `include-book`, before
`host/store-host.lisp` (the file this lane changed) is loaded; the smoke
session with the new include booted in 15 s. They need a rerun on a quiet
laptop, one module at a time.
