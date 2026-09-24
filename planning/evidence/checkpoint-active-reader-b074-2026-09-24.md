# Active reader excludes offline Store reclamation

The `test_pack_reclaim_refuses_active_reader_then_retains_source` fixture in
`tests/test_native_checkpoint.py` ran against the source-matched developer
image frozen at `b074f94ed3e612a6e71c18859a3af3c9112c3708`. The initial
test assertion mistakenly looked for the operator's accepted status on stdout;
the operator emits that status on stderr. Test-only commit `97978480` corrected
that assertion without changing the substantive reader/reclaim checks. The
qualifier reran the exact case with that overlay and it passed in 0.815 s.

- Image launcher SHA-256: `c901bdf5d366fa1982a8035a0db4178d543d8df17aadfb3f1798611a9aa0fbba`.
- Image core SHA-256: `b6dcd8c31860962032290671e62189999c6076f1ea6358c0f970ef8678499f0b`.
- Test overlay SHA-256: `ae848fb37f2b98639ccbaeb34a8eadbe3e219f4f6bf1a593bb459fed001f9ccd`.
- Invocation: `FN_NATIVE_DEVELOPER_HOST=/tank/fn/gates/wide-combined-b074f94e-exact-20260924/build/fn-host-developer FN_NATIVE_TEST_ROOT=/tank/fn/gates/wide-combined-b074f94e-exact-20260924 python3 -m unittest tests.test_native_checkpoint.NativeCheckpointTests.test_active_reader_blocks_pack_reclaim_and_reopen_keeps_archive_pin -v`.
- Result log: `/tank/fn/gates/wide-combined-b074f94e-exact-20260924/build/freeze/checkpoint-reader-overlay.log`.

The fixture establishes a read-only Store opener before the reclaim attempt.
The exclusive lock refusal is checked separately from uncertain/fault status;
no prefix unlink occurs while the opener lives. After the opener exits, the
reclaim succeeds and cold reopen returns the exact article source and the
same retention pin/reserved aggregates. This is an offline exclusion witness,
not a theorem for general concurrent physical reclamation or all crash cuts.
