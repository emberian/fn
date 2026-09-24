# Combined native preservation qualification handoff

Run one source-matched production/developer image pair after root integrates
the pack-retirement packet, its cut-audit/reporter correction, topic v2, and
author lifecycle.  Keep the existing exact pre-v2 `b074f94e` developer image
as the legacy half of the topic migration test.  The new images must be built
from one recorded source revision with a passing frozen ACL2 closure; record
both image hashes, toolchain identity, OpenSSL version, command output, and
test exit codes.  This is a handoff, not a claim that the image has run.

With `DEV_IMAGE`, `PROD_IMAGE`, and `LEGACY_IMAGE` set to the actual saved
images, run these focused scopes from the frozen source tree:

```sh
FN_NATIVE_DEVELOPER_HOST="$DEV_IMAGE" python3 -m unittest -v \
  tests.test_native_checkpoint.NativeCheckpointTests.test_retiring_old_pack_generations_keeps_exact_retained_sources \
  tests.test_native_checkpoint.NativeCheckpointTests.test_pack_generation_retirement_death_reopens_and_retries \
  tests.test_native_checkpoint.NativeCheckpointTests.test_active_reader_blocks_pack_reclaim_and_reopen_keeps_archive_pin

FN_NATIVE_DEVELOPER_HOST="$DEV_IMAGE" FN_RUN_NATIVE_CLONE=1 \
  python3 -m unittest -v \
  tests.test_native_checkpoint.NativeCheckpointTests.test_clone_reopens_historical_authorship_verdict

FN_NATIVE_DEVELOPER_HOST="$DEV_IMAGE" FN_NATIVE_TOPIC_V1_HOST="$LEGACY_IMAGE" \
  FN_RUN_TOPIC_LOCAL_E2E=1 python3 -m unittest -v \
  tests.test_native_topic_local.NativeTopicLocalTest.test_v1_history_reopens_under_v2 \
  tests.test_native_topic_local.NativeTopicLocalTest.test_fresh_v2_anchor_refuses_legacy_reopen

FN_NATIVE_HOST="$PROD_IMAGE" FN_RUN_HYBRID_E2E=1 \
  python3 -m unittest -v \
  tests.test_native_hybrid_author.NativeHybridAuthorTest.test_local_revocation_targets_one_principal
```

The topic migration fixture now preserves its pre-compaction transaction
hashes for lost-reply retry, revokes the current principal only after both
historical v1 and fresh v2 anchors are durable, and then checks that replayed
historical report authority survives.  It selected-packs, reclaims covered
transaction files, replaces the selected pack, retires the old pack, and
selects a node checkpoint before final reopen.  Store transaction/article
counts and retention reserved charge must match their pre-compaction values;
the selected checkpoint must report `auxiliary=equal-v2`, which compares
topic and consumer/index projections reconstructed from exact event bytes.
Final topic retries must add no transaction after this new physical baseline.

The checkpoint retirement test covers first and second unlink process-death
cuts, the packs-directory cut, no-op retirement without a directory cut, and
active-reader refusal before deletion.  The authored clone test carries a
historical verdict and exact signed source through replacement and retirement
of its selected pack.  These process-death tests exercise SIGKILL/reopen on
the tested filesystem; they do not prove power-loss behavior or authorize
pruning any retained Store event or protected article object.  A later
generation ceiling remains a separately open capacity contract.
