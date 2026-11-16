# Native physical-cut correspondence

The four storage cut coordinates now have an executable ACL2 consumer:
`fn2-native-device-cut-replay`. This source path is not yet certified or run
against the current native application. The default native-program gate remains
incomplete; neither inventory success nor this document discharges it.

## Captured subject

`fn2-n-boundary` assigns the real ordinal under its existing mutex. Its optional,
NIL-default diagnostic observer receives that ordinal, label, actual job slot
and generation, and the exact selected-death flag. Storage submission, worker
entry/return, and completion harvest supply their real operation incarnation.
The worker callback now receives its actual job; both host callback providers
and the device test consumer use that ABI.

The test-only recorder reuses `native-device-effects-capture.lsp` and its stream
mutex. It adds the actual initialization profile, boot result, complete envelope
events, and boundary records. At selected death it freezes that evidence stream
until the original boundary exits. It neither retries nor cancels a syscall.
A syscall already begun can still affect the image: absent its recorded return,
the existing model treats a Write's requested span as uncertain. A queued Write
which has not begun cannot explain image changes. Short/error returns are not
rewritten to successes. Trace overflow, malformed tails, or records following
the selected boundary refuse the capture.

## Executed model path

The consumer validates contiguous boundary ordinals, a final selected marker,
and its slot/generation. It distinguishes before-submit, before-physical,
after-physical, and before-terminal-post. It then calls the recovered existing
`fn2-native-device-control-replay`, which runs the actual envelope transitions
from the captured initialization/boot state, binds every submitted device job
to the selected logical loan and Write bytes, and checks physical return/Post
ordering and normalization. The raw consumer also runs the existing complete
image comparison over every byte of immutable before/after copies. The physical
model reports exact process effects or uncertain effect bounds separately.

The joined envelope consumer and its existing controls were recovered from
`8ff8a4411`; their source is unchanged. The complete image driver is recovered
from the same source, with one explicit empty-prefix case for a cut before the
first physical submission. This does not accept changed image bytes.

## Selected-image run

Prepare the actual current startup without copying its implementation:

```
python3 tests/native-device-cut-launch.py /tmp/native-cut-startup.lsp
```

This inserts only the test capture load immediately before the original
`fn2-nserve-main` call. Run through the normal qualified launcher in an allocated
scope, with `FN2_TEST_DEVICE_EFFECTS` naming a new external capture file,
`FN2_ENVELOPE_TRACE` large enough for the whole bounded campaign, and the real
`FN2_KILL_AT` ordinal. All ordinary image/profile/listener settings are unchanged.
The campaign must observe exit86 and retain immutable complete before/after
image copies. Replay uses `tests/native-device-cut-replay.lsp` with the same
capture, `FN2_TEST_DEVICE_BACKEND`, `FN2_TEST_DEVICE_BEFORE`, and
`FN2_TEST_DEVICE_AFTER`; an empty physical prefix also requires the actual
`FN2_TEST_DEVICE_FD`. This checks one selected run, not every reachable crash.

## Outstanding semantic obligations

- Certify the new consumer and execute a real initialized positive run plus
  ordinal, generation, missing-return, changed-image and partial-image controls.
- Bind the exact run/image/source and immutable snapshots in the shared campaign.
- Current inventory has 19 sites. The other 15 remain unmapped here, including
  network, take/ack/post, TLS and COMPRESS. Their labels are not mapped to a
  storage cut by default. Existing simulator take/post programs are separate.
- The older envelope consumer refuses COMPRESS `:input-prefix` events. It must
  consume the actual corresponding core effect before a compressed run can pass;
  dropping the event or treating it as a no-op is not a repair.
- Process-visible file-image correspondence does not prove power-loss durability,
  Fence honesty, kernel behavior, or the simulator's whole crash/restart relation.
  In particular this consumer must not be advertised as all-cut host refinement.
