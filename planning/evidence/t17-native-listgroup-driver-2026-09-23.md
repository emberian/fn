# T17 native LISTGROUP driver prepared, 2026-09-23

`tests/test_native_reader_index.py` now contains two additional saved-image
methods under the existing `FN_RUN_NATIVE_READER_INDEX=1` gate. They drive
only the public operator CLI and NNTP socket, not a Python implementation of
bucket selection or article allocation.

The historical method opens an old reader, creates `fn.live` on the running
owner, opens a configured reader, publishes two `fn.test` articles and one
`fn.live` article, and opens middle/fresh readers at different points. It
checks exact LISTGROUP number lines and selected ranges on each pin, old
refusal of the later group, an empty range above the current high number,
and the two groups after graceful owner restart. This follows the historical
reader ACL2 witness in `config-owner-live-tests` but exercises the native
connection lifecycle. The current public operator CLI has no deletion or
watermark-advance command, so this method does not claim an internal
allocation hole; an explicit recovery fixture would be needed for that case.

The workload creates 24 distinct groups and publishes one article in each,
then warms a pinned reader and measures 96 `LISTGROUP group 1-1` socket
commands across two selected groups. It asserts each reply, prints elapsed
monotonic time, and excludes configuration, publication and process startup
from that interval. It does not assert one group is faster or infer an
asymptotic bound from socket timings.

`python3 -m py_compile tests/test_native_reader_index.py` passed, and ordinary
unittest discovery found all three methods and skipped them because this lane
has no source-matched saved image. Root will run them with
`FN_RUN_NATIVE_READER_INDEX=1` and `FN_NATIVE_HOST` pointing at its next
qualified integrated image. No image or live node was built or run here.
