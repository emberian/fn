# Fenced cold-clone source packet (2026-09-23)

This packet follows the certified auxiliary recovery packet `b9ffcf6b` and
the finite native consumer-publisher seam `d84c18f0` (cherry-picked here as
`4019bd85`).  It does not change the Store event or pack codec.  The fence
stores the exact canonical version-one `fnce` rollover event that ACL2
proposes from the recovered Store's dense sequence and allocator txid; the
host supplies only the fresh incarnation octets.  `fn-cpa-clone-phase` admits
`:pending` only when the marker equals that proposal and `:completed` only
when the exact marker is the final committed Store event and the recovered
consumer incarnation and dense sequence match.  A retry cannot append a
second rollover after completion.

`checkpoint clone SOURCE DESTINATION FRESH-INCARNATION-ID` opens the source
under its exclusive writer lock, builds a sibling staging tree, writes and
barriers the fence before copying source bytes, copies only ordinary files
and directories through no-follow descriptors, fsyncs the copied tree, and
publishes it with Linux `renameat2(RENAME_NOREPLACE)`.  ACL2 supplies the
directory-depth and total-entry limits.  Ordinary Store acquisition and
initialization refuse a fenced destination.  The clone executor alone opens
it under the exclusive owner, publishes the ACL2 event through
`fnn-owner-consumer-commit`, closes, reopens the full exact history, requires
`:completed`, and only then unlinks and barriers the fence.  The separate
`checkpoint clone-resume` command handles a process death after publication.
An occupied destination is untouched; same incarnation is refused before
copy.  The developer-only `consumer-bootstrap-fixture` uses the same owner
publisher and ACL2 bootstrap proposal to create an E2 Store for the native
integration test.  It is not a public consumer administration interface.

ACL2 qualification: `python3 tools/farm.py submit persvati --root
/Users/ember/dev/fn/build/lanes/preservation-clone --remote-root
/home/ember/fn-lanes/preservation-clone-e2 --jobs 2
books/checkpoint-auxiliary tests/acl2/checkpoint-auxiliary-tests`, run
`run-20260923T200306Z-e792`, archived manifest
`planning/evidence/manifests/certify-20260923T200311Z-3706431.json`.
ACL2 8.7 on SBCL 2.6.8, toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`;
65 dependency books installed from three cache origins, both changed roots
certified in 4.535 seconds, status passed.  Book/test source SHA-256:
`3f03c2f1af3f7312e613a707fc5961f9add065eae399205a8f0e81efcfdf7b6b`,
`ed2a436eca23f0c5b25bc841ca81054ffc0dbd9d96755b8383ba010a60305b3b`.
The ACL2 tests exercise pending/completed/refused marker phases, rollover
identity refusal, and bootstrap proposal coordinates.  Raw host files read
successfully under SBCL; the native test source is syntax checked.

The developer-image native test `test_fenced_clone_rollover_after_selected_pack_reclaim`
is written but has **not** run: no saved image contains this E2/checkpoint
source yet.  It is gated by `FN_RUN_NATIVE_CLONE=1` and must run against a
combined developer image.  In particular, this packet cannot yet claim a
physical process-death, no-replace syscall, or served old-cursor witness.
The trust boundary includes Linux `renameat2` no-replace semantics, fsync
ordering, and the existing Store publisher's OS assumptions; ACL2 does not
prove a syscall or persistence hardware.  The source-only event-phase facts
do not by themselves prove byte-copy correspondence or every crash cut.
