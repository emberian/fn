# Handoff: w12/feed-durability

Baseline `8b474e2`; code tip `59eb42f`. This packet repairs the physical FNFD
append/reopen path. It does not wait for, or implement, the next packet's
submission intent/abort protocol. No shared registry, milestone, BOARD or
Makefile root list was edited.

## Contract and code

`books/feed-journal.lisp` owns the existing four-octet outer envelope, exact
bounded read length, frame integrity/schema/peer checks, last accepted repair
offset and the barrier phase machine. `tools/feed_wire.py:Journal` reads only
the extent ACL2 authorizes, accumulates short reads to actual EOF, replays a
complete accepted frame through the host bridge, and stops at the first EOF,
torn suffix or invalid evidence. A torn suffix is truncated to ACL2's safe
offset. Complete invalid evidence is never skipped or truncated.

Recovery completes content, feed-directory and store-directory barriers,
including on empty/new journals, before append is permitted. Appends write
exactly ACL2's envelope, then complete the platform content barrier. The
existing store helpers supply Darwin F_FULLFSYNC/fallback and other platforms'
fsync behavior. An ambiguous append closes the file descriptor and retains an
uncertain logical phase when the bridge can answer. There is no same-image
unfence. Invalid evidence is a startup fault; ambiguous I/O is uncertain.

`Owner.feed_flush()` checks that every authorized frame has a peer and an open
journal. Any failure calls `feed_fence(error)` then raises `StoreIndeterminate`.
The fence sets `feed_uncertain`, `stopping` and `EXIT_UNCERTAIN`. Feed poll,
read, write, dial and flush cease; feed drop closes transport without reporting
lost or attempting another append. The general guard and served/control entry
points stop, and the served event returns immediately after a fenced drain.
`take_fault` preserves the uncertain label and traceback before generic fault
handling. The control channel reports the existing uncertain outcome/exit code.

The host calls the exact theorem subjects:

- `Acl2Owner.feed_journal_scan` invokes `fn-owner-feed-journal-scan`; that
  wrapper calls `fn-feed-journal-scan` and only then installs its returned safe
  offset and decoded entry through the existing `:feed-replay` transition.
- `Acl2Owner.feed_journal_step` calls `fn-feed-journal-phase-step` directly;
  `Journal._step` carries its returned phase. `fn-feed-journal-phase-run` is
  the fold of this same transition over later observations.
- `feed_journal_prefix` and `feed_journal_wrap` call their identically named
  ACL2 functions. The old Python struct codec, bound and trailer size copies
  are removed. `fn-owner-feed-sealed-frame` owns protected-prefix selection
  and trailer assembly; Python receives a whole sealed frame.

Valid record replay retains `fn-feed-apply-record` semantics. The scanner
checks schema/integrity/peer but deliberately does not strengthen replay to
`fn-feed-drivenp` against historical no-ops or changed limits.

## Evidence

Final coherent certification invocation:

```
python3 tools/farm.py submit hbox books/feed-journal tests/acl2/feed-journal-tests --jobs 4 --remote-root /tank/fn/lanes/w12-feed-durability
python3 tools/farm.py wait hbox run-20260921T062240Z-adcd --timeout 5
```

Both roots passed. The archived
[manifest](../evidence/manifests/certify-20260921T062242Z-1643977.json)
records ACL2 8.7, SBCL 2.6.8, exact source/driver/executable/certificate
hashes, invocations and results. The farm uses `swarm-build`; no broad roots
outside the initial owned dependency closure were requested. Earlier failures
were ordinary guard/test-admission failures, fixed without trust facilities.

Host validation is the exact command, version, revision and input hashes in
[the generated host evidence](../evidence/feed-journal-w12-host.json), with
[raw output](../evidence/feed-journal-w12-host.log):

```
python3 -m unittest discover -s tests -p 'test_feed*.py' -v
python3 -m py_compile tools/feed_wire.py tools/run_owner.py tests/test_feed_journal_live.py tests/test_feed_fence.py
```

The live tests run the actual ACL2 scanner and feed replay fold in one local
ACL2 image. They exercise every byte cut of a trailing restart envelope,
repair then append then a second restart, complete bad digest/grammar/peer and
invalid prefix evidence, short reads, each recovery barrier failure followed
by successful recovery, and append-sync ambiguity followed by a refused second
append. Child-process I/O deaths cover the named open, clean EOF, repair,
truncate, content/directory/parent barrier, append, write and append-barrier
phases. Host-only tests script bridge answers for I/O ordering and exercise
real owner methods against a mock bridge to show no later mutation or success
outcome escapes the fence. These do not run the full owner/NNTP composition.

## Exact root/registry/scenario delta for root

Register these owned roots in the Makefile root list:

```
books/feed-journal
tests/acl2/feed-journal-tests
```

All production and test helper function prefixes are under the already
registered `fn-feed-`; no prefix addition is needed.

Candidate curated proof events, with scope in the same sentence:

- `fn-feed-journal-next-is-bounded-progress`: under an actual scanner `:next`
  result, the safe offset increases strictly by a bounded envelope extent.
- `fn-feed-journal-uncertainty-survives-all-later-observations`: from an
  uncertain phase, arbitrary later observations cannot restore readiness.

Do not curate `fn-feed-journal-repair-offset-unfolds`; it is explicitly an
unfolding helper. Event and guard/test/root counts must come from
`tools/ledger.py`, which was run read-only in this lane. Root allocates any new
proof target ID; PRF-029's existing scope-selection title should not be widened
silently to claim physical durability. ENC-002 and FLR-001 can cite this
implemented narrow recovery surface while retaining their broader status.
PRF-035's host-site description should name `fn-owner-feed-sealed-frame` for
the moved FNFD protected-prefix/trailer assembly.

The scenario registry should record the FNFD suffix-repair/reappend/reopen
case; complete invalid evidence preserved and startup refused; content and
namespace barrier failures distinguished as uncertain; and the owner mutation
fence. Executable cases are the named tests above. The specification update is
`specs/peering.md`, section “Status (wave 12, FNFD physical prefix recovery)”.
Root updates milestone/current-task and registry status together with landing.

## Remaining assurance and integration scope

The phase theorem proves control/fence discipline, not survival of a physical
byte image. Physical K0 composition stays open. Retained-prefix preservation
is conditional on A-WRITE-ISOLATION; durable bytes/namespace are conditional on
A-DURABILITY. No theorem here claims power-loss qualification, cryptographic
collision resistance, crash images always being prefixes, or detection of a
whole missing previously durable suffix without an independent anchor.
Journal aggregate length/replay work remain unbounded by this repair.

General K5 live/replay correspondence and acceptance-to-feed intent atomicity
remain open in this packet. The submission lane owns the latter extension:
its recovery reconciliation hook belongs after every Journal is opened/replayed
and before `bridge.feed_restart(); self.feed_flush()`. The scanner will accept
its next FNFD kind once the shared codec does; this lane edits no peer-feed
record family. That extension must rerun the integrated roots and full owner
scenarios against its new history, rather than treating this packet's evidence
as evidence for the extension.

Wire-block lane owns Session framing. Preserve this packet's
`if self.feed_uncertain or not command: return` when merging its `feed_write`
change. Journal's constructor is now `(root, peer_bytes, bridge, faults=NO_FAULTS)`;
there is no `.records()` iterator or Python `MAX_RECORD`/`TRAILER_BYTES` API.
The final full-owner host load, CLI/served composition and wire tests belong to
root's frozen integrated batch; current evidence deliberately does not claim
those unrun checks.
