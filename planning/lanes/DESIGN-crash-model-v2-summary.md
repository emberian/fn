# DESIGN summary: crash model v2 (lane `w4/crash-model-design`)

Full design: [`specs/crash-model-v2.md`](../../specs/crash-model-v2.md).
Branch `w4/crash-model-design` from `9321344`. No certification ran; every
ACL2 form in the spec is a proposed definition or an unproved statement.

## The verdict, in one sentence

`fn-sf-crash-imagep` states the right conclusion (frontier old-or-new,
records stable-or-plus-exact-candidate) as a *hypothesis*; v2 makes it a
theorem about a byte-level model of files, directories, pending writes,
fences and torn crashes, with the host's real syscall sequences transcribed
as programs over that model and every process-death cut a step index.

## What v2 is

- **Model** (`books/byte-store.lisp`, prefix `fn-bs-`): inodes as octet
  lists, directories as name maps, a pending list of `:write` /
  `:set-entry` / `:del-entry` operations. `fsync(fd)` drains exactly that
  inode's writes; `fsync(dirfd)` drains exactly that directory's entry
  operations. A crash applies any subsequence of pending operations, each
  write cut into write-unit pieces that land, land as zeros, or land as
  garbage. `link`/`rename` are per-entry atomic and durable only after the
  directory fence; `rename`'s source removal is a separate operation. Every
  syscall takes an outcome: EIO and ENOSPC with partial progress; a failed
  `fsync` lands a torn subset and discards the rest (fsyncgate).
  Definitions written out in full (spec §1).
- **Programs** (§2): P-FRONTIER, P-RECORD, P-FINISH, P-RECOVER, P-INIT,
  P-JOURNAL (FNWF/FNRJ), P-INBOX (FNBI), P-CHECKPOINT (from the uncommitted
  w3 `tools/checkpoint.py`), each a constant step list with line numbers and
  `:cut` markers equal to the host's `faults.at` names. A new table rule:
  every durable syscall in a write path has a step and a cut after it,
  checked by AST against the ACL2 constants.
- **Keystones** (§3, exact statements): K1 the scan never faults on a crash
  image of a related state; K2 every such image satisfies the *present*
  `fn-sf-crash-imagep` (old-or-new becomes a theorem); K3 `fn-sf-crash`
  reproduces it (constructor as corollary); K4 acknowledged retention across
  a byte crash through `fn-sn-open-observed`; K5 stable prefix; K6 no partial
  transaction; K7/K8 fence-after-uncertainty and the completed fence removes
  the choice; K9/K10 the same for FNWF/FNRJ/FNBI, closing the campaign's two
  `gap` cuts; K11 the frame trailer: truncation and resize never validate
  (structural, no crypto), a validated torn frame is a digest forgery, and
  A-CRYPTO-TRAILER bounds nature's tears.
- **Finding worth stating**: for the host's programs the trailer is never
  *needed* for crash recovery (K1/K6 hold without it), because every link
  and rename is issued only after the inode's fence and no authority inode
  is ever overwritten. The trailer is defence in depth for images outside
  the crash relation (media, a lying fence).
- **Assumptions** (§3.6): one encapsulate `fn-assume-physical-crash` whose
  constraint is "the platform's image is admissible", from which fenced
  survival, invents-nothing, per-inode isolation and per-entry atomicity are
  *theorems*; one `fn-assume-crash-tearp` for the trailer. Media corruption,
  lying firmware, non-POSIX filesystems and whole-store rollback are named
  exclusions with the contract each would need.
- **Obligation map** (§4): the two v1 old-or-new theorems and the two
  completed-barrier theorems become corollaries; the crash-preservation and
  reopen theorems become lemmas; `fn-assume-durability-image` and
  `fn-assume-write-isolation-observe` are retired as strawmen; the
  Python-computed frontier/config checksums are deleted (twin); the six hand
  cuts and `journal.lisp`'s crash constructor are retired, with what the
  journal model got right listed.
- **Campaign v2** (§5): ACL2 image import and differential check (host
  reopen versus `fn-bs-scan-store` + `fn-sn-open-observed`); torn/zero/
  garble/lose/drop variants derived from ACL2's own pending list at each
  cut, at unit 1 and 4096; admissible versus inadmissible directory loss
  (the latter must exit `EXIT_FAULT`); a test-only unsafe-host flag so the
  campaign is shown able to fail.

## Packets (§6), in order

P0 adopt and register prefix; P1 byte-store kernel with teeth; P2 programs
and the transcription check; P3 scan, relation, K0-K8 (PRF-007 re-cited at
K4); P4 ACL2-owned frontier/config frames and K11; P5 journals K9/K10
(`model-gaps=0`); P6 campaign v2; P7 assumptions swap; P8 checkpoint hookup
after w3 lands; P9 retirements; P10 platform qualification (process death
only, no power-loss claim). Each row carries an acceptance criterion the
coordinator can check without reading the lane's summary.

## Decisions the coordinator must make

1. Approve the `fn-bs-` prefix and the four proposed book names.
2. Approve P4's store-format change (frontier and config become frames);
   it is the only packet that touches on-disk bytes.
3. Confirm P8 waits for `w3-checkpoint` to commit `tools/checkpoint.py`; the
   transcription in §2.2 is from its uncommitted worktree.

## What this lane did not do

No book was written, no theorem proved, no host line changed, no prefix
registered. `specs/failures.md` and `store-refinement.md` are not edited;
§4 says which sentences P7 and P9 replace.
