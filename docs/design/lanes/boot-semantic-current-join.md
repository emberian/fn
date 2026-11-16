# Current BOOT semantic continuation

This source projection is based on `b37d2df9d`; named canonical runtime forms
come from `653f3ff46`. It imports no historical BOOT or CORE. It is unexecuted
source, not a recovered/applied/serving witness.

The actual descriptor CHECKSTEP must first leave its candidate CHECKED with
anchor provenance and five captured root Refs. Then role2 intake must run the
canonical reader/reach consumers, reach complete map coverage and bounded FIFO
validation. Only actual map VALIDATED with matching descriptor, cuts, history,
incarnation and reach generation permits semantic BEGIN. Role5 arena validation
and all other required root roles remain separate authorities; descriptor
checking does not imply any of them.

`boot-semantic-kind` registers only semantic1/work(E); central preindex owns
reader1/map(E)/map-control1/reach(E)/reach-control1. Current C already registers
summary/sources. E is the admitted extent profile, not a stored-entry ceiling.

## Actual child protocol

- BEGIN: `fn2-boot-semantic-start-children(slot gen kind owner generation row
  base budget, checkpoints refs bytes map map-control reach-control semantic
  summary fc fields pool)` returns code, semantic, summary, fc, pool. It invokes
  actual semantic BEGIN then summary BEGIN and resets the exclusive root lease
  and checker. Parent BOOT derives the live owner and current64KiB pool handle;
  it must not call this during a pending read or borrow. No READY input exists.
- TARGET: `fn2-boot-semantic-target-children(checkpoints refs bytes map
  map-control reach-control semantic boot-config pool)` returns READ/address
  from the actual selected Ref and destination fill. No caller cursor can skip
  a sector. Image size is the retained bootstrap-checked configuration.
- Parent issues one ordinary4KiB read to its RX lease and checks the exact
  completion/address/actor generation. COPY takes rxslot, rxgen, budget and
  the same source children (without boot-config), returns code/pool, and copies
  one actual sector at the current page fill. READ loops; CHECK means65536
  untrusted bytes are present. COPY never sets ENTRIES, CAPTURED or APPLIED.
- CHECK: canonical `fn2-checkpoint-restore-semantic-page-reach` validates the
  full hash/header/identity and records the typed reach claim. MORE resumes;
  ENTRIES moves to CAPTURE. Its mutable output subset is8 carriers.
- CAPTURE: canonical `fn2-checkpoint-summary-capture` copies only an actual
  directory entry; revisit is idempotent. CONSUME then runs canonical DFS.
  FIND selects a child or resets/re-reads/re-authenticates the retained parent.
  PAYLOAD-REQUIRED must invoke the actual schema2 payload closure consumer;
  it must never increment the leaf cursor or be mapped to DONE.
- TREE-READY permits canonical summary CLOSE only after exact DFS CLOSED root,
  all descendants/payloads and directory counts agree. This yields CAPTURED,
  not APPLIED. Non-directory semantic schema10 sources remain traversal data.

Suggested parent phases: semantic-begin, semantic-load, semantic-read-result,
semantic-copy, semantic-check, semantic-capture, semantic-consume, semantic-find,
semantic-payload, semantic-close. Existing raw read/harvest/wake is reused;
these child leaves never issue hidden I/O. BEGIN uses128 byte credit; COPY8192;
CHECK4096; CAPTURE/CONSUME use the codec-derived semantic entry bound.

## Missing authority before C application

A captured directory cannot call an unchecked installer. Historical cold APPLY
requires actual selected-source PROJECTED provenance tied to candidate census,
all root roles, allocator/map/arena reconstruction, event/journal validation,
loader capability scan, and an actual persistent Cbase closure hold. Those
constructors are not established by this leaf. Current map/reach intake is
wire-state evidence, not an installed allocator edge or promised-read token.

Ordinary BOOT raw read also needs the composed nonserving/exclusive startup
argument: no allocator reuse may run while these unpinned cold investigation
reads are in flight. The actor's pending/address checks authenticate completion
routing; full-page verification authenticates bytes; neither is a persistent
allocation lifetime promise. Parent must connect actual cold retention/
reconstruction authority before enabling FREE, catalog APPLY or listeners.
Candidate fallback additionally needs a typed pending0/owned-workspace abandon
transition; this first-candidate constructor deliberately does not accept a
caller reset/complete flag or overwrite an active semantic continuation.
