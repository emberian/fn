# Wildmat and file-publication integration — 2026-09-18

`make test` passed on revision `fe02b6e`: 33 ACL2 logical/assertion roots,
the actual acceptance simulator, and 31 Python tests (4 tooling, 10 reader,
17 store). The selected source hashes were unchanged during the run. A subsequent
independent Python 3.9.6 `nntplib` probe passed against an actual reopened store,
including filtered LIST ACTIVE and LIST NEWSGROUPS.

The [machine-readable record](2026-09-18-wildmat-storage.json) retains commands,
versions, source/certificate digests, outcomes, and raw log locations. Tooling:
ACL2 8.7, SBCL 2.6.8, Python 3.14, macOS 26.6.1 arm64. The
[article batch](2026-09-18-articles.md) and earlier records remain unchanged
historical snapshots. The maximum-profile probe belongs to the earlier storage
batch and was not repeated here.

## Added behavior and evidence

| Area | Established scope |
| --- | --- |
| Wildmat | Strict UTF-8 decoding, RFC 3977 §4 grammar, whole-character `?`, anchored/rightmost matching, and bounded dynamic-programming rows; RFC/malformed/limit/star-heavy assertion vectors |
| Filtered listings | ACL2 parses each pattern once and filters configured groups for LIST ACTIVE/NEWSGROUPS; empty results and errors preserve session state; independent client checks both variants |
| Command boundary | 510 content octets plus CRLF; 497-octet actual arguments; minimum-three-character keywords; BOM and malformed UTF-8 rejection; boundary and socket regressions |
| LIST errors | Supported forms retain 215 behavior; known unmaintained forms use 503 with valid arity, unknown/malformed forms use 501; capability advertisement remains VERSION/IMPLEMENTATION |
| File model | Executable allocator replacement, one-use reservation, immutable record publication, old/new and absent/exact crash choices, actual replay, completion gate, and five recovery barriers |
| File-model proofs | Initial state and start-frontier preservation; general fence rejection, matching-completion requirement, incomplete-recovery gate, allocator-error and lost-completion fencing |
| Real completion faults | Rejected completion, failed reply before completion, and lost reply after actual core completion leave the host fenced and emit no success; reopened files retain the article and pin |
| Real allocator faults | A failed directory barrier after successful frontier replacement is recovered by rereading the observed disk frontier, including through the same Store object; the next post uses the advanced identity |

The file-model trace tests cover pre-attempt abort versus attempted-publication
uncertainty, completed-barrier survival, exact candidate survival, lost replies,
recovery gating, and non-reuse after refusal/abort/recovery. A fresh allocator
barrier produces a one-use `reserved` state; ordinary ready state cannot reuse
the last consumed identity. A frontier candidate must fit uint32 too.

## Remaining boundaries

- Wildmat definitions and examples certify, but there is no general proof of
  UTF-8 decoding, grammar correspondence, DP semantics, or work/allocation bounds.
  Its algorithmic O(m*n) argument is not a mechanically proved complexity result.
- The file kernel does not prove preservation for every transition or crash,
  acknowledged-history survival, or a refinement of the Python/POSIX adapter.
  It calls existing replay with supplied groups/capacity; it does not carry a
  live pending node. Matching core completion remains an explicit observation.
- Configuration/frame validation, syscall association, atomic namespace behavior,
  retained stable storage, checksum behavior, and physical barriers require the
  premises in the [refinement contract](../../specs/store-refinement.md).
  Tests do not qualify power loss or detect a wholly valid rollback.
- Network POST, full article injection, complete READER/OVER, native signatures,
  live concurrent posting, private groups, and DTN integration remain unfinished.
- Record accepted-input canonicality is separate unfinished proof work and is
  excluded from this frozen source set and default certification roots. Primitive
  canonicality and full value/record round trips retain their earlier evidence.

No broad requirement, proof target, or implementation milestone is closed here.
