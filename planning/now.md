# Current work: W12 operational repair and composition

Priority correction (2026-09-21): the user reaffirmed D07, **no Python in a
running/deployed fn node or its operator CLI**. Sol's owner-convergence lane
finishes its coherent ACL2 integration checkpoint, then adopts that machine in
the native Lisp service. Sol's native-storage lane supplies shared I/O and
concrete codecs; Terra inventories and implements independent native CLI/config
and packaging work. BP remains native. Python service measurements are diagnostic
baselines; production claims require native two-node evidence. Preserve the full
selected feature set and its assurance obligations during this migration.

The user also requested a high-assurance, pleasant implementation with duplicated
decisions and awkward interfaces consolidated. The [consolidation audit](duplication-audit-2026-09-21.md)
tracks concrete findings and owners. A BP candidate's visible-file fallback after
failed publication barriers was repaired in the integrated `2dab68d` packet,
with actual-error and restart evidence. Outcome aggregation and repeated journal scans are
separate assigned work. This extends the one-owner rule to raw Lisp as well as
Python; the native migration is not permission to reproduce the same twins.

Development has resumed from `8b474e2`. Both outbound feed and transit repair
branches are merged. Their [combined book certification](evidence/manifests/certify-20260921T051833Z-3941584.json)
does not establish the behavior of the merged packaged service; the selected
matrix predates that combination.

The [active cycles](swarm-cycles.md) assign isolated implementation lanes for
reader/transit authorization, coherent proof artifacts, feed journal durability,
physical storage correspondence, concrete storage codecs, durable native BP
sequence allocation, shared CLI/NNTP submission, and ACL2 outbound framing.
Both hbox and persvati are used for owned certification and integration work.
Root integrates coherent batches and updates the registries from their evidence.
The first auth/feed/framing/artifact batch is integrated at `cdbd6b2`; Terra
completed the frozen two-node runtime exercise on hbox. The TAKETHIS probe
stall was a harness ordering defect, corrected in a scoped supplemental run.
The original run still has authentication-gate disagreements on both nodes and
a BP crash disagreement; Sol owns diagnosis with the producing lanes. It is
not a passing service result. Luna
finished the frozen-source ledger synchronization. Storage codecs and the
scoped physical relation packet are integrated at `1501492`; metadata
initialization and first-frontier results do not establish full current-host
initialization or general recovery. Terra now owns the feed correspondence
continuation and a fresh initializer transcription; both Astra proof lanes have
handed off their checkpoints. Luna registered the scoped storage evidence
as PRF-044; the conditional scope and missing host correspondence remain explicit.
The overnight goal remains active. Luna handles bounded mechanical work, Terra
implementation, and Sol substantial implementation/proof debugging and combined
owner-service integration. Astra handles periodic cross-project review and
difficult residual problems. Native metadata, frontier, transaction naming and
posting provenance now use ACL2 definitions in the integrated native adapter;
the [codec packet](evidence/native-storage-codec-w13-2026-09-21.md) records
byte-identical committed frames and the remaining staging recovery differences.

The principal composition obligations are explicit: durable article acceptance
must preserve feed intent; uncertain persistence must fence all mutations;
storage proofs need the actual host-generated program inputs and concrete
codec realization; native BP needs persistent allocation before its larger
lifecycle can claim non-reuse. A proof of an uncalled sibling does not close a
running path.

v0 retains the [full two-peer release scope](milestones.md#release-shape-v0-and-v1).
v1 reaches M6 and beyond. Next cycles compose native BP, live configuration,
checkpoints, statement authority and provenance, then broaden recovery,
long-lived retention and the integrated feature matrix. These are planned
outcomes, not declarations that the current implementation already provides them.

The [evidence index](evidence-index.md), [assurance matrix](assurance-closure.md)
and [implementation status](../docs/implementation.md) retain scoped historical
evidence. A passing scaffold check is not certification; certification is not a
running-system, RFC-conformance or mission-qualification claim.

The next integration order is the combined live-config/submission/feed path,
native BP receive integrity and allocation/lifecycle crash joins, then persisted identity
and admission context, checkpoints/index adoption, and bounded long-lived
operation. Prerequisite-ready work continues in parallel. Fresh initializer
transcription and native metadata adoption close existing assurance gaps;
they are not new release scope.

Design discussion should now settle deployment resource targets, human/agent
principal and delegation semantics, and offline policy/restore/release behavior.
Existing D09/D11 proposals are inputs, not selected requirements. The performance
baseline now includes a [source-pinned direct native sample](evidence/performance/native-image-direct-20260921T0414-final.md):
one 1 KiB store post, initialization, reopen and reader startup. It does not
measure the concurrent native owner, scaling or the two-peer release workload.
The historical scale measurements and placeholder native comparison do not
qualify this head; the converged owner still needs its own measurement.

Native BP carrier convergence through `2dab68d` is integrated with a certified
persvati image and source-pinned allocation/spool/queue/crash tests. The
[evidence record](evidence/bp-convergence-native-2026-09-21.md) retains the open
receive fencing, fault classification and session evidence overwrite findings.
PRF-045/046 now name the universal allocation/lifecycle obligations without
promoting helper lemmas to whole-path proofs. Native FNWF/FNRJ composition is
being repaired for remaining host admission/naming decisions before landing.
