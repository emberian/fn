# Current work: W12 operational repair and composition

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
is measuring the combined two-node runtime on hbox; that run has exposed a
transfer-probe stall under investigation, not a passing service result. Luna
finished the frozen-source ledger synchronization. Storage codecs and the
scoped physical relation packet are integrated at `1501492`; metadata
initialization and first-frontier results do not establish full current-host
initialization or general recovery. Terra now owns the feed correspondence
continuation and a fresh initializer transcription; both Astra proof lanes have
handed off their checkpoints. Luna is registering the scoped storage evidence.
The overnight goal remains active, with routine work assigned to Luna/Terra
and Astra reviewing larger batches.

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
