# Durable sender workflow adapter

`books/bp-workflow-records.lisp` validates decoded local records and drives the
actual `fn-bp-step` definitions. `tools/workflow_journal.py` owns bounded framing
and filesystem operations; `tools/workflow_bridge.py` invokes ACL2 through the
live recovered Store session. This is the experimental [BP path](bp-path.md),
not a selected native article/signature schema.

## Publication and recovery

Configuration names local/peer EIDs, policy, receipt authority, transport
lifetime, origin incarnation and authorization context. Enqueue binds work to
an already committed article, immutable subject and archive obligation. This
profile permits one work entry per Message-ID and one peer per workflow. The
workflow retains a recovered node snapshot; later Store changes require reopening
the current adapter against the new committed node.

Intent and outcome are separate durable records. An intent permanently consumes
its local transaction/generation pair, including after abort or restart. Before
intent publication, the host reserves two slots and one maximum-sized resolution
record of byte headroom. ACL2 preflight checks context and identity before bytes
are written, against both live state and the complete durable history plus the
candidate record. The history check is pure: it installs no state or effects.
The host writes/fsyncs a temporary file, links the immutable record
name and fsyncs the records directory, then applies that record to live ACL2 state.
Ambiguous publication fences the owner.

Recovery bounds/checks the contiguous namespace and frames, re-establishes
barriers, and replays through ACL2 against the recovered node. A lone intent
remains fenced. Ordinary completion is refused after recovery; an explicit
recovery outcome resolves it. Committed attempt recovery emits no submission.

A live durable attempt outcome grants one exact submit permission, consumed
before the BPA call. Historical replay effects are non-actionable. A lost call
or reply remains uncertainty. Delivery, deletion, expiry and contact observations
cannot release an archive pin or create application evidence. An explicit
policy-matching retry request permits another attempt after delivery if the
application receipt was lost.

Restart may change the live attempt status to `:restart-observed`; that status
is not itself a journal record. Before another attempt, persist an explicit
policy-matching retry request. Otherwise an attempt accepted only because of
the transient restart status would be unreplayable from durable history. The
history preflight rejects that attempt before publication or any BPA call.

## Authority and trust

Receipt checks bind work, subject, issuer, peer, policy, origin incarnation,
authorization context and terms. The local receipt-intent adapter assumes a
trusted A-POLICY check has already authorized its input; it must not be called
directly with remote claims. SHA-256 frame checks detect corruption and provide
no authentication. Receiver receipt emission requires its own durable context
and decision path; the sender's receipt-intent means accepting returned evidence.

FNWF currently allows 4,096 records, 16 MiB aggregate framed bytes, 16 KiB per
record and 512-byte UTF-8 fields. The host validates framing, bounds, integer
types, enums, UTF-8 and SHA-256. It validates these before constructing fixed Lisp
forms; text is passed as decimal octets. ACL2 owns all workflow decisions.
The filesystem, hash implementation, interpreted bridge and local policy remain
trusted boundaries. This adapter does not implement authenticated remote peering,
article deletion, dependency GC, or platform power-loss qualification.
