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

`fn-bp-replay-journal` is the function `host/workflow-host.lisp` calls on open
and for the history preflight; `fn-bp-apply-journal-record` is the function it
calls for record preflight and application. `books/bp-workflow-records-invariants.lisp`
proves, over arbitrary record lists: both preserve `fn-bp-statep`,
`fn-bp-binding-statep` and the exact node; a malformed record, or a
configuration record after the first, anywhere in the list makes replay return
a refusal rather than skipping it (`fn-bp-replay-journal-rejects-any-malformed-record`);
a successful live application is exactly one `fn-bp-step` on the record's
event (`fn-bp-apply-journal-record-is-step-when-ok`); and a successful replay
is exactly `fn-bp-trace` of the initial state over the journal's denotation
(`fn-bp-replay-journal-is-trace-when-ok`). The denotation
(`fn-bp-journal-denotation`) is the records after the configuration, each
ordinary outcome as its `:storage-complete` event, each recovery outcome as the
crash-implied `:storage-complete ... :indeterminate` fence followed by its
`:storage-recover` event, and a trailing `:restart`. Replay's effect list is
the trace's effects with the fences' `:recover-required` demands removed
(`fn-bp-actionable-effects`), because the next event in the denotation is their
recorded resolution; the host discards replay effects in any case. A live
recovery outcome is refused unless the image is already fenced, which after a
process restart is what the trailing `:restart` establishes for a lone intent.

A reopen keeps the works its history enqueued.
`fn-bp-replay-preserves-works` says no step of the interpreter
`fn-bp-replay-journal` calls (`fn-bp-replay-records`) drops a work id it was
given, over arbitrary record lists and with no well-formedness hypothesis;
`fn-bp-durable-enqueue-holds-the-work` says the `:ordinary :durable` outcome of
a pending enqueue puts that work in the state. The host's read model for one
work id is `fn-bp-work-status`, and ACL2 owns it: `:absent` means the installed
image holds no such work, `:outstanding` means it holds one with no attempt yet
-- the state a committed enqueue leaves and a reopen preserves -- and otherwise
the answer is the work's attempt status, or `:receipted` once its receipt is
committed. Reading the attempt status alone answered `:absent` for a work that
was enqueued and not yet attempted, which is what made a reopened journal look
empty to `tests/bp-dtn7/run_four_node_lab.py`.

What a reopen does to that answer is `fn-bp-work-status-after-restart` and
nothing else. `books/bp-workflow-replay-status.lisp` proves it twice:
`fn-bp-work-status-of-restart` says the `:restart` transition marks an attempt
that was in flight as `:restart-observed` and leaves `:absent`, `:outstanding`,
`:receipted`, a retryable status and `:delivered` alone, under the single
hypothesis `fn-bp-statep`; and
`fn-bp-replay-work-status-is-the-pre-crash-status-restarted` lifts that to the
function the host calls on open, so a work id in a replayed history reads what
the machine that never died would have answered for it, marked by the restart.
`fn-bp-durable-events` names that machine: the journal's denotation without the
trailing restart. So `:absent` after a successful replay means the pre-crash
machine held no such work, and nothing weaker.

Provenance is a second question with a second answer, because the status word
cannot carry it: a work recovered from a cut and a work enqueued after the
reopen both read `:outstanding`, and they are materially different situations.
`fn-workflow-install-replay` records `fn-bp-work-ids` of the image it installed
-- ACL2 computes the list, the host carries it back unread -- and
`fn-workflow-work-origin` calls `fn-bp-work-origin` on it: `:recovered` for a
work the reopen found in the journal, `:enqueued` for one this session put
there, `:absent` for an id the image does not hold.
`fn-bp-work-origin-at-open-is-recovered-or-absent` says that at open the two
answers are exactly "the image holds it" and "it does not", so `:recovered` is
never said of a work that is not there; and
`fn-bp-durable-enqueue-after-open-reads-enqueued` says this session's durable
enqueue of an id the image did not hold reads `:enqueued`. The lab's
`relay_a_onward_obligation_recoverable_after_kill` reads both: in the session
that resolved the mid-forward cut the obligation is that session's
(`enqueued`), and in the next process it comes back out of the journal
(`recovered`), which is the difference the assertion was removed for lacking.

An attempt record's `bp-lifetime` must equal the configuration's:
`fn-bp-record-contextp` refuses the record otherwise, in the live preflight and
in the history preflight alike, so a submission cannot shorten its own expiry
without a reconfiguration.

The model's "durable intent before submission" theorems
(`fn-bp-step-submit-requires-matching-durable-attempt-completion`,
`fn-bp-apply-journal-record-submit-requires-ordinary-durable-attempt-outcome`)
make a `:submit` effect impossible before the `:ordinary :durable` outcome of
the pending attempt is applied. The word durable is the host's. A-HOST here is
exactly: `tools/workflow_journal.py` writes, fsyncs and links the `:attempt`
intent record before the ACL2 prepare transition runs; it writes, fsyncs and
links the `:outcome` record before that completion is applied; and it calls
the BPA only after `fn-workflow-take-submit` has consumed the single `:submit`
effect of that application. The theorems are about the model's refusal to
grant earlier, not about the host obeying the grant, and not about the drive
honouring `fsync`.

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

## Native operator path

The DTN native image loads `books/app-journal.lisp`,
`host/journal-publish-host.lisp`, `host/native/immutable-publish.lisp`, and
`host/native/workflow.lisp`.  Its `app-journal workflow-enqueue` command opens
one Store, replays FNWF against that same Store image, asks
`fn-workflow-enqueue-record` for the Store-bound enqueue, and publishes the
intent and ordinary durable outcome as separate immutable records.  A later
process obtains status only after replaying those records.

`fn-aj-authorize` is the admission function this path calls.  Its carried
frontier owns the exact next filename, record count, aggregate byte count,
configuration-first order, per-domain frame bound, and intent-resolution
headroom.  Recovery folds each observed name, frame length, and decoded kind
through `fn-aj-recover-record` once; append does not rescan or restat the old
journal.  An authorized operation embeds the initial `fn-jpub` publication
state and its successor frontier.  Raw Lisp executes the requested stage,
file barrier, no-replace link, and records-directory barrier.  It installs the
successor only after `:durable`; an error after link begins or at the final
directory barrier returns `:uncertain` and fences the journal.  An empty open
explicitly resets the workflow domain globals before accepting configuration,
so another journal previously used in the process cannot supply its image.

This is currently an operator and restart/replay path.  The native owner may
call the same store-parametric functions while holding its service lock, but
the composed workflow-to-owner acceptance callback is still an integration
join.  The path does not yet replace the Python BP carrier command or add a
second Store owner.
