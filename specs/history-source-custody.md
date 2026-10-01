# Captured all-event history custody

This is the source preparation boundary for the S7/P12 history producer and
remote consumer. Dense frontier F counts every committed Store event. The
article catalog ordinal is not F. An event value NIL is distinct from an
unavailable read: a successful page/provider read returns `:row` with its
value, including NIL. No gap is skipped.

The canonical backing owns Source9:
`(:history-source sourceID concreteEpoch rootID forest maxheight pagecount F ownerPublicationID)`.
Its publication in the owner carries parent6:
`(:history-installed sourceID concreteEpoch rootID ownerPublicationID canonicalOwnerEpoch)`.
`fn-owner-history-install-publication` obtains the source from the backing
and the epoch from actual STATE. It belongs inside the same owner transition
that installs Store, CP and configuration. `fn-owner-history-source` reads
that association and rejects an old parent epoch or inconsistent scalar
stamps. These bounded metadata checks do not establish atomic publication,
physical provenance, or constructor authority by shape.

Capture debits the actual shared page-read ledger before creating the sole
retained slot and registering its backing epoch pin. Its token is the actual
ledger-issued identity; there is no history-specific shadow counter. The
retained slot stores the exact Source9 and captured F. Read-begin accepts
only that token and an ordinal below captured F. Each read-step rechecks the
actual slot, canonical epoch and registered capture, then performs one
directory step or the separately funded physical lookup. A later append in
the same live epoch does not invalidate the older captured prefix. Native
code supplies neither a root, a leaf, a count nor a completion Boolean.

Cancellation retains the slot, read aliases, pin and charge. An actual terminal
producer must first join every borrowed alias and native callback completion,
then clear its remote holder and quiesce the read. Aggregate release returns
the registered pin while that quiescent authority remains present, and only
then refunds reusable ledger coordinates. The spent identity remains spent.
Long-poll waiting must finish return before sleeping; the sole slot is work
serialization, not a limit on stored history.

The owner checkpoint swap reports its existing `:busy` outcome before durable
replacement while a slot is held. Both selected recovery entrypoints refuse
before clearing an open receipt or loading/resetting history. The independent
canonical epoch in parent6 prevents a stale parent/source pair from becoming
current after reset. Direct reset/import/publication callers must preserve
this custody gate and the same-publication association.

The current source is guarded, and its narrow laws cover exact source
attribution, stale parent refusal and cancellation refusal without STATE
effects. Executable fixtures construct INTERNAL metadata and exercise the
actual slot transitions; they are not physical installation witnesses. The
selected capture tariff and native callback-completion issuer remain
unavailable. The complete logical STATE literal witness is prepared but not
replayed after the shared world closed. Existing source receipts do not
certify changed dependency bytes, a qualified image or a deployment.

Legacy FnHist append can resize the whole rows array and hash table, and its
clear/load path is not bounded scheduling work. The new producer must replace
that path with the all-event backing in the same actual publication; dual
append, whole-history synchronization and replay scanning are not a bounded
publication argument. Actual constructor registration, selected operation
funding, nested provider depth qualification, raw bound-NIL construction and
same Store/CP/source publication remain explicit integration obligations.
