# Authenticated remote consumers: implementation plan

Source coordinate: `b6dac49d2` plus the stale-ACK scenario increment.
Authority: [PKT-673](decisions.md#2026-09-29-authenticated-remote-consumers-pkt-673).
This is a concrete implementation plan for PKT-255, not a claim that the
remote endpoint or multi-group profile exists. The selected consumer contract
remains [consumer-progress](../specs/consumer-progress.md).

## Endpoint and authority boundary

Use a separate, explicitly configured TLS-only consumer listener. Reuse the
native TLS facility, certificate configuration/rotation and network admission
machinery. Keep the Unix owner socket's same-UID check and every management
operation private. Do not make the control socket reachable by forwarding TCP
connections to its existing dispatcher.

A connection carries a bounded, versioned authenticated consumer request and
one response. Its envelope names the account and credential explicitly,
followed by the consumer operation. ACL2 owns envelope parsing, allowed
operations, credential comparison, scope selection and response octets. The
native adapter provides the protected-channel observation and transports
bytes. A missing protected channel, unknown version, unknown account,
credential failure, cross-account name or management verb refuses before
reading an article or proposing a Store event. No plain-frame downgrade is
permitted on this listener. Existing consumer response/cursor codecs should
be retained where their represented domain remains sufficient.

The operation set is register, rebase, poll, wait, position, status, ack and
unregister, for the authenticated account's own consumer. Bootstrap, account
binding, listener configuration and owner/admin requests are absent. ACL2
checks the current account and current query/view on every operation,
including a resumed WAIT: a credential accepted earlier does not authorize
a later request after deletion/revocation. A credential is never inferred
from a consumer ID, cursor, TLS peer address or account display text.

## Durable query and view

The existing local wrapper cannot supply remote scope. It fixes principal to
`local`, query version to 1 and view to 0, and treats the query ID as one group.
The generic `fn-cp-*` kernel already compares principal, query ID/version,
view, registration epoch, history and incarnation. Retain those comparisons.

A multi-group query needs a durable immutable definition separate from its
opaque cursor ID. It selects a canonical finite set of configured groups;
selection checks exact membership once per event, so a crosspost appears once.
The query's admitted size and representation must come from the supported
operator profile and funded request/work budgets. Do not silently use the
cursor ID's 64-octet field as a ceiling on encoded group names.

Persist a query definition before a consumer registration may reference it.
The ID must resolve to exactly that definition after replay; an unreferenced
committed definition creates no acknowledgement or processing claim. Retries
must reuse the definition and registration instead of allocating a new query
or registration epoch on each uncertain response. No accepted registration
may reference an uncommitted definition. Choosing the concrete config/event
schema is the next implementation step and must be announced to the snapshot
owner before changing its projection.

The caller never supplies authoritative query/view versions. ACL2 derives
them from committed context. A change that may reveal an old article changes
the view version and requires explicit rebase to zero. Conservatively using a
durable configuration generation is safe only if every such change is covered;
article withdrawal/visibility publication also needs an epoch, and ordinary
new articles must not force repeated rescans. A mutable local counter or the
snapshot operation's resource lease is not a consumer view identity.

Account deletion/recreation deserves a specific witness: the existing local
principal derives from login text, so account-incarnation authority must not
be inferred from that digest alone. New effective authority and view must
fence old cursors even when the login spelling and endpoint are reused.

## Exact integration boundaries

- `books/consumer-position.lisp`: reuse register/rebase/ack/unregister scope
  and fresh-epoch decisions. Do not weaken the stale-epoch check.
- `books/consumer-poll-index.lisp` and the concrete history cursor: scan only
  a funded window and yield with exact continuation. Empty/filtered windows
  advance; an unavailable gap does not silently advance. Multi-group and
  withdrawal selection must agree on the same pinned view.
- `host/owner-host.lisp`: new host-called remote decision wrappers derive
  authority from current committed configuration and account state. They
  must consume the carried cursor-domain invariant, never revalidate the
  whole Store. `execution_costs_resume` owns extraction/preservation of the
  actual prepare-consumer wrapper and its relation.
- `host/native/owner.lisp`: publish only the ACL2-proposed event through the
  existing durable consumer completion gate. An ambiguous persistence result
  fences mutation and reports uncertain.
- `host/native/control.lisp`: retain private owner dispatch. A separate remote
  dispatcher must have its own ACL2 allowlist and authenticated context.
- `architecture_reorientation` owns snapshot capture/publication. Its
  source epoch/lease are not account authorization. A schema extension must
  survive its exact consumer projection. Ordinary compaction requires the
  existing-prefix cursor mapping; restore must establish that mapping or
  mint a new incarnation and require explicit rebase.

## Evidence required before the original row closes

For every new host-called boundary, commit the nontrivial scope/no-disclosure,
continuation and durable-effect theorems with reachable positive and
hypothesis-removal witnesses; name an equivalence for every concrete cursor
implementation. Test two accounts remotely over TLS, both correct credentials
and matching-password/cross-account cases; wrong/expired/revoked credentials;
private operation rejection; unknown protocol/cursor versions; overlapping
groups with one crosspost; empty/filtered windows; withdrawal without content;
query/view changes and newly visible old articles; explicit rebase and stale
old token rejection; unregister/re-register/stale ACK; restore/compaction;
reply loss and process death. Preserve refused/uncertain/accepted separately.

PKT-392, PKT-369, PKT-672, PKT-710 and PKT-466(b) now have strengthened source
drivers in this lane, with matching native results pending the runner.
PKT-466(c) remains a separate composition: actual signed R/Q over BP and relay
outage, application deduplication and per-hop identities. The BP lane supplies
transport/recovery; this consumer lane owns that mission integration.

## Implemented request component and durable schema integration

The FNCR logical request codec now exists in `books/consumer-remote-codec.lisp`
with all eight operations. It accepts no authoritative principal, query
version or view version from the client. The account credential is explicit;
the current account must still authenticate it at every request and WAIT
resumption. CNS-011/SCN-1031 retain the full endpoint scope; PRF-1125 remains
planned. There is no remote listener or served host caller yet.

The snapshot producer/recovery owners confirmed that complete consumer state
and entry fields are captured as generic trees. They impose no fixed CP entry
shape. Candidate remote entries can therefore append the immutable group
set and account-incarnation binding to the local eight fields; this is a
current-format schema extension, not a migration fallback. Before doing so:

- `fn-cp-entryp` currently requires exactly eight fields. `fn-cp-apply`'s ACK
  reconstructs those fields and would discard any appended query definition;
  registration, rebase, ACK, recognizer and invariants must change together.
- `fn-cpe-max-octets` is 512 and is the `:consumer` publication reservation
  ceiling. Atomic query definitions require a real codec/reservation change
  matched to the supported profile, not just a larger list in the logical
  event. The current `fn-cpe-encode` grammar only has fixed IDs and integers.
- A durable view identity must account for applicable visibility/control
  publications as well as configuration changes. A current configuration
  generation alone is not evidence of that property. The CP state is exactly
  six fields today; any added carried view scalar requires establishment and
  preservation through its projection and owner transitions.
- Snapshot recovery must retain exact extended fields, while article binding
  remains the other owner's mandatory record12/held16 schema. Consumers must
  use the common article/group/report accessors and preserve that binding.

These are implementation dependencies, not new approval gates or a reduced
single-group remote profile.
