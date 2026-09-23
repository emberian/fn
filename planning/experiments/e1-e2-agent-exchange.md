# E1/E2 experiment contract: sleeping-agent correspondence

Status: **proposal**, 2026-09-23, against `24a5df6b`. The user selected the
report/receipt plus reply, consumer-owned durable inbox/outbox with explicit fn
cursor/acknowledgement, and two separately administered stores with trusted
transport peers ([decision register](../decisions.md)). This contract does not
extend the selected v0 gate, define a server API, or add proof events. It
specifies the experiment to implement after the T10 authorship/verdict and
A1–A3 BP joins have their own evidence.

## E1: one immutable exchange

Agent A authors article **R**, a versioned dregg report with its application
receipt bytes. Agent B sleeps while R crosses A's native submission, a legacy
NNTP relay, and the BP path to B's separately administered store; carried-media
import is exercised where supported. On waking, B verifies the *exact authored
source* and the application payload with its own verifier, records the report,
and later authors article **Q**, a reply to R. A wakes and consumes Q. Both
stores make their own acceptance, numbering, capacity and visibility decisions.
The report's dregg receipt, an fn retention receipt, a BP status report, and
B's later consumer acknowledgement are different objects with different
issuers and claims.

The experimental application envelope is a bounded **opaque byte payload** in
the signed authored source, not a new core statement kind or executable form.
Its logical fields are `(application-id, payload-version, operation-id,
correlation-id, dependency-references, kind, payload-octets)`. `kind` is
`report-receipt` or `reply`; R chooses a fresh operation ID and Q names R's
operation ID and immutable source identity as its correlation and dependency.
Dependencies are a bounded list of typed content/source references; a missing
dependency is reported to the consumer, never chased without a work bound.
Message-ID identifies the NNTP article, the source identity identifies exact
bytes, the application operation ID identifies a logical retry, and each BP
bundle/attempt has its own transport identity. None substitutes for another.
A repeated operation ID with different source bytes is preserved as an
application-level conflict by the consumer, not selected by arrival time or
silently executed twice. fn's existing article deduplication does not inspect
this opaque operation ID.

Only the selected exact-source dual-signature profile, Ed25519 **and**
ML-DSA-65 over the profile's domain, principal, ordered keyset and authored
bytes, can yield a native authorship verdict. Historical verification needs
the acceptance-time key context and durable verdict once T10 provides it.
The dregg receipt is independently parsed and verified by dregg; a valid fn
author signature does not assert that application result. An unknown payload
version or unsupported author profile remains bounded evidence where article
policy admits it, with **no** application or administrative authority. A
legacy relay may add trace/injection projections but must return the signed
authored source unchanged. An existing text-oriented `fn_client.py post`
normalizes line endings and is therefore not the byte-preserving authoring
path for this experiment; use the future native signing/carrier path and
compare bytes at each hop.

The carrier lane's v1/suite1 proposal fixes nine canonical CBOR items and a
5405-octet binary carrier cap (8192 base64 field cap); those are *signature
carrier* limits, not permission for an E1 application payload of that size.
It keeps `FN-Authorship` distinct from `FN-Statement`, and a sole supported
`fn-hybrid-v1` tag; its encoder-length gate is still under proof. E1 vectors
must use the carrier's certified limit and report an oversized application
body separately.

The byte grammar and numeric limits remain experimental. The implementation
must pick finite maximum payload, reference count/depth, article size, BP ADU,
staging charge and per-peer retained evidence before accepting a vector.
These are separate limits: A1's draft held-image bound is 131072 octets while
the existing `fn-bpb` payload limit is 1 MiB, so neither can be copied as a
universal E1 payload bound. If R cannot fit the chosen whole-article acceptance
unit, the test reports refusal or a measured need for a bounded manifest; it
does not silently split R into independently accepted application operations.

| Step | Observable, identity-preserving event |
| --- | --- |
| A1 | A signs R's exact source, commits it locally, and records its Message-ID, source identity and operation ID. |
| A2 | A enqueues R for B; outage, restart and retry can change BP attempt identity but not R's application operation. |
| B1 | B's distinct Store commits R under B's local number and may issue its own fn retention receipt; B's agent is still asleep. |
| B2 | B's agent wakes, verifies source and dregg payload, commits inbox R plus outbox Q, then acknowledges its consumer cursor. |
| B3 | B posts the same Q source from its outbox and settles an uncertain post by lookup. |
| A3 | A's agent wakes, independently verifies Q's author and correlation to R, then records its application result. |

| Adversarial E1 vector | Required observation |
| --- | --- |
| Relay changes one authored payload octet but keeps Message-ID | Source/verdict mismatch or explicit conflict; B does not treat it as R. |
| Relay changes only Path/Xref projection | R's authored source and application bytes still agree; provenance changes remain visible. |
| Q names R's Message-ID but the wrong source identity or operation ID | No correlation to R; preserve Q as attributable evidence if article policy admits it. |
| Duplicate BP attempt carries R with the same Message-ID and source; second bundle identity differs | Article duplicate handling preserves one B article/charge under its proved identity contract, while attempts remain distinguishable; application retries under different Message-IDs still require consumer deduplication. |
| Unknown payload/profile, malformed length or oversized dependency list | Bounded preserve/refuse outcome with no dregg authority or unbounded parse work. |
| Valid fn signature on a false dregg receipt | Author attribution may succeed; dregg verification fails independently. |

## E2: a scoped, bounded consumer position

The selected E2 direction now has a concrete proposed v1 operation, identity,
limit and recovery contract in [consumer progress](../../specs/consumer-progress.md).
Its [adversarial trace set](e1-e2-v1-traces.json) identifies the fn and
consumer database observations and the process-death cuts each implementation
must execute. They are specified traces, not passing tests or a served API.

Proposed cursor meaning is `(store-history/incarnation, consumer-id,
query-definition/version, authorization-view/version, committed position)`.
It is opaque on the wire and authenticates those fields; it is **not** a bare
host, TLS certificate, Message-ID, timestamp, BP EID or per-group article
number. A poll returns a bounded page and a cursor for the committed prefix it
scanned, including holes and filtered entries, so a consumer can advance
through an empty page. The first query is a small ACL2-owned selection over
configured groups and, if needed, principal/profile. The server reports
`accepted`, `refused`, or `uncertain` distinctly for state-changing calls.

The consumer owns a durable transaction: insert `(store identity, source
identity, application operation ID, payload verdict)` into its inbox if
absent, apply its local deterministic transition, and append any reply to its
outbox **atomically**. It then acknowledges the page cursor to fn. The
acknowledgement means only that fn durably recorded that consumer's declared
position, not that dregg work was correct, an external effect happened, or an
fn retention obligation was released. A repeated ack is idempotent; one behind
the recorded position cannot rewind it. On an uncertain ack, the consumer
queries its recorded position and may repeat the ack. Posting the outbox item
uses a stable signed source and Message-ID; uncertain posting is settled by
identity lookup before retry, as today's client already requires.

This is at-least-once delivery. Exactly-once local application transitions
require the consumer's own unique inbox key and atomic transaction. An API,
payment, shell command or other external effect needs its own idempotency or
reconciliation; fn's ack cannot make it exactly once. The existing
`fn_client.py` watermark is keyed by host/port and group, advances after
stdout flush, and uses local article numbers. It remains a reader convenience,
not this cursor or acknowledgement.

| Cut in B's consume/reply trace | Durable state after restart | Required next action |
| --- | --- | --- |
| Poll returned R, before consumer transaction | Neither inbox nor outbox has R; fn ack stays old. | Poll R again. |
| Inbox/outbox transaction uncertain | Consumer asks its own store whether R's unique inbox key and Q outbox entry committed. | Commit if absent; otherwise reuse exactly Q. No new operation ID. |
| Consumer transaction committed, before fn ack | Inbox has R and outbox has Q; fn ack stays old. | Poll may repeat R; unique key prevents another transition; retry ack. |
| fn ack uncertain | Consumer transaction remains committed; fn position may be old or new. | Query ack position, then retry same monotone ack if needed. |
| fn ack committed, before Q post | fn position advanced; outbox still holds Q. | Post Q from outbox independently. |
| Q post uncertain | Q may or may not be accepted at B. | Look up Q's stable Message-ID/source; repost only after definitive absence. |
| B accepted Q, before A polls | B's outbox records Q; A's cursor is old. | A polls Q after waking and runs its own inbox transaction. |

A restored/cloned store at the same endpoint with a different history must
refuse the old cursor (`wrong-store`/`rebase-required`), even if its local
numbers repeat. A restoration of the *same* history must prove its selected
incarnation/position mapping; D10's fresh sequence namespace rule cannot be
evaded by copying a hostname or TLS key. If group policy, authorization or
filter changes make old articles newly visible, the old view cursor is
explicitly invalidated and the consumer replays a bounded scan under the new
view, deduplicating through its inbox. It may not simply continue from the
largest article number. A denied article is not disclosed through the cursor.

Poll bounds cover scanned records, returned records, returned octets, token
size and parse work independently. A server-side ack table, if used, has a
configured maximum consumers and bytes, charges metadata before accepting a
new consumer, and refuses at capacity. Ack storage alone creates **no**
unlimited unread backlog or retention pin. Explicit unregister/administration
and crash-safe recovery of ack metadata are needed before claiming a durable
server position; the consumer's inbox/outbox remains the source of processing
truth. The exact ack persistence location and expiry/unregister policy are
still choices for E2 implementation, not selected by this proposal.

The decisive E2 negative traces are: two consumers of R must advance
independently; an old endpoint cursor after store replacement must be refused;
a newly visible old article must be offered after view rebasing; a duplicated
R must leave one inbox transition and one Q; an unauthorized ack or a cursor
for another query must not advance progress; a full consumer table must refuse
before promising a position. Each trace needs a real crash/reopen and an
observation of both the consumer database and fn state, not arrival alone.

## Implementation seam and open choices

The existing native owner/Store already provides immutable article acceptance,
local numbering, explicit three-way completion and retained evidence; the BP
workflow already distinguishes jobs, attempts and retention receipts. The
selected carrier lane supplies the v0 source/profile bytes; A1's draft
`fn-bpnf-step` distinguishes ingress principal, held bundle identity,
submission and receipt handoff. None currently exposes an E2 store-scoped
cursor, durable consumer ack, or atomic consumer transaction. A future ACL2
query/ack decision belongs beside the served owner and committed Store
projection; the native host should only transport bounded bytes and persist
the decision. A consumer library can own its inbox/outbox and dregg verifier.

Before implementation, choose the cursor's exact encoding and store-history
identity, auth/view rebasing rule, finite limits, ack metadata lifecycle, and
the concrete E1 payload grammar with two independent consumers. Key custody
and succession, private-group confidentiality, cross-silo untrusted receipt
authority and external-effect execution remain separate decisions. No claim in
this proposal depends on silently selecting them.
