# Experimental legacy-article BP ingress

Status: isolated executable ACL2 composition experiment. It admits one bounded,
exact legacy NNTP article ADU through the existing article parser, semantic
field extractor, and Store-node acceptance model. It does not select a portable
BP/native fn envelope, a signature, receipt format, or D01 wire contract.

## Boundary and transport staging

The callable model is [`books/bp-ingress.lisp`](../books/bp-ingress.lisp).
`fn-bpi-ingress-prepare` takes four ACL2 values: a Store state already in its
allocator-reserved phase, an explicit local ingress policy, observed transport
context, and one ADU octet list. The ADU is the exact received legacy article
bytes. The model passes those bytes directly to `fn-article-parse` and later
uses the same list as `fn-record-payload`; it does not reconstruct the article
from selected headers or use a host-language parser.

A host integration must stage a bounded downloaded ADU safely before invoking
this model: inventory a BPA bundle ID, obtain it using the non-destructive
BPA download operation, write a temporary file, fsync it, publish an immutable
name, fsync the inbox directory, then call this ACL2 path. It must not use the
BPA endpoint-pop/dequeue operation on this branch. BPA deletion remains after
successful staged processing and must be an explicit operation. This book has
no BPA client or filesystem implementation and makes no durability claim for
those host operations.

The observed context retains destination EID, source EID, local BPA bundle ID,
and lifetime as transport metadata. The policy binds the selected destination
endpoint, configured local Store groups, archive obligation, immutable subject,
policy/terms identifiers, and issuer context. A BPA ID is a local lookup key;
source EID and legacy `From` do not authenticate an author, create an article
identity, or authorize a receipt. Local Store transaction IDs, generations,
sequence numbers, and NNTP article numbers are created only after local Store
reservation and are never sent as part of the portable ADU.

## Parse, field, and policy admission

The parser and `fn-af-proto-article-check` are the only source grammar in this
experiment. The parser's existing bounded octet profile applies. The ingress
requires a single valid `Newsgroups` field and a single valid `Message-ID`;
the fields book permits a missing Message-ID for later injection, but this
inbound profile rejects it. It rejects malformed syntax, missing, duplicate,
or invalid critical fields; Injection-Info and Xref; a destination outside the
configured ingress policy; unknown mapped groups; malformed records; and
refusal by the actual Store duplicate/admission gate.

The parsed Message-ID octets become the Store string by the existing exact
ASCII conversion, while the payload remains the original ADU octet list. Each
parsed Newsgroups octet name must map to an explicit configured local Store
group. The model does not lower-case or choose a winner among duplicate fields
or groups.

## Durable consequence and receipt limit

`fn-bpi-finish-prepared` drives the existing `fn-sn-finish` publication path
with modeled file-kernel observations. `fn-bpi-durably-acceptedp` requires both
the Store success pair and the composed node's published article and archive
binding. Inbox staging, BPA download/deletion, source EID, a transport status,
or a host acknowledgement alone never meet this predicate.

`fn-bpi-receipt-eligibility` returns only unsigned context after that predicate:
Message-ID, immutable subject, archive obligation, policy/terms identifiers,
issuer context, and observed peer EID. It is deliberately not an application
receipt. The current record does not contain a separate durable receipt-intent
and receipt-decision transaction, an explicit A-POLICY authorization premise,
or a selected signature grammar. A receipt implementation must compose those
additional durable decisions and preserve its incoming terms before claiming
application evidence.

## Evidence

`tests/acl2/bp-ingress-tests.lisp` certifies a complete exact-byte ingress,
actual Store finish, duplicate refusal, crash/recovery reconstruction, malformed
article rejection, destination-policy rejection, missing/duplicate critical
field rejection, and unknown-group rejection. These are ACL2 executable
assertions over the same parser and acceptance definitions; no Python parser
participates.

## Isolated host bridge

`host/bp-ingress-host.lisp` loads the certified ingress book alongside the
existing Store host wrapper. `tools/run_bp_ingress.py` passes decimal ADU octets
and bounded observed destination EID, source EID, BID, and lifetime into that
ACL2 wrapper. The static lab policy is explicit in the wrapper: destination
`dtn://fn.lab/inbox`, groups `fn.letters` and `fn.test`, and named lab
policy/terms/issuer metadata. The Python bridge never parses Message-ID or
Newsgroups and never derives an article from the BP envelope.

The bridge imports the coordinated `workflow_journal.py` by an explicit path;
it does not copy or reimplement that journal. It deliberately invokes
`stage_inbound` with a deferred-delete callback, handles the journal's durable
`InboundDeletePending` result, closes and reopens the journal to validate the
published inbound item, and only then reads the journal's framed ADU. A parser,
policy, or Store rejection leaves the inbound file and BPA bundle present.
After `fn-sn-finish` reports actual durable completion, the bridge attempts the
explicit BPA delete. If deletion fails, it reports pending deletion while the
journal item persists. On restart, `fn-bpi-adu-durably-acceptedp` reparses the
exact staged ADU and compares its identity, bytes, groups, archive obligation,
and subject with the recovered node binding. Only that exact prior acceptance
permits a retry delete without allocating a second Store transaction.

`tests/test_bp-ingress-host.py` runs this path against temporary real files,
the coordinated workflow journal candidate, and an interpreted ACL2 Store. It
covers one accepted ADU and exact lookup, a failed BPA delete followed by
fresh journal/Store recovery and duplicate deletion with one transaction, and
malformed/unknown-group ADUs that remain staged and unaccepted. It is a local
host experiment; POSIX fsync behavior and the supplied BPA adapter remain host
assumptions, and no receipt is emitted.
