# Experimental receiver BP request and receipt decision

Status: integrated experimental ACL2 receiver model. This is separate from the sender-side
`fn-bp` workflow. It decodes the experimental canonical BP ADU request codec,
accepts an exact already-durable article under a trusted local lab policy, and
constructs an unsigned receipt ADU only after a committed receiver decision.

`fn-bpr-accept-request` requires a successful typed request decode, exact
request article and subject equality with an actual `fn-bpr-store-record-acceptedp`
Store record, configured destination and policy identifiers, and an explicit
local `A_POLICY = t` input. Request source EID, origin incarnation, and wire
authorization context are retained as request context; none authenticates the
sender or authorizes receipt emission.

The recovered acceptance predicate requires a valid Store in file phase `:ready`,
exact membership of the encoded record in authoritative recovered records, and
the matching node article/subject/archive binding. Transient success history is
not reconstructed on reopen and cannot serve as this gate.

The durable context binds work ID, accepted Message-ID, subject, archive ID,
peer EID, policy, origin incarnation, authorization context, terms, and exact
request. A second equal context is duplicate; a changed context for an existing
work ID or Message-ID is conflict. A receipt is pending after preparation and
has no encoded ADU until `fn-bpr-commit-receipt :committed`. Regeneration takes
only the exact stored request and produces the same canonical receipt ADU. BPA
BIDs are transport metadata and do not appear in the decision or receipt.

The FNRJ receiver journal persists typed request contexts, receipt intents and
decisions, then replays them through this model against the actual recovered
Store. It is distinct from the sender's FNWF journal. The [receiver adapter](bp-receive.md)
stages the complete ADU before parsing, commits acceptance and the receipt
decision before BPA deletion, and regenerates the same receipt after reopen.
The older `bp-receipt-host` wrapper remains a process-local model harness.
No signature is selected and this experiment makes no cryptographic or
authenticated-transport claim.
