# Experimental receiver BP request and receipt decision

Status: isolated ACL2 receiver model. This is separate from the sender-side
`fn-bp` workflow. It decodes the experimental canonical BP ADU request codec,
accepts an exact already-durable article under a trusted local lab policy, and
constructs an unsigned receipt ADU only after a committed receiver decision.

`fn-bpr-accept-request` requires a successful typed request decode, exact
request article and subject equality with an actual `fn-bpi-durably-acceptedp`
Store record, configured destination and policy identifiers, and an explicit
local `A_POLICY = t` input. Request source EID, origin incarnation, and wire
authorization context are retained as request context; none authenticates the
sender or authorizes receipt emission.

The durable context binds work ID, accepted Message-ID, subject, archive ID,
peer EID, policy, origin incarnation, authorization context, terms, and exact
request. A second equal context is duplicate; a changed context for an existing
work ID or Message-ID is conflict. A receipt is pending after preparation and
has no encoded ADU until `fn-bpr-commit-receipt :committed`. Regeneration takes
only the exact stored request and produces the same canonical receipt ADU. BPA
BIDs are transport metadata and do not appear in the decision or receipt.

The included host wrapper drives parsing and decisions in ACL2 against the
actual recovered Store state. It is intentionally process-local until the
separate typed receiver journal/replay records are delivered by the workflow
owner. The existing FNWF workflow records are sender-side and cannot encode
receiver origin-incarnation/auth-context safely. No receipt is emitted by the
current host wrapper, no signature is selected, and this experiment makes no
cryptographic or authenticated-transport claim.
