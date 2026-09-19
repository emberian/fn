# Objects and identities

Status: behavioral requirements; native author-signature support plus legacy
gateway provenance is selected (D02). D01 selects exact authored source bytes
with separate mutable trace/injection projections. Concrete field layouts and
profile grammar remain open under D08, D09, D10, and D11 in the
[decision workbook](../planning/decisions.md) govern their realization.

## Logical records

The following are conceptual records, not committed wire schemas or Lisp forms.

| Record | Information it must represent |
| --- | --- |
| Content object | Type/domain, format version, algorithm-tagged identity, exact bytes, byte length |
| Article record | Exact Message-ID, source/variant references, provenance, selected local representation, acceptance policy context |
| Blob manifest | Ordered content/chunk references, logical length, reconstruction profile |
| Statement | Kind, issuer, scope, subject references, terms/dependencies, authenticated encoding |
| Origin event | Origin identity, incarnation, sequence number, optional causal predecessors |
| Group | Local name, authority/configuration context, description, allocation watermark |
| Membership | Local group, non-reused article number, article reference |

OBJ-001: store immutable content. A second insertion of the same verified object
does not mutate its bytes. On an apparent digest collision with different bytes,
stop treating that identifier as an unambiguous reference; quarantine/report the
conflict rather than overwrite or silently substitute content. Cryptographic
collision resistance is an assumption, not a universal injectivity axiom.

OBJ-002: Message-ID comparison is exact octet equality. Do not lowercase its
domain-looking portion. Keep Message-IDs distinct from content digests, origin
event IDs, transaction IDs, paths, and local group numbers. See RFC 5536 §3.1.3.

OBJ-003: preserve original received representations and their provenance. Native
fn source objects travel unchanged. Per D01, author signatures bind exact
authored source bytes, including unknown allowed headers and MIME/body octets.
Mutable Path/Xref and gateway injection records live in separate projections
or provenance and are outside that source signature. Projection changes must
not rewrite signed source or silently strip fields after signing.
Legacy imports may have no author signature and may arrive with different Path
or Xref values. Neither whole-file digest inequality nor Message-ID equality alone
establishes conflicting authored content. Legacy-variant comparison and local
conflict/quarantine policy still need an explicit profile; stripping trace
fields cannot establish the original authored bytes of an unsigned import.

OBJ-004: preserve conflicting claims as distinguishable evidence. Selecting a
local served variant does not declare that arrival order establishes global
truth. Ordinary duplicate suppression must remain available without retaining
unlimited hostile variants: quarantine/evidence storage is subject to quotas.
Replica convergence claims concern validated fact sets, not identical local
variant selection, group numbers, or visibility policies.

OBJ-005: membership indexes refer to committed articles and use numbers local to
a particular server/group. Allocate all memberships of a local cross-post in a
single transaction. Never reuse a number for a different article, including after
expiry or removal. Exhaustion must be explicit; machine integers may not wrap.

OBJ-006: bytes and causal identity do not depend on wall-clock ordering. An
origin's incarnation and counter cannot be reused for a different event. A backup
restore or cloning operation must follow an explicit recovery/fork procedure;
freshness is not inferred from the current time. See D10.

## Article bytes and large content

Preserve octets without implicit charset conversion. Parse fields into a separate
bounded view. Header folding, duplicate fields, MIME, and generated injection
headers must follow the eventual article profile. Parsed caches are not source
bytes. Source bytes are never executed as Lisp.

A small article may be one object. A large body may be stored through a chunk
manifest. Distinguish the identity of reconstructed bytes from the identity of
the manifest describing their storage. Repacking cannot change the logical byte
identity. Chunk size and layout are open; no fixed value is committed here.

Thread references can be missing, malformed, or cyclic in imported news. They
are references to resolve, not permission to recurse without bounds or proof that
all article relationships form a DAG. Preserve useful partial conversations.

## Authority

OBJ-007: support native author signatures and explicit gateway provenance for
legacy NNTP posts in the first release (D02). Authenticate and authorize statements
separately. Receiving a valid
signature does not make its issuer an administrator, prove a physical write, or
authenticate the display name in From. Legacy, gateway-attested, and author-signed
provenance must remain distinguishable. Define signing subjects and key-rotation
rules before claiming end-to-end authorship.

Group names initially describe configured local groups. D11 decides the portable
authority/naming representation. No cross-site consensus service is assumed.
