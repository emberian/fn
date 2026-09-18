# Terminology

| Term | Meaning in fn |
| --- | --- |
| Octets | Exact byte sequence; never implicitly Unicode-normalized. |
| Content object | Immutable typed bytes with a versioned content identity. |
| Object ID | Domain-separated digest identity under an explicit algorithm/profile. |
| Message-ID | The news identifier; distinct from a digest and compared exactly. |
| Source article | Preserved article bytes with provenance; exact native profile remains open. |
| Wire variant | A particular NNTP representation, potentially including different relay headers. |
| Article record | A local association between news identity, source objects, provenance, and policy decisions. |
| Group membership | One local group-number association for an article. |
| Statement | An immutable assertion with issuer and scope; authentication/authority are separate checks. |
| Receipt | A statement acknowledging a specifically identified event or undertaking. |
| Obligation | A locally accepted responsibility to retain or deliver identified content under explicit terms. |
| Reservation | Accounted capacity for fulfilling an obligation, including metadata and recovery overhead. |
| Pin | A reason an object is presently ineligible for reclamation. |
| Commit | Atomic publication of a local transaction after the required durable barrier. |
| Transaction | One local state change containing all of its allocation and obligation effects. |
| Journal | Authoritative local sequence of transaction records. |
| Checkpoint | A recoverable committed state tied to a journal frontier and format version. |
| Projection | A view computed from retained facts and local policy, such as an NNTP group. |
| Incarnation | An origin's sequence namespace; prevents a restored node from silently reusing sequence identities. |
| Fact-set convergence | Same validated portable facts after receiving the same inputs under stated validation assumptions. |
| Local acceptance | Durable local transaction; distinct from remote delivery and human reading. |
| BP | Bundle Protocol, a store-carry-forward overlay; fn is an application above it. |
| LTP | Licklider Transmission Protocol; a possible convergence layer beneath BP. |

“Received”, “accepted”, “forwarded”, “delivered”, and “read” are not synonyms.
A signed receipt identifies a speaker and statement; it is not physical proof
that an untrusted speaker saved bytes. An object hash checks content identity
under cryptographic assumptions; it does not repair missing content.
