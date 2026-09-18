# Privacy and group encryption

Status: design discussion. The user requires a sound cryptographic design rather
than a naive encryption feature. D04 selects shared community groups first with
privacy boundaries designed now. D09 and the later group protocol remain open.
No encrypted-group protocol
or library has been selected, implemented, or audited for fn.

## Recommendation and candidates

Build shared community groups first while specifying privacy boundaries now.
Evaluate an established group protocol and maintained implementation before
shipping private groups. MLS is one candidate whose membership/ordering requirements
may not fit fn; relevant research protocols can also be evaluated. A new ePrint
design needs security analysis, implementation evidence, and review before adoption.
This is not a decision to implement MLS from scratch or adapt its cryptographic rules.

Matrix's Megolm uses sender sessions and documents partial forward secrecy and
absence of post-compromise recovery within an unchanged compromised session.
Rotation, secure key sharing, and history handling are application responsibilities.
Those are tradeoffs, not a basis for calling the entire Matrix system insecure.
[Megolm specification](https://spec.matrix.org/unstable/olm-megolm/megolm/)

MLS targets asynchronous groups with forward secrecy and post-compromise security.
Delayed-message processing still needs retention/work bounds.
[RFC 9420](https://www.rfc-editor.org/rfc/rfc9420.html)

MLS membership evolution requires agreement on a sequence of commits/epochs.
Disconnected concurrent changes therefore need an application delivery policy;
fn's commutative object-set merge does not solve that ordering problem.
[RFC 9750 §5.2](https://www.rfc-editor.org/rfc/rfc9750.html#section-5.2)

## Boundaries to preserve now

SEC-001: define a private profile's trusted endpoints and visible metadata before
claiming confidentiality. Separate transport protection, membership/access control,
and end-to-end encryption. Record what relays and members learn from sizes,
routing, inventories, signatures, receipts, and timing. Relays should be able
to retain/deliver opaque ciphertext without reading inner news metadata.

SEC-002: distinguish retained ciphertext, endpoint plaintext archives, and live
cryptographic secrets. Do not put ratchet secrets or private keys into the generic
replicated immutable object store/journal. A crypto-state adapter must follow the
selected library's persistence, deletion, backup, and rollback requirements.
Crash-induced nonce/state reuse belongs in its integration validation.

D03's indefinite retention does not require preserving every old group secret.
Decide whether recipients keep private archives and how those are recovered.
A recoverable archive has a corresponding decryption authority; compromising
that authority can expose the archive. Protocol forward secrecy and archive
protection need separate threat models.

SEC-003: distinguish public transferable author signatures from private
conversation authentication. Decide whether private articles carry transferable
authorship evidence, where signatures live, and whether group-specific identities
are needed. D02 does not imply publishing private metadata outside encryption.
Plaintext hashes and cross-group deduplication indexes must not silently leak
content equality or guesses in a private profile.

SEC-004: before selecting/shipping group encryption, exercise offline membership
changes, delayed messages, device loss/rejoin, compromise, replay, backups, and
state rollback with the chosen implementation. Define when revocation is effective
for each sender. A disconnected sender cannot act on a change it has not received.
Do not invent a new ratchet/fork-merging construction to hide that tradeoff.

## Private-profile decision agenda

| Question | Example to resolve |
| --- | --- |
| Endpoints | Does a private NNTP gateway decrypt for its human, making that host a trusted endpoint? |
| Partitioned membership | Two sites remove different devices while disconnected; what can each safely send? |
| History | Can a new member or replacement device read pre-join messages? |
| Delayed delivery | A letter arrives six months later from an earlier epoch; which secrets remain and why? |
| Archive/recovery | A laptop is lost; what recovery authority exists and what compromise exposes? |
| Authorship | Are private statements publicly attributable, group-attributable, or intended to be deniable? |
| Metadata | What can a relay infer from identifiers, sizes, inventories, and receipts? |
| Crypto lifetime | Which quantum/longevity assumptions and upgrades fit the archive horizon? |

Evaluate published security analysis and current implementation/audit status
when selecting a library. ACL2 can prove fn's modeled integration behavior under
explicit crypto assumptions; it does not make an unevaluated composition sound.
