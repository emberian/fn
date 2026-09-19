# Private-profile design packet (C3-08)

Status: research and design. **This packet selects no protocol and no library,
and nothing here is an implementation, a proof, or an audit.** D04 keeps shared
community groups first and defers private encrypted groups; the packet's job is
to make the eventual choice decidable by recording what fn actually leaks, what
fn's disconnection facts are, and which mechanisms of the candidate systems
those facts break. It also fixes the one thing that must not wait: the
admissibility policy a site applies to a late letter, which is now an
executable model rather than prose.

The model is [`books/membership-epochs.lisp`](../books/membership-epochs.lisp),
its keystones are in
[`books/membership-epochs-invariants.lisp`](../books/membership-epochs-invariants.lisp),
and its witnesses and teeth are in
[`tests/acl2/membership-epochs-tests.lisp`](../tests/acl2/membership-epochs-tests.lisp).
It contains no keys, no ciphertext and no digest, and it may not be cited as
evidence about any cryptographic construction.

All external documents in this packet were retrieved on **2026-09-19**. Each
citation names the section that carries the claim.

Sources, retrieved 2026-09-19:

- RFC 9420, *The Messaging Layer Security (MLS) Protocol*,
  <https://www.rfc-editor.org/rfc/rfc9420.txt> (HTML section anchors:
  <https://www.rfc-editor.org/rfc/rfc9420.html>).
- RFC 9750, *The Messaging Layer Security (MLS) Architecture*,
  <https://www.rfc-editor.org/rfc/rfc9750.txt>.
- RFC 9180, *Hybrid Public Key Encryption*,
  <https://www.rfc-editor.org/rfc/rfc9180.txt>.
- OpenMLS README, <https://raw.githubusercontent.com/openmls/openmls/main/README.md>.
- OpenMLS book, *Fork Resolution*,
  <https://book.openmls.tech/user_manual/fork-resolution.html>.
- mls-rs README, <https://raw.githubusercontent.com/awslabs/mls-rs/main/mls-rs/README.md>.
- Megolm specification, <https://spec.matrix.org/unstable/olm-megolm/megolm/>
  (already cited by [`specs/privacy.md`](../specs/privacy.md)).

## 1. fn's disconnection facts

These are the facts the library evaluation is run against. They are fn's, not
MLS's, and they come from the decision register and the specifications, not
from this packet.

| Fact | Source |
| --- | --- |
| F1. Sites stay independently useful while disconnected; batches travel by network or carried media. | A05 |
| F2. There is no delivery service and no total order. Set union of validated immutable facts is the convergence claim; forks and conflicting claims do not disappear through arrival order. | REP-002 |
| F3. Retention is indefinite until explicit authorized release; there is no automatic expiry. | D03, RET-001..004 |
| F4. A letter may arrive months after it was written, and wall-clock time is not evidence of non-delivery. | REP-005, `books/clock.lisp` |
| F5. Conflicting evidence is preserved with explicit provenance; last-writer-wins by wall clock is forbidden. | AGENTS.md, REP-002 |
| F6. Relays should retain and forward opaque ciphertext without reading inner news metadata. | SEC-001 |
| F7. Content identity is a plaintext digest today (`books/identity.lisp`), so equal payloads have equal ids everywhere. | SEC-003, D01 |

## 2. Threat and metadata-leakage matrix

Adversaries: **R** a relay or carrier that holds bundles it forwards; **M** a
current group member; **X** a removed (revoked) member holding old state; **A**
someone who later obtains an archive or a lost device.

| fn artifact | Where it lives today | What it discloses | To | Mitigation, and what it costs |
| --- | --- | --- | --- | --- |
| Group name | `books/store-config.lisp` group table; NNTP `Newsgroups`; batch scope | Which community a letter belongs to, and therefore the social graph of a carrier's route | R, M | Carry an opaque group handle on the wire and keep the human name local; costs cross-site group discovery and operator legibility, and needs a handle-to-name mapping that is itself private state |
| Article size | Bundle payload length, `fn-charge-for-payload` page count | Length of the plaintext to within a page; distinguishes a one-line reply from a photo; over a thread, reconstructs turn-taking | R, M | Pad to a size ladder before encryption (RFC 9420 §15.1 provides padding inside the protocol and §16 notes it is not a complete defence; RFC 9180 §9.7.6 states HPKE does not hide plaintext length). Costs storage and DTN contact budget, directly against D15/D16 |
| Inventory / reconciliation summaries | REP-004 peer inventory, Merkle summaries | Exactly which objects a site holds; with F7, which objects two sites hold *in common* | R, M | Scope inventories per authorized peer and per group, and key the identifiers (§5); costs reconciliation efficiency, since a keyed id cannot be compared across groups |
| Receipts | RET-003 typed receipts, `books/bp-receipt.lisp` | Who accepted what, when, and from whom; a receipt graph is a contact graph even when every payload is opaque | R, M | Receipts bind an obligation id rather than a content id, and a relay receipt need not name the group. Costs the operator's ability to audit a specific article's path |
| Contact timing | BP bundle creation timestamps, `books/clock.lisp` observations | When a site was reachable and who it met; with F4 the timestamps are long-lived and archived | R | Coarsen creation timestamps to a bucket and rely on the Bundle Age path (RFC 9171 §4.4.2) rather than exact wall clock; costs expiry precision |
| Relay knowledge | Path, routing, `fn-bpo-` outbound projections | Topology; which sites are adjacent; which site is the archive of record | R | F6 is the requirement: a relay stores and forwards without parsing inner news metadata. Nothing currently enforces it, because there is no inner encryption yet |
| Content ids | `books/identity.lisp` `sha256:` subject | **Equality of plaintext**, across groups and across profiles (F7) | R, M, A | §5 below: keyed identities |
| Membership commits | Would be new objects in the fact set | Who is in a group and when they changed; RFC 9420 §16.4.1 states MLS does not protect group id, epoch or message frequency from the delivery service | R | Keep commits inside the encrypted envelope where the protocol allows it, and accept that epoch and group handle are visible to a carrier |

The matrix is the answer to SEC-001's "record what relays and members learn".
Two rows have no mitigation that does not cost something fn has already
decided it wants: **size** fights D15/D16's contact budget, and **inventory**
fights REP-004's whole point. Those are the tradeoffs to bring to the user,
not problems to be engineered away quietly.

## 3. The decision agenda, row by row

One section per row of the table in [`specs/privacy.md`](../specs/privacy.md).
Each gives a concrete recommendation and the alternative that was not taken.
None of these is a selected decision; they are what this lane would defend.

### 3.1 Endpoints — does a private NNTP gateway decrypt for its human?

**Recommendation.** Yes, and say so: a private profile's NNTP gateway is a
**trusted endpoint**, listed by name in the profile, and the plaintext boundary
is drawn at that host. An ordinary newsreader cannot hold group secrets, and
D17 puts newsreaders first, so pretending otherwise would be the dishonest
option. The profile records, per group, which endpoints are trusted, and a
site refuses to serve a private group over a listener not on that list.

**Alternative.** A decrypting client-side plugin, making the reader the
endpoint. Stronger — the gateway host never sees plaintext — but it forecloses
D17's "ordinary NNTP clients" goal for private groups and requires a client
implementation per reader.

### 3.2 Partitioned membership — two sites remove different devices

**Recommendation.** This is now the model, not prose. Both removals are
retained as commits in an evidence set merged by id union
(`fn-me-merge`), the conflict is a value (`fn-me-fork-evidence`), and neither
site's adopted chain is revised by the arrival of the other's evidence
(`fn-me-site-merge-never-revises-admissibility`). What each site may safely
send is what its own adopted chain says, and what it may accept is
`fn-me-decide`. Resolution of a fork is a separate, named, authorized act,
never a merge side effect — F5.

Concretely, from `tests/acl2/membership-epochs-tests.lisp`: A removes dave at
epoch 3, B removes carol at epoch 3, and A refuses exactly the letter B
admits. That is not a bug to be fixed by better tie-breaking; it is the
honest state of a partitioned group, and both sites can see it after they
merge.

**Alternative.** A deterministic tie-break over conflicting commits for the
same epoch, which is what RFC 9750 §5.2.2 suggests for an eventually
consistent delivery service ("clients can use a deterministic tie-breaking
policy to decide which to accept"). Rejected as the default because in fn the
losing branch may be months of a site's real history, and F5 forbids
discarding it; a tie-break may still be offered as an *operator-invoked
resolution* whose input is the fork evidence.

### 3.3 History — can a new member or replacement device read pre-join messages?

**Recommendation.** No by default, and the archive is a separate, explicitly
authorized transfer (§4). MLS gives a joiner no access to earlier epochs, and
RFC 9750 §6.6 says a member recovering from state loss "reinitializ[es] ...
does not provide the member with access to group messages exchanged during the
state loss window", though an application may choose to re-supply them.

**Alternative.** Re-encrypt history to the joiner automatically. Simpler for
humans, but it makes every add a bulk disclosure decision taken by whoever
happens to be online, and under F1 that person may be the least informed
member in the group.

### 3.4 Delayed delivery — a letter arrives six months later

**Recommendation.** An explicit two-sided bound, both now in the model.
Backward: a bounded **window** (`fn-me-window`) of epochs behind the local
epoch from which a letter is still admissible; older letters are refused *for
the conversation* while the object itself stays retained under D03. Forward: a
bounded **hold** (`fn-me-hold-limit`); a letter from an epoch the site has not
reached is held, not dropped, and at the limit the site answers `:capacity`,
which is a refusal to take custody, not a silent drop.

This is RFC 9420 §15.3 read as an obligation rather than advice: applications
SHOULD "define a policy on how long to keep unused nonce and key pairs for a
sender, and the maximum number to keep", and SHOULD "define a policy limiting
the maximum number of steps that clients will move the ratchet forward", or a
single message with `generation = 0xffffffff` forces billions of derivations.
RFC 9420 §9.2 is the other side: consumed secrets MUST be deleted immediately,
and unconsumed ones may be kept only "for some reasonable amount of time".
**A six-month delay and immediate deletion of consumed secrets are in direct
tension, and no ratchet resolves it.** The window is where fn states its
choice, in epochs rather than in seconds, because F4 says wall clock is not
evidence.

**Alternative.** Keep every epoch's secrets forever so no letter is ever
undecryptable. Rejected: it converts D03's indefinite retention into indefinite
retention of *live cryptographic secrets*, which is precisely what SEC-002
forbids, and it destroys forward secrecy for the whole archive horizon.

### 3.5 Archive and recovery — a laptop is lost

**Recommendation.** Three stores, separately governed (SEC-002):

1. **Retained ciphertext** — the replicated immutable object store and journal.
   Indefinite under D03. Contains no secret.
2. **Endpoint plaintext archive** — per endpoint, encrypted at rest under an
   *archive key*, written only after a message is admitted. This is what a
   human searches. It is not replicated by the generic object store.
3. **Live cryptographic state** — epoch secrets, ratchets, private keys. Held
   by a crypto-state adapter that follows the selected library's persistence,
   deletion, backup and rollback requirements, never in the journal, never in
   a checkpoint, never in a batch.

Recovery after device loss re-joins the group as a new member (RFC 9750 §6.6)
and restores the plaintext archive from the archive key, not from the group.
The archive key's custody is the recovery authority, and **it is the thing
whose compromise exposes the archive**; that must be said plainly wherever
recovery is offered.

**Alternative.** No plaintext archive: re-derive everything from retained
ciphertext on demand. It removes store 2 entirely, but it requires store 3 to
live as long as store 1, which contradicts §3.4 and SEC-002.

Crash and rollback are integration validation items, not model items: a
restored snapshot of store 3 can reuse a nonce. `books/clock.lisp`'s
`:uncertain` discipline and fn's recovery rules are the right shape, but no
theorem here covers a real ratchet's state file.

### 3.6 Authorship — attributable, group-attributable, or deniable?

**Recommendation.** Keep D02's transferable author signature for **public**
articles, and make private articles **group-attributable by default**: the
signature is verifiable by group members against a group-scoped identity, and
carries no transferable proof for an outsider. Private and public articles then
use different signing profiles under D09's algorithm-tagged containers, and a
private article is never republished with a public signature by accident.

RFC 9750 §8.2.3 names non-repudiation versus deniability as an explicit
application choice; RFC 9750 §8.6 warns that MLS does not protect against
replay by insiders within an epoch and that applications should add a unique
message identifier. fn already has one — the content id — which makes replay
detection cheap, and §5 keeps it from also being an equality oracle.

**Alternative.** One signing profile everywhere, so a private statement is as
publicly provable as a public one. Simpler key handling and fewer profiles, but
it makes every private group a repository of transferable evidence against its
members, which is a decision for the user, not for a lane.

### 3.7 Metadata — what can a relay infer?

See §2. The recommendation is that F6 becomes a checked property of the relay
path: a relay's admission decision must be computable from the bundle's
outer fields alone. That is testable against `books/relay.lisp` today, before
any encryption exists, and should be tested before it is claimed.

**Alternative.** Accept relay-visible inner metadata for the first private
release and document it. Cheaper, and honest if written down — but it leaks
exactly the rows of §2 that have no later fix, because the bundles are
retained indefinitely under D03 and can be re-examined at leisure.

### 3.8 Crypto lifetime — quantum and longevity

**Recommendation.** Treat the archive horizon as decades and plan for
harvest-now-decrypt-later: retained ciphertext under D03 is a standing target.
Require D09's algorithm-tagged containers everywhere before the first private
byte exists, so a suite can be added; prefer a KEM with a post-quantum option
on the roadmap. RFC 9180 §9.1.3 discusses post-quantum security of HPKE's
KEMs, and RFC 9420 §13.1 provides for additional cipher suites; neither makes
today's default suites post-quantum.

**Alternative.** Fix one suite now and migrate later by re-encrypting the
archive. Cheaper to build and possible because fn owns the archive — but
re-encryption cannot help bundles already copied by a relay under F6.

## 4. Archive and key separation against indefinite retention (SEC-002)

D03 chose indefinite retention. The failure mode to avoid is *indefinite
retention of decryption capability*, which is a different promise and a much
worse one. The separation in §3.5 is the design; three rules make it
enforceable:

1. **No secret enters the replicated store.** The object store, the journal,
   the checkpoint and any batch carry ciphertext and public material only. A
   crypto-state adapter owns store 3, outside the replicated path.
2. **Deletion of a secret is not a retention release.** RET-004's release
   predicate governs *objects*. Deleting an epoch secret per RFC 9420 §9.2 is
   not a release, produces no receipt, and discharges no obligation. The two
   vocabularies must not be merged, or an operator will eventually "release"
   an archive by deleting a key.
3. **The archive key has a named authority and a named exposure.** Whoever can
   restore a lost laptop's archive can read that archive. Write it in the
   profile next to the recovery procedure.

What remains open: the exact adapter contract (persistence, atomicity,
rollback detection) and its crash validation. Those are SEC-004 integration
work and cannot be closed by a model.

## 5. Equality leakage under a private profile (SEC-003)

**The leak, precisely.** `books/identity.lisp` derives
`subject = "sha256:" + hex(sha256(payload))` and
`obligation = "archive:" + hex(sha256(msgid || 0x00 || subject))`. These are
unkeyed. Two consequences:

- Anyone holding a subject id can test a **guess** of the payload by hashing
  it. Short, low-entropy payloads (a yes/no reply, a known form letter, an
  address) are enumerable.
- Two sites, two groups or two profiles that hold the same payload produce the
  same id, so a relay or a member sees **equality across groups** without
  reading anything. That is the cross-group deduplication index
  `specs/privacy.md` warns about, and it exists today.

**Recommendation: keyed identities for private profiles.** Under a private
profile, the identity fed to the shared store is
`PRF(group_identity_key, canonical_preimage)` rather than a bare digest, where
the PRF output replaces the digest octets in the existing 71/72-octet
identity grammar so nothing downstream changes shape. Properties this buys:
a guess is only testable by someone holding the group key; equality is visible
only *within* one group; the public profile's ids are unchanged, so public
articles keep D01's transferable identity. An MLS-based deployment can source
that key from an exporter (RFC 9420 §8.5); a non-MLS deployment needs its own.

**Costs, stated.** Cross-group deduplication stops working by construction —
that is the point, but it is also a storage cost under D03. A keyed id cannot
be verified by a relay, so relay-side integrity checks fall back to the frame
trailer. And key rotation changes ids, so the profile must fix whether the
identity key rotates at all (recommendation: it does **not** rotate with the
epoch; it is a long-lived group-identity key, separate from message secrets,
because F3 means ids must stay stable for the archive's life).

**Alternative.** Keep unkeyed ids and forbid private groups from sharing a
store with public ones. Simpler, but the separation is operational rather than
cryptographic, and one misconfigured profile restores the oracle.

`books/identity.lisp` already records that its preimage is not domain
separated. A keyed identity profile is the natural place to fix both at once,
under D09's tagged containers, and it must not silently change existing lab
stores.

## 6. Library evaluation against the disconnection facts

### 6.1 MLS (RFC 9420 / RFC 9750)

| MLS mechanism | Section | Fits fn? | Why |
| --- | --- | --- | --- |
| Epoch ordering of commits | RFC 9420 §14 | **No, not as specified** | "Applications MUST have an established way to resolve conflicting Commit messages for the same epoch ... either by preventing conflicting messages ... or by developing rules for deciding which Commit ... will be canonical." Under F1/F2 fn can do neither: there is no coordinator to prevent conflicts and F5 forbids discarding the loser. §14 also requires minimising the time forked states are held in memory; F4 says the fork may last months |
| Out-of-order and delayed application messages | RFC 9420 §15.3 | **Partly** | The mechanism (group id + epoch + generation, ratchet fast-forward, stored unused keys) is exactly right, and fn's window/hold model is built on it. What does not fit is the implied timescale: §9.2 requires immediate deletion of consumed secrets and only "some reasonable amount of time" for unconsumed ones |
| Deletion schedule | RFC 9420 §9.2 | **Tension with D03** | Forward secrecy depends on deleting epoch secrets; fn's letters may arrive after those secrets are gone. Resolvable only by a stated window (§3.4), i.e. by accepting that some late letters are permanently inadmissible |
| Welcome / add while offline | RFC 9420 §10, mls-rs README ("Asynchronous by design with pre-computed key packages, allowing members to be added to a group while offline") | **Yes** | Pre-published KeyPackages are a good match for scarce contacts (D15) |
| PSK and resumption PSK | RFC 9420 §8.4, §8.6 | **Partly** | §8.6: "Some uses of resumption PSKs might call for the use of PSKs from historical epochs. The application SHOULD specify an upper limit on the number of past epochs for which the resumption_psk may be stored." Useful for proving prior membership after device loss (RFC 9750 §6.6), but it is another long-lived secret, against SEC-002 |
| External commits / external join | RFC 9420 §12.1.6, RFC 9750 §6.1 | **Useful, and a hazard** | An external join lets a recovered device rejoin without a member being online, which fits F1. But RFC 9750 §6.1 notes it authorises "anyone to join who has access to the GroupInfo object", and RFC 9420 §16.4.2 notes the GroupInfo leaks group extensions unless separately protected |
| Agreement on membership | RFC 9750 §6.1 | **No** | "MLS aims to provide agreement on group membership." F2 gives fn convergence of a fact set, not agreement on a sequence. `specs/privacy.md` already says the commutative object-set merge does not solve the ordering problem, and the model in this packet is the statement of what fn does instead |
| Eventually consistent delivery | RFC 9750 §5.2.2 | **Closest fit, still short** | The two suggested strategies are "pause sending ... to account for a reasonable degree of network latency" and "accept ... but keep a copy of the previous group state for a short period", both with deterministic tie-breaking and prompt deletion of forked states. Every one of those phrases assumes a latency scale fn does not have |
| Replay by insiders | RFC 9750 §8.6 | **fn must add it** | MLS does not prevent intra-epoch replay; applications should carry a unique message identifier. fn has content ids, so this is cheap — see §5 |
| Fragmentation by a malicious insider | RFC 9420 §16.12 | **Worse under F1** | A malformed commit can lock out exactly the members who could detect it; "in an asynchronous application, it may be the case that all members that could detect a fault in a Commit are offline", and the affected members must later rejoin externally or reinitialise |

**Implementations.** OpenMLS (README, 2026-09-19) is a Rust implementation of
RFC 9420 maintained by Phoenix R&D and CE Labs, with three supported cipher
suites, pluggable crypto providers, and — directly relevant — a
`fork-resolution` feature whose book page describes the situation as "if
members of a group merge different commits, the group state is called forked
... they have different keys and will not be able to decrypt each others'
messages. **While this should not happen in normal operation, it may still
occur due to bugs.**" Its two helpers are `readd` (remove and re-add the forked
members) and `reboot` (create a new group and migrate state). For fn, forking
is not a bug; it is F1. That the mature implementation treats a fork as a
recovery case is the single clearest statement that MLS's requirements, as
D04's resolution log puts it, "may not fit disconnected operation".

mls-rs (README, 2026-09-19) claims 100% RFC 9420 conformance with all default
credential, proposal and extension types, configurable storage for key
packages, secrets and group state via traits, subgroup branching, PSK support,
and OpenSSL / AWS-LC / Rust Crypto providers. Its storage traits are the right
shape for SEC-002's crypto-state adapter. Neither library removes the §14
ordering requirement, because neither can: it is in the protocol.

### 6.2 HPKE-based sender keys (RFC 9180), against the same facts

The alternative family: each sender holds a symmetric sending key for a group
and distributes it to members with HPKE; this is the shape Megolm uses
(Megolm specification, cited in `specs/privacy.md`).

| Property | Section | Against fn's facts |
| --- | --- | --- |
| No epoch sequencing at all | RFC 9180 §5.1 | **Fits F1/F2.** A sender key needs no agreement on an order; a member with the key decrypts whenever the letter arrives. This is the mechanism's whole advantage here |
| Sender authentication | RFC 9180 §5.1.3 (`AuthEncap`) | Fits §3.6: per-sender authentication without transferable proof to outsiders. §9.1.1 notes key-compromise impersonation considerations |
| Forward secrecy | RFC 9180 §9.1, §9.7.4 | **Does not fit F3 well.** "HPKE does not provide forward secrecy with respect to recipient private key" (§9.1); §9.7.4 makes forward secrecy an application responsibility. A sender key that is never rotated keeps decrypting the whole archive |
| Post-compromise security | — | **Absent.** Removing a member requires every remaining sender to rotate and redistribute. Under F1 that rotation is itself delayed, so revocation takes effect per sender, at different times, at different sites — which is exactly the effectiveness question the model states and bounds |
| Message order and loss | RFC 9180 §9.7.1 | Fits F4: HPKE puts ordering and loss outside its scope, which is where fn needs it |
| Replay | RFC 9180 §9.7.3 | fn must add it; content ids again |
| Metadata and length | RFC 9180 §9.9, §9.7.6 | Same leaks as §2; HPKE hides neither length nor the fact of communication |

**The trade, in one line.** MLS gives strong forward secrecy and post-compromise
security and demands an ordering fn cannot provide; HPKE sender keys give fn's
ordering freedom and demand that fn provide forward secrecy and revocation
itself, per sender, with exactly the delay the model makes explicit. **Neither
is selected here.** D04's resolution log forbids inventing a ratchet to escape
that trade, and this packet does not.

## 7. What would have to be true for private groups to ship

Ordered; each is a gate, not a wish.

1. **A selected protocol with published analysis and a maintained
   implementation**, chosen against §6 with the user, plus an explicit
   statement of which of §6's "does not fit" rows the deployment accepts.
2. **The conflict rule is fn's, in ACL2, and the library obeys it.** The model
   in this packet is that rule; integration means the chosen library's commit
   handling is driven by `fn-me-decide` and `fn-me-fork-evidence`, not the
   other way round, with a named theorem tying the host call to the model
   (AGENTS.md's "theorem subject is the function the host calls").
3. **A crypto-state adapter meeting SEC-002**, with its persistence, deletion,
   backup and rollback contract written down and crash-validated, including
   nonce/state reuse after an uncertain commit.
4. **Keyed identities** (§5) in place before the first private byte is stored,
   with a migration that does not rewrite existing lab stores.
5. **The §2 matrix agreed as the disclosed leakage**, with padding and
   inventory-scoping decisions taken against their D15/D16 costs.
6. **SEC-004's design cases exercised against the chosen implementation**, not
   against the model: offline membership changes, delayed messages, device
   loss and rejoin, compromise, replay, backups, state rollback.
7. **A trusted-endpoint list** (§3.1) enforced by the server, with private
   groups refused on any other listener.

Until 1 to 7 hold, fn's private-group status is: boundaries specified,
admissibility policy modelled and proved, **no cryptography implemented and
none claimed**.
