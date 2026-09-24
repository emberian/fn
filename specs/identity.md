# Identity: the crypto seam, principals and key succession

Status: local engineering substrate with a selected native signature suite.
D09 now requires Ed25519 **and** ML-DSA-65 from the first release (user decision,
2026-09-21). The native profile and runtime primitive boundary are implemented;
key custody, remote succession authority and deployment qualification remain
open, and no public ABI is frozen (D08).
Cryptographic unforgeability remains an A-CRYPTO assumption in
[failures](failures.md), not an ACL2 theorem.

The executable profile in `books/hybrid-signature.lisp` binds version 1,
required suite 1, the principal, the ordered algorithm-tagged enrolled Ed25519
and ML-DSA-65 keys, and a length-delimited exact authored-source subject under
`fn-authored-source-hybrid-v1`. Both pure signatures cover those full bytes;
authorship is not reduced to an externally supplied content-id digest.
Both signatures must verify; unsupported, absent or invalid components cannot
authorize via a classical-only fallback. `fn-hsig-authorize` is the final ACL2
decision called through `host/hybrid-signature-host.lisp`. The native boundary
uses libsodium for Ed25519 and OpenSSL 3.5 or newer for ML-DSA-65, sharing the
TLS process library and explicitly fetching the provider algorithm. Callers
supply independent key material. Legacy unsigned NNTP submissions
retain their explicit gateway provenance. The standard primitive is
[ML-DSA in FIPS 204](https://csrc.nist.gov/pubs/fips/204/final);
[OpenSSL 3.5's ML-DSA interface](https://docs.openssl.org/3.5/man7/EVP_SIGNATURE-ML-DSA/)
is the native implementation boundary, not a proved primitive.

The production image exposes `fn hybrid-sign PRINCIPAL ED-PUBLIC ED-SECRET
ML-PUBLIC-PEM ML-PRIVATE-PEM SOURCE`. The first three binary files have exact
widths 32, 32 and 64 octets; the source is read byte-exact up to the article
limit. The command prints separate algorithm-tagged hexadecimal components
only after verifying the newly produced pair through the ACL2 profile. It
stores no keys and defines no custody or recovery authority.

The live owner also accepts bounded `hybrid-enroll` and `hybrid-author`
operations on its operator-authorized local-control socket. `hybrid-author`
verifies both native signatures against the selected enrolled keyring, then
asks ACL2 to render the portable `FN-Authorship` carrier and run the ordinary
news injection decision with the live owner's post configuration and clock.
The injected article gains Path, Injection-Date, and Injection-Info before the
carrier and exact authored source. ACL2 constructs the atomic article/verdict
event only for those same injected octets. The Store content identity and
charge apply to the injected article; the parent separately retains the exact
signed source and its ACL2-derived identity. Its owner-observed acceptance
stamp remains in the embedded record. Recovery checks the stored schema-1
source projection rather than re-running injection, so older accepted
pathless schema-1 records remain readable. Missing, unknown, or substituted
enrollment generations are refusals. This local operator path is not yet the
portable authenticated author transport.

The local operator lifecycle uses the same ordered kind-3 Store history.
`hybrid-enroll CONTROL GENERATION PRINCIPAL ED-PUBLIC ML-PUBLIC-PEM` requires
the next global snapshot generation; it enrolls or rotates only the named
principal's active public-key pair. Another principal's later enrollment does
not retire it. `hybrid-revoke CONTROL GENERATION PRINCIPAL` requires the next
global generation and an actively enrolled matching principal; it publishes a
kind-3 event with the distinct `fn-hybrid-revoked-v1` profile and an exactly
32-octet principal payload. The old `fn-hybrid-v1` snapshot encoding is
unchanged. The new profile cannot decode as an enrollment; unknown profiles
retain their opaque replay meaning. A later explicit local enrollment can
restore operator-local capability, but supplies no proof of key-holder
succession or remote recovery authority. `hybrid-author` now selects the
requested generation only when it is that principal's newest recognized
enrollment. It refuses an older rotated generation and a revoked principal,
without disabling another principal. `hybrid-key-history STORE` gives an
offline, read-only replay view of generation, active/retired/revoked/opaque
status and principal; the writer must be stopped so the Store lock can be
acquired. The view omits public-key payloads and never reads private keys.
Kind-4 accepted events continue to name their exact historical snapshot and
replay their recorded verdict after rotation or revocation. Portable
`hybrid-verify-source` checks an artifact's signatures against its supplied
public key independently of this node's current operator permission; a
delayed remote artifact is not retroactively invalidated by a local tombstone.
The per-principal scan is over ordered keyring snapshots, not the whole
article Store; an indexed active-key table and its correspondence remain a
cost obligation if this history becomes large. This is local same-owner
control policy, not an offline revocation or portable principal-succession
protocol.
For a completed kind-3 Store-node event, the maintained-path projection in
`books/hybrid-lifecycle-store-invariants.lisp` equates the post-finish local
selector to the identity replay step and proves that earlier carried verdicts
are unchanged. Its trace checks the node/file and journal-sequence relations
through A/B enrollment, A rotation, A tombstone and observed reopen. A general
crash-phase relation for all possible lifecycle traces remains an obligation.
On successful `fn-sn-recover`, the carried per-principal selector and accepted
verdict list are projections of the recovered durable records' identity
replay; before- and after-publication crash witnesses distinguish whether B's
enrollment exists after recovery.

`fn-hsig-subject-body-injective` proves that equality of two valid authored
subject bodies implies equality of their principal, ordered Ed25519 and
ML-DSA-65 key set, and exact source octets. The proof projects the fixed-width
fields and the source from the bytes; there are no optional profile fields or
normalization variants. `fn-hsig-signed-preimage-injective` instantiates the
tagged-preimage theorem with the exact hybrid domain tag and those bodies.
Both results concern byte framing below the signature primitives. They make no
claim about signature unforgeability, hash collisions, library correctness, or
key custody.
The book and its concrete hypothesis counterexamples have
[source-matched hbox certification](../planning/evidence/hybrid-injectivity-certification-2026-09-21.md).
The initial failed attempt used older CBOR source and is retained separately.

Books: `books/crypto-seam.lisp`, `books/hybrid-signature.lisp`,
`books/hybrid-signature-invariants.lisp`, `books/principal.lisp`,
`books/principal-invariants.lisp`; tests `tests/acl2/crypto-seam-tests.lisp`,
`tests/acl2/principal-tests.lisp`. The [decision packet](../planning/decision-packet-d09-d11.md)
carries the proposals this profile assumes.

## Portable FN-Authorship v1 carrier (bounded precursor)

`books/hybrid-carrier.lisp` defines a distinct `FN-Authorship` field for the
exact-source hybrid signature. Its canonical binary value is nine ordered CBOR
items: version 1, suite 1, 32-octet principal, Ed25519 algorithm 1 and
32-octet public key, ML-DSA-65 algorithm 2 and 1952-octet public key, then
64-octet Ed25519 and 3309-octet ML-DSA-65 signatures. The encoded binary is
bounded to 5405 octets before emission and before parsing; the base64 field is
bounded to 8192 octets before emission and before decoding. A fixed nine-item
budget and the bounded article parser constrain work before any carrier value
can become a verification subject. A future version or suite is a separate
profile: these v1 bytes keep their meaning, and unknown bounded evidence may
be retained without gaining authority.
`fn-stxe-profile-supportedp` recognizes exactly `fn-hybrid-v1`. The evidence
record's `fn-stxe-authority-verdict` returns `:requires-binding` for that tag:
a tag and stored token alone cannot upgrade arbitrary detail bytes to a
verified author. The T10 Store join must bind the accepted event, keyring
snapshot and both primitive observations before presenting a verdict.

The authored source contains the signed Date, Message-ID, Newsgroups, From and
Subject fields. `fn-hc-native-plan` refuses the mutable namespace in native
source. `fn-hc-received-plan` requires one valid FN-Authorship field, projects
Path, Xref, Injection-Date and Injection-Info outside the signed source, and
retains original received octets on refusal. It also refuses other reserved
fn fields rather than guessing an authored source. This carrier does not give
FN-Statement's content-id signature the semantics of exact-source authorship.
`host/native/signatures.lisp` has a ready verification entry that calls the
ACL2 projection and preimage, asks libsodium and OpenSSL for independent
observations, and calls ACL2's both-required `fn-hsig-authorize`. The actual
The kind-4 accepted-event codec preserves version-0's eleven items and bytes.
Version 1 has thirteen items: the original eleven followed by exact authored
source and its versioned content identity. Replay accepts version 1 only when
the received article projects to that exact source, its canonical carrier
contains the enrolled principal and ordered key set plus both signature
components, and its recorded `:verified` verdict names that principal.
Replay retains the historical verdict without recomputing today's keyring
capability or trusting a profile tag alone. Native acceptance and reader
exposure require a combined image/runtime qualification; the reader projection
is still pending.

The native `hybrid-sign-carrier PRINCIPAL ED-PUBLIC ED-SECRET ML-PUBLIC-PEM
ML-PRIVATE-PEM SOURCE OUTPUT` command writes an ACL2-rendered article with
`FN-Authorship` to a new file after both signatures verify. The companion
`hybrid-verify-carrier ARTICLE ML-PUBLIC-PEM` command reads a bounded article,
uses ACL2's received-source projection, checks the Ed25519 and ML-DSA-65
signatures with native libraries, and asks ACL2 for the final conjunction.
ACL2's `fn-hc-render-at-most` refuses output when carrier expansion pushes the
complete received article over the same article cap the verifier reads.
It reports `verified PRINCIPAL-HEX` (exit 0) or `unverified REASON` (exit 1).
The caller-supplied ML public key must match the carrier's key set. This is an
independent portable artifact check, not Store acceptance or a historical
verdict. The commands use caller-supplied keys and do not enroll, succeed, or
revoke a principal; manual enrollment remains the existing node policy, and
the authority for key succession is still an unchosen D09 decision. A
generated field can travel with an article while the exact signed
source and mutable relay fields remain separate projections.

An agent without the control socket POSTs the `hybrid-sign-carrier` output
over NNTP. The served POST (like a local control `post` and a BP application
submission) takes the classification protected transit takes
(`fnn-owner-attempt-served`, host/native/owner.lisp): ACL2's
`fn-pa-current-plan` over the injected octets and this Store's keyring
snapshots. Absent carrier is the unsigned arm; present and valid under the
node's current enrollment of the principal, with both native observations
verified, is a kind-4 acceptance whose verdict `HDR :fn-verified` reports;
present and invalid is refused with its reason as its own 441 line
(`fn-pa-served-word`), never the unsigned arm. On a served POST an
unenrolled principal is `local-enrollment` (decision register, 2026-09-24
entry on D02's scope).

**Carried, not verified (D23).** NNTP transit asks the same
`fn-pa-current-plan` with one more input: the carried-source list of the
boundary that delivered the article ([peering §1.2.2](peering.md#122-the-carried-source-list-d23)).
When this node has no keyring snapshot of the carrier's principal at all
(never enrolled, never revoked) and that list names it, the plan is
`(:carried source principal keys signatures)`. The node stores the article
byte-exact, as a kind-4 composite whose verdict token is `:carried`, whose
detail is the carrier's principal and whose keyring generation is 0, which
no enrollment has (`fn-pa-carried-event`,
`fn-hsig-article-event-carried-bindsp`). It takes no signature observation
and claims none. Its feed relays the stored octets, carrier intact. `HDR
:fn-verified` answers `carried <principal-hex>`, never `verified`. A node that
enrolled the author verifies as before and answers `verified`. A principal
that is on no list and not enrolled is still refused with
`local-enrollment` (439 on transit). A revoked principal, or one enrolled
under other keys, is refused whatever the list says. Served POST, bound
submissions and BP transit pass no list, so they keep the D02 decision
(`fn-pa-current-plan-without-carried-list-never-carries`).

The companion `hybrid-verify-source ARTICLE ML-PUBLIC-PEM` uses the same
ACL2 carrier projection and native two-suite decision. On success it emits
one `fn-portable-v1` line with lowercase hex fields in this exact order:
principal (32 octets), ACL2-derived authored-source identity (48 octets),
verified Ed25519 key (32 octets), verified ML-DSA-65 key (1952 octets), and
exact authored source (at most 32768 octets). The final newline is required;
the output is bounded below 70000 characters. It refuses malformed carriers,
bad signatures, and nonzero native outcomes rather than emitting partial
source evidence. A consumer compares the full key set and principal with
independent pins, and can derive an application payload only from the returned
authenticated source. This line establishes portable authorship, never local
Store admission, historical keyring enrollment, group membership, or cursor
progress. A source identity in a report without this check and a Store event
reference remains a claim.

At a configured protected peer or BP transit ingress, the receiver classifies
the received `FN-Authorship` field in ACL2. An absent field follows the legacy
article path; a present malformed field refuses without downgrading. For a new
carrier, the receiver selects its own current enrolled snapshot for the exact
carrier principal and ordered Ed25519/ML-DSA-65 keys, observes both signatures
over the exact authored source with native primitives, and asks ACL2 to make
the existing schema-1 kind-4 event. The ordinary Store identity publication
then persists the receiver's relayed article, exact source, local snapshot and
historical verdict together. The configured peer establishes transport
provenance only. A later local rotation or tombstone refuses a new event under
the old key but cannot change an already stored verdict. A byte-identical
duplicate of a previously stored legacy `fn-r` article remains legacy and has
no historical verdict; duplicate suppression never upgrades old acceptance.
These are the selected first-deployment local rules, not portable succession
or a claim that a remote verifier can authorize Store acceptance.

The remaining Store join needs a versioned accepted-article binding with two
distinct subjects: the received article octets used for storage and content
identity, and the exact authored source recovered by the ACL2 carrier
projection. Its admission constructor must show that the carrier's ordered
key set and both signatures equal the historical verdict detail, the selected
enrollment snapshot matches that key set, and both primitive observations
authorized that authored source. The versioned record should carry an ACL2-
derived authored-source identity separately from the received article's
content identity. Replay must check the structural bindings
without promoting an unsupported profile or reinterpreting old kind-4 bytes;
the recorded verdict remains historical, while current capability uses the
current keyring. Only after the composite finish/index theorem covers this
record can a served `:fn-verified` value be attributed to that accepted event.

## The signed bytes

This section is the whole contract an independent verifier needs. Each step
names the ACL2 function that defines it; where the prose and that function
disagree, the function is what the node runs and the prose is the defect.
`tests/test_fn_verify.py` (`SpecBookTieTests`, run by `make check`) fails when
a function or constant named here is no longer defined, or when the book's
constants, this section and `tools/fn_verify.py` state different tag bytes,
widths or dropped field names. It does not compare the layouts themselves;
`FakeNodeVerifyTests` and the native run in the
[P8 record](../planning/evidence/p8-verifier-2026-09-24.md) do that.

**Carrier.** The `FN-Authorship` value is the field's unfolded value with
SP and HTAB removed, then strict base64 (`fn-hc-field-decode`). The decoded
binary is the nine canonical CBOR items above in that order, each with a
minimal head and nothing after the ninth (`fn-hc-decode`). The value is at
most 8192 octets (`*fn-hc-max-field-octets*`) and the binary at most 5405
(`*fn-hc-max-binary-octets*`).

**Authored source** (`fn-hc-authored-source`, over the article
`fn-hc-received-plan` parsed). These are the article's octets, not the NNTP
dot-stuffed wire form.

1. The header is the field lines before the first empty line. A field is its
   first physical line and every continuation line (one starting with SP or
   HTAB) after it. Field names match case-insensitively
   (`fn-hc-reserved-namep` compares the lower-cased name).
2. The received article must carry exactly one `FN-Authorship` field and no
   `FN-Statement` or `FN-Policy` field. Anything else is refused, and no
   source is inferred (`fn-hc-received-plan`, `fn-hc-no-other-reservedp`).
3. Every physical line of every field named `FN-Authorship`, `Path`, `Xref`,
   `Injection-Date` or `Injection-Info` is dropped (`fn-hc-source-header`).
   These are the fields an injecting, relaying or serving agent adds or
   rewrites (RFC 5537 §3.2.1 and §3.5, RFC 5536 §3.2.14). Dropping them is an
   fn profile choice, not an RFC requirement.
4. Every other field is kept in received order. Each physical line is kept
   byte-exact, without its CRLF, followed by CRLF (`fn-stx-field-octets`).
   Folding, whitespace and case are not normalized.
5. Then one CRLF (the empty line), then the body octets unchanged.
6. The result must itself parse as an article with exactly one each of
   `From`, `Subject`, `Date`, `Message-ID` and `Newsgroups`, and with no
   reserved field (`fn-hc-required-sourcep`, `fn-hc-fields-nativep`). It is
   at most 32768 octets (`*fn-article-max-octets*`).

**Preimage** (`fn-hsig-signed-preimage`, which is `fn-digest-tagged-preimage`
of `*fn-hsig-domain-tag*` and `fn-hsig-subject-body`), in order:

| Octets | Content | Defined by |
| --- | --- | --- |
| 2 | `58 1c`: the CBOR byte-string head for 28 octets | `fn-digest-tagged-preimage` |
| 28 | ASCII `fn-authored-source-hybrid-v1` | `*fn-hsig-domain-tag*` |
| 1 | `01`, the profile version | `*fn-hsig-version*` |
| 1 | `01`, the suite | `*fn-hsig-suite*` |
| 32 | the principal | `fn-hsig-subject-body` |
| 1 | `01`, the Ed25519 algorithm | `*fn-hsig-ed25519-algorithm*` |
| 32 | the Ed25519 public key | `*fn-hsig-ed25519-public-key-octets*` |
| 1 | `02`, the ML-DSA-65 algorithm | `*fn-hsig-ml-dsa-65-algorithm*` |
| 1952 | the ML-DSA-65 public key | `*fn-hsig-ml-dsa-65-public-key-octets*` |
| 2 | the source length, unsigned big-endian | `fn-cbor-u16-bytes` |
| n | the authored source | `fn-hsig-subject-body` |

After the tag, the body is raw octets: no CBOR items, no padding. The
fixed widths delimit the key set, and the final length makes an empty or
prefix-related source unambiguous (`fn-hsig-subject-body-injective`). The
principal and keys come from the carrier.

**Signatures.** Both primitives sign the preimage itself, not a digest of
it (a stronger fn choice: authorship is not reduced to a content-id).

- Ed25519 is pure Ed25519 (RFC 8032 §5.1), not Ed25519ph or Ed25519ctx. The
  public key is 32 octets and the signature 64
  (`*fn-hsig-ed25519-signature-octets*`). The node uses libsodium
  `crypto_sign_verify_detached`.
- ML-DSA-65 is pure ML-DSA (FIPS 204 Algorithms 2 and 3), not HashML-DSA,
  with the empty context string: the signed message is `00 00` followed by
  the preimage. The public key is the 1952-octet FIPS 204 encoding and the
  signature 3309 octets (`*fn-hsig-ml-dsa-65-signature-octets*`). The node
  calls OpenSSL `EVP_PKEY_verify_message_init` with NULL parameters
  (`host/native/signatures.lisp`), which is OpenSSL's pure, empty-context
  default. Signing is hedged, so equal inputs do not give equal signatures.
  A verifier checks signatures and never compares their bytes.

Both must verify, and `fn-hsig-authorize` decides. Neither signature alone
authorizes.

## What a `:fn-verified` line binds

`HDR :fn-verified` ([substrate transport §5](substrate-transport.md#5-the-agent-angle); RFC
3977 §8.5 lets a server define metadata items with a leading colon) is the
node's claim. The claim has three limits, and an independent verifier needs
all three.

- **It binds a Message-ID, not content.** The line names the article by
  number or Message-ID and carries no content identity. A node or a path to
  it can therefore serve another article under the requested Message-ID, and
  the line still reads `verified`. A verifier must check that the
  `Message-ID` field in the signed source is the one it asked for.
  `tools/fn_verify.py` does this. It treats a mismatch as not verified, so a
  `verified` line over it is a disagreement (exit 2).
- **The node publishes no keyring.** No NNTP command returns the keys behind
  a `verified` line, and `hybrid-key-history` prints no key material. This is
  deliberate. Keys fetched from the node would only repeat the node's claim,
  so a check against them would not be independent. A verifier pins each
  author's Ed25519 and ML-DSA-65 public keys out of band, from the author,
  and accepts the carrier's keys only when they equal the pins for the
  carrier's principal. Signatures that verify under the carrier's own keys
  do not say whose those keys are. This is a local policy, not an RFC
  requirement.
- **The generation is local.** The `keyring N` term is this node's global
  kind-3 snapshot generation (`hybrid-enroll` above). Every enrollment,
  rotation and revocation on this Store advances it, whatever the principal. Another node's number for the same
  keys is unrelated, and a reader cannot resolve it to keys. A verifier can
  confirm that the carried keys are its pins, but not that generation N held
  them.

A fourth form, `carried <principal-hex>` (D23), is not a claim about the
signature. It says that this node holds the article for a neighbour whose
boundary lists that principal and that the node verified nothing.
`tools/fn_verify.py` exits 3 (cannot decide) on it and reports its own
check beside it. To get a decision, ask a node that enrolled the author.

The line also does not show whether the node should have accepted, that is,
whether enrollment was current or group policy allowed the post. Those
checks are local node policy. The independent check covers the signature
half only.

## The seam

`fn-digest` (any object to 32 octets) and the triple `fn-sig-public-key`,
`fn-sig-sign`, `fn-sig-verify` are ACL2 constrained functions introduced by
`encapsulate` with local witnesses. ACL2 knows exactly four things about them:

| Constraint | Statement | What it does not say |
| --- | --- | --- |
| `fn-digest-shape` | the digest is 32 octets | nothing relates two preimages with equal digests; the local witness is a constant |
| `fn-sig-public-key-shape`, `fn-sig-signature-shape` | a public key is 1 to 4096 octets, a signature 0 to 4096 octets | which suite; hybrid ed25519 + ML-DSA-65 fits (32 + 1952, 64 + 3309) |
| `fn-sig-verify-is-boolean` | verification is a boolean | |
| `fn-sig-verify-of-sign` | for a 32-octet seed `sk` and octet message `m`, `(fn-sig-verify (fn-sig-public-key sk) m (fn-sig-sign sk m))` | that any other signature is rejected: the local witness accepts a signature equal to the public key |

Collision resistance and existential unforgeability are A-CRYPTO. The test
book attaches two realisers with `defattach` and ACL2 proves both satisfy the
seam: a 256-bit polynomial fold, and the input length zero-padded, under which
every equal-length pair collides. That the second one is admitted is the
evidence that the seam carries no collision claim; it rebuilds
`lengthScheme_not_binding` of `~/dev/minidregg/Theory/LaceMerge.lean`.
`must-fail` records that digest injectivity and signature unforgeability are
not theorems.

Shapes mirror `~/dev/breadstuffs/metatheory/Dregg2/Authority/BiscuitGraph.lean`
line 55 (`SigChecker`, an opaque `PubKey -> Block -> Bool` the law only reads)
and `Dregg2/Crypto/CapabilityChain.lean` line 65 (`SigScheme.verify` inside
`VerifyFrom`); the seed-derived hybrid key with a domain-separation context is
`~/dev/breadstuffs/blocklace/src/pq.rs` (`BLOCK_PQ_CTX`, `from_seed`) and
`signer.rs` (`HybridBlockSigner`).

## Domain separation

Every digested or signed preimage is `fn-digest-tagged-preimage tag m`: the
CBOR byte string of an ASCII tag `fn-<purpose>-v1` followed by the message.
Theorem `fn-digest-tagged-preimage-separates`: for a 1 to 64 octet tag and an
octet message within the one-item decoder cap, decoding the preimage yields
the tag item and leaves exactly the message. Theorem
`fn-digest-tagged-preimage-injective`: two tagged preimages are equal only if
their tags and messages are equal. Both are about preimages, below the digest.
Tags in use: `fn-principal-v1`, `fn-statement-v1`, `fn-statement-sig-v1`,
`fn-payload-v1`, `fn-policy-evidence-v1`.

## Principals

A principal id is `fn-digest-tagged "fn-principal-v1" (bstr pk || bstr token)`,
the ACL2 translation of `CellId = blake3::derive_key("dregg-cell-id-v1",
pubkey || token)` in `~/dev/breadstuffs/README-LLMs.md` section 2. The token
lets one key own several principals; a node checks a claimed genesis binding
with `fn-prin-genesis-bindsp` by recomputation.

| Theorem | Property | Hypotheses | Scope |
| --- | --- | --- | --- |
| `fn-prin-preimage-injective` | the encoded (key, token) pair determines both | key is 1 to 4096 octets, token at most 64 octets | the preimage; a principal id determines its key preimage only under A-CRYPTO collision resistance, which `principal-tests` shows failing under the length realiser |
| `fn-prin-id-unfolds` | the id is the tagged digest of that preimage | none | definitional; named so |

## Key succession

A principal's key chain is the state `(id key incarnation next-sequence)`. A
succession is a statement of kind `:succession` (see [statements](statement.md))
by the principal whose payload is one byte string, the new public key.
`fn-prin-succession-acceptablep st s` requires: well-formed statement, kind
`:succession`, creator equal to the principal id, incarnation and sequence
equal to the state's, sequence not exhausted, a decodable key, and
`fn-stmt-verifiedp s (current key)`. `fn-prin-resolve` folds a statement list
through `fn-prin-apply-succession`, skipping what is not acceptable.

| Theorem | Property | Hypotheses | Scope |
| --- | --- | --- | --- |
| `fn-prin-sign-succession-advances-key` | the holder of the current key moves the key to a new one | state well formed, seed's public key equals the state's key, new key well shaped, sequence below 2^32 - 1 | the satisfiable pole, using the seam's `fn-sig-verify-of-sign` |
| `fn-prin-first-key-move-is-verified-under-prior-key` | if resolution over any list moves the key, the first accepted statement is in the list, is a `:succession` by this principal, and verifies under the key held before it | state well formed | conditional on what `fn-sig-verify` accepts; unforgeability is A-CRYPTO |
| `fn-prin-trail-is-valid-chain` | the accepted trail is a chain in which every step verifies under the key its predecessor installed | none | the `VerifyFrom` shape of `CapabilityChain.lean` line 65 and `WellFormed` of `BiscuitGraph.lean` line 55, depth one at each step |
| `fn-prin-resolve-is-resolve-of-trail` | resolving the trail alone gives the same state | none | the skipped statements do not contribute |

Teeth (`principal-tests`): a succession signed by a non-holder is not
acceptable and leaves the state unchanged; a replayed succession, one signed
with the retired key, a wrong incarnation, a wrong principal id, a wrong kind,
an undecodable payload and an exhausted sequence are each rejected; a mixed
list resolves to the expected key with the expected trail.

## Keyrings

A keyring is a list of `(id . public key)` entries, the node's resolved view
of principals; `fn-prin-verifiedp s keyring` holds when the creator is a known
principal and the statement verifies under that key. An unknown creator never
verifies. The operator-local hybrid snapshot/tombstone history above is a
separate, persisted D09 profile; it does not settle this general keyring's
portable succession or revocation under partition. Those policies remain in
the decision packet, and their theorems are conditional on the keyring.

## Assumed

A-CRYPTO for collision resistance and unforgeability; the keyring's genesis
bindings were checked by recomputation; the seed of a principal is held by
the principal (custody is a D09 proposal); the deployed realiser of the seam
is not chosen here.
