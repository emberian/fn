# Article-byte examples for the D01/D09 discussion

Status: D01 selects exact authored source bytes plus separate projections. The
worked examples and candidate encodings below do not freeze the native article
schema, signing algorithm, or persistent ABI. They make
the byte boundaries visible so those choices can be made against concrete input.

The examples use `\r\n` escapes in code blocks. They describe octets; the escapes
stand for the two octets `0d 0a`, rather than the four ASCII characters shown.
Each `\xHH` escape similarly stands for one octet. Body placeholders in later
views refer to the first example, without adding another trailing CRLF. A
placeholder such as `SIG(illustrative)` or `digest=EXAMPLE` is not a valid
signature or digest and must not be used as cryptographic evidence.

D01 now selects signing the exact authored source bytes, preserving unknown
allowed headers and MIME/body octets, with mutable NNTP Path/Xref and gateway
injection records kept in separate projections. The envelope encoding is open. D02 is
selected: native author signatures are supported, while ordinary unsigned NNTP
posts retain explicit gateway provenance. D09's algorithm, key workflow, and
signature container are still open. The proposed deterministic CBOR profile in
`specs/encoding.md` is also not frozen.

## Four views of one article

The example article has a supplied Message-ID, a UTF-8 body, a MIME attachment,
and two unrecognized `X-` fields. It is intended to show what remains byte-stable
as the article passes through an injecting and serving site.

### 1. Submitted proto-article

This is an ordinary unsigned legacy/NNTP proto-article: it has no fn native
envelope and no author signature. It is the posting agent's input before
injection. The following is a schematic
octet listing; the MIME boundary and the escaped body bytes are chosen only for
illustration.

```text
Date: Fri, 18 Sep 2026 12:00:00 +0000\r\n
From: "Aiko" <aiko@example.net>\r\n
Newsgroups: fn.example,fn.utf8\r\n
Subject: =?UTF-8?Q?caf=C3=A9_=E2=80=94_r=C3=A9sum=C3=A9?=\r\n
Message-ID: <aiko-42@example.net>\r\n
MIME-Version: 1.0\r\n
Content-Type: multipart/mixed; boundary="fn-b42"\r\n
X-Client-Note: draft-7; preserve-me\r\n
X-Client-Route: =?UTF-8?Q?caf=C3=A9?=\r\n
\r\n
--fn-b42\r\n
Content-Type: text/plain; charset=UTF-8\r\n
Content-Transfer-Encoding: 8bit\r\n
\r\n
\xe3\x81\x93\xe3\x82\x93\xe3\x81\xab\xe3\x81\xa1\xe3\x81\xaf\r\n
\r\n
--fn-b42\r\n
Content-Type: application/octet-stream\r\n
Content-Transfer-Encoding: base64\r\n
\r\n
AAEC/wo=\r\n
--fn-b42--\r\n
```

The displayed `Subject` and `X-Client-Route` are ASCII encoded-word forms; the
header octets are not an implicit native-character conversion. The text part's
UTF-8 bytes are part of the body octets. The attachment decodes to the five
octets `00 01 02 ff 0a`; whether a future article profile accepts that payload
over a particular transport is a profile question, not a reason to replace it
with a host string.

For this example, the submitted source byte string includes every header field,
its original order and folding, the blank line, MIME delimiters, and body octets.
The two `X-Client-*` fields are unknown to the current fn schema but are retained
as source bytes. A bounded parsed view may index their names and values; it does
not become the source object.

This follows RFC 5536 §2.2's generated-header rules and US-ASCII header-field
profile, RFC 5536 §2.3's MIME mechanisms, and RFC 5537 §2's requirement that
Netnews transports treat articles as octet sequences and convey header fields
unmodified, including nested `message/rfc822` headers. RFC 5536 §3.1.3 puts the
angle brackets inside the Message-ID value, bounds it to 250 octets, and says
that the `id-right` is case-sensitive. fn must therefore retain the exact
Message-ID octets and never lowercase them.

### 2. Injected stored article

An injecting agent adds fields that describe entry into Netnews. A conceptual
stored projection could be:

```text
Injection-Date: Fri, 18 Sep 2026 12:00:03 +0000\r\n
Injection-Info: inject.example; posting-account="aiko-session-7"\r\n
Path: inject.example!.POSTED.aiko-laptop.example!not-for-mail\r\n
Date: Fri, 18 Sep 2026 12:00:00 +0000\r\n
From: "Aiko" <aiko@example.net>\r\n
Newsgroups: fn.example,fn.utf8\r\n
Subject: =?UTF-8?Q?caf=C3=A9_=E2=80=94_r=C3=A9sum=C3=A9?=\r\n
Message-ID: <aiko-42@example.net>\r\n
MIME-Version: 1.0\r\n
Content-Type: multipart/mixed; boundary="fn-b42"\r\n
X-Client-Note: draft-7; preserve-me\r\n
X-Client-Route: =?UTF-8?Q?caf=C3=A9?=\r\n
\r\n
[the exact MIME body octets from the proto-article]\r\n
```

The source object remains the submitted proto-article bytes. The injected view
records the added fields as a projection or accepted representation and keeps
provenance that identifies the injecting site. It must not silently claim that
`Injection-Info` authenticates the person named by `From`.

RFC 5536 §3.2.7 requires `Injection-Date` when an article is injected and says
not to alter an existing `Date`; §3.2.8 defines `Injection-Info` as information
from the injecting server about how the article entered the system. RFC 5537
§3.2.1 defines the Path-prepending process and its `POSTED`, `SEEN`, `MISMATCH`,
and match diagnostics. Those fields are transport/provenance evidence, not
authored source bytes.

### 3. Native source plus versioned envelope

This is a candidate logical record, shown in JSON-like notation for readability;
it is not a selected wire format. `source` is an exact octet string, not parsed
text. The envelope may be encoded later using the proposed deterministic CBOR
profile.

```text
{
  kind: "fn-native-article",
  schema-version: 1,
  message-id-octets: 3c 61 69 6b 6f 2d 34 32 40 65 78 61 6d 70 6c 65
                    2e 6e 65 74 3e,
  source: <the complete proto-article octet string above>,
  source-length: <exact octet count>,
  requested-groups: ["fn.example", "fn.utf8"],
  author-principal: "principal/example-aiko-v1",
  author-signature: "SIG(illustrative; not cryptographic output)",
  provenance: [
    { kind: "gateway-attestation",
      gateway: "inject.example",
      received-account: "aiko-session-7",
      evidence: "ATTESTATION(illustrative; not cryptographic output)" }
  ]
}
```

The repeated Message-ID is checked against the source's exact field octets after
parsing; it is not a normalized display string. The duplicated requested-group
list must likewise agree with the signed source field under the chosen group
grammar; an unsigned wrapper cannot change the signed destination intent. A native signature, if present,
binds an explicitly defined source/envelope preimage. The gateway attestation
binds a statement by `inject.example` about receipt or processing. It does not
turn `From: "Aiko"` into an authenticated author identity. This separation is
the distinction required by `OBJ-007` and the trust boundary in the architecture.

### 4. NNTP serving projection

After local membership allocation, a serving site may expose a projection such
as the following. `Xref` is local to this server and the numbers are not portable
article identity.

```text
Path: fn.example!inject.example!.POSTED.aiko-laptop.example!not-for-mail\r\n
Xref: fn.example fn.example:17 fn.utf8:9\r\n
Injection-Date: Fri, 18 Sep 2026 12:00:03 +0000\r\n
Injection-Info: inject.example; posting-account="aiko-session-7"\r\n
Date: Fri, 18 Sep 2026 12:00:00 +0000\r\n
From: "Aiko" <aiko@example.net>\r\n
Newsgroups: fn.example,fn.utf8\r\n
Subject: =?UTF-8?Q?caf=C3=A9_=E2=80=94_r=C3=A9sum=C3=A9?=\r\n
Message-ID: <aiko-42@example.net>\r\n
MIME-Version: 1.0\r\n
Content-Type: multipart/mixed; boundary="fn-b42"\r\n
X-Client-Note: draft-7; preserve-me\r\n
X-Client-Route: =?UTF-8?Q?caf=C3=A9?=\r\n
\r\n
[the exact MIME body octets from the proto-article]\r\n
```

The local group numbers `17` and `9` are memberships, not part of the portable
article identity. Another site may number the same article differently. RFC 5536
§3.2.14 describes Xref as information from the last server that filed an article
and permits its locations to differ from Newsgroups. RFC 5537 §§3.6–3.7 permits
relaying/serving agents to update Path and remove or add their own Xref, while
requiring them not to alter other fields or the body. fn's stronger source-object
rule keeps all four views distinguishable even when a legacy implementation
cannot expose the native envelope.

## What changes, and what does not

| Item | Proto-article to injected article | Relay/serving projection | Native binding |
| --- | --- | --- | --- |
| Message-ID | Preserved exactly for this example | Preserved exactly | Exact octets are a key, including case |
| Date | Supplied by the posting agent | Existing value preserved | Source field remains unchanged |
| Injection-Date | Added by injector | Usually retained | Provenance/projection field |
| Injection-Info | Added by injector | Usually retained | Gateway evidence, not author identity |
| Path | Added/updated as agents process article | Prepended and possibly folded | Mutable trace, excluded from source |
| Xref | Usually absent | Added or replaced locally | Local membership projection |
| Unknown headers | Preserved as source octets | Relays must not rewrite them | Included in source bytes |
| MIME/body octets | Preserved | Relays must not rewrite them | Included in source bytes |
| Local group numbers | Not present | Allocated atomically per site | Not portable identity |

The table separates three identities that are easy to conflate: the exact source
octet object, the exact Message-ID, and a site's local membership. A whole-file
digest of two projections is expected to differ when Path or Xref changes. That
difference alone is not an authored-content conflict. Conversely, two source
objects with the same Message-ID but different body or authored headers are
conflicting evidence and must not overwrite one another. This follows `OBJ-001`
through `OBJ-005`, rather than an assumption that Message-ID equality proves
content equality.

## Retry, variant, and gateway cases

### Exact retry

If the client resends the same proto-article bytes with
`Message-ID: <aiko-42@example.net>`, the source reference, Message-ID binding,
and local membership intent are the same. fn may answer according to its eventual
POST profile, but the durable effect is a duplicate no-op. RFC 5537 §3.4.2 says
that multiple injection should offer the same proto-article and retain Message-ID,
Date, and Injection-Date where already present. `NNT-005` separately requires
that a lost success response cannot allocate a second local article.

If the client omitted Message-ID and the injector generated a fresh one on every
retry, the retries are not the same identity. `NNT-005` therefore does not infer
deduplication from a new generated ID; a client or gateway must retain the retry
identity.

### Same ID, different source

Suppose a second source keeps the same Message-ID but changes the body bytes from
the UTF-8 sequence above to `48 65 6c 6c 6f 0d 0a`, or changes an authored
`Subject` field. fn preserves the original binding and stores the second arrival
as a conflict/variant record with its arrival provenance, subject to bounded
evidence policy. It does not overwrite the first source and does not treat
arrival time as authorship truth. The second arrival can be rejected at the
protocol boundary while retaining enough evidence for diagnosis; that policy is
still open.

If only Path, Xref, or another permitted trace field differs, the source bytes
may still be the same article. For a native object, the retained source and explicit projection supply that
separation. A legacy article arriving from a relay does not reveal its exact
pre-injection bytes: stripping trace fields cannot reconstruct them or establish
shared authorship. Preserve that received variant; any equivalence rule for
legacy variants needs its own explicit, weaker policy. RFC 5537 §3.6 explicitly prohibits a
relaying agent from altering anything except Path and Xref and prohibits body
modification.

### Gateway-attested legacy post

An unsigned legacy proto-article may have:

```text
From: "Imported User" <legacy@example.invalid>\r\n
Message-ID: <legacy-884@example.invalid>\r\n
X-Legacy-Thread: 884\r\n
```

The fn envelope can record `provenance.kind = gateway-attestation`, the gateway
principal, the received source bytes, and the gateway's statement that it accepted
the submission. It must leave `author-signature` absent. The gateway has attested
to its own processing; it has not proved that the display name or mailbox in
`From` is the human author. RFC 5537 §3.10.2 requires an incoming gateway not to
gate the same message twice and recommends using an equivalent source message
identifier when forming the Netnews Message-ID. Its identity mapping and any
collision handling remain fn policy choices.

## Two signing-preimage candidates

Both candidates bind the exact source bytes and use length-delimited or
canonical-field encodings. Neither selects a signature algorithm, key type, or
permanent ABI. The `profile` field is a candidate algorithm/profile identifier;
the actual algorithm-tagged signature container is a D09 deliverable.

### Candidate A: explicit length-prefixed tuple

```text
preimage-A =
  ASCII("fn/native-source-signing") || 00 ||
  u16be(schema-version) ||
  u16be(profile-id-length) || profile-id-octets ||
  u16be(message-id-length) || message-id-octets ||
  u32be(source-length) || source-octets ||
  u16be(author-reference-length) || author-reference-octets ||
  u16be(policy-context-length) || policy-context-octets
```

The domain tag and every length make concatenation unambiguous. `source-octets`
is the complete proto-article byte string, so unknown headers, MIME boundaries,
folding, and body bytes are covered. The profile and policy context can prevent
the same signature from being interpreted under two schemas. This form is easy
to implement in a small bounded codec and easy to compare in golden vectors.
Its cost is that every field addition requires a versioned grammar and careful
rules for optional fields.

### Candidate B: canonical map whose source value is a byte string

```text
preimage-B = deterministic-CBOR({
  "domain":       "fn/native-source-signing",
  "version":      1,
  "profile":      <algorithm/profile identifier>,
  "message-id":   h'3c61696b6f2d3432406578616d706c652e6e65743e',
  "source":       h'<exact proto-article octets>',
  "author-ref":   h'<stable author-reference octets>',
  "policy":       h'<policy-context octets>'
})
```

This relies on a restricted profile: definite lengths, deterministic map-key
ordering, rejected duplicate keys, bounded fields, and byte strings for all
octet-bearing values. Those are consistent with the proposal in
`specs/encoding.md`, but the profile is not selected. The map is easier to evolve
as an envelope and easier for independent implementations to inspect. Its cost is
that canonicalization and unknown-key rules become part of the signature
security boundary; a permissive decoder must not silently sign one interpretation
and verify another.

### Working recommendation

Carry Candidate B forward as the preferred design direction because D08 already
proposes restricted deterministic CBOR and D09 calls for algorithm-tagged,
versioned containers. Keep Candidate A as a minimal reference grammar and test
oracle. The user selected the shared source boundary of both candidates: the
signed value binds the exact authored source byte string, not a reconstructed
header map or normalized display text. Mutable Path/Xref, local article numbers
and gateway injection records are outside this source signature. Separate
provenance signatures, if needed, have their own specified subjects. To make this consistent with signing an exact proto-article, a
native submission profile must forbid mutable trace fields in its source (or
define them as immutable authored claims with separate projected trace fields).
It cannot silently strip fields after the author signs them.

This recommendation does not choose Ed25519, a post-quantum scheme, a hybrid, a
COSE profile, a key-rotation protocol, or an ABI. The signature and digest values
shown in this document are deliberately nonfunctional placeholders. RFC 5536 §5
states that the Netnews article format itself supplies no sender authentication or
non-repudiation; any such service is layered above or below it. fn must therefore
state the cryptographic assumptions and implementation evidence separately from
the RFC wire behavior.

## Decisions this document leaves for later

D01 resolves the source/projection architecture. The remaining profile questions
are more specific:

1. What exact native submission grammar and envelope fields carry the authored
   octets, and how does it reject mutable trace fields without rewriting a
   source after signing?
2. Which separate gateway/injection statements need signatures, and what are
   their exact subjects and authority contexts?
3. Which preserved unknown headers may the bounded parsed view expose to search
   or policy, without treating their contents as authority?
4. When the same Message-ID has conflicting source bytes, which evidence is
   retained, which variant is served locally, and how are quotas applied?
5. What stable author reference and policy context are signed, and how do key
   succession and revocation statements relate to an old source signature?
6. Does an incoming gateway preserve a source Message-ID directly, or use a
   deterministic namespaced transformation when its source identifier is absent
   or collides?

These profile/D08/D09 questions need byte vectors, collision/variant traces and
an implementation/profile audit before a format or cryptographic suite is called
selected. The two preimage encodings above remain candidates; D01 did not select
either one.
