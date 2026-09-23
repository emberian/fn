# NNTP projection and article acceptance

Status: the selected reader profile is implemented and advertised, and POST is
advertised exactly on the connections that may use it. `books/nntp.lisp` always
advertises `VERSION 2`, `READER`, `OVER MSGID`, `HDR`, `NEWNEWS` and
`LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT`. Every clause RFC 3977
appendix B assigns to those labels is marked proved or tested in
[the clause matrix](nntp-audit.md#the-reader-clause-matrix); none is open.
`POST` (RFC 3977 §5.2.2) is advertised when, and only when, this connection's
pinned configuration allows posting (`fn-inj-config-allow`, threaded to the
dispatcher as the third field of `fn-nntp-env`) — the same bit
`fn-nntp-post-step` reads before it answers a `POST` command with 340 rather
than 440, so the label is a promise this server keeps. The greeting carries the
same bit as §5.1.1's code (`200` when this connection may post, `201` when it
may not, `fn-served-greeting config session`) and so does `MODE READER`
(§5.3.2). On a connection under a policy that requires a login the allowance is
the conjunction of that bit and `fn-auth-postingp`, so an unauthenticated
connection greets 201 and gains the label with its 281; before 2026-09-21 the
greeting read the injection configuration alone and promised 200 where POST
answered 480. `fn-served-open-greets-200-exactly-when-the-connection-may-post`
and `fn-served-open-greeting-agrees-with-the-post-label` (PRF-039) are the
statement of it. The read-only reader profile pins a configuration that
disallows posting, so it greets with 201 and advertises no POST. IHAVE and
MODE-READER remain unadvertised. D05's checklist
is the matrix. See [implementation status](../docs/implementation.md).

## Planned surface

| Bundle/function | Planned commands |
| --- | --- |
| Mandatory | CAPABILITIES, HEAD, HELP, QUIT, STAT |
| READER | ARTICLE, BODY, DATE, GROUP, LAST, LISTGROUP, NEWGROUPS, NEXT |
| Required reader listings | LIST / LIST ACTIVE, LIST NEWSGROUPS |
| Posting | POST |
| Overview | OVER, LIST OVERVIEW.FMT |
| Compatibility behavior | MODE READER, according to the actual advertised mode |
| Clock and creation facts | DATE and NEWGROUPS consume an explicit `fn-clock-observationp` and a persisted `fn-nntp-group-factp` list; neither is invented by the reader |
| Header access | HDR, LIST HEADERS |
| Polling | NEWNEWS (§7.4), under the work budget below |
| Legacy spellings (RFC 2980) | XOVER (§2.8), XHDR (§2.6), LIST ACTIVE.TIMES (§2.1.3) |
| Later optional capabilities | IHAVE, XPAT, streaming, authentication/compression extensions as selected |

NNT-001: advertise only complete supported bundles and variants. Build a checklist
of every applicable RFC branch, argument form, response, and state effect.
Ranges, wildmat, dates, optional arguments, error precedence, and pipelining are
part of that work. A command name appearing in this table is not conformance.
Use RFC 3977 §§3.4 and 3.4.2, command sections, and Appendix B as the baseline.
The [implementation checklist](nntp-audit.md) tracks branches and remaining work;
it is not a completed conformance audit.

## Reserved header fields

fn reserves header field names for its own use. Each is an ordinary RFC 5536
§3.1 header field carried by a relaying agent unchanged — RFC 5537 §3.6 permits
it to alter Path and Xref and nothing else — and none of them is an instruction
to the receiving node: fn executes no control message (RFC 5537 §5).

| Field | Reserved for | Defined in |
| --- | --- | --- |
| `FN-Statement` | The detached statement about this article: creator, incarnation, sequence, kind, payload reference and signature, base64-encoded. `ARTICLE` and `HEAD` return it byte-identical so a client verifies with its own keyring; the node's own three-valued verdict is the separate `:fn-verified` HDR metadata item, never this field. | [substrate transport](substrate-transport.md#12-the-field) |

## Clock and group-creation inputs

The reader answers DATE and NEWGROUPS only from inputs an owner or
host supplies. `fn-nntp-step` takes a fourth argument, the reader environment
`(:fn-nntp-env observation facts)`. `observation` is `books/clock.lisp`'s
`fn-clock-observationp`; with `has-wall` false, DATE answers the stated 503
refusal and a two-digit NEWGROUPS year is refused rather than resolved against a
guess. `facts` is a list of `(:fn-nntp-group-fact name created-at-dtn-ms
observation)` records: the group's name, the DTN time (RFC 9171 §4.2.6) at
which it was created, and the clock observation under which that time was
established, so a creation time carries its own provenance and can never be
back-filled from the reader's current clock. The mutable-owner lane persists
these records; the reader consumes the shape and stores none of its own. The
POSIX-to-DTN epoch shift is `fn-nntp-unix-dtn-ms` in ACL2, not in the adapter.

fn's reader has no timezone database. Its local time zone **is** Coordinated
Universal Time, which RFC 3977 §7.3.2 notes the protocol cannot convey; the
optional GMT token therefore changes nothing and is accepted only where the
grammar allows it.

## Legacy spellings (RFC 2980)

Real readers -- slrn, tin, older Thunderbird -- send `XOVER` and `XHDR`
before they will send `OVER` and `HDR`, and some never send the modern
spelling at all. fn implements them, and implements them as spellings rather
than as a second implementation:

- `XOVER` calls the same renderer `OVER` calls. `fn-nntp-xover-range` and
  `fn-nntp-over-range` are proved equal wherever RFC 2980 §2.8.1 and RFC 3977
  §8.3.1 assign the same response (`fn-nntp-xover-agrees-with-over-on-a-
  nonempty-range`, `books/nntp-legacy.lisp`); they differ only where the two
  documents themselves differ, which is 420 against 423 for an empty range.
  RFC 2980 defines no message-id form, so `XOVER <message-id>` is a syntax
  error rather than a code §2.8.1 does not list.
- `XHDR` and `HDR` are one function, `fn-nntp-hdr-command`, with a flag that
  selects the three things the two documents disagree about: the initial line
  (221 or 225), the empty-range code (420 or 423), and whether the message-id
  form labels its line with `0` or with the message-id.
- Neither carries a capability label. RFC 2980 predates RFC 3977 §3.3 and
  names none, so a client discovers them by sending them. `HDR` does carry
  one, and advertising it is a promise about `LIST HEADERS` too (§3.3.2),
  which is why `LIST HEADERS` stopped answering 503 in the same change.

`LIST ACTIVE.TIMES` reads the same persisted creation facts `NEWGROUPS`
reads, so §7.6.4's "the results SHOULD be consistent" is true by construction.
Its third field is the plain text `unattributed`: a configuration record
records who may reconfigure the node, not a mailbox to attribute a group to,
and fn does not fabricate one. `LIST NEWSGROUPS` renders the fixed marker
`(no description)` for the same reason: the group table
(`books/config-records.lisp`) carries names, policy ids and created/retired
stamps and no description, so nothing group-specific is invented and the
marker is a statement about the server, not about the group. §7.6.6 permits
the description to be omitted or passed on as held, and it is **not** the
empty string: Python `nntplib` strips the line and then requires a name,
white space and text, so a bare `name TAB` drops the group from
`descriptions()` entirely (measured against `tests/interop_nntplib.py`,
2026-09-20). OPEN: a per-group description field in the durable
configuration record, which R5 would add; until then this row is a stated
local limitation and not a claim that fn has descriptions.

## Polling: NEWNEWS

RFC 3977 §7.4 answers `NEWNEWS wildmat date time [GMT]` with a 230 block of
Message-IDs in matching groups accepted since the given instant. The served
path reaches `fn-nntp-newnews-response` through `fn-served-dispatch` →
`fn-auth-step` → `fn-peer-step` → `fn-nntp-post-step` → `fn-nntp-step` →
`fn-nntp-archive-command`; `fn-nntp-step-dispatches-newnews-to-the-newnews-response`
is the subject equation.

**Which instant.** A schema-1 article's durable stamp is the owner's wall-clock
second at prepare, in seconds since the DTN epoch; payload `Injection-Date`
and `Date` do not enter the test. A schema-0 article carries `:legacy` and is
dated conservatively by the nearest article accepted after it with a natural
stamp, even when that newer article belongs to a different group. With no
such article, the horizon is the reader's pinned wall second; with no wall,
the legacy article is reported at every threshold. These may over-report a
legacy article; assuming the wall clock did not regress across migration,
they do not omit one accepted after the requested instant. Availability at a
number in a matched group still gates every reported identifier.

**Cost and proof scope.** One command walks the committed article list once,
testing memberships in the matched groups and comparing one natural stamp
per article. No article payload octet is read
(`fn-nntp-newnews-scan-reads-no-payload`). The pessimistic bound is
`O(A·G')` for `A` committed articles and `G'` groups matched by the wildmat,
with at most `C` lines for `C` candidates, where `C` is bounded by Store
`max_transactions`. The former 256 article-parse budget and its 503 refusal
are gone. `fn-nntp-newnews-scan-is-the-acceptance-filter` equates the one-pass
scan with an independent quadratic specification, establishing soundness and
completeness. `fn-nntp-newnews-lines-are-clean` and
`fn-nntp-newnews-scan-lines-at-most-candidates` establish block hygiene and
the output bound. The per-group index of `books/nntp-index.lisp` is not on the
served path; replacing the whole-list walk remains open.

Message-ID forms of `ARTICLE`, `HEAD`, `BODY`, and `STAT` use the connection's
pinned trie rather than scanning its accepted article list. The owner refreshes
the current view with `fn-midx-refresh` when Store reaches an idle phase, then
pins the archive and corresponding trie together at open or after a durable
posting outcome. Existing connections keep their earlier pair. The proof-side
`fn-own-relation` includes exact trie-to-archive correspondence for the current
view and every retained connection; it is established by `fn-own-start-relation`
and carried by `fn-own-run-preserves-relation`. Under that premise,
`fn-nntp-msgid-retrieval-indexed-refines-scan` equates the indexed answer with
the original list lookup. The host-called `fn-own-read` is tied to the pinned
served step by `fn-own-read-is-served-step-on-pinned-prefix`. These are in-memory
indexes, reconstructed from committed acceptance on recovery; they do not
change acceptance authority or add disk index files. Per-group number/range
reads and `NEWNEWS` still walk the pinned archive.

230 is a complete answer. 501 is the syntax refusal for malformed arguments,
date/time or wildmat. 503 remains only for a two-digit year when the pinned
reader observation has no wall clock, per §7.3.2. NEWNEWS changes no session
state (`fn-nntp-newnews-response-preserves-session`). The DATE-to-NEWNEWS
no-miss property across reader pin and in-flight prepare depends on A-CLOCK
and is the separate T6 proof target.

NNT-008: NEWNEWS reports exactly the committed Message-IDs available in
matching groups whose durable acceptance stamp, or conservative legacy
horizon, is at or after the requested instant; it reads no payload octets and
never returns a partial block for a size limit.

## Overview projection

Every OVER field comes from the proved `fields` view of
`books/article.lisp`, read through `books/article-fields.lisp`'s lookup. The
reader does not parse an article a second time and holds no overview database:
a line is projected on demand from the exact retained octets. RFC 3977 §8.3.2's
transformation - remove CRLF pairs, then replace each remaining TAB, NUL, LF and
CR with one space - is applied once, and `books/nntp-overview.lisp` proves the
result clean for any input whatsoever. `:bytes` is the retained octet count and
`:lines` the retained body line count; Xref is omitted rather than approximated,
so exactly eight fields are emitted and LIST OVERVIEW.FMT lists exactly the
seven fixed lines of §8.4.2.

## Sessions and framing

NNT-002: maintain a per-connection selected group and current article number.
Failed GROUP leaves them unchanged; successful GROUP selects its first available
article or an invalid cursor for an empty group. Retrieval by Message-ID does
not move either; successful numeric retrieval updates the current article number.
Use the specified 412/420/423/430 cases and error precedence. Later expiry can
invalidate a once-valid cursor; do not bake eternal existence into the invariant.

NNT-007: the session also carries the archive-configuration verdict computed
when the connection opens. No command recomputes a whole-archive recognizer:
`fn-nntp-open-session` decides once, `fn-nntp-step` reads the carried value, and
`fn-nntp-step-preserves-carried-projection` states that every step keeps it. A
committed article the projection cannot render answers for itself and does not
deny the service; see the served-path section of
[the implementation checklist](nntp-audit.md).

NNT-003: interpret CRLF framing and dot-stuffed multi-line data independently of
socket chunk boundaries. A line containing only the terminator ends article
input; command-like body text stays body text. Bound buffers and drain rejected
input to a safe protocol boundary or close the connection. Do not reinterpret
the remainder of an oversized article as fresh commands. Response framing must
preserve payload octets subject to the specified wire transformation.

## Posting and projection

NNT-004: distinguish proto-article submission from a stored/relayed article.
Validate required fields; supply permitted missing injection fields under a
specified policy. Preserve MIME content and unknown allowable fields. `From` is
not authenticated identity. References permit missing ancestors. Article dates,
field folding, generated Message-IDs, and Path/Xref behavior require the RFC 5536/
5537 dependency audit and the concrete native/legacy profile. D01 now fixes
the native boundary: exact authored source bytes are signed; mutable Path/Xref
and gateway injection records belong to separate projections. Injection must
not rewrite those signed bytes. Legacy input keeps its explicit provenance.

NNT-005: positive POST acceptance follows fn's durable transaction contract and
the selected local retention policy: keep until explicit authorized release,
without automatic expiry (D03).
Preserve a supplied valid Message-ID for retry identity according to the chosen
injection policy. If success is lost, a retry cannot create another allocation.
The duplicate POST response is a policy/profile decision; idempotent storage
effects do not imply identical wire replies. A generated new ID on every retry
cannot by itself provide deduplication for clients that omitted one.

NNT-006: project committed local membership and retained article state. Allocation
watermarks survive removal and restart. GROUP counts/low/high values and empty-
group representations follow RFC 3977; indexes and pagination cannot silently
omit entries. Cross-posting affects all intended configured local groups in one
transaction. D05 defines treatment of unknown groups for local posts and later
incoming transfers; preserve the original Newsgroups header/provenance.

## POST (RFC 3977 §6.3.1)

POST is one composed transition with a durable step in the middle, and the
three parts have three different owners of the *reply*, all of them ACL2.

1. `fn-nntp-step` answers a `POST` command line with `340 send article to be
   posted` and one `:begin-article` effect. That effect is the instruction to
   put the wire into article mode; the host applies it by calling
   `fn-wire-begin-article` and does nothing else with it. The dispatcher has
   no configuration argument and no clock, so it decides nothing further.
2. `fn-nntp-post-step` (`books/nntp-post.lisp`) is the function the serving
   host calls. It wraps `fn-nntp-step`: for every command that is not POST it
   returns that result unchanged. When it sees the offer it consults the
   configuration: posting disallowed becomes `440 posting not permitted` and
   the session does not enter article mode. When the terminated body arrives
   as an `(:article body)` wire event it calls `fn-inj-decide`. A refusal is
   `441` carrying that reason's own line. An acceptance emits **no reply**: it
   emits a *submission*, which is the injected article's exact octets, its
   Message-ID and its groups.
3. The owner (`books/owner.lisp`, served by `tools/run_owner.py`) records
   the submission against the connection and its pinned version
   (`fn-own-read`), moves it into the durable path one at a time
   (`fn-own-take-submission`: only when nothing is in flight, no transaction
   is pending and the store is `:ready`), the host carries it through the
   same durable acceptance path the command-line `post` uses —
   `fn-node-prepare`, publication, then `fn-sn-finish` — and feeds the word
   it observed to `fn-own-outcome`, which renders the reply through
   `fn-served-post-outcome` for that connection alone. `:durable` is `240
   article received OK`, and the owner renders it only when a completion
   was consumed into its ledger after the take
   (`fn-own-durable-reply-names-a-durable-record`): a host that claims
   `:durable` without one gets the uncertain line. `:refused` and
   `:uncertain` are two distinct `441` lines, and stay distinct out to the
   wire: an uncertain outcome never becomes a 240 and never becomes the
   refusal line, because a client must not repost on it. A duplicate or
   conflicting Message-ID, an uncarried group and a reached bound are
   refusals; an indeterminate commit and a host fault are uncertain.

Read-back. A 240 is a promise the poster can act on, so the 240 moves the
poster's own pin: `fn-own-outcome`'s `:durable` branch is one `fn-own-advance`
on that connection and on no other, so the poster's next `GROUP` or `ARTICLE`
reads the prefix that contains its own article
(`fn-own-durable-outcome-repins-the-poster`; the served step is still one
`fn-served-step` over the connection's pinned archive, K1). Every other
connection keeps the version it pinned at open, including a reader opened
before the post, and moves only when the control channel advances it
(`fn-own-outcome-touches-only-its-connection`,
`fn-own-pinned-prefix-survives-any-trace`). A `:refused` or `:uncertain`
outcome moves no pin. K1 covers either choice — it constrains what a
connection reads at its pin, not which pin it holds — so this is a recorded
policy choice, not a consequence of the keystones.
The read-only reader (`tools/run_reader.py`) answers POST with 440.

A submission is not an acknowledgement. No 240 is reachable from
`fn-nntp-post-step`; it exists only in `fn-nntp-post-outcome` under
`:durable`.

### What injection is

`books/injection.lisp` implements RFC 5537 §3.5 as a function of exactly three
things: the source octets the posting agent supplied, one
`fn-clock-observationp`, and a configuration record naming the injecting
agent's identity, the groups it accepts, and its size bound. The host computes
none of it — not the Message-ID, not the Injection-Date, not the Path, not the
injected octets.

**Which clock reading.** The observation `fn-inj-decide` is given is the one
the host took *for this submission*, not the one the connection pinned when it
was accepted. RFC 5537 §3.4 makes `Injection-Date` the time of injection, and
fn derives a generated `Message-ID` from the same reading, so one reading per
connection would give every submission on a connection the identity of the
first: the second POST on a connection would be refused as a duplicate
identity whatever its body. `fn-nntp-post-step` therefore takes two readings —
`observation`, pinned at accept, which is the reader environment (DATE,
NEWGROUPS, `fn-nntp-env`), and `injection`, supplied with the article event,
which is the only one `fn-inj-decide` sees. `books/owner.lisp` supplies the
owner's current observation on every `fn-own-read`; `tools/run_owner.py` takes
that reading before each socket chunk. Two submissions on one connection whose
injection clocks differ in either number receive distinct identities
(`fn-post-distinct-injection-clocks-give-distinct-identities`, over
`fn-inj-generated-identity-separates-different-clock-readings`).

**When the server has no reading.** The owner holds no clock exactly when its
host reported a reading contradicting the one it held, or has reported none
since it started ([D10-a](../planning/decisions.md); `specs/owner.md`). The
injection reading is then not an observation, and the article is refused with
`441 posting failed; this server has no usable clock reading` and no
submission (`fn-post-without-a-clock-refuses-with-the-clock-line`). That is a
different constant from every article verdict the step can give, which is the
point: a clock fault must not reach a posting agent as a judgement about its
article. Before D10-a the owner kept the contradicted reading, minted the
previous identity again, and the duplicate reached the poster as `441 posting
failed; the article was refused`. Under the
*same* reading the retry rule still holds: the same proto-article injected
twice is the same article, and — because the generator's only inputs are the
clock and the configured agent — two different bodies under one reading do
share a generated Message-ID. That is why the reading must move, and it is
witnessed both ways in `tests/acl2/nntp-post-tests.lisp`.

The injecting agent generates `Path`, `Injection-Date`, `Injection-Info`, and
`Message-ID` and `Date` when the proto-article omits them (RFC 5537 §3.4.1
permits exactly those three omissions). `From`, `Subject` and `Newsgroups`
must be supplied. The generated lines are *prepended*: the supplied source is
a verbatim suffix of the injected article, which is proved
(`fn-inj-injected-article-retains-the-source-octets`), and is what makes the
"MUST NOT alter the body" clause of §3.5 item 6 hold structurally rather than
by inspection.

Two choices here are local policy, not RFC requirements, and are recorded as
such:

- A proto-article that already carries `Path` or `Injection-Date` is refused
  rather than rewritten. §3.2.1 would have an injecting agent prepend its
  identity to an existing `Path`; rewriting a supplied field would break the
  verbatim-suffix property, so fn refuses. fn is the origin injecting agent
  for a POST.
- The wall clock must be present and inside the 400-year Gregorian cycle from
  2000-01-01. Outside it there is no Injection-Date this model renders, and
  the outcome is a refusal, not a guess.

### Retry identity (NNT-005, D01)

The design choice, stated because it constrains clients: a **supplied**
Message-ID is retained octet for octet and survives any clock reading, so a
posting agent that supplies one has an exact retry identity. A **generated**
Message-ID is derived from the clock, so a retry that omits Message-ID is a
new article and fn will not deduplicate it. Both halves are theorems in
`books/injection-invariants.lisp`; the second is stated so that no client
assumes otherwise.

### Not yet true of POST

There is no
freshness window on a supplied `Date` (RFC 5537 §3.5 item 3), no
trusted-source check (item 1) and no moderated-group handling (item 7).

An earlier version of this section said RFC 3977 §3.5 forbids pipelining
after POST's article. It does not, and the claim is withdrawn: §3.5 requires
the server to allow pipelining and forbids it from throwing away text
received after a command, and only a command whose own description says
"MUST NOT be pipelined" ends a pipeline. POST's description says no such
thing. fn now serves the pipelined case and proves it
(`fn-served-pipelined-read-is-the-sequential-reply`,
`fn-wire-article-event-resumes-command-mode`, `books/served.lisp`). What
remains true is the ordering: a command pipelined behind the article body is
answered before the 240 or 441, because the durable outcome is a later input
(`fn-served-post-outcome`). That is §3.5's "process commands in the order
they are sent" together with fn's refusal to acknowledge a posting before it
has observed durability, not a pipelining defect.

## Transport security, and what is trusted

TLS is a **host facility and is outside the model**. RFC 4642 STARTTLS is
served by `books/nntp-auth.lisp`, which emits a `(:starttls)` effect. The
native owner loads a configured OpenSSL 3 server context and performs the
handshake in `host/native/tls.lisp`; the development adapter uses Python's
`ssl` module. Both adapters report `(:tls-established)` to ACL2 only after a
successful handshake. The book sees plaintext octets on both sides of that
boundary, and no theorem in this tree says anything about confidentiality,
integrity, certificate validation, cipher selection or the handshake itself.
The OpenSSL library, dynamic loader, C ABI and socket BIO are explicit native
trust. The implementation follows OpenSSL's documented retry contracts for
[`SSL_accept`](https://docs.openssl.org/3.0/man3/SSL_accept/),
[`SSL_get_error`](https://docs.openssl.org/3.0/man3/SSL_get_error/),
[`SSL_read`](https://docs.openssl.org/3.0/man3/SSL_read/) and
[`SSL_write`](https://docs.openssl.org/3.0/man3/SSL_write/); this is an
implementation dependency, not a TLS correctness theorem.

What is proved is the protocol state machine around the upgrade: the
capability label appears only where RFC 4642 §2.1 allows, 382 is emitted only
from the branch that also records that a handshake is owed, a second STARTTLS
is 502, and the cached username and authenticated subject are discarded
across the handshake. The clause-by-clause split is the RFC 4642 matrix in
[the audit](nntp-audit.md).

AUTHINFO USER/PASS is likewise a **cleartext mechanism on the wire**, and no
change below makes it otherwise: the secret still crosses the connection in
the open, which is why RFC 4643 §2.3.2 asks for a protected channel and why an
operator who needs the secret protected sets `[listener] auth protected-only`,
which makes AUTHINFO answer 483 until a TLS layer is active. What changed on
2026-09-20 is what the *configuration file* holds.

### The stored AUTHINFO credential

`books/auth-secret.lisp` defines the scheme, exactly:

| element | value |
| --- | --- |
| salt | exactly 16 octets, one per credential, chosen at enrolment |
| preimage | `salt \|\| secret` (the salt's length is fixed, so the boundary is unambiguous) |
| tag | `"fn-authinfo-v1"`, the crypto seam's domain separation |
| stored | `(:fn-authsec-v1 salt (fn-digest-tagged tag preimage))` |
| check | the supplied octets pass iff re-deriving the digest under the stored salt yields the stored digest |

The digest is the seam's, and the seam is now executable:
`books/crypto-attach.lisp` attaches the guard-verified SHA-256 of
`books/sha256.lisp` to `fn-digest`. That is what `OB-AUTH-DIGEST` was waiting
for; the audit's entry is updated rather than deleted, because the reason the
credential was cleartext is part of the record.

Proved (`books/auth-secret.lisp`): the enrolled secret checks; the verifier
is a structured value rather than an octet list; its digest has a fixed length;
and the preimage encoding recovers `(salt, secret)`. These shape/encoding facts
do not establish secrecy of the password or its length, resistance to offline
guessing, or universal rejection of a different secret. The seam's constant-
digest witness accepts every secret. Concrete rejection cases in
`tests/acl2/auth-secret-tests.lisp` remain witnesses for those inputs.

The concrete v1 scheme is a fast salted, tagged SHA-256 verifier, with no tunable
work factor or memory-hard password derivation. Preserving this format in native
administration establishes compatibility, not hardened password storage. The
next authentication profile needs an explicit version/migration contract,
password-guessing threat model, bounded verification resource policy and a
reviewed primitive/backend boundary. Argon2id is a candidate for that design:
[RFC 9106](https://www.rfc-editor.org/rfc/rfc9106.html) specifies memory-hard
password hashing and parameter selection. No new suite or parameters are selected
here. This issue is separate from TLS transport protection, native author
signatures, and the deferred private-group cryptosystem.

**Done 2026-09-20**: `books/nntp-auth.lisp` holds a `fn-authsec-verifierp`
in `fn-auth-cred-secret`, `fn-auth-credp` recognizes it, and
`fn-auth-checkp` is `fn-authsec-checkp`. `fn-authsec-verifier-is-not-octets` distinguishes the verifier tuple from
an octet-list token; it is not a confidentiality theorem. `fn principal set-password` derives the verifier
through `tools/auth_secret.py` — one ACL2 session over `books/auth-secret`,
no `hashlib`, and `bin/fn` no longer imports that module. An existing
credential file in the old format is refused by name
(`cleartext-credential`) and the operator re-sets the password; fn does not
read a stored password to re-derive it. The live evidence is
`planning/evidence/auth-w10-2026-09-20.md`.

**Native startup slice 2026-09-21**: `books/native-auth-profile.lisp` parses
the bounded credential file and constructs the same `fn-auth-config` the
served owner already pins at connection open. `host/native/auth.lisp` only
reads the ACL2-selected path and transports octets; it neither parses a
credential nor hashes or compares a secret. The native operator admits
`auth.required` on its ACL2-restricted loopback listeners. The W23 native
transport consumes the ACL2-projected paired TLS paths, validates the
certificate/key pair before listening, and admits `auth.protected_only` only
when such a pair is configured. The authentication profile receives TLS
availability from the successfully loaded context; configured path text alone
does not establish it. Credentials and the TLS context are startup-pinned;
live reload/generation switching remains open.

**Native administration component 2026-09-21**:
`books/native-auth-admin.lisp` owns the bounded `principal list` and
`principal set-password` tail grammar, login and principal validation, prompt
confirmation verdict, existing `fn-authsec-enrol` call, row replacement,
canonical sorted serialization and the public-only list report.  The password
is not an argv, plan, result or report field.  Raw Lisp observes the two
bounded prompt entries and one exact 16-octet OS-CSPRNG salt.  It holds a
fixed adjacent exclusive lock, removes and directory-barriers any surviving
fixed stage, barriers the observed final file and its directory before decode,
and then drives the ACL2 mutable-replacement phases.  Failure after replace is
issued, including a lost rename result or final-directory barrier, is
`uncertain`; only the successful final directory barrier is `accepted`.
The service still pins credentials at startup, so a successful password change
reports that restart is required.  The public native-operator routing is a
separate composition edge; this component does not add a second top-level
grammar or a Python fallback.

This administration path preserves the existing explicit
`:fn-authsec-v1` compatibility format.  Salted, domain-tagged SHA-256 is not a
tunable-cost or memory-hard password KDF, and this component makes no claim
that low-entropy passwords resist offline guessing.  A hardening successor
must use a new credential version and an explicit migration/refusal policy;
it must not reinterpret the existing salt/digest fields in place.

**Closed 2026-09-20**: RFC 4642 §2.2 says STARTTLS MUST NOT be pipelined,
and the handshake begins with the first octet after the 382's CRLF, so any
octets that arrived in the same read after the `STARTTLS` command line are
handshake bytes and not NNTP. `fn-served-feed` now has a second stopping
condition, `fn-served-tls-handshakingp`, carried in the connection exactly
as the closed wire is: the 382 branch leaves the session HANDSHAKING rather
than in TLS, and a handshaking connection frames nothing
(`fn-served-feed-of-handshaking-connection`,
`fn-served-step-of-handshaking-connection-is-a-no-op`,
`fn-auth-handshaking-session-serves-nothing`). Because the stop is a
property of the CONNECTION and not of the effects just emitted,
`fn-served-feed-of-append` and partition independence hold unchanged — a
test on the effects would have broken them, which is why the condition is
where it is. The host performs the upgrade on the `(:starttls)` effect and
re-enters the plaintext stream with the `(:tls-established)` wire event,
the only transition that sets `tlsp`
(`fn-auth-tls-established-sets-the-layer`). ACL2 owns the decision; the
host owns only the socket.

The native transport additionally tolerates a peer that places its
ClientHello behind the STARTTLS line in one kernel observation. This is a
robustness property and does not relax RFC 4642's client prohibition. The
sole connection worker observes with `MSG_PEEK`; `fn-ocfg-read-tls-prefix`
returns the one ACL2 transition, its effects and the exact consumed count.
`fn-ocfg-read-tls-prefix-is-full-read`, under the configured-owner state
invariant, proves that the actual host-call result equals the checked full
observation. The host-called path uses `fn-served-step-counted-fast`: its entry
predicate examines the fixed eight-cell wire record and scalar counters, never
the retained current line or article body. `fn-served-step-counted-fast-is-reference`
equates it to the total checked transition under the full wire invariant, and
`fn-served-step-counted-fast-preserves-connp` carries that invariant to the
next read. `fn-served-tls-prefix-suffix-accounting` proves that prefix and
suffix reconstruct the observation. Raw Lisp then consumes and
byte-checks only that prefix before OpenSSL reads the suffix. Sole-reader
ownership and stable `MSG_PEEK`/consume behavior are explicit scheduling and
platform premises; a short, changed or failed consume closes the connection
without replaying the logical transition.

### The posting allowance

Posting is the AUTHENTICATED PRINCIPAL's, not the connection's.

**Fixed 2026-09-21, and it is why none of the paragraph below reached a
running server.** `fn-served-open-peer` pinned the literal
`(fn-auth-open-config)` — no credential, no protected-only bit, no
certificate — while `fn-served-open` pinned the operator's. The owner decides
a connection's role at accept from the peer table and matches the SOURCE
ADDRESS and nothing else (`fn-owner-peer-name-for`, host/owner-host.lisp), so
wherever a configured peer answers on loopback every client is opened by the
peer branch. On the v0 matrix's two nodes that was every client: `AUTHINFO
PASS` answered 481 with the secret `fn principal set-password` had just
written, `CAPABILITIES` carried no AUTHINFO line, and POST was never gated.
The measurement, one variable at a time, is
[the live record](../planning/evidence/auth-live-2026-09-21.md); the repair is
the `acfg` argument through `fn-served-open-peer`, `fn-own-open-peer` and
`fn-owner-open-peer`, and PRF-039 carries the theorems that are false of
the old definition. The operator sets the policy with `fn init
--auth-required` / `--auth-protected-only`, which is also new: before it there
was no way to reach `fn-auth-config-requiredp` from the operator surface. `fn principal
set-password --posting/--no-posting` writes the flag; `fn-auth-postingp`
reads it. Authenticated, the credential decides and nothing else: a
principal enrolled without the flag passes the 480 gate and is still
refused RFC 3977 §6.3.1.1's `440`, however permissive `[posting] enabled`
is. Unauthenticated, a configuration that requires authentication refuses,
and one that does not leaves the decision where it was, with
`fn-nntp-post-step` and the pinned injection configuration. The
CAPABILITIES `POST` label is the conjunction of the two, so the label, the
greeting code and the 440 cannot disagree
(`fn-auth-post-without-permission-is-not-offered` and its lift
`fn-auth-step-post-without-permission-is-not-offered`, with
`fn-served-dispatch-of-a-refused-post-leaves-the-wire-in-place` in
`books/nntp-auth-invariants.lisp`: no 340 means no body means no
submission).

Reader authorization does not stand in for transit authorization. On a
connection the owner resolved from a configured peer source role,
`fn-auth-step` delegates IHAVE, CHECK and TAKETHIS without requiring an
AUTHINFO principal; `fn-peer-step` owns their configured-peer decision. A
reader connection still receives that layer's 502 refusal for the transit
verbs, while local POST and reader commands remain subject to the pinned
AUTHINFO policy. CAPABILITIES takes the same composed route: IHAVE and
STREAMING appear exactly when the pinned peer record has an inbound half;
AUTHINFO USER continues to describe only the reader mechanism the connection
may use now.

**Open, named**: the fold-level form of that statement — no read of a
connection under a configuration that grants posting to no one emits a
submission — is `OB-AUTH-FOLD`, recorded in `planning/proofs.json` and in
the header of `books/nntp-auth-invariants.lisp` with the three lemmas it
waits on.

## Scope

No moderation, automated control-message execution, private-mail confidentiality,
or unrestricted federation is implied by this profile. Those need explicit
policy and authorization. First client acceptance tests should include an actual
newsreader and an independent transcript client, rather than only fn talking to
itself. Legacy convenience aliases are added only with documented semantics.
