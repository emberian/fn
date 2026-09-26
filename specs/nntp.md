# NNTP projection and article acceptance

Status: the selected reader profile is implemented and advertised, and POST is
advertised exactly on the connections that may use it. `books/nntp.lisp` always
advertises `VERSION 2`, `READER`, `OVER MSGID`, `HDR`, `NEWNEWS` and
`LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS NEWSGROUPS OVERVIEW.FMT`. Every clause RFC 3977
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

NNT-016: XPAT is listed in the capability block and answers RFC 2980 section 2.9 on the served reader step

- `XPAT` is RFC 2980 §2.9 and has no RFC 3977 spelling a client could
  discover instead, so fn lists it as a private-extension label (RFC 3977
  §3.3.3: such a label begins with "X"). `XOVER` and `XHDR` stay unlisted.
  `fn-auth-capability-lines-advertise-xpat` (`books/nntp-xpat.lisp`) is over
  the block the served CAPABILITIES arm renders.
- The pattern rule is §2.9's: "If there are additional arguments the are
  joined together separated by a single space to form one complete pattern."
  A second argument is therefore part of one pattern, not an alternative,
  as in INN's nnrpd. The alternative is the wildmat comma (RFC 3977 §4.2):
  `fn-nntp-xpat-alternation-is-or` shows non-negated alternatives OR at the
  matcher the XPAT arm calls. Matching is case-sensitive: RFC 3977 §4.2, "A
  <wildmat-exact> matches the same character".
- The subject is the served step: `fn-nntp-step-pinned-xpat-is-the-xpat-
  response` equates the XPAT arm of `fn-nntp-step-pinned` (reached from
  `fn-served-step` through `fn-auth-step-pinned` and
  `fn-nntp-post-step-pinned`) with `fn-nntp-xpat-response`.
- The web reader (`tools/fn_web.py` `/search`) sends the reader's own
  wildmat in one bounded `XPAT` window; it builds no pattern.

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
the output bound. The LISTGROUP group buckets do not index NEWNEWS; replacing
this whole-list walk remains open.

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
change acceptance authority or add disk index files. LISTGROUP range reads
select from immutable per-group buckets pinned with that archive, and the
owner/served invariant maintains exact bucket-to-archive correspondence.
OVER and XOVER numeric ranges select numbers from that bucket and resolve each
entry through the same pinned Message-ID trie. The carried bucket/trie relation
proves their complete replies equal the archive fold; XOVER retains its 420
empty-range code and OVER its 423. For G bucket headers, M selected-group
memberships, S output numbers and maximum Message-ID length L, the structural
work is O(G + M + S·M + S·L + S²), plus article rendering. This replaces the
former O(A + S·A + S²) archive search for A retained articles; neither bound
claims elapsed-time performance. HDR/XHDR, GROUP, NEXT, LAST and NEWNEWS still
use their current archive folds. The
LISTGROUP selection cost is at most G + S inspected headers and selected
entries, for G retained groups and S entries in the chosen group; this excludes
number sorting, reply rendering, and index construction.

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
   A Store refusal names its kind (`fn-post-store-refusal-line`), each a
   distinct `441` line (`fn-post-outcome-store-refusal-kinds-are-distinct`):
   `:duplicate` "this article is already stored here", `:conflict` "a
   different article with this Message-ID is stored here" (the two answers of
   `fn-pb-existing-action`, which since D25 compares the poster's *source*:
   each article's source is recovered by the injection inverse
   `fn-inj-source-of`, under the agent the submission's own Path line names,
   and two sources are compared octet for octet; an article that inverse does
   not read -- another agent's, a relayed one, an ambiguous recipe-v1 record --
   is compared as octets, never widened. So a resend of the same source at any
   later clock reading, with its Date present or absent, is the duplicate, and
   any changed source octet, an authored Date changed or removed included, is
   the conflict; the stored record keeps its injected fields;
   `books/poster-bytes-invariants.lisp`), `:malformed` (`fn-owner-prepare`'s `:invalid`),
   `:unaffordable` (the persisted profile or the transaction capacity),
   `:storage-failed` (a write that failed before publication, whose
   reservation `fn-owner-known-abort` consumed, so nothing was stored), the
   three control-message filing refusals of `fn-pa-filing-plan` (C1,
   [peering §8](peering.md#8-control-messages-filing-and-authority-implemented-cancel-decided-served-withdrawal-open-group-control-deferred)):
   `:control-not-filed` "control message not filed: its control group is not
   configured here", `:control-malformed` "the Control header field is
   malformed" (a signed control article is filed like an unsigned one, so
   the former `:control-signed` word was removed from both tables, PKT-208),
   and
   `:refused` "the article was refused" for a refusal no kind names. RFC 3977
   §6.3.1 permits `441` for all of them; the distinct text is a stronger fn
   guarantee and its exact words are a local policy choice (P2; the
   duplicate-versus-conflict key is decision D25). A refusal is
   rendered only while no completion has been consumed after the take: once
   one has, every word but `:durable` is the uncertain line
   (`fn-own-consumed-completion-is-240-or-uncertain`), so a durable article
   is never reported refused.

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

The injecting agent generates `Path`, `Injection-Info`, and `Message-ID` and
`Date` when the proto-article omits them (RFC 5537 §3.4.1 permits exactly
those three omissions), and `Injection-Date` as RFC 5537 §3.5 item 11
directs. `From`, `Subject` and `Newsgroups` must be supplied. The generated
lines are *prepended*: with no Path supplied, the supplied source is a
verbatim suffix of the injected article, which is proved
(`fn-inj-injected-article-retains-the-source-octets`), and is what makes the
"MUST NOT alter the body" clause of §3.5 item 6 hold structurally rather than
by inspection. With a supplied Path (D32, below) the one change is `AGENT!`
inserted at the start of the Path content; the body and every other octet
are the poster's, and the inverse recovers the source exactly.

**Injection-Date (RFC 5537 §3.5 item 11), one theorem per case in
`books/injection-invariants.lisp`.** The RFC requirement: a supplied
Injection-Date MUST NOT be modified or replaced; when the proto-article
supplies both Message-ID and Date, an Injection-Date MUST NOT be added;
otherwise one MUST be added with the current time. fn implements the last two
as stated (`fn-inj-no-injection-date-when-date-and-message-id-are-supplied`:
the injected article is then the Path line, the Injection-Info line and the
source, at every clock reading; `fn-inj-injection-date-is-the-clock-otherwise`).
For the first, fn's accepted-input policy refuses a proto-article carrying an
Injection-Date (`:injection-date-present`,
`fn-inj-a-supplied-injection-date-is-never-replaced`) -- a local choice, not an
RFC requirement, and consistent with it, since nothing is modified when
nothing is injected. fn refuses rather than keeps it because §3.5 item 3 would
have it judge that date's distance from now with no date-time parser, and
because fn's generated Date is recognised by its equality with the
Injection-Date fn wrote.

**The injected block and its inverse (recipe v2, 2026-09-24).** The block is
Path; then, when anything is generated, Injection-Date, the generated
Message-ID, the generated Date, in that order; then Injection-Info, which
closes it. Every octet after the Injection-Info line is the poster's, so the
block names which fields were generated and `fn-inj-source-of` recovers the
source exactly (`fn-inj-source-of-inverts-the-injection`, for every clock
reading and all four generated-field cases). That is the provenance D25
needs, carried in the stored octets themselves, with no field added to the
Store record. Recipe v1 (before 2026-09-24: Path, Injection-Date,
Injection-Info, generated lines, source; an Injection-Date always) is
recognised by its Injection-Info directly after the Injection-Date, which v2
never writes; its source is read only where v1 is unambiguous
(`fn-inj-source-of-a-v1-record`), and a v1 record whose source position opens
with a Date line of the injection's date or with its own Message-ID line gives
back nothing (`fn-inj-source-of-an-ambiguous-v1-record`), so it is compared
octet for octet.

#### A supplied Path (D32, 2026-09-25)

NNT-012: a served POST whose proto-article carries one Path field that is
RFC 5536 §3.1.5 syntax is injected with the node's identity and "!"
prefixed to that Path in place, and the injection inverse gives back the
poster's source, supplied Path included, octet for octet; a malformed,
duplicated or POSTED-carrying Path is refused by name.

(PRF-090, SCN-050.) RFC 5537
§3.4.1 lets a proto-article carry Path (without a POSTED diag-keyword) and
§3.2.1 has the injecting agent prepend its path-identity and "!". fn does
exactly that, in place: the injected Path is `AGENT!` followed by the
supplied content, inserted at the octet where that content begins
(`books/injection-path.lisp` `fn-inj-splice`), and the injected block is
recipe v2's without its Path line (**recipe v3**, `fn-inj-block`), so the
article has one Path, where the poster put it. The supplied Path is part of
the poster's source under D25: `fn-inj-source-of` removes the insertion and
gives the source back octet for octet
(`fn-inj-source-of-inverts-the-injection`, now over v2 and v3;
`fn-inj-unsplice-of-a-splice`), so a resend at any clock is "already stored
here" and a changed supplied Path is the conflict line
(`fn-pb-one-source-at-two-clocks-is-one-article`,
`fn-pb-two-sources-are-two-articles`, whose agent is read from a v3 block's
Injection-Info line). The verbatim-suffix theorem now carries the hypothesis
that no Path was supplied; with one supplied the octets are stated exactly by
`fn-inj-injected-octets-are-the-block-and-the-prefixed-source`, and each
Injection-Date case has its twin (`...-with-a-path`). What stays refused, each
with its own 441 line: a Path that is not RFC 5536 §3.1.5 syntax
(`:path-malformed`, "Path is not a valid path"; fn also requires the content
to begin one SP after the colon, since `AGENT!` before extra WSP would not be
a path), a second Path field (`:path-duplicate`), a Path carrying the POSTED
diag-keyword (`:path-posted`, local policy: it claims an injection this node
did not make), and Xref (`:xref`, the server's). fn writes no `!.POSTED`
diagnostic (RFC 5537 §3.2.1 item 2 is a SHOULD), for a supplied Path as for
its own `AGENT!not-for-mail`. The hybrid carrier route
(`fn-hsig-injected-carrier-plan`, the operator's signed submission) still
refuses a carrier that supplies Path (`:path-present`), so its exact signed
source stays a suffix; a served POST of a signed carrier with a Path is
accepted, and the authored-source projection (`fn-hc-authored-source`, which
drops the Path the poster wrote) is unchanged by the prefix
(`tests/acl2/hybrid-store-tests.lisp`).

One further choice here is local policy, not an RFC requirement, and is
recorded as such:

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
assumes otherwise. A client therefore creates and persists its Message-ID
before the uncertain network operation (`docs/agents.md`): a resend under that
Message-ID of the same source is answered "already stored here" at any later
clock reading (`fn-pb-a-resend-at-any-clock-is-answered-already-stored`), a
changed source under it is the conflict line
(`fn-pb-a-changed-source-is-answered-conflict`), and neither writes anything
(`fn-pb-an-existing-action-writes-nothing`); a deliberate second post of the
same text under a new Message-ID is a new article.

### Stored, visible and absent: settling a lost reply (NNT-019)

NNT-019: 430/423 is a visibility observation, not acceptance evidence;
acceptance is settled by re-submitting the same source; an ordinary reader
that cannot resubmit reports unresolved.

A posting agent that lost the reply to a POST does not know whether the node
accepted the article. A Message-ID lookup does not tell it: the node answers
`430` for an article it never stored, and also for one it accepted and a
cancel since withdrew from newly published views (`430 withdrawn`, NNT-011,
D29 C3), for one whose content was reclaimed (D13), and for one this reader is
not served. None of these erases the identity history the Store keeps.

The honest question is the re-submission of the SAME source under the SAME
Message-ID (D25). The node answers it from the Store, not from a reader view:

- `240`: the re-submission is accepted, and it is the one acceptance;
- `441 posting failed; this article is already stored here`: the source was
  accepted earlier;
- `441 posting failed; a different article with this Message-ID is stored
  here`: this source is not stored under that Message-ID;
- any other answer (a refusal by a policy the poster no longer satisfies, a
  lost connection, the node's own uncertain line): unresolved.

What is proved, over the decision the host calls
(`books/visibility-join.lisp`; `host/native/owner.lisp` `fnn-owner-attempt`
through `host/owner-host.lisp` `fn-owner-existing-action-buffer`, whose
decision is `fn-rclb-existing-action`; the carried-signature ingress through
`fn-owner-existing-action`, `fn-rcl-existing-action`): once a Message-ID is
held, the decision answers `:duplicate` or `:conflict`, never nil, after any
Store completion (`fn-vj-a-completion-keeps-a-held-message-id-answered`; the
cancel that withdraws the target is such a completion, `fn-sn-finish`) and
after reclamation (`fn-vj-reclamation-keeps-a-held-message-id-answered`); the
served reply to it while the re-submission is in flight is one of the two
441 lines (`fn-vj-a-held-message-id-is-answered-441`). The host returns that
word before any reservation or prepare, so no transaction or article number
is allocated. That the same source is `:duplicate` rather than `:conflict`
after reclamation is `fn-rcl-existing-action-after-reclaim` with its stated
SHA-256 collision disjuncts. Not proved: the login-binding gate and the
posting allowance run before the Store's decision, so a poster whose
authorization changed is answered by them (unresolved); PKT-164 in
`planning/evidence/visibility-join-2026-09-25.md` is the decision on a
privileged query for that case.

This is a stronger fn guarantee and a client contract, not an RFC
requirement: RFC 3977 §6.3.1 allows 441 for any posting failure; the two
duplicate answers and their meaning are fn's (D25). The clients
(`tools/fn_client.py` `post --draft` / `reconcile`, `tools/fn_web.py`
`/reconcile`) keep the original observed outcome, record each
reconciliation beside it, re-send the stored bytes, and never mint a second
Message-ID; `docs/agents.md` states it for agents.

### One source, one identity across routes (NNT-020)

NNT-020: one authored source keeps one identity through every route the node offers, and each layer's equality is the one its contract means

The mandate's cross-route corpus (`tests/fixtures/source-corpus`) is driven
through every route by `tests/test_native_source_corpus.py`, which prints the
identity table. What each identity is, and which equality holds:

| Layer | Identity | Equality the contract means |
| --- | --- | --- |
| Application operation | the client's own (a persisted Message-ID) | a client that omits Message-ID has no retry identity: its resend is a new article (NNT-005) |
| Message-ID | RFC 5536 s3.1.3 | transit (IHAVE, CHECK, TAKETHIS) and BP admission decide duplicates by it alone (RFC 3977 s6.3.2, RFC 4644); `fn-peer-decide-offer`, `fn-peer-decide-transfer` |
| Authored source | the poster's octets, recovered by the injection inverse (`fn-inj-source-of`) | on the injecting routes (served POST, `operator post`, `hybrid-author`) the D25 verdict the host calls, `fn-rcl-existing-action`: same source at any later clock is "already stored here" (`fn-sr-a-retry-is-already-stored`), one changed authored byte is "a different article" (`fn-sr-a-changed-source-is-a-conflict`); a supplied Path tail is source (D32); no field is normalized, so a signed carrier is stored octet for octet after the injected block |
| Stored representation | the record payload (`store inspect`), its SHA-256 | the injected octets on the injecting node; on a receiving node the same octets with that node's path identity spliced into Path and any Xref dropped (`fn-peer-relayed-octets`); an injection is never a tombstone (`fn-sr-an-injection-is-not-a-tombstone`) |
| Tombstone | SHA-256 of the octets and of the source, and the injecting agent | a retry after reclamation is still the duplicate and a changed source the conflict, up to a SHA-256 collision on the two sources (`fn-sr-a-retry-after-reclaim-is-already-stored`, `fn-sr-a-changed-source-after-reclaim-is-a-conflict`); unreachable-in-composition until a program writes tombstones (`store reclaim` is not implemented) |
| Bundle identity | RFC 9171 (source EID, creation time, sequence) | one per carried request; a re-offer of an uncertain forwarding attempt keeps it (specs/bp-node-machine.md s4.3.1) |
| Forwarding attempt | one durable kind-8 FNBS row | settled by kind 9; never an article identity |
| Local sequence and number | per node, per group | never compared across nodes; kept across reopen |

The relayed copy's authored source is not a value the receiving node
recomputes for unsigned articles: its duplicate key is the Message-ID. For a
signed carrier the receiver verifies the author's signature over
`fn-hc-authored-source`, which drops exactly the node-added fields.

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

**Login binding 2026-09-25**: `principal bind LOGIN PRINCIPAL-HEX` and
`principal unbind LOGIN` write or remove the login's `signing` field through
the same replacement machine; `policy set posting-policy bound-logins` turns
on the served POST gate that refuses a bound login's article unless it is
signed by the bound principal (`:login-unsigned`, `:login-not-bound`, each its
own 441 line). specs/identity.md, "A login bound to a signing principal".

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

### Invitation-code accounts (NNT-034)

NNT-034: An operator's one-use invitation code lets a friend make their own AUTHINFO account over TLS, bound once and only once across a crash, without the operator editing auth.toml or restarting

An account for a friend is made by the friend, from a code the operator hands
them, and lands in the configuration the owner publishes live. None of this is
an RFC requirement: `XREDEEM` is **an fn extension**, not RFC 4643's AUTHINFO
(section 2.3 defines USER/PASS and nothing here overloads it); the reply codes
reuse RFC 4643's 381, 281, 482 and 483 in the classes RFC 3977 section 3.2
gives them.

- **The code.** `operator CONFIG account invite [--expires SECONDS]` prints one
  code, once, and stages the pending row. The code is never stored: the row is
  keyed on the crypto seam's tagged SHA-256 digest of it
  (`fn-acct-code-digest`, tag `"fn-account-code-v1"`). That a code the
  operator did not print finds no row is the seam's preimage resistance
  (A-CRYPTO), not a theorem here.
- **The slot.** The configuration's tenth slot `accounts` (books/config.lisp
  `fn-cfg-accounts`) holds `(DIGEST ISSUER EXPIRY 0)` pending and
  `(DIGEST LOGIN VERIFIER 1)` redeemed; VERIFIER is the text of the
  books/auth-secret.lisp verifier (salt and digest, 96 hexadecimal
  characters; `fn-acct-text-verifier-of-verifier-text` is the round trip). The
  kinds are `:account-invite` (code 15) and `:account-redeem` (code 16). A
  row is never removed.
- **Admission** (`fn-cfg-delta-reason`): an invite of a digest that keys a row
  is `:account-digest-reused`; a redeem of no row is `:account-unknown`, of a
  pending row whose expiry the record's stamp does not lie wholly before (or
  a stamp without a wall clock) `:account-expired`, under a login a redeemed
  row holds `:account-login-taken`, and of a redeemed row
  `:account-redeemed` unless it is the identical row.
- **Once only** (PRF-164): a redeemed row is the same row after every later
  acceptable record the owner replays (`fn-acct-redeemed-row-stays-across-replay`);
  the redeem plan (`fn-acct-redeem-plan`, a pure function of the
  configuration value and the request) plans a redeem only of a delta the
  configuration admits (`fn-acct-redeem-plan-is-admitted-and-redeems`), and
  after that delta is published the same request plans "already redeemed by
  this login" and stages nothing
  (`fn-acct-redeem-plan-after-its-redeem-is-already-redeemed`: the crash cut
  after `fn-ocl-publish`'s root barrier and before the reply). Another login
  is refused (`fn-acct-redeem-plan-refuses-another-login`); an unknown code
  stages nothing (`fn-acct-redeem-plan-of-an-unknown-code-stages-nothing`).
- **The credential table.** One table, two producers: auth.toml's credentials
  read at start, then one credential per redeemed row of the configuration a
  connection pins at open (books/nntp-auth.lisp
  `fn-auth-config-with-accounts`, called by books/owner-config.lisp
  `fn-ocfg-open`). auth.toml wins a login both name. A redeemed account's
  credential is its login, the login's local principal
  (`fn-acct-local-principal`, the principal `fn principal set-password`
  gives a login without `--principal`), the row's verifier and the posting
  allowance; its AUTHINFO USER/PASS then binds exactly that principal
  (`fn-auth-config-with-accounts-finds-the-redeemed-credential` with
  `fn-auth-step-principal-login-binds-exactly-the-unique-match`). The
  login-to-signing-key binding is not this section's (specs/identity.md).
- **The wire** (fn extension; RFC 4643 section 2.3 is AUTHINFO's and is not
  overloaded; the codes keep RFC 3977 section 3.2's classes):

      XREDEEM CODE NAME        -> 381 send the password with XREDEEM PASS
      XREDEEM PASS PASSWORD    -> (held) then 281 or 482

  `XREDEEM CODE NAME` caches the code and the login in the connection's memory
  and answers `381`. `XREDEEM PASS PASSWORD` (one token, like AUTHINFO PASS;
  the password is never a bare line, so a client that loses its place cannot
  send it as a command) answers nothing at once: the session holds, the served
  fold stops at the end of that line, and the owner, under its mutex, reads a
  16-octet salt from the OS CSPRNG, runs `fn-acct-redeem-bounded-plan` over
  the live configuration, and publishes a `:redeem` plan's delta through
  `fnn-owner-live-reconfigure-locked`. Only then does it feed the connection
  `(:account-outcome WORD)`: `281 account bound; authenticate with AUTHINFO on
  a new connection` when WORD is `:bound` (the record is durable, or was
  already durable for this login and password), otherwise `482 invitation
  code refused`, with the reason class in the service log (`account redeem
  refused account-unknown`) and never the code, its digest or the password.
  A crash between the publication and the reply loses the 281; the same
  exchange again answers 281 and binds nothing new. Before a TLS layer on a
  listener that requires one both lines are `483` (AUTHINFO's rule above); on
  an authenticated connection `502`; `XREDEEM PASS` with nothing cached is
  `482`. The snapshot a connection pinned at open does not change, so the
  friend logs in with AUTHINFO USER/PASS on a new connection. A code is the
  operator's 32 hexadecimal characters and is never the word PASS. Theorems:
  `fn-auth-step-pinned-xredeem-before-tls-is-483`,
  `fn-auth-step-pinned-xredeem-pass-holds-for-the-owner`,
  `fn-auth-step-pinned-redeem-outcome-answers-the-word`,
  `fn-acct-redeem-word-is-bound-only-after-a-durable-redeem`.
- **The admission limit** (D27: a profile limit, not a code ceiling): a
  redeem is refused `:account-credential-bound` once auth.toml's credentials
  plus the redeemed rows reach the store profile's `max-credentials`, the
  bound auth.toml is loaded under
  (`fn-acct-redeem-bounded-plan-refuses-exactly-past-the-operator-bound`); a
  resume adds no row and is never refused by it. Pending rows are bounded by
  their expiry, in the record clock's unit (books/clock.lisp: wall
  milliseconds since 2000-01-01).
- **The operator.** `operator CONFIG account invite [--expires SECONDS]`
  (default 604800): the host reads 16 CSPRNG octets, ACL2 renders the code
  (`fn-acct-code-text`) and its digest, and only the digest is sent (to the
  running owner over the control socket, or offline into the configuration
  when no owner runs, as `peer add` is); the code is printed once, to stdout,
  after the pending row is durable. `account list` prints `redeemed LOGIN
  PRINCIPAL-HEX` and `pending expires EXPIRY` lines, never a digest or a
  verifier.
- **Rollback (PKT-440, decided).** Once an account code is redeemed on a
  release with accounts, releases before it cannot open the store (an older
  image refuses delta kinds 15 and 16 at decode); roll back only from the
  pre-upgrade snapshot. The upgrade rehearsal checks that sentence.

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

**Proved for the local posting path**: `OB-AUTH-FOLD` is
`fn-auth-fold-step-has-no-local-submission` in `books/nntp-auth-fold.lisp`.
For a valid served connection with a pinned no-posters credential policy and
no pending local POST body, the complete `fn-served-step` effect list has no
injected submission; `fn-auth-fold-step-preserves-safe-connp` carries those
conditions across reads. This does not prohibit a separately authorized
transit peer: a no-posting credential can bind a configured peer role, and
TAKETHIS may then produce a distinct transit submission. The complete-read
witness and local POST counterexample for the removed policy premise are in
`tests/acl2/nntp-auth-fold-tests.lisp`.
The test also constructs a well-formed, no-posters connection with a pending
POST body by changing the pinned policy after a genuine 340 offer. Its body
does submit locally, demonstrating why the no-pending premise is needed for
an arbitrary state. That state is **unreachable in composition** from a
no-posters open: the open has no pending POST, and
`fn-auth-fold-step-preserves-safe-connp` preserves that fact across reads.
`fn-served-connp` is the structural connection invariant seeded by open and
carried by the served path; it is theorem vocabulary, not a runtime
whole-store check or an independent posting authority condition.

## Public exposure (NNT-031)

NNT-031: A reader port facing strangers admits, paces and closes connections within operator limits ACL2 decides, and an unauthenticated session under the none policy reaches no reader or posting command

A listener off loopback answers people the operator never met. What it
owes them is RFC 3977's, and what it will spend on them is the operator's,
decided in `books/public-exposure.lisp` (PRF-161) over rows of the live
configuration (`fn operator CONFIG policy set SLOT VALUE`, applied to the
running owner like every configuration record). The host counts nothing: it
passes the kernel's source address, the connection id and the owner's clock,
and sends, waits or closes as the answer says.

| Slot | Decides | The client sees | Loopback default | Public default |
| --- | --- | --- | --- | --- |
| `exposure-connections` | connections held (never above the run's max) | `400 too many connections; try again later`, then close (RFC 3977 §5.1.1) | the run's max | the run's max |
| `exposure-per-address` | connections held from one source address | `400 too many connections from this address; try again later` | the total | 8 |
| `exposure-steps-per-second` | served steps one address starts per 1000 ms (one step: one host read, D27 work) | nothing: the connection waits for the next quantum (TCP backpressure) | unlimited | 64 |
| `exposure-first-seconds` | wait for the first command (RFC 3977 §3.1 permits a shorter one) | close, no reply (§3.1) | none | 60 |
| `exposure-idle-seconds` | autologout after that (§3.1: at least three minutes) | close, no reply | none | 600 |
| `exposure-auth-failures` | `481` answers one address may draw per minute | `400 too many authentication failures; closing connection`, and at the next accept `400 too many authentication failures from this address` | unlimited | 10 |
| `exposure-posts-per-minute` | submissions per authenticated principal per minute | nothing: the principal's connections wait for the next minute | unlimited | 60 |
| `anonymous` (policy) | what an unauthenticated session may do: `none` or `open` | under `none`, `480 authentication required` for every reader and posting command (RFC 4643 §2.2) | as `[auth] required` | `none` |

Progress that resets the timers is an answered command or 512 octets
consumed since the last progress (§3.1's "significant amount of data"), so a
client trickling one octet at a time is closed by the first-command or idle
timer. `anonymous open` never weakens `[auth] required`. A row that is absent
takes the listener's default: loopback keeps the behaviour every store had
before this section; a listener outside 127.0.0.0/8 and `::1` takes the
public column. What the proof covers, what the host adds and what is not
covered is PRF-161's statement and the record
`planning/evidence/public-exposure-2026-09-26.md`; `operator CONFIG health`
prints the exposure lines after its eight states.

Which of these is an RFC requirement, an fn guarantee and a local policy:
the 400/502 greeting and the immediate close after it, and the 480 for an
unauthenticated command, are RFC 3977 §5.1 and RFC 4643 §2.2; the silent
close on the timer is RFC 3977 §3.1's SHOULD; every number, the per-address
accounting and waiting instead of refusing are local policy.

## Scope

No moderation, automated control-message execution, private-mail confidentiality,
or unrestricted federation is implied by this profile. Those need explicit
policy and authorization. First client acceptance tests should include an actual
newsreader and an independent transcript client, rather than only fn talking to
itself. Legacy convenience aliases are added only with documented semantics.
