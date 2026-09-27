# NNTP projection and article acceptance

Status: the selected reader profile is implemented and advertised, and POST is
advertised exactly on the connections that may use it. `books/nntp.lisp` always
advertises `VERSION 2`, `READER`, `OVER MSGID`, `HDR`, `NEWNEWS` and
`LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS MOTD NEWSGROUPS OVERVIEW.FMT`. Every clause RFC 3977
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

## HELP: the served command table (NNT-038)

NNT-038: HELP lists every command the served dispatcher recognizes, and a command HELP does not list is answered 500

RFC 3977 section 7.2 requires HELP (it is in the mandatory bundle) and
leaves its text free: "a short summary of the commands that are understood
by this implementation". That is the RFC requirement. fn's stronger
guarantee is that the summary is exact: the lines HELP prints are the rows
of one table, `*fn-nntp-served-command-table*` (`books/nntp-help.lisp`),
and every keyword the served step does anything with is in it. The
grouping into six lines and their order are local policy:

```text
100 help text follows
CAPABILITIES HELP QUIT MODE DATE POST
AUTHINFO STARTTLS XREDEEM
GROUP LISTGROUP LIST NEXT LAST NEWGROUPS NEWNEWS
ARTICLE HEAD BODY STAT
OVER XOVER HDR XHDR XPAT
IHAVE CHECK TAKETHIS
.
```

The table spans three layers of one dispatcher. `fn-auth-step-pinned`
(`books/nntp-auth.lisp`, called by `books/served.lisp` `fn-served-dispatch`)
answers AUTHINFO (RFC 4643), STARTTLS (RFC 4642), XREDEEM (NNT-034) and the
connection's CAPABILITIES; the peer layer answers IHAVE, CHECK, TAKETHIS
and MODE STREAM on a peer connection, and a reader connection answers the
three transit verbs 502 (RFC 3977 section 3.2.1: understood, not
permitted); `books/nntp.lisp` answers the rest. Before 2026-09-26 HELP
listed only the last layer's verbs (the NNTP gap inventory's R4).

`fn-auth-step-pinned-answers-500-to-a-keyword-help-does-not-list` (PRF-194)
is the keystone: on a served session in command mode (not handshaking TLS,
no transit article or POST body awaited, the reader session open), a
well-formed command line whose keyword is not in the table is answered
exactly `500 command not recognized`, submits nothing and leaves the
session unchanged. `fn-nntp-help-renders-the-served-command-table-by-definition`
says HELP's lines are the table's rows. The converse, that each listed
keyword draws a reply other than 500 for every argument list, is checked by
evaluation on a served session in `tests/acl2/nntp-help-tests.lisp` and is
not a theorem (PKT-571).

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
and fn does not fabricate one. `LIST NEWSGROUPS` shows each group's description when the operator has set
one, and otherwise the fixed marker `(no description)`: the marker is a
statement about the server, not about the group, and it is **not** the empty
string: Python `nntplib` strips the line and then requires a name, white
space and text, so a bare `name TAB` drops the group from `descriptions()`
entirely (measured against `tests/interop_nntplib.py`, 2026-09-20). How a
description is set and shown is the next section.

## Group descriptions and the message of the day (NNT-039)

NNT-039: The operator sets a group's description and the node's message of the day on a running node, and LIST NEWSGROUPS and LIST MOTD show exactly what the configuration holds

- **RFC requirements.** RFC 3977 §7.6.6: `LIST NEWSGROUPS [wildmat]` answers
  215 and one line per group, the name, white space and "a short
  description"; §7.6.1's argument grammar (a wildmat, else 501). RFC 6048
  §2.5: `LIST MOTD` takes no argument ("Otherwise, a 501 response code MUST
  be returned"), answers 215 and a dot-stuffed block, "MAY be empty", and a
  server that does not maintain it answers 503.
- **Stronger fn guarantees.** The text is the configuration's, published
  live and replayed: `fn operator CONFIG group describe NAME [TEXT ...]` and
  `fn operator CONFIG motd set LINE [LINE ...] | motd clear` each publish one
  configuration record carrying one `:set-group-description` delta (config
  delta kind code 20, `books/config.lisp`), which a running owner applies
  over its control socket like every other configuration change and a
  restart replays. The reader is shown what the connection's pinned
  configuration holds, and nothing a host computed:
  `fn-served-step-list-newsgroups-is-the-described-listing` and
  `fn-served-step-list-motd-is-the-configured-message`
  (`books/owner-descriptions-read.lisp`), with
  `fn-oag-description-of-the-listing` and `fn-oag-motd-of-the-listing`
  stating what the posting configuration `fn-oag-post-config`
  (host/owner-host.lisp `fn-owner-post-config`) carries, and
  `fn-cfg-description-after-set-is-its-pieces`,
  `fn-cfg-description-after-set-of-another-name`,
  `fn-cfg-motd-after-set-is-its-lines` and
  `fn-cfg-descriptions-of-other-kinds` (`books/config-descriptions.lisp`)
  what a delta does. The injection decision does not read the listing
  (`fn-inj-decide-ignores-the-listing`).
- **Local policy.** A description is printable ASCII (octets 32 to 126) with
  at least one graphic octet; admission refuses anything else by name
  (`:description-row`, `:description-blank`), and a name that is neither a
  live group nor the node (`:no-such-group`,
  `fn-cfg-set-group-description-refuses-an-unknown-group-by-definition`). RFC 6048 §2.5
  asks for UTF-8; printable ASCII is a subset, and the operator's argv is
  ASCII today (`fn-native-admin-argvp`). A description is cut into row
  pieces of at most 256 octets (the configuration row's label,
  `*fn-cfg-max-label*`) and concatenated when shown, so its length is bound
  by what one configuration record represents, never by a row; a message
  line is one row, so a line is at most 256 octets. fn maintains the message
  (CAPABILITIES names `MOTD`), so a node without one answers an empty 215
  block, never 503. A description or line the reader's test refuses is not
  sent (the marker is, or the line is dropped); admission makes that case
  unreachable.
- **Scope.** The listing is pinned with the connection's configuration: a
  connection opened before `group describe` keeps the text it opened with,
  as it keeps the group table. XGTITLE (RFC 2980 §2.12) is not served.

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
number through the bucket's number index (a trie keyed by local number, at most
31 levels for numbers up to 2^31 - 1; each entry's number and Message-ID are
decided once, when the entry is added) and then the same pinned Message-ID
trie. The group index carries the relation that every bucket's number index is
its entries' (`fn-gidx-numbers-okp`, established by every build and preserved
by every put and refresh); under it the served lookup equals the bucket walk
(`fn-gidx-nidx-number-article-is-walk`, PRF-189), and the carried bucket/trie
relation proves their complete replies equal the archive fold; XOVER retains
its 420 empty-range code and OVER its 423. For G bucket headers, M
selected-group memberships, S output numbers and maximum Message-ID length L,
the structural work is O(G + M + S·31 + S·L + S²), plus article rendering.
This replaces the former O(G + M + S·M + S·L + S²) bucket walk per row
(over-number-index) and before it the O(A + S·A + S²) archive search for A
retained articles; neither bound claims elapsed-time performance. HDR/XHDR, GROUP, NEXT, LAST and NEWNEWS still
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
`:lines` the retained body line count.

### The Xref overview field (PRF-206, 2026-09-26)

On the served path (the pinned dispatcher, `fn-nntp-archive-command-pinned`)
every OVER/XOVER line carries a ninth field in RFC 3977 §8.3.2's full form,
`Xref: SERVER group:number ...` (RFC 5536 §3.2.14 syntax), and LIST
OVERVIEW.FMT lists `Xref:full` after the seven fixed lines (§8.4). The
distinction:

- RFC requirement (§8.3.2, §8.4): a field past the eighth is named in LIST
  OVERVIEW.FMT, and a full-form field carries its header name. Both are
  decided on the same value, the environment's server name
  (`fn-nntp-xref-server`), so the format list and the lines never disagree.
- fn guarantee (PRF-206): the locations are exactly the (group, number)
  pairs at which this node serves the article, the local numbers GROUP,
  LISTGROUP and ARTICLE n use (`fn-xref-pairs-exact`), each an entry the
  group index builds for it (`fn-xref-pair-is-an-index-entry`); SERVER is
  the node's `path-identity` (`fn-oag-listing-server-is-the-path-identity`;
  unset, the `.invalid` agent); the eight fields are the eight-field
  renderer's (`fn-nov-served-lines-numbered-extend-the-eight-fields`). Local
  numbers are never merged across nodes: a peer's Xref is not read.
- Local policy: Xref is overview metadata only. ARTICLE and HEAD serve the
  stored octets as held (no Xref header is spliced in); a proto-article
  carrying Xref is refused at injection (RFC 5537 §3.5 item 2), but an
  article a peer relayed is stored as offered, so its HEAD may carry the
  peer's Xref with the peer's numbers (PKT-597 (c)); the overview field is
  the one naming this node's. A group whose name carries a colon is not listed (none is
  admitted). Without a server name (a blind environment, not the served
  path) the eight fields and seven format lines of before are answered.

## Sessions and framing

NNT-002: maintain a per-connection selected group and current article number.
Failed GROUP leaves them unchanged; successful GROUP selects its first available
article or an invalid cursor for an empty group. Retrieval by Message-ID does
not move either; successful numeric retrieval updates the current article number.
Use the specified 412/420/423/430 cases and error precedence. Later expiry can
invalidate a once-valid cursor; do not bake eternal existence into the invariant.

Local article numbers follow the committed history. RFC 3977 §6 requires one
article per number within a group, one number per article within a group, and
numbers issued in arrival order; it constrains the numbers a server issues to
clients. A local article number held by a submission that was never
acknowledged and never became durable may be assigned to the next committed
article after recovery; numbers are assigned by the committed history, and a
client observes a number only after a 240 or a served view, both after
durability. This is the reading the power-loss campaign measured
(`planning/evidence/power-loss-2026-09-26.md`, "a lost POST's number is used
again": at 258 cuts the fresh POST after recovery took the lost in-flight
POST's number, and no acknowledged or served number moved or was issued twice).

NNT-042: a reader connection's view of the store is a VERSION, the committed
count when the view was taken: the connection sees the articles committed below
it, and a cancel committed after one of them leaves that article visible to the
connection until it advances past the cancel. GROUP and LISTGROUP advance the
connection's version to the current count between commands; within a command
the version is fixed (C3), so a multi-line response is consistent. A long-lived
reader therefore sees a peer's new article after its next GROUP, never only on
reconnection. A stronger fn guarantee than RFC 3977 section 6.1.1, which fixes
no view semantics; `fn-view-advance`, `fn-view-sees` and
`fn-view-cancel-after-target` (books/catalog-delta.lisp) are the ACL2 half; the
served path does not read them yet (PKT-585).

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

### Read-only groups (NNT-040)

NNT-040: a group the operator sets read-only (`group policy NAME n`) refuses a local POST that names it with a 441 naming the reason, and LIST ACTIVE lists it with status `n`, from the same configured list on the same connection

RFC 3977 section 7.6.3 gives LIST ACTIVE a status field: `y` (posting
permitted) or `n` (posting not permitted). RFC 6048 section 2.1 names the
other values; fn serves `y` and `n` only (`m` is moderation, deferred with
P3; `x`, `j` and `=` are not served). `n` means *local* postings are not
permitted: articles relayed by peers (IHAVE, TAKETHIS, BP) still arrive,
which is the RFC's meaning of the flag and not a stronger fn guarantee.

- **Configuration.** `operator CONFIG group policy NAME n|y` (offline, or
  live through the control socket) stages `(:set-group-status NAME STATUS 0
  nil)`, configuration delta code 21 (`books/config.lisp`), admitted only for
  a live group and `y` or `n` (`:no-such-group`, `:group-status`). The fold
  rewrites the group entry's policy identifier (`*fn-cfg-read-only-policy-id*` is
  `n`, the default `*fn-cfg-default-policy-id*` is `y`); nothing else about the
  group changes. Keystone `fn-cfg-set-group-status-sets-the-status`
  (`books/config-invariants.lisp`) over `fn-cfg-apply-delta`: the status set
  is the status read, and no other group's changes. No store record and no
  format changes: the value is replayed, and the delta kind is a code of the
  existing record codec.
- **One list.** The owner's posting configuration
  (`books/owner-agent.lisp` `fn-oag-post-config`, installed at recovery and
  at every live reconfiguration) carries `fn-cfg-closed-names`, the live
  groups whose status is `n` (`fn-cfg-closed-names-are-the-n-groups`). A
  connection answers from the configuration it pinned, like every other
  served answer: a connection opened before the change keeps its answer
  until it re-pins.
- **POST.** `fn-nntp-post-step` runs the gate `fn-gst-post-gate`
  (`books/group-status.lisp`) on an article the injection decision accepts
  (`fn-post-gated-decision`); every refusal the decision makes keeps its own
  line, so a clockless server still answers the clock line. An ordinary
  article (no Control field) that names a closed group, alone or in a
  cross-post, is answered
  `441 posting failed; a group this article names is read-only here (LIST ACTIVE status n)`
  and nothing is submitted. A control message (a cancel) is not a posting to
  the group and is not gated; a Supersedes article is a posting and is.
- **LIST ACTIVE.** LIST and LIST ACTIVE [wildmat] render each group's status
  with `fn-nntp-closed-status` of the same list
  (`fn-nntp-list-status-response`, through the environment
  `fn-post-reader-env` builds from the connection's configuration); with no
  group closed the answer is byte-for-byte the earlier one.
- **The claim.** Keystone `fn-gst-post-gate-refuses-exactly-a-listed-n-group`:
  the gate refuses exactly when the article names a group whose listed
  status is `n`. LIST COUNTS still reports `y` for every group (PKT-575).

### Injection-Info parameters: posting-account and mail-complaints-to (PKT-597, 2026-09-26)

RFC requirement (RFC 5536 section 3.2.8): Injection-Info is the injecting
agent's <path-identity> followed by optional parameters, each at most once;
"posting-account" names the source "in a form that cannot be interpreted by
other sites", and two posts from one source SHOULD carry the same value;
"mail-complaints-to" is an <address-list> for complaints about the poster.
RFC 5537 section 3.5 item 10 asks the injecting agent for the field; relaying
agents never add or change it (section 3.6).

What the node writes (fn guarantee). For a served POST decided under an
authenticated login L, with the node secret installed, the one Injection-Info
line of the stored article is

    Injection-Info: AGENT; posting-account="HEX"[; mail-complaints-to="ADDR"]

where AGENT is the node's path-identity (the agent of the plain line, which
the injection decision writes), HEX the 64 lowercase hexadecimal digits of
HMAC-SHA256 of L's octets under the posting-account purpose key, HKDF-SHA256
of the key ring's current root with the node identity as salt and info
`fn/posting-account/v1` (books/posting-account.lisp fn-pa-account-value over
fn-pa-mac = books/node-secret.lisp fn-ns-posting-account-mac), and ADDR the
`complaints-to` policy of the live configuration when set. Without a login
(an anonymous POST where the configuration allows one, a control or BP
submission) there is no posting-account parameter; without a login and
without an address the line is the plain `Injection-Info: AGENT`. The line
is rewritten in place in the injected block (books/injection-info-params.lisp
fn-ipp-injected-octets, called by books/owner-served-invariants.lisp
fn-own-sub-stored-octets for every local submission the owner stages, before
the Cancel-Lock insertion, which then follows this line); nothing else in
the article moves. Keystones (books/injection-info-params-invariants.lisp):
`fn-ipp-injected-octets-carry-the-parameters` (the stored octets are the
injected block with its one Injection-Info line carrying the parameters,
then the source; the proto-article check refuses a source with its own
Injection-Info, so the line is the article's only one),
`fn-ipp-params-of-a-login` (under a login the parameters open with that
login's value), `fn-ipp-params-without-a-login`,
`fn-ipp-injected-octets-without-parameters`. The login is the one the
`:submit` effect carries: the AUTHINFO USER name of the session at the event
that delivered the article body (books/served.lisp fn-served-login, recorded
by fn-own-finish-read as fn-own-sub-login); an authenticated session refuses
a further AUTHINFO with 502 (RFC 4643 section 2.3.1), so the login in force
for a POST never changes before its article arrives, and an AUTHINFO later in
the same read never claims an earlier anonymous article.

D25 is unchanged. Generated Injection-Info is injecting-node metadata, not
authored source, like the node's Cancel-Lock lines in front of the block
(`fn-oii-stored-octets-keep-the-d25-subject`, books/owner-injection-info.lisp:
the D25 subject of the octets the owner stores is the poster's source,
whatever account, login, key epoch or complaints address wrote them): the injection inverse reads the line with or without
parameters (books/injection.lisp fn-inj-strip-info), so a stored article
with parameters gives back the same poster's source
(`fn-ipp-with-params-keeps-the-source`), a same-source retry under the same
Message-ID resolves as already stored whatever the new header says
(books/poster-bytes.lisp fn-pb-subject; the buffer twin
fn-pbb-strip-info-at), and the operator's retry test is unchanged. No stored
record is rewritten and no migration exists: a record written before this
change has the plain line and reads back as before.

Transit (fn guarantee): an article accepted from a peer keeps the peer's
Injection-Info octet for octet; the transit arm of fn-own-sub-stored-octets
is fn-peer-relayed-octets (Path prepended, Xref removed), which never reads
or writes Injection-Info.

Privacy (local policy, authorized disclosure). The posting-account value is
a LINKABLE PSEUDONYM, not anonymity. What it discloses to every reader of
every copy of the article, here and on every peer: that two articles
carrying one value were posted by one login on this node (RFC 5536 asks for
exactly that, for rate limiting and abuse handling). What it does not
disclose: the login, its length, or any octet of it (the value is 64 hex
digits whatever the login, `fn-pa-account-value-is-hex`, and depends on the
login only through the MAC, `fn-pa-account-value-depends-only-on-the-mac`);
testing a guessed login needs the node secret. The operator authorizes this
by running a node that accepts authenticated posting; docs/operator.md says
so where logins are issued. Not claimed: that one value means one login
(HMAC-SHA256 collision resistance, an assumption about the real function:
for n logins under one secret a shared value has probability at most
n(n-1)/2^257), and not unlinkability across a key rotation (a new epoch gives every login
a new value; the value names only the current epoch). A login name reused for another person
carries the old pseudonym (the value is keyed by the login spelling, not an
internal account id).

Operator surface. `fn operator CONFIG policy set complaints-to ADDR` sets the
address: a durable `:set-policy` row like path-identity, applied live, no
configuration delta code of its own; ADDR must be an <addr-spec> of two
dot-atoms (books/injection-info-policy.lisp fn-ipp-addr-specp), so it has no
DQUOTE, backslash, ";", CR or LF and stands in the quoted-string as it is
(`fn-ipp-addr-spec-has-no-quote-or-line-break`); anything else is refused.
`fn operator CONFIG account hash LOGIN` prints the value an article posted
under LOGIN carries (the host reads STORE/keys/node-secret.key with the
owner's permission checks; ACL2 computes the value,
fn-ipp-account-hash), which is how an operator answers a complaint that
quotes a posting-account. Known limit: the parameters are computed from the
live configuration when the writer stages the article and again when the
completion is checked, so a `complaints-to` change between the two answers
that one POST with the uncertain 441 (the article is durable; a same-source
retry is a duplicate), as a path-identity change already does for transit.

### Own-post cancel and Cancel-Lock (SEC-006)

SEC-006: an unsigned article's poster, and only its poster, can withdraw it: by the same authenticated account on the node that injected it, and across nodes by a Cancel-Key matching the article's Cancel-Lock (RFC 8315)

Status: implemented (PRF-210; lanes newsreader-cancel, -2 and -3; gpt-6's
review of 2026-09-26 section 3, binding, is the design below). An unsigned
cancel or Supersedes whose RFC 8315 Cancel-Key opens a Cancel-Lock of its
target withdraws it, here and on every peer; the node writes the lock and key
for the authenticated ACCOUNT, so a client that writes none (Thunderbird)
cancels its own post, and a client that writes its own (tin) keeps its lines.
RFC 5537 section 5.3 leaves cancel authentication to local policy; the account
basis is that local policy; the lock and key are RFC 8315.

The account. The account id is the principal the connection authenticated as
(`fn-auth-session-subject`, set by AUTHINFO PASS from the credential): a
credential file login's configured principal, or a redeemed account's local
principal, which no later record changes or reassigns. It is recorded on the
submission when the article is enqueued (`fn-own-sub-account`), so the lock
does not depend on the connection still being open when the writer takes it,
and an AUTHINFO later in the same read never claims the article. Not the login
spelling: a renamed login keeps its principal, and a login name alone owns
nothing.

The root and the purpose keys. One random root per key epoch (32 octets from
the OS CSPRNG) in the store directory, the node's persistent private state
under D34: `STORE/keys/node-secret.key` (the current epoch) and
`node-secret-E.key` (each older epoch a rotation kept), directory 0700, files
0600, never served, printed, written into a configuration record or exported.
A file is versioned: `fn-node-secret v1` LF, the epoch (4 octets, big-endian),
the node identity's length (2 octets) and octets, the root
(`fn-ns-file-render`, read back by `fn-ns-file-parse`;
`fn-ns-file-parse-of-render`). `store ROOT node-secret create [IDENTITY]` (and
`init`) writes epoch 1 once and refuses by name when a secret exists; `store
ROOT node-secret rotate [IDENTITY]` keeps the current file as
`node-secret-E.key` and writes epoch E+1. A start reads the current file and
every kept older epoch and hands ACL2 the ring (current first, epochs
strictly decreasing, `fn-ns-ringp`); it refuses by name when a file is
missing, accessible to group or others, or does not parse, and it never
creates a secret. Every use is a purpose key derived by HKDF-SHA256 (RFC 5869)
from one epoch's root, salt the node identity recorded in its file, info a
versioned label: `fn/cancel-lock/v1` (below) and `fn/posting-account/v1`
(Injection-Info's posting-account). `fn-ns-expand-input-separates-info`:
distinct labels never expand the same HMAC input under one root.

What the node writes. The octets the owner stores for a served POST from
account A are `fn-own-sub-stored-octets` of the submission under the owner's
ring (books/owner-served-invariants.lisp; the host stages exactly that value
for the Store in `fn-owner-take`, and the completion gate compares the
durable record with the same function of the same owner). IN FRONT of the
injected block it writes

    Cancel-Lock: sha256:Base64(SHA-256(Base64(K)))
    Cancel-Key: sha256:K1 sha256:K2 ...     (a cancel or Supersedes only)

with `K = HMAC-SHA256(sec, uid || mid)` (RFC 8315 section 4): `sec` the
current epoch's cancel-lock purpose key, `uid` A in lowercase hex (no angle
brackets), `mid` the Message-ID with its angle brackets; the lock hashes the
Base64-encoded key, as RFC 8315 section 2.1 and the example of section 5.2
do (the teeth check that example). A cancel's Cancel-Key carries one key per
kept epoch for its target, current first, so a post locked before a rotation
stays cancellable by its poster (`fn-cl-ring-keys-open-every-retained-lock`).
L above is not the login spelling: A is the principal id the session
authenticated as (`fn-own-sub-account`), and it and the login
(`fn-own-sub-login`, which the Injection-Info parameters read) are recorded
on the submission from the `:submit` effect, i.e. the session at the event
that delivered the article body (books/served.lisp fn-served-login and
fn-served-account), so neither depends on the connection still being open
when the writer takes it, and an AUTHINFO later in the same read never
claims the article.

D25: the lines are injecting-node metadata, outside the authored source.
They stand in front of the block, where the poster never writes, and the
comparison reads an article through `fn-cll-skip`, which sets them aside
(`fn-cll-skip-of-the-generated-lines`,
`fn-cl-served-payload-projects-to-the-injected-octets`). So a same-source
retry under the same Message-ID from another account, or from the same
account after a rotation, answers "already stored": nothing is stored, the
held article's lock is not replaced, and the retrying account gets no key
that opens it. A Cancel-Lock the poster wrote is the poster's input: it stays
in the source (a changed one is a conflict) and the node adds no lock beside
it (RFC 8315 section 2: the field occurs once); one that carries Cancel-Key
gets no node key. A signed article (an FN-Authorship carrier) gets neither:
its signer is its principal, and its signed bytes are never edited. An
unauthenticated POST, a control or BP submission and a transit article get
nothing.

How it is decided. The withdrawal plan decides a cause this node did not
verify by its Cancel-Key entries (a record naming them), and the effect's
`:poster` arm withdraws a target one of whose sha256 Cancel-Lock entries is
Base64(SHA-256(key)) for one of them (RFC 8315 sections 2.1, 2.2, 3). The
decision reads the two articles only, so it is the same on every node that
holds both, in either arrival order, and it replays from the Store after a
restart; relays keep the lines, which are article octets. A cause this node
verified is decided exactly as before, whatever keys it carries. The reply
to the cancel's POST stays 240; the target is withdrawn at the refresh that
publishes the cancel (ARTICLE 430, gone from OVER; HDR :fn-control says
`executed withdrawal <T> poster`; a key that opens nothing says `declined
no-lock-match`).

What it proves and what it cannot. Keystone
`fn-ctl-withdrawal-authority-is-exactly-signer-or-poster`: a cancel's record
withdraws exactly for a verified signer who authored the target, a verified
signer whose grants cover every group of the target, or an unverified cause
whose key opens a lock of the target. By
`fn-cl-account-key-opens-exactly-its-lock` the key the node derives for an
account opens A's lock exactly when that account's lock equals A's, so A's
own key opens it. Not theorems: that the written line parses back as the
entry the decision reads (the teeth check it on served articles), that
another account's key opens nothing (SHA-256 of two HMAC outputs under a key
the forger does not hold would have to collide: 2^128 generic work for a
collision among chosen accounts; 2^256 for a second preimage against a seen
lock), and that distinct labels give unrelated keys (HMAC as a PRF). An
abstract model of the hash would prove nothing about the real one, so there
is no assumption book entry.

Known gaps against RFC 8315: comments (CFWS) inside a Cancel-Lock or
Cancel-Key value are not stripped (section 2's MUST accept); only sha256 is
read (sha512 is skipped, which section 2 permits); a Cancel-Key a poster
supplies on a cancel of an article the node locked gets no node key beside it
(section 3.3). Privacy: the lock is per article and reveals nothing linkable;
the posting-account value is a stable pseudonym of the account (Injection-Info,
lane usenet-headers-3), a disclosure the operator's profile authorizes.

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
`fn-ocfg-read-tls-prefix-is-read-of-consumed-prefix`, under the
configured-owner state invariant, proves that the actual host-call result
equals the checked read of the prefix it consumed (the whole observation's,
since a handshaking connection frames nothing more; a read also yields after
a submission, NNT-044). The host-called path uses `fn-served-step-counted-fast`: its entry
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
| `exposure-connections` | the connection capacity: connections held at once (NNT-043) | `400 too many connections; try again later`, then close (RFC 3977 §5.1.1) | 31 | 31 |
| `exposure-per-address` | connections held from one source address outside `exposure-trusted` | `400 too many connections from this address; try again later` | the total | 8 |
| `exposure-steps-per-second` | served steps one address starts per 1000 ms (one step: one host read, D27 work) | nothing: the connection waits for the next quantum (TCP backpressure) | unlimited | 64 |
| `exposure-first-seconds` | wait for the first command (RFC 3977 §3.1 permits a shorter one) | close, no reply (§3.1) | none | 60 |
| `exposure-idle-seconds` | autologout after that (§3.1: at least three minutes) | close, no reply | none | 600 |
| `exposure-auth-failures` | `481` answers one address may draw per minute | `400 too many authentication failures; closing connection`, and at the next accept `400 too many authentication failures from this address` | unlimited | 10 |
| `exposure-posts-per-minute` | submissions per authenticated principal per minute | nothing: the principal's connections wait for the next minute | unlimited | 60 |
| `anonymous` (policy) | what an unauthenticated session may do: `none` or `open` | under `none`, `480 authentication required` for every reader and posting command (RFC 4643 §2.2) | as `[auth] required` | `none` |

Progress that resets the timers is an answered command or 512 octets
consumed since the last progress (§3.1's "significant amount of data"), so a
client trickling one octet at a time is closed by the first-command or idle
timer. After every served step the observation reads two facts of the
step's reply and nothing else: whether it sent any octet, and how many of its
replies begin `481 ` at a line start. It reads them by one scan of the step's
effects, never by building a copy of the reply, so a step whose reply is
several MiB (the ARTICLE of an article at the operator's bound, an OVER over
a large group) is observed in constant stack; its decisions are those over
the reply octets (SCN-111, PKT-481). `anonymous open` never weakens `[auth]
required`. A row that is absent
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

## Connection capacity and the trusted range (NNT-043)

NNT-043: The reader port holds exactly the operator's connection capacity and refuses the next connection with RFC 3977's 400 by name, and an address in the operator's trusted range is never refused on the per-address rule

The capacity is the `exposure-connections` row, a natural up to the limit
rows' width (the CBOR uint32 maximum); with no row it is 31, the figure a
run held before. No fixed ceiling sits under it: the owner a run installs is
bounded one past that width (`*fn-exp-owner-connection-bound*`,
books/public-exposure-rows.lisp), so the owner's own bound never refuses what
the row admits, and the private connection a live `policy set` stages
through always finds room. Below the capacity a connection is refused only
by the per-address or failed-login rule; at it, every connection reads `400
too many connections; try again later` and is closed
(`fn-exp-open-refuses-exactly-at-the-capacity`, PRF-211). A raised row takes
effect at the next accept.

`exposure-trusted` (a policy row: `none`, or one or more comma-separated
ranges `ADDRESS/BITS`, each address in `[listener] host`'s grammar, BITS at
most 32 or 128, a bare address meaning the whole address) names the sources
exempt from `exposure-per-address`. A node behind a home router whose NAT
loopback presents every LAN reader as the router's address is the case: its
readers would otherwise share one address's allowance. The exemption is from
that rule alone: the capacity, the step budget and the failed-login limit
apply to a trusted source as to any other
(`fn-exp-trusted-address-is-never-refused-by-address`,
`fn-exp-untrusted-address-is-refused-exactly-at-its-limit`). A range is
matched by the kernel's family and the first BITS bits of the source
address; an IPv4 range does not match an IPv4-mapped IPv6 source, which no
admitted listener receives (NNT-041 refuses `::` and the mapped range).

`operator CONFIG health` and `operator CONFIG status` print `exposure
capacity connections=N capacity=C per-address=P trusted=RANGES`: the
connections the owner holds, the capacity in force, the per-address limit
and the trusted word (`none` when there is none).

That the port refuses with 400 past a limit is RFC 3977 §5.1.1; the capacity,
its default and the trusted range are local policy.

## Listener addresses (NNT-041)

NNT-041: The reader listener binds every address `[listener] host` names, IPv4 and IPv6 alike, exactly as ACL2 admitted it, and a refused address names why

`[listener] host` is one address or a comma-separated list. Each is an IPv4
dotted quad, an IPv6 literal in RFC 4291 §2.2's text forms (optionally
bracketed as RFC 3986 §3.2.2's IP-literal; the port is `[listener] port`,
never inside the host) or the name `localhost` (the IPv4 loopback, never
resolved). ACL2 (`fn-native-config-listener-addresses`,
books/native-config.lisp) projects the list to the family and octets the
owner binds, one listener per address on the same port, and one
implicit-TLS listener per address when `tls_port` is set (the TLS listener
itself is unchanged). PRF-197 is the keystone: every admitted list is
nonempty, duplicate-free, and each element is an AF_INET quad other than
`0.0.0.0` or an AF_INET6 address other than `::` and `::ffff:0:0/96`.
A refusal is `listener-address` (not the grammar), `listener-unspecified`
(a wildcard), `listener-mapped` (an IPv4-mapped IPv6 address: write the IPv4
address) or `listener-duplicate`. RFC requirement: the text forms (RFC 4291
§2.2, RFC 3986 §3.2.2). Local policy: the wildcard and mapped refusals, and
one listener per written address rather than a dual-stack wildcard socket
(OpenBSD's AF_INET6 sockets never carry IPv4, so one address per family is
the portable form). The node is public when any listener is
(`fn-exp-address-publicp` per address). A live reconfiguration does not
rebind listeners (PKT-464 (a)); a changed `host` takes effect at restart.
What remains: PKT-577.

## Transit streaming (NNT-045)

NNT-045: A streaming peer's CHECK and TAKETHIS get the answer IHAVE would get from the same admission decision, the pipeline is bounded by the peer's max-inflight, and fn's feed streams to a peer that permits it and falls back to IHAVE on one that does not

A peer connection (a configured peer with an inbound half) accepts MODE
STREAM with 203 (RFC 4644 §2.3; stateless: IHAVE stays available), CHECK
(§2.4) and TAKETHIS (§2.5). The three forms are answered from two ACL2
decisions of books/peer-inbound.lisp: `fn-peer-decide-offer` before the
article (IHAVE's first reply, CHECK's only reply) and
`fn-peer-decide-transfer` after it (IHAVE's second reply, TAKETHIS's only
reply; it has no command formal). PRF-207 states the correspondence on the
codes a peer reads off the socket:

| decision | IHAVE (RFC 3977 §6.3.2) | streaming (RFC 4644) |
| --- | --- | --- |
| offer wanted / held / deferred or refused | 335 / 435 / 436, 435 | CHECK 238 / 438 / 431, 438 |
| transfer durable / refused or held / deferred or uncertain | 235 / 437 / 436 | TAKETHIS 239 / 439 / 436 |

RFC requirements: the codes and the Message-ID echoed by every CHECK and
TAKETHIS reply. fn guarantee: one admission decision for all three forms,
so no article is admitted under one form that another would refuse, and a
duplicate is refused under every form. Local policy: 436 after TAKETHIS
(RFC 4644 §2.5 names 400; innfeed retries 436 and a 400 closes the
connection with every pipelined article behind it), and the pipeline
bound: each 238 is a promise counted on the connection, a TAKETHIS retires
one, and a CHECK with the peer record's inbound max-inflight outstanding
(16 from `peer add`) answers 431, so a peer may pipeline without limit and
fn's work per connection stays bounded (D27; the unbounded part is the
peer's queue, not fn's).

Outbound, fn sends MODE STREAM after the greeting when the peer record
says streaming. 203: the feed offers with CHECK and transfers with
TAKETHIS. 500 or 501 (RFC 3977 §3.2.1: the command or its argument is
unknown, which is what a server without RFC 4644 answers): the same
connection goes on with IHAVE, the owner logs one line
(`fn-fc-fallback-log-line`) and records no stop; the next connection asks
again. Any other answer is a refusal and stops the dial for the owner
process (PRF-130). The form is per connection: `fn-own-feed-connect` sets
it at every connect. RFC 4644 §2.3 prefers CAPABILITIES for discovery; fn
asks MODE STREAM, which every legacy server answers (PKT-599).

## Pipelined articles (NNT-044)

NNT-044: Pipelined articles are each admitted and answered in order: two TAKETHIS or two POST articles in one socket read lose neither, and what is consumed from a stream does not depend on where it was cut

A client may send a command before the previous reply arrives and the
server must neither discard data nor lose synchronisation (RFC 3977 §3.5);
a streaming peer pipelines TAKETHIS with its article (RFC 4644 §2.5), and
innfeed does. One socket read can therefore carry several complete
articles. The served read yields after the octet that completed an
article's submission (books/served-tls-prefix.lisp `fn-served-feed-counted`,
the span fold books/served-span.lisp `fn-scar-feed-span`): the host commits
the article and sends the replies of the read and the article's outcome,
then feeds the unconsumed rest of the read as the next read
(host/native/owner.lisp, the serve loop's retained suffix). Every step's
work is bounded by the read (D27); no octet is dropped or read twice.

RFC requirement: pipelined data is neither lost nor reordered. fn guarantee
(PRF-213): the loop driven to exhaustion is one read of the whole input
(`fn-served-drain-is-step`), so the commands and articles consumed and their
answers are the same wherever the network or a yield cut the stream
(`fn-served-drain-run-is-boundary-independent`); a yield carries at most one
submission and the ones taken are all of them
(`fn-served-drain-takes-every-submission`); the outcome of an article is on
the wire before the reply to any command after it. Before PKT-600 was
repaired the second article of a read was never admitted and never
answered.

## Scope

No moderation, automated control-message execution, private-mail confidentiality,
or unrestricted federation is implied by this profile. Those need explicit
policy and authorization. First client acceptance tests should include an actual
newsreader and an independent transcript client, rather than only fn talking to
itself. Legacy convenience aliases are added only with documented semantics.
