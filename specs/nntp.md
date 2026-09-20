# NNTP projection and article acceptance

Status: the selected reader profile is implemented and advertised; POST is not.
`books/nntp.lisp` now advertises `VERSION 2`, `READER`, `OVER MSGID` and
`LIST ACTIVE NEWSGROUPS OVERVIEW.FMT`. Every clause RFC 3977 appendix B assigns
to those labels is marked proved or tested in
[the clause matrix](nntp-audit.md#the-reader-clause-matrix); none is open.
POST, IHAVE, NEWNEWS, HDR and MODE-READER remain unadvertised. D05's checklist
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
| Legacy spellings (RFC 2980) | XOVER (§2.8), XHDR (§2.6), LIST ACTIVE.TIMES (§2.1.3) |
| Later optional capabilities | IHAVE, NEWNEWS, XPAT, streaming, authentication/compression extensions as selected |

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
and fn does not fabricate one. `LIST NEWSGROUPS` renders an empty
description for the same reason -- the group table has no description field
until R5 adds one.

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

The posting connection keeps the version it pinned at open: its own post is
visible to connections opened after the completion and to itself only once
the control channel advances it (`fn-own-pinned-prefix-survives-any-trace`).
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

The greeting is still a fixed 201 and does not vary with the configured
posting permission. POST is not advertised in CAPABILITIES. There is no
freshness window on a supplied `Date` (§3.5 item 3), no trusted-source check
(item 1) and no moderated-group handling (item 7). RFC 3977 section 3.5
forbids pipelining after POST's article until its response; a client that
does so anyway gets the pipelined replies before the 240/441, because the
read is consumed whole and the outcome is a later input.

## Scope

No moderation, automated control-message execution, private-mail confidentiality,
or unrestricted federation is implied by this profile. Those need explicit
policy and authorization. First client acceptance tests should include an actual
newsreader and an independent transcript client, rather than only fn talking to
itself. Legacy convenience aliases are added only with documented semantics.
