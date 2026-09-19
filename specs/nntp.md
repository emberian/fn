# NNTP projection and article acceptance

Status: the first usable profile below is still proposed. An experimental reader
subset now exists in `books/nntp.lisp`; it advertises VERSION/IMPLEMENTATION only,
without READER or POST. Resolve D05 and finish the clause-level audit before
claiming the complete profile. See [implementation status](../docs/implementation.md).

## Planned surface

| Bundle/function | Planned commands |
| --- | --- |
| Mandatory | CAPABILITIES, HEAD, HELP, QUIT, STAT |
| READER | ARTICLE, BODY, DATE, GROUP, LAST, LISTGROUP, NEWGROUPS, NEXT |
| Required reader listings | LIST / LIST ACTIVE, LIST NEWSGROUPS |
| Posting | POST |
| Overview | OVER, LIST OVERVIEW.FMT |
| Compatibility behavior | MODE READER, according to the actual advertised mode |
| Later optional capabilities | IHAVE, NEWNEWS, HDR, streaming, authentication/compression extensions as selected |

NNT-001: advertise only complete supported bundles and variants. Build a checklist
of every applicable RFC branch, argument form, response, and state effect.
Ranges, wildmat, dates, optional arguments, error precedence, and pipelining are
part of that work. A command name appearing in this table is not conformance.
Use RFC 3977 §§3.4 and 3.4.2, command sections, and Appendix B as the baseline.
The [implementation checklist](nntp-audit.md) tracks branches and remaining work;
it is not a completed conformance audit.

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
3. The host carries that submission through the same durable acceptance path
   the command-line `post` uses — `fn-node-prepare`, publication, then
   `fn-node-complete` — and calls `fn-nntp-post-outcome` with what it
   observed. `:durable` is `240 article received OK`. `:refused` and
   `:uncertain` are two distinct `441` lines, and stay distinct out to the
   wire: an uncertain outcome never becomes a 240 and never becomes the
   refusal line, because a client must not repost on it.

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
(item 1) and no moderated-group handling (item 7). The reader process that
serves POST today holds the writer path itself; the mutable-owner lane
replaces that.

## Scope

No moderation, automated control-message execution, private-mail confidentiality,
or unrestricted federation is implied by this profile. Those need explicit
policy and authorization. First client acceptance tests should include an actual
newsreader and an independent transcript client, rather than only fn talking to
itself. Legacy convenience aliases are added only with documented semantics.
