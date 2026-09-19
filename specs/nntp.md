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
| Later optional capabilities | IHAVE, NEWNEWS, HDR, streaming, authentication/compression extensions as selected |

NNT-001: advertise only complete supported bundles and variants. Build a checklist
of every applicable RFC branch, argument form, response, and state effect.
Ranges, wildmat, dates, optional arguments, error precedence, and pipelining are
part of that work. A command name appearing in this table is not conformance.
Use RFC 3977 §§3.4 and 3.4.2, command sections, and Appendix B as the baseline.
The [implementation checklist](nntp-audit.md) tracks branches and remaining work;
it is not a completed conformance audit.

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

## Scope

No moderation, automated control-message execution, private-mail confidentiality,
or unrestricted federation is implied by this profile. Those need explicit
policy and authorization. First client acceptance tests should include an actual
newsreader and an independent transcript client, rather than only fn talking to
itself. Legacy convenience aliases are added only with documented semantics.
