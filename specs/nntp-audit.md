# NNTP implementation checklist

This is a branch-level work list for the experimental reader, not a declaration
of RFC conformance. The source baseline is the supplied [RFC 3977](../rfc3977.txt).
The [NNTP contract](nntp.md) describes the intended usable profile. Capability
advertisement remains VERSION/IMPLEMENTATION until complete bundles have their
own evidence; a command name alone does not close its row.

The latest frozen [storage batch](../tests/evidence/2026-09-18-storage.md) covers
the reader subset before LISTGROUP. Current assertion tests live in
[nntp-tests.lisp](../tests/acl2/nntp-tests.lisp); socket tests and independent client
probes supply different evidence from those pure transcripts.

| RFC clause | Branches to account for | Current scope / remaining work |
| --- | --- | --- |
| §§3.1–3.1.1, §9 | CRLF, command syntax/limits, case, whitespace, multiline termination and dot transformation | Wire/command books and socket partitions exercise the core; complete accepted grammar, boundary precedence, work bounds, and protocol-wide refinement remain open |
| §6, §9.2 | Local article numbers, watermarks, valid numeric grammar | Node allocation and numeric regression cases exist; number values are 1 through 2,147,483,647 with at most 16 digits, including leading zeros, as §6 requires |
| §§3.3–3.5 | Pipelining, state visibility, capabilities, mode changes | Sequential owner and event-yield parsing exist; no concurrent live posting, authentication transition, or mode-switch implementation |
| §5.1 | Initial greeting and posting permission | Fixed 201 on loopback, no POST advertised; deployment authorization is separate |
| §5.2 | CAPABILITIES with no argument and optional keyword; 101 multiline result | Implemented/tested, including unknown syntactically valid keyword; only VERSION 2 and IMPLEMENTATION emitted; complete bundle audit remains open |
| §5.3 | MODE READER and possible mode/capability transitions | Unimplemented; not an advertised mode-switching server |
| §5.4 | QUIT, argument errors, 205 then connection close | Pure transcript and real EOF checks exist |
| §6.1.1 | GROUP success, nonexistent group, empty group, counts/low/high, cursor | Implemented/tested; general session refinement and later group removal/expiry policy remain open |
| §6.1.2 | LISTGROUP current/explicit group, optional range, sparse/empty output, sorted numbers, cursor reset | Active implementation batch; details below are the contract, not completed evidence |
| §§6.1.3–6.1.4 | LAST/NEXT, 412/420, boundary 421/422, gaps, successful 223 | Implemented subset with transcript coverage; later cursor invalidation and complete error-precedence audit remain open |
| §§6.2.1–6.2.4 | ARTICLE/HEAD/BODY/STAT by current number, explicit number, Message-ID; 412/420/423/430 | Implemented/tested; Message-ID lookup leaves session unchanged and returns allowed number 0; complete Message-ID grammar and all stale-cursor branches remain open |
| §6.3.1; RFC 5536/5537 | POST handshake, proto-article validation/injection, durable result, retry/conflict behavior | Unimplemented on the network. CLI storage is not article injection and does not imply POST support |
| §6.3.2 | IHAVE transfer negotiation and acceptance | Deferred; no capability claim |
| §7.1, §7.5 | DATE, clock observations, exact formatting | Unimplemented. A future explicit host clock observation supplies data; wall-clock ordering must not replace immutable identity |
| §7.2 | HELP multiline response, unsupported arguments | Implemented/tested; help text must track actual command subset |
| §7.3, §7.5 | NEWGROUPS time forms, GMT/local semantics, group creation metadata | Unimplemented; requires persisted group creation/configuration facts, not invented dates |
| §7.4 | NEWNEWS filtering/time forms | Deferred; no capability claim |
| §7.6.1 | LIST defaults, keyword variants, syntax/availability errors, no state changes | Default, ACTIVE, and NEWSGROUPS implemented without optional wildmat; recognized-but-unmaintained variants and complete 501/503 distinction remain to audit |
| §4, §§7.6.3/7.6.6 | Wildmat grammar/semantics and filtered ACTIVE/NEWSGROUPS | Unimplemented; requires explicit bounded matching work, not uncontrolled backtracking |
| §§8.1–8.4 | OVER by range/Message-ID/current, missing fields, byte/line metadata, OVERVIEW.FMT | Unimplemented; depends on the parsed article view and exact projection/metadata contract |
| §§8.5–8.6 | HDR and LIST HEADERS | Deferred; no capability claim |

## LISTGROUP contract for the active batch

RFC 3977 §6.1.2.2 makes LISTGROUP select the group as GROUP does, then return the
available numbers as a numerically ordered multiline block. The initial 211
count/low/high describe the group, even when the requested range filters out
every returned number. A successful selection resets the current article to the
first available article in the group, even when that article is outside the
range. An empty group has an invalid current article.

The grammar is `LISTGROUP [group [range]]`: a single token is a group argument,
not a range on the current group. The range forms are `n`, `n-`, and `n-m`, with
inclusive bounds; `m < n` denotes an empty range, not a syntax error. Omitted
range is equivalent to `1-`. No group argument uses the current group; if that
selection is invalid, return 412. An explicitly unavailable group returns 411.
Failure preserves the prior session. Invalid argument grammar uses the generic
syntax handling from §§3.2/9; concrete error-precedence cases belong in tests.

Article number lists are rebuilt from committed local memberships. They are not
obtained from a global Message-ID order or another site's numbers. Tests should
include gaps and groups whose allocated watermarks exceed retained membership.

## Evidence needed before expanding advertisement

For each branch, retain the supporting RFC clause, an independently specified
expected transcript, state effects, and integration coverage where transport or
persistence matters. Complete the missing READER commands and required listing
forms before advertising READER. POST additionally needs the injection/provenance
profile and actual durable transaction path; a successful storage CLI command
does not establish a successful POST implementation. OVER requires exact header
and metadata behavior, not only tab-separated formatting.
