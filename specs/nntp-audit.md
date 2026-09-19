# NNTP implementation checklist

This is a branch-level work list for the experimental reader, not a declaration
of RFC conformance. The source baseline is the supplied [RFC 3977](../rfc3977.txt).
The [NNTP contract](nntp.md) describes the intended usable profile. Capability
advertisement remains VERSION/IMPLEMENTATION until complete bundles have their
own evidence; a command name alone does not close its row.

The latest frozen [reader/storage batch](../tests/evidence/2026-09-18-wildmat-storage.md)
covers LISTGROUP, filtered LIST variants, command limits, socket tests, and an
independent stored-reader probe. Current assertion tests live in
[nntp-tests.lisp](../tests/acl2/nntp-tests.lisp); socket tests and independent client
probes supply different evidence from those pure transcripts.

| RFC clause | Branches to account for | Current scope / remaining work |
| --- | --- | --- |
| §§3.1–3.1.1, §9 | CRLF, command syntax/limits, case, whitespace, multiline termination and dot transformation | Wire/command books and socket partitions exercise the core; the emitted response grammar is now re-parsed and proved (see "Effect typing" below); complete accepted grammar, boundary precedence, and protocol-wide refinement remain open |
| §3.2 | Three-digit status, SP separation, generic 500/501/503 assignment | Proved of every emitted reply through `fn-nntp-replyp`; the mapping of each situation to its code is tested, not proved |
| §6, §9.2 | Local article numbers, watermarks, valid numeric grammar | Node allocation and numeric regression cases exist; number values are 1 through 2,147,483,647 with at most 16 digits, including leading zeros, as §6 requires; a committed article numbered outside that range is not available to the reader |
| §§3.3–3.5 | Pipelining, state visibility, capabilities, mode changes | Sequential owner and event-yield parsing exist; no concurrent live posting, authentication transition, or mode-switch implementation |
| §5.1 | Initial greeting and posting permission | Fixed 201 on loopback, no POST advertised; deployment authorization is separate |
| §5.2 | CAPABILITIES with no argument and optional keyword; 101 multiline result | Implemented/tested, including unknown syntactically valid keyword; proved independent of the archive; only VERSION 2 and IMPLEMENTATION emitted; complete bundle audit remains open |
| §5.3 | MODE READER and possible mode/capability transitions | Unimplemented; not an advertised mode-switching server |
| §5.4 | QUIT, argument errors, 205 then connection close | Pure transcript and real EOF checks exist; proved independent of the archive |
| §6.1.1 | GROUP success, nonexistent group, empty group, counts/low/high, cursor | Implemented/tested; cursor placement on selection is now proved (`fn-nntp-group-selects-the-first-available-article`, `fn-nntp-group-on-empty-group-invalidates-the-cursor`); later group removal/expiry policy remains open |
| §6.1.2 | LISTGROUP current/explicit group, optional range, sparse/empty output, sorted numbers, cursor reset | Implemented with ACL2 transcripts, socket tests, independent client traffic, and unknown-group session preservation; numerical order of the emitted block is proved (`fn-nntp-group-range-numbers-are-ordered`); cursor reset to the group's first article is proved |
| §§6.1.3–6.1.4 | LAST/NEXT, 412/420, boundary 421/422, gaps, successful 223 | Implemented subset with transcript coverage; "moves the cursor only to an existing article, or not at all" is proved (`fn-nntp-next-or-last-moves-only-to-an-available-article`); complete error-precedence audit remains open |
| §§6.2.1–6.2.4 | ARTICLE/HEAD/BODY/STAT by current number, explicit number, Message-ID; 412/420/423/430 | Implemented/tested; Message-ID lookup leaves session unchanged (`fn-nntp-msgid-preserves-session`) and returns allowed number 0; an article the projection cannot render answers 503 for itself only; complete Message-ID grammar and all stale-cursor branches remain open |
| §6.3.1; RFC 5536/5537 | POST handshake, proto-article validation/injection, durable result, retry/conflict behavior | Unimplemented on the network. CLI storage is not article injection and does not imply POST support |
| §6.3.2 | IHAVE transfer negotiation and acceptance | Deferred; no capability claim |
| §7.1, §7.5 | DATE, clock observations, exact formatting | Unimplemented. A future explicit host clock observation supplies data; wall-clock ordering must not replace immutable identity |
| §7.2 | HELP multiline response, unsupported arguments | Implemented/tested; help text must track actual command subset |
| §7.3, §7.5 | NEWGROUPS time forms, GMT/local semantics, group creation metadata | Unimplemented; requires persisted group creation/configuration facts, not invented dates |
| §7.4 | NEWNEWS filtering/time forms | Deferred; no capability claim |
| §7.6.1 | LIST defaults, keyword variants, syntax/availability errors, no state changes | Default, ACTIVE, NEWSGROUPS and filtered forms implemented; known unmaintained variants distinguish valid-arity 503 from malformed/unknown 501; session preservation proved (`fn-nntp-list-response-preserves-session`) |
| §4, §§7.6.3/7.6.6 | Wildmat grammar/semantics and filtered ACTIVE/NEWSGROUPS | Bounded strict UTF-8 parser and dynamic-programming matcher integrated; RFC, malformed, boundary, socket and independent-client cases pass; general DP/reference equivalence, UTF-8 progress/scalar bounds and parser-output recognition are proved; matcher work and runtime guard graphs have scoped certification; parser work and complete protocol refinement remain open |
| §§8.1–8.4 | OVER by range/Message-ID/current, missing fields, byte/line metadata, OVERVIEW.FMT | Unimplemented; depends on the parsed article view and exact projection/metadata contract |
| §§8.5–8.6 | HDR and LIST HEADERS | Deferred; no capability claim |

## The served path carries its projection verdict

Defect D3 of [the independent review](../planning/review-2026-09-18-independent.md)
was an availability bug: `fn-nntp-step` re-ran the whole-archive recognizer
`fn-nntp-projectionp` on every command, that recognizer demanded every committed
article be renderable, and `fn-articlep` admits articles that are not. One such
article answered 503 to every command, CAPABILITIES and QUIT included, and every
command cost work proportional to the whole store.

The reader now separates three things.

**Configuration, decided once.** `fn-nntp-projectionp` is now a configuration
recognizer: the acceptance state recognizer, group names that a response can
render (nonempty printable US-ASCII, at most 460 octets), watermarks inside RFC
3977 §6's range, and an article capacity of at most 2,147,483,647.
`fn-nntp-open-session` evaluates it once, when the reader opens a connection
(`host/reader-host.lisp` `fn-reader-reset`), and stores the verdict as the
session's fourth field. `fn-nntp-step-preserves-carried-projection` states that
every step returns a session with the same verdict, and
`fn-nntp-finite-trace-preserves-carried-projection` lifts that to finite traces.
No command re-runs `fn-nntp-projectionp`.

**Commands that do not read the archive.** `fn-nntp-command` dispatches
CAPABILITIES, HELP, QUIT, an unrecognized keyword, and a syntax error through
`fn-nntp-session-command`, which takes no archive argument.
`fn-nntp-archive-free-step-ignores-the-archive` states that for any command line
whose keyword is not one of the nine archive commands, the step's result is the
same for every archive. No committed article and no configuration can deny those
commands. When the carried verdict is false, only the nine archive commands
answer `503 archive projection unavailable`, which is RFC 3977 §3.2.1's code for
a recognized command whose required information the server does not hold.

**Articles that degrade only themselves.** Per-article checks are split by what
a response actually needs. `fn-nntp-article-idp` is the bounded identifier check
(a string of at most 250 octets forming a valid `message-id`); STAT, NEXT and
LAST need only this. `fn-nntp-article-framedp` is the payload check (CRLF-framed
throughout, carrying no NUL, and containing a header/body separator); only
ARTICLE, HEAD and BODY need it.

| Situation | Response | Effect on the group |
| --- | --- | --- |
| Identifier not renderable | `503 stored article identifier unavailable` to ARTICLE/HEAD/BODY/STAT naming its number | Excluded from the count, the water marks, LISTGROUP, and NEXT/LAST |
| Identifier fine, payload not framed | `503 stored article framing unavailable` to ARTICLE/HEAD/BODY; STAT, NEXT and LAST succeed | Included; the number is real and STAT answers for it |
| Number outside RFC 3977 §6's range | as "identifier not renderable" | Excluded |

`fn-nntp-effects-article-response` is now unconditional in the article: the
response constructor gates on both checks itself, so no caller has to discharge
a hypothesis about stored bytes.

## Per-command cost

The costs below are of the executed graph, in the committed article count `A`,
the configured group count `G`, the per-article membership count `m` (bounded by
`G`), the command line length `L` (at most 510 octets), and `k`, the number of
articles inside the range the command's own argument names.

| Command | Work |
| --- | --- |
| CAPABILITIES, HELP, QUIT, 500, 501 | `O(L)`. No archive traversal at all. |
| GROUP, NEXT, LAST | `O(A · (m + 251))` — one pass over the articles with bounded per-article work — plus `O(L)`. Previously `O(A²)` from an insertion sort, on top of a whole-archive revalidation. |
| LISTGROUP *group* [*range*] | `O(A · (m + 251))` for the pass, plus `O(k²)` to order the `k` numbers the requested range selects, plus `O(k)` to render them. The sort is charged to the command's own range, not to the archive. |
| ARTICLE / HEAD / BODY / STAT *n* | `O(A · m)` to locate, plus, for ARTICLE/HEAD/BODY only, `O(P)` in that one article's payload length `P`. |
| ARTICLE / HEAD / BODY / STAT *message-id* | `O(A)` identifier comparisons, plus `O(P)` for that article. |
| LIST, LIST ACTIVE [*wildmat*] | `O(G · A · (m + 251))`: one pass over the articles for each listed group. LIST NEWSGROUPS does not touch the articles. |

What was removed: the per-command `fn-nntp-projectionp` call, which re-ran
`fn-statep` (whose `fn-article-listp` conjunct is quadratic in `A` through
Message-ID non-membership) and re-scanned every committed payload; and the
insertion sort in the former `fn-nntp-group-numbers`, which every group-scoped
command paid in full. What remains quadratic is the ordering of a LISTGROUP
range, `O(k²)` in the size of that range's own output.

## Effect typing

`fn-nntp-effectp` no longer accepts `(:reply (65))`. A reply's octets are
re-parsed as a response:

- `fn-nntp-status-prefixp`: three decimal digits followed by SP or by the
  terminating CRLF (RFC 3977 §3.2).
- `fn-nntp-initial-line-tail`: the initial line ends at a CRLF pair, carries no
  NUL, LF or CR, and is at most 512 octets counting that CRLF (§3.1).
- `fn-nntp-block-scan`: a multi-line reply's block is a sequence of lines each
  ending CRLF and carrying none of NUL, LF or CR; a line whose first octet is
  the termination octet is dot-stuffed with a second one; the block ends with
  `.` CRLF and nothing follows it (§3.1.1).

`fn-nntp-command-effects-well-formed` and `fn-nntp-step-effects-well-formed` are
re-proved against that definition, each under the single hypothesis
`fn-nntp-session-consistentp`, which `fn-nntp-open-session` establishes and every
step preserves.

**The 549-octet case.** The review's LISTGROUP 211 line with a 497-octet group
name was 549 octets. The fixed part of that line is 52 octets: `211 `, three
decimal fields of at most ten octets each with their three separating spaces,
` list follows`, and CRLF. `fn-nntp-safe-group-namep` therefore bounds a
projected group name at 460 octets, and a configuration carrying a longer name
is refused before the reader opens. The ten-octet field bound is structural, not
assumed: every rendered number passes through `fn-nntp-decimal-field`, which is
by definition a nonempty run of at most ten decimal digits.
`fn-nntp-group-initial-fits`, `fn-nntp-listgroup-initial-fits` and
`fn-nntp-retrieval-initial-fits` give the 512-octet bound unconditionally
because of that guard, and none of them needs an arithmetic side condition.
**Open**: that the guard never actually fires for a number in RFC 3977 §6's
range is *not* proved. The event that said so,
`fn-nntp-decimal-field-is-exact-in-range`, needed `arithmetic-5/top`, which
this ACL2 build refuses to include, so it was removed rather than left
uncertified. The boundary values 0, 1 and 2147483647 are pinned by
`assert-event` only.

## Session invariant

`fn-nntp-session-consistentp` previously admitted a NIL cursor unconditionally,
so a dispatcher that cleared the cursor after every command satisfied it. It now
also requires:

- the carried projection verdict implies the archive is projectable;
- no selected group implies an invalid cursor;
- a selected group is a configured group;
- a selected group with at least one available article implies the cursor is
  valid, that is, it names an article available at that number in that group
  (RFC 3977 §§6.1.1.2 and 6.1.2.2);
- a selected group with no available article implies an invalid cursor.

`fn-nntp-step-preserves-consistent-session` and
`fn-nntp-finite-trace-preserves-consistent-session` carry it over the real step
and over arbitrary finite event lists, including malformed events and events
after QUIT. `fn-nntp-opened-finite-trace-is-consistent` roots that at
`fn-nntp-open-session`.

## What is proved, what is tested, what is open

| Claim | Status |
| --- | --- |
| Every step keeps the projection verdict it opened with | proved (`fn-nntp-step-preserves-carried-projection`) |
| No archive can change CAPABILITIES, HELP, QUIT, 500 or 501 | proved (`fn-nntp-archive-free-step-ignores-the-archive`) |
| Every emitted reply is a well-formed RFC 3977 §§3.1/3.1.1/3.2 response | proved (`fn-nntp-step-effects-well-formed`) |
| Every generated initial line is at most 512 octets including CRLF | proved (`fn-nntp-group-initial-fits`, `fn-nntp-listgroup-initial-fits`, `fn-nntp-retrieval-initial-fits`) |
| Selection sets the cursor to the group's first available article, or invalidates it for an empty group | proved (`fn-nntp-group-selects-the-first-available-article`, `fn-nntp-listgroup-selects-the-first-available-article`, `fn-nntp-group-on-empty-group-invalidates-the-cursor`) |
| NEXT/LAST move the cursor only to an available article, or not at all | proved (`fn-nntp-next-or-last-moves-only-to-an-available-article`) |
| Retrieval by Message-ID leaves the session unchanged | proved (`fn-nntp-msgid-preserves-session`) |
| A LISTGROUP block is in numerical order | proved (`fn-nntp-group-range-numbers-are-ordered`) |
| 412 precedes 420/423; 430 for an absent Message-ID; 501 for leading/trailing white space and for an over-long line | tested (expected transcripts in `tests/acl2/nntp-tests.lisp` and socket partitions) |
| The specific status code chosen for each situation | tested, not proved |
| The 211 count is an estimate satisfying §6.1.1.2's bounds relative to low and high | open |
| Cursor behaviour once articles can be removed or expire | open; the relation is stated against an immutable archive |
| The per-command costs above | measured by reading the executed graph, not certified by a cost theorem |

## Why READER is not advertised

RFC 3977 §3.3.2 makes a capability label a promise that the whole bundle is
available. The READER bundle requires ARTICLE, BODY, DATE, GROUP, HDR, HEAD,
HELP, LAST, LIST, LISTGROUP, NEWGROUPS, NEWNEWS, NEXT, OVER, POST and STAT with
their full argument forms. This profile has no DATE (no clock observation
exists), no NEWGROUPS (no persisted group-creation facts exist), no NEWNEWS, no
OVER or HDR (no overview projection exists) and no POST. Advertising READER
would be a false promise that clients are entitled to act on, and §3.2's rule
that a conforming client only sees listed responses would be broken the first
time such a client issued DATE. The capability list therefore stays VERSION 2
and IMPLEMENTATION until each missing command has its own evidence.

## Implemented LISTGROUP contract

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
obtained from a global Message-ID order or another site's numbers. Tests include
gaps, groups whose allocated watermarks exceed retained membership, and articles
excluded because their stored identifier cannot be rendered.

## Evidence needed before expanding advertisement

For each branch, retain the supporting RFC clause, an independently specified
expected transcript, state effects, and integration coverage where transport or
persistence matters. Complete the missing READER commands and required listing
forms before advertising READER. POST additionally needs the injection/provenance
profile and actual durable transaction path; a successful storage CLI command
does not establish a successful POST implementation. OVER requires exact header
and metadata behavior, not only tab-separated formatting.

## Session preservation evidence

[`books/nntp-invariants.lisp`](../books/nntp-invariants.lisp) proves the implemented
command and wire-event dispatchers preserve the session relation described above
relative to an immutable valid archive projection. An actual step fold preserves
it over arbitrary finite event lists, including malformed events and events after
QUIT. This is a state/cursor and availability theorem, not a proof of every
response byte's RFC meaning or of a future mutable-archive policy. The broad
conformance rows above therefore remain separately audited.

The companion [`nntp-effects`](../books/nntp-effects.lisp) proves
`fn-nntp-command-effects-well-formed` for every dispatcher branch and
`fn-nntp-step-effects-well-formed` for any consistent session and arbitrary wire
event, against the re-parsing response grammar above. Closed sessions emit no
effects. These are response-grammar theorems, separate from byte-for-byte RFC
semantics and from runtime work bounds.

Teeth for each keystone live in [nntp-tests.lisp](../tests/acl2/nntp-tests.lisp):
a reachable non-degenerate witness, and a concrete counterexample or a
`must-fail` for each hypothesis.
