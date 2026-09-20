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
| §5.1 | Initial greeting and posting permission | Fixed 201 on loopback; the greeting does not yet vary with the configured posting permission, so a client learns of POST only by issuing it (440 when refused). Deployment authorization is separate |
| §5.2 | CAPABILITIES with no argument and optional keyword; 101 multiline result | Implemented/tested, including unknown syntactically valid keyword; proved independent of the archive; only VERSION 2 and IMPLEMENTATION emitted; complete bundle audit remains open |
| §5.3 | MODE READER and possible mode/capability transitions | Implemented for the non-mode-switching case §5.3.2 fixes: this reader never advertises MODE-READER, advertises READER, and answers `201 posting prohibited` with no state change (`fn-nntp-mode-response-preserves-session`). The 502-and-close branch is reachable only by flipping `*fn-nntp-advertise-readerp*`; mode switching itself remains unimplemented and unclaimed |
| §5.4 | QUIT, argument errors, 205 then connection close | Pure transcript and real EOF checks exist; proved independent of the archive |
| §6.1.1 | GROUP success, nonexistent group, empty group, counts/low/high, cursor | Implemented/tested; cursor placement on selection is now proved (`fn-nntp-group-selects-the-first-available-article`, `fn-nntp-group-on-empty-group-invalidates-the-cursor`); later group removal/expiry policy remains open |
| §6.1.2 | LISTGROUP current/explicit group, optional range, sparse/empty output, sorted numbers, cursor reset | Implemented with ACL2 transcripts, socket tests, independent client traffic, and unknown-group session preservation; numerical order of the emitted block is proved (`fn-nntp-group-range-numbers-are-ordered`); cursor reset to the group's first article is proved |
| §§6.1.3–6.1.4 | LAST/NEXT, 412/420, boundary 421/422, gaps, successful 223 | Implemented subset with transcript coverage; "moves the cursor only to an existing article, or not at all" is proved (`fn-nntp-next-or-last-moves-only-to-an-available-article`); complete error-precedence audit remains open |
| §§6.2.1–6.2.4 | ARTICLE/HEAD/BODY/STAT by current number, explicit number, Message-ID; 412/420/423/430 | Implemented/tested; Message-ID lookup leaves session unchanged (`fn-nntp-msgid-preserves-session`) and returns allowed number 0; an article the projection cannot render answers 503 for itself only; complete Message-ID grammar and all stale-cursor branches remain open |
| §6.3.1 | POST handshake: 340 then article mode, 240 only after a durable acceptance observation, 441 otherwise, 440 when posting is not configured | Implemented and proved as a composed transition. `fn-nntp-step` answers a POST command line with 340 and one `:begin-article` effect (`books/nntp.lisp`), and the existing keystones `fn-nntp-step-effects-well-formed` and `fn-nntp-step-preserves-consistent-session` cover that branch with their statements unchanged. The served decision is `fn-nntp-post-step` (`books/nntp-post.lisp`), called at `host/reader-host.lisp` `fn-reader-chunk`; `fn-post-step-effects-well-formed`, `fn-post-step-preserves-consistent-session`, `fn-post-submission-is-an-injected-article` and `fn-post-disallowed-posting-does-not-await` are proved of it. The 340/240/441/440 transcript is tested, not proved: `tests/acl2/nntp-post-tests.lisp` and `tests/test_post.py`. Pipelined POST, duplicate-identity wire policy and moderated groups remain open |
| RFC 5537 §3.5 items 2, 4, 5, 6 | Reject a proto-article with Injection-Info, Xref or invalid syntax; check Newsgroups; add Message-ID and Date when absent; never alter the body or an existing Message-ID | Implemented in `books/injection.lisp` as one function of the source octets, one clock observation and a configuration record. Proved: a refusal produces no octets and names a reason; an injected article carries the supplied source as a verbatim suffix (`fn-inj-injected-article-retains-the-source-octets`), so the body and every supplied field are unaltered; a supplied Message-ID is retained exactly and survives a different clock; the injected article is within the configured bound. Tested with ground witnesses and one violating article per clause: `tests/acl2/injection-tests.lisp`. Item 1 (trusted source) and item 3 (Date/Injection-Date freshness window) are open; item 7 (moderated groups) is out of scope for this profile |
| RFC 5536 §3 mandatory fields; §3.2.6, §3.2.8, §3.1.5 | Date, From, Message-ID, Newsgroups, Path, Subject; Injection-Date; Injection-Info; Path | From, Subject and Newsgroups must be supplied; Message-ID, Date, Injection-Date, Injection-Info and Path are generated by ACL2 and by nothing else. Local policy, not an RFC requirement: a proto-article that already carries Path or Injection-Date is refused rather than rewritten, which is what makes the verbatim-suffix theorem true. Open: `fn-af-message-idp` of every generated identifier is witnessed, not proved; and that a different millisecond reading yields a different instant (the two calendar inverse lemmas and the rendering injectivity are proved in `books/injection-invariants.lisp`) |
| §6.3.2 | IHAVE transfer negotiation and acceptance | Deferred; no capability claim |
| §7.1, §7.5 | DATE, clock observations, exact formatting | Implemented over an explicit `fn-clock-observationp` input. With `has-wall` false the reply is `503`, stated, never a fabricated timestamp; the 111 line is always eighteen octets (`fn-nntp-date-octets-length`) and is response text for any reading (`fn-nntp-date-octets-is-response-text`). The calendar conversion is closed-form and is pinned by transcripts, not proved |
| §7.2 | HELP multiline response, unsupported arguments | Implemented/tested; help text must track actual command subset |
| §7.3, §7.5 | NEWGROUPS time forms, GMT/local semantics, group creation metadata | Implemented over persisted `fn-nntp-group-factp` records supplied as an input list. Both year forms with §7.3.2's century rule; a two-digit year with no wall reading is `503`, not a guess. fn's local time zone is UTC, so the optional GMT token changes nothing and is accepted only in third position. Emitted names are renderable with no environment hypothesis (`fn-nntp-facts-since-are-facts`) |
| §7.4 | NEWNEWS filtering/time forms | Deferred; no capability claim |
| §7.6.1 | LIST defaults, keyword variants, syntax/availability errors, no state changes | Default, ACTIVE, NEWSGROUPS and filtered forms implemented; known unmaintained variants distinguish valid-arity 503 from malformed/unknown 501; session preservation proved (`fn-nntp-list-response-preserves-session`) |
| §4, §§7.6.3/7.6.6 | Wildmat grammar/semantics and filtered ACTIVE/NEWSGROUPS | Bounded strict UTF-8 parser and dynamic-programming matcher integrated; RFC, malformed, boundary, socket and independent-client cases pass; general DP/reference equivalence, UTF-8 progress/scalar bounds and parser-output recognition are proved; matcher work and runtime guard graphs have scoped certification; parser work and complete protocol refinement remain open |
| §§8.3–8.4 | OVER by range/Message-ID/current, missing fields, byte/line metadata, OVERVIEW.FMT | Implemented over the proved `fields` view in `books/article.lisp`/`books/article-fields.lisp`. All three forms; §8.3.2's escaping is proved total (`fn-nov-scrub-is-clean`), a missing header yields the empty field (`fn-nov-missing-header-is-empty`), `:bytes` and `:lines` are the exact retained octets (`fn-nov-bytes-is-the-retained-octet-count`, `fn-nov-lines-counts-the-retained-body-lines`), and the eight-field line carries no CR, LF or NUL (`fn-nov-line-is-a-clean-line`). Xref is omitted, so exactly eight fields are emitted and OVERVIEW.FMT lists exactly the seven fixed lines. §§8.1/8.2's overview database as a stored structure is not implemented: each line is projected on demand |
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
| Every emitted reply is a well-formed RFC 3977 §§3.1/3.1.1/3.2 response | proved (`fn-nntp-step-effects-well-formed`), now including DATE, NEWGROUPS, MODE READER, OVER and LIST OVERVIEW.FMT, under the same single hypothesis it had before |
| No overview field carries TAB, CR, LF or NUL, whatever the stored article | proved (`fn-nov-scrub-is-clean`, `fn-nov-header-content-is-clean`, `fn-nov-line-is-a-clean-line`) — unconditional |
| A header the article does not carry gives the empty overview field | proved (`fn-nov-missing-header-is-empty`) |
| `:bytes` and `:lines` are the exact retained octets and retained body lines | proved (`fn-nov-bytes-is-the-retained-octet-count`, `fn-nov-lines-counts-the-retained-body-lines`) |
| DATE, NEWGROUPS, MODE READER, OVER and LIST OVERVIEW.FMT change no session state | proved (`fn-nntp-date-response-preserves-session` and siblings) |
| The DATE calendar conversion is the proleptic Gregorian civil date of the reading | tested at epoch, leap-day and the profile's own boundaries; **open** as a theorem |
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

## The READER clause matrix

RFC 3977 §3.3.2 makes a capability label a promise that the whole bundle is
available. **Appendix B is the authority on which commands a label covers**,
and it is narrower than this document previously claimed: READER covers exactly
ARTICLE, BODY, DATE, GROUP, LAST, LISTGROUP, NEWGROUPS and NEXT. HDR, NEWNEWS,
OVER and POST each indicate their *own* capability and are not part of READER;
LIST ACTIVE and LIST NEWSGROUPS belong to LIST, and LIST OVERVIEW.FMT to OVER.
The earlier text listing HDR, NEWNEWS, OVER and POST as READER requirements was
wrong, and it is what kept the label unadvertised after the commands existed.

Every clause below is marked **proved** (with the theorem that carries it),
**tested** (with where the expectation lives), or **open**. "Tested" means an
independently written expected transcript, not a recorded run.

Verification state (2026-09-20, branch `w3/reader-profile` merged with dev
`b7f106b`): every book the rows cite certifies; the rows stand as written,
none moved. Counts: eleven rows; four **proved** plus one **proved by
construction**; six **tested** (`tests/acl2/nntp-reader-profile-tests`,
`tests/acl2/nntp-tests`, `tests/test_reader.py`); one **stated local policy**;
one **open** (the §6.1.1.2 estimate-bounds theorem). On the served path the
environment carries no group-creation facts, so NEWGROUPS there is the empty
block; the tested NEWGROUPS rows are evidence at the dispatcher, not over a
socket.

| RFC clause | Requirement | Status |
| --- | --- | --- |
| §6.1.1.2 GROUP | 211 count/low/high, 411 for an unknown group, cursor to the first available article | proved (`fn-nntp-group-selects-the-first-available-article`, `fn-nntp-group-on-empty-group-invalidates-the-cursor`, `fn-nntp-unknown-group-keeps-the-session`) |
| §6.1.1.2 GROUP | The 211 count is an estimate satisfying the bounds relative to low and high | tested (`nntp-tests.lisp`); fn's count is exact, which satisfies the bound, but no theorem says so — **open** as a theorem |
| §6.1.2.2 LISTGROUP | Group/range forms, sparse and empty output, numerical order, cursor reset | proved (`fn-nntp-group-range-numbers-are-ordered`, `fn-nntp-listgroup-selects-the-first-available-article`) |
| §§6.1.3/6.1.4 LAST/NEXT | 412/420/421/422, move only to an existing article | proved (`fn-nntp-next-or-last-moves-only-to-an-available-article`); code choice per situation tested |
| §§6.2.1/6.2.3 ARTICLE/BODY | Current, number and message-id forms; 412/420/423/430 precedence | tested (`nntp-reader-profile-tests.lisp`, `nntp-tests.lisp`); message-id form leaves the session unchanged is proved (`fn-nntp-msgid-preserves-session`) |
| §7.1 DATE | 111 yyyymmddhhmmss from the server clock | tested (`nntp-reader-profile-tests.lisp`); the line's length and grammar are proved (`fn-nntp-date-octets-length`, `fn-nntp-date-octets-is-a-status-line`); the civil conversion itself is **tested, not proved** |
| §7.1 DATE | No clock reading available | tested: `503`, stated. RFC 3977 lists only 111 for DATE, so §3.2.1's 503 is a local reading of "does not hold the required information" — a **stated deviation**, not a claim of conformance for that branch |
| §7.3.2 NEWGROUPS | Eight-digit and six-digit date forms with the century rule; hhmmss with leap second; optional GMT | tested (`nntp-reader-profile-tests.lisp`, both forms, every range boundary, both century directions) |
| §7.3.2 NEWGROUPS | Results in LIST ACTIVE format; empty list valid; groups may be omitted | tested (the transcript compares the NEWGROUPS block with the LIST ACTIVE block) |
| §7.3.2 NEWGROUPS | Server's local time zone | fn's local zone **is** UTC and the protocol cannot convey another; stated local policy |
| §3.2.1/§3.3.2 | Advertise a label only when the whole bundle is available | proved by construction: one constant, `*fn-nntp-advertise-readerp*`, decides both the capability list and MODE READER, so the two cannot disagree |

No READER clause is open, so **READER is advertised**. The one item this table
leaves open, the §6.1.1.2 count *theorem*, is an assurance gap about a value the
transcripts pin exactly; it is not a missing command or an unimplemented branch.
OVER is advertised as `OVER MSGID` because the message-id form is implemented;
§8.3.2 requires the MSGID argument exactly when that form works. LIST is
advertised with the three variants that answer with data. POST, IHAVE, NEWNEWS,
HDR and MODE-READER stay unadvertised; this reader is not mode-switching.

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
