# NNTP implementation checklist

This is a branch-level work list for the experimental reader, not a declaration
of RFC conformance. The source baseline is the supplied [RFC 3977](../rfc3977.txt).
The [NNTP contract](nntp.md) describes the intended usable profile. A command name alone does not close its row: a label is advertised
only when the whole bundle behind it is implemented, and every label this
reader emits has a row below.

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
| §§3.3–3.5 | Pipelining, state visibility, capabilities, mode changes | **Pipelining proved**, in two parts. Byte boundaries: `fn-served-step-partition-independence` and `fn-served-reply-stream-is-partition-independent` say the connection and the reply octets after a run depend only on the concatenated input, so the network may cut the stream anywhere. The command boundary POST introduces: `fn-wire-article-event-resumes-command-mode` says the byte that completes an article leaves the wire in command mode in the same call, and `fn-served-pipelined-read-is-the-sequential-reply` and `fn-served-pipelined-read-submission-is-the-post-block-submission` (both `books/served.lisp`) say a read carrying POST, the body, the terminator and a following command produces exactly the two reads' replies and the POST block's own submission. Teeth: a transcript in `tests/acl2/served-tests.lisp` where the trailing GROUP earns its 211 inside the POST read and the session carries the selected group afterwards. The authentication transition is RFC 4643 below; mode switching stays unimplemented |
| §5.1 | Initial greeting and posting permission | Implemented: `fn-served-open` (`books/served.lisp`) emits `fn-served-greeting` of the connection's pinned configuration AND of the session it just opened, which is 200 when `fn-inj-config-allow` is set and the connection may post as it stands, 201 when it may not. **Corrected 2026-09-21**: it read `fn-inj-config-allow` alone, so a connection under `[auth] required = true` greeted 200 and answered POST 480 — §5.1.2's MUST says 201 there, and §5.1.2's own note says the distinction has proved insufficient for exactly this case. The same value decides the POST capability label (§5.2.2), MODE READER (§5.3.2) and what `fn-nntp-post-step` does with a POST command, so the four cannot disagree; `fn-served-open-greets-200-exactly-when-the-connection-may-post` and `fn-served-open-greeting-agrees-with-the-post-label` say so (PRF-039). Both spellings are witnessed in `tests/acl2/served-tests.lisp`. Before this lane the reader greeting was a fixed 201 even where posting was allowed; the peer greeting already varied. Deployment authorization is separate. **Open**: 400 (service temporarily unavailable) and 502 (permanently unavailable) at connection time are not emitted; the owner refuses a connection by closing it, which §5.1.1 does not describe |
| §5.2 | CAPABILITIES with no argument and optional keyword; 101 multiline result | Implemented/tested, including an unknown but syntactically valid keyword; proved independent of the archive (`fn-nntp-archive-free-step-ignores-the-archive`). Three functions build the block and each owns one connection kind: `fn-nntp-capability-lines` the reader's own labels, `fn-peer-capability-lines` a peer's (adds IHAVE, STREAMING), `fn-auth-capability-lines` an authenticating reader's (adds STARTTLS and AUTHINFO USER, and takes the posting bit from the authenticated principal). The access-dependent labels are proved to appear only where their RFCs allow: `fn-auth-starttls-is-not-advertised-under-tls`, `fn-auth-starttls-is-not-advertised-without-a-certificate`, `fn-auth-authinfo-is-not-advertised-once-authenticated` (`books/nntp-auth.lisp`). Every state's block is pinned as a whole-transcript equality in `tests/acl2/nntp-auth-tests.lisp`: unauthenticated/plain, unauthenticated/TLS, authenticated/posting, authenticated/read-only, no-certificate, protected-only |
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
| §7.2 | HELP multiline response, unsupported arguments | Implemented/tested; the text lists every keyword `fn-nntp-session-command` and `fn-nntp-archive-command` recognize and nothing else, and `tests/acl2/nntp-legacy-tests.lisp` pins the two lists against each other so a new command that is not listed fails the test book. The control for that pin is XPATH (RFC 2980 §2.10), a real legacy keyword this reader refuses; it was XPAT until this lane implemented XPAT. **Open**: AUTHINFO and STARTTLS are answered by `books/nntp-auth.lisp`, above the dispatcher, so the HELP text the dispatcher renders does not list them and the pin cannot see them |
| §7.3, §7.5 | NEWGROUPS time forms, GMT/local semantics, group creation metadata | Implemented over persisted `fn-nntp-group-factp` records supplied as an input list. Both year forms with §7.3.2's century rule; a two-digit year with no wall reading is `503`, not a guess. fn's local time zone is UTC, so the optional GMT token changes nothing and is accepted only in third position. Emitted names are renderable with no environment hypothesis (`fn-nntp-facts-since-are-facts`) |
| §7.4 | NEWNEWS filtering/time forms | Deferred; no capability claim |
| §7.6.1 | LIST defaults, keyword variants, syntax/availability errors, no state changes | Default, ACTIVE (with and without a wildmat), ACTIVE.TIMES, NEWSGROUPS, HEADERS and OVERVIEW.FMT implemented; DISTRIB.PATS and DISTRIBUTIONS are recognized-but-unmaintained 503; malformed or unknown variants are 501. The variant keyword is dispatched by `fn-nntp-list-command`, which is what `books/nntp.lisp` calls, so that ACTIVE.TIMES can read the environment; session preservation proved (`fn-nntp-list-response-preserves-session`) |
| §4, §§7.6.3/7.6.6 | Wildmat grammar/semantics and filtered ACTIVE/NEWSGROUPS | Bounded strict UTF-8 parser and dynamic-programming matcher integrated; RFC, malformed, boundary, socket and independent-client cases pass; general DP/reference equivalence, UTF-8 progress/scalar bounds and parser-output recognition are proved; matcher work and runtime guard graphs have scoped certification; parser work and complete protocol refinement remain open |
| §§8.3–8.4 | OVER by range/Message-ID/current, missing fields, byte/line metadata, OVERVIEW.FMT | Implemented over the proved `fields` view in `books/article.lisp`/`books/article-fields.lisp`. All three forms; §8.3.2's escaping is proved total (`fn-nov-scrub-is-clean`), a missing header yields the empty field (`fn-nov-missing-header-is-empty`), `:bytes` and `:lines` are the exact retained octets (`fn-nov-bytes-is-the-retained-octet-count`, `fn-nov-lines-counts-the-retained-body-lines`), and the eight-field line carries no CR, LF or NUL (`fn-nov-line-is-a-clean-line`). Xref is omitted, so exactly eight fields are emitted and OVERVIEW.FMT lists exactly the seven fixed lines. §§8.1/8.2's overview database as a stored structure is not implemented: each line is projected on demand |
| §§8.5–8.6 | HDR field forms (message-id, range, current), 225/430/423/420/412, metadata items, LIST HEADERS | Implemented over the same `fields` view and the same §8.3.2 transformation OVER uses, so no second header projection exists. All three forms; any header may be requested, so LIST HEADERS answers with the single colon §8.6.2 requires plus the two metadata items. Proved: the value half of an HDR line is clean with no hypothesis (`fn-nntp-hdr-content-is-clean`), the whole line carries no TAB, CR, LF or NUL (`fn-nntp-hdr-line-is-a-clean-field`, `fn-nntp-hdr-lines-for-numbers-are-clean`), and a field the article does not carry renders empty (`fn-nntp-hdr-of-a-missing-field-is-empty`). The code chosen per situation is tested, not proved. §8.5.2's permission to renumber a message-id hit found in the selected group is not taken: the number is always 0 |
| §7.6.4 LIST ACTIVE.TIMES | Group name, creation time in seconds since 1970-01-01, creator text; optional wildmat | Implemented from the same persisted `fn-nntp-group-factp` list NEWGROUPS reads (`fn-nntp-env-facts`), so §7.6.4's "SHOULD be consistent with NEWGROUPS" holds by construction rather than by a second derivation. A group with no creation fact is omitted, which §7.6.4 permits. The third field is the plain text `unattributed`: fn's configuration record carries no creator, and inventing a mailbox would be fabricating provenance. Lines are proved clean (`fn-nntp-active-times-lines-are-clean`). **Host-side source, not yet wired**: the created stamps live in the node's configuration as `fn-cfg-group-created` of the entries `fn-cfg-group-all-names`/`fn-cfg-groups` of `(fn-cnode-config cn)` (`books/node-config.lisp`, w5-config-groups); the served connection today builds its environment with an empty fact list (`books/nntp-post.lisp`), so the served reply is the empty block. Wiring that is the mutable-owner lane's, recorded open |
| §7.6.5 / RFC 2980 §2.1.4 | LIST DISTRIB.PATS, LIST DISTRIBUTIONS | Recognized with their §7.6.5 / §2.1.4 arities and answered `503 data item not stored`; fn holds no distribution data and none is invented |

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
| HDR / XHDR *field* *n* \| *range* | as ARTICLE for the located article(s): `O(A · m)` to locate plus `O(P)` to parse each selected article's payload. One parse per article, the same parse OVER does. |
| XOVER [*range*] | exactly OVER's cost; it is the same renderer. |
| LIST ACTIVE.TIMES [*wildmat*] | `O(F)` in the number of creation facts, plus the wildmat match per fact where one is given. No archive traversal. |
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
| XOVER reports the same overview as OVER | proved (`fn-nntp-xover-agrees-with-over-on-a-nonempty-range`, `fn-nntp-xover-with-no-argument-is-over-with-no-argument`) — the two differ only where RFC 2980 §2.8.1 and RFC 3977 §8.3.1 assign different codes |
| No HDR or XHDR line carries TAB, CR, LF or NUL, whatever the stored article | proved (`fn-nntp-hdr-content-is-clean`, `fn-nntp-hdr-line-is-a-clean-field`, `fn-nntp-hdr-lines-for-numbers-are-clean`) — unconditional |
| A field the article does not carry gives an empty HDR value | proved (`fn-nntp-hdr-of-a-missing-field-is-empty`) |
| No LIST ACTIVE.TIMES or LIST NEWSGROUPS line carries CR, LF or NUL | proved (`fn-nntp-active-times-lines-are-clean`; `fn-nntp-newsgroup-lines-are-clean` under `fn-nntp-safe-group-listp`) |
| Every LIST ACTIVE.TIMES stamp is the group's persisted creation fact, never the reader's clock | proved by construction: `fn-nntp-active-times-line` reads `fn-nntp-fact-created` and no other input; the served connection supplies no facts yet, so the served block is empty |
| LIST ACTIVE.TIMES on the served path lists the configured groups' created stamps | **open**: the served environment is built with an empty fact list (`books/nntp-post.lisp`), so the served reply is the empty block. Wiring `fn-cnode-config`'s created stamps into the served conn is the mutable-owner lane's |
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
| §7.6.6 LIST NEWSGROUPS | Group name, separator, short description; description may be passed on as held | Implemented; the second field is the fixed marker `(no description)`, identical for every group. fn's group table (`books/config-records.lisp`) carries names, policy ids and created/retired stamps and no description, so nothing group-specific is invented; the marker is a statement about the server. It is **not** the empty string, and that is measured: Python nntplib strips the line and then requires name + white space + text, so a bare `name TAB` drops the group from `descriptions()` entirely (`tests/interop_nntplib.py`, 2026-09-20). Until R5 carries a description per group this row is a stated local limitation. The line is proved clean (`fn-nntp-newsgroup-lines-are-clean`) |

## The RFC 2980 clause matrix

[RFC 2980](../rfc2980.txt) is informational: it records what deployed servers
did before RFC 3977. A row is closed only where fn implements the clause as
RFC 2980 describes it, including that section's own response codes where they
differ from RFC 3977's.

| RFC 2980 clause | Requirement | Status |
| --- | --- | --- |
| §2.1.2 LIST ACTIVE | Optional wildmat argument limiting the listed groups | implemented (`fn-nntp-list-active-or-newsgroups` with `fn-nntp-filter-groups-by-wildmat`); socket and independent-client cases in `tests/test_reader.py` and `tests/interop_nntplib.py` |
| §2.1.3 LIST ACTIVE.TIMES | Name, creation seconds since 1970-01-01, creator; optional wildmat | implemented from the environment's creation facts; the creator field is the plain text `unattributed` because no creator is recorded. See the §7.6.4 row |
| §2.1.4 LIST DISTRIBUTIONS | Distribution list | deferred: fn has no distribution data. Recognized with its arity and answered `503 data item not stored`, never a fabricated list |
| §2.1.5 LIST DISTRIB.PATS | Distribution patterns | deferred, as §2.1.4 |
| §2.1.6 LIST NEWSGROUPS | Name and description, optional wildmat | implemented with the fixed `(no description)` marker; see the §7.6.6 row |
| §2.1.7 LIST OVERVIEW.FMT | The overview field order | implemented; the seven fixed lines, proved clean (`fn-nov-fmt-lines-are-clean`) |
| §2.1.8 LIST SUBSCRIPTIONS | Default subscription list | deferred: fn has no subscription policy and inventing one would be a recommendation the operator did not make. Answered `503 data item not stored`, which is §2.1.8's own second response code; it was 501 until slrn 1.0.3 was measured sending this on every connection (2026-09-20) |
| §2.2 LISTGROUP | Group and range forms | implemented (RFC 3977 §6.1.2 row) |
| §2.3 MODE READER | 200/201 or 502 | implemented (RFC 3977 §5.3 row) |
| §2.4 XGTITLE | Per-group description by wildmat | deferred: the same missing descriptions as LIST NEWSGROUPS. `500 command not recognized` |
| §2.5 XHDR *(numbered §2.5.1 in the response list)* | — | see §2.6 |
| §2.6 XHDR | `XHDR header [range\|<message-id>]`; 221 then `number SP value` per line, or the message-id in place of the number; 412/420/430 | implemented as `fn-nntp-xhdr-response`, one dispatcher line in `books/nntp.lisp`. It is `fn-nntp-hdr-command` with the legacy flag: the same value renderer as HDR, 221 instead of 225, 420 instead of 423 for an empty range, and the message-id itself as the label. The label passes through `fn-nov-scrub`, which is proved the identity on a printable token (`fn-nov-scrub-is-the-identity-on-a-printable-token`), so the client's own octets come back unchanged and still cannot split a line. The "(none)" variant some implementations emit is **not** produced: §2.6 offers it as an alternative, and the 221-then-empty-block form is the one RFC 3977 §8.5.2 also allows |
| §2.7 XINDEX | The tin index file | deferred: an undocumented external format with no specification in RFC 2980 to audit against. `500 command not recognized` |
| §2.8 XOVER | `XOVER [range]`; 224 then the seven-field overview line per article; 412/420 | implemented as `fn-nntp-xover-response`, one dispatcher line. Proved to be OVER on every input where the two RFCs assign the same response (`fn-nntp-xover-agrees-with-over-on-a-nonempty-range`, `fn-nntp-xover-with-no-argument-is-over-with-no-argument`), so the legacy spelling cannot report a different overview. RFC 2980 defines no message-id form and no 430, so `XOVER <message-id>` is `501 syntax error` rather than a code §2.8.1 does not list |
| §2.9 XPAT | `XPAT header range\|<message-id> pat [pat...]`; 221 then the matching header lines, including an empty list; 430 for an unknown message-id | implemented as `fn-nntp-xpat-response`, one dispatcher line in `books/nntp.lisp`. The bound the earlier deferral asked for is supplied by `fn-wildmat-decode` itself, which refuses a target longer than `*fn-wildmat-max-octets*` (497) before any DP work, so the match cost is set by the command and the cap and never by stored article length. Proved: every line XPAT emits is a line XHDR emits for the same field, group and numbers (`fn-nntp-xpat-lines-are-hdr-lines`, a `subsetp-equal`), and a filter that selects everything gives XHDR's block exactly (`fn-nntp-xpat-with-a-total-filter-is-the-hdr-block`) — so XPAT is not a second header projection and cannot report a header XHDR renders differently. Lines are proved clean (`fn-nntp-xpat-lines-are-clean`) and the block is response text (`fn-nntp-xpat-block-is-block-text`). §2.9's joining of trailing arguments into one space-separated pattern is `fn-nntp-xpat-join`, witnessed directly, and the joined pattern is parsed with the **header-value wildmat profile** (`fn-wildmat-parse-text`, decision D19), not with RFC 3977 §4.1's newsgroup-name grammar. **OB-XPAT-SPACE is CLOSED.** It was that §4.1's `<wildmat-exact>` excludes SP — for the reason §4.1 gives, that "these characters cannot occur in newsgroup names, which is the only current use of wildmats" — so every XPAT with more than one pattern token got `501 syntax error` and the join's multi-token branch could never produce a match. §4.3 licenses the wider profile and the proviso is discharged: `fn-wildmat-parse` is extensionally unchanged and `fn-wildmat-item-character-matchp-is-rfc3977-on-rfc3977-items` says the matcher's literal test is the pre-D19 one on every §4.1 item. fn now phrase-searches a header: `XPAT subject 1-1 *Hello *there *world*` against `Subject: Hello there world` renders the line, and a multi-token pattern that does not match is §2.9's 221 with an empty list, which is also what INN 2.7.4 answers (its `Glom` joins identically and `uwildmat_simple` treats SP as a literal; measured against INN's own `libinn.a` in `planning/evidence/inn-xpat-2026-09-20.md`). A second, smaller divergence the other way is recorded and deliberately unchanged, and D19 does not touch it because `,` is an exact item in neither profile: fn reads `,` as wildmat alternation, INN as a literal, and here RFC 2980's "at least one pattern in wildmat" is on fn's side. Both are pinned by `tests/acl2/nntp-legacy-tests.lisp`. **LOCAL POLICY, stated**: a header value longer than 497 octets matches no pattern and its article is omitted; §2.9 promises nothing for that case |
| §2.10 XPATH | The server's filesystem path for an article | refused permanently, not deferred: fn's article storage layout is not part of its protocol surface and exposing it would leak the store's internals. `500 command not recognized` |
| §2.11 XROVER | Bare References overview | deferred: `XHDR references <range>` is the same information and is implemented. `500 command not recognized` |
| §2.12 XTHREAD | The threading database | deferred: fn maintains no threading database. `500 command not recognized` |
| §3.x AUTHINFO | Authentication | superseded by RFC 4643, which fn implements; see the RFC 4643 matrix below. RFC 2980 §3.1.1's original AUTHINFO USER/PASS codes are RFC 4643 §2.3.1's, so the same implementation answers both |

## The RFC 4643 clause matrix (AUTHINFO)

[RFC 4643](../rfc4643.txt) is implemented in [`books/nntp-auth.lisp`](../books/nntp-auth.lisp),
which is the outermost wrapper of the served command chain: `fn-served-dispatch`
calls `fn-auth-step`, which answers AUTHINFO, STARTTLS and CAPABILITIES and
delegates everything else to `fn-peer-step` unchanged. Evidence is
[`tests/acl2/nntp-auth-tests.lisp`](../tests/acl2/nntp-auth-tests.lisp).

**Every row below was true of the model and false of the running server
until 2026-09-21**, and the whole of the difference was one argument:
`fn-served-open-peer` pinned `(fn-auth-open-config)` instead of the
operator's policy, and the owner opens a connection with that branch
whenever the source address matches a peer record — which on one box is
every client. `AUTHINFO PASS` answered 481 with the secret just written,
no AUTHINFO label was advertised and POST was never gated.
[The live record](../planning/evidence/auth-live-2026-09-21.md) is the
before and after; PRF-039 carries the theorems; and the test that
would have caught it is `tests/test_auth.py ServedCredentialTests`, which
starts the node through `bin/fn run` with a peer record, because no test
that starts `tools/run_owner.py` directly can reach the peer branch. The
lesson is recorded here and not only in the lane handoff: a clause matrix
about a book is not a claim about a listener.

| RFC 4643 clause | Requirement | Status |
| --- | --- | --- |
| §2.1 | Advertise `AUTHINFO USER` only for what the server will accept now | proved: `fn-auth-authinfo-is-not-advertised-once-authenticated`. Also withheld on an unprotected connection when the configuration is protected-only, because the server would answer 483, and withheld when the configuration holds NO credential, because every PASS would then be 481. The SASL argument is never advertised. Live since 2026-09-21: the label appears in `CAPABILITIES` on a node started `fn run` with a credential the CLI wrote, on a reader connection and on one the owner resolved to a peer record alike (`fn-served-peer-and-reader-open-under-the-same-policy`, PRF-039) |
| §2.2 | 480 before authentication; the command is not performed | **keystone** `fn-auth-gated-command-is-refused-and-not-performed`: with authentication required and no authenticated subject, a restricted command's step submits nothing, never offers article mode, returns the session unchanged, and its whole effect list is the single 480 line. The restricted set is `fn-auth-restricted-keywordp`: every archive and transit command plus POST. CAPABILITIES, HELP, QUIT, MODE, DATE, AUTHINFO and STARTTLS stay available, so an unauthenticated client can still discover the server and still authenticate |
| §2.3.1 | 281 / 381 / 481 / 482 / 502 exactly | implemented and pinned as transcripts; each code has its own line and no two are equal |
| §2.3.2 | MUST return 381 to AUTHINFO USER | implemented unconditionally, for a configured and an unconfigured name alike, and the two replies are asserted equal so the reply cannot disclose whether the name exists |
| §2.3.2 | MUST give 482 to AUTHINFO PASS with no cached username | implemented; also after a failed PASS, because the cached name is cleared on failure, so a password cannot be retried without a fresh USER |
| §2.3.2 | MUST NOT return 480 to AUTHINFO USER/PASS | implemented: the gate is checked before AUTHINFO only for keywords in `fn-auth-restricted-keywordp`, and AUTHINFO is not in it (asserted). Once authenticated the answer is 502, §2.3.1's own "command unavailable" |
| §2.3.2 | MUST NOT return 381 to AUTHINFO PASS | implemented: 381 exists on the USER branch only |
| §2.3.2 / §2.5 | A cleartext mechanism needs a protected channel | `fn-auth-config-protected-onlyp` answers 483 on an unprotected connection and 381 under TLS; both witnessed |
| §2.3.2 | Authentication grants privileges to this connection | the posting allowance is the authenticated principal's `fn-auth-cred-postingp`, not the connection's: two principals are witnessed, one that may post and one that may not, and the POST capability label follows each |
| §2.4 SASL | AUTHINFO SASL with a mechanism list | **deferred**, answered `502 no SASL mechanism is offered` (§2.4.1 note [2]), and no SASL argument is advertised. PLAIN was considered and not shipped: over a protected channel it is USER/PASS with a base64 wrapper and adds no property fn can state, and the mechanisms that would add one (SCRAM, EXTERNAL over a client certificate) need either an executable digest — the same `OB-AUTH-DIGEST` below — or certificate material the book does not see |
| §2.5 | Security considerations: the cleartext secret | the STORED secret is now a salted digest (`books/auth-secret.lisp`); the WIRE secret is still cleartext, which is what the mechanism is. See `OB-AUTH-DIGEST` below |

### OB-AUTH-DIGEST (CLOSED 2026-09-20; the record of why it was open stays)

**It was open** because the only digest fn had was `fn-digest`
(`books/crypto-seam.lisp`), an `encapsulate`d constrained function with no
attachment, so it could not be evaluated: calling it on the served path
would have made `fn-served-step` non-executable and the reader would have
stopped serving. Deriving the digest in Python instead is refused by the
one-owner rule in `AGENTS.md`. So the configuration held the shared secret
in the clear and `fn-auth-checkp` compared the supplied octets to it with
`equal`.

**It is closed** because `books/sha256.lisp` defines an executable,
guard-verified SHA-256 and `books/crypto-attach.lisp` attaches it to
`fn-digest`. `books/auth-secret.lisp` is the scheme over it — a 16-octet
salt per credential, the tagged digest of `salt || secret`, the stored
verifier `(:fn-authsec-v1 salt digest)` — and `fn-auth-checkp` is
`fn-authsec-checkp` on that verifier. `fn-auth-credp` recognizes a
`fn-authsec-verifierp` where it recognized a printable token, so by
`fn-authsec-verifier-is-not-octets` a cleartext secret is not even
well-formed in the slot any more. `fn principal set-password` derives the
verifier through `tools/auth_secret.py`, which is one ACL2 session and no
`hashlib`; `bin/fn` no longer imports that module at all.

**What did NOT change.** The wire. AUTHINFO USER/PASS over a plaintext
connection still reveals the secret to anyone on the path: that is a
property of the mechanism RFC 4643 §2.3 defines, which is why §2.3.2 asks
for a protected channel and why `fn-auth-config-protected-onlyp` exists.
What changed is what a stolen *configuration file* contains. And that a
WRONG secret is rejected is still not a theorem — it is second-preimage
resistance of the attached SHA-256, A-CRYPTO — though it is now a witness
on concrete octets under the real attachment in
`tests/acl2/nntp-auth-tests.lisp` and on the wire in
`planning/evidence/auth-w10-2026-09-20.md`.

**Migration, a local policy choice.** An existing credential file in the
old format (a `secret` key in the clear) is REFUSED by name —
`cleartext-credential` — by both `fn principal set-password` and
`tools/run_owner.py`, and the operator re-sets the password. fn does not
migrate it: the cleartext cannot be turned into a verifier without reading
it, and reading an operator's stored password to re-derive it is the thing
the scheme exists to stop.

## The RFC 4642 clause matrix (STARTTLS)

[RFC 4642](../rfc4642.txt). **TLS itself is a trusted host facility and is not
in the model.** `books/nntp-auth.lisp` sees plaintext octets on both sides of
the handshake: it emits a `(:starttls)` effect and `tools/run_owner.py` wraps
the socket with Python's `ssl` module. What the book proves is the protocol
state machine around the upgrade, and nothing about the upgrade.

| RFC 4642 clause | Requirement | Proved / tested / trusted |
| --- | --- | --- |
| §2.1 | Advertise the STARTTLS label; MUST NOT advertise it once a TLS layer is active | **proved**: `fn-auth-starttls-is-not-advertised-under-tls`, and `fn-auth-starttls-is-not-advertised-without-a-certificate` for the case where no certificate is configured |
| §2.2.1 | `STARTTLS` takes no arguments | implemented: 501 with an argument, witnessed |
| §2.2.2 | 382 then the handshake | implemented: the reply and one `(:starttls)` effect. `fn-auth-starttls-effect-only-with-382` says the effect appears only from the branch that also puts the session into the HANDSHAKE, so a handshake can never begin without the client having been told, and `tlsp` is NOT set there: `fn-auth-tls-established-sets-the-layer` is the only transition that sets it and only the host's `(:tls-established)` wire event reaches it |
| §2.2 | STARTTLS MUST NOT be pipelined; the handshake begins with the first octet after the 382's CRLF | **proved, and it used to be open.** `fn-served-feed` (`books/served.lisp`) stops on a handshaking connection exactly as it stops on a closed wire (`fn-served-feed-of-handshaking-connection`, `fn-served-step-of-handshaking-connection-is-a-no-op`), so octets behind the command line in the same read are never framed as NNTP. The stop is a property of the CONNECTION, not of the effects just emitted, which is what lets `fn-served-feed-of-append` and partition independence survive it. Before 2026-09-20 the host discarded those octets by itself and the spec recorded that as a defect |
| §2.2.2 | Once a TLS layer is active, STARTTLS is not a valid command | **proved**: `fn-auth-second-starttls-is-refused` — 502 and no second handshake effect |
| §2.2.2 | 580 when the server cannot initiate | implemented for the configuration reason (no certificate or key configured). A host-side handshake failure after a 382 is not a 580: by then the 382 has been sent, and `tools/run_owner.py` closes the connection, which §2.2.2 permits |
| §2.2.2 | MUST NOT reply 480 or 483 to STARTTLS | implemented: the STARTTLS branch has three replies (501, 502, 580) and 382, and none of the others is reachable from it. STARTTLS is not in `fn-auth-restricted-keywordp`, so the §2.2 gate never sees it |
| §2.2.2 | Discard protocol state across the handshake | implemented: the 382 branch clears the cached username and the authenticated subject, witnessed both ways |
| §2.3 | The security layer itself: confidentiality, integrity, certificate validation, cipher selection, Client Hello compatibility, SNI | **trusted, not modelled.** Python's `ssl` with the configured `[listener] tls cert key`. No theorem in this tree says anything about it. Recorded in the trust boundary of [the NNTP contract](nntp.md) |
| §2.3 | A client MUST discard cached CAPABILITIES across the handshake | a client obligation; fn re-answers CAPABILITIES from the post-handshake session, which is what makes discarding correct |
| §5 | 483 for a restricted command on an unprotected connection | **partially**: 483 is emitted for AUTHINFO under `protected-onlyp`. A general "restricted command" set gated on TLS rather than on authentication is **not** implemented; `fn-auth-restricted-keywordp` gates on authentication only. Recorded open |

### What a real legacy client sends

slrn 1.0.3 (Homebrew `slrn`, macOS arm64), driven by `tests/interop_slrn.py`
against `tools/run_reader.py` on 2026-09-20, sends exactly this and nothing
else before it reaches its group list: `MODE READER`, `XOVER`, `XHDR Path`,
`LIST OVERVIEW.FMT`, `LIST`, `LIST SUBSCRIPTIONS`, `QUIT`. Three of those
(`XOVER`, `XHDR`, `LIST SUBSCRIPTIONS`) did not exist in fn before this lane
and two of them are the reason it exists. fn answered every one without a
500 or a 501, and slrn built a newsrc naming the served group. The 412s in
that transcript are correct: slrn probes `XOVER` and `XHDR` before selecting
a group. That is one client at one version, not an RFC audit.

No READER clause is open, so **READER is advertised**. STARTTLS is advertised
when a certificate is configured and no TLS layer is active (RFC 4642 §2.1) and
AUTHINFO USER while the connection is unauthenticated and the server would
accept it (RFC 4643 §2.1); both are proved, not asserted. The one item this table
leaves open, the §6.1.1.2 count *theorem*, is an assurance gap about a value the
transcripts pin exactly; it is not a missing command or an unimplemented branch.
OVER is advertised as `OVER MSGID` because the message-id form is implemented;
§8.3.2 requires the MSGID argument exactly when that form works. LIST is
advertised with the three variants that answer with data. POST, IHAVE, NEWNEWS,
HDR and MODE-READER stay unadvertised; this reader is not mode-switching.
XPAT and XHDR carry no capability label at all: RFC 2980 predates §3.3 and names
none, and a client discovers them by trying them.

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

## Certification status of this matrix (w9/server-polish, 2026-09-20)

Recorded exactly, because a row above claims a theorem and a theorem is only
a theorem once ACL2 has checked it.

**Certified** on hbox, run `run-20260920T181811Z-484a`, evidence
`/tank/fn/lanes/w9-server-polish/build/acl2/certify-20260920T181816Z-1031915`:
`books/nntp-responses`, `books/nntp`, `books/nntp-overview`,
`books/nntp-legacy` and `books/nntp-invariants`, which carry every XPAT
definition and the XPAT keystones (`fn-nntp-xpat-lines-are-hdr-lines`,
`fn-nntp-xpat-with-a-total-filter-is-the-hdr-block`,
`fn-nntp-xpat-lines-are-clean`) and the three
`fn-nntp-xpat-*-preserves-session` rules
`fn-nntp-archive-command-keeps-projection` needs.

**No verdict**, for a cause outside this lane: `books/peer-config` fails at
`( DEFTHM FN-CFG-SET-PEER-DELTA-IS-ADMISSIBLE ...)` on this tree, from
`74503ed` "w6/peering-inbound: ... (peer books uncertified)". It sits under
`peer-inbound` and therefore under `served`, so **`books/served`,
`tests/acl2/served-tests`, `books/nntp-auth`, `tests/acl2/nntp-auth-tests`,
`books/owner`, `books/owner-invariants` and `tests/acl2/owner-tests` cascade
off it**. Every §3.5 pipelining row and every RFC 4643 and RFC 4642 row above
therefore names a theorem that is written and committed and has NOT been
checked by ACL2 on this tree. None was weakened to manufacture a green and
none was removed. The one form standing between dev and a certified served
path is the peer-config one.

`books/nntp-effects` carries the XPAT effect typing. Its message-id lemma was
rerouted off `fn-nntp-hdr-labelled-line-is-block-text`, which
w5/owner-followups recorded open on dev after 2598 s and 1.47e9 prover steps;
`fn-nntp-xpat-msgid-block-is-block-text` goes through
`fn-nntp-hdr-clean-fields-are-clean-lines` instead, the route the range form
uses. The rerouted version is committed and was not reached before this lane's
budget ended.

The Python suites (`tests.test_reader`, `tests.test_post`, `tests.test_owner`)
and the slrn and nntplib probes did not run: they drive a live owner, which
needs the certificates the cascade above withholds. The XPAT socket transcript
in `tests/test_reader.py` and the TLS transcripts in `tests/test_owner.py` are
written and unrun, and are named here so nobody reads them as evidence.

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
