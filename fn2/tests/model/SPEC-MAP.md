# H2a: independent NNTP surface model

The authority for this model is the root `specs/nntp.md` and the root RFC text
files. No implementation source was opened, including the permitted optional
reply-text cross-check. RFC examples are illustrative text, not canonical reply
phrases. Status codes, required status arguments, framing, determined content,
and the explicitly required withdrawal/refusal words are checked separately.

## Rule map

The Python `SPECS` table is also attached to every mismatch verdict. Shared
helpers implement the following rules; command wrappers select their own rule
name and citation, so a HEAD failure is reported as HEAD, not ARTICLE.

| Rule / function | Source | Constraint checked / state effect |
|---|---|---|
| `command_line`, `_dispatch`, `_error` | RFC 3977 §§3.1, 3.2.1, 9.2; specs/nntp.md:512-519 | CRLF; one command; 512 octets including CRLF; 497 argument octets; case-insensitive keyword; SP/TAB separation; 501 for invalid syntax; observed close alternatives only for malformed framing/UTF-8 (H2d below). |
| `lines`, `stuff`, `unstuff`, `encode_block`, `decode_block` | RFC 3977 §3.1.1; specs/nntp.md:512-519 | Exact CRLF, no bare CR/LF/NUL; stuff each initial dot; exactly one terminal dot line; no trailing octets. Raw stuff/unstuff are invertible even on arbitrary binary; block functions validate the narrower wire domain. |
| `Expect.check/update`, `_queue` | RFC 3977 §3.5; specs/nntp.md:2453-2478 | Check is observational; update validates before committing and is idempotent; queued expectations resolve and update in wire order; body predicates receive decoded bytes only after checking wire framing. |
| unknown keyword | specs/nntp.md:51-93; RFC 3977 §3.2.1 | 500; no state effect. Known private extensions have their explicit rules (A1). |
| greeting | specs/nntp.md:9-23,1985-2010; RFC 3977 §5.1 | 200 iff posting is allowed now; otherwise 201. Illustrative banner text unconstrained. |
| capacity / `connect` | specs/nntp.md:2301-2384; RFC 3977 §5.1.1 | Total capacity default 31; public address default 8; trusted ranges exempt address count only; named 400 closes on greeting update. |
| CAPABILITIES | specs/nntp.md:3-24,1698-1736,2480-2507; RFC 3977 §5.2; RFC 8054 §2.1 | 101 block; VERSION first, required reader labels, no duplicates; optional keyword ignored; conditional POST, IHAVE, STREAMING, STARTTLS, AUTHINFO, SASL. COMPRESS DEFLATE is required when authenticated and inactive, optional before authentication, forbidden when active (HV seat ruling). No MODE-READER/XOVER/XHDR. Unknown extra extension labels allowed. |
| HELP | specs/nntp.md:51-93; RFC 3977 §7.2 | 100; exact keyword set, accepting the old table or that table plus the two explicitly served private verbs (A1). |
| MODE READER | specs/nntp.md:14-24; RFC 3977 §5.3 | 200/201 follows posting allowance, records `mode_reader_seen`, no mode-switching server inferred. |
| MODE STREAM | specs/nntp.md:78-80,2416-2418; RFC 3977 §3.2.1; RFC 4644 §2.3 | 203 on peer; 501 on reader where STREAM is not an implemented MODE variant. The explicit 502 rule names IHAVE/CHECK/TAKETHIS only. |
| QUIT | specs/nntp.md:521-528; RFC 3977 §5.4 | 205 commits closed; every later command/block, including AUTHINFO, expects zero octets and no body/terminator. |
| DATE | specs/nntp.md:106-134,667; RFC 3977 §7.1 | Current supplied wall observation, 111 with 14 digits; no clock 503; unknown observation accepts either shape (E2). |
| durable issuance / `add_article` | specs/nntp.md:426-448,491-505,701-707; RFC 3977 §6 | Explicit `(number, Message-ID)` entries; monotonically allocated watermark independent of list position; withdrawn/retired identities never release numbers; duplicate acceptance assigns nothing. |
| `_pin`, `_snapshot`, `_visible` | specs/nntp.md:450-505,539-577,1916-1982 | Capture coherent per-connection article, membership, watermark, withdrawal, flags and stamp view; access is a projection; use executed view policy, not unlanded debt (A2). |
| GROUP | specs/nntp.md:419-505; RFC 3977 §6.1.1 | 211 exact available count/low/high/name; empty `0 wm+1 wm`; first available cursor; 411 leaves old selection and pin. Leading zeroes accepted. |
| LISTGROUP | specs/nntp.md:419-505; RFC 3977 §6.1.2 | Same fresh selection as GROUP, optional group/range; exact sorted numbers; range does not change which first article is selected; empty range is an empty 211 block. |
| NEXT | specs/nntp.md:419-505; RFC 3977 §6.1.4 | Lowest available number greater than cursor; 223 identity; 412/420/421; failure keeps cursor. |
| LAST | specs/nntp.md:419-505; RFC 3977 §6.1.3 | Greatest available number below cursor; 223 identity; 412/420/422; failure keeps cursor. |
| ARTICLE | specs/nntp.md:330-362,400-424,974-988; RFC 3977 §6.2.1 | 220 and exact stored article with generated first Xref line; number/current success moves cursor; Message-ID never moves it; 412/420/423/430. |
| HEAD | specs/nntp.md:400-424; RFC 3977 §6.2.2 | 221 and exact first-Xref plus stored header lines, excluding separator/body; same reference/cursor rules. |
| BODY | specs/nntp.md:400-424; RFC 3977 §6.2.3 | 222 and exact retained body, no Xref; same reference/cursor rules. |
| STAT | specs/nntp.md:419-424; RFC 3977 §6.2.4 | 223 with number/Message-ID, no block; same reference/cursor rules. |
| `_lookup` withdrawn / hidden | specs/nntp.md:974-988,1943-1952 | Withdrawn visible Message-ID requires `430 withdrawn`; hidden article gets ordinary 430; numeric absence requires 423 (text not prescribed by these passages). |
| `_lookup` Message-ID number | RFC 3977 §6.2.1.2; specs/nntp.md:419-424,2644-2650 | Accept zero OR actual selected-group number, only zero without membership; preserve cursor. |
| `msgid`, `stored_msgid`, `number_range` | RFC 3977 §§6,9.8; RFC 5536 §3.1.3 | Command Message-ID grammar is deliberately looser than stored identity grammar; stored dot-atom/literal identity; 250 octets; article numbers positive, at most 2^31-1 and 16 decimal digits. |
| `headers`, `scrub`, `body_lines`, `_nov` | specs/nntp.md:319-328,2207-2229; RFC 3977 §§8.3.2,8.5.2 | First field wins; remove CRLF then replace TAB/NUL/CR/LF with spaces; source byte count and body line count independently computed; invalid body framing counts zero as the spec states. |
| `_xref` | specs/nntp.md:330-362,400-416; RFC 5536 §3.2.14 | Node server name and exact visible local group:number pairs; never peer Xref numbers. Default server `.invalid`; explicit `None` is the documented blind environment. |
| OVER | specs/nntp.md:319-362; RFC 3977 §8.3 | 224; exact NOV fields 1–8 plus required Xref ninth field; current/range/Message-ID; 412/420/423/430; no cursor update. |
| XOVER | specs/nntp.md:136-159; RFC 2980 §2.8 | Same rows, empty range 420 instead of 423, Message-ID form 501. |
| HDR | specs/nntp.md:400-416,2771-2806; RFC 3977 §8.5 | 225; field value/metadata/served Xref; absent field still has row; empty value may omit separating space; unknown metadata 503; no cursor update. |
| XHDR | specs/nntp.md:136-159,400-416; RFC 2980 §2.6 | 221; empty range 420; Message-ID labels the row in Message-ID form. |
| XPAT | specs/nntp.md:161-180,415-416; RFC 2980 §2.9 | 221 even for no matches; join pattern arguments with one space; case-sensitive rightmost wildmat; stored Xref only, not generated Xref. No undocumented 2,000-article truncation (A8). |
| `wildmat` | RFC 3977 §§4.1-4.2; specs/nntp.md:161-180 | Rightmost matching comma alternative wins; `!` exclusion after first alternative; anchored `*`/`?` on Unicode characters; invalid patterns refused. |
| LIST / LIST ACTIVE | specs/nntp.md:491-505,1061-1118,1916-1982; RFC 3977 §7.6.3 | Exact visible names and high/low; y/n/m from read-only, moderation and post access; order arbitrary; numeric leading zeroes allowed. |
| LIST COUNTS | specs/nntp.md:1109-1118; RFC 6048 §2.2 | ACTIVE fields plus exact available count; same status; spaces, not tabs; arbitrary row order. |
| LIST NEWSGROUPS | specs/nntp.md:182-235; RFC 3977 §7.6.6 | Exact configured descriptions or `(no description)`; whitespace separating name/text. |
| LIST OVERVIEW.FMT | specs/nntp.md:330-362,397-399; RFC 3977 §8.4 | Fixed ordered headers, `Bytes:`, `Lines:`, then `Xref:full` in served environment. |
| LIST HEADERS | specs/nntp.md:151-159,643-647; RFC 3977 §8.6 | `:` any header, `:bytes`, `:lines`, optional explicitly supported fn metadata; MSGID/RANGE forms; unordered. |
| LIST ACTIVE.TIMES | specs/nntp.md:182-185,375-389; RFC 3977 §7.6.4 | Persisted creation timestamp plus `unattributed`; missing creation facts omitted; visible groups only. Corrects source citation typo (A5). |
| LIST MOTD | specs/nntp.md:190-235; RFC 6048 §2.5 | Exact configured lines, empty 215 when unset, arguments 501. |
| LIST SUBSCRIPTIONS | specs/nntp.md:390-396; RFC 6048 §2.6 | Configured order cut to visible/matching groups; unset/empty defaults to view's groups. |
| LIST DISTRIB.PATS / DISTRIBUTIONS | RELEASE-PLAN §1 reader rows; RFC 3977 §7.6.5; RFC 6048 §2.3 | Recognized, unavailable 503; malformed argument form 501 under general syntax rule. |
| NEWGROUPS | specs/nntp.md:106-134,375-389; RFC 3977 §7.3 | Persisted creation at/after threshold, omit missing facts, no pin/cursor update; UTC local time; current-year resolution. |
| NEWNEWS | specs/nntp.md:237-317; RFC 3977 §7.4 | Exact available IDs in matching groups at/after durable stamp; legacy nearest later known stamp or pinned horizon, no wall means conservative inclusion; no payload Date inference. |
| `_instant` | specs/nntp.md:106-134,307-311; RFC 3977 §7.3.2 | Six/eight digit date, six digit time, calendar validation and leap-second spelling; YY current or previous century; unknown clock seam E2. |
| POST command | specs/nntp.md:709-741,1985-2010; RFC 3977 §6.3.1 | 340 enters body state; 440 disallowed; 480 authentication gate; no body mode after refusal. |
| POST body / `_article_block` | specs/nntp.md:741-809,851-949; RFC 3977 §6.3.1; RFC 5537 §§3.4.1,3.5 | Validate framing/basic required fields/identity; determined refusals; otherwise 240 or named 441; acceptance update allocates once and refreshes only poster; explicit projection inputs E3 for fields not determined here. |
| POST duplicate/conflict | specs/nntp.md:745-768,953-1030 | Same supplied source under held ID => already stored; changed source => different article; neither reissues a number. |
| POST policy / outcomes | specs/nntp.md:1061-1202,1600-1605,1985-2010 | Closed and unauthorized groups refused, forged approval refused, unapproved moderated post may queue; accepted/refused/uncertain recorded distinctly; uncertainty does not assert a durable acceptance (E4). |
| IHAVE | specs/nntp.md:530-537,2412-2443; RFC 3977 §6.3.2 | Reader 502; held ID 435; unknown offer {335,435,436}; 335 enters body mode; transfer {235,437,436}; duplicate 437. |
| CHECK | specs/nntp.md:2412-2443; RFC 4644 §2.4 as cited there | Echo ID; held 438; unknown {238,431,438}; 238 records promise; full max-inflight gives 431. |
| TAKETHIS | specs/nntp.md:530-537,2412-2443; RFC 4644 §2.5 as cited there | No initial reply; valid-ID block settles {239,439,436} with ID; malformed/missing-ID command still consumes a block, then 439 with sent token or `-`; retire promise; excessive body 439 then closed. |
| AUTHINFO USER/PASS | specs/nntp.md:1482-1509,1661-1696; RFC 4643 §2.3 | 381 caches latest username; missing USER 482; known credential 281; wrong 481; protected-only 483; after authentication/compression 502. |
| AUTHINFO failure budget | specs/nntp.md:1661-1696; RFC 4643 §6 | Third failed PASS/SASL is 481 plus 400 then closed; cancellation/syntax/483/503/504 do not increment; STARTTLS preserves count. |
| AUTHINFO SASL | specs/nntp.md:1698-1774; RFC 4643 §2.4 | Mechanism offer rules; PLAIN TLS-only; 383/canonical challenge, 281 PLAIN or 283 canonical final; 481/503/504; cancellation; response state consumes command-looking lines. Cryptographic exchange outcome is abstract, per H2b boundary. |
| STARTTLS / `tls_established` | specs/nntp.md:1482-1509,1620-1660; RFC 4642 §2.2 | {382,580}; 382 suspends command framing; receipt alone activates TLS and clears group/cursor; preserve MODE and failure count; auth/active TLS/compression => 502. |
| COMPRESS DEFLATE | specs/nntp.md:2480-2536 (NNT-054); RFC 8054 §2.2 as quoted there | Active compression => 502 first; otherwise unauthenticated => 480 regardless of auth-required policy (HV seat ruling). After authentication, 206 activates compression without cursor reset, including after TLS; unknown algorithm 503, malformed arguments 501. Subsequent AUTHINFO/STARTTLS => 502. Transport codec is outside H2a. |
| XREDEEM | specs/nntp.md:1784-1914 | Code/name 381; uncached PASS 482; protected-only 483; authenticated 502; completion {281,482}; 281 creates account for future connections without authenticating/refreshing this connection. |
| XFNCATCHUP | specs/nntp.md:676; RELEASE-PLAN §1 own-command row | Peer state and four argument shape; {291 block,423,501}; no invented chain/content rule. |
| XFN-ZARTICLE | specs/nntp.md:2484-2499 | Offered digest list; 229 digest/length/stored-length plus encoded lines <=128 octets, or ordinary ARTICLE predicate; no cursor change for ID form. |

## Ambiguities and conflicts in the supplied specifications

- **A1 — HELP/private verbs.** specs/nntp.md:64-72 contains 29 keywords, not
  RELEASE-PLAN's 31. specs/nntp.md:676-677 and 2484-2499 explicitly serve two
  more. The model accepts HELP's 29 or all 31 and recognizes the two extensions;
  all other unknown keywords require 500. No help-table implementation was read.
- **A2 — executed versus decided views.** specs/nntp.md:539-577 expressly says
  completed discovery and Message-ID fallback are debt, not the executed rule.
  Model uses pinned LIST/NEWNEWS/NEWGROUPS/retrieval, with refresh on successful
  GROUP/LISTGROUP/own 240. It does not silently model the proposed future view.
- **A3 — POST reply ordering.** specs/nntp.md:1473-1480 says later commands precede
  240/441; specs/nntp.md:2453-2478 expressly reverses that old behavior. Model
  follows NNT-044: outcome first, then subsequent pipelined replies.
- **A4 — Message-ID response number.** specs/nntp.md:419-424 does not choose
  between RFC 3977 §6.2.1.2's zero and actual selected-group number. Both match;
  a number in another group never matches. The same choice applies to OVER/HDR.
- **A5 — ACTIVE.TIMES citation error.** specs/nntp.md:182 and 375 attribute it to
  RFC 6048 §2.3, which defines DISTRIBUTIONS. ACTIVE.TIMES is RFC 3977 §7.6.4.
  Model follows the command's actual RFC plus fn's explicit creation policy.
- **A6 — unknown-group injection.** specs/nntp.md:704-707 delegates unknown
  group treatment to D05 without defining the mixed known/unknown case here.
  RFC 5537 §3.5 permits mixtures. The model accepts 240 or named 441 for mixed
  known/unknown groups; 240 allocates only carried groups while preserving the
  original Newsgroups bytes. An article naming no carried group requires 441.
- **A7 — empty range and expired cursor.** No ambiguity for OVER/XOVER: the
  explicit specs/nntp.md:143-152 distinction is 423/420. For XPAT, RFC 2980 §2.9
  explicitly includes an empty successful list, so the model returns 221 for an
  empty explicit range. The task's cursor invariant is scoped to the pinned
  view, consistent with specs/nntp.md:419-424 allowing later invalidation.
- **A8 — XPAT 2,000 window.** RELEASE-PLAN mentions a 2,000-article window;
  specs/nntp.md:161-180 specifies no wire refusal or truncation at that size.
  The model does not invent one; it checks the complete matched block.
- **A9 — retired index word.** specs/nntp.md:774-778 still names `mpx-saturated`,
  whereas RELEASE-PLAN retires fn1 index-specific words in fn2. The fn1-facing
  model currently permits that named 441; it is not a fn2 implementation promise.
- **A10 — miscellaneous reply text and listing order.** RFC 3977 §§2,3.2 and
  command sections leave illustrative text free. Model constrains code and
  semantic arguments; LIST rows may be reordered except SUBSCRIPTIONS, and an
  absent HDR field may omit its separating space (RFC 3977 §8.5.2).
- **A11 — private metadata/extension shapes.** specs/nntp.md:643-647 names fn
  HDR metadata without a full value grammar. Without supplied values, predicates
  enforce correct row identities and framing but allow any clean value. The
  supplied XFNCATCHUP description likewise does not define its chain/body.
- **A12 — empty group RFC alternatives.** RFC 3977 §6.1.1.2 permits three
  encodings; specs/nntp.md:491-505 explicitly selects `0 wm+1 wm`. Only that
  encoding matches fn, even though some RFC examples use `0 0 0`.

- **A13 — malformed keyword response.** RFC 3977 §9.8 (`rfc3977.txt:5422`)
  requires `ALPHA 2*(ALPHA / DIGIT / "." / "-")`; `Date:`, `From:`, `Path:`
  and `POSTFrom:` are not keywords. Section 3.2.1 (`rfc3977.txt:543-555`)
  prescribes 500 for an unrecognized command and 501 for bad arguments to a
  **recognized** command. specs/nntp.md:83-87 guarantees 500 only for a
  **well-formed** unknown command. Neither selects a unique code for an invalid
  keyword. The 80 observed 501s therefore do not justify changing the model to
  require 501; the current unknown-500 predicate remains a diagnostic outside
  its determinate domain. Layer D must choose this rejection policy explicitly.
- **A14 — malformed input recovery and closure.** specs/nntp.md:513-518 permits
  draining to a safe boundary **or closing**; RFC 3977 §12.5
  (`rfc3977.txt:5866-5899`) explicitly permits closing on illegal UTF-8.
  Neither specifies the complete reply/close sequence for every malformed
  command prefix. H2a's single 501 with a reusable connection is therefore an
  over-specific diagnostic for these inputs. H2b records an empty status both
  on timeout and on EOF, and saves no prior replies. Its 94 zero-status rows
  cannot distinguish permitted closure, body draining, and a lost reply. A
  one-command minimized candidate is not an observed empty reply: ddmin kept
  the rule only, and the stored reply belongs to the original transcript.
  H2d's complete evidence resolves **130** run-2 rows as model defects: the
  preceding structurally malformed command received 501, then a clean EOF was
  observed while awaiting the next command. `Expect.close_after_reply` and
  `close_without_reply` expose the allowed alternatives for invalid framing,
  over-512-octet lines and illegal UTF-8. Overlength specifically requires 501
  (RFC 3977 §3.2.1, `rfc3977.txt:547-551`), so only reply-then-EOF is
  accepted for it; `check/update(..., eof=True)` commits
  closure only when the driver supplies an actual clean EOF observation. An
  ordinary semantic 501 (bad argument count/range) does not grant this permission.
  A malformed article block may be drained to its terminator and rejected without
  closing; the 14 `closed` rows were an incorrect mandatory-close model effect.
  Neither timeout nor TLS reset is evidence of a permitted clean server close.

  **A14 TAKETHIS timing resolved (HT):** RFC 4644 §2.5.2
  (`rfc4644.txt:375-387`) says “The article is sent immediately following
  the CRLF at the end of the TAKETHIS command line.” The model consumes the
  block before replying even when the peer's offered identifier is malformed
  or absent, then requires 439. RFC 4644 §2.5.1 (`rfc4644.txt:370-371`) binds
  the reply to the offered Message-ID; it defines no binding for an invalid or
  absent identifier. The model accepts the sent token or `-` in that case,
  while a valid offered ID retains its exact echo requirement. Structural line
  framing/length bounds and reader-side A15 precedence remain separate.
  All 15 original run-2 A14 rows now match the observed command prefix: their
  timeout contains no reply before the article, exactly what the model expects;
  this proves no body acceptance, body refusal, or EOF. The 15 corresponding HS
  probes all observed `awaited-body`, then 439, and now match both phases.
  The mutation control rejects early 439 and subsequent body-as-command parsing.
- **A15 — permission versus malformed argument precedence.**
  specs/nntp.md:78-80 specifies reader 502 for the three transit verbs; RFC 3977
  §3.2.1 (`rfc3977.txt:547-555,579-603`) specifies syntax and authorization
  responses without choosing their precedence. Section 12.5 additionally
  permits replacement or rejection of malformed UTF-8. For the six reader/node
  TAKETHIS lines with invalid UTF-8 and malformed arguments, 502 cannot be
  called a determinate server violation merely because the model checks UTF-8
  first. Layer D must select and document the order.

- **A16 — multiple invalid article fields and refusal precedence.** The three
  run-2 POST rows have both an empty Path and an unnamed `: empty name` header.
  specs/nntp.md:905-909,930-935 explicitly requires malformed Path to be refused
  by name (`Path is not a valid path`); RFC 5537 §3.5 step 2
  (`rfc5537.txt:876-884`) requires rejection of syntactically invalid articles
  without selecting which of multiple defects determines the refusal reason.
  The recorded `441 posting failed; the article is not valid syntax` is therefore
  not a determinate basis for weakening the Path-only predicate. Retain these
  three rows evidence-open and require layer D to specify rejection precedence.
  H2c's missing-required-field prose correction remains: those eighteen cases
  did not establish a license to erase an explicitly named Path reason.

## Environmental inputs, abstraction boundaries, and driver contract

H2c fixture observations: `group_creation_window=(lo, hi)` gives an inclusive
POSIX-second interval observed around creation of all fixture groups. LIST
ACTIVE.TIMES then requires every visible fixture group once, `unattributed`, and
a timestamp within the interval; an explicit per-group `created_at` remains an
exact constraint. NEWGROUPS requires a group when the entire creation interval
is at/after its cutoff, omits it when the entire interval is earlier, and permits
either inclusion or omission when the cutoff splits the interval; exact facts
still dominate. Without a window, missing `created_at` still means no retained
creation fact and the group is omitted. These interval checks are weaker than
exact persisted-time conformance. The driver records the interval independently
of reply bytes. Legacy H2b had no
interval; replay may use the externally supplied run date as a clearly labeled
coarse bound, never derive a bound from the reply under test.

Constructor groups are `{name: flags}`. Flags: `entries` (optional explicit
`(number, id)` pairs), `watermark`, `posting` (`y/n/m`), `read_only`, `moderated`,
`moderators` (login list), `queue`, `retired`, `description`, and `created_at`
(POSIX UTC seconds). The initialization articles are **stored bytes**; membership
allocation fills unspecified entries. Explicit entries seed sparse histories.
`add_article`, `withdraw`, and `retire_group` are completed environment events,
not commands, and retain number history.

Accounts are `{login: {password, read, post, posting}}`; a string value is shorthand
for password. `read_wildmats`/`post_wildmats` are accepted aliases; lists join with
commas in their given order. Policies: `required`, `protected_only`, `posting`,
`anonymous`, `anonymous_access`, `server`, `peer` or `peers` (source addresses),
`max_inflight`, `connections`, `per_address`, `trusted` (CIDRs), `article_limit`,
`inbound_max_octets`, `clock`, `stamps`, `subscriptions`, `motd`, `metadata`,
`starttls`, `sasl_mechanisms`, and the projection inputs below. Policy observations
are explicit inputs, not values obtained from an implementation by this code.

- **E1 — transport.** Specs/nntp.md:1482-1509,1620-1660: `send` consumes a complete
  plaintext line including CRLF. `send_block` consumes the complete *wire* block
  including stuffing/terminator. After checking and updating 382, call
  `tls_established()` only when the actual transport handshake succeeds.
  Handshaking sends expect nothing. Implicit TLS starts protected immediately.
- **E2 — clock.** Specs/nntp.md:106-134,237-254: `clock` is `YYYYMMDDhhmmss`,
  `None` (no wall observation), or omitted/`"unknown"` (driver did not supply it).
  Unknown DATE accepts 111 date shape or 503; unknown YY discovery accepts 503
  or a framed success without asserting its content. Supplying a clock makes
  these exact. `created_at`, `stamps`, `acceptance_stamp` use POSIX UTC seconds;
  H2b must convert any external DTN input explicitly. NEWNEWS uses its pinned
  clock; NEWGROUPS uses the current observation, as the spec distinguishes.
- **E3 — injected bytes.** Specs/nntp.md:851-949,1215-1457: for anonymous POST
  with supplied Message-ID and Date, the model constructs Path/Injection-Info
  independently. Authenticated/generated/moderation projections also depend on
  secret metadata and exact generated fields. Supply `stored_articles[id]`
  (stored bytes) for these and `generated_id` when the source omits it and 240
  does not name it. These are explicit fixture facts, not derived cryptography.
  Without them a successful update raises an explanatory ValueError **before
  changing body/number state**. This is an integration limitation, not evidence
  that such a node response is wrong. Refusal updates require no projection input.
- **E4 — uncertain persistence.** Specs/nntp.md:741-809,974-1030: `post_outcomes`
  distinguishes accepted/refused/uncertain. A 441 uncertain allocates no *asserted*
  durable article in this oracle. Before testing later discovery after uncertain
  persistence, the environment must supply the recovered completed acceptance
  (if any) using `add_article`; do not treat uncertainty as proof of absence.
- **E5 — SASL.** Specs/nntp.md:1698-1774; RFC 4643 §2.4: canonical base64,
  mechanism names, challenge/final shapes and state transitions are checked.
  Cryptographic success/failure is intentionally abstract. PLAIN/client-first
  SCRAM syntax identifies the login without checking its proof. A driver can set
  `Conn.sasl_identity` for other abstract exchanges. The context's offered list
  is supplied through `sasl_mechanisms` (default SCRAM-SHA-256 plus PLAIN on TLS).
  `tls_exporter=True` adds required PLUS to that default; `False` excludes it;
  explicit `None` means installation is unobserved and permits PLUS on TLS
  without requiring it. `tls_version="TLSv1.2"` excludes PLUS; `"TLSv1.3"`
  permits the exporter rule, while absent version is an explicit historical
  observation limit. An explicit `sasl_mechanisms` list remains exact even with
  an unknown exporter. This does not assert an installed exporter or test
  channel binding. AUTHINFO SASL PLUS with an unknown exporter and no exact
  offered list raises an environmental RuntimeError (supply that E5 input),
  rather than claiming that either 503 or a challenge is mandatory.
- **E6 — reply consumption.** RFC 3977 §3.5; specs/nntp.md:1661-1696,2453-2478:
  call `check(status, body)` then `update(status, body)` in order; queued sends
  are allowed, out-of-order resolution raises RuntimeError. Third auth failure
  passes **both** `481...\r\n400...\r\n` in `status_line`, with `body=None`.
  Standard command expectations have boolean `multiline`. Mixed-code extension
  expectations (291/423, unknown-clock discovery) expose `multiline=True` for
  potential data; use additive `multiline_for(status_line)` after the status to
  decide whether to read a block. This is a necessary driver convention for
  those nondeterministic outcomes; it does not change the requested signatures.

## Deliberate fn policies and deviations recorded by the spec

This list separates the protocol choices modeled above from deeper mechanisms
whose outcomes are only abstract inputs to this surface oracle.

- specs/nntp.md:9-24: greeting/MODE/POST capability agree with principal posting;
  MODE READER is compatibility behavior, MODE-READER is not advertised.
- specs/nntp.md:51-93: stronger-than-RFC exact HELP keyword promise (A1 conflict).
- specs/nntp.md:106-134: no timezone database, local timezone UTC; unavailable
  clock produces 503 rather than guessing; NEWNEWS YY still pinned (stated debt).
- specs/nntp.md:136-185: legacy XOVER/XHDR remain unadvertised; XPAT advertised;
  joined patterns and stored-only XPAT Xref; ACTIVE.TIMES `unattributed`.
- specs/nntp.md:190-235: printable ASCII descriptions/MOTD, `(no description)`
  fallback, maintained empty MOTD is 215 rather than 503, pinned configuration.
- specs/nntp.md:237-317: acceptance stamps rather than Date/Injection-Date;
  conservative legacy horizon; no partial NEWNEWS block for a size limit.
- specs/nntp.md:330-416: serve-time local Xref prefix; compatibility `Bytes:` and
  `Lines:`; omit unknown creation dates; subscriptions default to visible groups.
- specs/nntp.md:419-505: exact available summaries, chosen empty encoding,
  never-reused issued numbers, explicit refresh boundaries and pinned withdrawals.
- specs/nntp.md:709-809,953-1030: named POST failures, distinct uncertainty,
  source-based duplicate/conflict identity, durable acknowledgment and poster repin.
- specs/nntp.md:851-949: injection-generated fields prepend; source preserved;
  supplied Injection-Date refused, supplied Xref refused, Path prefixed in place;
  malformed/duplicate/POSTED Path refused; no generated POSTED diagnostic;
  injection dates restricted to Gregorian cycle 2000–2399 (projection input).
- specs/nntp.md:953-1030: omitted Message-ID lacks retry deduplication; visibility
  does not settle acceptance; retry of the exact source is the reconciliation.
- specs/nntp.md:1061-1202: y/n/m only; read-only local posting does not prohibit
  relay; approved local posts require moderator login; unapproved posts queue
  rather than becoming visible under their source ID; moderator queues private.
- specs/nntp.md:1215-1457: account pseudonym, source inverse, node-added
  Cancel-Lock/Key and authorization are policy, not RFC 3977 requirements.
  Linkability, crypto assumptions, unchanged signed source and the documented
  RFC 8315 CFWS/sha512/supplied-key limitations are outside H2a's cryptography.
- specs/nntp.md:1460-1466: no supplied-Date freshness window or trusted-source
  injection check; these omissions are not converted into model rejections.
- specs/nntp.md:1482-1696: protected-only USER/PASS; three failures then 481/400;
  TLS handshake itself is outside protocol logic; fast stored verifier is not a
  password-hardening guarantee. H2a models plaintext expected credentials only.
- specs/nntp.md:1698-1774: deliberate DIGEST-MD5 omission; SCRAM-SHA-256 and
  TLS-exporter PLUS substitute; PLAIN TLS-only; 512-octet challenge cap despite
  extension permission to exceed it; printable-token SASLprep is identity.
- specs/nntp.md:1784-1982: XREDEEM is a private one-use account protocol; fresh
  connection needed to authenticate; READ/POST wildmats project away existence;
  transit authorization is separate from reader login authorization.
- specs/nntp.md:2301-2410: local capacity/address defaults, trusted exemption,
  pacing by waiting, silent first/idle close, no wildcard/mapped listener bind.
  H2a models acceptance capacity; timers/pacing/listener socket behavior are H2b.
- specs/nntp.md:2412-2478: max-inflight promises; TAKETHIS deferred/uncertain
  **436**, deliberately differing from RFC 4644's 400; sequential durable outcomes.
- specs/nntp.md:2480-2536: DEFLATE only; compression bomb bound, BFINAL refusal,
  stored-dictionary XFN-ZARTICLE; COMPRESS preset dictionaries not yet served.
  H2a models state and encoded reply shape, not compression/crypto correctness.

## Fixtures and mutation controls

27 `.txt` files are literal `[C]`/`[S]` excerpts from the specified RFC example
sections (17 RFC 3977, 6 RFC 4643, 4 RFC 6048). Each header records section and
source line range. The test re-extracts and compares each against the root RFC,
then checks and commits every server reply. These are selected **excerpts**, not
an assertion that every RFC example describes fn. ARTICLE/HEAD RFC examples use
the explicitly documented blind environment to preserve their original bytes;
separate fn-profile tests require Xref. COUNTS supplies the actual sparse counts,
not an estimate invented by the checker. Mutations are independent wire answers
from a separate fake-server state, with an unmutated control checked by the same
Conn/Expect API:

- Reissued number after withdrawal: `test_mutation_reused_number_is_caught_by_group_after_withdrawal` (specs/nntp.md:426-448,491-505).
- Wrong 423 for XOVER's 420: `test_mutation_423_instead_of_420_is_caught_by_xover_empty_range` (specs/nntp.md:143-152; RFC 2980 §2.8).
- Framed response after QUIT: `test_mutation_reply_after_quit_is_caught_by_none_predicate` (specs/nntp.md:521-528; RFC 3977 §5.4).

The stateful test runs 200 examples × at most 50 steps with generated identity
bundles, publication/withdrawal/selection/navigation/quit/reconnect, independent
issuance logs, monotone watermarks, available-or-none pinned cursors, and silence
after QUIT. Four additional properties each request 200 examples: arbitrary
binary stuffing, valid-block framing, chunk splitting, and unknown keywords.

## H2d transport observation contract

`Expect.check(status, body, eof=True)` means **clean observed peer EOF**, not an
empty read caused by timeout, a TLS/transport exception, or the final drain after
the client initiated shutdown. A permitted reply may already be committed when
EOF is detected on the next pipelined command: `update` with the same response
and `eof=True` (or `observe_eof`) commits the closure once without replaying its
semantic effect. The driver attributes that observation to the preceding reply.
Silent EOF is accepted only for structurally malformed/rejected input with the
explicit specs/nntp.md:513-518 / RFC 3977 §12.5 permission. QUIT and third
failed authentication retain their mandatory status requirements and halt state;
a silent close cannot replace 205 or 481 plus 400.
