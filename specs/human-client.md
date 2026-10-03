# Separate human client submission contract

WEB-001: Deferred, retired on 2026-09-28 with `tools/fn_web.py`: an optional
local web-client outbox that durably binds one exact composed article,
Message-ID and NNTP target to a submission identifier before its first
network attempt, and never sends that identifier again automatically. On the
node's own web face (WEB-005) a post is the node's served POST on the
session's own connection, so the one ambiguity left is a lost HTTP reply,
which no outbox on the browser's side settles. `tools/fn_client.py`
`post --draft` / `reconcile` keeps the command-line contract (NNT-019).

## The daily reader

NNT-021: The reader shows what the node serves around a hole, a conversation
and a search as the node's answers within a stated scope, and keeps a post's
provenance facts apart. Inside a group window every number in the node's
current range that has no overview row is shown with the node's own `STAT`
answer: `423 withdrawn` (C3, `books/nntp-control.lisp`) is shown as a
withdrawal that happened, never as absence, and a number with no article is
shown as the node's other answer; numbers above the high-water mark are not
yet assigned. A conversation asks the node about each References entry by
Message-ID and shows each one's answer (served, `430 withdrawn`, not served
here), and shows as replies exactly the lines of the node's
`XPAT References <low>-<high> *<root>*` over one stated window of one group; a
search is the node's `XPAT` over one stated window. The node decides which
served articles are in that scope and match: the reply is XHDR's lines for the
numbers in the range whose served article renders the field and matches, and
a withdrawn number is never one of them (PRF-122,
`books/nntp-search-scope.lisp`). The client keeps no index, builds no
visibility decision and states the window and the command on the page; a
Message-ID with characters a wildmat cannot state is matched with `?` for each
and the page says the match may include a near-identical identifier. An
article page shows separately the claimed From, which authorship carriers are
present, the node's historical verdict (`HDR :fn-verified`, what the node
recorded at acceptance, unchanged by a later key retirement), the node's
current enrollment of that verdict's principal (`HDR :fn-enrollment`, the
node's current keyring view, a separate fact), and the reader's own
independent verification with the reader's own keyring (or why it was not
performed); the grammar of each line is "Reader metadata lines" below. An uncertain submission, including an in-flight intent found
after restart, is settled only on the person's explicit request, by NNT-019's
reconciliation: the same bytes under the same Message-ID, the answer recorded
beside the original, which never changes. A compose form's identifier is
minted once and named in the page's URL, so Back, refresh and a restored tab
return to the same identifier and a posted form says so instead of posting
again. Local HTTP refuses a request its browser marks as coming from another
site (`Sec-Fetch-Site`) before any NNTP command or local write; reading never
posts, and the lookup and the re-send are form POSTs with the per-process
token. The web reader that did this, `tools/fn_web.py`, was retired on
2026-09-28; the node's own face (WEB-005) has no conversation or search page
yet.

## Reader metadata lines

The node's words a reader parses, specified once here. A reader accepts
exactly these (`tools/fn_verify.py` `parse_hdr_item` reads the `:fn-verified`
items, `revoked` from PKT-212); a line outside them is the node's
non-answer, shown as unavailable, never as a status. Each HDR reply is RFC 3977
section 8.5's `225` with one line `N ITEM` (N the local number, or `0` for the
Message-ID form).

`HDR :fn-verified` (range, current article or Message-ID; the historical
verdict the Store recorded at acceptance, `books/stx-verify.lisp`
`fn-stx-verified-item`, `books/stx-reader.lisp` `fn-stx-reader-item`):

    verified HEX keyring G        the signature verified for principal HEX under keyring generation G
    verified legacy keyring G     an earlier record whose detail is not a principal id
    revoked HEX keyring G         the principal was revoked under generation G when checked
    carried HEX                   authorship evidence naming HEX carried, not verified here
    unverified REASON keyring G   REASON: malformed | ref-mismatch | signature | no-field | unknown
    absent REASON                 REASON: the same words, or no-record (no verdict is recorded)

HEX is the 64-hex-digit principal id and G a decimal generation. The verdict
record names the principal and keyring generation and never the login that
posted: that is by design (`books/login-binding.lisp`, the verdict record
comment), since the login binding is a separate, logged decision.

`HDR :fn-control <msgid>` (the withdrawal status of a control or superseding
article, `books/nntp.lisp` `fn-nntp-control-hdr-response`,
`books/control-served.lisp` `fn-ctl-control-item`):

    executed withdrawal TARGET author      TARGET withdrawn on the author basis
    executed withdrawal TARGET authority   TARGET withdrawn on the node's authority
    owed                                   the withdrawal is due and not yet executed
    declined REASON                        not executed, for REASON (a lower-case word)
    none                                   the article withdraws nothing

A retrieval of a withdrawn article answers the response text `423 withdrawn`
(by number) or `430 withdrawn` (by Message-ID) instead of the plain "no
article"; `withdrawn` is a response text, not an HDR item.

`HDR :fn-enrollment <msgid>` (Message-ID form only, like `:fn-control`; the
node's current keyring view of the principal the recorded verdict names,
decided in ACL2 from the connection's pinned view; a separate fact from the
historical verdict, which a later rotation or revocation never changes):

    active HEX keyring N      the verdict's key generation is HEX's current enrollment, N
    retired HEX keyring N     HEX enrolled again since; its current generation is N
    revoked HEX keyring N     HEX's newest keyring entry is its revocation, at generation N
    unenrolled HEX            the node's keyring view holds no entry for HEX
    none no-record            no verdict is recorded for the article
    none no-principal         the recorded verdict names no principal
    none no-keyring-view      the connection pins no keyring view

`430` answers a Message-ID the pinned view does not serve and `501` any other
argument shape. Independent verification is not a node line: it is
`tools/fn_verify.py check-article` run by the reader with the reader's own
keyring (verified here, failed here with the reason, or not performed with
why).

WEB-002: Deferred, retired on 2026-09-28 with `tools/fn_web.py`: a web reader
that verifies a signed article independently with the reader's own keyring,
never the node's, says whose keyring it used, and shows the result beside and
never merged with the node's historical verdict. A check with the reader's
own keyring is by definition not the node's, so the node's own face does not
make it; `tools/fn_verify.py check-article` still does, from the command line.

## Everyday tools over protection

NNT-032: An ordinary reader reaches a protected node with the tools people
use, and every command the documentation names exists with the grammar it
gives. The node offers, besides STARTTLS on its listener (RFC 4642 section
2.2), an implicit-TLS listener (`[listener] tls_port`, the separate-port
practice RFC 4642 section 1 describes, a local policy) only beside a loaded
certificate and key, on a port of its own, and a connection on it is the
STARTTLS session after its handshake: no STARTTLS label, 502 to STARTTLS,
AUTHINFO under `protected_only` from the first command (PRF-162,
`books/served-implicit-tls.lisp`). tin, which speaks only that form, logs
in, reads, posts, follows up and cancels through it. `tools/docs_check.py` parses every operator
command quoted in docs/ with the ACL2 grammar (a generated book) and every
Python tool invocation with that tool's own parser, and requires every
quoted reply line to be printable by the code. A client left unresolved
because its re-send met the login or posting gate has one privileged
resolution: the operator's `store inspect MESSAGE-ID` on the stopped store,
whose accepted/absent answer is the store node's lookup (PRF-162).

## The friends' reader

WEB-003: The friends' web reader signs in only by the node's AUTHINFO answer
and decides nothing: it is the node's own web face (WEB-005), whose session
exists only after the node answers `281` to the AUTHINFO its sign-in sent on
the session's own reader connection (RFC 4643 section 2.3), bound to that
connection and login (`fn-web-sessions-bound-by-281`, PRF-339). `481` is
"name and password don't match". The face adds no account, permission or
decision of its own.

The node decides and the face shows: which groups the login is served (an
access rule, NNT-046, hides a group exactly as an absent one), whether a post
is accepted, refused with the node's reason, or not sure (keeping those
apart on the page), and whether a removal
withdraws (the node's cancel, SEC-006: after the node's `240` the face asks
`STAT` of the target and reports `430` as removed, anything else as still
shown). An account is made by the node's XREDEEM. The password is carried in
the command octets of its one request and kept nowhere.

Not built on the face: a thread view, search, read marks, drafts or an
outbox, moderation approval pages and the reader's own signature check. The
Python friends' reader, `tools/fn_reader.py`, which had these as a separate
service, was retired on 2026-09-28.

### The node's own web face

WEB-005: The node serves its own web face: an HTTP/1.1 listener in the
native image (`[web] port`, loopback by default; HTTPS itself with
`[listener]`'s certificate when `[web] tls = true`, or behind a TLS proxy on
the same machine with `[web] proxied = true`), in which every decision is
ACL2's and no Python or other process stands between the browser and the
node. The request is framed and parsed in place from a byte buffer
(`books/web-request.lisp`: RFC 9112 grammar, one pass, at most 2N work for
an N-octet head; the operator's head limit, 431 past it; the body limit the
owner's article limit implies, 413 past it; chunked transfer coding is 501,
a stated local policy because the face accepts only its own HTML forms).
After article submission, the browser preserves the core's outcome distinction.
The owner's exact uncertain 441 reply and internal 403 fault produce a
503 uncertainty page advising inspection before another submission; ordinary
441 posting refusal remains definite refusal. A numeric 4xx class alone cannot
settle the article's durable outcome. Removal verification distinguishes STAT223
(article present), STAT430 (article absent), and every other response (check
uncertain); a failed check never says the article is still present. If an
invitation password exchange loses its reply, the account may already exist:
the page preserves that uncertainty and recommends signing in with the chosen
credentials before reusing the invitation.

A browser session is bound to a logical reader connection of the owner,
opened through the owner's own exposure admission for the browser's address
(the socket peer, or with `proxied` the proxy's last `X-Forwarded-For`
entry); sign-in is the node's AUTHINFO on that connection (RFC 4643), so the
login pacing is the owner's `exposure-auth-failures` rule; an account is
made by the node's XREDEEM; every page is rendered by ACL2 from the replies
the node gave the session's own connection, so a session reads exactly what
its login reads over NNTP (`account access` included); a post is the
authored article (D25) through the served POST path; a removal is the
cancel control article through the same path, checked with STAT (430).
Pages escape every octet that came from a reply or a form
(`books/web-render.lisp`: no `<`, `>`, `"` or `'` and every `&` an entity,
outside the renderer's own vocabulary of markup), carry
`Content-Security-Policy: default-src 'none'`, no script and no font from
anywhere, and the static newsreader's look (`site/style.css`). The session
table (a token drawn from the OS CSPRNG, the connection, the login, a CSRF
token, the last use) is node-local and never logged; no password is kept.

Local policy, not an RFC requirement: one request per connection
(`Connection: close`), one registered I/O actor multiplexing at most `[web] max_sessions` HTTP
connections (connections beyond those slots remain in the kernel backlog),
a request completed within 15 seconds, the idle life of a session
(`[web] idle_seconds`, 12 hours) and the number kept (`[web]
max_sessions`, 64; each holds one owner connection).

Q10d, WEB-005: `GET /health` and `HEAD /health` use the same running owner,
with no account/session or second image process. ACL2 projects the fixed
scheduler mode, whether free space was observed, and whether checkpoint
publication is deferred. `200` requires observed space, mode `:ok` or
`:slow` (the existing PRF-358 disk-health policy), and no deferred checkpoint.
Full/stalled disk, deferred publication, malformed or unobserved inputs
answer `503`; the fixed plain-text body is at most 23 octets and never
copies counters or peer names. `HEAD` suppresses that body while preserving
its length. This local readiness policy does not replace the full operator
health verdict and does not claim namespace, profile, route or receipt
health. The existing HTTP parser, request bounds and listener TLS apply.

### The reader in the release

WEB-004: The release turns on the node's own web face with
`install.sh --reader` (a `[web]` table in `fn.toml`), with no reader service,
account or Python beside the node. It appends `[web]` with
`port = 8920`, `host = "127.0.0.1"`, `proxied = true`, `site` and `domain` to
the node's `fn.toml` once `mission` has written it (a table already there is
left as it is), and the node reads it when it starts
(`books/web-config.lisp` `fn-web-config-plan`, PRF-340). HTTPS is Caddy on the
same machine (`share/fn/caddy/fn-web.caddy`), or the node itself with
`tls = true`. The release's `clients/` carries no service (HST-029). The
threat model is docs/operator-internals.md, "The friends' web reader".

WEB-006: The web I/O actor retains each request's socket, private octet buffers, event flow,
partial output offset and logical reader continuation. A stalled TLS handshake,
partial head/body, queued POST completion or cold payload read yields to other
connections; no connection creates a thread. One fixed semantic worker executes
owner chunk/render/cold operations that can wait for publication or scheduler
admission, through a mailbox of at most one operation per admitted HTTP record.
Cancellation retains the exact request/CID/plan until that activation returns,
independently of disposing its transport. Requests sharing a browser session
serialize their semantic flows on its one owner connection. Completed HTTP pages
are sent in windows with the exact Content-Length; a deadline, cancellation or
uncertain submission closes without an accepted/refused HTTP outcome. Socket
cleanup and cold publication cancellation do not imply that an issued physical
read has ended. The owner's generated actor lifecycle retains the web actor
through its physical join before shared service close.

The native page path requests a validated immutable segment plan from
`fn-wss-page`, then counts and emits it through `fn-web-host-page-step`
(`books/web-page-cursor.lisp`) outside the owner section. Each step has fixed
cursor fuel and a window of at most 4096 octets. A short encoded header may
add the existing bounded RFC 2047 decode; long headers remain span reads.
Count mode allocates no output list. GET emits the counted page from the same
retained reply and plan; HEAD counts the page and sends its head alone. It
never constructs a complete HTML output buffer. SCN-1105 compares all segment
kinds and native partial writes to the existing segment reference.

The cursor is presently a program boundary. Its guard verification and
refinement to `fn-wr-seq` are planned in PRF-1277; raw equality witnesses do not
extend the existing web proofs to it. Exact captured read/post reply events run on the fixed semantic worker without
consulting or writing the live session table (PRF-1279, admission pending).
Stateful owner admission and session decisions still run under the owner lock.
Reply segment construction remains a full worker operation, and a long
owner operation can therefore delay stateful event handling;
this is not a full semantic-event fairness guarantee. The fixed semantic
worker also serializes operations that need that worker.

This scheduling contract does not yet establish full allocation funding.
The NNTP reply backing buffer, page segment spine and text, bounded decoder,
head/window/cursor and job capture remain the actual tariff frontier. Eliminating
the complete HTML output buffer does not fund the retained input or plan.


The native ARTICLE/OVER/LIST paths scan rendered NNTP windows into virtual
metadata (`books/web-reply-stream.lisp`) and replay the captured persistent
plan for the source windows requested by the page cursor. ARTICLE keeps five
header spans/body offsets and bounded ownership metadata; OVER keeps at most
its existing100 requested number rows as spans; LIST keeps only status/block
offsets and creates one row plan while traversing the source. Long source fields
are not copied into row metadata, and group count does not grow Web's retained
row plan. Count and emit use the same capture. A saved renderer tail resumes
monotone spans; backward field/link seeks restart it without another command.
The final response pin survives both HTML passes and the HTTP suffix or actual
semantic disposal; preliminary GROUP status pins settle before the next command.
Cold replay retains the exact plan and deadline. SCN-1113/1114/1115 compare exact
reference HTML and the connected native window/pin consumer. These program
boundaries await guard/refinement and matching image (PRF-1283/1284/1285).

This removes Web's additional full NNTP input and row-list collectors. The
original NNTP ARTICLE producer still realizes payload and complete section
block, LIST ACTIVE still realizes its complete reply, and some OVER paths
realize full NOV/projection replies before capture. Those upstream producers,
the supported numeric representation, working cursor/decoder/renderer vectors,
repeated physical reads and mailbox captures require a qualified complete
tariff. Native output grants do not cover Web implicitly. Stateful owner
admission can still delay the fixed worker/network event flow.


Captured POST/remove BEGIN (PRF-1290 planned, SCN-1119) now looks up/touches
its session and handles expiry in the owner section, then returns a core-selected
private-begin action for the existing fixed semantic worker. That worker runs
the exact same-site/session/CSRF gate and authored POST/cancel preparation
outside O. Missing-session requests keep their immediate refusal. PRF-1279/1290
equivalences and reached witnesses admit in a fresh ACL2 source world
(`planning/evidence/web-private-source-2026-10-03.md`); certification and
composed native/browser execution remain pending. Raw classifier/held-worker
scheduling passes with a healthy owner event progressing. Body preparation still runs to completion on one worker;
full body/working/capture allocation is unpriced, and stateful owner admission
can still delay events. No second worker or full fairness warranty.


Streaming Web command and await plans enter a fixed-worker `:ready` phase before
replay capture. `fnn-owner-ready-plan-step` resolves one shared ARTICLE framing
preflight quantum; yielded/raw and cold continuations are retained without
publication. Only READY stores the immutable original plan for both HTML passes.
No preflight/selection scan is replayed during count or emit. The consumer pairs
with Access source e7624ab8a/e41b22c21 and Served a3bd4513f; its raw adversarial
owner adapter checks cold/yield/READY capture custody, not producer semantics.
Actual composed source execution and complete Web tariff remain pending.


Shared ARTICLE producer/native Web composition: Access2a0f46790 byte-window
entry now supplies exact-W parts, with immutable pending dot fragments. The
actual shared producer bodies plus native Web scan/replay/count/write consumer
pass5,000 dot-leading lines, cold replay, partial drain and exact HTML/count/pin
receipt. The old work-only producer fails this same fixture with5,408 output
bytes for W4,096. Recording arena/owner/cold/I/O seams remain; full native
source-loaded browser execution and qualified Web funding are not established.


The host-reached ARTICLE/OVER/LIST program functions and Web window wrappers
now admit and execute in the same actual ACL2 source stobj world as the private
reply/gate functions. tests/acl2/web-stream-consumer-source-tests.lisp compares
complete reference page plans with virtual scan/count/emit under chunk1/2/7/4096
fixtures. Guard/refinement and complete endpoint/funding qualification remain
open; concrete-fill invariant-risk warnings are retained in the source receipt.

A closed HTTP continuation cannot submit another semantic job. Terminal disposal
requires the exact outstanding job's return; cancellation alone leaves its
captured POST, response and replay references live. The sole disposal activation
then clears input/output, authored POST state, page state and saved response
plans before releasing the response's scalar loan and pin. Failed cleanup keeps
its exact cold-read identity in the debt record. Discard of these references is
a lifetime receipt; it does not establish a complete physical heap tariff.

The Web root close hook retains the face until its actors have ended, the job
mailbox is closed and empty, and every retained connection has a terminal
semantic receipt with no cleanup debt. Listener disposal proceeds independently;
its actual close receipt must be `:closed`. A failed or torn listener attempt
retains the face and is never retried. A Web close-hook failure blocks successful
Store teardown rather than discarding the only record of unfinished custody.
