# Separate human client submission contract

WEB-001: The optional local web-client outbox must durably bind one exact
composed article, Message-ID and NNTP target to a submission identifier before
its first network attempt. A second request, concurrent handler, or restart
must never automatically send that identifier again. Accepted, refused and
uncertain NNTP responses remain distinct; an in-flight record after restart is
uncertain, and later ARTICLE observations do not rewrite the response. The
outbox is private, single-instance and bounded without automatic deletion.
Any ambiguous local persistence failure fences new attempts. The default
in-memory mode remains available. This is a client evidence contract, not a
server acceptance or retention guarantee. The operator behavior and current
filesystem assumptions are in [the client guide](../docs/human-web-client.md).

In durable mode a user may also save incomplete editable draft fields under the
same local identifier. Saving and restoring a draft never opens NNTP or creates
a Message-ID. The first later valid Post replaces the draft with immutable
in-flight intent before network. Drafts share the outbox capacity and are not
silently evicted. A new outbox leaf directory requires an existing durable
parent; startup synchronizes that parent before posting.

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
token.

## Reader metadata lines

The node's words a reader parses, specified once here. `tools/fn_web.py`
(`parse_verdict_hdr`, `parse_enrollment_hdr`) accepts exactly these
(`tools/fn_verify.py` `parse_hdr_item` reads the `:fn-verified` items, `revoked`
from PKT-212); a line outside them is the node's
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
argument shape. A web page's fifth fact, independent verification here, is
not a node line: it is `tools/fn_verify.py check-article` run by the reader
with the reader's own keyring (verified here, failed here with the reason, or
not performed with why).

WEB-002: The web reader verifies a signed article independently with the
reader's own keyring, never the node's, says whose keyring it used, and
shows verified here, failed here with the reason, or not performed with why,
beside and never merged with the node's historical verdict.

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
in, reads, posts, follows up and cancels through it. The web reader's group
view marks a card whose parent the node answers withdrawn with the same
answer the conversation shows. `tools/docs_check.py` parses every operator
command quoted in docs/ with the ACL2 grammar (a generated book) and every
Python tool invocation with that tool's own parser, and requires every
quoted reply line to be printable by the code. A client left unresolved
because its re-send met the login or posting gate has one privileged
resolution: the operator's `store inspect MESSAGE-ID` on the stopped store,
whose accepted/absent answer is the store node's lookup (PRF-162).

## The friends' reader

WEB-003: The friends' web reader signs a person in only with the node's own
answer to their AUTHINFO login over a verified TLS channel, adds no account,
permission or decision of its own, and keeps accepted, refused, not sent and
not sure apart on every page.

`tools/fn_reader.py` is a hosted client: one process serves many signed-in
browsers, each on its own NNTP connection logged in with that person's
credentials (RFC 4643 section 2.3, after RFC 4642 STARTTLS with the node's
certificate verified). A `281` is the only way in; `481` is "name and
password don't match"; a connection or handshake failure is "can't reach
the server" and never a wrong password. The browser side is HTTPS, or plain
HTTP bound to loopback behind a TLS proxy; the process refuses anything
else. The password is held in memory for the session and never written to
a file, URL, page or log.

The node decides and the reader shows: which groups the login is served
(LIST ACTIVE, LIST COUNTS, LIST NEWSGROUPS, GROUP; an access rule, NNT-046,
hides a group exactly as an absent one), whether a post is accepted, held
for a moderator (the group's LIST ACTIVE status `m`, NNT-047), refused with
the node's reason, or uncertain (books/nntp-post.lisp's 441 lines), whether
an approval (the moderator's POST of the envelope's proto-article with
Approved, RFC 5537 section 3.5.1) is taken, and whether a cancel withdraws
(the same account, SEC-006: after the node's `240` the reader asks `STAT`
of the target and reports `430` as removed, anything else as still shown).
Threading (References, RFC 5536 section 3.2.10), the unread marks and the
display name are the reader's own and decide nothing. Each submission's
exact lines and Message-ID are written to the reader's state before the
POST; a lost answer is settled only by re-sending those lines under the
same Message-ID (NNT-019), and a failure before any byte of the article
was sent is "not sent" and may be retried with the same lines.

Local policy, not an RFC requirement: the form token on every POST, the
Origin and Sec-Fetch-Site checks, a pause after eight failed sign-ins from
one address in fifteen minutes, and the per-request display bounds (one
window of 200 numbers per group page, 1,000 per thread page, 80 articles
per thread) bound this client's work per request and never what the node
stores (D27).

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
(`Connection: close`), one connection served at a time by the face's
thread, a request completed within 15 seconds, the idle life of a session
(`[web] idle_seconds`, 12 hours) and the number kept (`[web]
max_sessions`, 64; each holds one owner connection).

### The reader in the release

WEB-004: The release carries the friends' web reader as its own service
beside the node, and it reaches the node only as an NNTP client. It is
`clients/bin/fn-reader` (HST-029), installed by `install.sh --reader` under
its own account and folder, which the node folder (store, control socket,
logins, keys) does not admit; the systemd unit also makes the node folder
inaccessible. It dials the node's implicit-TLS port (`tls_port`, RFC 8143;
port 563 or `--tls`) or its reader port with STARTTLS (RFC 4642), verifying
the certificate before any login octet. It listens on loopback behind an
HTTPS proxy (`--proxied`: the proxy's last `X-Forwarded-For` entry is the
browser's address, cookies are `Secure`). A friend with an invitation code
makes the account through the node's own `fn redeem` (ACL2's
`fn-redeem-step`; the code and login shape-checked so neither is an option,
the password on standard input), and the reader never sends more than
`--node-failures-per-minute` refused logins or codes a minute, below the
node's `exposure-auth-failures`, because every friend shares its address.
The threat model is docs/operator-internals.md, "The friends' web reader".
