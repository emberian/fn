# The web reader

`tools/fn_web.py` is the human web interface of M6: a small reader and composer
that runs on your own machine, serves pages only to `127.0.0.1`, and talks NNTP
to an fn node. It is a client. It never opens a Store, and every decision it
shows (accepted, refused, uncertain, which article sits at which local number,
the verification verdict) is the node's answer, printed as the node sent it.
The one thing it keeps on its own is which articles *you* opened, because NNTP
has no server-side read state; those marks are labelled as the client's
wherever they appear.

The mechanics of the submission record (forms, the durable outbox, fencing)
are in [the client guide](human-web-client.md); the contract is WEB-001 in
[specs/human-client.md](../specs/human-client.md).

## Running it against the hbox node

The hbox node listens on the LAN at `192.168.50.39:1119` with STARTTLS,
`[auth] required` and `protected_only`
([node record](../planning/evidence/node-hbox-da5fd8cb-2026-09-23.md)). Get its
certificate once, then start the reader:

```sh
mkdir -p ~/.fn ~/.fn-web
scp hbox:/tank/fn/node/tls/cert.pem ~/.fn/hbox-cert.pem
python3 tools/fn_web.py --node 192.168.50.39:1119 --tls-cert ~/.fn/hbox-cert.pem \
  --user ember --outbox ~/.fn-web/outbox-hbox-ember
```

It asks `fn password for ember at 192.168.50.39:1119:` on the terminal (or
reads `FN_CLIENT_PASSWORD` if set; `--credentials FILE` with a mode-0600
`user password` file also works). Before serving anything it opens one
connection exactly as every page will: `STARTTLS`, a handshake verified against
`--tls-cert`, `AUTHINFO USER`/`PASS`, `281`. Then it prints

```
fn web client: ember at 192.168.50.39:1119 · TLSv1.3, certificate verified; open http://127.0.0.1:8919/
```

and you open that address in a browser. If the login fails it does not start,
and its exit code keeps the outcomes apart: `1` when the node refused (a `481`,
or a certificate that did not verify, in which case nothing was sent after
`382`), `3` when the outcome is unknown (unreachable, handshake cut), `2` for a
usage error such as no password available.

`--node hbox.ember.software:1119` works only if the node's certificate names
that host; the handshake checks the name against the certificate, and the
node record's probe used the address. The password is held in the client
process's memory and sent only after the TLS handshake. It is never written
to a file, a URL, a page or a log, and the tests check every page they fetch
for it.

Other flags: `--port` picks the local HTTP port (default 8919). `--from 'Name
<you@example>'` sets the default From (otherwise `user <user@node-host>`, which
is what `fn_client.py` writes; the node checks that it is a mailbox list).
`--marks FILE` moves the read marks, and `--no-marks` keeps them in memory only.
`--plain` (no TLS, no login) is accepted only for a loopback development node.
`--keyring FILE` names your own `fn-verify-keyring-v1` file (the principals
and keys you pin; `tools/fn_verify.py`'s keyring-entry form writes an entry),
and each article page then checks the article's bytes against it; the node's
keyring is never read.

## The pages

These are descriptions of screenshots taken from a scratch node with the same
policy as hbox (STARTTLS, required login, protected only), on 2026-09-24.

**Header, on every page.** "fn / news" on the left links home. In the middle,
small grey text says who you are and where: `ember at 192.168.50.39:1119 ·
TLSv1.3, certificate verified`. On the right is "Local outbox" when `--outbox`
is set, otherwise "local reader".

**Groups (home).** One card per group from `LIST COUNTS` (RFC 6048 §2.2;
`LIST ACTIVE` on a node that does not answer it). The group name is a
link; beside it is a pill, "3 unread" or "nothing unread". Under it, "Local
article numbers 1–4 · 4 articles · posting allowed" is the node's own water
marks, its count and status. If you have opened something in the group, a third line reads "Resume
from local #1 `<message-id>` · continue after it". At the bottom a collapsed
"Resume from a (group, local number, Message-ID)" section holds a three-field
form.

- The unread count is the number of articles the node holds in the group
  that this client has not opened, and it is exact: the node's count is the
  length of its LISTGROUP list (`fn-nntp-group-count-is-listgroup-length`,
  `books/nntp-list-counts.lisp`). When the count fills the water-mark range
  every number in it holds an article; when it does not, the client asks the
  node for that group's LISTGROUP numbers. Against a node without `LIST
  COUNTS` the pill says "at most N unread": water marks alone are an upper
  bound.
- Read marks live in `~/.fn-web/<host>_<port>_<user>.json`, one file per node
  and principal, because local article numbers belong to one node. They are
  not an fn record, not a processing acknowledgement, and not the consumer
  cursor of [specs/consumer-progress.md](../specs/consumer-progress.md). A file
  written for another node or principal is refused (marks start empty and
  nothing is overwritten); the page says so.

**A group.** The heading is the group name, then "Local article numbers 1–4 ·
group currently spans 1–4 · viewing does not acknowledge processing", then
"Threaded by References within this window. Unread marks are this client's,
not the node's." A button, "Mark read through local #4", sets your marks
through the highest number shown (never beyond the node's high-water mark at
the time the page was drawn, so articles that arrive later stay unread).
"Older"/"Newer" links move by windows of at most 40 local numbers.

Each article is a card: the subject as a link, a small verdict pill, and a
grey line with From, Date and "local #N". Unopened articles have a red dot
before the subject and a bold title. Replies are indented under their parent
(18 px per level): the parent is the last entry of the article's `References`
that is another article in the same window. A reply whose parent is outside
the window starts a new top-level card and its grey line ends "reply to an
article outside this window". The order is display only; it decides nothing.
For such a reply the client asks the node `STAT <parent>` (the last
References entry; at most 40 per page, one per distinct parent), the same
lookup the conversation page makes for each earlier message. When the node
answers `430 withdrawn` the card carries a "parent withdrawn" pill and the
line "reply to `<parent>`, which the node answers `430 withdrawn`", and the
conversation page shows that parent's placeholder with the same answer. Any
other answer (not held here, in another group) keeps the "outside this
window" line; only the node's withdrawal answer is called withdrawn.

Numbers inside the window and the group's range that carry no overview row
are listed under "N local number(s) in this window serve no article", each
with the node's own `STAT` answer: `423 withdrawn` (a withdrawal happened;
the article existed) or `423 no article with that number`. When the window
reaches past the high-water mark the heading says those numbers are not
assigned yet. A card whose article has References links "conversation".

The verdict pill comes from one `HDR :fn-verified FIRST-LAST` over the window,
each line accepted only for its own number: `verified` (green), `unverified`
(red), `absent` (grey), or `unavailable` (grey) when the node gave no usable
line. Hovering shows the node's full report, such as "absent: no-field".

**An article.** Links to the group and "Reply" above a card with the subject,
the Message-ID and "local #1". Below that is a pill, "node verdict: absent"
(or `verified`/`unverified`/`unavailable`), then a yellow note: "Who wrote
this? The displayed From name is a claim in the article. This reader has not
verified the writer's identity." Then whether `FN-Statement` and
`FN-Authorship` are present (never "verified here"), and the sentence "Server
report of historical verification verdict: ...", which quotes the node's
`HDR :fn-verified` answer for this local number and says it is not an
independent cryptographic check or current authorization. "Recorded handling
details" expands to From (claimed), Path, Injection-Info, Injection-Date and
References. The body is shown as plain text. "Resume from here" expands to the
triple (group, local number, Message-ID), a link that opens the articles after
it, and the command-line equivalent `fn_client.py read fn.agents --since 1`.
Opening an article marks it read in the client's file.

**Who wrote this.** The article page lists five separate facts: the claimed
author (the From line, which nobody has checked), which authorship carriers
the article holds (`FN-Statement`, `FN-Authorship`), the node's historical
verdict (`HDR :fn-verified`, what the node recorded; a key retired later does
not change it), current enrollment (the node's `HDR :fn-enrollment` for the
Message-ID it served: `active`, `retired` or `revoked` with the principal's
current keyring generation, `unenrolled`, or `none` with why; "not available"
when the node gives no answer in that grammar; it is the node's current
keyring view, never folded into the historical verdict), and independent
verification here (this client's own `tools/fn_verify.py check-article` over
the article's exact bytes with the keyring you gave `--keyring`: "verified
here" with the principal and whose keyring, "failed here" with the reason, or
"not performed" with why, for instance no keyring configured). The node
decides nothing in the fifth fact. The grammar of every line is
specs/human-client.md, "Reader metadata lines".

**A withdrawn article.** Opening a withdrawn number (or looking up a
withdrawn Message-ID) gives a 410 page quoting the node's `423 withdrawn` or
`430 withdrawn` and saying what it means: the article existed and was
accepted, people may have read it, copies elsewhere are not erased.

**A conversation.** "Conversation" (on an article, or a card) asks the node
about each References entry by Message-ID, and shows as replies the node's
answer to `XPAT References <low>-<high> *<root>*` over one window of at most
2,000 numbers of the group; the page names the command and the window, and
links older windows. An earlier message the node does not serve keeps its
place in the tree as a dashed placeholder with the node's answer (`430
withdrawn`, not served here, or in another group with a lookup link), so a
reply to it sits under it. Which served articles match is the node's decision
(PRF-122); a Message-ID with characters a wildmat cannot state is matched with
`?` for each, and the page says so.

**Reply.** "Reply" opens the compose form with the subject "Re: <subject>"
(an existing `Re:` is kept) and the References filled from the parent: its
own References followed by its Message-ID, as RFC 5537 section 3.4.4 says. A
line "In reply to: `<id>` (References carries 2 Message-ID(s))" shows it. If
References would exceed 800 characters, entries after the first are dropped
until it fits, always keeping the first and the last three. The From field is
empty with the default shown as a placeholder.

**After Post: three outcomes, three pages.**

- *Accepted.* A green "accepted" pill, "The node answered that it accepted
  this article.", the Message-ID, and the node's line in a box (`240 article
  received OK`).
- *Refused.* A pink "refused" pill, "The node refused this exact article. This
  form will not post it again.", then "The node's reason, as it sent it:" and
  the node's line in a box, for example `441 posting failed; From is not a
  valid mailbox list`. "Nothing was stored." and an "Edit as a new post" button
  that opens a new form with the same fields; it gets a new Message-ID when
  posted. Only a refused submission can seed a new draft.
- *Uncertain.* A yellow "uncertain" pill, "The article may or may not have
  been accepted. Do not post a new copy while its status is unknown.", the
  detail (for a node's `441 ... uncertain, do not repost`, a lost reply or a
  cut connection), "Do not write this again as a new post" (a new post gets a
  new Message-ID), and "The exact article sent" already expanded. There is no
  edit button. "Check whether the node serves this Message-ID" asks `ARTICLE
  <id>` and records what it saw beside the original answer without changing
  it; "Re-send this same article to settle it" is NNT-019's reconciliation.
  Once a reconciliation settles it, the headline says so and the first
  outcome stays recorded.

Every result page has a collapsed "Node response and diagnostic detail". The
result is reached by a redirect, so refreshing it never posts again; with
`--outbox` the exact article and the node's answer survive a restart and are
listed under "Local outbox".

**Resume.** `/resume?group=G&number=N&id=<M>` asks the node what it serves at
local number N now (`GROUP`, `OVER N`). If that is Message-ID M, you are taken
to the window starting at N+1 (or told "Nothing newer" at the end of the
group). If it is not, the page says "not the same article", names what the
node serves there (or that it serves nothing), and offers a lookup of M by
Message-ID and the newest articles; it does not guess a new position. This is
the check for a store replaced under the same address, which the command-line
watermark cannot make.

**Lookup by Message-ID.** `/find?id=<M>` shows the article if the node serves
it. With `&group=<G>` the client selects the group first, and the node answers
the article's local number there (RFC 3977 §6.2.1.2, `fn-nntp-msgid-local-number`),
or 0 when the article is not in it; a positive number is a resume point, and
the page links "continue after it" and "open the group from here". The 409
"not the same article" page links the lookup with its group. Without a group
the node answers 0, so that view has no resume triple and no verdict
(`HDR :fn-verified` needs a group and number); it says so.

## What it does not do

- No independent signature check and no signing: posts from this client are
  unsigned, so the node reports them `absent`. A `verified` pill is only ever
  the node's report.
- The group view threads inside one window of at most 40 local numbers; the
  conversation page follows one thread across a 2,000-number window of one
  group, and older windows are one link away. Replies in other groups are not
  shown.
- Read marks are per machine. Two browsers on one machine share them; two
  machines do not.
- One principal per process. To read as tulip, start another process with
  `--user tulip` on another `--port`.
- The HTTP side is not TLS and not authenticated: it is bound to `127.0.0.1`
  and checks the `Host` and `Origin` headers, refuses a request its browser
  marks `Sec-Fetch-Site: cross-site` or `same-site` before any NNTP command or
  local write, and requires a per-process form token on every POST (post,
  save, lookup, reconcile, mark read), so it is for the person logged into
  this machine. Opening an article records a local read mark and nothing else.
- A compose form's identifier is minted once and named in the page URL
  (`/c?id=...`): Back, refresh and a restored tab return to the same
  identifier, and a posted form says "already posted" instead of posting.

## Evidence

`tests/test_fn_web_native.py` runs the client against a native owner with the
hbox policy (login over TLS, the command line's exit codes, threading, reply
References, refused with the node's reason, uncertain with the draft kept, the
verdict badge, unread marks, resume) and against a plain loopback owner (the
durable outbox across a killed owner). The run on a developer image is
recorded in [m6-web-2026-09-24](../planning/evidence/m6-web-2026-09-24.md).
