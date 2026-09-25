# Reader spike: the human surface on a developer image — 2026-09-25

Spike lane `spike/reader` (D28), from `spike/mega` `0e2173ab`. Python client
and harness only: `tools/fn_web.py`, `tests/test_fn_web.py`,
`tools/spike_reader_node.py`, `tools/spike_reader_drive.mjs`,
`tools/nntp_wire_log.py`, `tools/spike_tin_drive.sh`, `tools/v0_matrix.py`.
No book, host or image source changed, so no farm run.

## The run

- Image: the large-article lane's developer image, built on hbox from
  `4d75b021` (merged into dev before `0e2173ab`), copied to
  `/tank/fn/scratch/spike-reader/tree` with its launcher repointed.
  `fn-host-developer.core` SHA-256 `7354b90e…2ce1`. OpenSSL 3.5.8
  (`FN_OPENSSL_PREFIX`), ACL2 w28 `acl2-literal-4g` for `principal set-password`.
- Node: `tools/spike_reader_node.py` under `systemd-run --user
  --unit=spike-reader-node -p MemoryMax=24G`: Store `fn.agents fn.test`,
  STARTTLS listener on 127.0.0.1:11919, `[auth] required`, `protected_only =
  false` (so tin can log in without TLS), control socket; logins `ember` and
  `guest` with posting; one hybrid key per login, enrolled with
  `hybrid-enroll` at generations 1 and 2. The scratch passwords in
  `hbox/node1.log` belong to this throwaway node only.
- Web client: `fn_web.py` SHA-256 `dbe472c9…387f` under `systemd-run --user
  --unit=spike-reader-web -p MemoryMax=8G`, STARTTLS verified, login `ember`,
  durable outbox, `--signing-key node1/keys/ember`, `--operator-store`.
- Browser: Playwright 1.62.1 Chromium on the laptop over `ssh -L 8919`,
  `node tools/spike_reader_drive.mjs`, desktop 1100 px and phone 390 px.
  Screenshots, page HTML and `drive.json` are in
  `spike-reader-2026-09-25/`; hbox logs in `spike-reader-2026-09-25/hbox/`
  with `SHA256SUMS`; tin panes in `spike-reader-2026-09-25/tin/`.
- Fake-node suite: `python3 -m unittest tests.test_fn_web`, 33 cases pass on
  macOS (30 existing, 3 new in `ReaderSpikeTests`).

## What works, and which node command answers it

| Surface | Observed | Node command |
| --- | --- | --- |
| Group list with unread | `7 unread` after one article opened (drive.json `unread`) | `LIST COUNTS` (+ `LISTGROUP` when the count leaves gaps) |
| Threading | root / reply / reply-to-reply at depth 0/1/2; the probe's In-Reply-To-only reply threads under its root at depth 1 (`04-group-threaded`) | `OVER a-b` (References) and one `HDR In-Reply-To a-b` over the same window |
| Search by subject | `probe root` → both probe articles; `XPAT Subject 1-9 *probe?root*` shown on the page (`06-search-subject`) | `XPAT Subject a-b *q*` |
| Search by author | `guest` → the guest article, `XPAT From 1-9 *guest*` | `XPAT From a-b *q*` |
| Verdict badges | `verified` rows, `absent` rows; article page "verified by principal 9261767a… under keyring generation 1" (`05-article-verified`) | `HDR :fn-verified a-b` / `HDR :fn-verified N` |
| Signed post | 240, meta "signed on this machine (FN-Authorship carrier)", node verdict `verified` | `POST` of the `hybrid-sign-carrier` output |
| Signed reply | 240, References carries the parent, `verified` | same |
| 441 with the node's reason | `441 posting failed; From is not a valid mailbox list` for unsigned and signed (`03-refused-441`, `03b-refused-signed`) | the node's ACL2 refusal word |
| Draft across reload | subject and body restored, "Restored the draft this browser kept" (`07-draft-restored`) | none: browser origin storage |
| Operator page | `DATE`, per-group counts, capabilities; the local status/retention/peers commands shown verbatim (`08-operator`) | `CAPABILITIES`, `DATE`, `LIST COUNTS` |
| Phone layout | `scrollWidth` 390 on groups, group, article and compose; thread indents cap at 32 px | — |

Search keeps no index in the web layer: each page asks the node one `XPAT`
over at most 2000 numbers ending at `before` (default the high-water mark)
and one `OVER` over the hits' span, and links the next older window. That is
a bound on work per request, not on the group.

Unread is per login and per node (`~/.fn-web/HOST_PORT_USER.json`), counted
against the node's `LIST COUNTS`; NNTP keeps no read state, so the marks are
this client's and the page says so.

## Signing: the honest choice

Three options were on the table. The spike signs **on the author's machine
with the local fn image**: `Signer` runs `fn-host-developer --fn
hybrid-sign-carrier PRINCIPAL ED-PUBLIC ED-SECRET ML-PUBLIC ML-PRIVATE SOURCE
OUT` over the composed source (with the author's `Date`), and POSTs the
ACL2-rendered carrier. The secret key stays in a 0700 directory; ACL2
renders the preimage and the carrier and verifies both signatures before
writing. Trust implied: this machine, its fn image and the key directory's
mode. The node verifies the carrier against its enrollment and answers
240/441.

Rejected: a key in the browser's origin storage would need a JavaScript copy
of the ACL2 preimage and CBOR carrier codec (a second owner, against the
one-owner rule) plus an unreviewed ML-DSA-65 library; a node signing verb
gives the node custody of the secret, so `verified` would mean only "the
node says this login posted".

## Deferrals (what the web layer or harness decides that the node should)

1. `;; SPIKE` in `fn_web.Signer` and `tools/spike_reader_node.py`: the
   **login-to-principal binding**. The node relates no AUTHINFO user to a
   hybrid principal. Measured (`hbox/gap.log`): login `ember` POSTed an
   article signed with guest's key and the node answered `0 verified
   bdfb1bc1… keyring 2`, guest's principal. That is correct as a signature
   claim, but "the login's enrolled key" is not a node concept; the web
   client signs with whatever key directory it is given.
2. `;; SPIKE` in `parse_verdict_hdr`: the `withdrawn` token's grammar. The
   reader shows the node's words and infers nothing. `carried <hex>` follows
   identity.md (D23); `revoked <hex> keyring G` follows spike/peering's
   `fn_verify.py`. spike/control's withdrawal hides articles from the served
   view and reports through `HDR :fn-control`, which this reader does not read
   yet. Neither `carried`, `revoked` nor `withdrawn` was observed on this
   image; they are covered by the fake-node tests only.
3. `;; SPIKE` in `WebServer.operator_reports`: a **live read-only status
   verb**. While the owner runs, `store status`, `store retention` (pins) and
   `bin/fn peer list` all answer `store is already locked`; the page shows
   exactly that. spike/operator reports the same finding. Headroom, pins and
   peers therefore have no live source.
4. The search's wildmat construction (`*` + query with reserved characters
   and spaces as `?` + `*`) is the web layer's; the match is the node's.
5. The composed source's `Date` for a signed post is the client's clock (the
   author's claim, inside the signature).

## Findings from the third-party client (tin 2.6.2)

Built without root on hbox from `tin-2.6.2.tar.xz` (SHA-256 `91df3cc0…068c`):
`CFLAGS=-std=gnu17`, `--enable-nntp-only --with-screen=ncursesw
--with-domain-name=example.org`, `GETTIMEOFDAY_2ARGS` forced in
`autoconf.h` (configure misdetects it under gcc 14), site defaults dir moved
to scratch with `disable_sender=ON`. Driven in tmux by
`tools/spike_tin_drive.sh` through `tools/nntp_wire_log.py` (every line both
ways, AUTHINFO PASS redacted; `hbox/tin-wire.log`).

What works (wire lines from `hbox/tin-wire.log`):

- Login: `201 fn-nntp experimental reader ready`, `CAPABILITIES`, `AUTHINFO
  USER ember` → `381`, `AUTHINFO PASS` → `281 authentication accepted`.
- List: `LIST OVERVIEW.FMT`, `LIST COUNTS`, `LIST NEWSGROUPS` (`(no
  description)`), all 215.
- Group and overview: `LISTGROUP fn.test` → `211 6 1 6 fn.test list
  follows`, `OVER 1-6` → 224, `LIST HEADERS RANGE` → 215, `HDR XREF 1-6` →
  225 with empty values.
- Read: `ARTICLE 3` → `220 3 <…> article follows`, including the
  `FN-Authorship` carrier folded over continuation lines; tin shows the
  signed article and its dot-led body line correctly.
- `XPAT` answers although `CAPABILITIES` does not list it (RFC 2980 predates
  labels); matching is case-sensitive, a second pattern argument does not
  OR (`XPAT Subject 1-10 *root* *zzz*` matched nothing), and `[...]` classes
  are not supported (`*[Rr]e*` matched nothing) (`hbox/probe-3.log`).

What refuses:

- **Every tin POST.** tin always sends a `Path` field: `Path: not-for-mail`
  (stock build, `inews.c`) or `Path: example.org!hbox` (`-DFORGERY`,
  `post.c`), and fn answers `441 posting failed; Path must not be supplied`
  to the followup, the new post and the cancel (`cmsg cancel`, Path
  `cyberspam!example.org!hbox`). RFC 5537 §3.4 lets a proto-article carry
  Path (only without a `POSTED` diag keyword), and §3.2.1 has the injecting
  agent prepend to it; fn's refusal is a recorded local policy
  (specs/nntp.md, "A proto-article that already carries Path is refused").
  The consequence: no stock tin can post, reply or cancel on fn. dev should
  accept a supplied Path, prepend its identity, and restate the
  verbatim-suffix property over the authored remainder.
- tin-side, not fn: `Invalid Sender:-header <hbox@hbox..>` until the site
  defaults set `disable_sender=ON` (hbox has no FQDN); "article unchanged"
  when the scripted editor wrote within the same second.

slrn was not built (it needs S-Lang, not on the box).

Matrix: `tools/v0_matrix.py` gains four `F-CLIENT` rows
(`V0-CLIENT-TIN-READ`, `-REPLY`, `-POST`, `-CANCEL`) and a "client" phase
(`tin_client`) that runs the same driver and wire logger against node A and
reads each verdict from the node's reply line (`tin_wire_outcomes`, checked
here against the run-7 wire log: `220` for the read, `441 … Path must not be
supplied` for all three POSTs). The phase has not run inside a matrix run;
the box needs tin on `PATH`. Until a matrix run publishes, `make check`
reports the four rows missing from `planning/v0-matrix.json`, which is
generated and cannot be edited by hand.

## What this does not claim

- Not the live node, not dev's image, and no TLS for tin (tin was built
  without TLS; the web client uses STARTTLS).
- The browser drive is one run of one scripted user; the phone layout was
  measured by viewport width only.
- `verified` is the node's historical report; the reader did not verify a
  signature itself (`tools/fn_verify.py` does that).
- A wire probe of mine (`probe2.py`) looped on EOF and filled its log; it was
  stopped with `pkill -x -f "python3 probe2.py"` on hbox — an exact-match
  pattern kill of my own process, which the box rules forbid; recorded here.
