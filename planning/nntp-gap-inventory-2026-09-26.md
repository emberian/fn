# NNTP and Usenet gap inventory (2026-09-26)

ember's question: what NNTP and Usenet features does fn lack that it should
add, so the server is more generally useful and usable? The setting is D36:
fn.fg-goose.online, peered with two friends' fn nodes and possibly with the
wider Usenet later. The friends read with tin, pan, slrn and Thunderbird, and
one of them runs OpenBSD.

Coordinate: source revision `079103f1d` (dev). This is a reading of the tree,
the specs and the RFC copies at the repository root (`rfc3977.txt`,
`rfc4642-4644`, `rfc5536`, `rfc5537`, `rfc6048`, `rfc8054`, `rfc8315`,
`rfc2980`). Nothing was run, and no row claims more than the tree says.
Statements about client behaviour that the tree has not measured are marked
*(unmeasured)*.

Every served command reaches ACL2 through one host line:
`host/native/owner.lisp` `fnn-owner-handle-chunk` (l.1757) calls
`host/owner-host.lisp` `fn-owner-chunk` (l.2291), which calls `fn-served-step`.
From there the chain is `fn-auth-step` (books/nntp-auth), then `fn-peer-step`
(books/peer-inbound), then `fn-nntp-post-step` (books/nntp-post), then
`fn-nntp-step` (books/nntp). The table's "where" column names the book and the
deciding function.

## 1. Commands and extensions

| Command | RFC | fn | Where | Reply codes |
| --- | --- | --- | --- | --- |
| CAPABILITIES | 3977 §5.2 | served. The auth layer adds STARTTLS and AUTHINFO USER, the peer layer adds IHAVE and STREAMING | nntp-responses `fn-nntp-capability-lines`, nntp-auth, peer-inbound | 101, 501 |
| MODE READER | 3977 §5.3 | served, non-mode-switching (MODE-READER is not advertised) | `fn-nntp-mode-response` | 200/201, 501 |
| QUIT | 3977 §5.4 | served | nntp `fn-nntp-session-command` | 205 |
| HELP | 3977 §7.2 | served, but it lists only the reader layer's verbs (no AUTHINFO, STARTTLS, XREDEEM or transit verbs) | `fn-nntp-help` | 100 |
| DATE | 3977 §7.1 | served; 503 without a wall clock | `fn-nntp-date-response` | 111, 503 |
| GROUP | 3977 §6.1.1 | served | nntp-projection `fn-nntp-group-result` | 211, 411, 501 |
| LISTGROUP [grp [range]] | 3977 §6.1.2 | served, with range forms, from group buckets | `fn-nntp-listgroup-command` | 211, 411, 412, 501 |
| LAST / NEXT | 3977 §6.1.3-4 | served | `fn-nntp-next-or-last` | 223, 412, 420, 421, 422 |
| ARTICLE / HEAD / BODY / STAT | 3977 §6.2 | served. By Message-ID it uses the pinned trie; a withdrawn or reclaimed article answers 430 | `fn-nntp-retrieval` | 220-223, 412, 420, 423, 430 |
| POST | 3977 §6.3.1 | served when both the pinned configuration and the principal allow it. Each refusal has its own 441 line | nntp-post `fn-nntp-post-step`, owner `fn-served-post-outcome` | 340, 240, 440, 441, 480 |
| IHAVE | 3977 §6.3.2 | served on peer connections only | peer-inbound `fn-peer-command` | 335/435/436, then 235/436/437; 502 on a reader connection |
| NEWGROUPS | 3977 §7.3 | served from persisted creation facts | `fn-nntp-newgroups-response` | 231, 501, 503 |
| NEWNEWS | 3977 §7.4 | served, as one O(A·G') walk | nntp-newnews `fn-nntp-newnews-response` | 230, 501, 503 |
| LIST [ACTIVE [wildmat]] | 3977 §7.6.3 | served; the status field is always `y` | `fn-nntp-list-active-or-newsgroups` | 215, 501 |
| LIST ACTIVE.TIMES | 3977 §7.6.4 | served; the creator field is `unattributed` | `fn-nntp-list-command` | 215 |
| LIST NEWSGROUPS | 3977 §7.6.6 | served; every group's description is `(no description)` | `fn-nntp-list-active-or-newsgroups` | 215 |
| LIST DISTRIB.PATS | 3977 §7.6.5 | refused by name | `fn-nntp-list-unmaintained-response` | 503 |
| LIST OVERVIEW.FMT | 3977 §8.4 | served: seven fields, no `Xref:full` | `fn-nntp-list-overview-fmt` | 215 |
| LIST HEADERS | 3977 §8.6 | served (`:`, `:bytes`, `:lines`) | `fn-nntp-list-headers` | 215 |
| OVER | 3977 §8.3 | served, by range and by Message-ID, bucket-indexed | `fn-nntp-over-response` | 224, 412, 420, 423, 430 |
| HDR | 3977 §8.5 | served for any header, as an archive fold | `fn-nntp-hdr-response` | 225, 412, 420, 423, 430 |
| LIST COUNTS | 6048 §2.2 | served | `fn-nntp-list-counts-command` | 215 |
| LIST DISTRIBUTIONS / SUBSCRIPTIONS | 6048 §2.3, §2.6 | refused by name | `fn-nntp-list-unmaintained-response` | 503 |
| LIST MODERATORS / MOTD | 6048 §2.4, §2.5 | **absent** | the same function's fallthrough | 501 unsupported LIST variant |
| XOVER / XHDR | 2980 §2.8, §2.6 | served as spellings of OVER and HDR (proved equal) | nntp-legacy, `fn-nntp-xover-response`, `fn-nntp-xhdr-response` | 224/221, 420 |
| XPAT | 2980 §2.9 | served, and advertised as `XPAT` | nntp-xpat `fn-nntp-xpat-response` | 221, 430 |
| XGTITLE, XINDEX, XROVER, XTHREAD | 2980 §2.4, 2.7, 2.11, 2.12 | absent (deferred) | none | 500 |
| XPATH | 2980 §2.10 | never: it would expose the store's layout | none | 500 |
| STARTTLS; implicit TLS (`tls_port`) | 4642 §2.2, §1 | served when a certificate is configured | nntp-auth `fn-auth-starttls`, served-implicit-tls | 382, 502 |
| AUTHINFO USER/PASS | 4643 §2.3 | served; `protected_only` answers 483 before TLS | `fn-auth-authinfo` | 281, 381, 481, 482, 483, 502 |
| AUTHINFO SASL | 4643 §2.4 | refused by name | `fn-auth-authinfo` | 502 |
| MODE STREAM | 4644 §2.3 | served on peer connections; 501 on a reader connection | `fn-peer-command` | 203 |
| CHECK / TAKETHIS | 4644 §2.4, §2.5 | served on peer connections | `fn-peer-command` | 238/431/438, then 239/439, plus 436 (local policy); 502 on a reader connection |
| COMPRESS DEFLATE | 8054 §2 | **absent** | none | 500 |
| XREDEEM | fn extension | served (invitation accounts) | `fn-auth-xredeem` | 381, 281, 482, 483, 502 |

## 2. Gaps

Size is one of small, a lane, or a wave. The Proof column records whether the
change touches an ACL2 keystone or the decision the host calls. The
recommendation is one of do, defer or never, with the reason.

### Reader side

Already served, so no gap: MODE READER, LISTGROUP ranges, DATE, NEWGROUPS,
XOVER/XHDR/XPAT, LIST OVERVIEW.FMT, LIST HEADERS, LIST COUNTS, implicit TLS.

| Gap | Expectation | Why it matters for the public node | Size | Proof | Rec |
| --- | --- | --- | --- | --- | --- |
| R1. A reader connection keeps the view it pinned at open. Only the poster is re-pinned after its own 240 (specs/nntp.md "Read-back"), and the tree has no native caller of `(:advance id)` (the old `ADVANCE` control verb exists only in `tools/run_owner.py`) | RFC 3977 §6.1.1's 211 reports the group as it is now. pan and Thunderbird cache connections, and slrn re-sends GROUP on refresh *(unmeasured)* | a friend on a long-lived connection would not see a peer's article until they reconnect | a lane | yes: the owner relation. specs/nntp.md says K1 admits either pin policy | **do.** First confirm it with one native test, then re-pin at GROUP/LISTGROUP between commands |
| R2. No group descriptions: LIST NEWSGROUPS and XGTITLE | 3977 §7.6.6. tin, pan and Thunderbird show descriptions in their subscribe views | strangers and friends browse the group list | small (a description field in the group record, "R5" in specs/nntp.md) | yes: the config record codec | **do** |
| R3. No Xref: it is removed on relay, never generated, and absent from the overview | RFC 5536 §3.2.14 and 3977 §8.4.2 `Xref:full`. tin, slrn and pan use it to mark a cross-post read in every group it appears in *(unmeasured)* | cross-posts between the friends' groups show as unread once per group | a lane: render it from local numbers as overview metadata, not stored octets (peering §2.3 rejects serving-time rewriting of stored bytes) | yes: the OVER=XOVER and OVERVIEW.FMT keystones | **do** |
| R4. HELP omits the AUTHINFO, STARTTLS and XREDEEM verbs | 3977 §7.2 | a stranger's first look at the server | small | the help-list test only | **do** (a rider) |
| R5. No LIST MOTD | 6048 §2.5 | the operator has no way to say "this is fn.fg-goose.online, ask ember for a code" | small (a text row in the configuration) | yes, small | **do** |
| R6. An anonymous read-only level is missing (PKT-405): `anonymous open` also opens POST when `[posting]` is enabled | RFC 4643 §2.2 lets a server grant reading without login | public reading with posting restricted to friends is the usual shape for a public node | small | yes: the `fn-auth-step` gate | **do**, if ember wants anonymous reading |
| R7. The listener admits only a numeric IPv4 address or the loopback aliases (`books/native-config.lisp` `fn-native-config-listener-hostp`). There is no public IPv6 address and no second listener address | none in the RFCs; this is deployment practice | if the host has IPv6, friends reach it only over v4 | small | yes: the listener projection | **do** if the VPS has v6 |
| R8. HDR/XHDR, GROUP, NEXT, LAST and NEWNEWS use archive folds that are linear per command | none; this is cost | slrn probes `XHDR Path`, and tin threads with XHDR *(unmeasured)* | a lane (a bucket refinement like OVER's) | yes | **defer** until the volume is measured; required before the wider Usenet |
| R9. COMPRESS DEFLATE | RFC 8054 | tin, slrn and Thunderbird do not speak it *(unmeasured)*; it would add zlib to the native trust boundary | a lane | the trust boundary | **defer** |
| R10. AUTHINFO SASL | RFC 4643 §2.4 | every target client uses USER/PASS; PLAIN over TLS adds nothing | a lane | yes | **never**, until a client needs SCRAM |
| R11. XGTITLE, XROVER, XTHREAD, XINDEX | RFC 2980 | superseded by LIST NEWSGROUPS and HDR; XINDEX has no specification | none | none | **never** (XGTITLE comes free if R2 lands) |

### Posting side

| Gap | Expectation | Why | Size | Proof | Rec |
| --- | --- | --- | --- | --- | --- |
| P1. A cancel or Supersedes from an ordinary newsreader does nothing. It is filed, but only a *verified signed* canceller with a grant can withdraw (peering §8; docs/human-web-client.md "tin over TLS") | RFC 5537 §5.3; RFC 8315 Cancel-Lock/Cancel-Key, which INN 2.7 and tin support | a friend cannot take back their own post from tin, pan or Thunderbird | a lane. Two authority bases: (a) the canceller's authenticated principal equals the target's `:post` provenance principal, for the same node; (b) a Cancel-Key matching the target's Cancel-Lock, which works across nodes, and optionally the injector adds a Cancel-Lock | yes: `fn-ctl-authorize` needs a new basis with teeth; (b)'s injected Cancel-Lock changes the D25 inverse | **do** |
| P2. Injection-Info names only the agent (`fn-inj-injection-info-line`) | RFC 5536 §3.2.8: posting-account, posting-host, logging-data, mail-complaints-to | on a public node, an abuse report has to be traceable to a login without exposing it | small to a lane | yes: the injected block and `fn-inj-source-of` | **do** (a hashed posting-account and mail-complaints-to) |
| P3. No moderated groups: no `m` flag, no Approved check, no forward to a moderator (specs/nntp.md "Not yet true of POST") | RFC 5537 §3.5 item 7, §3.5.1 (the article goes by mail), §3.9; RFC 5536 §3.2.1 | only if a friend wants a moderated group. fn has no mail path, so "moderated" would mean Approved by a granted principal, else a 441 | a lane | yes: the injection decision and the active flags | **defer**. Do the read-only `n` flag first (O2) |
| P4. Distribution is ignored, so `Distribution: local` still feeds to peers | RFC 5536 §3.2.4; relays may filter on it | small for friends; it matters for the wider Usenet | small | yes: `fn-feed-offerablep` | **defer**; do it before the wider Usenet |
| P5. Expires is not honoured | RFC 5536 §3.2.5 (advisory) | D03: no automatic expiry. The explicit rule exists node-wide (`admin retention set ... release-after DAYS`), but `store reclaim` is not implemented | a lane (per group) | yes (D13) | **never** automatically (D03). The per-group release rule is O3 |
| P6. No freshness check on a supplied Date and no trusted-source check | RFC 5537 §3.5 items 1 and 3 | a stale or forged date from a posting client | small, but it needs a certified RFC 5322 date reader | yes | **defer** (shares its reader with T3) |
| P7. There is no per-group maximum article size, only the profile-wide `max-article-octets` and the per-peer `inbound max-octets` | local policy | text groups do not need one | small | yes | **defer** |
| P8. Followup-To | RFC 5537 §3.4.3: a posting-agent duty | fn keeps it verbatim | none | none | **never** (nothing to do) |
| P9. Fixed ceilings in `books/article.lisp`: 64 fields, 256 header lines and 16,384 header octets. The 998-octet line limit is RFC 5322's MUST | D27: no arbitrary ceilings on stored data | posts from friends fit; relayed Usenet articles sometimes do not | a lane | yes: the parser bounds and every public-work theorem | **defer** for friends. Do it before the wider Usenet (D27) |

### Transit side

MODE STREAM, CHECK and TAKETHIS are complete. CHECK re-reads the live node.
The 431/436 versus 437/439 split matches innfeed's retry switch
(docs/interop-inn.md).

| Gap | Expectation | Why | Size | Proof | Rec |
| --- | --- | --- | --- | --- | --- |
| T1. Refused offers are not remembered: the history holds accepted articles only (peering §2.5) | RFC 5537 §3.3. INN records rejects in its history | on the wider Usenet, spam arrives from every peer and is parsed each time | a lane (with D13) | yes | **defer** until the wider Usenet |
| T2. Two relay checks are open: RFC 5537 §3.6 step 2 (Date more than 24 h in the future) and §3.7 step 1 (a missing mandatory field; articles without a Path are accepted) | RFC 5537 | hygiene against a sloppy or hostile feed | small once the date reader exists | yes | **defer**; required before the wider Usenet |
| T3. The loop check knows one identity. There is no alias list like INN's `ME/` exclusions | RFC 5537 §3.2 | a node that ever renames its `path-identity` | small | yes (K2) | **defer** |
| T4. Per-peer policy covers group wildmats, max-octets, max-inflight, max-queue, backoff and the D23 carried list. It lacks a cross-post count limit, a Distribution filter and INN-style `!site` path exclusions | INN `newsfeeds` practice | spam control on a wider feed | small each | yes | **defer** |
| T5. Peering with INN: `incoming.conf` identifies a peer by address; innfeed can send AUTHINFO but, as far as is known, has no TLS client (the lab built INN without TLS). Under `protected_only`, an INN peer must therefore be a source-address peer | docs/interop-inn.md | the wider Usenet will mean INN | none (it is configuration) | none | **do**: document the INN recipe. docs/operator.md "Require a login" still says `[auth] required` answers 480 to transit peers, which contradicts the principal-bound role (peering 2026-09-21). Verify and fix |
| T6. The NEWNEWS pull starts one day back and needs the peer to allow NEWNEWS (INN `allownewnews`) | RFC 3977 §7.4 | NAT'd friends | none | none | nothing to add |

### Control side

| Gap | Expectation | Why | Size | Proof | Rec |
| --- | --- | --- | --- | --- | --- |
| CT1. newgroup and rmgroup by article (C4) | RFC 5537 §5.2 | D29 defers C4 until group authority and succession are decided. With two friends, operator verbs suffice | a wave | yes | **defer** (D29) |
| CT2. checkgroups as a report the operator may apply, never automatically | RFC 5537 §5.2.3 | useful only with the Big-8 | a lane | yes | **defer** until the wider Usenet |
| CT3. The operator's takedown means posting a *signed* cancel with a granted key. There is no `withdraw MSGID` verb for the node's own authority | RFC 5537 §5.3; public-node abuse practice | on a public node, the operator has to be able to pull an article quickly | small to a lane (a new withdrawal cause kind) | yes: `fn-ctl-cancel-plan`, and visible(T,C) = visible(C,T) must stay | **do** |

### Operator side

| Gap | Expectation | Why | Size | Proof | Rec |
| --- | --- | --- | --- | --- | --- |
| O1. Group verbs are `create` and `retire` only. There is no `describe`, no status, no moderator and no MOTD text | INN `ctlinnd newgroup name flag creator`, `newsgroups`, `motd.nnrpd` | this is where R2, R5 and O2 land | a lane (one configuration delta family) | yes | **do**, together with R2 and R5 |
| O2. The LIST ACTIVE status field is always `y` (`nntp-responses.lisp` l.200, l.222) | RFC 6048 §2.1: y n m x j = | `n` (read-only, e.g. an announcements group) needs a per-group posting gate. `books/policy.lisp` has a signed per-group policy, but no served decision uses it | a lane | yes: the injection decision | **do** `n`. **defer** `m` (P3) and `x`. **never** `j` and `=` (no junk group, no aliases) |
| O3. Expiry per group as a retention rule | D03 and D13 | disk on the public node | a lane (`store reclaim` and the per-group rule) | yes (D13) | **defer** until disk pressure. Release stays explicit |
| O4. An overview database rebuild | INN `makehistory -O` | not needed: overview lines are projected from retained octets, and indexes are rebuilt from committed acceptance at recovery | none | none | **never** (by design) |
| O5. Doc drift: "Add a group" says the service must stop (the Python-era `fn group`), while the native `operator CONFIG group create` is live. `max-article-octets` is given as 32,768 in one table and 16 MiB in the next paragraph | none | a stranger installs from these docs (D35) | small | none | **do** |

### Client compatibility

| Client | Evidence | What it needs that is missing |
| --- | --- | --- |
| tin 2.6.2 | measured: `planning/evidence/sanding-2026-09-26.md` (log in, read, follow up, post and cancel over TLS on 1563) and path-and-login (D32) | its cancel has no effect (P1); cross-posts need Xref (R3); descriptions (R2). A From domain is the client's own setting (docs/human-web-client.md) |
| slrn 1.0.3 | measured 2026-09-20, plain, loopback, reading only (specs/nntp-audit.md): MODE READER, XOVER, `XHDR Path`, LIST OVERVIEW.FMT, LIST, LIST SUBSCRIPTIONS, all answered | posting and TLS are unmeasured; Xref (R3) *(unmeasured)* |
| pan | **unmeasured** | expected: implicit TLS, AUTHINFO, heavy XOVER, 2-4 connections (within `exposure-per-address` 8), LIST NEWSGROUPS; freshness (R1) |
| Thunderbird | **unmeasured** | expected: MODE READER, LIST ACTIVE with a wildmat, XOVER, XHDR, XPAT (server search), NEWGROUPS, STARTTLS or 563, AUTHINFO USER/PASS. It caches connections (R1), and its cancel runs into P1 |
| OpenBSD friend | tin and slrn are in OpenBSD packages; the node side is D35 | nothing NNTP-specific; the release tarball is the gap (D35) |

The next cheap measurement: a lane that adds pan and Thunderbird rows to the
v0 matrix, in the shape of the `V0-CLIENT-TIN-*` rows, run against the TLS
listener with an invitation-code account.

## 3. The first ten for a public node with friends

1. **R1, reader freshness.** Measure whether a long-lived connection sees a
   peer's new article, then re-pin at GROUP/LISTGROUP.
2. **Measure pan and Thunderbird** in the v0 matrix, over TLS with an
   invitation account.
3. **P1, own-post cancel and supersede for unsigned readers.** Login
   provenance for posts made on the same node; Cancel-Lock (RFC 8315) for
   posts from other nodes.
4. **R2 + R5 + O1: group descriptions, LIST MOTD and a `group describe`
   verb**, as one configuration lane.
5. **R3: Xref and `Xref:full` in the overview**, so a cross-post is read
   once.
6. **P2: Injection-Info with a hashed posting-account and
   mail-complaints-to.**
7. **R6: an anonymous read-only level** (PKT-405), if public reading is
   wanted.
8. **O2: the `n` flag** (read-only groups) through a per-group posting gate,
   which puts the status field of LIST ACTIVE to use.
9. **CT3: an operator withdraw-by-Message-ID verb** under the node's own
   authority.
10. **R7: an IPv6 or dual-stack listener**, with the small riders R4 (HELP),
    O5 (docs) and T5 (INN recipe, auth doc).

Before the wider Usenet, not before friends: P9 (the header ceilings, D27), T1
(the reject history), T2 and P6 (the date reader and the missing Path), P4
(Distribution), T4 (the per-peer filters), R8 (indexed HDR/GROUP), and CT2
(the checkgroups report).
