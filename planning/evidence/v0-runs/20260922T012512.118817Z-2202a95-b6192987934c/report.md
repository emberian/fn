# v0 matrix: 2202a95 on persvati

v0 is every feature of fn usable between two peered fn nodes. This is that
question asked feature by feature against one commit on one box, with five
verdicts and no pass/fail collapse: accepted, refused and uncertain are the
three outcomes and each is a real observation; not-exercised names what
blocked the row; not-built names the lane that owns the missing feature.
It establishes nothing about the books beyond which certificates ACL2 read.

## What ran

| fact | value |
| --- | --- |
| commit | `2202a95` (2202a95fdc01fea1c90cdc8c267a7a83044af957) |
| tree | `native915` |
| host | `persvati` |
| started | 2026-09-22T01:25:12Z |
| wall time | 33.8 s |
| gate tool | `tools/v0_matrix.py` |
| os | Ubuntu 25.10 kernel=Linux 6.17.0-40-generic arch=x86_64 cores=24 |
| python3 | Python 3.13.7 |
| acl2version | + ACL2 Version 8.7                                                     + |
| certificates | not acquired by this slice; it consumes the explicitly named saved image |
| node a | native-operator on port 11190 (main), store $HOME/fn-deploy/native915-2202a95/a/store |
| node b | native-operator on port 11191 (main), store $HOME/fn-deploy/native915-2202a95/b/store |
| server entry point | native-operator |
| rows | 192 rows: 69 accepted, 12 refused, 0 uncertain, 101 not exercised, 10 not built, 0 disagreed |
| alt | python3.12 Python 3.12.13 |
| execution backend | native-operator |
| execution image | launcher sha256=ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142; image sha256=2d8259c22388119793ad3dde525497f9095bdb2489ac01e597b439f3d0ff5c09; declared runtime=b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5; sidecar core sha256=eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2 (static only before a live-owner witness); source correspondence unestablished |
| execution source | 2202a95 |
| server | node B (native-operator) on port 11191 (b-main) |
| host clients | expect=ABSENT, inews=ABSENT, nn=ABSENT, script=/usr/bin/script, slrn=ABSENT, tin=ABSENT, trn=ABSENT |

## The v0 matrix

**Execution subject.** Backend `native-operator`; deployed source `2202a95`; runtime image `launcher sha256=ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142; image sha256=2d8259c22388119793ad3dde525497f9095bdb2489ac01e597b439f3d0ff5c09; declared runtime=b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5; sidecar core sha256=eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2 (static only before a live-owner witness); source correspondence unestablished; live owners observed via /proc runtime sha256=b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5 and core sha256=eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2`. These are separate labels: naming the source and hashing an externally supplied image does not prove they correspond.

192 rows: 69 accepted, 12 refused, 0 uncertain, 101 not exercised, 10 not built; 0 row(s) did not do what they were designed to do. Every count here is `tools/v0_matrix.py`'s over the rows below, and `planning/evidence/v0-runs/20260922T012512.118817Z-2202a95-b6192987934c/matrix.json` carries the same rows with their digest.


**Who saw it.** 0 of the 81 outcome rows were observed by something that is not fn's own code; 81 were observed by fn talking to fn. A feature that only fn's own client has ever seen is a weaker claim than "usable between two peered servers" reads, and every row carries the client that saw it in its `client` field. Clients in this run: fn CLI (exit code) (2); the matrix's raw-socket driver (79).

| feature | accepted | refused | uncertain | not exercised | not built | disagreed |
| --- | --- | --- | --- | --- | --- | --- |
| node init, configuration, start and stop (F-NODE) | 4 | 0 | 0 | 1 | 10 | 0 |
| the three outcomes on the operator surface (F-OUT) | 0 | 0 | 0 | 8 | 0 | 0 |
| groups, capacity, peers and live reconfiguration (F-GROUP) | 0 | 0 | 0 | 20 | 0 | 0 |
| principals, AUTHINFO and posting permission (F-AUTH) | 0 | 0 | 0 | 17 | 0 | 0 |
| POST and its read-back (F-POST) | 10 | 2 | 0 | 1 | 0 | 0 |
| the reader profile on each node (F-READ) | 46 | 8 | 0 | 0 | 0 | 0 |
| capability truthfulness (F-PIN) | 0 | 0 | 0 | 4 | 0 | 0 |
| transit inbound, A to B and B to A (F-TRANSIT) | 6 | 2 | 0 | 18 | 0 | 0 |
| the owner-driven outbound feed (F-FEED) | 3 | 0 | 0 | 1 | 0 | 0 |
| checkpoint, recovery and the process-death cut table (F-CRASH) | 0 | 0 | 0 | 9 | 0 | 0 |
| BP over TCPCLv4 between the two nodes (F-BP) | 0 | 0 | 0 | 8 | 0 | 0 |
| statement sign and verify across the pair (F-STX) | 0 | 0 | 0 | 6 | 0 | 0 |
| the carried-media letter (F-MEDIA) | 0 | 0 | 0 | 3 | 0 | 0 |
| scale (F-SCALE) | 0 | 0 | 0 | 1 | 0 | 0 |
| INN as a third node (F-INN) | 0 | 0 | 0 | 1 | 0 | 0 |
| independent newsreader clients (F-CLIENT) | 0 | 0 | 0 | 3 | 0 | 0 |

### Every row

| row | title | verdict | expected | agrees | independent | observed |
| --- | --- | --- | --- | --- | --- | --- |
| `V0-NODE-INIT-A` | fn init creates the store and writes fn.toml | **not-built** | accepted | - | - | (not run) |
| `V0-NODE-INIT-B` | fn init creates the store and writes fn.toml | **not-built** | accepted | - | - | (not run) |
| `V0-NODE-CONFIG-A` | fn.toml carries [store] path and [acl2] path | **not-built** | accepted | - | - | (not run) |
| `V0-NODE-CONFIG-B` | fn.toml carries [store] path and [acl2] path | **not-built** | accepted | - | - | (not run) |
| `V0-NODE-REINIT-A` | what a second fn init over a store that already holds articles does | **not-built** | - | - | - | (not run) |
| `V0-NODE-REINIT-B` | what a second fn init over a store that already holds articles does | **not-built** | - | - | - | (not run) |
| `V0-NODE-REINIT-SAFE-A` | the articles the store already held are still there after the second init | **not-built** | accepted | - | - | (not run) |
| `V0-NODE-REINIT-SAFE-B` | the articles the store already held are still there after the second init | **not-built** | accepted | - | - | (not run) |
| `V0-NODE-STATUS-A` | fn status reports generation and article count | **accepted** | accepted | yes | fn only | rc=0 transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment |
| `V0-NODE-STATUS-B` | fn status reports generation and article count | **accepted** | accepted | yes | fn only | rc=0 transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment |
| `V0-NODE-START-A` | the service starts and reaches LISTENING | **accepted** | accepted | yes | fn only | `native-operator` reached LISTENING |
| `V0-NODE-START-B` | the service starts and reaches LISTENING | **accepted** | accepted | yes | fn only | `native-operator` reached LISTENING |
| `V0-NODE-STOP-A` | the service stops and releases the store | **not-built** | accepted | - | - | (not run) |
| `V0-NODE-STOP-B` | the service stops and releases the store | **not-built** | accepted | - | - | (not run) |
| `V0-NODE-LOOPBACK` | a non-loopback listener host is refused rather than silently bound | **not-exercised** | refused | - | - | (not run) |
| `V0-OUT-ACCEPTED-A` | an accepted post exits 0 | **not-exercised** | accepted | - | - | (not run) |
| `V0-OUT-ACCEPTED-B` | an accepted post exits 0 | **not-exercised** | accepted | - | - | (not run) |
| `V0-OUT-REFUSED-A` | a lookup of an article the node does not hold exits 1 | **not-exercised** | refused | - | - | (not run) |
| `V0-OUT-REFUSED-B` | a lookup of an article the node does not hold exits 1 | **not-exercised** | refused | - | - | (not run) |
| `V0-OUT-UNCERTAIN-A` | a post interrupted after publication exits 3 and fences the store | **not-exercised** | uncertain | - | - | (not run) |
| `V0-OUT-UNCERTAIN-B` | a post interrupted after publication exits 3 and fences the store | **not-exercised** | uncertain | - | - | (not run) |
| `V0-OUT-RECOVER-A` | recover after the uncertain publication exits 0 | **not-exercised** | accepted | - | - | (not run) |
| `V0-OUT-RECOVER-B` | recover after the uncertain publication exits 0 | **not-exercised** | accepted | - | - | (not run) |
| `V0-GROUP-CREATE-A` | fn group create adds a served group | **not-exercised** | accepted | - | - | (not run) |
| `V0-GROUP-CREATE-B` | fn group create adds a served group | **not-exercised** | accepted | - | - | (not run) |
| `V0-GROUP-SERVED-A` | the new group is served over the socket | **not-exercised** | accepted | - | - | (not run) |
| `V0-GROUP-SERVED-B` | the new group is served over the socket | **not-exercised** | accepted | - | - | (not run) |
| `V0-GROUP-RETIRE-A` | fn group retire removes it again | **not-exercised** | accepted | - | - | (not run) |
| `V0-GROUP-RETIRE-B` | fn group retire removes it again | **not-exercised** | accepted | - | - | (not run) |
| `V0-GROUP-UNKNOWN-A` | retiring a group the node does not serve is refused | **not-exercised** | refused | - | - | (not run) |
| `V0-GROUP-UNKNOWN-B` | retiring a group the node does not serve is refused | **not-exercised** | refused | - | - | (not run) |
| `V0-CAP-SET-A` | fn capacity sets the retention capacity | **not-exercised** | accepted | - | - | (not run) |
| `V0-CAP-SET-B` | fn capacity sets the retention capacity | **not-exercised** | accepted | - | - | (not run) |
| `V0-CAP-REFUSE-A` | an article that does not fit the capacity is refused before it is written | **not-exercised** | refused | - | - | (not run) |
| `V0-CAP-REFUSE-B` | an article that does not fit the capacity is refused before it is written | **not-exercised** | refused | - | - | (not run) |
| `V0-PEER-ADD-A` | fn peer add writes a transit peer record | **not-exercised** | accepted | - | - | (not run) |
| `V0-PEER-ADD-B` | fn peer add writes a transit peer record | **not-exercised** | accepted | - | - | (not run) |
| `V0-PEER-LIST-A` | fn peer list reads the record back | **not-exercised** | accepted | - | - | (not run) |
| `V0-PEER-LIST-B` | fn peer list reads the record back | **not-exercised** | accepted | - | - | (not run) |
| `V0-PEER-ABSENT` | fn peer remove of a peer that is not there is refused | **not-exercised** | refused | - | - | (not run) |
| `V0-PEER-REMOVE` | fn peer remove of a configured peer is accepted | **not-exercised** | accepted | - | - | (not run) |
| `V0-CFG-LIVE` | a group declared on the running service's control channel reaches the served configuration | **not-exercised** | accepted | - | - | (not run) |
| `V0-CFG-LIVE-REFUSE` | an offline configuration command is refused while the service holds the store | **not-exercised** | refused | - | - | (not run) |
| `V0-AUTH-NEW` | fn principal new derives a principal id from a seed | **not-exercised** | accepted | - | - | (not run) |
| `V0-AUTH-PASSWORD-A` | fn principal set-password records an AUTHINFO credential | **not-exercised** | accepted | - | - | (not run) |
| `V0-AUTH-PASSWORD-B` | fn principal set-password records an AUTHINFO credential | **not-exercised** | accepted | - | - | (not run) |
| `V0-AUTH-LIST-A` | fn principal list shows the credential | **not-exercised** | accepted | - | - | (not run) |
| `V0-AUTH-LIST-B` | fn principal list shows the credential | **not-exercised** | accepted | - | - | (not run) |
| `V0-AUTH-ADVERTISED-A` | AUTHINFO USER is advertised while the connection is unauthenticated | **not-exercised** | accepted | - | - | (not run) |
| `V0-AUTH-ADVERTISED-B` | AUTHINFO USER is advertised while the connection is unauthenticated | **not-exercised** | accepted | - | - | (not run) |
| `V0-AUTH-GATED-A` | POST before a login is refused, not performed | **not-exercised** | refused | - | - | (not run) |
| `V0-AUTH-GATED-B` | POST before a login is refused, not performed | **not-exercised** | refused | - | - | (not run) |
| `V0-AUTH-LOGIN-A` | AUTHINFO USER then PASS answers 281 | **not-exercised** | accepted | - | - | (not run) |
| `V0-AUTH-LOGIN-B` | AUTHINFO USER then PASS answers 281 | **not-exercised** | accepted | - | - | (not run) |
| `V0-AUTH-WITHDRAWN-A` | AUTHINFO is no longer advertised once the connection is authenticated | **not-exercised** | accepted | - | - | (not run) |
| `V0-AUTH-WITHDRAWN-B` | AUTHINFO is no longer advertised once the connection is authenticated | **not-exercised** | accepted | - | - | (not run) |
| `V0-AUTH-POST-A` | POST after the login is accepted | **not-exercised** | accepted | - | - | (not run) |
| `V0-AUTH-POST-B` | POST after the login is accepted | **not-exercised** | accepted | - | - | (not run) |
| `V0-AUTH-WRONG-A` | a wrong password answers 481 and grants nothing | **not-exercised** | refused | - | - | (not run) |
| `V0-AUTH-WRONG-B` | a wrong password answers 481 and grants nothing | **not-exercised** | refused | - | - | (not run) |
| `V0-POST-OPEN-A` | POST on the served socket answers 340 | **accepted** | accepted | yes | fn only | 340 send article to be posted |
| `V0-POST-OPEN-B` | POST on the served socket answers 340 | **accepted** | accepted | yes | fn only | 340 send article to be posted |
| `V0-POST-COMMIT-A` | the article is accepted with 240 | **accepted** | accepted | yes | fn only | 240 article received OK |
| `V0-POST-COMMIT-B` | the article is accepted with 240 | **accepted** | accepted | yes | fn only | 240 article received OK |
| `V0-POST-READBACK-A` | the posting connection's next GROUP already counts the article | **accepted** | accepted | yes | fn only | GROUP before=211 0 1 0 fn.letters after=211 1 1 1 fn.letters |
| `V0-POST-READBACK-B` | the posting connection's next GROUP already counts the article | **accepted** | accepted | yes | fn only | GROUP before=211 0 1 0 fn.letters after=211 1 1 1 fn.letters |
| `V0-POST-FRESH-A` | a fresh connection reads it back by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <native-matrix-1e227a4b796c-a@example.invalid> article follows |
| `V0-POST-FRESH-B` | a fresh connection reads it back by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <native-matrix-b3222d2dad52-b@example.invalid> article follows |
| `V0-POST-DUPLICATE-A` | a second POST of the same Message-ID is refused and allocates nothing | **refused** | refused | yes | fn only | 441 posting failed; the article was refused |
| `V0-POST-DUPLICATE-B` | a second POST of the same Message-ID is refused and allocates nothing | **refused** | refused | yes | fn only | 441 posting failed; the article was refused |
| `V0-POST-CLOCK-A` | a duplicate POST is refused as an article and does not cost the node its clock | **accepted** | accepted | yes | fn only | the duplicate answered '441 posting failed; the article was refused' and DATE afterwards answered '111 20260922012521' |
| `V0-POST-CLOCK-B` | a duplicate POST is refused as an article and does not cost the node its clock | **accepted** | accepted | yes | fn only | the duplicate answered '441 posting failed; the article was refused' and DATE afterwards answered '111 20260922012523' |
| `V0-POST-CONCURRENT` | a second reader stays live across another connection's whole POST | **not-exercised** | accepted | - | - | (not run) |
| `V0-READ-CAPABILITIES-A` | CAPABILITIES | **accepted** | accepted | yes | fn only | 101 capability list follows |
| `V0-READ-CAPABILITIES-B` | CAPABILITIES | **accepted** | accepted | yes | fn only | 101 capability list follows |
| `V0-READ-MODE-READER-A` | MODE READER | **accepted** | accepted | yes | fn only | 200 posting allowed |
| `V0-READ-MODE-READER-B` | MODE READER | **accepted** | accepted | yes | fn only | 200 posting allowed |
| `V0-READ-LIST-ACTIVE-A` | LIST ACTIVE | **accepted** | accepted | yes | fn only | 215 list of active newsgroups follows |
| `V0-READ-LIST-ACTIVE-B` | LIST ACTIVE | **accepted** | accepted | yes | fn only | 215 list of active newsgroups follows |
| `V0-READ-LIST-NEWSGROUPS-A` | LIST NEWSGROUPS | **accepted** | accepted | yes | fn only | 215 list of newsgroups follows |
| `V0-READ-LIST-NEWSGROUPS-B` | LIST NEWSGROUPS | **accepted** | accepted | yes | fn only | 215 list of newsgroups follows |
| `V0-READ-LIST-OVERVIEW-FMT-A` | LIST OVERVIEW.FMT | **accepted** | accepted | yes | fn only | 215 order of fields in overview database |
| `V0-READ-LIST-OVERVIEW-FMT-B` | LIST OVERVIEW.FMT | **accepted** | accepted | yes | fn only | 215 order of fields in overview database |
| `V0-READ-LIST-ACTIVE-TIMES-A` | LIST ACTIVE.TIMES | **accepted** | accepted | yes | fn only | 215 information follows |
| `V0-READ-LIST-ACTIVE-TIMES-B` | LIST ACTIVE.TIMES | **accepted** | accepted | yes | fn only | 215 information follows |
| `V0-READ-LIST-HEADERS-A` | LIST HEADERS | **accepted** | accepted | yes | fn only | 215 field list follows |
| `V0-READ-LIST-HEADERS-B` | LIST HEADERS | **accepted** | accepted | yes | fn only | 215 field list follows |
| `V0-READ-GROUP-A` | GROUP | **accepted** | accepted | yes | fn only | 211 1 1 1 fn.letters |
| `V0-READ-GROUP-B` | GROUP | **accepted** | accepted | yes | fn only | 211 1 1 1 fn.letters |
| `V0-READ-LISTGROUP-A` | LISTGROUP with a range | **accepted** | accepted | yes | fn only | 211 1 1 1 fn.letters list follows |
| `V0-READ-LISTGROUP-B` | LISTGROUP with a range | **accepted** | accepted | yes | fn only | 211 1 1 1 fn.letters list follows |
| `V0-READ-ARTICLE-A` | ARTICLE by number | **accepted** | accepted | yes | fn only | 220 1 <native-matrix-1e227a4b796c-a@example.invalid> article follows |
| `V0-READ-ARTICLE-B` | ARTICLE by number | **accepted** | accepted | yes | fn only | 220 1 <native-matrix-b3222d2dad52-b@example.invalid> article follows |
| `V0-READ-HEAD-A` | HEAD by number | **accepted** | accepted | yes | fn only | 221 1 <native-matrix-1e227a4b796c-a@example.invalid> headers follow |
| `V0-READ-HEAD-B` | HEAD by number | **accepted** | accepted | yes | fn only | 221 1 <native-matrix-b3222d2dad52-b@example.invalid> headers follow |
| `V0-READ-BODY-A` | BODY by number | **accepted** | accepted | yes | fn only | 222 1 <native-matrix-1e227a4b796c-a@example.invalid> body follows |
| `V0-READ-BODY-B` | BODY by number | **accepted** | accepted | yes | fn only | 222 1 <native-matrix-b3222d2dad52-b@example.invalid> body follows |
| `V0-READ-STAT-A` | STAT by number | **accepted** | accepted | yes | fn only | 223 1 <native-matrix-1e227a4b796c-a@example.invalid> retrieved |
| `V0-READ-STAT-B` | STAT by number | **accepted** | accepted | yes | fn only | 223 1 <native-matrix-b3222d2dad52-b@example.invalid> retrieved |
| `V0-READ-ARTICLE-MSGID-A` | ARTICLE by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <native-matrix-1e227a4b796c-a@example.invalid> article follows |
| `V0-READ-ARTICLE-MSGID-B` | ARTICLE by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <native-matrix-b3222d2dad52-b@example.invalid> article follows |
| `V0-READ-ARTICLE-ABSENT-A` | ARTICLE of a Message-ID the node does not hold is refused | **refused** | refused | yes | fn only | 430 no article with that message-id |
| `V0-READ-ARTICLE-ABSENT-B` | ARTICLE of a Message-ID the node does not hold is refused | **refused** | refused | yes | fn only | 430 no article with that message-id |
| `V0-READ-OVER-A` | OVER for one article | **accepted** | accepted | yes | fn only | 224 overview information follows |
| `V0-READ-OVER-B` | OVER for one article | **accepted** | accepted | yes | fn only | 224 overview information follows |
| `V0-READ-OVER-RANGE-A` | OVER over a range | **accepted** | accepted | yes | fn only | 224 overview information follows |
| `V0-READ-OVER-RANGE-B` | OVER over a range | **accepted** | accepted | yes | fn only | 224 overview information follows |
| `V0-READ-HDR-A` | HDR Subject | **accepted** | accepted | yes | fn only | 225 headers follow |
| `V0-READ-HDR-B` | HDR Subject | **accepted** | accepted | yes | fn only | 225 headers follow |
| `V0-READ-XOVER-A` | XOVER (the legacy spelling) | **accepted** | accepted | yes | fn only | 224 overview information follows |
| `V0-READ-XOVER-B` | XOVER (the legacy spelling) | **accepted** | accepted | yes | fn only | 224 overview information follows |
| `V0-READ-XHDR-A` | XHDR (the legacy spelling) | **accepted** | accepted | yes | fn only | 221 header follows |
| `V0-READ-XHDR-B` | XHDR (the legacy spelling) | **accepted** | accepted | yes | fn only | 221 header follows |
| `V0-READ-XPAT-A` | XPAT Subject | **accepted** | accepted | yes | fn only | 221 header follows |
| `V0-READ-XPAT-B` | XPAT Subject | **accepted** | accepted | yes | fn only | 221 header follows |
| `V0-READ-NEXT-A` | NEXT moves the cursor | **refused** | - | - | fn only | 421 no next article |
| `V0-READ-NEXT-B` | NEXT moves the cursor | **refused** | - | - | fn only | 421 no next article |
| `V0-READ-LAST-A` | LAST moves the cursor back | **refused** | - | - | fn only | 422 no previous article |
| `V0-READ-LAST-B` | LAST moves the cursor back | **refused** | - | - | fn only | 422 no previous article |
| `V0-READ-DATE-A` | DATE | **accepted** | accepted | yes | fn only | 111 20260922012521 |
| `V0-READ-DATE-B` | DATE | **accepted** | accepted | yes | fn only | 111 20260922012523 |
| `V0-READ-HELP-A` | HELP | **accepted** | accepted | yes | fn only | 100 help text follows |
| `V0-READ-HELP-B` | HELP | **accepted** | accepted | yes | fn only | 100 help text follows |
| `V0-READ-UNKNOWN-A` | an unknown command is refused with 500 | **refused** | refused | yes | fn only | 500 command not recognized |
| `V0-READ-UNKNOWN-B` | an unknown command is refused with 500 | **refused** | refused | yes | fn only | 500 command not recognized |
| `V0-READ-FRAMING-A` | a command split across two TCP segments is answered once, the same way | **accepted** | accepted | yes | fn only | DATE split across two segments answered '111 20260922012521' against '111 20260922012521' |
| `V0-READ-FRAMING-B` | a command split across two TCP segments is answered once, the same way | **accepted** | accepted | yes | fn only | DATE split across two segments answered '111 20260922012523' against '111 20260922012523' |
| `V0-PIN-DISPATCHED-A` | every capability the node advertises is dispatched by the node | **not-exercised** | accepted | - | - | (not run) |
| `V0-PIN-DISPATCHED-B` | every capability the node advertises is dispatched by the node | **not-exercised** | accepted | - | - | (not run) |
| `V0-PIN-ADVERTISED-A` | every command the node dispatches is advertised in CAPABILITIES | **not-exercised** | accepted | - | - | (not run) |
| `V0-PIN-ADVERTISED-B` | every command the node dispatches is advertised in CAPABILITIES | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-IDENTITY-A` | the node has an RFC 5537 <path-identity> of its own | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-IDENTITY-B` | the node has an RFC 5537 <path-identity> of its own | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-INDEPENDENT-A` | each node serves its own seeded articles and 43x for the other's seeds | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-INDEPENDENT-B` | each node serves its own seeded articles and 43x for the other's seeds | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-MODE-STREAM-AB` | MODE STREAM is accepted on the peer connection | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-MODE-STREAM-BA` | MODE STREAM is accepted on the peer connection | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-OFFER-AB` | IHAVE of a wanted article answers 335 | **accepted** | accepted | yes | fn only | {"duplicate": "435", "identical": true, "offer": "335", "transfer": "235"} |
| `V0-TRANSIT-OFFER-BA` | IHAVE of a wanted article answers 335 | **accepted** | accepted | yes | fn only | {"duplicate": "435", "identical": true, "offer": "335", "transfer": "235"} |
| `V0-TRANSIT-TRANSFER-AB` | the transferred article is taken with 235 | **accepted** | accepted | yes | fn only | {"duplicate": "435", "identical": true, "offer": "335", "transfer": "235"} |
| `V0-TRANSIT-TRANSFER-BA` | the transferred article is taken with 235 | **accepted** | accepted | yes | fn only | {"duplicate": "435", "identical": true, "offer": "335", "transfer": "235"} |
| `V0-TRANSIT-IDENTICAL-AB` | the far side serves the same octets the source served | **accepted** | accepted | yes | fn only | {"duplicate": "435", "identical": true, "offer": "335", "transfer": "235"} |
| `V0-TRANSIT-IDENTICAL-BA` | the far side serves the same octets the source served | **accepted** | accepted | yes | fn only | {"duplicate": "435", "identical": true, "offer": "335", "transfer": "235"} |
| `V0-TRANSIT-DUPLICATE-AB` | a second IHAVE of the same Message-ID is refused with 435 | **refused** | refused | yes | fn only | {"duplicate": "435", "identical": true, "offer": "335", "transfer": "235"} |
| `V0-TRANSIT-DUPLICATE-BA` | a second IHAVE of the same Message-ID is refused with 435 | **refused** | refused | yes | fn only | {"duplicate": "435", "identical": true, "offer": "335", "transfer": "235"} |
| `V0-TRANSIT-LOOP-AB` | an article whose Path already names the target is refused after its 335 | **not-exercised** | refused | - | - | (not run) |
| `V0-TRANSIT-LOOP-BA` | an article whose Path already names the target is refused after its 335 | **not-exercised** | refused | - | - | (not run) |
| `V0-TRANSIT-LOOP-ABSENT-AB` | the refused loop article is not served by the target afterwards | **not-exercised** | refused | - | - | (not run) |
| `V0-TRANSIT-LOOP-ABSENT-BA` | the refused loop article is not served by the target afterwards | **not-exercised** | refused | - | - | (not run) |
| `V0-TRANSIT-CHECK-FRESH-AB` | CHECK of a Message-ID the target has not seen answers 238 | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-CHECK-FRESH-BA` | CHECK of a Message-ID the target has not seen answers 238 | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-TAKETHIS-AB` | TAKETHIS of that wanted article answers 239 | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-TAKETHIS-BA` | TAKETHIS of that wanted article answers 239 | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-CHECK-DUP-AB` | CHECK of an article the target holds answers 438 | **not-exercised** | refused | - | - | (not run) |
| `V0-TRANSIT-CHECK-DUP-BA` | CHECK of an article the target holds answers 438 | **not-exercised** | refused | - | - | (not run) |
| `V0-TRANSIT-TAKETHIS-DUP-AB` | TAKETHIS that ignores that advice answers 439, never a 2xx and never a retry | **not-exercised** | refused | - | - | (not run) |
| `V0-TRANSIT-TAKETHIS-DUP-BA` | TAKETHIS that ignores that advice answers 439, never a 2xx and never a retry | **not-exercised** | refused | - | - | (not run) |
| `V0-FEED-QUEUE` | an article accepted on the source enters the matching peer's outbound queue | **accepted** | accepted | yes | fn only | {"duplicate": "435", "identity": {"restart-a": {"core": "/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host.core", "core_sha256": "eaa5b56c8337b5c6b02eb |
| `V0-FEED-OFFER` | the owner opens the session and offers it, with no hand-driven socket | **accepted** | accepted | yes | fn only | {"ab": {"duplicate": "435", "identical": true}, "ba": {"duplicate": "435", "identical": true}} |
| `V0-FEED-ONCE` | an acknowledged transfer is not offered a second time | **not-exercised** | accepted | - | - | (not run) |
| `V0-FEED-JOURNAL` | the feed journal records the transfer and survives a restart | **accepted** | accepted | yes | fn only | {"duplicate": "435", "identity": {"restart-a": {"core": "/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host.core", "core_sha256": "eaa5b56c8337b5c6b02eb |
| `V0-CRASH-CHECKPOINT` | a checkpoint is published and the store reopens from it | **not-exercised** | accepted | - | - | (not run) |
| `V0-CRASH-KILL` | node B is SIGKILLed inside a transfer it had already agreed to take | **not-exercised** | - | - | - | (not run) |
| `V0-CRASH-SURVIVOR` | node A is unaffected by node B's death | **not-exercised** | accepted | - | - | (not run) |
| `V0-CRASH-RECOVER` | node B recovers through the real recovery path | **not-exercised** | accepted | - | - | (not run) |
| `V0-CRASH-ACKNOWLEDGED` | everything node B acknowledged is still there after the recovery | **not-exercised** | accepted | - | - | (not run) |
| `V0-CRASH-INTERRUPTED` | the interrupted transfer is not there after the recovery | **not-exercised** | refused | - | - | (not run) |
| `V0-CRASH-RESTART` | node B serves again after the recovery | **not-exercised** | accepted | - | - | (not run) |
| `V0-CRASH-CUT-TABLE` | the declared cut table still matches the fault points in the host | **not-exercised** | accepted | - | - | (not run) |
| `V0-CRASH-CAMPAIGN` | the process-death campaign runs its cuts and each recovers to a state the model expresses | **not-exercised** | accepted | - | - | (not run) |
| `V0-BP-IMAGE` | the native image carrying the convergence layer builds | **not-exercised** | accepted | - | - | (not run) |
| `V0-BP-EXCHANGE` | one bundle each way inside one TCPCLv4 session | **not-exercised** | accepted | - | - | (not run) |
| `V0-BP-REFUSED` | a contact the layer refuses is refused | **not-exercised** | refused | - | - | (not run) |
| `V0-BP-KEEPALIVE` | the session keepalive holds an idle contact open | **not-exercised** | accepted | - | - | (not run) |
| `V0-BP-CRASH` | an interrupted contact loses and duplicates nothing | **not-exercised** | accepted | - | - | (not run) |
| `V0-BP-PROFILE` | the session profile is the one the layer declared | **not-exercised** | accepted | - | - | (not run) |
| `V0-BP-REPLAY` | the transfer replays from the session log | **not-exercised** | accepted | - | - | (not run) |
| `V0-BP-NODE` | a BP node behind the layer carries an fn article between the two nodes | **not-exercised** | accepted | - | - | (not run) |
| `V0-STX-SIGN` | fn statement sign produces a canonical FN-Statement field | **not-exercised** | accepted | - | - | (not run) |
| `V0-STX-ATTACH` | the field is attached to an article as a header line | **not-exercised** | accepted | - | - | (not run) |
| `V0-STX-CROSS` | the statement-bearing article crosses to the other node unchanged | **not-exercised** | accepted | - | - | (not run) |
| `V0-STX-VERIFY` | the receiving node computes its own verdict on it | **not-exercised** | accepted | - | - | (not run) |
| `V0-STX-UNVERIFIED` | a tampered statement is unverified, distinct from absent | **not-exercised** | refused | - | - | (not run) |
| `V0-STX-READER` | the reader exposes the statement octets and the recorded verdict | **not-exercised** | accepted | - | - | (not run) |
| `V0-MEDIA-EXPORT` | a carried volume is written from one node's store | **not-exercised** | accepted | - | - | (not run) |
| `V0-MEDIA-VERIFY` | the volume's copy check passes on its own | **not-exercised** | accepted | - | - | (not run) |
| `V0-MEDIA-IMPORT` | the other node imports it as a network receipt | **not-exercised** | accepted | - | - | (not run) |
| `V0-SCALE-CEILING` | the store size at which a post or a recover crosses its deadline | **not-exercised** | accepted | - | - | (not run) |
| `V0-INN-INTEROP` | a real INN server exchanges with an fn node as a third peer | **not-exercised** | accepted | - | - | (not run) |
| `V0-CLIENT-NNTPLIB-A` | an independent stdlib nntplib client reads a group and an article | **not-exercised** | accepted | - | - | (not run) |
| `V0-CLIENT-NNTPLIB-B` | an independent stdlib nntplib client reads a group and an article | **not-exercised** | accepted | - | - | (not run) |
| `V0-CLIENT-SLRN` | slrn reads a group and an article | **not-exercised** | accepted | - | - | (not run) |

### What every row that is not an outcome is waiting for

- `V0-NODE-INIT-A` (not-built): the public native operator has no init/reinit command; this native slice uses the two explicitly supplied, preprovisioned configurations -- owned by `native operator init surface`
- `V0-NODE-INIT-B` (not-built): the public native operator has no init/reinit command; this native slice uses the two explicitly supplied, preprovisioned configurations -- owned by `native operator init surface`
- `V0-NODE-CONFIG-A` (not-built): the public native operator has no init/reinit command; this native slice uses the two explicitly supplied, preprovisioned configurations -- owned by `native operator init surface`
- `V0-NODE-CONFIG-B` (not-built): the public native operator has no init/reinit command; this native slice uses the two explicitly supplied, preprovisioned configurations -- owned by `native operator init surface`
- `V0-NODE-REINIT-A` (not-built): the public native operator has no init/reinit command; this native slice uses the two explicitly supplied, preprovisioned configurations -- owned by `native operator init surface`
- `V0-NODE-REINIT-B` (not-built): the public native operator has no init/reinit command; this native slice uses the two explicitly supplied, preprovisioned configurations -- owned by `native operator init surface`
- `V0-NODE-REINIT-SAFE-A` (not-built): the public native operator has no init/reinit command; this native slice uses the two explicitly supplied, preprovisioned configurations -- owned by `native operator init surface`
- `V0-NODE-REINIT-SAFE-B` (not-built): the public native operator has no init/reinit command; this native slice uses the two explicitly supplied, preprovisioned configurations -- owned by `native operator init surface`
- `V0-NODE-STOP-A` (not-built): the native public operator has no orderly stop command or stop-result contract; harness process cleanup is not an operator outcome -- owned by `native control surface`
- `V0-NODE-STOP-B` (not-built): the native public operator has no orderly stop command or stop-result contract; harness process cleanup is not an operator outcome -- owned by `native control surface`
- `V0-NODE-LOOPBACK` (not-exercised): this slice consumes existing configs and does not synthesize a second config solely to test the loopback refusal
- `V0-OUT-ACCEPTED-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-OUT-ACCEPTED-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-OUT-REFUSED-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-OUT-REFUSED-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-OUT-UNCERTAIN-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-OUT-UNCERTAIN-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-OUT-RECOVER-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-OUT-RECOVER-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-GROUP-CREATE-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-GROUP-CREATE-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-GROUP-SERVED-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-GROUP-SERVED-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-GROUP-RETIRE-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-GROUP-RETIRE-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-GROUP-UNKNOWN-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-GROUP-UNKNOWN-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-CAP-SET-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-CAP-SET-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-CAP-REFUSE-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-CAP-REFUSE-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-PEER-ADD-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-PEER-ADD-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-PEER-LIST-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-PEER-LIST-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-PEER-ABSENT` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-PEER-REMOVE` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-CFG-LIVE` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-CFG-LIVE-REFUSE` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-AUTH-NEW` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-AUTH-PASSWORD-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-AUTH-PASSWORD-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-AUTH-LIST-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-AUTH-LIST-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-AUTH-ADVERTISED-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-AUTH-ADVERTISED-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-AUTH-GATED-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-AUTH-GATED-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-AUTH-LOGIN-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-AUTH-LOGIN-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-AUTH-WITHDRAWN-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-AUTH-WITHDRAWN-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-AUTH-POST-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-AUTH-POST-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-AUTH-WRONG-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-AUTH-WRONG-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-POST-CONCURRENT` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-PIN-DISPATCHED-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-PIN-DISPATCHED-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-PIN-ADVERTISED-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-PIN-ADVERTISED-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-TRANSIT-IDENTITY-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-TRANSIT-IDENTITY-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-TRANSIT-INDEPENDENT-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-TRANSIT-INDEPENDENT-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-TRANSIT-MODE-STREAM-AB` (not-exercised): the shared native witness does not drive this transit command or loop/error case
- `V0-TRANSIT-MODE-STREAM-BA` (not-exercised): the shared native witness does not drive this transit command or loop/error case
- `V0-TRANSIT-LOOP-AB` (not-exercised): the shared native witness does not drive this transit command or loop/error case
- `V0-TRANSIT-LOOP-BA` (not-exercised): the shared native witness does not drive this transit command or loop/error case
- `V0-TRANSIT-LOOP-ABSENT-AB` (not-exercised): the shared native witness does not drive this transit command or loop/error case
- `V0-TRANSIT-LOOP-ABSENT-BA` (not-exercised): the shared native witness does not drive this transit command or loop/error case
- `V0-TRANSIT-CHECK-FRESH-AB` (not-exercised): the shared native witness does not drive this transit command or loop/error case
- `V0-TRANSIT-CHECK-FRESH-BA` (not-exercised): the shared native witness does not drive this transit command or loop/error case
- `V0-TRANSIT-TAKETHIS-AB` (not-exercised): the shared native witness does not drive this transit command or loop/error case
- `V0-TRANSIT-TAKETHIS-BA` (not-exercised): the shared native witness does not drive this transit command or loop/error case
- `V0-TRANSIT-CHECK-DUP-AB` (not-exercised): the shared native witness does not drive this transit command or loop/error case
- `V0-TRANSIT-CHECK-DUP-BA` (not-exercised): the shared native witness does not drive this transit command or loop/error case
- `V0-TRANSIT-TAKETHIS-DUP-AB` (not-exercised): the shared native witness does not drive this transit command or loop/error case
- `V0-TRANSIT-TAKETHIS-DUP-BA` (not-exercised): the shared native witness does not drive this transit command or loop/error case
- `V0-FEED-ONCE` (not-exercised): 435 answers a manually opened inbound IHAVE; this witness does not observe the owner queue after acknowledgement
- `V0-CRASH-CHECKPOINT` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-CRASH-KILL` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-CRASH-SURVIVOR` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-CRASH-RECOVER` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-CRASH-ACKNOWLEDGED` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-CRASH-INTERRUPTED` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-CRASH-RESTART` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-CRASH-CUT-TABLE` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-CRASH-CAMPAIGN` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-BP-IMAGE` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-BP-EXCHANGE` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-BP-REFUSED` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-BP-KEEPALIVE` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-BP-CRASH` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-BP-PROFILE` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-BP-REPLAY` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-BP-NODE` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-STX-SIGN` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-STX-ATTACH` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-STX-CROSS` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-STX-VERIFY` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-STX-UNVERIFIED` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-STX-READER` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-MEDIA-EXPORT` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-MEDIA-VERIFY` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-MEDIA-IMPORT` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-SCALE-CEILING` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-INN-INTEROP` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-CLIENT-NNTPLIB-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-CLIENT-NNTPLIB-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-CLIENT-SLRN` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which

### What each row does not show

- `V0-NODE-REINIT-A`: nothing in docs/operator.md says whether a second `init` adopts the store or refuses, so this row records the outcome rather than asserting one; the property that matters is the next row
- `V0-NODE-REINIT-B`: nothing in docs/operator.md says whether a second `init` adopts the store or refuses, so this row records the outcome rather than asserting one; the property that matters is the next row
- `V0-NODE-STATUS-A`: the public native operator read one preprovisioned store; this slice did not create or alter its configuration
- `V0-NODE-STATUS-B`: the public native operator read one preprovisioned store; this slice did not create or alter its configuration
- `V0-NODE-START-A`: the entry point that started is `native-operator`; every served row for this node is about that process, not about the ones above it in the list, which was given --max-connections 64
- `V0-NODE-START-B`: the entry point that started is `native-operator`; every served row for this node is about that process, not about the ones above it in the list, which was given --max-connections 64
- `V0-POST-COMMIT-A`: one article; the durability behind the 240 is the store's, asserted by the recovery rows below
- `V0-POST-COMMIT-B`: one article; the durability behind the 240 is the store's, asserted by the recovery rows below
- `V0-POST-DUPLICATE-A`: the duplicate is offered on a fresh connection because one clock observation is pinned per connection at accept
- `V0-POST-DUPLICATE-B`: the duplicate is offered on a fresh connection because one clock observation is pinned per connection at accept
- `V0-POST-CLOCK-A`: a 441 for an article the node already holds and a 441 for a clock the node no longer has are the same code; DATE is what separates them from outside, because a refused reading costs the owner its clock (D10-a) and DATE then answers 503. This row does not INDUCE a clock fault -- it checks that an ordinary duplicate did not cause one
- `V0-POST-CLOCK-B`: a 441 for an article the node already holds and a 441 for a clock the node no longer has are the same code; DATE is what separates them from outside, because a refused reading costs the owner its clock (D10-a) and DATE then answers 503. This row does not INDUCE a clock fault -- it checks that an ordinary duplicate did not cause one
- `V0-READ-CAPABILITIES-A`: served by `native-operator` on port 11190
- `V0-READ-CAPABILITIES-B`: served by `native-operator` on port 11191
- `V0-READ-MODE-READER-A`: served by `native-operator` on port 11190
- `V0-READ-MODE-READER-B`: served by `native-operator` on port 11191
- `V0-READ-LIST-ACTIVE-A`: served by `native-operator` on port 11190
- `V0-READ-LIST-ACTIVE-B`: served by `native-operator` on port 11191
- `V0-READ-LIST-NEWSGROUPS-A`: served by `native-operator` on port 11190
- `V0-READ-LIST-NEWSGROUPS-B`: served by `native-operator` on port 11191
- `V0-READ-LIST-OVERVIEW-FMT-A`: served by `native-operator` on port 11190
- `V0-READ-LIST-OVERVIEW-FMT-B`: served by `native-operator` on port 11191
- `V0-READ-LIST-ACTIVE-TIMES-A`: served by `native-operator` on port 11190
- `V0-READ-LIST-ACTIVE-TIMES-B`: served by `native-operator` on port 11191
- `V0-READ-LIST-HEADERS-A`: served by `native-operator` on port 11190
- `V0-READ-LIST-HEADERS-B`: served by `native-operator` on port 11191
- `V0-READ-GROUP-A`: served by `native-operator` on port 11190
- `V0-READ-GROUP-B`: served by `native-operator` on port 11191
- `V0-READ-LISTGROUP-A`: served by `native-operator` on port 11190
- `V0-READ-LISTGROUP-B`: served by `native-operator` on port 11191
- `V0-READ-ARTICLE-A`: served by `native-operator` on port 11190
- `V0-READ-ARTICLE-B`: served by `native-operator` on port 11191
- `V0-READ-HEAD-A`: served by `native-operator` on port 11190
- `V0-READ-HEAD-B`: served by `native-operator` on port 11191
- `V0-READ-BODY-A`: served by `native-operator` on port 11190
- `V0-READ-BODY-B`: served by `native-operator` on port 11191
- `V0-READ-STAT-A`: served by `native-operator` on port 11190
- `V0-READ-STAT-B`: served by `native-operator` on port 11191
- `V0-READ-ARTICLE-MSGID-A`: served by `native-operator` on port 11190
- `V0-READ-ARTICLE-MSGID-B`: served by `native-operator` on port 11191
- `V0-READ-ARTICLE-ABSENT-A`: served by `native-operator` on port 11190
- `V0-READ-ARTICLE-ABSENT-B`: served by `native-operator` on port 11191
- `V0-READ-OVER-A`: served by `native-operator` on port 11190
- `V0-READ-OVER-B`: served by `native-operator` on port 11191
- `V0-READ-OVER-RANGE-A`: served by `native-operator` on port 11190
- `V0-READ-OVER-RANGE-B`: served by `native-operator` on port 11191
- `V0-READ-HDR-A`: served by `native-operator` on port 11190
- `V0-READ-HDR-B`: served by `native-operator` on port 11191
- `V0-READ-XOVER-A`: served by `native-operator` on port 11190
- `V0-READ-XOVER-B`: served by `native-operator` on port 11191
- `V0-READ-XHDR-A`: served by `native-operator` on port 11190
- `V0-READ-XHDR-B`: served by `native-operator` on port 11191
- `V0-READ-XPAT-A`: served by `native-operator` on port 11190
- `V0-READ-XPAT-B`: served by `native-operator` on port 11191
- `V0-READ-NEXT-A`: the expected outcome depends on how many articles the group holds; the row records the count it was run against; served by `native-operator` on port 11190; the group held 1 article(s) when this ran, and with one article 421/422 is the correct answer
- `V0-READ-NEXT-B`: the expected outcome depends on how many articles the group holds; the row records the count it was run against; served by `native-operator` on port 11191; the group held 1 article(s) when this ran, and with one article 421/422 is the correct answer
- `V0-READ-LAST-A`: the expected outcome depends on where the cursor was; served by `native-operator` on port 11190; the group held 1 article(s) when this ran, and with one article 421/422 is the correct answer
- `V0-READ-LAST-B`: the expected outcome depends on where the cursor was; served by `native-operator` on port 11191; the group held 1 article(s) when this ran, and with one article 421/422 is the correct answer
- `V0-READ-DATE-A`: served by `native-operator` on port 11190
- `V0-READ-DATE-B`: served by `native-operator` on port 11191
- `V0-READ-HELP-A`: served by `native-operator` on port 11190
- `V0-READ-HELP-B`: served by `native-operator` on port 11191
- `V0-READ-UNKNOWN-A`: served by `native-operator` on port 11190
- `V0-READ-UNKNOWN-B`: served by `native-operator` on port 11191
- `V0-READ-FRAMING-A`: one command split at one point; the chunk-independence keystone is books/wire-invariants', not this row
- `V0-READ-FRAMING-B`: one command split at one point; the chunk-independence keystone is books/wire-invariants', not this row
- `V0-TRANSIT-IDENTITY-A`: `fn-peer-local-identity` reads the `path-identity` policy slot and an unset slot is the empty string, which `fn-path-names-p` never matches: a node without this answers no loop, so V0-TRANSIT-LOOP rests on it
- `V0-TRANSIT-IDENTITY-B`: `fn-peer-local-identity` reads the `path-identity` policy slot and an unset slot is the empty string, which `fn-path-names-p` never matches: a node without this answers no loop, so V0-TRANSIT-LOOP rests on it
- `V0-TRANSIT-OFFER-AB`: tests.test_native_peering sent IHAVE and observed 335
- `V0-TRANSIT-OFFER-BA`: tests.test_native_peering sent IHAVE and observed 335
- `V0-TRANSIT-TRANSFER-AB`: the peer accepted the transferred RFC 3977 block with 235
- `V0-TRANSIT-TRANSFER-BA`: the peer accepted the transferred RFC 3977 block with 235
- `V0-TRANSIT-IDENTICAL-AB`: the target-served article octets equal the sent block
- `V0-TRANSIT-IDENTICAL-BA`: the target-served article octets equal the sent block
- `V0-TRANSIT-DUPLICATE-AB`: a repeated IHAVE received 435
- `V0-TRANSIT-DUPLICATE-BA`: a repeated IHAVE received 435
- `V0-FEED-QUEUE`: the restart witness found FNFD intent
- `V0-FEED-OFFER`: the public owner delivered both directions
- `V0-FEED-JOURNAL`: intent survived source death and restart
- `V0-CRASH-KILL`: what the client saw is recorded; an acknowledgement after the kill would be the defect, and its absence is the assertion
- `V0-SCALE-CEILING`: a measured ceiling on one box with one payload grid; it is not a bound and not a proof

### The exact invocation of every row

- `V0-NODE-INIT-A`: `packaging/fn-native operator CONFIG`
- `V0-NODE-INIT-B`: `packaging/fn-native operator CONFIG`
- `V0-NODE-CONFIG-A`: `packaging/fn-native operator CONFIG`
- `V0-NODE-CONFIG-B`: `packaging/fn-native operator CONFIG`
- `V0-NODE-REINIT-A`: `packaging/fn-native operator CONFIG`
- `V0-NODE-REINIT-B`: `packaging/fn-native operator CONFIG`
- `V0-NODE-REINIT-SAFE-A`: `packaging/fn-native operator CONFIG`
- `V0-NODE-REINIT-SAFE-B`: `packaging/fn-native operator CONFIG`
- `V0-NODE-STATUS-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml status`
- `V0-NODE-STATUS-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml status`
- `V0-NODE-START-A`: `env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml run`
- `V0-NODE-START-B`: `env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml run`
- `V0-NODE-STOP-A`: `harness process cleanup`
- `V0-NODE-STOP-B`: `harness process cleanup`
- `V0-NODE-LOOPBACK`: `packaging/fn-native operator CONFIG run`
- `V0-OUT-ACCEPTED-A`: `(none)`
- `V0-OUT-ACCEPTED-B`: `(none)`
- `V0-OUT-REFUSED-A`: `(none)`
- `V0-OUT-REFUSED-B`: `(none)`
- `V0-OUT-UNCERTAIN-A`: `(none)`
- `V0-OUT-UNCERTAIN-B`: `(none)`
- `V0-OUT-RECOVER-A`: `(none)`
- `V0-OUT-RECOVER-B`: `(none)`
- `V0-GROUP-CREATE-A`: `(none)`
- `V0-GROUP-CREATE-B`: `(none)`
- `V0-GROUP-SERVED-A`: `(none)`
- `V0-GROUP-SERVED-B`: `(none)`
- `V0-GROUP-RETIRE-A`: `(none)`
- `V0-GROUP-RETIRE-B`: `(none)`
- `V0-GROUP-UNKNOWN-A`: `(none)`
- `V0-GROUP-UNKNOWN-B`: `(none)`
- `V0-CAP-SET-A`: `(none)`
- `V0-CAP-SET-B`: `(none)`
- `V0-CAP-REFUSE-A`: `(none)`
- `V0-CAP-REFUSE-B`: `(none)`
- `V0-PEER-ADD-A`: `(none)`
- `V0-PEER-ADD-B`: `(none)`
- `V0-PEER-LIST-A`: `(none)`
- `V0-PEER-LIST-B`: `(none)`
- `V0-PEER-ABSENT`: `(none)`
- `V0-PEER-REMOVE`: `(none)`
- `V0-CFG-LIVE`: `(none)`
- `V0-CFG-LIVE-REFUSE`: `(none)`
- `V0-AUTH-NEW`: `(none)`
- `V0-AUTH-PASSWORD-A`: `(none)`
- `V0-AUTH-PASSWORD-B`: `(none)`
- `V0-AUTH-LIST-A`: `(none)`
- `V0-AUTH-LIST-B`: `(none)`
- `V0-AUTH-ADVERTISED-A`: `(none)`
- `V0-AUTH-ADVERTISED-B`: `(none)`
- `V0-AUTH-GATED-A`: `(none)`
- `V0-AUTH-GATED-B`: `(none)`
- `V0-AUTH-LOGIN-A`: `(none)`
- `V0-AUTH-LOGIN-B`: `(none)`
- `V0-AUTH-WITHDRAWN-A`: `(none)`
- `V0-AUTH-WITHDRAWN-B`: `(none)`
- `V0-AUTH-POST-A`: `(none)`
- `V0-AUTH-POST-B`: `(none)`
- `V0-AUTH-WRONG-A`: `(none)`
- `V0-AUTH-WRONG-B`: `(none)`
- `V0-POST-OPEN-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --user '' --secret ''`
- `V0-POST-OPEN-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --user '' --secret ''`
- `V0-POST-COMMIT-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --user '' --secret ''`
- `V0-POST-COMMIT-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --user '' --secret ''`
- `V0-POST-READBACK-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --user '' --secret ''`
- `V0-POST-READBACK-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --user '' --secret ''`
- `V0-POST-FRESH-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --user '' --secret ''`
- `V0-POST-FRESH-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --user '' --secret ''`
- `V0-POST-DUPLICATE-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --user '' --secret ''`
- `V0-POST-DUPLICATE-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --user '' --secret ''`
- `V0-POST-CLOCK-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --user '' --secret ''`
- `V0-POST-CLOCK-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --user '' --secret ''`
- `V0-POST-CONCURRENT`: `(none)`
- `V0-READ-CAPABILITIES-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-CAPABILITIES-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-MODE-READER-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-MODE-READER-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-OVERVIEW-FMT-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-OVERVIEW-FMT-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-TIMES-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-TIMES-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-HEADERS-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-HEADERS-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-GROUP-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-GROUP-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LISTGROUP-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LISTGROUP-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HEAD-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HEAD-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-BODY-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-BODY-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-STAT-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-STAT-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-MSGID-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-MSGID-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-ABSENT-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-ABSENT-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-RANGE-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-RANGE-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HDR-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HDR-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XOVER-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XOVER-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XHDR-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XHDR-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XPAT-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XPAT-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEXT-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEXT-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LAST-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LAST-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-DATE-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-DATE-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HELP-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HELP-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-UNKNOWN-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-UNKNOWN-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-FRAMING-A`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-FRAMING-B`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-PIN-DISPATCHED-A`: `(none)`
- `V0-PIN-DISPATCHED-B`: `(none)`
- `V0-PIN-ADVERTISED-A`: `(none)`
- `V0-PIN-ADVERTISED-B`: `(none)`
- `V0-TRANSIT-IDENTITY-A`: `(none)`
- `V0-TRANSIT-IDENTITY-B`: `(none)`
- `V0-TRANSIT-INDEPENDENT-A`: `(none)`
- `V0-TRANSIT-INDEPENDENT-B`: `(none)`
- `V0-TRANSIT-MODE-STREAM-AB`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-MODE-STREAM-BA`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-OFFER-AB`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-OFFER-BA`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-TRANSFER-AB`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-TRANSFER-BA`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-IDENTICAL-AB`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-IDENTICAL-BA`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-DUPLICATE-AB`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-DUPLICATE-BA`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-LOOP-AB`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-LOOP-BA`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-LOOP-ABSENT-AB`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-LOOP-ABSENT-BA`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-CHECK-FRESH-AB`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-CHECK-FRESH-BA`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-TAKETHIS-AB`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-TAKETHIS-BA`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-CHECK-DUP-AB`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-CHECK-DUP-BA`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-TAKETHIS-DUP-AB`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-TRANSIT-TAKETHIS-DUP-BA`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-FEED-QUEUE`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-FEED-OFFER`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-FEED-ONCE`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-FEED-JOURNAL`: `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-CRASH-CHECKPOINT`: `(none)`
- `V0-CRASH-KILL`: `(none)`
- `V0-CRASH-SURVIVOR`: `(none)`
- `V0-CRASH-RECOVER`: `(none)`
- `V0-CRASH-ACKNOWLEDGED`: `(none)`
- `V0-CRASH-INTERRUPTED`: `(none)`
- `V0-CRASH-RESTART`: `(none)`
- `V0-CRASH-CUT-TABLE`: `(none)`
- `V0-CRASH-CAMPAIGN`: `(none)`
- `V0-BP-IMAGE`: `(none)`
- `V0-BP-EXCHANGE`: `(none)`
- `V0-BP-REFUSED`: `(none)`
- `V0-BP-KEEPALIVE`: `(none)`
- `V0-BP-CRASH`: `(none)`
- `V0-BP-PROFILE`: `(none)`
- `V0-BP-REPLAY`: `(none)`
- `V0-BP-NODE`: `(none)`
- `V0-STX-SIGN`: `(none)`
- `V0-STX-ATTACH`: `(none)`
- `V0-STX-CROSS`: `(none)`
- `V0-STX-VERIFY`: `(none)`
- `V0-STX-UNVERIFIED`: `(none)`
- `V0-STX-READER`: `(none)`
- `V0-MEDIA-EXPORT`: `(none)`
- `V0-MEDIA-VERIFY`: `(none)`
- `V0-MEDIA-IMPORT`: `(none)`
- `V0-SCALE-CEILING`: `(none)`
- `V0-INN-INTEROP`: `(none)`
- `V0-CLIENT-NNTPLIB-A`: `(none)`
- `V0-CLIENT-NNTPLIB-B`: `(none)`
- `V0-CLIENT-SLRN`: `(none)`

## Every command

| # | step | rc | first line | s |
| --- | --- | --- | --- | --- |
| 1 | preflight | 0 | `os=Ubuntu 25.10 kernel=Linux 6.17.0-40-generic arch=x86_64 cores=24` | 1.3 |
| 2 | acquire deploy lock | 0 | `` | 0.4 |
| 3 | ship archive | 0 | `` | 2.7 |
| 4 | make run dir | 0 | `` | 0.4 |
| 5 | install drive.py | 0 | `` | 0.4 |
| 6 | install feed.py | 0 | `` | 0.3 |
| 7 | install matrix.py | 0 | `` | 0.4 |
| 8 | native packaged operator subject | 0 | `NATIVE-LAUNCHER-DIGEST ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142` | 1.5 |
| 9 | node A native run directory | 0 | `` | 0.3 |
| 10 | node A native config exists | 0 | `` | 0.3 |
| 11 | node A native operator status | 0 | `transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment` | 0.4 |
| 12 | node B native run directory | 0 | `` | 0.3 |
| 13 | node B native config exists | 0 | `` | 0.3 |
| 14 | node B native operator status | 0 | `transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment` | 0.3 |
| 15 | start server (node A (native-operator), a-main) | 0 | `LISTENING 11190` | 1.4 |
| 16 | node A pid | 0 | `2160265` | 0.6 |
| 17 | start server (node B (native-operator), b-main) | 0 | `LISTENING 11191` | 1.7 |
| 18 | node B pid | 0 | `2160596` | 0.6 |
| 19 | node A server is alive | 0 | `ALIVE` | 0.5 |
| 20 | node A POST cycle | 0 | `{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-1e2` | 0.4 |
| 21 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 22 | node A reader surface | 0 | `{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES ` | 0.7 |
| 23 | node B server is alive | 0 | `ALIVE` | 1.1 |
| 24 | node B POST cycle | 0 | `{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-b32` | 0.4 |
| 25 | node B server is alive | 0 | `ALIVE` | 0.5 |
| 26 | node B reader surface | 0 | `{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES ` | 1.0 |
| 27 | native public peering/restart witness | 0 | `NATIVE-PEERING-EXPECTED-RUNTIME b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5` | 7.0 |
| 28 | stop server node A (main) | 0 | `stopped` | 2.3 |
| 29 | stop server node B (main) | 0 | `stopped` | 1.9 |
| 30 | stop server node A (main) | 0 | `stopped` | 0.9 |
| 31 | stop the tap in front of node A | 0 | `stopped` | 0.5 |
| 32 | stop server node B (main) | 0 | `stopped` | 0.6 |
| 33 | stop the tap in front of node B | 0 | `stopped` | 0.7 |
| 34 | stray fn processes | 0 | `CLEAN` | 0.6 |
| 35 | remove the deploy tree | 0 | `` | 0.6 |
| 36 | release deploy lock | 0 | `` | 0.6 |

### Commands in full

1. **preflight** -- `. /etc/os-release 2>/dev/null || true ; echo "os=${PRETTY_NAME:-unknown} kernel=$(uname -sr) arch=$(uname -m) cores=$(nproc 2>/dev/null || echo ?)" ; echo "python3=$(python3 -V 2>&1)" ; for p in python3.9 python3.10 python3.11 python3.12; do ; command -v $p >/dev/null && echo "alt=$p $($p -V 2>&1)" ; done ; for c in slrn tin nn trn inews expect script; do ; printf 'client %s=%s\n' "$c" "$(comma...`
2. **acquire deploy lock** -- `mkdir -p $HOME/fn-deploy/.locks ; if ! mkdir $HOME/fn-deploy/.locks/native915-2202a95.lock 2>/dev/null; then ; echo "deploy identity is already active: native915-2202a95" ; exit 73 ; fi`
3. **ship archive** -- `git archive 2202a95 | tar -x -C $HOME/fn-deploy/native915-2202a95`
4. **make run dir** -- `mkdir -p $HOME/fn-deploy/native915-2202a95/gate-run`
5. **install drive.py** -- `base64 -d > $HOME/fn-deploy/native915-2202a95/gate-run/drive.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJJbmRlcGVuZGVudCBOTlRQIGRyaXZpbmcgZm9yIHRo ; ZSBkZXBsb3kgZ2F0ZTsgbm8gZm4gbW9kdWxlIGlzIGltcG9ydGVkLiIiIgppbXBvcnQgYXJncGFy ; c2UsIGpzb24sIG9zLCBzb2NrZXQsIHN5cywgdGltZQoKCmNsYXNzIENvbm46CiAgICBkZWYgX19p ; bml0X18oc2VsZiwgcG9ydCwgdGltZW91dD0zMCk6CiAgICAgICAgc2VsZi5zb2NrID0gc29ja2V0 ;...`
6. **install feed.py** -- `base64 -d > $HOME/fn-deploy/native915-2202a95/gate-run/feed.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJUaGUgdHdvLW5vZGUgcGhhc2VzLiAgTm8gZm4gbW9k ; dWxlIGlzIGltcG9ydGVkOyBDb25uIGlzIGRlcGxveV9nYXRlJ3MuCgpgcHJlc2VuY2VgIGlzIHRo ; ZSBjb250cm9sIGFuZCB0aGUgcmVyZWFkOiB3aGF0IGEgbm9kZSBob2xkcyBhbmQgd2hhdCBpdCBt ; dXN0Cm5vdC4gIGByZWxheWAgaXMgUkZDIDM5NzcgNi4zLjIgZHJpdmVuIGJ5IGhhbmQgb3ZlciBh ; ...`
7. **install matrix.py** -- `base64 -d > $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJUaGUgdjAgbWF0cml4J3Mgb3duIE5OVFAgcGhhc2Vz ; LiAgTm8gZm4gbW9kdWxlIGlzIGltcG9ydGVkOyBDb25uIGlzCnRvb2xzL2RlcGxveV9nYXRlLnB5 ; J3MgZHJpdmVyLCBzaGlwcGVkIGJlc2lkZSB0aGlzIGZpbGUgYXMgZHJpdmUucHkuCgpFdmVyeSBw ; aGFzZSBwcmludHMgT05FIGpzb24gb2JqZWN0IHdob3NlIGtleXMgYXJlIGNvbW1hbmQgbmFtZXMg ...`
8. **native packaged operator subject** -- `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; wrapper=packaging/fn-native ; runtime=/home/ember/fn-tools/sbcl/bin/sbcl ; test -x "$image" || { echo "NATIVE-IMAGE-MISSING $image"; exit 4; } ; test -x "$wrapper" || { echo NATIVE-WRAPPER-MISSING; exit 4; } ; test -s "$image.core" || { echo...`
9. **node A native run directory** -- `mkdir -p $HOME/fn-deploy/native915-2202a95/a`
10. **node A native config exists** -- `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; test -f /home/ember/fn-native915-matrix/a/fn.toml`
11. **node A native operator status** -- `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml status`
12. **node B native run directory** -- `mkdir -p $HOME/fn-deploy/native915-2202a95/b`
13. **node B native config exists** -- `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; test -f /home/ember/fn-native915-matrix/b/fn.toml`
14. **node B native operator status** -- `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml status`
15. **start server (node A (native-operator), a-main)** -- `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; rm -f $HOME/fn-deploy/native915-2202a95/a/server-a-main.log ; nohup env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml run > $HOME/fn-deploy/native915-2202a95/a/server-a-main.log 2>&1 < /dev/null & ; echo $! > ...`
16. **node A pid** -- `cat $HOME/fn-deploy/native915-2202a95/a/server.pid`
17. **start server (node B (native-operator), b-main)** -- `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; rm -f $HOME/fn-deploy/native915-2202a95/b/server-b-main.log ; nohup env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml run > $HOME/fn-deploy/native915-2202a95/b/server-b-main.log 2>&1 < /dev/null & ; echo $! > ...`
18. **node B pid** -- `cat $HOME/fn-deploy/native915-2202a95/b/server.pid`
19. **node A server is alive** -- `kill -0 2160265 2>/dev/null && echo ALIVE || echo DEAD`
20. **node A POST cycle** -- `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --user '' --secret ''`
21. **node A server is alive** -- `kill -0 2160265 2>/dev/null && echo ALIVE || echo DEAD`
22. **node A reader surface** -- `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-1e227a4b796c-a@example.invalid>' --absent '<absent@example.invalid>'`
23. **node B server is alive** -- `kill -0 2160596 2>/dev/null && echo ALIVE || echo DEAD`
24. **node B POST cycle** -- `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --user '' --secret ''`
25. **node B server is alive** -- `kill -0 2160596 2>/dev/null && echo ALIVE || echo DEAD`
26. **node B reader surface** -- `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; python3 $HOME/fn-deploy/native915-2202a95/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3222d2dad52-b@example.invalid>' --absent '<absent@example.invalid>'`
27. **native public peering/restart witness** -- `cd $HOME/fn-deploy/native915-2202a95 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
28. **stop server node A (main)** -- `if [ -f $HOME/fn-deploy/native915-2202a95/a/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native915-2202a95/a/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native915-2202a95/a/server.pid ; fi ; echo stopped`
29. **stop server node B (main)** -- `if [ -f $HOME/fn-deploy/native915-2202a95/b/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native915-2202a95/b/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native915-2202a95/b/server.pid ; fi ; echo stopped`
30. **stop server node A (main)** -- `if [ -f $HOME/fn-deploy/native915-2202a95/a/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native915-2202a95/a/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native915-2202a95/a/server.pid ; fi ; echo stopped`
31. **stop the tap in front of node A** -- `if [ -f $HOME/fn-deploy/native915-2202a95/a/tap.pid ]; then ; pid=$(cat $HOME/fn-deploy/native915-2202a95/a/tap.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 10); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native915-2202a95/a/tap.pid ; fi ; echo stopped`
32. **stop server node B (main)** -- `if [ -f $HOME/fn-deploy/native915-2202a95/b/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native915-2202a95/b/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native915-2202a95/b/server.pid ; fi ; echo stopped`
33. **stop the tap in front of node B** -- `if [ -f $HOME/fn-deploy/native915-2202a95/b/tap.pid ]; then ; pid=$(cat $HOME/fn-deploy/native915-2202a95/b/tap.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 10); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native915-2202a95/b/tap.pid ; fi ; echo stopped`
34. **stray fn processes** -- `pgrep -f 'fn-deploy/native915-2202a95' >/dev/null 2>&1 && echo STRAY || echo CLEAN`
35. **remove the deploy tree** -- `rm -rf $HOME/fn-deploy/native915-2202a95`
36. **release deploy lock** -- `rmdir $HOME/fn-deploy/.locks/native915-2202a95.lock`

## Findings

One row per stated assertion. `held` and `violated` are the two that
DECIDE it; `inconclusive` means this run could not decide it and so
establishes nothing; `not-exercised` and `not-built` mean it was not
reached and why; `limitation` is a scope boundary no run of this
harness crosses.

The process exit is 1 for a violation, 3 for an inconclusive run with no violation, 2 when the gate stopped early, 0 otherwise.

Verdict of this run: **held** (no findings).

| assertion | verdict | what it says |
| --- | --- | --- |

## What was NOT exercised

Nothing was skipped in this run.

Standing gaps of the gate itself, independent of this run:

- Both nodes are on ONE host, over loopback. Nothing here exercises a real
  network, a partition, latency, or two machines' clocks disagreeing.
- A SIGKILL of a server process is not a power loss, and killing one node is
  not a partition: A stays reachable throughout.
- One kill point is exercised. The enumerated cut table is
  `tests/campaign/cuts.py`; this gate does not replace it.
- The peer records are configuration, not authorization: no lane on this tree
  authenticates a peer, so a node accepts transit from whoever connects.
- No convergence claim. Two articles crossing once is not the merge property
  of specs/peering.md section 4 (K4); that needs the certified statement.
- No third node, no concurrent load, no RFC conformance audit: the
  assertions are this driver's, not a spec's.
- The `tcpcl` scenario carries opaque octets, not BPv7 bundles: TCPCLv4 does
  not parse what it transfers, and no BP node is wired to the layer yet.
- The certificates were not re-established here; see the certificate row.
- A verdict here is an observation of a reply, an exit code or a file. It is
  not a proof, and an `accepted` row says the feature ran once on one box,
  not that it is correct for every input.
- The matrix computes no identity, no group table, no charge, no frame and no
  bound: where it needed one it asked the node for it.
- A `not-built` row is this matrix's reading of a probe, not a promise from
  the lane it names.

## Raw step output

```
--- 1 preflight (rc=0)
os=Ubuntu 25.10 kernel=Linux 6.17.0-40-generic arch=x86_64 cores=24
python3=Python 3.13.7
alt=python3.12 Python 3.12.13
client slrn=ABSENT
client tin=ABSENT
client nn=ABSENT
client trn=ABSENT
client inews=ABSENT
client expect=ABSENT
client script=/usr/bin/script
acl2version= + ACL2 Version 8.7                                                     +
acl2version=unavailable on this host
--- 2 acquire deploy lock (rc=0)
--- 3 ship archive (rc=0)
--- 4 make run dir (rc=0)
--- 5 install drive.py (rc=0)
--- 6 install feed.py (rc=0)
--- 7 install matrix.py (rc=0)
--- 8 native packaged operator subject (rc=0)
NATIVE-LAUNCHER-DIGEST ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142
NATIVE-IMAGE-DIGEST 2d8259c22388119793ad3dde525497f9095bdb2489ac01e597b439f3d0ff5c09
NATIVE-RUNTIME-DIGEST b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5
NATIVE-CORE-DIGEST eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2
usage: fn operator CONFIG run [--once]
accepted operator help
--- 9 node A native run directory (rc=0)
--- 10 node A native config exists (rc=0)
--- 11 node A native operator status (rc=0)
transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment
accepted operator STATUS
--- 12 node B native run directory (rc=0)
--- 13 node B native config exists (rc=0)
--- 14 node B native operator status (rc=0)
transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment
accepted operator STATUS
--- 15 start server (node A (native-operator), a-main) (rc=0)
LISTENING 11190
--- 16 node A pid (rc=0)
2160265
--- 17 start server (node B (native-operator), b-main) (rc=0)
LISTENING 11191
--- 18 node B pid (rc=0)
2160596
--- 19 node A server is alive (rc=0)
ALIVE
--- 20 node A POST cycle (rc=0)
{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-1e227a4b796c-a@example.invalid> article follows", "DUPLICATE POST": "340 send article to be posted", "DUPLICATE": "441 posting failed; the article was refused", "DATE AFTER DUPLICATE": "111 20260922012521", "counted": true, "ok": true}
--- 21 node A server is alive (rc=0)
ALIVE
--- 22 node A reader surface (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab"], "MODE READER": "200 posting allowed", "LIST ACTIVE": "215 list of active newsgroups follows", "LIST NEWSGROUPS": "215 list of newsgroups follows", "LIST OVERVIEW.FMT": "215 order of fields in overview database", "LIST ACTIVE.TIMES": "215 information follows", "LIST HEADERS": "215 field list follows", "GROUP": "211 1 1 1 fn.letters", "group_count": 1, "group_first": 1, "group_last": 1, "LISTGROUP": "211 1 1 1 fn.letters list follows", "ARTICLE": "220 1 <native-matrix-1e227a4b796c-a@example.invalid> article follows", "HEAD": "221 1 <native-matrix-1e227a4b796c-a@example.invalid> headers follow", "BODY": "222 1 <native-matrix-1e227a4b796c-a@example.invalid> body follows", "STAT": "223 1 <native-matrix-1e227a4b796c-a@example.invalid> retrieved", "ARTICLE MSGID": "220 0 <native-matrix-1e227a4b796c-a@example.invalid> article follows", "ARTICLE ABSENT": "430 no article with that message-id", "OVER": "224 overview information follows", "OVER RANGE": "224 overview information follows", "HDR": "225 headers follow", "XOVER": "224 overview information follows", "XHDR": "221 header follows", "XPAT": "221 header follows", "NEXT": "421 no next article", "LAST": "422 no previous article", "DATE": "111 20260922012521", "HELP": "100 help text follows", "UNKNOWN": "500 command not recognized", "FRAMING": "111 20260922012521", "FRAMING SAME": true, "ok": true}
--- 23 node B server is alive (rc=0)
ALIVE
--- 24 node B POST cycle (rc=0)
{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-b3222d2dad52-b@example.invalid> article follows", "DUPLICATE POST": "340 send article to be posted", "DUPLICATE": "441 posting failed; the article was refused", "DATE AFTER DUPLICATE": "111 20260922012523", "counted": true, "ok": true}
--- 25 node B server is alive (rc=0)
ALIVE
--- 26 node B reader surface (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab"], "MODE READER": "200 posting allowed", "LIST ACTIVE": "215 list of active newsgroups follows", "LIST NEWSGROUPS": "215 list of newsgroups follows", "LIST OVERVIEW.FMT": "215 order of fields in overview database", "LIST ACTIVE.TIMES": "215 information follows", "LIST HEADERS": "215 field list follows", "GROUP": "211 1 1 1 fn.letters", "group_count": 1, "group_first": 1, "group_last": 1, "LISTGROUP": "211 1 1 1 fn.letters list follows", "ARTICLE": "220 1 <native-matrix-b3222d2dad52-b@example.invalid> article follows", "HEAD": "221 1 <native-matrix-b3222d2dad52-b@example.invalid> headers follow", "BODY": "222 1 <native-matrix-b3222d2dad52-b@example.invalid> body follows", "STAT": "223 1 <native-matrix-b3222d2dad52-b@example.invalid> retrieved", "ARTICLE MSGID": "220 0 <native-matrix-b3222d2dad52-b@example.invalid> article follows", "ARTICLE ABSENT": "430 no article with that message-id", "OVER": "224 overview information follows", "OVER RANGE": "224 overview information follows", "HDR": "225 headers follow", "XOVER": "224 overview information follows", "XHDR": "221 header follows", "XPAT": "221 header follows", "NEXT": "421 no next article", "LAST": "422 no previous article", "DATE": "111 20260922012523", "HELP": "100 help text follows", "UNKNOWN": "500 command not recognized", "FRAMING": "111 20260922012523", "FRAMING SAME": true, "ok": true}
--- 27 native public peering/restart witness (rc=0)
NATIVE-PEERING-EXPECTED-RUNTIME b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5
NATIVE-PEERING-EXPECTED-CORE eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2
test_public_native_nodes_exchange_both_ways_and_suppress_duplicate (tests.test_native_peering.NativePeeringTests.test_public_native_nodes_exchange_both_ways_and_suppress_duplicate) ... ok
test_durable_feed_requeues_after_source_process_death (tests.test_native_peering.NativePeeringTests.test_durable_feed_requeues_after_source_process_death) ... ok

----------------------------------------------------------------------
Ran 2 tests in 4.726s

OK
native-peering launcher-sha256=2d8259c22388119793ad3dde525497f9095bdb2489ac01e597b439f3d0ff5c09 core-sha256=eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2 declared-source=source-commit=915d5c729877eddee7dd3f72eadad21cca463d1a source-manifest-sha256=eb0051343d388901b48e7f1de281ba3d1f6079cab062f25060b186cf01e3aaa4
NATIVE-PEERING-WITNESS {"feed": {"ab": {"duplicate": "435", "identical": true}, "ba": {"duplicate": "435", "identical": true}}, "identity": {"a": {"core": "/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host.core", "core_sha256": "eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2", "runtime": "/home/ember/fn-tools/sbcl/bin/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}, "b": {"core": "/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host.core", "core_sha256": "eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2", "runtime": "/home/ember/fn-tools/sbcl/bin/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}}, "kind": "transit-and-feed", "transit": {"ab": {"duplicate": "435", "identical": true, "offer": "335", "transfer": "235"}, "ba": {"duplicate": "435", "identical": true, "offer": "335", "transfer": "235"}}}
NATIVE-PEERING-WITNESS {"duplicate": "435", "identity": {"restart-a": {"core": "/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host.core", "core_sha256": "eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2", "runtime": "/home/ember/fn-tools/sbcl/bin/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}, "restart-b": {"core": "/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host.core", "core_sha256": "eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2", "runtime": "/home/ember/fn-tools/sbcl/bin/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}}, "journal": true, "kind": "requeue-restart", "source_killed": true, "source_restarted": true, "target_identical": true}
--- 28 stop server node A (main) (rc=0)
stopped
--- 29 stop server node B (main) (rc=0)
stopped
--- 30 stop server node A (main) (rc=0)
stopped
--- 31 stop the tap in front of node A (rc=0)
stopped
--- 32 stop server node B (main) (rc=0)
stopped
--- 33 stop the tap in front of node B (rc=0)
stopped
--- 34 stray fn processes (rc=0)
CLEAN
--- 35 remove the deploy tree (rc=0)
--- 36 release deploy lock (rc=0)
```
