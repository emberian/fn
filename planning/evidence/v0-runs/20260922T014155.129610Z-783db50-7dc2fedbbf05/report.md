# v0 matrix: 783db50 on persvati

v0 is every feature of fn usable between two peered fn nodes. This is that
question asked feature by feature against one commit on one box, with five
verdicts and no pass/fail collapse: accepted, refused and uncertain are the
three outcomes and each is a real observation; not-exercised names what
blocked the row; not-built names the lane that owns the missing feature.
It establishes nothing about the books beyond which certificates ACL2 read.

## What ran

| fact | value |
| --- | --- |
| commit | `783db50` (783db508ac4f44398d39d5af6bcef62f7f8fcee5) |
| tree | `native915` |
| host | `persvati` |
| started | 2026-09-22T01:41:55Z |
| wall time | 48.5 s |
| gate tool | `tools/v0_matrix.py` |
| os | Ubuntu 25.10 kernel=Linux 6.17.0-40-generic arch=x86_64 cores=24 |
| python3 | Python 3.13.7 |
| acl2version | + ACL2 Version 8.7                                                     + |
| certificates | not acquired by this slice; it consumes the explicitly named saved image |
| node a | native-operator on port 11190 (main), store $HOME/fn-deploy/native915-783db50/a/store |
| node b | native-operator on port 11191 (main), store $HOME/fn-deploy/native915-783db50/b/store |
| server entry point | native-operator |
| three outcomes a | accepted=0 refused=1 uncertain=not-built |
| three outcomes b | accepted=0 refused=1 uncertain=not-built |
| transit | IHAVE -> '435 duplicate'; CAPABILITIES lists IHAVE: True |
| rows | 192 rows: 93 accepted, 26 refused, 2 uncertain, 56 not exercised, 15 not built, 12 disagreed, 2 faulted |
| alt | python3.12 Python 3.12.13 |
| execution backend | native-operator |
| execution image | launcher sha256=ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142; image sha256=2d8259c22388119793ad3dde525497f9095bdb2489ac01e597b439f3d0ff5c09; declared runtime=b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5; sidecar core sha256=eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2 (static only before a live-owner witness); source correspondence unestablished |
| execution source | 783db50 |
| server | node B (native-operator) on port 11191 (b-main) |
| host clients | expect=ABSENT, inews=ABSENT, nn=ABSENT, script=/usr/bin/script, slrn=ABSENT, tin=ABSENT, trn=ABSENT |

## The v0 matrix

**Execution subject.** Backend `native-operator`; deployed source `783db50`; runtime image `launcher sha256=ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142; image sha256=2d8259c22388119793ad3dde525497f9095bdb2489ac01e597b439f3d0ff5c09; declared runtime=b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5; sidecar core sha256=eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2 (static only before a live-owner witness); source correspondence unestablished; live owners observed via /proc runtime sha256=b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5 and core sha256=eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2`. These are separate labels: naming the source and hashing an externally supplied image does not prove they correspond.

192 rows: 93 accepted, 26 refused, 2 uncertain, 56 not exercised, 15 not built; 12 row(s) did not do what they were designed to do, and 2 exited with a host fault or usage error, which is not an outcome and is counted among the not exercised. Every count here is `tools/v0_matrix.py`'s over the rows below, and `planning/evidence/v0-runs/20260922T014155.129610Z-783db50-7dc2fedbbf05/matrix.json` carries the same rows with their digest.


**Who saw it.** 0 of the 121 outcome rows were observed by something that is not fn's own code; 121 were observed by fn talking to fn. A feature that only fn's own client has ever seen is a weaker claim than "usable between two peered servers" reads, and every row carries the client that saw it in its `client` field. Clients in this run: fn CLI (exit code) (21); the matrix's raw-socket driver (102).

| feature | accepted | refused | uncertain | not exercised | not built | disagreed |
| --- | --- | --- | --- | --- | --- | --- |
| node init, configuration, start and stop (F-NODE) | 6 | 0 | 0 | 1 | 8 | 0 |
| the three outcomes on the operator surface (F-OUT) | 4 | 2 | 0 | 0 | 2 | 0 |
| groups, capacity, peers and live reconfiguration (F-GROUP) | 9 | 4 | 0 | 4 | 3 | 0 |
| principals, AUTHINFO and posting permission (F-AUTH) | 0 | 0 | 0 | 17 | 0 | 0 |
| POST and its read-back (F-POST) | 11 | 2 | 0 | 0 | 0 | 0 |
| the reader profile on each node (F-READ) | 48 | 6 | 0 | 0 | 0 | 0 |
| capability truthfulness (F-PIN) | 4 | 0 | 0 | 0 | 0 | 0 |
| transit inbound, A to B and B to A (F-TRANSIT) | 8 | 12 | 2 | 2 | 2 | 12 |
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
| `V0-NODE-STOP-A` | the service stops and releases the store | **accepted** | accepted | yes | fn only | stop rc=0; native status afterwards rc=0 transactions=8 articles=8 staging-orphans=0 unsigned-legacy-experiment |
| `V0-NODE-STOP-B` | the service stops and releases the store | **accepted** | accepted | yes | fn only | stop rc=0; native status afterwards rc=0 transactions=8 articles=8 staging-orphans=0 unsigned-legacy-experiment |
| `V0-NODE-LOOPBACK` | a non-loopback listener host is refused rather than silently bound | **not-exercised** | refused | - | - | (not run) |
| `V0-OUT-ACCEPTED-A` | an accepted post exits 0 | **accepted** | accepted | yes | fn only | rc=0 accepted operator post ACCEPTED |
| `V0-OUT-ACCEPTED-B` | an accepted post exits 0 | **accepted** | accepted | yes | fn only | rc=0 accepted operator post ACCEPTED |
| `V0-OUT-REFUSED-A` | a lookup of an article the node does not hold exits 1 | **refused** | refused | yes | fn only | rc=1 refused operator post REFUSED |
| `V0-OUT-REFUSED-B` | a lookup of an article the node does not hold exits 1 | **refused** | refused | yes | fn only | rc=1 refused operator post REFUSED |
| `V0-OUT-UNCERTAIN-A` | a post interrupted after publication exits 3 and fences the store | **not-built** | uncertain | - | - | (not run) |
| `V0-OUT-UNCERTAIN-B` | a post interrupted after publication exits 3 and fences the store | **not-built** | uncertain | - | - | (not run) |
| `V0-OUT-RECOVER-A` | recover after the uncertain publication exits 0 | **accepted** | accepted | yes | fn only | rc=0 recovered transactions=8 articles=8 staging-orphans=0 anchor=none checkpoint=none |
| `V0-OUT-RECOVER-B` | recover after the uncertain publication exits 0 | **accepted** | accepted | yes | fn only | rc=0 recovered transactions=8 articles=8 staging-orphans=0 anchor=none checkpoint=none |
| `V0-GROUP-CREATE-A` | fn group create adds a served group | **accepted** | accepted | yes | fn only | rc=0 configured generation=2 record=00000002.cfg verification=VERIFIED |
| `V0-GROUP-CREATE-B` | fn group create adds a served group | **accepted** | accepted | yes | fn only | rc=0 configured generation=2 record=00000002.cfg verification=VERIFIED |
| `V0-GROUP-SERVED-A` | the new group is served over the socket | **accepted** | accepted | yes | fn only | 211 0 1 0 fn.matrix |
| `V0-GROUP-SERVED-B` | the new group is served over the socket | **accepted** | accepted | yes | fn only | 211 0 1 0 fn.matrix |
| `V0-GROUP-RETIRE-A` | fn group retire removes it again | **accepted** | accepted | yes | fn only | rc=0 configured generation=4 record=00000004.cfg verification=VERIFIED |
| `V0-GROUP-RETIRE-B` | fn group retire removes it again | **accepted** | accepted | yes | fn only | rc=0 configured generation=4 record=00000004.cfg verification=VERIFIED |
| `V0-GROUP-UNKNOWN-A` | retiring a group the node does not serve is refused | **refused** | refused | yes | fn only | rc=1 refused operator group administrative configuration refused: NO-SUCH-GROUP |
| `V0-GROUP-UNKNOWN-B` | retiring a group the node does not serve is refused | **refused** | refused | yes | fn only | rc=1 refused operator group administrative configuration refused: NO-SUCH-GROUP |
| `V0-CAP-SET-A` | fn capacity sets the retention capacity | **not-exercised** | accepted | - | - | rc=5 fn-host: error: operator configuration file is missing |
| `V0-CAP-SET-B` | fn capacity sets the retention capacity | **not-exercised** | accepted | - | - | rc=5 fn-host: error: operator configuration file is missing |
| `V0-CAP-REFUSE-A` | an article that does not fit the capacity is refused before it is written | **not-exercised** | refused | - | - | (not run) |
| `V0-CAP-REFUSE-B` | an article that does not fit the capacity is refused before it is written | **not-exercised** | refused | - | - | (not run) |
| `V0-PEER-ADD-A` | fn peer add writes a transit peer record | **accepted** | accepted | yes | fn only | rc=0 configured generation=5 record=00000005.cfg verification=VERIFIED |
| `V0-PEER-ADD-B` | fn peer add writes a transit peer record | **accepted** | accepted | yes | fn only | rc=0 configured generation=5 record=00000005.cfg verification=VERIFIED |
| `V0-PEER-LIST-A` | fn peer list reads the record back | **not-built** | accepted | - | - | (not run) |
| `V0-PEER-LIST-B` | fn peer list reads the record back | **not-built** | accepted | - | - | (not run) |
| `V0-PEER-ABSENT` | fn peer remove of a peer that is not there is refused | **refused** | refused | yes | fn only | rc=1 refused operator peer administrative configuration refused: NO-SUCH-PEER |
| `V0-PEER-REMOVE` | fn peer remove of a configured peer is accepted | **accepted** | accepted | yes | fn only | rc=0 configured generation=6 record=00000006.cfg verification=VERIFIED |
| `V0-CFG-LIVE` | a group declared on the running service's control channel reaches the served configuration | **not-built** | accepted | - | - | (not run) |
| `V0-CFG-LIVE-REFUSE` | an offline configuration command is refused while the service holds the store | **refused** | refused | yes | fn only | rc=1 refused operator group store is already locked |
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
| `V0-POST-READBACK-B` | the posting connection's next GROUP already counts the article | **accepted** | accepted | yes | fn only | GROUP before=211 3 1 3 fn.letters after=211 4 1 4 fn.letters |
| `V0-POST-FRESH-A` | a fresh connection reads it back by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <native-matrix-b210aefdde17-a@example.invalid> article follows |
| `V0-POST-FRESH-B` | a fresh connection reads it back by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <native-matrix-b3ec5e97e130-b@example.invalid> article follows |
| `V0-POST-DUPLICATE-A` | a second POST of the same Message-ID is refused and allocates nothing | **refused** | refused | yes | fn only | 441 posting failed; the article was refused |
| `V0-POST-DUPLICATE-B` | a second POST of the same Message-ID is refused and allocates nothing | **refused** | refused | yes | fn only | 441 posting failed; the article was refused |
| `V0-POST-CLOCK-A` | a duplicate POST is refused as an article and does not cost the node its clock | **accepted** | accepted | yes | fn only | the duplicate answered '441 posting failed; the article was refused' and DATE afterwards answered '111 20260922014210' |
| `V0-POST-CLOCK-B` | a duplicate POST is refused as an article and does not cost the node its clock | **accepted** | accepted | yes | fn only | the duplicate answered '441 posting failed; the article was refused' and DATE afterwards answered '111 20260922014212' |
| `V0-POST-CONCURRENT` | a second reader stays live across another connection's whole POST | **accepted** | accepted | yes | fn only | watcher mid-post=211 7 1 7 fn.letters commit=240 article received OK |
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
| `V0-READ-GROUP-B` | GROUP | **accepted** | accepted | yes | fn only | 211 4 1 4 fn.letters |
| `V0-READ-LISTGROUP-A` | LISTGROUP with a range | **accepted** | accepted | yes | fn only | 211 1 1 1 fn.letters list follows |
| `V0-READ-LISTGROUP-B` | LISTGROUP with a range | **accepted** | accepted | yes | fn only | 211 4 1 4 fn.letters list follows |
| `V0-READ-ARTICLE-A` | ARTICLE by number | **accepted** | accepted | yes | fn only | 220 1 <native-matrix-b210aefdde17-a@example.invalid> article follows |
| `V0-READ-ARTICLE-B` | ARTICLE by number | **accepted** | accepted | yes | fn only | 220 1 <native-matrix-b210aefdde17-a@example.invalid> article follows |
| `V0-READ-HEAD-A` | HEAD by number | **accepted** | accepted | yes | fn only | 221 1 <native-matrix-b210aefdde17-a@example.invalid> headers follow |
| `V0-READ-HEAD-B` | HEAD by number | **accepted** | accepted | yes | fn only | 221 1 <native-matrix-b210aefdde17-a@example.invalid> headers follow |
| `V0-READ-BODY-A` | BODY by number | **accepted** | accepted | yes | fn only | 222 1 <native-matrix-b210aefdde17-a@example.invalid> body follows |
| `V0-READ-BODY-B` | BODY by number | **accepted** | accepted | yes | fn only | 222 1 <native-matrix-b210aefdde17-a@example.invalid> body follows |
| `V0-READ-STAT-A` | STAT by number | **accepted** | accepted | yes | fn only | 223 1 <native-matrix-b210aefdde17-a@example.invalid> retrieved |
| `V0-READ-STAT-B` | STAT by number | **accepted** | accepted | yes | fn only | 223 1 <native-matrix-b210aefdde17-a@example.invalid> retrieved |
| `V0-READ-ARTICLE-MSGID-A` | ARTICLE by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <native-matrix-b210aefdde17-a@example.invalid> article follows |
| `V0-READ-ARTICLE-MSGID-B` | ARTICLE by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <native-matrix-b3ec5e97e130-b@example.invalid> article follows |
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
| `V0-READ-NEXT-B` | NEXT moves the cursor | **accepted** | - | - | fn only | 223 2 <alpha@a.example.invalid> retrieved |
| `V0-READ-LAST-A` | LAST moves the cursor back | **refused** | - | - | fn only | 422 no previous article |
| `V0-READ-LAST-B` | LAST moves the cursor back | **accepted** | - | - | fn only | 223 1 <native-matrix-b210aefdde17-a@example.invalid> retrieved |
| `V0-READ-DATE-A` | DATE | **accepted** | accepted | yes | fn only | 111 20260922014210 |
| `V0-READ-DATE-B` | DATE | **accepted** | accepted | yes | fn only | 111 20260922014212 |
| `V0-READ-HELP-A` | HELP | **accepted** | accepted | yes | fn only | 100 help text follows |
| `V0-READ-HELP-B` | HELP | **accepted** | accepted | yes | fn only | 100 help text follows |
| `V0-READ-UNKNOWN-A` | an unknown command is refused with 500 | **refused** | refused | yes | fn only | 500 command not recognized |
| `V0-READ-UNKNOWN-B` | an unknown command is refused with 500 | **refused** | refused | yes | fn only | 500 command not recognized |
| `V0-READ-FRAMING-A` | a command split across two TCP segments is answered once, the same way | **accepted** | accepted | yes | fn only | DATE split across two segments answered '111 20260922014210' against '111 20260922014210' |
| `V0-READ-FRAMING-B` | a command split across two TCP segments is answered once, the same way | **accepted** | accepted | yes | fn only | DATE split across two segments answered '111 20260922014212' against '111 20260922014212' |
| `V0-PIN-DISPATCHED-A` | every capability the node advertises is dispatched by the node | **accepted** | accepted | yes | fn only | advertised=VERSION,READER,POST,OVER,HDR,LIST,IMPLEMENTATION,IHAVE,STREAMING not dispatched=(none) |
| `V0-PIN-DISPATCHED-B` | every capability the node advertises is dispatched by the node | **accepted** | accepted | yes | fn only | advertised=VERSION,READER,POST,OVER,HDR,LIST,IMPLEMENTATION,IHAVE,STREAMING not dispatched=(none) |
| `V0-PIN-ADVERTISED-A` | every command the node dispatches is advertised in CAPABILITIES | **accepted** | accepted | yes | fn only | dispatched=READER,POST,IHAVE,STREAMING,OVER,HDR,LIST,AUTHINFO,STARTTLS,MODE-READER,XOVER,XHDR,XPAT,LISTGROUP,CHECK,TAKETHIS not advertised=(none) |
| `V0-PIN-ADVERTISED-B` | every command the node dispatches is advertised in CAPABILITIES | **accepted** | accepted | yes | fn only | dispatched=READER,POST,IHAVE,STREAMING,OVER,HDR,LIST,AUTHINFO,STARTTLS,MODE-READER,XOVER,XHDR,XPAT,LISTGROUP,CHECK,TAKETHIS not advertised=(none) |
| `V0-TRANSIT-IDENTITY-A` | the node has an RFC 5537 <path-identity> of its own | **not-built** | accepted | - | - | (not run) |
| `V0-TRANSIT-IDENTITY-B` | the node has an RFC 5537 <path-identity> of its own | **not-built** | accepted | - | - | (not run) |
| `V0-TRANSIT-INDEPENDENT-A` | each node serves its own seeded articles and 43x for the other's seeds | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-INDEPENDENT-B` | each node serves its own seeded articles and 43x for the other's seeds | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-MODE-STREAM-AB` | MODE STREAM is accepted on the peer connection | **accepted** | accepted | yes | fn only | 203 streaming permitted |
| `V0-TRANSIT-MODE-STREAM-BA` | MODE STREAM is accepted on the peer connection | **accepted** | accepted | yes | fn only | 203 streaming permitted |
| `V0-TRANSIT-OFFER-AB` | IHAVE of a wanted article answers 335 | **refused** | accepted | NO | fn only | 435 duplicate |
| `V0-TRANSIT-OFFER-BA` | IHAVE of a wanted article answers 335 | **refused** | accepted | NO | fn only | 435 duplicate |
| `V0-TRANSIT-TRANSFER-AB` | the transferred article is taken with 235 | **uncertain** | accepted | NO | fn only | (nothing sent: the offer drew 435 duplicate) |
| `V0-TRANSIT-TRANSFER-BA` | the transferred article is taken with 235 | **uncertain** | accepted | NO | fn only | (nothing sent: the offer drew 435 duplicate) |
| `V0-TRANSIT-IDENTICAL-AB` | the far side serves the same octets the source served | **accepted** | accepted | yes | fn only | reread=220 0 <alpha@a.example.invalid> article follows identical=True |
| `V0-TRANSIT-IDENTICAL-BA` | the far side serves the same octets the source served | **accepted** | accepted | yes | fn only | reread=220 0 <beta@b.example.invalid> article follows identical=True |
| `V0-TRANSIT-DUPLICATE-AB` | a second IHAVE of the same Message-ID is refused with 435 | **refused** | refused | yes | fn only | 435 duplicate |
| `V0-TRANSIT-DUPLICATE-BA` | a second IHAVE of the same Message-ID is refused with 435 | **refused** | refused | yes | fn only | 435 duplicate |
| `V0-TRANSIT-LOOP-AB` | an article whose Path already names the target is refused after its 335 | **accepted** | refused | NO | fn only | 235 article transferred OK |
| `V0-TRANSIT-LOOP-BA` | an article whose Path already names the target is refused after its 335 | **accepted** | refused | NO | fn only | 235 article transferred OK |
| `V0-TRANSIT-LOOP-ABSENT-AB` | the refused loop article is not served by the target afterwards | **accepted** | refused | NO | fn only | 220 0 <loop-ab@example.invalid> article follows |
| `V0-TRANSIT-LOOP-ABSENT-BA` | the refused loop article is not served by the target afterwards | **accepted** | refused | NO | fn only | 220 0 <loop-ba@example.invalid> article follows |
| `V0-TRANSIT-CHECK-FRESH-AB` | CHECK of a Message-ID the target has not seen answers 238 | **refused** | accepted | NO | fn only | 438 <stream-a@example.invalid> |
| `V0-TRANSIT-CHECK-FRESH-BA` | CHECK of a Message-ID the target has not seen answers 238 | **refused** | accepted | NO | fn only | 438 <stream-b@example.invalid> |
| `V0-TRANSIT-TAKETHIS-AB` | TAKETHIS of that wanted article answers 239 | **refused** | accepted | NO | fn only | 439 <stream-a@example.invalid> |
| `V0-TRANSIT-TAKETHIS-BA` | TAKETHIS of that wanted article answers 239 | **refused** | accepted | NO | fn only | 439 <stream-b@example.invalid> |
| `V0-TRANSIT-CHECK-DUP-AB` | CHECK of an article the target holds answers 438 | **refused** | refused | yes | fn only | 438 <alpha@a.example.invalid> |
| `V0-TRANSIT-CHECK-DUP-BA` | CHECK of an article the target holds answers 438 | **refused** | refused | yes | fn only | 438 <beta@b.example.invalid> |
| `V0-TRANSIT-TAKETHIS-DUP-AB` | TAKETHIS that ignores that advice answers 439, never a 2xx and never a retry | **refused** | refused | yes | fn only | 439 <alpha@a.example.invalid> |
| `V0-TRANSIT-TAKETHIS-DUP-BA` | TAKETHIS that ignores that advice answers 439, never a 2xx and never a retry | **refused** | refused | yes | fn only | 439 <beta@b.example.invalid> |
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
- `V0-NODE-LOOPBACK` (not-exercised): this slice consumes existing configs and does not synthesize a second config solely to test the loopback refusal
- `V0-OUT-UNCERTAIN-A` (not-built): the production image has no fault-injection option; an uncertain publication is the developer image's cut campaign, not a public operator outcome -- owned by `native developer cut campaign`
- `V0-OUT-UNCERTAIN-B` (not-built): the production image has no fault-injection option; an uncertain publication is the developer image's cut campaign, not a public operator outcome -- owned by `native developer cut campaign`
- `V0-CAP-SET-A` (not-exercised): the command exited 5, a usage error, which is not one of the three outcomes (docs/operator.md: 0 accepted, 1 refused, 3 uncertain)
- `V0-CAP-SET-B` (not-exercised): the command exited 5, a usage error, which is not one of the three outcomes (docs/operator.md: 0 accepted, 1 refused, 3 uncertain)
- `V0-CAP-REFUSE-A` (not-exercised): native `post` is a submission to a live owner over its control socket, and this slice starts no owner over the scratch store
- `V0-CAP-REFUSE-B` (not-exercised): native `post` is a submission to a live owner over its control socket, and this slice starts no owner over the scratch store
- `V0-PEER-LIST-A` (not-built): the packaged native operator has no `peer list` verb; the record's effect is observed by whether the peer's transit is dispatched -- owned by `native peer listing`
- `V0-PEER-LIST-B` (not-built): the packaged native operator has no `peer list` verb; the record's effect is observed by whether the peer's transit is dispatched -- owned by `native peer listing`
- `V0-CFG-LIVE` (not-built): the native owner's control socket carries ACL2-framed submissions (host/native/control.lisp), not the line protocol the matrix's `control` phase speaks, and this image has no public verb that declares a group on a live owner -- owned by `native live administration`
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
- `V0-TRANSIT-IDENTITY-A` (not-built): the packaged native operator has no policy verb and the native configuration (books/native-config.lisp) carries no <path-identity> of the node's own; RFC 5537 3.5 loop suppression cannot fire on an unnamed node, and the loop rows measure exactly that -- owned by `native path-identity administration`
- `V0-TRANSIT-IDENTITY-B` (not-built): the packaged native operator has no policy verb and the native configuration (books/native-config.lisp) carries no <path-identity> of the node's own; RFC 5537 3.5 loop suppression cannot fire on an unnamed node, and the loop rows measure exactly that -- owned by `native path-identity administration`
- `V0-TRANSIT-INDEPENDENT-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-TRANSIT-INDEPENDENT-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
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
- `V0-NODE-STOP-A`: the stop is the harness's SIGTERM, not an operator verb; the store reopening for the offline operator is the writer lock being gone; no in-flight session was observed across the stop
- `V0-NODE-STOP-B`: the stop is the harness's SIGTERM, not an operator verb; the store reopening for the offline operator is the writer lock being gone; no in-flight session was observed across the stop
- `V0-OUT-ACCEPTED-A`: one article submitted to the live owner over its control socket; the exit code is the observation
- `V0-OUT-ACCEPTED-B`: one article submitted to the live owner over its control socket; the exit code is the observation
- `V0-OUT-REFUSED-A`: NOT a lookup: the native operator has no article lookup verb, so the refused outcome observed here is the same submission a second time, refused by the Message-ID binding
- `V0-OUT-REFUSED-B`: NOT a lookup: the native operator has no article lookup verb, so the refused outcome observed here is the same submission a second time, refused by the Message-ID binding
- `V0-OUT-RECOVER-A`: recovery of a store the owner released on SIGTERM; no uncertain publication preceded it on this image
- `V0-OUT-RECOVER-B`: recovery of a store the owner released on SIGTERM; no uncertain publication preceded it on this image
- `V0-GROUP-CREATE-A`: one group on a store no service holds
- `V0-GROUP-CREATE-B`: one group on a store no service holds
- `V0-GROUP-SERVED-A`: the group was created before the service started
- `V0-GROUP-SERVED-B`: the group was created before the service started
- `V0-CAP-SET-A`: a scratch store beside the served one, initialised through the image's store entry, so a refusal here cannot change what the node serves
- `V0-CAP-SET-B`: a scratch store beside the served one, initialised through the image's store entry, so a refusal here cannot change what the node serves
- `V0-PEER-ADD-A`: a peer record is configuration, not authorization; the positional grammar is books/native-operator.lisp's and the inbound ceiling is the record's own default
- `V0-PEER-ADD-B`: a peer record is configuration, not authorization; the positional grammar is books/native-operator.lisp's and the inbound ceiling is the record's own default
- `V0-PEER-REMOVE`: run after the owners stopped, so it says nothing about removing a peer from a live service
- `V0-CFG-LIVE-REFUSE`: the refusal is the writer lock's; a different server that does not take the writer lock would not produce it
- `V0-POST-COMMIT-A`: one article; the durability behind the 240 is the store's, asserted by the recovery rows below
- `V0-POST-COMMIT-B`: one article; the durability behind the 240 is the store's, asserted by the recovery rows below
- `V0-POST-DUPLICATE-A`: the duplicate is offered on a fresh connection because one clock observation is pinned per connection at accept
- `V0-POST-DUPLICATE-B`: the duplicate is offered on a fresh connection because one clock observation is pinned per connection at accept
- `V0-POST-CLOCK-A`: a 441 for an article the node already holds and a 441 for a clock the node no longer has are the same code; DATE is what separates them from outside, because a refused reading costs the owner its clock (D10-a) and DATE then answers 503. This row does not INDUCE a clock fault -- it checks that an ordinary duplicate did not cause one
- `V0-POST-CLOCK-B`: a 441 for an article the node already holds and a 441 for a clock the node no longer has are the same code; DATE is what separates them from outside, because a refused reading costs the owner its clock (D10-a) and DATE then answers 503. This row does not INDUCE a clock fault -- it checks that an ordinary duplicate did not cause one
- `V0-POST-CONCURRENT`: two connections on one box; this is not concurrent load
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
- `V0-READ-NEXT-B`: the expected outcome depends on how many articles the group holds; the row records the count it was run against; served by `native-operator` on port 11191; the group held 4 article(s) when this ran, and with one article 421/422 is the correct answer
- `V0-READ-LAST-A`: the expected outcome depends on where the cursor was; served by `native-operator` on port 11190; the group held 1 article(s) when this ran, and with one article 421/422 is the correct answer
- `V0-READ-LAST-B`: the expected outcome depends on where the cursor was; served by `native-operator` on port 11191; the group held 4 article(s) when this ran, and with one article 421/422 is the correct answer
- `V0-READ-DATE-A`: served by `native-operator` on port 11190
- `V0-READ-DATE-B`: served by `native-operator` on port 11191
- `V0-READ-HELP-A`: served by `native-operator` on port 11190
- `V0-READ-HELP-B`: served by `native-operator` on port 11191
- `V0-READ-UNKNOWN-A`: served by `native-operator` on port 11190
- `V0-READ-UNKNOWN-B`: served by `native-operator` on port 11191
- `V0-READ-FRAMING-A`: one command split at one point; the chunk-independence keystone is books/wire-invariants', not this row
- `V0-READ-FRAMING-B`: one command split at one point; the chunk-independence keystone is books/wire-invariants', not this row
- `V0-PIN-DISPATCHED-A`: only the 9 labels with a probe command are checked; VERSION and IMPLEMENTATION have none
- `V0-PIN-DISPATCHED-B`: only the 9 labels with a probe command are checked; VERSION and IMPLEMENTATION have none
- `V0-PIN-ADVERTISED-A`: only the 9 labels with a probe command are checked; VERSION and IMPLEMENTATION have none; RFC 3977 section 5.2.2 requires the capability exactly when the command is available
- `V0-PIN-ADVERTISED-B`: only the 9 labels with a probe command are checked; VERSION and IMPLEMENTATION have none; RFC 3977 section 5.2.2 requires the capability exactly when the command is available
- `V0-TRANSIT-IDENTITY-A`: `fn-peer-local-identity` reads the `path-identity` policy slot and an unset slot is the empty string, which `fn-path-names-p` never matches: a node without this answers no loop, so V0-TRANSIT-LOOP rests on it
- `V0-TRANSIT-IDENTITY-B`: `fn-peer-local-identity` reads the `path-identity` policy slot and an unset slot is the empty string, which `fn-path-names-p` never matches: a node without this answers no loop, so V0-TRANSIT-LOOP rests on it
- `V0-TRANSIT-MODE-STREAM-AB`: node B is `native-operator`; the peer record on it names a
- `V0-TRANSIT-MODE-STREAM-BA`: node A is `native-operator`; the peer record on it names b
- `V0-TRANSIT-OFFER-AB`: node B is `native-operator`; the peer record on it names a
- `V0-TRANSIT-OFFER-BA`: node A is `native-operator`; the peer record on it names b
- `V0-TRANSIT-TRANSFER-AB`: node B is `native-operator`; the peer record on it names a
- `V0-TRANSIT-TRANSFER-BA`: node A is `native-operator`; the peer record on it names b
- `V0-TRANSIT-IDENTICAL-AB`: the octets are compared line for line against what the source served; local article numbers are not compared and may differ
- `V0-TRANSIT-IDENTICAL-BA`: the octets are compared line for line against what the source served; local article numbers are not compared and may differ
- `V0-TRANSIT-DUPLICATE-AB`: RFC 3977 6.3.2: 435 is the Message-ID history refusing an article the node already holds
- `V0-TRANSIT-DUPLICATE-BA`: RFC 3977 6.3.2: 435 is the Message-ID history refusing an article the node already holds
- `V0-TRANSIT-LOOP-AB`: RFC 5537 3.5; the Path is inside the article, so a correct server says 335 first and then refuses
- `V0-TRANSIT-LOOP-BA`: RFC 5537 3.5; the Path is inside the article, so a correct server says 335 first and then refuses
- `V0-TRANSIT-CHECK-FRESH-AB`: RFC 4644 2.4: 238 is the only 'send it' answer; 431 and 438 are the two refusals the row accepts as decisions
- `V0-TRANSIT-CHECK-FRESH-BA`: RFC 4644 2.4: 238 is the only 'send it' answer; 431 and 438 are the two refusals the row accepts as decisions
- `V0-TRANSIT-TAKETHIS-AB`: one article over one session
- `V0-TRANSIT-TAKETHIS-BA`: one article over one session
- `V0-TRANSIT-CHECK-DUP-AB`: RFC 4644 2.4
- `V0-TRANSIT-CHECK-DUP-BA`: RFC 4644 2.4
- `V0-TRANSIT-TAKETHIS-DUP-AB`: RFC 4644 2.5: a client that ignores the advisory CHECK must be refused after the bytes, never with a 2xx and never with a retry code
- `V0-TRANSIT-TAKETHIS-DUP-BA`: RFC 4644 2.5: a client that ignores the advisory CHECK must be refused after the bytes, never with a 2xx and never with a retry code
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
- `V0-NODE-STATUS-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml status`
- `V0-NODE-STATUS-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml status`
- `V0-NODE-START-A`: `env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml run`
- `V0-NODE-START-B`: `env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml run`
- `V0-NODE-STOP-A`: `kill -TERM <owner pid> (harness) ; cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml status`
- `V0-NODE-STOP-B`: `kill -TERM <owner pid> (harness) ; cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml status`
- `V0-NODE-LOOPBACK`: `packaging/fn-native operator CONFIG run`
- `V0-OUT-ACCEPTED-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml post --message-id '<alpha@a.example.invalid>' --payload $HOME/fn-deploy/native915-783db50/a/alpha.article --group fn.letters`
- `V0-OUT-ACCEPTED-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml post --message-id '<beta@b.example.invalid>' --payload $HOME/fn-deploy/native915-783db50/b/beta.article --group fn.letters`
- `V0-OUT-REFUSED-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml post --message-id '<alpha@a.example.invalid>' --payload $HOME/fn-deploy/native915-783db50/a/alpha.article --group fn.letters`
- `V0-OUT-REFUSED-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml post --message-id '<beta@b.example.invalid>' --payload $HOME/fn-deploy/native915-783db50/b/beta.article --group fn.letters`
- `V0-OUT-UNCERTAIN-A`: `env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml post --inject-fault postpublish`
- `V0-OUT-UNCERTAIN-B`: `env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml post --inject-fault postpublish`
- `V0-OUT-RECOVER-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml recover`
- `V0-OUT-RECOVER-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml recover`
- `V0-GROUP-CREATE-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml group create fn.matrix`
- `V0-GROUP-CREATE-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml group create fn.matrix`
- `V0-GROUP-SERVED-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py presence --port 11190 --groups fn.matrix`
- `V0-GROUP-SERVED-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py presence --port 11191 --groups fn.matrix`
- `V0-GROUP-RETIRE-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml group retire fn.matrix.throwaway`
- `V0-GROUP-RETIRE-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml group retire fn.matrix.throwaway`
- `V0-GROUP-UNKNOWN-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml group retire fn.not.served`
- `V0-GROUP-UNKNOWN-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml group retire fn.not.served`
- `V0-CAP-SET-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator '$HOME/fn-deploy/native915-783db50/a/capacity/fn.toml' capacity 64`
- `V0-CAP-SET-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator '$HOME/fn-deploy/native915-783db50/b/capacity/fn.toml' capacity 64`
- `V0-CAP-REFUSE-A`: `env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator '$HOME/fn-deploy/native915-783db50/a/capacity/fn.toml' post --message-id '<capacity@example.invalid>' --payload ... --group fn.letters`
- `V0-CAP-REFUSE-B`: `env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator '$HOME/fn-deploy/native915-783db50/b/capacity/fn.toml' post --message-id '<capacity@example.invalid>' --payload ... --group fn.letters`
- `V0-PEER-ADD-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml peer add b b.gate.example.invalid 127.0.0.1 11191 'fn.*' 'fn.*' 127.0.0.1 true`
- `V0-PEER-ADD-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml peer add a a.gate.example.invalid 127.0.0.1 11190 'fn.*' 'fn.*' 127.0.0.1 true`
- `V0-PEER-LIST-A`: `env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml peer list`
- `V0-PEER-LIST-B`: `env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml peer list`
- `V0-PEER-ABSENT`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml peer remove no-such-peer`
- `V0-PEER-REMOVE`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml peer remove b`
- `V0-CFG-LIVE`: `matrix.py control --socket ... --line 'DECLARE-GROUP ...'`
- `V0-CFG-LIVE-REFUSE`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml group create fn.matrix.offline`
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
- `V0-POST-OPEN-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --user '' --secret ''`
- `V0-POST-OPEN-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --user '' --secret ''`
- `V0-POST-COMMIT-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --user '' --secret ''`
- `V0-POST-COMMIT-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --user '' --secret ''`
- `V0-POST-READBACK-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --user '' --secret ''`
- `V0-POST-READBACK-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --user '' --secret ''`
- `V0-POST-FRESH-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --user '' --secret ''`
- `V0-POST-FRESH-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --user '' --secret ''`
- `V0-POST-DUPLICATE-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --user '' --secret ''`
- `V0-POST-DUPLICATE-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --user '' --secret ''`
- `V0-POST-CLOCK-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --user '' --secret ''`
- `V0-POST-CLOCK-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --user '' --secret ''`
- `V0-POST-CONCURRENT`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py concurrent --port 11190 --group fn.letters --msgid '<concurrent@example.invalid>' --user '' --secret ''`
- `V0-READ-CAPABILITIES-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-CAPABILITIES-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-MODE-READER-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-MODE-READER-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-OVERVIEW-FMT-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-OVERVIEW-FMT-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-TIMES-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-TIMES-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-HEADERS-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-HEADERS-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-GROUP-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-GROUP-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LISTGROUP-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LISTGROUP-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HEAD-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HEAD-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-BODY-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-BODY-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-STAT-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-STAT-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-MSGID-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-MSGID-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-ABSENT-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-ABSENT-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-RANGE-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-RANGE-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HDR-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HDR-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XOVER-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XOVER-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XHDR-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XHDR-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XPAT-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XPAT-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEXT-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEXT-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LAST-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LAST-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-DATE-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-DATE-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HELP-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HELP-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-UNKNOWN-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-UNKNOWN-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-FRAMING-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-FRAMING-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-PIN-DISPATCHED-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py pins --port 11190 --group fn.letters --user '' --secret ''`
- `V0-PIN-DISPATCHED-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py pins --port 11191 --group fn.letters --user '' --secret ''`
- `V0-PIN-ADVERTISED-A`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py pins --port 11190 --group fn.letters --user '' --secret ''`
- `V0-PIN-ADVERTISED-B`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py pins --port 11191 --group fn.letters --user '' --secret ''`
- `V0-TRANSIT-IDENTITY-A`: `env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml policy set path-identity a.gate.example.invalid`
- `V0-TRANSIT-IDENTITY-B`: `env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml policy set path-identity b.gate.example.invalid`
- `V0-TRANSIT-INDEPENDENT-A`: `(none)`
- `V0-TRANSIT-INDEPENDENT-B`: `(none)`
- `V0-TRANSIT-MODE-STREAM-AB`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-MODE-STREAM-BA`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-OFFER-AB`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-OFFER-BA`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-TRANSFER-AB`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-TRANSFER-BA`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-IDENTICAL-AB`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-IDENTICAL-BA`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-DUPLICATE-AB`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-DUPLICATE-BA`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-LOOP-AB`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-LOOP-BA`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-LOOP-ABSENT-AB`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-LOOP-ABSENT-BA`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-CHECK-FRESH-AB`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py stream --from-port 11190 --to-port 11191 --msgid '<stream-a@example.invalid>'`
- `V0-TRANSIT-CHECK-FRESH-BA`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py stream --from-port 11191 --to-port 11190 --msgid '<stream-b@example.invalid>'`
- `V0-TRANSIT-TAKETHIS-AB`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py stream --from-port 11190 --to-port 11191 --msgid '<stream-a@example.invalid>'`
- `V0-TRANSIT-TAKETHIS-BA`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py stream --from-port 11191 --to-port 11190 --msgid '<stream-b@example.invalid>'`
- `V0-TRANSIT-CHECK-DUP-AB`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-CHECK-DUP-BA`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-TAKETHIS-DUP-AB`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-TAKETHIS-DUP-BA`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-FEED-QUEUE`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-FEED-OFFER`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-FEED-ONCE`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
- `V0-FEED-JOURNAL`: `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
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
| 1 | preflight | 0 | `os=Ubuntu 25.10 kernel=Linux 6.17.0-40-generic arch=x86_64 cores=24` | 0.9 |
| 2 | acquire deploy lock | 0 | `` | 0.3 |
| 3 | ship archive | 0 | `` | 2.7 |
| 4 | make run dir | 0 | `` | 0.3 |
| 5 | install drive.py | 0 | `` | 0.3 |
| 6 | install feed.py | 0 | `` | 0.4 |
| 7 | install matrix.py | 0 | `` | 0.3 |
| 8 | native packaged operator subject | 0 | `NATIVE-LAUNCHER-DIGEST ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142` | 1.6 |
| 9 | node A native run directory | 0 | `` | 0.4 |
| 10 | node A native config exists | 0 | `` | 0.3 |
| 11 | node A native operator status | 0 | `transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment` | 0.4 |
| 12 | node B native run directory | 0 | `` | 0.3 |
| 13 | node B native config exists | 0 | `` | 0.4 |
| 14 | node B native operator status | 0 | `transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment` | 0.4 |
| 15 | node A group create fn.matrix | 0 | `configured generation=2 record=00000002.cfg verification=VERIFIED` | 0.3 |
| 16 | node A group create fn.matrix.throwaway | 0 | `configured generation=3 record=00000003.cfg verification=VERIFIED` | 0.5 |
| 17 | node A group retire fn.matrix.throwaway | 0 | `configured generation=4 record=00000004.cfg verification=VERIFIED` | 0.4 |
| 18 | node A group retire an unserved group | 1 | `refused operator group administrative configuration refused: NO-SUCH-GROUP` | 0.4 |
| 19 | node A capacity scratch store | 0 | `initialized /home/ember/fn-deploy/native915-783db50/a/capacity/store` | 0.4 |
| 20 | node A capacity 64 | 5 | `fn-host: error: operator configuration file is missing` | 0.3 |
| 21 | node B group create fn.matrix | 0 | `configured generation=2 record=00000002.cfg verification=VERIFIED` | 0.4 |
| 22 | node B group create fn.matrix.throwaway | 0 | `configured generation=3 record=00000003.cfg verification=VERIFIED` | 0.5 |
| 23 | node B group retire fn.matrix.throwaway | 0 | `configured generation=4 record=00000004.cfg verification=VERIFIED` | 0.4 |
| 24 | node B group retire an unserved group | 1 | `refused operator group administrative configuration refused: NO-SUCH-GROUP` | 0.4 |
| 25 | node B capacity scratch store | 0 | `initialized /home/ember/fn-deploy/native915-783db50/b/capacity/store` | 0.5 |
| 26 | node B capacity 64 | 5 | `fn-host: error: operator configuration file is missing` | 0.3 |
| 27 | node B configured port | 0 | `11191` | 0.3 |
| 28 | node A peer record for B | 0 | `configured generation=5 record=00000005.cfg verification=VERIFIED` | 0.4 |
| 29 | node A configured port | 0 | `11190` | 0.2 |
| 30 | node B peer record for A | 0 | `configured generation=5 record=00000005.cfg verification=VERIFIED` | 0.4 |
| 31 | start server (node A (native-operator), a-main) | 0 | `LISTENING 11190` | 1.3 |
| 32 | node A pid | 0 | `2312462` | 0.3 |
| 33 | start server (node B (native-operator), b-main) | 0 | `LISTENING 11191` | 1.3 |
| 34 | node B pid | 0 | `2312686` | 1.9 |
| 35 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 36 | node A serves fn.matrix | 0 | `{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}` | 0.4 |
| 37 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 38 | node A POST cycle | 0 | `{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-b21` | 0.3 |
| 39 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 40 | node A reader surface | 0 | `{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES ` | 0.7 |
| 41 | node A server is alive | 0 | `ALIVE` | 0.2 |
| 42 | install alpha.article | 0 | `` | 1.1 |
| 43 | node A outcome accepted | 0 | `accepted operator post ACCEPTED` | 0.4 |
| 44 | install alpha.article | 0 | `` | 0.3 |
| 45 | node A outcome refused | 1 | `refused operator post REFUSED` | 0.4 |
| 46 | install stream-a.article | 0 | `` | 0.2 |
| 47 | node A seed <stream-a@example.invalid> | 0 | `accepted operator post ACCEPTED` | 0.4 |
| 48 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 49 | node B serves fn.matrix | 0 | `{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}` | 0.3 |
| 50 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 51 | node B POST cycle | 0 | `{"GROUP BEFORE": "211 3 1 3 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 4 1 4 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-b3e` | 0.3 |
| 52 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 53 | node B reader surface | 0 | `{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES ` | 0.7 |
| 54 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 55 | install beta.article | 0 | `` | 0.2 |
| 56 | node B outcome accepted | 0 | `accepted operator post ACCEPTED` | 0.4 |
| 57 | install beta.article | 0 | `` | 0.3 |
| 58 | node B outcome refused | 1 | `refused operator post REFUSED` | 0.3 |
| 59 | install stream-b.article | 0 | `` | 0.3 |
| 60 | node B seed <stream-b@example.invalid> | 0 | `accepted operator post ACCEPTED` | 0.4 |
| 61 | node A server is alive | 0 | `ALIVE` | 0.2 |
| 62 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 63 | node B server is alive | 0 | `ALIVE` | 0.2 |
| 64 | transit AB: offer <alpha@a.example.invalid> from A to B | 1 | `{"msgid": "<alpha@a.example.invalid>", "source": "220 0 <alpha@a.example.invalid> article follows", "source_lines": 7, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE` | 0.4 |
| 65 | transit AB: CHECK/TAKETHIS <stream-a@example.invalid> from A to B | 1 | `{"SOURCE": "220 0 <stream-a@example.invalid> article follows", "MODE STREAM": "203 streaming permitted", "CHECK": "438 <stream-a@example.invalid>", "TAKETHIS": "439 <stream-a@example.invalid>", "CHECK` | 0.4 |
| 66 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 67 | transit BA: offer <beta@b.example.invalid> from B to A | 1 | `{"msgid": "<beta@b.example.invalid>", "source": "220 0 <beta@b.example.invalid> article follows", "source_lines": 7, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE A` | 0.4 |
| 68 | transit BA: CHECK/TAKETHIS <stream-b@example.invalid> from B to A | 1 | `{"SOURCE": "220 0 <stream-b@example.invalid> article follows", "MODE STREAM": "203 streaming permitted", "CHECK": "438 <stream-b@example.invalid>", "TAKETHIS": "439 <stream-b@example.invalid>", "CHECK` | 0.4 |
| 69 | node A server is alive | 0 | `ALIVE` | 0.2 |
| 70 | node A capability pins | 0 | `{"advertised": ["VERSION", "READER", "POST", "OVER", "HDR", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING"], "answered": {"READER": "211 7 1 7 fn.letters", "POST": "340 send article to be posted", "PO` | 0.3 |
| 71 | node B server is alive | 0 | `ALIVE` | 0.2 |
| 72 | node B capability pins | 0 | `{"advertised": ["VERSION", "READER", "POST", "OVER", "HDR", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING"], "answered": {"READER": "211 7 1 7 fn.letters", "POST": "340 send article to be posted", "PO` | 0.3 |
| 73 | node A server is alive | 0 | `ALIVE` | 0.2 |
| 74 | node B server is alive | 0 | `ALIVE` | 0.2 |
| 75 | a second reader across node A's POST | 0 | `{"WATCHER BEFORE": "211 7 1 7 fn.letters", "POST": "340 send article to be posted", "WATCHER MID": "211 7 1 7 fn.letters", "WATCHER ARTICLE MID": "223 1 <native-matrix-b210aefdde17-a@example.invalid> ` | 0.4 |
| 76 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 77 | node B server is alive | 0 | `ALIVE` | 0.2 |
| 78 | offline group create while the owner holds the store | 1 | `refused operator group store is already locked` | 0.4 |
| 79 | native public peering/restart witness | 0 | `NATIVE-PEERING-EXPECTED-RUNTIME b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5` | 5.4 |
| 80 | stop server node A (main) | 0 | `stopped` | 1.9 |
| 81 | node A store after the stop | 0 | `transactions=8 articles=8 staging-orphans=0 unsigned-legacy-experiment` | 0.4 |
| 82 | node A recover after the stop | 0 | `recovered transactions=8 articles=8 staging-orphans=0 anchor=none checkpoint=none` | 0.3 |
| 83 | node A log tail | 0 | `CONTROL /home/ember/fn-native915-matrix/a/control.sock` | 0.4 |
| 84 | stop server node B (main) | 0 | `stopped` | 1.4 |
| 85 | node B store after the stop | 0 | `transactions=8 articles=8 staging-orphans=0 unsigned-legacy-experiment` | 0.3 |
| 86 | node B recover after the stop | 0 | `recovered transactions=8 articles=8 staging-orphans=0 anchor=none checkpoint=none` | 0.3 |
| 87 | node B log tail | 0 | `CONTROL /home/ember/fn-native915-matrix/b/control.sock` | 0.3 |
| 88 | peer remove a peer that is not there | 1 | `refused operator peer administrative configuration refused: NO-SUCH-PEER` | 0.4 |
| 89 | peer remove the configured peer | 0 | `configured generation=6 record=00000006.cfg verification=VERIFIED` | 0.3 |
| 90 | stop server node A (main) | 0 | `stopped` | 0.3 |
| 91 | stop the tap in front of node A | 0 | `stopped` | 0.3 |
| 92 | stop server node B (main) | 0 | `stopped` | 0.2 |
| 93 | stop the tap in front of node B | 0 | `stopped` | 0.3 |
| 94 | stray fn processes | 0 | `CLEAN` | 0.3 |
| 95 | remove the deploy tree | 0 | `` | 0.3 |
| 96 | release deploy lock | 0 | `` | 0.3 |

### Commands in full

1. **preflight** -- `. /etc/os-release 2>/dev/null || true ; echo "os=${PRETTY_NAME:-unknown} kernel=$(uname -sr) arch=$(uname -m) cores=$(nproc 2>/dev/null || echo ?)" ; echo "python3=$(python3 -V 2>&1)" ; for p in python3.9 python3.10 python3.11 python3.12; do ; command -v $p >/dev/null && echo "alt=$p $($p -V 2>&1)" ; done ; for c in slrn tin nn trn inews expect script; do ; printf 'client %s=%s\n' "$c" "$(comma...`
2. **acquire deploy lock** -- `mkdir -p $HOME/fn-deploy/.locks ; if ! mkdir $HOME/fn-deploy/.locks/native915-783db50.lock 2>/dev/null; then ; echo "deploy identity is already active: native915-783db50" ; exit 73 ; fi`
3. **ship archive** -- `git archive 783db50 | tar -x -C $HOME/fn-deploy/native915-783db50`
4. **make run dir** -- `mkdir -p $HOME/fn-deploy/native915-783db50/gate-run`
5. **install drive.py** -- `base64 -d > $HOME/fn-deploy/native915-783db50/gate-run/drive.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJJbmRlcGVuZGVudCBOTlRQIGRyaXZpbmcgZm9yIHRo ; ZSBkZXBsb3kgZ2F0ZTsgbm8gZm4gbW9kdWxlIGlzIGltcG9ydGVkLiIiIgppbXBvcnQgYXJncGFy ; c2UsIGpzb24sIG9zLCBzb2NrZXQsIHN5cywgdGltZQoKCmNsYXNzIENvbm46CiAgICBkZWYgX19p ; bml0X18oc2VsZiwgcG9ydCwgdGltZW91dD0zMCk6CiAgICAgICAgc2VsZi5zb2NrID0gc29ja2V0 ;...`
6. **install feed.py** -- `base64 -d > $HOME/fn-deploy/native915-783db50/gate-run/feed.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJUaGUgdHdvLW5vZGUgcGhhc2VzLiAgTm8gZm4gbW9k ; dWxlIGlzIGltcG9ydGVkOyBDb25uIGlzIGRlcGxveV9nYXRlJ3MuCgpgcHJlc2VuY2VgIGlzIHRo ; ZSBjb250cm9sIGFuZCB0aGUgcmVyZWFkOiB3aGF0IGEgbm9kZSBob2xkcyBhbmQgd2hhdCBpdCBt ; dXN0Cm5vdC4gIGByZWxheWAgaXMgUkZDIDM5NzcgNi4zLjIgZHJpdmVuIGJ5IGhhbmQgb3ZlciBh ; ...`
7. **install matrix.py** -- `base64 -d > $HOME/fn-deploy/native915-783db50/gate-run/matrix.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJUaGUgdjAgbWF0cml4J3Mgb3duIE5OVFAgcGhhc2Vz ; LiAgTm8gZm4gbW9kdWxlIGlzIGltcG9ydGVkOyBDb25uIGlzCnRvb2xzL2RlcGxveV9nYXRlLnB5 ; J3MgZHJpdmVyLCBzaGlwcGVkIGJlc2lkZSB0aGlzIGZpbGUgYXMgZHJpdmUucHkuCgpFdmVyeSBw ; aGFzZSBwcmludHMgT05FIGpzb24gb2JqZWN0IHdob3NlIGtleXMgYXJlIGNvbW1hbmQgbmFtZXMg ...`
8. **native packaged operator subject** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; wrapper=packaging/fn-native ; runtime=/home/ember/fn-tools/sbcl/bin/sbcl ; test -x "$image" || { echo "NATIVE-IMAGE-MISSING $image"; exit 4; } ; test -x "$wrapper" || { echo NATIVE-WRAPPER-MISSING; exit 4; } ; test -s "$image.core" || { echo...`
9. **node A native run directory** -- `mkdir -p $HOME/fn-deploy/native915-783db50/a`
10. **node A native config exists** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; test -f /home/ember/fn-native915-matrix/a/fn.toml`
11. **node A native operator status** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml status`
12. **node B native run directory** -- `mkdir -p $HOME/fn-deploy/native915-783db50/b`
13. **node B native config exists** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; test -f /home/ember/fn-native915-matrix/b/fn.toml`
14. **node B native operator status** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml status`
15. **node A group create fn.matrix** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml group create fn.matrix`
16. **node A group create fn.matrix.throwaway** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml group create fn.matrix.throwaway`
17. **node A group retire fn.matrix.throwaway** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml group retire fn.matrix.throwaway`
18. **node A group retire an unserved group** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml group retire fn.not.served`
19. **node A capacity scratch store** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; mkdir -p $HOME/fn-deploy/native915-783db50/a/capacity && env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native store $HOME/fn-deploy/native915-783db50/a/capacity/store init fn.letters && printf '[store]\npath = "%s"\n' "$HOME/fn-deploy/native915-783db50/a/capacity...`
20. **node A capacity 64** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator '$HOME/fn-deploy/native915-783db50/a/capacity/fn.toml' capacity 64`
21. **node B group create fn.matrix** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml group create fn.matrix`
22. **node B group create fn.matrix.throwaway** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml group create fn.matrix.throwaway`
23. **node B group retire fn.matrix.throwaway** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml group retire fn.matrix.throwaway`
24. **node B group retire an unserved group** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml group retire fn.not.served`
25. **node B capacity scratch store** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; mkdir -p $HOME/fn-deploy/native915-783db50/b/capacity && env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native store $HOME/fn-deploy/native915-783db50/b/capacity/store init fn.letters && printf '[store]\npath = "%s"\n' "$HOME/fn-deploy/native915-783db50/b/capacity...`
26. **node B capacity 64** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator '$HOME/fn-deploy/native915-783db50/b/capacity/fn.toml' capacity 64`
27. **node B configured port** -- `sed -n 's/^port *= *\([0-9][0-9]*\).*/\1/p' /home/ember/fn-native915-matrix/b/fn.toml | head -1`
28. **node A peer record for B** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml peer add b b.gate.example.invalid 127.0.0.1 11191 'fn.*' 'fn.*' 127.0.0.1 true`
29. **node A configured port** -- `sed -n 's/^port *= *\([0-9][0-9]*\).*/\1/p' /home/ember/fn-native915-matrix/a/fn.toml | head -1`
30. **node B peer record for A** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml peer add a a.gate.example.invalid 127.0.0.1 11190 'fn.*' 'fn.*' 127.0.0.1 true`
31. **start server (node A (native-operator), a-main)** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; rm -f $HOME/fn-deploy/native915-783db50/a/server-a-main.log ; nohup env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml run > $HOME/fn-deploy/native915-783db50/a/server-a-main.log 2>&1 < /dev/null & ; echo $! > ...`
32. **node A pid** -- `cat $HOME/fn-deploy/native915-783db50/a/server.pid`
33. **start server (node B (native-operator), b-main)** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; rm -f $HOME/fn-deploy/native915-783db50/b/server-b-main.log ; nohup env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml run > $HOME/fn-deploy/native915-783db50/b/server-b-main.log 2>&1 < /dev/null & ; echo $! > ...`
34. **node B pid** -- `cat $HOME/fn-deploy/native915-783db50/b/server.pid`
35. **node A server is alive** -- `kill -0 2312462 2>/dev/null && echo ALIVE || echo DEAD`
36. **node A serves fn.matrix** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py presence --port 11190 --groups fn.matrix`
37. **node A server is alive** -- `kill -0 2312462 2>/dev/null && echo ALIVE || echo DEAD`
38. **node A POST cycle** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --user '' --secret ''`
39. **node A server is alive** -- `kill -0 2312462 2>/dev/null && echo ALIVE || echo DEAD`
40. **node A reader surface** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-b210aefdde17-a@example.invalid>' --absent '<absent@example.invalid>'`
41. **node A server is alive** -- `kill -0 2312462 2>/dev/null && echo ALIVE || echo DEAD`
42. **install alpha.article** -- `base64 -d > $HOME/fn-deploy/native915-783db50/a/alpha.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; QQ0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogVHVlLCAyMiBTZXAgMjAyNiAwMTo0Mjox ; NyArMDAwMA0KTWVzc2FnZS1JRDogPGFscGhhQGEuZXhhbXBsZS5pbnZhbGlkPg0KDQpXcml0dGVu ; IG9uIG5vZGUgQSBieSB0aGUgdjAgbWF0cml4IHRocm91Z2ggdGhlIG5hdGl2ZSBvcGVyYXRvci4N ; C...`
43. **node A outcome accepted** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml post --message-id '<alpha@a.example.invalid>' --payload $HOME/fn-deploy/native915-783db50/a/alpha.article --group fn.letters`
44. **install alpha.article** -- `base64 -d > $HOME/fn-deploy/native915-783db50/a/alpha.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; QQ0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogVHVlLCAyMiBTZXAgMjAyNiAwMTo0Mjox ; OCArMDAwMA0KTWVzc2FnZS1JRDogPGFscGhhQGEuZXhhbXBsZS5pbnZhbGlkPg0KDQpXcml0dGVu ; IG9uIG5vZGUgQSBieSB0aGUgdjAgbWF0cml4IHRocm91Z2ggdGhlIG5hdGl2ZSBvcGVyYXRvci4N ; C...`
45. **node A outcome refused** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml post --message-id '<alpha@a.example.invalid>' --payload $HOME/fn-deploy/native915-783db50/a/alpha.article --group fn.letters`
46. **install stream-a.article** -- `base64 -d > $HOME/fn-deploy/native915-783db50/a/stream-a.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IGZvciB0aGUgc3RyZWFtaW5nIG9m ; ZmVyDQpOZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDAxOjQy ; OjE5ICswMDAwDQpNZXNzYWdlLUlEOiA8c3RyZWFtLWFAZXhhbXBsZS5pbnZhbGlkPg0KDQpTZWVk ; ZWQgb24gbm9kZSBBIGJ5IHRoZSB2MCBtYXRyaXguDQo= ; FN_GATE_EOF ; chmod 644 $HOME/...`
47. **node A seed <stream-a@example.invalid>** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml post --message-id '<stream-a@example.invalid>' --payload $HOME/fn-deploy/native915-783db50/a/stream-a.article --group fn.letters`
48. **node B server is alive** -- `kill -0 2312686 2>/dev/null && echo ALIVE || echo DEAD`
49. **node B serves fn.matrix** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py presence --port 11191 --groups fn.matrix`
50. **node B server is alive** -- `kill -0 2312686 2>/dev/null && echo ALIVE || echo DEAD`
51. **node B POST cycle** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --user '' --secret ''`
52. **node B server is alive** -- `kill -0 2312686 2>/dev/null && echo ALIVE || echo DEAD`
53. **node B reader surface** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-b3ec5e97e130-b@example.invalid>' --absent '<absent@example.invalid>'`
54. **node B server is alive** -- `kill -0 2312686 2>/dev/null && echo ALIVE || echo DEAD`
55. **install beta.article** -- `base64 -d > $HOME/fn-deploy/native915-783db50/b/beta.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; Qg0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogVHVlLCAyMiBTZXAgMjAyNiAwMTo0Mjoy ; MiArMDAwMA0KTWVzc2FnZS1JRDogPGJldGFAYi5leGFtcGxlLmludmFsaWQ+DQoNCldyaXR0ZW4g ; b24gbm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXggdGhyb3VnaCB0aGUgbmF0aXZlIG9wZXJhdG9yLg0K ; FN...`
56. **node B outcome accepted** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml post --message-id '<beta@b.example.invalid>' --payload $HOME/fn-deploy/native915-783db50/b/beta.article --group fn.letters`
57. **install beta.article** -- `base64 -d > $HOME/fn-deploy/native915-783db50/b/beta.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; Qg0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogVHVlLCAyMiBTZXAgMjAyNiAwMTo0Mjoy ; MyArMDAwMA0KTWVzc2FnZS1JRDogPGJldGFAYi5leGFtcGxlLmludmFsaWQ+DQoNCldyaXR0ZW4g ; b24gbm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXggdGhyb3VnaCB0aGUgbmF0aXZlIG9wZXJhdG9yLg0K ; FN...`
58. **node B outcome refused** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml post --message-id '<beta@b.example.invalid>' --payload $HOME/fn-deploy/native915-783db50/b/beta.article --group fn.letters`
59. **install stream-b.article** -- `base64 -d > $HOME/fn-deploy/native915-783db50/b/stream-b.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IGZvciB0aGUgc3RyZWFtaW5nIG9m ; ZmVyDQpOZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDAxOjQy ; OjI0ICswMDAwDQpNZXNzYWdlLUlEOiA8c3RyZWFtLWJAZXhhbXBsZS5pbnZhbGlkPg0KDQpTZWVk ; ZWQgb24gbm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXguDQo= ; FN_GATE_EOF ; chmod 644 $HOME/...`
60. **node B seed <stream-b@example.invalid>** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml post --message-id '<stream-b@example.invalid>' --payload $HOME/fn-deploy/native915-783db50/b/stream-b.article --group fn.letters`
61. **node A server is alive** -- `kill -0 2312462 2>/dev/null && echo ALIVE || echo DEAD`
62. **node B server is alive** -- `kill -0 2312686 2>/dev/null && echo ALIVE || echo DEAD`
63. **node B server is alive** -- `kill -0 2312686 2>/dev/null && echo ALIVE || echo DEAD`
64. **transit AB: offer <alpha@a.example.invalid> from A to B** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
65. **transit AB: CHECK/TAKETHIS <stream-a@example.invalid> from A to B** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py stream --from-port 11190 --to-port 11191 --msgid '<stream-a@example.invalid>'`
66. **node A server is alive** -- `kill -0 2312462 2>/dev/null && echo ALIVE || echo DEAD`
67. **transit BA: offer <beta@b.example.invalid> from B to A** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
68. **transit BA: CHECK/TAKETHIS <stream-b@example.invalid> from B to A** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py stream --from-port 11191 --to-port 11190 --msgid '<stream-b@example.invalid>'`
69. **node A server is alive** -- `kill -0 2312462 2>/dev/null && echo ALIVE || echo DEAD`
70. **node A capability pins** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py pins --port 11190 --group fn.letters --user '' --secret ''`
71. **node B server is alive** -- `kill -0 2312686 2>/dev/null && echo ALIVE || echo DEAD`
72. **node B capability pins** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py pins --port 11191 --group fn.letters --user '' --secret ''`
73. **node A server is alive** -- `kill -0 2312462 2>/dev/null && echo ALIVE || echo DEAD`
74. **node B server is alive** -- `kill -0 2312686 2>/dev/null && echo ALIVE || echo DEAD`
75. **a second reader across node A's POST** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; python3 $HOME/fn-deploy/native915-783db50/gate-run/matrix.py concurrent --port 11190 --group fn.letters --msgid '<concurrent@example.invalid>' --user '' --secret ''`
76. **node A server is alive** -- `kill -0 2312462 2>/dev/null && echo ALIVE || echo DEAD`
77. **node B server is alive** -- `kill -0 2312686 2>/dev/null && echo ALIVE || echo DEAD`
78. **offline group create while the owner holds the store** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml group create fn.matrix.offline`
79. **native public peering/restart witness** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; image=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_befo...`
80. **stop server node A (main)** -- `if [ -f $HOME/fn-deploy/native915-783db50/a/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native915-783db50/a/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native915-783db50/a/server.pid ; fi ; echo stopped`
81. **node A store after the stop** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml status`
82. **node A recover after the stop** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml recover`
83. **node A log tail** -- `tail -12 $HOME/fn-deploy/native915-783db50/a/server-a-main.log 2>/dev/null || echo NO-LOG`
84. **stop server node B (main)** -- `if [ -f $HOME/fn-deploy/native915-783db50/b/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native915-783db50/b/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native915-783db50/b/server.pid ; fi ; echo stopped`
85. **node B store after the stop** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml status`
86. **node B recover after the stop** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/b/fn.toml recover`
87. **node B log tail** -- `tail -12 $HOME/fn-deploy/native915-783db50/b/server-b-main.log 2>/dev/null || echo NO-LOG`
88. **peer remove a peer that is not there** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml peer remove no-such-peer`
89. **peer remove the configured peer** -- `cd $HOME/fn-deploy/native915-783db50 || exit 9 ; env FN_NATIVE_HOST=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host packaging/fn-native operator /home/ember/fn-native915-matrix/a/fn.toml peer remove b`
90. **stop server node A (main)** -- `if [ -f $HOME/fn-deploy/native915-783db50/a/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native915-783db50/a/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native915-783db50/a/server.pid ; fi ; echo stopped`
91. **stop the tap in front of node A** -- `if [ -f $HOME/fn-deploy/native915-783db50/a/tap.pid ]; then ; pid=$(cat $HOME/fn-deploy/native915-783db50/a/tap.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 10); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native915-783db50/a/tap.pid ; fi ; echo stopped`
92. **stop server node B (main)** -- `if [ -f $HOME/fn-deploy/native915-783db50/b/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native915-783db50/b/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native915-783db50/b/server.pid ; fi ; echo stopped`
93. **stop the tap in front of node B** -- `if [ -f $HOME/fn-deploy/native915-783db50/b/tap.pid ]; then ; pid=$(cat $HOME/fn-deploy/native915-783db50/b/tap.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 10); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native915-783db50/b/tap.pid ; fi ; echo stopped`
94. **stray fn processes** -- `pgrep -f 'fn-deploy/native915-783db50' >/dev/null 2>&1 && echo STRAY || echo CLEAN`
95. **remove the deploy tree** -- `rm -rf $HOME/fn-deploy/native915-783db50`
96. **release deploy lock** -- `rmdir $HOME/fn-deploy/.locks/native915-783db50.lock`

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
--- 15 node A group create fn.matrix (rc=0)
configured generation=2 record=00000002.cfg verification=VERIFIED
accepted operator group
--- 16 node A group create fn.matrix.throwaway (rc=0)
configured generation=3 record=00000003.cfg verification=VERIFIED
accepted operator group
--- 17 node A group retire fn.matrix.throwaway (rc=0)
configured generation=4 record=00000004.cfg verification=VERIFIED
accepted operator group
--- 18 node A group retire an unserved group (rc=1)
refused operator group administrative configuration refused: NO-SUCH-GROUP
--- 19 node A capacity scratch store (rc=0)
initialized /home/ember/fn-deploy/native915-783db50/a/capacity/store
--- 20 node A capacity 64 (rc=5)
fn-host: error: operator configuration file is missing
--- 21 node B group create fn.matrix (rc=0)
configured generation=2 record=00000002.cfg verification=VERIFIED
accepted operator group
--- 22 node B group create fn.matrix.throwaway (rc=0)
configured generation=3 record=00000003.cfg verification=VERIFIED
accepted operator group
--- 23 node B group retire fn.matrix.throwaway (rc=0)
configured generation=4 record=00000004.cfg verification=VERIFIED
accepted operator group
--- 24 node B group retire an unserved group (rc=1)
refused operator group administrative configuration refused: NO-SUCH-GROUP
--- 25 node B capacity scratch store (rc=0)
initialized /home/ember/fn-deploy/native915-783db50/b/capacity/store
--- 26 node B capacity 64 (rc=5)
fn-host: error: operator configuration file is missing
--- 27 node B configured port (rc=0)
11191
--- 28 node A peer record for B (rc=0)
configured generation=5 record=00000005.cfg verification=VERIFIED
accepted operator peer
--- 29 node A configured port (rc=0)
11190
--- 30 node B peer record for A (rc=0)
configured generation=5 record=00000005.cfg verification=VERIFIED
accepted operator peer
--- 31 start server (node A (native-operator), a-main) (rc=0)
LISTENING 11190
--- 32 node A pid (rc=0)
2312462
--- 33 start server (node B (native-operator), b-main) (rc=0)
LISTENING 11191
--- 34 node B pid (rc=0)
2312686
--- 35 node A server is alive (rc=0)
ALIVE
--- 36 node A serves fn.matrix (rc=0)
{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}
--- 37 node A server is alive (rc=0)
ALIVE
--- 38 node A POST cycle (rc=0)
{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-b210aefdde17-a@example.invalid> article follows", "DUPLICATE POST": "340 send article to be posted", "DUPLICATE": "441 posting failed; the article was refused", "DATE AFTER DUPLICATE": "111 20260922014210", "counted": true, "ok": true}
--- 39 node A server is alive (rc=0)
ALIVE
--- 40 node A reader surface (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING"], "MODE READER": "200 posting allowed", "LIST ACTIVE": "215 list of active newsgroups follows", "LIST NEWSGROUPS": "215 list of newsgroups follows", "LIST OVERVIEW.FMT": "215 order of fields in overview database", "LIST ACTIVE.TIMES": "215 information follows", "LIST HEADERS": "215 field list follows", "GROUP": "211 1 1 1 fn.letters", "group_count": 1, "group_first": 1, "group_last": 1, "LISTGROUP": "211 1 1 1 fn.letters list follows", "ARTICLE": "220 1 <native-matrix-b210aefdde17-a@example.invalid> article follows", "HEAD": "221 1 <native-matrix-b210aefdde17-a@example.invalid> headers follow", "BODY": "222 1 <native-matrix-b210aefdde17-a@example.invalid> body follows", "STAT": "223 1 <native-matrix-b210aefdde17-a@example.invalid> retrieved", "ARTICLE MSGID": "220 0 <native-matrix-b210aefdde17-a@example.invalid> article follows", "ARTICLE ABSENT": "430 no article with that message-id", "OVER": "224 overview information follows", "OVER RANGE": "224 overview information follows", "HDR": "225 headers follow", "XOVER": "224 overview information follows", "XHDR": "221 header follows", "XPAT": "221 header follows", "NEXT": "421 no next article", "LAST": "422 no previous article", "DATE": "111 20260922014210", "HELP": "100 help text follows", "UNKNOWN": "500 command not recognized", "FRAMING": "111 20260922014210", "FRAMING SAME": true, "ok": true}
--- 41 node A server is alive (rc=0)
ALIVE
--- 42 install alpha.article (rc=0)
--- 43 node A outcome accepted (rc=0)
accepted operator post ACCEPTED
--- 44 install alpha.article (rc=0)
--- 45 node A outcome refused (rc=1)
refused operator post REFUSED
--- 46 install stream-a.article (rc=0)
--- 47 node A seed <stream-a@example.invalid> (rc=0)
accepted operator post ACCEPTED
--- 48 node B server is alive (rc=0)
ALIVE
--- 49 node B serves fn.matrix (rc=0)
{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}
--- 50 node B server is alive (rc=0)
ALIVE
--- 51 node B POST cycle (rc=0)
{"GROUP BEFORE": "211 3 1 3 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 4 1 4 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-b3ec5e97e130-b@example.invalid> article follows", "DUPLICATE POST": "340 send article to be posted", "DUPLICATE": "441 posting failed; the article was refused", "DATE AFTER DUPLICATE": "111 20260922014212", "counted": true, "ok": true}
--- 52 node B server is alive (rc=0)
ALIVE
--- 53 node B reader surface (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING"], "MODE READER": "200 posting allowed", "LIST ACTIVE": "215 list of active newsgroups follows", "LIST NEWSGROUPS": "215 list of newsgroups follows", "LIST OVERVIEW.FMT": "215 order of fields in overview database", "LIST ACTIVE.TIMES": "215 information follows", "LIST HEADERS": "215 field list follows", "GROUP": "211 4 1 4 fn.letters", "group_count": 4, "group_first": 1, "group_last": 4, "LISTGROUP": "211 4 1 4 fn.letters list follows", "ARTICLE": "220 1 <native-matrix-b210aefdde17-a@example.invalid> article follows", "HEAD": "221 1 <native-matrix-b210aefdde17-a@example.invalid> headers follow", "BODY": "222 1 <native-matrix-b210aefdde17-a@example.invalid> body follows", "STAT": "223 1 <native-matrix-b210aefdde17-a@example.invalid> retrieved", "ARTICLE MSGID": "220 0 <native-matrix-b3ec5e97e130-b@example.invalid> article follows", "ARTICLE ABSENT": "430 no article with that message-id", "OVER": "224 overview information follows", "OVER RANGE": "224 overview information follows", "HDR": "225 headers follow", "XOVER": "224 overview information follows", "XHDR": "221 header follows", "XPAT": "221 header follows", "NEXT": "223 2 <alpha@a.example.invalid> retrieved", "LAST": "223 1 <native-matrix-b210aefdde17-a@example.invalid> retrieved", "DATE": "111 20260922014212", "HELP": "100 help text follows", "UNKNOWN": "500 command not recognized", "FRAMING": "111 20260922014212", "FRAMING SAME": true, "ok": true}
--- 54 node B server is alive (rc=0)
ALIVE
--- 55 install beta.article (rc=0)
--- 56 node B outcome accepted (rc=0)
accepted operator post ACCEPTED
--- 57 install beta.article (rc=0)
--- 58 node B outcome refused (rc=1)
refused operator post REFUSED
--- 59 install stream-b.article (rc=0)
--- 60 node B seed <stream-b@example.invalid> (rc=0)
accepted operator post ACCEPTED
--- 61 node A server is alive (rc=0)
ALIVE
--- 62 node B server is alive (rc=0)
ALIVE
--- 63 node B server is alive (rc=0)
ALIVE
--- 64 transit AB: offer <alpha@a.example.invalid> from A to B (rc=1)
{"msgid": "<alpha@a.example.invalid>", "source": "220 0 <alpha@a.example.invalid> article follows", "source_lines": 7, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING"], "ihave_advertised": true, "streaming_advertised": true, "mode_stream": "203 streaming permitted", "offer": "435 duplicate", "transit": true, "transfer": "(nothing sent: the offer drew 435 duplicate)", "duplicate": "435 duplicate", "loop_offer": "335 send it; end with <CR-LF>.<CR-LF>", "loop_result": "235 article transferred OK", "check_duplicate": "438 <alpha@a.example.invalid>", "takethis_duplicate": "439 <alpha@a.example.invalid>", "check_fresh": "238 <fresh.check@gate.example.invalid>", "reread": "220 0 <alpha@a.example.invalid> article follows", "identical": true, "loop_absent": "220 0 <loop-ab@example.invalid> article follows", "streaming_ok": true, "ok": false}
--- 65 transit AB: CHECK/TAKETHIS <stream-a@example.invalid> from A to B (rc=1)
{"SOURCE": "220 0 <stream-a@example.invalid> article follows", "MODE STREAM": "203 streaming permitted", "CHECK": "438 <stream-a@example.invalid>", "TAKETHIS": "439 <stream-a@example.invalid>", "CHECK AGAIN": "438 <stream-a@example.invalid>", "TAKETHIS AGAIN": "439 <stream-a@example.invalid>", "REREAD": "220 0 <stream-a@example.invalid> article follows", "IDENTICAL": true, "ok": false}
--- 66 node A server is alive (rc=0)
ALIVE
--- 67 transit BA: offer <beta@b.example.invalid> from B to A (rc=1)
{"msgid": "<beta@b.example.invalid>", "source": "220 0 <beta@b.example.invalid> article follows", "source_lines": 7, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING"], "ihave_advertised": true, "streaming_advertised": true, "mode_stream": "203 streaming permitted", "offer": "435 duplicate", "transit": true, "transfer": "(nothing sent: the offer drew 435 duplicate)", "duplicate": "435 duplicate", "loop_offer": "335 send it; end with <CR-LF>.<CR-LF>", "loop_result": "235 article transferred OK", "check_duplicate": "438 <beta@b.example.invalid>", "takethis_duplicate": "439 <beta@b.example.invalid>", "check_fresh": "238 <fresh.check@gate.example.invalid>", "reread": "220 0 <beta@b.example.invalid> article follows", "identical": true, "loop_absent": "220 0 <loop-ba@example.invalid> article follows", "streaming_ok": true, "ok": false}
--- 68 transit BA: CHECK/TAKETHIS <stream-b@example.invalid> from B to A (rc=1)
{"SOURCE": "220 0 <stream-b@example.invalid> article follows", "MODE STREAM": "203 streaming permitted", "CHECK": "438 <stream-b@example.invalid>", "TAKETHIS": "439 <stream-b@example.invalid>", "CHECK AGAIN": "438 <stream-b@example.invalid>", "TAKETHIS AGAIN": "439 <stream-b@example.invalid>", "REREAD": "220 0 <stream-b@example.invalid> article follows", "IDENTICAL": true, "ok": false}
--- 69 node A server is alive (rc=0)
ALIVE
--- 70 node A capability pins (rc=0)
{"advertised": ["VERSION", "READER", "POST", "OVER", "HDR", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING"], "answered": {"READER": "211 7 1 7 fn.letters", "POST": "340 send article to be posted", "POST CLOSE": "441 posting failed; the article is not valid syntax", "IHAVE": "335 send it; end with <CR-LF>.<CR-LF>", "IHAVE CLOSE": "437 transfer rejected; not a valid article", "STREAMING": "203 streaming permitted", "OVER": "412 no newsgroup selected", "HDR": "412 no newsgroup selected", "LIST": "215 list of active newsgroups follows", "NEWNEWS": "500 command not recognized", "AUTHINFO": "381 password required", "STARTTLS": "580 can not initiate TLS negotiation", "MODE-READER": "200 posting allowed", "XOVER": "412 no newsgroup selected", "XHDR": "412 no newsgroup selected", "XPAT": "412 no newsgroup selected", "LISTGROUP": "211 7 1 7 fn.letters list follows", "CHECK": "238 <pin.check@matrix.example.invalid>", "TAKETHIS": "439 <pin.take@matrix.example.invalid>"}, "dispatched": ["READER", "POST", "IHAVE", "STREAMING", "OVER", "HDR", "LIST", "AUTHINFO", "STARTTLS", "MODE-READER", "XOVER", "XHDR", "XPAT", "LISTGROUP", "CHECK", "TAKETHIS"], "login": {}, "advertised_not_dispatched": [], "dispatched_not_advertised": [], "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING"], "ok": true}
--- 71 node B server is alive (rc=0)
ALIVE
--- 72 node B capability pins (rc=0)
{"advertised": ["VERSION", "READER", "POST", "OVER", "HDR", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING"], "answered": {"READER": "211 7 1 7 fn.letters", "POST": "340 send article to be posted", "POST CLOSE": "441 posting failed; the article is not valid syntax", "IHAVE": "335 send it; end with <CR-LF>.<CR-LF>", "IHAVE CLOSE": "437 transfer rejected; not a valid article", "STREAMING": "203 streaming permitted", "OVER": "412 no newsgroup selected", "HDR": "412 no newsgroup selected", "LIST": "215 list of active newsgroups follows", "NEWNEWS": "500 command not recognized", "AUTHINFO": "381 password required", "STARTTLS": "580 can not initiate TLS negotiation", "MODE-READER": "200 posting allowed", "XOVER": "412 no newsgroup selected", "XHDR": "412 no newsgroup selected", "XPAT": "412 no newsgroup selected", "LISTGROUP": "211 7 1 7 fn.letters list follows", "CHECK": "238 <pin.check@matrix.example.invalid>", "TAKETHIS": "439 <pin.take@matrix.example.invalid>"}, "dispatched": ["READER", "POST", "IHAVE", "STREAMING", "OVER", "HDR", "LIST", "AUTHINFO", "STARTTLS", "MODE-READER", "XOVER", "XHDR", "XPAT", "LISTGROUP", "CHECK", "TAKETHIS"], "login": {}, "advertised_not_dispatched": [], "dispatched_not_advertised": [], "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING"], "ok": true}
--- 73 node A server is alive (rc=0)
ALIVE
--- 74 node B server is alive (rc=0)
ALIVE
--- 75 a second reader across node A's POST (rc=0)
{"WATCHER BEFORE": "211 7 1 7 fn.letters", "POST": "340 send article to be posted", "WATCHER MID": "211 7 1 7 fn.letters", "WATCHER ARTICLE MID": "223 1 <native-matrix-b210aefdde17-a@example.invalid> retrieved", "COMMIT": "240 article received OK", "WATCHER AFTER": "211 7 1 7 fn.letters", "ok": true}
--- 76 node A server is alive (rc=0)
ALIVE
--- 77 node B server is alive (rc=0)
ALIVE
--- 78 offline group create while the owner holds the store (rc=1)
refused operator group store is already locked
--- 79 native public peering/restart witness (rc=0)
NATIVE-PEERING-EXPECTED-RUNTIME b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5
NATIVE-PEERING-EXPECTED-CORE eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2
test_public_native_nodes_exchange_both_ways_and_suppress_duplicate (tests.test_native_peering.NativePeeringTests.test_public_native_nodes_exchange_both_ways_and_suppress_duplicate) ... ok
test_durable_feed_requeues_after_source_process_death (tests.test_native_peering.NativePeeringTests.test_durable_feed_requeues_after_source_process_death) ... native-peering launcher-sha256=2d8259c22388119793ad3dde525497f9095bdb2489ac01e597b439f3d0ff5c09 core-sha256=eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2 declared-source=source-commit=915d5c729877eddee7dd3f72eadad21cca463d1a source-manifest-sha256=eb0051343d388901b48e7f1de281ba3d1f6079cab062f25060b186cf01e3aaa4
NATIVE-PEERING-WITNESS {"feed": {"ab": {"duplicate": "435", "identical": true}, "ba": {"duplicate": "435", "identical": true}}, "identity": {"a": {"core": "/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host.core", "core_sha256": "eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2", "runtime": "/home/ember/fn-tools/sbcl/bin/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}, "b": {"core": "/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host.core", "core_sha256": "eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2", "runtime": "/home/ember/fn-tools/sbcl/bin/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}}, "kind": "transit-and-feed", "transit": {"ab": {"duplicate": "435", "identical": true, "offer": "335", "transfer": "235"}, "ba": {"duplicate": "435", "identical": true, "offer": "335", "transfer": "235"}}}
NATIVE-PEERING-WITNESS {"duplicate": "435", "identity": {"restart-a": {"core": "/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host.core", "core_sha256": "eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2", "runtime": "/home/ember/fn-tools/sbcl/bin/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}, "restart-b": {"core": "/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host.core", "core_sha256": "eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2", "runtime": "/home/ember/fn-tools/sbcl/bin/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}}, "journal": true, "kind": "requeue-restart", "source_killed": true, "source_restarted": true, "target_identical": true}
ok

----------------------------------------------------------------------
Ran 2 tests in 3.728s

OK
--- 80 stop server node A (main) (rc=0)
stopped
--- 81 node A store after the stop (rc=0)
transactions=8 articles=8 staging-orphans=0 unsigned-legacy-experiment
accepted operator STATUS
--- 82 node A recover after the stop (rc=0)
recovered transactions=8 articles=8 staging-orphans=0 anchor=none checkpoint=none
accepted operator RECOVER
--- 83 node A log tail (rc=0)
CONTROL /home/ember/fn-native915-matrix/a/control.sock
LISTENING 11190
accepted operator run
--- 84 stop server node B (main) (rc=0)
stopped
--- 85 node B store after the stop (rc=0)
transactions=8 articles=8 staging-orphans=0 unsigned-legacy-experiment
accepted operator STATUS
--- 86 node B recover after the stop (rc=0)
recovered transactions=8 articles=8 staging-orphans=0 anchor=none checkpoint=none
accepted operator RECOVER
--- 87 node B log tail (rc=0)
CONTROL /home/ember/fn-native915-matrix/b/control.sock
LISTENING 11191
accepted operator run
--- 88 peer remove a peer that is not there (rc=1)
refused operator peer administrative configuration refused: NO-SUCH-PEER
--- 89 peer remove the configured peer (rc=0)
configured generation=6 record=00000006.cfg verification=VERIFIED
accepted operator peer
--- 90 stop server node A (main) (rc=0)
stopped
--- 91 stop the tap in front of node A (rc=0)
stopped
--- 92 stop server node B (main) (rc=0)
stopped
--- 93 stop the tap in front of node B (rc=0)
stopped
--- 94 stray fn processes (rc=0)
CLEAN
--- 95 remove the deploy tree (rc=0)
--- 96 release deploy lock (rc=0)
```
