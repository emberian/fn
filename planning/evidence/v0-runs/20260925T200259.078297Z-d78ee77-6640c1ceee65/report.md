# v0 matrix: d78ee77 on hbox

v0 is every feature of fn usable between two peered fn nodes. This is that
question asked feature by feature against one commit on one box, with five
verdicts and no pass/fail collapse: accepted, refused and uncertain are the
three outcomes and each is a real observation; not-exercised names what
blocked the row; not-built names the lane that owns the missing feature.
It establishes nothing about the books beyond which certificates ACL2 read.

## What ran

| fact | value |
| --- | --- |
| commit | `d78ee77` (d78ee77d8969e89c0996163c4001d30e73c6a95b) |
| tree | `native-e747dbcc` |
| host | `hbox` |
| started | 2026-09-25T20:02:59Z |
| wall time | 82.4 s |
| gate tool | `tools/v0_matrix.py` |
| os | Ubuntu 24.10 kernel=Linux 6.11.0-29-generic arch=x86_64 cores=24 |
| python3 | Python 3.12.7 |
| acl2version | + ACL2 Version 8.7                                                     + |
| certificates | not acquired by this slice; it consumes the explicitly named saved image |
| node a | native-operator on port 11190 (main), store $HOME/fn-deploy/native-e747dbcc-d78ee77/a/store |
| node b | native-operator on port 11191 (main), store $HOME/fn-deploy/native-e747dbcc-d78ee77/b/store |
| server entry point | native-operator |
| three outcomes a | accepted=0 refused=1 uncertain=3 (uncertain is the init scratch node's, not this one's) |
| three outcomes b | accepted=0 refused=1 uncertain=3 (uncertain is the init scratch node's, not this one's) |
| rows | 220 rows: 107 accepted, 26 refused, 2 uncertain, 84 not exercised, 1 not built, 0 disagreed, 0 faulted |
| alt | python3.12 Python 3.12.7 |
| duplicate resubmission a | identical octets: rc=0 accepted operator post DUPLICATE / different octets under the same Message-ID: rc=1 refused operator post REFUSED |
| duplicate resubmission b | identical octets: rc=0 accepted operator post DUPLICATE / different octets under the same Message-ID: rc=1 refused operator post REFUSED |
| execution backend | native-operator |
| execution image | launcher sha256=ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142; image sha256=432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505; declared runtime=b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5; sidecar core sha256=0c96e554fae5ed7345b6ac2be89a9975430e879afae0ba5ccb072720dbd38d08 (static only before a live-owner witness); source correspondence unestablished |
| execution source | d78ee77 |
| server | node B (native-operator) on port 11191 (b-main) |
| host clients | expect=ABSENT, inews=ABSENT, nn=ABSENT, script=/usr/bin/script, slrn=ABSENT, tin=/home/hbox/.cargo/bin/tin, trn=ABSENT |

## The v0 matrix

**Execution subject.** Backend `native-operator`; deployed source `d78ee77`; runtime image `launcher sha256=ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142; image sha256=432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505; declared runtime=b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5; sidecar core sha256=0c96e554fae5ed7345b6ac2be89a9975430e879afae0ba5ccb072720dbd38d08 (static only before a live-owner witness); source correspondence unestablished`. These are separate labels: naming the source and hashing an externally supplied image does not prove they correspond.

220 rows: 107 accepted, 26 refused, 2 uncertain, 84 not exercised, 1 not built; 0 row(s) did not do what they were designed to do, and 0 exited with a host fault or usage error, which is not an outcome and is counted among the not exercised. Every count here is `tools/v0_matrix.py`'s over the rows below, and `planning/evidence/v0-runs/20260925T200259.078297Z-d78ee77-6640c1ceee65/matrix.json` carries the same rows with their digest.


**Who saw it.** 2 of the 135 outcome rows were observed by something that is not fn's own code; 133 were observed by fn talking to fn. A feature that only fn's own client has ever seen is a weaker claim than "usable between two peered servers" reads, and every row carries the client that saw it in its `client` field. Clients in this run: fn CLI (exit code) (38); stdlib nntplib on python3.12 (2); the matrix's raw-socket driver (96).

| feature | accepted | refused | uncertain | not exercised | not built | disagreed |
| --- | --- | --- | --- | --- | --- | --- |
| node init, configuration, start and stop (F-NODE) | 11 | 2 | 0 | 3 | 0 | 0 |
| the three outcomes on the operator surface (F-OUT) | 4 | 2 | 2 | 0 | 0 | 0 |
| groups, capacity, peers and live reconfiguration (F-GROUP) | 12 | 4 | 0 | 4 | 0 | 0 |
| principals, AUTHINFO and posting permission (F-AUTH) | 12 | 4 | 0 | 0 | 1 | 0 |
| POST and its read-back (F-POST) | 10 | 4 | 0 | 1 | 0 | 0 |
| the reader profile on each node (F-READ) | 54 | 10 | 0 | 0 | 0 | 0 |
| capability truthfulness (F-PIN) | 0 | 0 | 0 | 4 | 0 | 0 |
| transit inbound, A to B and B to A (F-TRANSIT) | 2 | 0 | 0 | 30 | 0 | 0 |
| the owner-driven outbound feed (F-FEED) | 0 | 0 | 0 | 4 | 0 | 0 |
| checkpoint, recovery and the process-death cut table (F-CRASH) | 0 | 0 | 0 | 9 | 0 | 0 |
| BP over TCPCLv4 between the two nodes (F-BP) | 0 | 0 | 0 | 8 | 0 | 0 |
| statement sign and verify across the pair (F-STX) | 0 | 0 | 0 | 6 | 0 | 0 |
| the carried-media letter (F-MEDIA) | 0 | 0 | 0 | 3 | 0 | 0 |
| scale (F-SCALE) | 0 | 0 | 0 | 1 | 0 | 0 |
| INN as a third node (F-INN) | 0 | 0 | 0 | 10 | 0 | 0 |
| independent newsreader clients (F-CLIENT) | 2 | 0 | 0 | 1 | 0 | 0 |

### Every row

| row | title | verdict | expected | agrees | independent | observed |
| --- | --- | --- | --- | --- | --- | --- |
| `V0-NODE-INIT-A` | fn init creates the store and writes fn.toml | **accepted** | accepted | yes | fn only | rc=0 initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/a/init/store |
| `V0-NODE-INIT-B` | fn init creates the store and writes fn.toml | **accepted** | accepted | yes | fn only | rc=0 initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/b/init/store |
| `V0-NODE-CONFIG-A` | the native operator initializes the store named by fn.toml [store] path | **accepted** | accepted | yes | fn only | initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/a/init/store |
| `V0-NODE-CONFIG-B` | the native operator initializes the store named by fn.toml [store] path | **accepted** | accepted | yes | fn only | initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/b/init/store |
| `V0-NODE-REINIT-A` | what a second fn init over a store that already holds articles does | **refused** | - | - | fn only | rc=1 refused operator init STORE-EXISTS |
| `V0-NODE-REINIT-B` | what a second fn init over a store that already holds articles does | **refused** | - | - | fn only | rc=1 refused operator init STORE-EXISTS |
| `V0-NODE-REINIT-SAFE-A` | the articles the store already held are still there after the second init | **accepted** | accepted | yes | fn only | before: recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none / after: recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none |
| `V0-NODE-REINIT-SAFE-B` | the articles the store already held are still there after the second init | **accepted** | accepted | yes | fn only | before: recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none / after: recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none |
| `V0-NODE-STATUS-A` | fn status reports generation and article count | **accepted** | accepted | yes | fn only | rc=0 transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment |
| `V0-NODE-STATUS-B` | fn status reports generation and article count | **accepted** | accepted | yes | fn only | rc=0 transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment |
| `V0-NODE-START-A` | the service starts and reaches LISTENING | **accepted** | accepted | yes | fn only | `native-operator` reached LISTENING |
| `V0-NODE-START-B` | the service starts and reaches LISTENING | **accepted** | accepted | yes | fn only | `native-operator` reached LISTENING |
| `V0-NODE-STOP-A` | the service stops and releases the store | **not-exercised** | accepted | - | - | (not run) |
| `V0-NODE-STOP-B` | the service stops and releases the store | **not-exercised** | accepted | - | - | (not run) |
| `V0-NODE-LOOPBACK` | the wildcard listener host is rejected before bind | **not-exercised** | - | - | - | rc=5 usage operator request (CONFIGURATION INVALID) |
| `V0-NODE-PROFILE` | the operator honours `[log] path` (a post's line lands in the file) and refuses `[posting] agent` by name | **accepted** | accepted | yes | fn only | agent refusal: rc=5 usage operator run (UNSUPPORTED-PROFILE agent); post: rc=0 accepted operator post ACCEPTED; log line: accepted post path=control message-id=<profile-a@example.invalid> time=2026-09 |
| `V0-OUT-ACCEPTED-A` | an accepted post exits 0 | **accepted** | accepted | yes | fn only | rc=0 accepted operator post ACCEPTED |
| `V0-OUT-ACCEPTED-B` | an accepted post exits 0 | **accepted** | accepted | yes | fn only | rc=0 accepted operator post ACCEPTED |
| `V0-OUT-REFUSED-A` | a lookup of an article the node does not hold exits 1 | **refused** | refused | yes | fn only | rc=1 refused operator post REFUSED |
| `V0-OUT-REFUSED-B` | a lookup of an article the node does not hold exits 1 | **refused** | refused | yes | fn only | rc=1 refused operator post REFUSED |
| `V0-OUT-UNCERTAIN-A` | a post interrupted after publication exits 3 and fences the store | **uncertain** | uncertain | yes | fn only | rc=3 uncertain operator post UNCERTAIN |
| `V0-OUT-UNCERTAIN-B` | a post interrupted after publication exits 3 and fences the store | **uncertain** | uncertain | yes | fn only | rc=3 uncertain operator post UNCERTAIN |
| `V0-OUT-RECOVER-A` | recover after the uncertain publication exits 0 | **accepted** | accepted | yes | fn only | rc=0 recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none |
| `V0-OUT-RECOVER-B` | recover after the uncertain publication exits 0 | **accepted** | accepted | yes | fn only | rc=0 recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none |
| `V0-GROUP-CREATE-A` | fn group create adds a served group | **accepted** | accepted | yes | fn only | rc=0 configured generation=2 record=00000002.cfg verification=VERIFIED |
| `V0-GROUP-CREATE-B` | fn group create adds a served group | **accepted** | accepted | yes | fn only | rc=0 configured generation=2 record=00000002.cfg verification=VERIFIED |
| `V0-GROUP-SERVED-A` | the new group is served over the socket | **accepted** | accepted | yes | fn only | 211 0 1 0 fn.matrix |
| `V0-GROUP-SERVED-B` | the new group is served over the socket | **accepted** | accepted | yes | fn only | 211 0 1 0 fn.matrix |
| `V0-GROUP-RETIRE-A` | fn group retire removes it again | **accepted** | accepted | yes | fn only | rc=0 configured generation=4 record=00000004.cfg verification=VERIFIED |
| `V0-GROUP-RETIRE-B` | fn group retire removes it again | **accepted** | accepted | yes | fn only | rc=0 configured generation=4 record=00000004.cfg verification=VERIFIED |
| `V0-GROUP-UNKNOWN-A` | retiring a group the node does not serve is refused | **refused** | refused | yes | fn only | rc=1 refused operator group administrative configuration refused: NO-SUCH-GROUP |
| `V0-GROUP-UNKNOWN-B` | retiring a group the node does not serve is refused | **refused** | refused | yes | fn only | rc=1 refused operator group administrative configuration refused: NO-SUCH-GROUP |
| `V0-CAP-SET-A` | fn capacity sets the retention capacity | **accepted** | accepted | yes | fn only | rc=0 configured generation=2 record=00000002.cfg verification=VERIFIED |
| `V0-CAP-SET-B` | fn capacity sets the retention capacity | **accepted** | accepted | yes | fn only | rc=0 configured generation=2 record=00000002.cfg verification=VERIFIED |
| `V0-CAP-REFUSE-A` | an article that does not fit the capacity is refused before it is written | **refused** | refused | yes | fn only | rc=1 refused operator post REFUSED |
| `V0-CAP-REFUSE-B` | an article that does not fit the capacity is refused before it is written | **refused** | refused | yes | fn only | rc=1 refused operator post REFUSED |
| `V0-PEER-ADD-A` | fn peer add writes a transit peer record | **accepted** | accepted | yes | fn only | rc=0 configured generation=6 record=00000006.cfg verification=VERIFIED |
| `V0-PEER-ADD-B` | fn peer add writes a transit peer record | **accepted** | accepted | yes | fn only | rc=0 configured generation=6 record=00000006.cfg verification=VERIFIED |
| `V0-PEER-LIST-A` | fn peer list reads the record back | **accepted** | accepted | yes | fn only | rc=0 names b.gate.example.invalid: True |
| `V0-PEER-LIST-B` | fn peer list reads the record back | **accepted** | accepted | yes | fn only | rc=0 names a.gate.example.invalid: True |
| `V0-PEER-ABSENT` | fn peer remove of a peer that is not there is refused | **not-exercised** | refused | - | - | (not run) |
| `V0-PEER-REMOVE` | fn peer remove of a configured peer is accepted | **not-exercised** | accepted | - | - | (not run) |
| `V0-CFG-LIVE` | a group declared on the running service's control channel reaches the served configuration | **not-exercised** | accepted | - | - | (not run) |
| `V0-CFG-LIVE-REFUSE` | an offline configuration command is refused while the service holds the store | **not-exercised** | refused | - | - | (not run) |
| `V0-AUTH-NEW` | fn principal new derives a principal id from a seed | **not-built** | accepted | - | - | (not run) |
| `V0-AUTH-PASSWORD-A` | fn principal set-password records an AUTHINFO credential | **accepted** | accepted | yes | fn only | rc=0 Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true |
| `V0-AUTH-PASSWORD-B` | fn principal set-password records an AUTHINFO credential | **accepted** | accepted | yes | fn only | rc=0 Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true |
| `V0-AUTH-LIST-A` | fn principal list shows the credential | **accepted** | accepted | yes | fn only | rc=0 matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true; lists matrix: True |
| `V0-AUTH-LIST-B` | fn principal list shows the credential | **accepted** | accepted | yes | fn only | rc=0 matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true; lists matrix: True |
| `V0-AUTH-ADVERTISED-A` | AUTHINFO USER is advertised while the connection is unauthenticated | **accepted** | accepted | yes | fn only | CAPABILITIES before the login: VERSION, READER, POST, OVER, HDR, XPAT, NEWNEWS, LIST, IMPLEMENTATION, IHAVE, STREAMING, AUTHINFO |
| `V0-AUTH-ADVERTISED-B` | AUTHINFO USER is advertised while the connection is unauthenticated | **accepted** | accepted | yes | fn only | CAPABILITIES before the login: VERSION, READER, POST, OVER, HDR, XPAT, NEWNEWS, LIST, IMPLEMENTATION, IHAVE, STREAMING, AUTHINFO |
| `V0-AUTH-GATED-A` | POST before a login is refused, not performed | **refused** | refused | yes | fn only | 480 authentication required |
| `V0-AUTH-GATED-B` | POST before a login is refused, not performed | **refused** | refused | yes | fn only | 480 authentication required |
| `V0-AUTH-LOGIN-A` | AUTHINFO USER then PASS answers 281 | **accepted** | accepted | yes | fn only | 281 authentication accepted |
| `V0-AUTH-LOGIN-B` | AUTHINFO USER then PASS answers 281 | **accepted** | accepted | yes | fn only | 281 authentication accepted |
| `V0-AUTH-WITHDRAWN-A` | AUTHINFO is no longer advertised once the connection is authenticated | **accepted** | accepted | yes | fn only | CAPABILITIES after the login: VERSION, READER, POST, OVER, HDR, XPAT, NEWNEWS, LIST, IMPLEMENTATION, IHAVE, STREAMING |
| `V0-AUTH-WITHDRAWN-B` | AUTHINFO is no longer advertised once the connection is authenticated | **accepted** | accepted | yes | fn only | CAPABILITIES after the login: VERSION, READER, POST, OVER, HDR, XPAT, NEWNEWS, LIST, IMPLEMENTATION, IHAVE, STREAMING |
| `V0-AUTH-POST-A` | POST after the login is accepted | **accepted** | accepted | yes | fn only | 240 article received OK |
| `V0-AUTH-POST-B` | POST after the login is accepted | **accepted** | accepted | yes | fn only | 240 article received OK |
| `V0-AUTH-WRONG-A` | a wrong password answers 481 and grants nothing | **refused** | refused | yes | fn only | 481 authentication failed |
| `V0-AUTH-WRONG-B` | a wrong password answers 481 and grants nothing | **refused** | refused | yes | fn only | 481 authentication failed |
| `V0-POST-OPEN-A` | POST on the served socket answers 340 | **accepted** | accepted | yes | fn only | 340 send article to be posted |
| `V0-POST-OPEN-B` | POST on the served socket answers 340 | **accepted** | accepted | yes | fn only | 340 send article to be posted |
| `V0-POST-COMMIT-A` | the article is accepted with 240 | **accepted** | accepted | yes | fn only | 240 article received OK |
| `V0-POST-COMMIT-B` | the article is accepted with 240 | **accepted** | accepted | yes | fn only | 240 article received OK |
| `V0-POST-READBACK-A` | the posting connection's next GROUP already counts the article | **accepted** | accepted | yes | fn only | GROUP before=211 0 1 0 fn.letters after=211 1 1 1 fn.letters |
| `V0-POST-READBACK-B` | the posting connection's next GROUP already counts the article | **accepted** | accepted | yes | fn only | GROUP before=211 0 1 0 fn.letters after=211 1 1 1 fn.letters |
| `V0-POST-FRESH-A` | a fresh connection reads it back by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <native-matrix-c93c0fc7545f-a@example.invalid> article follows |
| `V0-POST-FRESH-B` | a fresh connection reads it back by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <native-matrix-38a65a1b0259-b@example.invalid> article follows |
| `V0-POST-DUPLICATE-A` | a second POST of the same Message-ID is refused and allocates nothing | **refused** | refused | yes | fn only | 441 posting failed; this article is already stored here |
| `V0-POST-DUPLICATE-B` | a second POST of the same Message-ID is refused and allocates nothing | **refused** | refused | yes | fn only | 441 posting failed; this article is already stored here |
| `V0-POST-CLOCK-A` | a duplicate POST is refused as an article and does not cost the node its clock | **accepted** | accepted | yes | fn only | the duplicate answered '441 posting failed; this article is already stored here' and DATE afterwards answered '111 20260925200404' |
| `V0-POST-CLOCK-B` | a duplicate POST is refused as an article and does not cost the node its clock | **accepted** | accepted | yes | fn only | the duplicate answered '441 posting failed; this article is already stored here' and DATE afterwards answered '111 20260925200411' |
| `V0-POST-FROM-MAILBOX-A` | a POST whose From names no address (`From: yue`) is refused with 441 and is not served | **refused** | refused | yes | fn only | POST of `From: yue` answered '441 posting failed; From is not a valid mailbox list'; STAT of its Message-ID answered '430 no article with that message-id' |
| `V0-POST-FROM-MAILBOX-B` | a POST whose From names no address (`From: yue`) is refused with 441 and is not served | **refused** | refused | yes | fn only | POST of `From: yue` answered '441 posting failed; From is not a valid mailbox list'; STAT of its Message-ID answered '430 no article with that message-id' |
| `V0-POST-CONCURRENT` | a second reader stays live across another connection's whole POST | **not-exercised** | accepted | - | - | (not run) |
| `V0-READ-CAPABILITIES-A` | CAPABILITIES | **accepted** | accepted | yes | fn only | 101 capability list follows |
| `V0-READ-CAPABILITIES-B` | CAPABILITIES | **accepted** | accepted | yes | fn only | 101 capability list follows |
| `V0-READ-MODE-READER-A` | MODE READER | **accepted** | accepted | yes | fn only | 200 posting allowed |
| `V0-READ-MODE-READER-B` | MODE READER | **accepted** | accepted | yes | fn only | 200 posting allowed |
| `V0-READ-LIST-ACTIVE-A` | LIST ACTIVE | **accepted** | accepted | yes | fn only | 215 list of active newsgroups follows |
| `V0-READ-LIST-ACTIVE-B` | LIST ACTIVE | **accepted** | accepted | yes | fn only | 215 list of active newsgroups follows |
| `V0-READ-LIST-NEWSGROUPS-A` | LIST NEWSGROUPS | **accepted** | accepted | yes | fn only | 215 list of newsgroups follows |
| `V0-READ-LIST-NEWSGROUPS-B` | LIST NEWSGROUPS | **accepted** | accepted | yes | fn only | 215 list of newsgroups follows |
| `V0-READ-LIST-NEWSGROUPS-WILDMAT-A` | LIST NEWSGROUPS filtered by a wildmat | **accepted** | accepted | yes | fn only | 215 list of newsgroups follows |
| `V0-READ-LIST-NEWSGROUPS-WILDMAT-B` | LIST NEWSGROUPS filtered by a wildmat | **accepted** | accepted | yes | fn only | 215 list of newsgroups follows |
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
| `V0-READ-ARTICLE-A` | ARTICLE by number | **accepted** | accepted | yes | fn only | 220 1 <native-matrix-c93c0fc7545f-a@example.invalid> article follows |
| `V0-READ-ARTICLE-B` | ARTICLE by number | **accepted** | accepted | yes | fn only | 220 1 <native-matrix-38a65a1b0259-b@example.invalid> article follows |
| `V0-READ-HEAD-A` | HEAD by number | **accepted** | accepted | yes | fn only | 221 1 <native-matrix-c93c0fc7545f-a@example.invalid> headers follow |
| `V0-READ-HEAD-B` | HEAD by number | **accepted** | accepted | yes | fn only | 221 1 <native-matrix-38a65a1b0259-b@example.invalid> headers follow |
| `V0-READ-BODY-A` | BODY by number | **accepted** | accepted | yes | fn only | 222 1 <native-matrix-c93c0fc7545f-a@example.invalid> body follows |
| `V0-READ-BODY-B` | BODY by number | **accepted** | accepted | yes | fn only | 222 1 <native-matrix-38a65a1b0259-b@example.invalid> body follows |
| `V0-READ-STAT-A` | STAT by number | **accepted** | accepted | yes | fn only | 223 1 <native-matrix-c93c0fc7545f-a@example.invalid> retrieved |
| `V0-READ-STAT-B` | STAT by number | **accepted** | accepted | yes | fn only | 223 1 <native-matrix-38a65a1b0259-b@example.invalid> retrieved |
| `V0-READ-ARTICLE-MSGID-A` | ARTICLE by Message-ID | **accepted** | accepted | yes | fn only | 220 1 <native-matrix-c93c0fc7545f-a@example.invalid> article follows |
| `V0-READ-ARTICLE-MSGID-B` | ARTICLE by Message-ID | **accepted** | accepted | yes | fn only | 220 1 <native-matrix-38a65a1b0259-b@example.invalid> article follows |
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
| `V0-READ-NEWNEWS-A` | NEWNEWS over a wildmat, since an instant before the store existed | **accepted** | accepted | yes | fn only | 230 list of new articles by message-id follows |
| `V0-READ-NEWNEWS-B` | NEWNEWS over a wildmat, since an instant before the store existed | **accepted** | accepted | yes | fn only | 230 list of new articles by message-id follows |
| `V0-READ-NEWNEWS-STAMP-A` | NEWNEWS since 1970 includes this node's accepted article even when its payload date differs from its acceptance | **accepted** | accepted | yes | fn only | whole-history NEWNEWS contains target <native-matrix-c93c0fc7545f-a@example.invalid>: True |
| `V0-READ-NEWNEWS-STAMP-B` | NEWNEWS since 1970 includes this node's accepted article even when its payload date differs from its acceptance | **accepted** | accepted | yes | fn only | whole-history NEWNEWS contains target <native-matrix-38a65a1b0259-b@example.invalid>: True |
| `V0-READ-NEWNEWS-FUTURE-A` | NEWNEWS since a future instant returns the empty block | **accepted** | accepted | yes | fn only | 230 list of new articles by message-id follows |
| `V0-READ-NEWNEWS-FUTURE-B` | NEWNEWS since a future instant returns the empty block | **accepted** | accepted | yes | fn only | 230 list of new articles by message-id follows |
| `V0-READ-NEWNEWS-SYNTAX-A` | NEWNEWS with a malformed wildmat is refused with 501 | **refused** | refused | yes | fn only | 501 syntax error |
| `V0-READ-NEWNEWS-SYNTAX-B` | NEWNEWS with a malformed wildmat is refused with 501 | **refused** | refused | yes | fn only | 501 syntax error |
| `V0-READ-DATE-A` | DATE | **accepted** | accepted | yes | fn only | 111 20260925200405 |
| `V0-READ-DATE-B` | DATE | **accepted** | accepted | yes | fn only | 111 20260925200411 |
| `V0-READ-HELP-A` | HELP | **accepted** | accepted | yes | fn only | 100 help text follows |
| `V0-READ-HELP-B` | HELP | **accepted** | accepted | yes | fn only | 100 help text follows |
| `V0-READ-UNKNOWN-A` | an unknown command is refused with 500 | **refused** | refused | yes | fn only | 500 command not recognized |
| `V0-READ-UNKNOWN-B` | an unknown command is refused with 500 | **refused** | refused | yes | fn only | 500 command not recognized |
| `V0-READ-FRAMING-A` | a command split across two TCP segments is answered once, the same way | **accepted** | accepted | yes | fn only | DATE split across two segments answered '111 20260925200405' against '111 20260925200405' |
| `V0-READ-FRAMING-B` | a command split across two TCP segments is answered once, the same way | **accepted** | accepted | yes | fn only | DATE split across two segments answered '111 20260925200411' against '111 20260925200411' |
| `V0-PIN-DISPATCHED-A` | every capability the node advertises is dispatched by the node | **not-exercised** | accepted | - | - | (not run) |
| `V0-PIN-DISPATCHED-B` | every capability the node advertises is dispatched by the node | **not-exercised** | accepted | - | - | (not run) |
| `V0-PIN-ADVERTISED-A` | every command the node dispatches is advertised in CAPABILITIES | **not-exercised** | accepted | - | - | (not run) |
| `V0-PIN-ADVERTISED-B` | every command the node dispatches is advertised in CAPABILITIES | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-IDENTITY-A` | the node has an RFC 5537 <path-identity> of its own | **accepted** | accepted | yes | fn only | rc=0 configured generation=5 record=00000005.cfg verification=VERIFIED |
| `V0-TRANSIT-IDENTITY-B` | the node has an RFC 5537 <path-identity> of its own | **accepted** | accepted | yes | fn only | rc=0 configured generation=5 record=00000005.cfg verification=VERIFIED |
| `V0-TRANSIT-INDEPENDENT-A` | each node serves its own seeded articles and 43x for the other's seeds | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-INDEPENDENT-B` | each node serves its own seeded articles and 43x for the other's seeds | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-MODE-STREAM-AB` | MODE STREAM is accepted on the peer connection | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-MODE-STREAM-BA` | MODE STREAM is accepted on the peer connection | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-OFFER-AB` | IHAVE of a wanted article answers 335 | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-OFFER-BA` | IHAVE of a wanted article answers 335 | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-TRANSFER-AB` | the transferred article is taken with 235 | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-TRANSFER-BA` | the transferred article is taken with 235 | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-IDENTICAL-AB` | the far side serves the source's octets with its own path identity and the diagnostic prepended to Path and no Xref, every other line identical | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-IDENTICAL-BA` | the far side serves the source's octets with its own path identity and the diagnostic prepended to Path and no Xref, every other line identical | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-DUPLICATE-AB` | a second IHAVE of the same Message-ID is refused with 435 | **not-exercised** | refused | - | - | (not run) |
| `V0-TRANSIT-DUPLICATE-BA` | a second IHAVE of the same Message-ID is refused with 435 | **not-exercised** | refused | - | - | (not run) |
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
| `V0-TRANSIT-TLS-AB` | the owner's feed reaches the peer over STARTTLS, the peer's certificate verified against the record's anchor and server name | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-TLS-BA` | the owner's feed reaches the peer over STARTTLS, the peer's certificate verified against the record's anchor and server name | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-AUTHINFO-AB` | the owner's feed logs in with AUTHINFO as the principal the peer's record binds before it offers, and the peer takes the offer in that role | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-AUTHINFO-BA` | the owner's feed logs in with AUTHINFO as the principal the peer's record binds before it offers, and the peer takes the offer in that role | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-TLS-WRONG-ANCHOR` | a feed whose record names an anchor that did not issue the peer's certificate delivers nothing, and both owners stay up | **not-exercised** | refused | - | - | (not run) |
| `V0-TRANSIT-AUTHINFO-WRONG` | a feed whose profile carries a wrong password delivers nothing, and both owners stay up | **not-exercised** | refused | - | - | (not run) |
| `V0-FEED-QUEUE` | an article accepted on the source enters the matching peer's outbound queue | **not-exercised** | accepted | - | - | (not run) |
| `V0-FEED-OFFER` | the owner opens the session and offers it, with no hand-driven socket | **not-exercised** | accepted | - | - | (not run) |
| `V0-FEED-ONCE` | an acknowledged transfer is not offered a second time | **not-exercised** | accepted | - | - | (not run) |
| `V0-FEED-JOURNAL` | the feed journal records the transfer and survives a restart | **not-exercised** | accepted | - | - | (not run) |
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
| `V0-INN-FEED-OUT` | an article POSTed to fn reaches INN through fn's outbound feed (IHAVE 335/235) and nnrpd serves it changed only in Path and Xref | **not-exercised** | accepted | - | - | (not run) |
| `V0-INN-FEED-IN` | INN's innfeed delivers an article to fn (CHECK 238, TAKETHIS 239) and fn serves it changed at most in Path and Xref | **not-exercised** | accepted | - | - | (not run) |
| `V0-INN-DUPLICATE-INN` | INN refuses a second IHAVE of the article fn fed it with 435 | **not-exercised** | refused | - | - | (not run) |
| `V0-INN-DUPLICATE-FN` | fn refuses a second IHAVE of each article it holds (INN's and its own) with 435 | **not-exercised** | refused | - | - | (not run) |
| `V0-INN-LOOP-INN` | INN refuses an article whose Path names it with 437 | **not-exercised** | refused | - | - | (not run) |
| `V0-INN-LOOP-FN` | fn refuses an article whose Path names its own path identity, and does not serve it | **not-exercised** | refused | - | - | (not run) |
| `V0-INN-RESTART` | INN's history survives a SIGKILL of innd, and fn's articles survive a SIGTERM, recover and restart byte-identical | **not-exercised** | accepted | - | - | (not run) |
| `V0-INN-SERVING-AGENT` | an article fn took from INN is served with fn's path identity in Path and without INN's Xref (RFC 5537 3.7 steps 6 and 7) | **not-exercised** | accepted | - | - | (not run) |
| `V0-INN-OPERATOR-POST` | an article submitted through `operator post` reaches INN through fn's feed, injected with fn's Path (IHAVE 335/235) | **not-exercised** | accepted | - | - | (not run) |
| `V0-CLIENT-NNTPLIB-A` | an independent stdlib nntplib client reads a group and an article | **accepted** | accepted | yes | yes | nntplib 3.12.7 drove CAPABILITIES, GROUP, STAT, ARTICLE, HEAD, BODY, OVER, LIST, ARTICLE (absent), QUIT; login=(not attempted) authinfo-advertised=None group={'count': 4, 'first': 1, 'last': 4, 'name' |
| `V0-CLIENT-NNTPLIB-B` | an independent stdlib nntplib client reads a group and an article | **accepted** | accepted | yes | yes | nntplib 3.12.7 drove CAPABILITIES, GROUP, STAT, ARTICLE, HEAD, BODY, OVER, LIST, ARTICLE (absent), QUIT; login=(not attempted) authinfo-advertised=None group={'count': 4, 'first': 1, 'last': 4, 'name' |
| `V0-CLIENT-SLRN` | slrn reads a group and an article | **not-exercised** | accepted | - | - | (slrn is not installed) |

### What every row that is not an outcome is waiting for

- `V0-NODE-STOP-A` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-NODE-STOP-B` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-NODE-LOOPBACK` (not-exercised): the command exited 5, a usage error, which is not one of the three outcomes (docs/operator.md: 0 accepted, 1 refused, 3 uncertain)
- `V0-PEER-ABSENT` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-PEER-REMOVE` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-CFG-LIVE` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-CFG-LIVE-REFUSE` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-AUTH-NEW` (not-built): the packaged native operator has no `principal new`: the local principal id is derived by ACL2 inside `set-password` (`fn-native-auth-admin-principal`, books/native-auth-admin.lisp) and no public verb derives one from a seed -- owned by `native principal derivation surface`
- `V0-POST-CONCURRENT` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-PIN-DISPATCHED-A` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-PIN-DISPATCHED-B` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-PIN-ADVERTISED-A` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-PIN-ADVERTISED-B` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-INDEPENDENT-A` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-INDEPENDENT-B` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-MODE-STREAM-AB` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-MODE-STREAM-BA` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-OFFER-AB` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-OFFER-BA` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-TRANSFER-AB` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-TRANSFER-BA` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-IDENTICAL-AB` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-IDENTICAL-BA` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-DUPLICATE-AB` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-DUPLICATE-BA` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-LOOP-AB` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-LOOP-BA` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-LOOP-ABSENT-AB` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-LOOP-ABSENT-BA` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-CHECK-FRESH-AB` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-CHECK-FRESH-BA` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-TAKETHIS-AB` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-TAKETHIS-BA` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-CHECK-DUP-AB` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-CHECK-DUP-BA` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-TAKETHIS-DUP-AB` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-TAKETHIS-DUP-BA` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-TLS-AB` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-TLS-BA` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-AUTHINFO-AB` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-AUTHINFO-BA` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-TLS-WRONG-ANCHOR` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-TRANSIT-AUTHINFO-WRONG` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-FEED-QUEUE` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-FEED-OFFER` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-FEED-ONCE` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-FEED-JOURNAL` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-CRASH-CHECKPOINT` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-CRASH-KILL` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-CRASH-SURVIVOR` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-CRASH-RECOVER` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-CRASH-ACKNOWLEDGED` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-CRASH-INTERRUPTED` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-CRASH-RESTART` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-CRASH-CUT-TABLE` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-CRASH-CAMPAIGN` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-BP-IMAGE` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-BP-EXCHANGE` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-BP-REFUSED` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-BP-KEEPALIVE` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-BP-CRASH` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-BP-PROFILE` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-BP-REPLAY` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-BP-NODE` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-STX-SIGN` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-STX-ATTACH` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-STX-CROSS` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-STX-VERIFY` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-STX-UNVERIFIED` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-STX-READER` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-MEDIA-EXPORT` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-MEDIA-VERIFY` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-MEDIA-IMPORT` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-SCALE-CEILING` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-INN-INTEROP` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-INN-FEED-OUT` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-INN-FEED-IN` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-INN-DUPLICATE-INN` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-INN-DUPLICATE-FN` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-INN-LOOP-INN` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-INN-LOOP-FN` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-INN-RESTART` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-INN-SERVING-AGENT` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-INN-OPERATOR-POST` (not-exercised): not exercised: the driver stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne
- `V0-CLIENT-SLRN` (not-exercised): slrn is not installed on hbox (nor on hbox, measured 2026-09-20); tests/interop_slrn.py has never run against an fn node

### What each row does not show

- `V0-NODE-INIT-A`: the store `[store] path` names, created by the public operator verb rather than by the image's low-level `store ROOT init` diagnostic; the groups are the ones this command named and there is no default table, so an `init` with no group is a usage error and not a store nobody chose the contents of. A scratch node beside the served one: nothing here changes what the node serves
- `V0-NODE-INIT-B`: the store `[store] path` names, created by the public operator verb rather than by the image's low-level `store ROOT init` diagnostic; the groups are the ones this command named and there is no default table, so an `init` with no group is a usage error and not a store nobody chose the contents of. A scratch node beside the served one: nothing here changes what the node serves
- `V0-NODE-CONFIG-A`: the native image embeds ACL2; its configuration has no [acl2] path; the scratch fn.toml named this store and the native operator reported initializing that exact path; this does not test an obsolete [acl2] path
- `V0-NODE-CONFIG-B`: the native image embeds ACL2; its configuration has no [acl2] path; the scratch fn.toml named this store and the native operator reported initializing that exact path; this does not test an obsolete [acl2] path
- `V0-NODE-REINIT-A`: nothing in docs/operator.md says whether a second `init` adopts the store or refuses, so this row records the outcome rather than asserting one; the property that matters is the next row; a second `init` over the store the first one made, which by then holds a submission. The refusal is on the presence of the store's own entries -- `config.json`, `writer.lock`, `allocation-frontier.json`, `transactions/`, `config/` -- so no lock is opened to reach it; the next row is whether that is true
- `V0-NODE-REINIT-B`: nothing in docs/operator.md says whether a second `init` adopts the store or refuses, so this row records the outcome rather than asserting one; the property that matters is the next row; a second `init` over the store the first one made, which by then holds a submission. The refusal is on the presence of the store's own entries -- `config.json`, `writer.lock`, `allocation-frontier.json`, `transactions/`, `config/` -- so no lock is opened to reach it; the next row is whether that is true
- `V0-NODE-REINIT-SAFE-A`: the whole recovery line is compared, not only a count: transactions, articles, staging orphans, anchor and checkpoint are all as they were before the refused init. The store held 1 article(s), so the comparison separates more than an empty store from itself
- `V0-NODE-REINIT-SAFE-B`: the whole recovery line is compared, not only a count: transactions, articles, staging orphans, anchor and checkpoint are all as they were before the refused init. The store held 1 article(s), so the comparison separates more than an empty store from itself
- `V0-NODE-STATUS-A`: the public native operator read one preprovisioned store; this slice did not create or alter its configuration
- `V0-NODE-STATUS-B`: the public native operator read one preprovisioned store; this slice did not create or alter its configuration
- `V0-NODE-START-A`: the entry point that started is `native-operator`; every served row for this node is about that process, not about the ones above it in the list, which was given --max-connections 64
- `V0-NODE-START-B`: the entry point that started is `native-operator`; every served row for this node is about that process, not about the ones above it in the list, which was given --max-connections 64
- `V0-NODE-LOOPBACK`: operator configuration admission reports usage, not a D13 request refusal; named non-loopback IPv4 hosts are admitted; the wildcard is refused at configuration admission (`fn-native-config-listener-hostp`, books/native-config.lisp), not at bind: `0.0.0.0` never reaches a listener, and the operator reports an inadmissible configuration as a usage error (5), outside the three request outcomes. A numeric non-loopback IPv4 address is ADMITTED by design and would be bound: this row is about the wildcard, not about fn declining to serve a network interface. Nothing here tests a bind the kernel would refuse for a different reason
- `V0-NODE-PROFILE`: a scratch owner beside node A's on port 11297; the log is the file `[log] path` names, opened append-only before the store, and the line is ACL2's (books/owner-log.lisp); the agent refusal is `fn-native-config-unsupported-key`'s, and the injecting agent a served POST names is the `path-identity` policy (books/owner-agent.lisp), which this row does not read
- `V0-OUT-ACCEPTED-A`: one article submitted to the live owner over its control socket; the exit code is the observation
- `V0-OUT-ACCEPTED-B`: one article submitted to the live owner over its control socket; the exit code is the observation
- `V0-OUT-REFUSED-A`: NOT a lookup: the native operator has no article lookup verb, so the refusal observed here is a second submission of the SAME Message-ID carrying DIFFERENT octets, which the node refuses as a conflicting immutable Message-ID. A byte-identical resubmission is a different observation: it is the idempotent duplicate, reported as accepted with exit 0, and it is the `duplicate resubmission` fact
- `V0-OUT-REFUSED-B`: NOT a lookup: the native operator has no article lookup verb, so the refusal observed here is a second submission of the SAME Message-ID carrying DIFFERENT octets, which the node refuses as a conflicting immutable Message-ID. A byte-identical resubmission is a different observation: it is the idempotent duplicate, reported as accepted with exit 0, and it is the `duplicate resubmission` fact
- `V0-OUT-UNCERTAIN-A`: the OWNER is the developer image and carries `FN_NATIVE_CONTROL_FAULT=postpublish`, one entry of the same named cut table `store post --inject-fault` selects from: FNN-STORE-INDETERMINATE after the final publication, so the record is durable and its report is not. The CLIENT is the production image and invents nothing: the word is ACL2's `fn-own-control-outcome-result`, carried as the :UNCERTAIN status of books/native-control.lisp and projected to 3 by `fn-native-control-status-exit-code`. The article is asserted in neither direction afterwards; an indeterminate outcome is evidence about the report. This is not a power loss
- `V0-OUT-UNCERTAIN-B`: the OWNER is the developer image and carries `FN_NATIVE_CONTROL_FAULT=postpublish`, one entry of the same named cut table `store post --inject-fault` selects from: FNN-STORE-INDETERMINATE after the final publication, so the record is durable and its report is not. The CLIENT is the production image and invents nothing: the word is ACL2's `fn-own-control-outcome-result`, carried as the :UNCERTAIN status of books/native-control.lisp and projected to 3 by `fn-native-control-status-exit-code`. The article is asserted in neither direction afterwards; an indeterminate outcome is evidence about the report. This is not a power loss
- `V0-OUT-RECOVER-A`: recovery of the store the scratch owner released when it fenced itself on the uncertain publication above
- `V0-OUT-RECOVER-B`: recovery of the store the scratch owner released when it fenced itself on the uncertain publication above
- `V0-GROUP-CREATE-A`: one group on a store no service holds
- `V0-GROUP-CREATE-B`: one group on a store no service holds
- `V0-GROUP-SERVED-A`: the group was created before the service started
- `V0-GROUP-SERVED-B`: the group was created before the service started
- `V0-CAP-SET-A`: a scratch store beside the served one, initialised through the image's store entry, so a refusal here cannot change what the node serves
- `V0-CAP-SET-B`: a scratch store beside the served one, initialised through the image's store entry, so a refusal here cannot change what the node serves
- `V0-CAP-REFUSE-A`: the capacity was set to 1 (rc=0) on a scratch store served by an owner of its own on port 11290; the article's own charge is what has to exceed it, and the charge is ACL2's
- `V0-CAP-REFUSE-B`: the capacity was set to 1 (rc=0) on a scratch store served by an owner of its own on port 11291; the article's own charge is what has to exceed it, and the charge is ACL2's
- `V0-PEER-ADD-A`: a peer record is configuration, not authorization; the positional grammar is books/native-operator.lisp's, the inbound ceiling is the record's own default, and the outbound pattern is `-` so the hand-driven transit rows are not pre-empted by the owner's feed
- `V0-PEER-ADD-B`: a peer record is configuration, not authorization; the positional grammar is books/native-operator.lisp's, the inbound ceiling is the record's own default, and the outbound pattern is `-` so the hand-driven transit rows are not pre-empted by the owner's feed
- `V0-PEER-LIST-A`: the record read back out of the durable configuration, in the order `peer add` takes its arguments and rendered by ACL2 (`fn-native-admin-peer-report`, books/native-admin.lisp); the <path-identity> is what is matched, not the one-letter node name. It is a read: the store is opened without the exclusive writer lock and the live owner is never reached, so it runs in this offline window and would refuse while an owner held the store, exactly as `status` does
- `V0-PEER-LIST-B`: the record read back out of the durable configuration, in the order `peer add` takes its arguments and rendered by ACL2 (`fn-native-admin-peer-report`, books/native-admin.lisp); the <path-identity> is what is matched, not the one-letter node name. It is a read: the store is opened without the exclusive writer lock and the live owner is never reached, so it runs in this offline window and would refuse while an owner held the store, exactly as `status` does
- `V0-AUTH-PASSWORD-A`: the password and its confirmation are read from a file on the execution host (two lines, umask 077) because the image reads them from standard input when there is no tty; what is stored is books/auth-secret.lisp's salted verifier and the row is about the operator writing it, not about the digest's strength or the secret's protection on the wire
- `V0-AUTH-PASSWORD-B`: the password and its confirmation are read from a file on the execution host (two lines, umask 077) because the image reads them from standard input when there is no tty; what is stored is books/auth-secret.lisp's salted verifier and the row is about the operator writing it, not about the digest's strength or the secret's protection on the wire
- `V0-AUTH-LIST-A`: one registry: `set-password` writes and `list` reads the credential file the running owner loads at startup; the listing prints the login, its principal and its posting flag and never the verifier
- `V0-AUTH-LIST-B`: one registry: `set-password` writes and `list` reads the credential file the running owner loads at startup; the listing prints the login, its principal and its posting flag and never the verifier
- `V0-AUTH-ADVERTISED-A`: RFC 4643 section 2.1 as books/nntp-auth.lisp reads it: the label is offered while the connection is unauthenticated AND a credential is configured, so this row depends on the enrolment above and says nothing about a node with no credential
- `V0-AUTH-ADVERTISED-B`: RFC 4643 section 2.1 as books/nntp-auth.lisp reads it: the label is offered while the connection is unauthenticated AND a credential is configured, so this row depends on the enrolment above and says nothing about a node with no credential
- `V0-AUTH-GATED-A`: the subject is a scratch store beside node A's, served by an owner of its own on port 11292 under `[auth] required = true`; the supplied configuration is not rewritten and does not set that policy, which is why its reader and POST rows stay unauthenticated. The same owner answered '281 authentication accepted' to the login and '340 send article to be posted' to POST after it, so the refusal above is the policy and not a dead node. RFC 4643 section 2.3 does not require the same code for every gated verb
- `V0-AUTH-GATED-B`: the subject is a scratch store beside node B's, served by an owner of its own on port 11293 under `[auth] required = true`; the supplied configuration is not rewritten and does not set that policy, which is why its reader and POST rows stay unauthenticated. The same owner answered '281 authentication accepted' to the login and '340 send article to be posted' to POST after it, so the refusal above is the policy and not a dead node. RFC 4643 section 2.3 does not require the same code for every gated verb
- `V0-AUTH-LOGIN-A`: USER/PASS over an unprotected loopback connection; the secret reached the driver as a file path and is in no recorded command
- `V0-AUTH-LOGIN-B`: USER/PASS over an unprotected loopback connection; the secret reached the driver as a file path and is in no recorded command
- `V0-AUTH-POST-A`: the posting allowance of an authenticated connection is the credential's own bit and nothing else (`fn-auth-postingp`); `set-password` defaults it to true and this run did not pass `--no-posting`
- `V0-AUTH-POST-B`: the posting allowance of an authenticated connection is the credential's own bit and nothing else (`fn-auth-postingp`); `set-password` defaults it to true and this run did not pass `--no-posting`
- `V0-AUTH-WRONG-A`: one wrong password; no rate limit or lockout is tested
- `V0-AUTH-WRONG-B`: one wrong password; no rate limit or lockout is tested
- `V0-POST-COMMIT-A`: one article; the durability behind the 240 is the store's, asserted by the recovery rows below
- `V0-POST-COMMIT-B`: one article; the durability behind the 240 is the store's, asserted by the recovery rows below
- `V0-POST-DUPLICATE-A`: the duplicate is offered on a fresh connection because one clock observation is pinned per connection at accept
- `V0-POST-DUPLICATE-B`: the duplicate is offered on a fresh connection because one clock observation is pinned per connection at accept
- `V0-POST-CLOCK-A`: a 441 for an article the node already holds and a 441 for a clock the node no longer has are the same code; DATE is what separates them from outside, because a refused reading costs the owner its clock (D10-a) and DATE then answers 503. This row does not INDUCE a clock fault -- it checks that an ordinary duplicate did not cause one
- `V0-POST-CLOCK-B`: a 441 for an article the node already holds and a 441 for a clock the node no longer has are the same code; DATE is what separates them from outside, because a refused reading costs the owner its clock (D10-a) and DATE then answers 503. This row does not INDUCE a clock fault -- it checks that an ordinary duplicate did not cause one
- `V0-POST-FROM-MAILBOX-A`: one unaddressed From; the rest of the mailbox-list grammar is books/mailbox.lisp's and its witnesses are tests/acl2/injection-tests.lisp
- `V0-POST-FROM-MAILBOX-B`: one unaddressed From; the rest of the mailbox-list grammar is books/mailbox.lisp's and its witnesses are tests/acl2/injection-tests.lisp
- `V0-READ-CAPABILITIES-A`: served by `native-operator` on port 11190
- `V0-READ-CAPABILITIES-B`: served by `native-operator` on port 11191
- `V0-READ-MODE-READER-A`: served by `native-operator` on port 11190
- `V0-READ-MODE-READER-B`: served by `native-operator` on port 11191
- `V0-READ-LIST-ACTIVE-A`: served by `native-operator` on port 11190
- `V0-READ-LIST-ACTIVE-B`: served by `native-operator` on port 11191
- `V0-READ-LIST-NEWSGROUPS-A`: served by `native-operator` on port 11190
- `V0-READ-LIST-NEWSGROUPS-B`: served by `native-operator` on port 11191
- `V0-READ-LIST-NEWSGROUPS-WILDMAT-A`: served by `native-operator` on port 11190
- `V0-READ-LIST-NEWSGROUPS-WILDMAT-B`: served by `native-operator` on port 11191
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
- `V0-READ-NEWNEWS-A`: the 230 block is complete over the node's durable acceptance stamps; served by `native-operator` on port 11190
- `V0-READ-NEWNEWS-B`: the 230 block is complete over the node's durable acceptance stamps; served by `native-operator` on port 11191
- `V0-READ-NEWNEWS-STAMP-A`: served by `native-operator` on port 11190
- `V0-READ-NEWNEWS-STAMP-B`: served by `native-operator` on port 11191
- `V0-READ-NEWNEWS-FUTURE-A`: served by `native-operator` on port 11190
- `V0-READ-NEWNEWS-FUTURE-B`: served by `native-operator` on port 11191
- `V0-READ-NEWNEWS-SYNTAX-A`: served by `native-operator` on port 11190
- `V0-READ-NEWNEWS-SYNTAX-B`: served by `native-operator` on port 11191
- `V0-READ-DATE-A`: served by `native-operator` on port 11190
- `V0-READ-DATE-B`: served by `native-operator` on port 11191
- `V0-READ-HELP-A`: served by `native-operator` on port 11190
- `V0-READ-HELP-B`: served by `native-operator` on port 11191
- `V0-READ-UNKNOWN-A`: served by `native-operator` on port 11190
- `V0-READ-UNKNOWN-B`: served by `native-operator` on port 11191
- `V0-READ-FRAMING-A`: one command split at one point; the chunk-independence keystone is books/wire-invariants', not this row
- `V0-READ-FRAMING-B`: one command split at one point; the chunk-independence keystone is books/wire-invariants', not this row
- `V0-TRANSIT-IDENTITY-A`: `fn-peer-local-identity` reads the `path-identity` policy slot and an unset slot is the empty string, which `fn-path-names-p` never matches: a node without this answers no loop, so V0-TRANSIT-LOOP rests on it; a `:set-policy` configuration record; the loop rows below are what shows the owner read it
- `V0-TRANSIT-IDENTITY-B`: `fn-peer-local-identity` reads the `path-identity` policy slot and an unset slot is the empty string, which `fn-path-names-p` never matches: a node without this answers no loop, so V0-TRANSIT-LOOP rests on it; a `:set-policy` configuration record; the loop rows below are what shows the owner read it
- `V0-TRANSIT-TLS-AB`: the article's arrival under a target that refuses AUTHINFO before TLS and denies unauthenticated transit with 502 is what shows the channel; the matrix does not see the feed's own socket, and OpenSSL's chain and hostname checks are trusted integration (PRF-047)
- `V0-TRANSIT-TLS-BA`: the article's arrival under a target that refuses AUTHINFO before TLS and denies unauthenticated transit with 502 is what shows the channel; the matrix does not see the feed's own socket, and OpenSSL's chain and hostname checks are trusted integration (PRF-047)
- `V0-TRANSIT-AUTHINFO-AB`: the same arrival: an unauthenticated offer of the same article is 502 on the target, so the feed's offer came on a connection that logged in; PRF-051's keystones are what say the feed sends no offer before the 281
- `V0-TRANSIT-AUTHINFO-BA`: the same arrival: an unauthenticated offer of the same article is 502 on the target, so the feed's offer came on a connection that logged in; PRF-051's keystones are what say the feed sends no offer before the 281
- `V0-CRASH-KILL`: what the client saw is recorded; an acknowledgement after the kill would be the defect, and its absence is the assertion
- `V0-SCALE-CEILING`: a measured ceiling on one box with one payload grid; it is not a bound and not a proof
- `V0-INN-SERVING-AGENT`: fn updates Path and removes Xref once, when it accepts the transfer, and stores what it serves (specs/peering.md 2.3, books/path-update.lisp); the reader path is what this row measures, and the outbound render to a second peer is not exercised by a lab with one peer
- `V0-CLIENT-NNTPLIB-A`: one client library, and it reads: nothing here is posted or fed by a foreign client. Its framing, folding and response parsing are the standard library's, not fn's, which is the point of the row
- `V0-CLIENT-NNTPLIB-B`: one client library, and it reads: nothing here is posted or fed by a foreign client. Its framing, folding and response parsing are the standard library's, not fn's, which is the point of the row

### The exact invocation of every row

- `V0-NODE-INIT-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/fn.toml init fn.letters`
- `V0-NODE-INIT-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/fn.toml init fn.letters`
- `V0-NODE-CONFIG-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/fn.toml init fn.letters`
- `V0-NODE-CONFIG-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/fn.toml init fn.letters`
- `V0-NODE-REINIT-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/fn.toml init fn.letters`
- `V0-NODE-REINIT-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/fn.toml init fn.letters`
- `V0-NODE-REINIT-SAFE-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/fn.toml init fn.letters
cd $HOME`
- `V0-NODE-REINIT-SAFE-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/fn.toml init fn.letters
cd $HOME`
- `V0-NODE-STATUS-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml status`
- `V0-NODE-STATUS-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml status`
- `V0-NODE-START-A`: `env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml run`
- `V0-NODE-START-B`: `env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml run`
- `V0-NODE-STOP-A`: `(none)`
- `V0-NODE-STOP-B`: `(none)`
- `V0-NODE-LOOPBACK`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; mkdir -p $HOME/fn-deploy/native-e747dbcc-d78ee77/loopback && env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native store $HOME/fn-deploy/na...`
- `V0-NODE-PROFILE`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; mkdir -p $HOME/fn-deploy/native-e747dbcc-d78ee77/a/profile && rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/profile/service.log && env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0...`
- `V0-OUT-ACCEPTED-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml post --message-id '<a...`
- `V0-OUT-ACCEPTED-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml post --message-id '<b...`
- `V0-OUT-REFUSED-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml post --message-id '<a...`
- `V0-OUT-REFUSED-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml post --message-id '<b...`
- `V0-OUT-UNCERTAIN-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/fn.toml post --message-id '<i...`
- `V0-OUT-UNCERTAIN-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/fn.toml post --message-id '<i...`
- `V0-OUT-RECOVER-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/fn.toml recover`
- `V0-OUT-RECOVER-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/fn.toml recover`
- `V0-GROUP-CREATE-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml group create fn.matrix`
- `V0-GROUP-CREATE-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml group create fn.matrix`
- `V0-GROUP-SERVED-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/feed.py presence --port 11190 --groups fn.matrix`
- `V0-GROUP-SERVED-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/feed.py presence --port 11191 --groups fn.matrix`
- `V0-GROUP-RETIRE-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml group retire fn.matri...`
- `V0-GROUP-RETIRE-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml group retire fn.matri...`
- `V0-GROUP-UNKNOWN-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml group retire fn.not.s...`
- `V0-GROUP-UNKNOWN-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml group retire fn.not.s...`
- `V0-CAP-SET-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/capacity/fn.toml capacity 64`
- `V0-CAP-SET-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/b/capacity/fn.toml capacity 64`
- `V0-CAP-REFUSE-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/capacity/fn.toml post --message-id...`
- `V0-CAP-REFUSE-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/b/capacity/fn.toml post --message-id...`
- `V0-PEER-ADD-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml peer add b b.gate.exa...`
- `V0-PEER-ADD-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml peer add a a.gate.exa...`
- `V0-PEER-LIST-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml peer list`
- `V0-PEER-LIST-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml peer list`
- `V0-PEER-ABSENT`: `(none)`
- `V0-PEER-REMOVE`: `(none)`
- `V0-CFG-LIVE`: `(none)`
- `V0-CFG-LIVE-REFUSE`: `(none)`
- `V0-AUTH-NEW`: `packaging/fn-native operator CONFIG principal new --seed FILE`
- `V0-AUTH-PASSWORD-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; timeout 120 env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml principal...`
- `V0-AUTH-PASSWORD-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; timeout 120 env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml principal...`
- `V0-AUTH-LIST-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml principal list`
- `V0-AUTH-LIST-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml principal list`
- `V0-AUTH-ADVERTISED-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-ADVERTISED-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
- `V0-AUTH-GATED-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py auth --port 11292 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret --msgid '<auth-gate-a@example.invalid>'`
- `V0-AUTH-GATED-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py auth --port 11293 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret --msgid '<auth-gate-b@example.invalid>'`
- `V0-AUTH-LOGIN-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-LOGIN-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
- `V0-AUTH-WITHDRAWN-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-WITHDRAWN-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
- `V0-AUTH-POST-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-POST-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
- `V0-AUTH-WRONG-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-WRONG-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
- `V0-POST-OPEN-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --user '' --secret ''`
- `V0-POST-OPEN-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --user '' --secret ''`
- `V0-POST-COMMIT-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --user '' --secret ''`
- `V0-POST-COMMIT-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --user '' --secret ''`
- `V0-POST-READBACK-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --user '' --secret ''`
- `V0-POST-READBACK-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --user '' --secret ''`
- `V0-POST-FRESH-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --user '' --secret ''`
- `V0-POST-FRESH-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --user '' --secret ''`
- `V0-POST-DUPLICATE-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --user '' --secret ''`
- `V0-POST-DUPLICATE-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --user '' --secret ''`
- `V0-POST-CLOCK-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --user '' --secret ''`
- `V0-POST-CLOCK-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --user '' --secret ''`
- `V0-POST-FROM-MAILBOX-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --user '' --secret ''`
- `V0-POST-FROM-MAILBOX-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --user '' --secret ''`
- `V0-POST-CONCURRENT`: `(none)`
- `V0-READ-CAPABILITIES-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-CAPABILITIES-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-MODE-READER-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-MODE-READER-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-WILDMAT-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-WILDMAT-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-OVERVIEW-FMT-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-OVERVIEW-FMT-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-TIMES-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-TIMES-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-HEADERS-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-HEADERS-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-GROUP-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-GROUP-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LISTGROUP-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LISTGROUP-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HEAD-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HEAD-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-BODY-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-BODY-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-STAT-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-STAT-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-MSGID-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-MSGID-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-ABSENT-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-ABSENT-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-RANGE-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-RANGE-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HDR-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HDR-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XOVER-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XOVER-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XHDR-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XHDR-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XPAT-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XPAT-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEXT-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEXT-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LAST-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LAST-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-STAMP-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-STAMP-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-FUTURE-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-FUTURE-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-SYNTAX-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-SYNTAX-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-DATE-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-DATE-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HELP-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HELP-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-UNKNOWN-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-UNKNOWN-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-FRAMING-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-FRAMING-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-PIN-DISPATCHED-A`: `(none)`
- `V0-PIN-DISPATCHED-B`: `(none)`
- `V0-PIN-ADVERTISED-A`: `(none)`
- `V0-PIN-ADVERTISED-B`: `(none)`
- `V0-TRANSIT-IDENTITY-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml policy set path-ident...`
- `V0-TRANSIT-IDENTITY-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml policy set path-ident...`
- `V0-TRANSIT-INDEPENDENT-A`: `(none)`
- `V0-TRANSIT-INDEPENDENT-B`: `(none)`
- `V0-TRANSIT-MODE-STREAM-AB`: `(none)`
- `V0-TRANSIT-MODE-STREAM-BA`: `(none)`
- `V0-TRANSIT-OFFER-AB`: `(none)`
- `V0-TRANSIT-OFFER-BA`: `(none)`
- `V0-TRANSIT-TRANSFER-AB`: `(none)`
- `V0-TRANSIT-TRANSFER-BA`: `(none)`
- `V0-TRANSIT-IDENTICAL-AB`: `(none)`
- `V0-TRANSIT-IDENTICAL-BA`: `(none)`
- `V0-TRANSIT-DUPLICATE-AB`: `(none)`
- `V0-TRANSIT-DUPLICATE-BA`: `(none)`
- `V0-TRANSIT-LOOP-AB`: `(none)`
- `V0-TRANSIT-LOOP-BA`: `(none)`
- `V0-TRANSIT-LOOP-ABSENT-AB`: `(none)`
- `V0-TRANSIT-LOOP-ABSENT-BA`: `(none)`
- `V0-TRANSIT-CHECK-FRESH-AB`: `(none)`
- `V0-TRANSIT-CHECK-FRESH-BA`: `(none)`
- `V0-TRANSIT-TAKETHIS-AB`: `(none)`
- `V0-TRANSIT-TAKETHIS-BA`: `(none)`
- `V0-TRANSIT-CHECK-DUP-AB`: `(none)`
- `V0-TRANSIT-CHECK-DUP-BA`: `(none)`
- `V0-TRANSIT-TAKETHIS-DUP-AB`: `(none)`
- `V0-TRANSIT-TAKETHIS-DUP-BA`: `(none)`
- `V0-TRANSIT-TLS-AB`: `(none)`
- `V0-TRANSIT-TLS-BA`: `(none)`
- `V0-TRANSIT-AUTHINFO-AB`: `(none)`
- `V0-TRANSIT-AUTHINFO-BA`: `(none)`
- `V0-TRANSIT-TLS-WRONG-ANCHOR`: `(none)`
- `V0-TRANSIT-AUTHINFO-WRONG`: `(none)`
- `V0-FEED-QUEUE`: `(none)`
- `V0-FEED-OFFER`: `(none)`
- `V0-FEED-ONCE`: `(none)`
- `V0-FEED-JOURNAL`: `(none)`
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
- `V0-INN-FEED-OUT`: `(none)`
- `V0-INN-FEED-IN`: `(none)`
- `V0-INN-DUPLICATE-INN`: `(none)`
- `V0-INN-DUPLICATE-FN`: `(none)`
- `V0-INN-LOOP-INN`: `(none)`
- `V0-INN-LOOP-FN`: `(none)`
- `V0-INN-RESTART`: `(none)`
- `V0-INN-SERVING-AGENT`: `(none)`
- `V0-INN-OPERATOR-POST`: `(none)`
- `V0-CLIENT-NNTPLIB-A`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3.12 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/independent.py --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>' --user '' --secret ''`
- `V0-CLIENT-NNTPLIB-B`: `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3.12 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/independent.py --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>' --user '' --secret ''`
- `V0-CLIENT-SLRN`: `slrn -h <host> -p <port>`

## Every command

| # | step | rc | first line | s |
| --- | --- | --- | --- | --- |
| 1 | preflight | 0 | `os=Ubuntu 24.10 kernel=Linux 6.11.0-29-generic arch=x86_64 cores=24` | 0.4 |
| 2 | acquire deploy lock | 0 | `` | 0.3 |
| 3 | ship archive | 0 | `` | 19.8 |
| 4 | make run dir | 0 | `` | 0.2 |
| 5 | install drive.py | 0 | `` | 0.3 |
| 6 | install feed.py | 0 | `` | 0.2 |
| 7 | install matrix.py | 0 | `` | 0.3 |
| 8 | native packaged operator subject | 0 | `NATIVE-LAUNCHER-DIGEST ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142` | 0.5 |
| 9 | node A native run directory | 0 | `` | 0.2 |
| 10 | node A native config exists | 0 | `` | 0.3 |
| 11 | node A native operator status | 0 | `transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment` | 0.3 |
| 12 | node B native run directory | 0 | `` | 0.3 |
| 13 | node B native config exists | 0 | `` | 0.2 |
| 14 | node B native operator status | 0 | `transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment` | 0.4 |
| 15 | loopback refusal: scratch store | 0 | `initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/loopback/store` | 0.3 |
| 16 | loopback refusal: run | 5 | `usage operator request (CONFIGURATION INVALID)` | 0.3 |
| 17 | node A profile scratch store | 0 | `initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/a/profile/store` | 0.4 |
| 18 | node A profile agent refusal | 5 | `usage operator run (UNSUPPORTED-PROFILE agent)` | 0.3 |
| 19 | start server (node A profile owner, profile-a) | 0 | `LISTENING 11297` | 1.3 |
| 20 | install profile.article | 0 | `` | 0.2 |
| 21 | node A profile post | 0 | `accepted operator post ACCEPTED` | 0.4 |
| 22 | stop server profile-a | 0 | `stopped` | 1.2 |
| 23 | node A profile service log | 0 | `accepted post path=control message-id=<profile-a@example.invalid> time=2026-09-25T20:03:25Z` | 0.3 |
| 24 | node A init scratch configuration | 0 | `MATRIX-CONFIG-STORE /home/hbox/fn-deploy/native-e747dbcc-d78ee77/a/init/store` | 0.2 |
| 25 | node A operator init | 0 | `initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/a/init/store` | 0.4 |
| 26 | start server (node A init owner, init-a) | 0 | `LISTENING 11295` | 1.3 |
| 27 | install init.article | 0 | `` | 0.2 |
| 28 | node A submission to the init scratch owner | 3 | `uncertain operator post UNCERTAIN` | 0.3 |
| 29 | stop server init-a | 0 | `stopped` | 0.2 |
| 30 | node A recover the init scratch store | 0 | `recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none` | 0.4 |
| 31 | node A second operator init | 1 | `refused operator init STORE-EXISTS` | 0.3 |
| 32 | node A recover after the second init | 0 | `recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none` | 0.4 |
| 33 | node B init scratch configuration | 0 | `MATRIX-CONFIG-STORE /home/hbox/fn-deploy/native-e747dbcc-d78ee77/b/init/store` | 0.2 |
| 34 | node B operator init | 0 | `initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/b/init/store` | 0.3 |
| 35 | start server (node B init owner, init-b) | 0 | `LISTENING 11296` | 1.4 |
| 36 | install init.article | 0 | `` | 0.2 |
| 37 | node B submission to the init scratch owner | 3 | `uncertain operator post UNCERTAIN` | 0.4 |
| 38 | stop server init-b | 0 | `stopped` | 0.2 |
| 39 | node B recover the init scratch store | 0 | `recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none` | 0.3 |
| 40 | node B second operator init | 1 | `refused operator init STORE-EXISTS` | 0.4 |
| 41 | node B recover after the second init | 0 | `recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none` | 0.3 |
| 42 | node A group create fn.matrix | 0 | `configured generation=2 record=00000002.cfg verification=VERIFIED` | 0.6 |
| 43 | node A group create fn.matrix.throwaway | 0 | `configured generation=3 record=00000003.cfg verification=VERIFIED` | 0.5 |
| 44 | node A group retire fn.matrix.throwaway | 0 | `configured generation=4 record=00000004.cfg verification=VERIFIED` | 0.5 |
| 45 | node A group retire an unserved group | 1 | `refused operator group administrative configuration refused: NO-SUCH-GROUP` | 0.3 |
| 46 | node A capacity scratch store | 0 | `initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/a/capacity/store` | 0.4 |
| 47 | node A capacity 64 | 0 | `configured generation=2 record=00000002.cfg verification=VERIFIED` | 0.3 |
| 48 | node A capacity 1 | 0 | `configured generation=3 record=00000003.cfg verification=VERIFIED` | 0.4 |
| 49 | node A capacity owner config | 0 | `` | 0.3 |
| 50 | start server (node A capacity owner, capacity-a) | 0 | `LISTENING 11290` | 1.2 |
| 51 | install capacity.article | 0 | `` | 0.3 |
| 52 | node A post beyond the capacity | 1 | `refused operator post REFUSED` | 0.3 |
| 53 | stop server capacity-a | 0 | `stopped` | 1.3 |
| 54 | native AUTHINFO secret | 0 | `SECRET-READY` | 0.2 |
| 55 | node A principal set-password matrix | 0 | `Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.4 |
| 56 | node A principal list | 0 | `matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.4 |
| 57 | node A auth-required scratch store | 0 | `initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/a/authgate/store` | 0.4 |
| 58 | node A auth-required scratch credential | 0 | `Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.3 |
| 59 | start server (node A auth-required owner, authgate-a) | 0 | `LISTENING 11292` | 1.3 |
| 60 | node A auth-required AUTHINFO gate | 0 | `{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "OVER", "HDR", "XPAT", "NEWNEWS", "LIST", "IMPLEMENTATION", "AUTHINFO"], "AUTHINFO ADVERTISED": true, ` | 0.3 |
| 61 | stop server authgate-a | 0 | `stopped` | 1.3 |
| 62 | node B group create fn.matrix | 0 | `configured generation=2 record=00000002.cfg verification=VERIFIED` | 0.5 |
| 63 | node B group create fn.matrix.throwaway | 0 | `configured generation=3 record=00000003.cfg verification=VERIFIED` | 0.5 |
| 64 | node B group retire fn.matrix.throwaway | 0 | `configured generation=4 record=00000004.cfg verification=VERIFIED` | 0.4 |
| 65 | node B group retire an unserved group | 1 | `refused operator group administrative configuration refused: NO-SUCH-GROUP` | 0.4 |
| 66 | node B capacity scratch store | 0 | `initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/b/capacity/store` | 0.5 |
| 67 | node B capacity 64 | 0 | `configured generation=2 record=00000002.cfg verification=VERIFIED` | 0.4 |
| 68 | node B capacity 1 | 0 | `configured generation=3 record=00000003.cfg verification=VERIFIED` | 0.4 |
| 69 | node B capacity owner config | 0 | `` | 0.3 |
| 70 | start server (node B capacity owner, capacity-b) | 0 | `LISTENING 11291` | 1.3 |
| 71 | install capacity.article | 0 | `` | 0.2 |
| 72 | node B post beyond the capacity | 1 | `refused operator post REFUSED` | 0.4 |
| 73 | stop server capacity-b | 0 | `stopped` | 1.2 |
| 74 | node B principal set-password matrix | 0 | `Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.5 |
| 75 | node B principal list | 0 | `matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.3 |
| 76 | node B auth-required scratch store | 0 | `initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/b/authgate/store` | 0.4 |
| 77 | node B auth-required scratch credential | 0 | `Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.3 |
| 78 | start server (node B auth-required owner, authgate-b) | 0 | `LISTENING 11293` | 1.3 |
| 79 | node B auth-required AUTHINFO gate | 0 | `{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "OVER", "HDR", "XPAT", "NEWNEWS", "LIST", "IMPLEMENTATION", "AUTHINFO"], "AUTHINFO ADVERTISED": true, ` | 0.3 |
| 80 | stop server authgate-b | 0 | `stopped` | 1.3 |
| 81 | node A path-identity | 0 | `configured generation=5 record=00000005.cfg verification=VERIFIED` | 0.3 |
| 82 | node B path-identity | 0 | `configured generation=5 record=00000005.cfg verification=VERIFIED` | 0.4 |
| 83 | node B configured port | 0 | `11191` | 0.3 |
| 84 | node A peer record for B | 0 | `configured generation=6 record=00000006.cfg verification=VERIFIED` | 0.4 |
| 85 | node A lists its peers | 0 | `b path-identity=b.gate.example.invalid address=127.0.0.1 port=11191 security=clear inbound=fn.* outbound=- auth=source-address:127.0.0.1` | 0.4 |
| 86 | node A configured port | 0 | `11190` | 0.3 |
| 87 | node B peer record for A | 0 | `configured generation=6 record=00000006.cfg verification=VERIFIED` | 0.5 |
| 88 | node B lists its peers | 0 | `a path-identity=a.gate.example.invalid address=127.0.0.1 port=11190 security=clear inbound=fn.* outbound=- auth=source-address:127.0.0.1` | 0.3 |
| 89 | start server (node A (native-operator), a-main) | 0 | `LISTENING 11190` | 1.3 |
| 90 | node A pid | 0 | `3701240` | 0.2 |
| 91 | start server (node B (native-operator), b-main) | 0 | `LISTENING 11191` | 1.3 |
| 92 | node B pid | 0 | `3701366` | 0.2 |
| 93 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 94 | node A serves fn.matrix | 0 | `{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}` | 0.3 |
| 95 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 96 | node A POST cycle | 0 | `{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-c93` | 0.4 |
| 97 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 98 | node A reader surface | 0 | `{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "XPAT", "NEWNEWS", "LIST A` | 0.8 |
| 99 | node A server is alive | 0 | `ALIVE` | 0.2 |
| 100 | node A AUTHINFO session | 0 | `{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "POST", "OVER", "HDR", "XPAT", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"],` | 0.7 |
| 101 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 102 | install alpha.article | 0 | `` | 0.2 |
| 103 | node A outcome accepted | 0 | `accepted operator post ACCEPTED` | 0.5 |
| 104 | install alpha.article | 0 | `` | 0.3 |
| 105 | node A outcome duplicate | 0 | `accepted operator post DUPLICATE` | 0.3 |
| 106 | install alpha-conflict.article | 0 | `` | 0.3 |
| 107 | node A outcome refused | 1 | `refused operator post REFUSED` | 0.3 |
| 108 | install stream-a.article | 0 | `` | 0.2 |
| 109 | node A seed <stream-a@example.invalid> | 0 | `accepted operator post ACCEPTED` | 0.6 |
| 110 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 111 | node B serves fn.matrix | 0 | `{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}` | 0.3 |
| 112 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 113 | node B POST cycle | 0 | `{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-38a` | 0.7 |
| 114 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 115 | node B reader surface | 0 | `{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "XPAT", "NEWNEWS", "LIST A` | 0.7 |
| 116 | node B server is alive | 0 | `ALIVE` | 0.2 |
| 117 | node B AUTHINFO session | 0 | `{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "POST", "OVER", "HDR", "XPAT", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"],` | 0.4 |
| 118 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 119 | install beta.article | 0 | `` | 0.2 |
| 120 | node B outcome accepted | 0 | `accepted operator post ACCEPTED` | 0.5 |
| 121 | install beta.article | 0 | `` | 0.3 |
| 122 | node B outcome duplicate | 0 | `accepted operator post DUPLICATE` | 0.3 |
| 123 | install beta-conflict.article | 0 | `` | 0.3 |
| 124 | node B outcome refused | 1 | `refused operator post REFUSED` | 0.3 |
| 125 | install stream-b.article | 0 | `` | 0.3 |
| 126 | node B seed <stream-b@example.invalid> | 0 | `accepted operator post ACCEPTED` | 0.6 |
| 127 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 128 | node B server is alive | 0 | `ALIVE` | 0.2 |
| 129 | nntplib interpreter | 0 | `USE python3.12` | 0.3 |
| 130 | install independent.py | 0 | `` | 0.2 |
| 131 | independent nntplib client on node A | 0 | `/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/independent.py:6: DeprecationWarning: 'nntplib' is deprecated and slated for removal in Python 3.13` | 0.3 |
| 132 | independent nntplib client on node B | 0 | `/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/independent.py:6: DeprecationWarning: 'nntplib' is deprecated and slated for removal in Python 3.13` | 0.3 |
| 133 | install .newsrc | 1 FAIL | `bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory` | 0.3 |
| 134 | stop server node A (main) | 0 | `stopped` | 1.4 |
| 135 | stop the tap in front of node A | 0 | `stopped` | 0.2 |
| 136 | stop server node B (main) | 0 | `stopped` | 1.2 |
| 137 | stop the tap in front of node B | 0 | `stopped` | 0.3 |
| 138 | stray fn processes | 0 | `CLEAN` | 0.3 |
| 139 | release deploy lock | 0 | `` | 0.2 |

### Commands in full

1. **preflight** -- `. /etc/os-release 2>/dev/null || true ; echo "os=${PRETTY_NAME:-unknown} kernel=$(uname -sr) arch=$(uname -m) cores=$(nproc 2>/dev/null || echo ?)" ; echo "python3=$(python3 -V 2>&1)" ; for p in python3.9 python3.10 python3.11 python3.12; do ; command -v $p >/dev/null && echo "alt=$p $($p -V 2>&1)" ; done ; for c in slrn tin nn trn inews expect script; do ; printf 'client %s=%s\n' "$c" "$(comma...`
2. **acquire deploy lock** -- `mkdir -p $HOME/fn-deploy/.locks ; if ! mkdir $HOME/fn-deploy/.locks/native-e747dbcc-d78ee77.lock 2>/dev/null; then ; echo "deploy identity is already active: native-e747dbcc-d78ee77" ; exit 73 ; fi`
3. **ship archive** -- `git archive d78ee77 | tar -x -C $HOME/fn-deploy/native-e747dbcc-d78ee77`
4. **make run dir** -- `mkdir -p $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run`
5. **install drive.py** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/drive.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJJbmRlcGVuZGVudCBOTlRQIGRyaXZpbmcgZm9yIHRo ; ZSBkZXBsb3kgZ2F0ZTsgbm8gZm4gbW9kdWxlIGlzIGltcG9ydGVkLiIiIgppbXBvcnQgYXJncGFy ; c2UsIGpzb24sIG9zLCBzb2NrZXQsIHN5cywgdGltZQoKCmNsYXNzIENvbm46CiAgICBkZWYgX19p ; bml0X18oc2VsZiwgcG9ydCwgdGltZW91dD0zMCk6CiAgICAgICAgc2VsZi5zb2NrID0gc29j...`
6. **install feed.py** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/feed.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJUaGUgdHdvLW5vZGUgcGhhc2VzLiAgTm8gZm4gbW9k ; dWxlIGlzIGltcG9ydGVkOyBDb25uIGlzIGRlcGxveV9nYXRlJ3MuCgpgcHJlc2VuY2VgIGlzIHRo ; ZSBjb250cm9sIGFuZCB0aGUgcmVyZWFkOiB3aGF0IGEgbm9kZSBob2xkcyBhbmQgd2hhdCBpdCBt ; dXN0Cm5vdC4gIGByZWxheWAgaXMgUkZDIDM5NzcgNi4zLjIgZHJpdmVuIGJ5IGhhbmQgb3Zlc...`
7. **install matrix.py** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJUaGUgdjAgbWF0cml4J3Mgb3duIE5OVFAgcGhhc2Vz ; LiAgTm8gZm4gbW9kdWxlIGlzIGltcG9ydGVkOyBDb25uIGlzCnRvb2xzL2RlcGxveV9nYXRlLnB5 ; J3MgZHJpdmVyLCBzaGlwcGVkIGJlc2lkZSB0aGlzIGZpbGUgYXMgZHJpdmUucHkuCgpFdmVyeSBw ; aGFzZSBwcmludHMgT05FIGpzb24gb2JqZWN0IHdob3NlIGtleXMgYXJlIGNvbW1hbmQgbmF...`
8. **native packaged operator subject** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; image=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host ; wrapper=packaging/fn-native ; runtime=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/runtime/sbcl ; test -x "$image" || { echo "NATIVE-IMAGE-MISSING $image"; exit 4; } ; test -x "$wrapper" ...`
9. **node A native run directory** -- `mkdir -p $HOME/fn-deploy/native-e747dbcc-d78ee77/a`
10. **node A native config exists** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; test -f /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml`
11. **node A native operator status** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml status`
12. **node B native run directory** -- `mkdir -p $HOME/fn-deploy/native-e747dbcc-d78ee77/b`
13. **node B native config exists** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; test -f /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml`
14. **node B native operator status** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml status`
15. **loopback refusal: scratch store** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; mkdir -p $HOME/fn-deploy/native-e747dbcc-d78ee77/loopback && env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native store $HOME/fn-deploy/na...`
16. **loopback refusal: run** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; timeout 60 env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/loopback/fn.toml run`
17. **node A profile scratch store** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; mkdir -p $HOME/fn-deploy/native-e747dbcc-d78ee77/a/profile && rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/profile/service.log && env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0...`
18. **node A profile agent refusal** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; timeout 60 env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/profile/agent.toml run`
19. **start server (node A profile owner, profile-a)** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/profile/server-profile-a.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native ...`
20. **install profile.article** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/a/profile/profile.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IHByb2ZpbGUNCk5ld3Nncm91cHM6 ; IGZuLmxldHRlcnMNCkRhdGU6IEZyaSwgMjUgU2VwIDIwMjYgMjA6MDM6MjUgKzAwMDANCk1lc3Nh ; Z2UtSUQ6IDxwcm9maWxlLWFAZXhhbXBsZS5pbnZhbGlkPg0KDQpUaGUgb3BlcmF0b3IgbG9nIGxp ; bmUgZm9yIHRoaXMgcG9zdC4NCg== ; FN_GATE_EOF ; chmod 644 $HOME/fn-...`
21. **node A profile post** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/profile/fn.toml post --message-id ...`
22. **stop server profile-a** -- `if [ -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/profile/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-e747dbcc-d78ee77/a/profile/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/profile/server.pid ; fi ; echo stopped`
23. **node A profile service log** -- `cat $HOME/fn-deploy/native-e747dbcc-d78ee77/a/profile/service.log 2>/dev/null || echo NO-LOG-FILE`
24. **node A init scratch configuration** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; mkdir -p $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init && printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = 11295\n[control]\npath = "%s"\n' "$HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/store" "$HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/control.sock" > $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/fn.toml && prin...`
25. **node A operator init** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/fn.toml init fn.letters`
26. **start server (node A init owner, init-a)** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/server-init-a.log ; nohup env FN_NATIVE_CONTROL_FAULT=postpublish FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e...`
27. **install init.article** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/init.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG9uZSBkdXJhYmxlIG91dGNvbWUN ; Ck5ld3Nncm91cHM6IGZuLmxldHRlcnMNCkRhdGU6IEZyaSwgMjUgU2VwIDIwMjYgMjA6MDM6Mjkg ; KzAwMDANCk1lc3NhZ2UtSUQ6IDxpbml0LWFAZXhhbXBsZS5pbnZhbGlkPg0KDQpTdWJtaXR0ZWQg ; b24gdGhlIEEgaW5pdCBzY3JhdGNoIG5vZGUgYnkgdGhlIHYwIG1hdHJpeC4NCg== ; FN_...`
28. **node A submission to the init scratch owner** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/fn.toml post --message-id '<i...`
29. **stop server init-a** -- `if [ -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/server.pid ; fi ; echo stopped`
30. **node A recover the init scratch store** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/fn.toml recover`
31. **node A second operator init** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/fn.toml init fn.letters`
32. **node A recover after the second init** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/init/fn.toml recover`
33. **node B init scratch configuration** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; mkdir -p $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init && printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = 11296\n[control]\npath = "%s"\n' "$HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/store" "$HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/control.sock" > $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/fn.toml && prin...`
34. **node B operator init** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/fn.toml init fn.letters`
35. **start server (node B init owner, init-b)** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/server-init-b.log ; nohup env FN_NATIVE_CONTROL_FAULT=postpublish FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e...`
36. **install init.article** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/init.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG9uZSBkdXJhYmxlIG91dGNvbWUN ; Ck5ld3Nncm91cHM6IGZuLmxldHRlcnMNCkRhdGU6IEZyaSwgMjUgU2VwIDIwMjYgMjA6MDM6MzMg ; KzAwMDANCk1lc3NhZ2UtSUQ6IDxpbml0LWJAZXhhbXBsZS5pbnZhbGlkPg0KDQpTdWJtaXR0ZWQg ; b24gdGhlIEIgaW5pdCBzY3JhdGNoIG5vZGUgYnkgdGhlIHYwIG1hdHJpeC4NCg== ; FN_...`
37. **node B submission to the init scratch owner** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/fn.toml post --message-id '<i...`
38. **stop server init-b** -- `if [ -f $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/server.pid ; fi ; echo stopped`
39. **node B recover the init scratch store** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/fn.toml recover`
40. **node B second operator init** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/fn.toml init fn.letters`
41. **node B recover after the second init** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/b/init/fn.toml recover`
42. **node A group create fn.matrix** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml group create fn.matrix`
43. **node A group create fn.matrix.throwaway** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml group create fn.matri...`
44. **node A group retire fn.matrix.throwaway** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml group retire fn.matri...`
45. **node A group retire an unserved group** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml group retire fn.not.s...`
46. **node A capacity scratch store** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; mkdir -p $HOME/fn-deploy/native-e747dbcc-d78ee77/a/capacity && env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native store $HOME/fn-deploy/...`
47. **node A capacity 64** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/capacity/fn.toml capacity 64`
48. **node A capacity 1** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/capacity/fn.toml capacity 1`
49. **node A capacity owner config** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; printf '[listener]\nhost = "127.0.0.1"\nport = 11290\n[control]\npath = "%s"\n' $HOME/fn-deploy/native-e747dbcc-d78ee77/a/capacity/control.sock >> $HOME/fn-deploy/native-e747dbcc-d78ee77/a/capacity/fn.toml`
50. **start server (node A capacity owner, capacity-a)** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/capacity/server-capacity-a.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-nativ...`
51. **install capacity.article** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/a/capacity/capacity.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG92ZXIgdGhlIGNhcGFjaXR5DQpO ; ZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBGcmksIDI1IFNlcCAyMDI2IDIwOjAzOjM5ICsw ; MDAwDQpNZXNzYWdlLUlEOiA8Y2FwYWNpdHktYUBleGFtcGxlLmludmFsaWQ+DQoNCnh4eHh4eHh4 ; eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eH...`
52. **node A post beyond the capacity** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/capacity/fn.toml post --message-id...`
53. **stop server capacity-a** -- `if [ -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/capacity/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-e747dbcc-d78ee77/a/capacity/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/capacity/server.pid ; fi ; echo stopped`
54. **native AUTHINFO secret** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; umask 077 && od -An -tx1 -N16 /dev/urandom | tr -d ' \n' > $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret && printf '%s\n%s\n' "$(cat $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret)" "$(cat $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret)" > $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secre...`
55. **node A principal set-password matrix** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; timeout 120 env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml principal...`
56. **node A principal list** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml principal list`
57. **node A auth-required scratch store** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; mkdir -p $HOME/fn-deploy/native-e747dbcc-d78ee77/a/authgate && env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native store $HOME/fn-deploy/...`
58. **node A auth-required scratch credential** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; timeout 120 env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/a/authgate/fn.toml princ...`
59. **start server (node A auth-required owner, authgate-a)** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/authgate/server-authgate-a.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-nativ...`
60. **node A auth-required AUTHINFO gate** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py auth --port 11292 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret --msgid '<auth-gate-a@example.invalid>'`
61. **stop server authgate-a** -- `if [ -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/authgate/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-e747dbcc-d78ee77/a/authgate/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/authgate/server.pid ; fi ; echo stopped`
62. **node B group create fn.matrix** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml group create fn.matrix`
63. **node B group create fn.matrix.throwaway** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml group create fn.matri...`
64. **node B group retire fn.matrix.throwaway** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml group retire fn.matri...`
65. **node B group retire an unserved group** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml group retire fn.not.s...`
66. **node B capacity scratch store** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; mkdir -p $HOME/fn-deploy/native-e747dbcc-d78ee77/b/capacity && env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native store $HOME/fn-deploy/...`
67. **node B capacity 64** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/b/capacity/fn.toml capacity 64`
68. **node B capacity 1** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/b/capacity/fn.toml capacity 1`
69. **node B capacity owner config** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; printf '[listener]\nhost = "127.0.0.1"\nport = 11291\n[control]\npath = "%s"\n' $HOME/fn-deploy/native-e747dbcc-d78ee77/b/capacity/control.sock >> $HOME/fn-deploy/native-e747dbcc-d78ee77/b/capacity/fn.toml`
70. **start server (node B capacity owner, capacity-b)** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/b/capacity/server-capacity-b.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-nativ...`
71. **install capacity.article** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/b/capacity/capacity.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG92ZXIgdGhlIGNhcGFjaXR5DQpO ; ZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBGcmksIDI1IFNlcCAyMDI2IDIwOjAzOjUwICsw ; MDAwDQpNZXNzYWdlLUlEOiA8Y2FwYWNpdHktYkBleGFtcGxlLmludmFsaWQ+DQoNCnh4eHh4eHh4 ; eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eH...`
72. **node B post beyond the capacity** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/b/capacity/fn.toml post --message-id...`
73. **stop server capacity-b** -- `if [ -f $HOME/fn-deploy/native-e747dbcc-d78ee77/b/capacity/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-e747dbcc-d78ee77/b/capacity/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/b/capacity/server.pid ; fi ; echo stopped`
74. **node B principal set-password matrix** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; timeout 120 env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml principal...`
75. **node B principal list** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml principal list`
76. **node B auth-required scratch store** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; mkdir -p $HOME/fn-deploy/native-e747dbcc-d78ee77/b/authgate && env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native store $HOME/fn-deploy/...`
77. **node B auth-required scratch credential** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; timeout 120 env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator $HOME/fn-deploy/native-e747dbcc-d78ee77/b/authgate/fn.toml princ...`
78. **start server (node B auth-required owner, authgate-b)** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/b/authgate/server-authgate-b.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-nativ...`
79. **node B auth-required AUTHINFO gate** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py auth --port 11293 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret --msgid '<auth-gate-b@example.invalid>'`
80. **stop server authgate-b** -- `if [ -f $HOME/fn-deploy/native-e747dbcc-d78ee77/b/authgate/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-e747dbcc-d78ee77/b/authgate/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/b/authgate/server.pid ; fi ; echo stopped`
81. **node A path-identity** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml policy set path-ident...`
82. **node B path-identity** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml policy set path-ident...`
83. **node B configured port** -- `sed -n 's/^port *= *\([0-9][0-9]*\).*/\1/p' /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml | head -1`
84. **node A peer record for B** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml peer add b b.gate.exa...`
85. **node A lists its peers** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml peer list`
86. **node A configured port** -- `sed -n 's/^port *= *\([0-9][0-9]*\).*/\1/p' /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml | head -1`
87. **node B peer record for A** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml peer add a a.gate.exa...`
88. **node B lists its peers** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml peer list`
89. **start server (node A (native-operator), a-main)** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/server-a-main.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /t...`
90. **node A pid** -- `cat $HOME/fn-deploy/native-e747dbcc-d78ee77/a/server.pid`
91. **start server (node B (native-operator), b-main)** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/b/server-b-main.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /t...`
92. **node B pid** -- `cat $HOME/fn-deploy/native-e747dbcc-d78ee77/b/server.pid`
93. **node A server is alive** -- `kill -0 3701240 2>/dev/null && echo ALIVE || echo DEAD`
94. **node A serves fn.matrix** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/feed.py presence --port 11190 --groups fn.matrix`
95. **node A server is alive** -- `kill -0 3701240 2>/dev/null && echo ALIVE || echo DEAD`
96. **node A POST cycle** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --user '' --secret ''`
97. **node A server is alive** -- `kill -0 3701240 2>/dev/null && echo ALIVE || echo DEAD`
98. **node A reader surface** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>'`
99. **node A server is alive** -- `kill -0 3701240 2>/dev/null && echo ALIVE || echo DEAD`
100. **node A AUTHINFO session** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
101. **node A server is alive** -- `kill -0 3701240 2>/dev/null && echo ALIVE || echo DEAD`
102. **install alpha.article** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/a/alpha.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; QQ0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogRnJpLCAyNSBTZXAgMjAyNiAyMDowNDow ; NiArMDAwMA0KTWVzc2FnZS1JRDogPGFscGhhQGEuZXhhbXBsZS5pbnZhbGlkPg0KDQpXcml0dGVu ; IG9uIG5vZGUgQSBieSB0aGUgdjAgbWF0cml4IHRocm91Z2ggdGhlIG5hdGl2ZSBvcGVyYXRvci...`
103. **node A outcome accepted** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml post --message-id '<a...`
104. **install alpha.article** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/a/alpha.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; QQ0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogRnJpLCAyNSBTZXAgMjAyNiAyMDowNDow ; NiArMDAwMA0KTWVzc2FnZS1JRDogPGFscGhhQGEuZXhhbXBsZS5pbnZhbGlkPg0KDQpXcml0dGVu ; IG9uIG5vZGUgQSBieSB0aGUgdjAgbWF0cml4IHRocm91Z2ggdGhlIG5hdGl2ZSBvcGVyYXRvci...`
105. **node A outcome duplicate** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml post --message-id '<a...`
106. **install alpha-conflict.article** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/a/alpha-conflict.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; QQ0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogRnJpLCAyNSBTZXAgMjAyNiAyMDowNDow ; NiArMDAwMA0KTWVzc2FnZS1JRDogPGFscGhhQGEuZXhhbXBsZS5pbnZhbGlkPg0KDQpXcml0dGVu ; IG9uIG5vZGUgQSBieSB0aGUgdjAgbWF0cml4IHRocm91Z2ggdGhlIG5hdGl2ZSBvc...`
107. **node A outcome refused** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml post --message-id '<a...`
108. **install stream-a.article** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/a/stream-a.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IGZvciB0aGUgc3RyZWFtaW5nIG9m ; ZmVyDQpOZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBGcmksIDI1IFNlcCAyMDI2IDIwOjA0 ; OjA4ICswMDAwDQpNZXNzYWdlLUlEOiA8c3RyZWFtLWFAZXhhbXBsZS5pbnZhbGlkPg0KDQpTZWVk ; ZWQgb24gbm9kZSBBIGJ5IHRoZSB2MCBtYXRyaXguDQo= ; FN_GATE_EOF ; chmod 644 ...`
109. **node A seed <stream-a@example.invalid>** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/a/fn.toml post --message-id '<s...`
110. **node B server is alive** -- `kill -0 3701366 2>/dev/null && echo ALIVE || echo DEAD`
111. **node B serves fn.matrix** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/feed.py presence --port 11191 --groups fn.matrix`
112. **node B server is alive** -- `kill -0 3701366 2>/dev/null && echo ALIVE || echo DEAD`
113. **node B POST cycle** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --user '' --secret ''`
114. **node B server is alive** -- `kill -0 3701366 2>/dev/null && echo ALIVE || echo DEAD`
115. **node B reader surface** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>'`
116. **node B server is alive** -- `kill -0 3701366 2>/dev/null && echo ALIVE || echo DEAD`
117. **node B AUTHINFO session** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
118. **node B server is alive** -- `kill -0 3701366 2>/dev/null && echo ALIVE || echo DEAD`
119. **install beta.article** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/b/beta.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; Qg0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogRnJpLCAyNSBTZXAgMjAyNiAyMDowNDox ; MiArMDAwMA0KTWVzc2FnZS1JRDogPGJldGFAYi5leGFtcGxlLmludmFsaWQ+DQoNCldyaXR0ZW4g ; b24gbm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXggdGhyb3VnaCB0aGUgbmF0aXZlIG9wZXJhdG9yLg0...`
120. **node B outcome accepted** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml post --message-id '<b...`
121. **install beta.article** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/b/beta.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; Qg0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogRnJpLCAyNSBTZXAgMjAyNiAyMDowNDox ; MiArMDAwMA0KTWVzc2FnZS1JRDogPGJldGFAYi5leGFtcGxlLmludmFsaWQ+DQoNCldyaXR0ZW4g ; b24gbm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXggdGhyb3VnaCB0aGUgbmF0aXZlIG9wZXJhdG9yLg0...`
122. **node B outcome duplicate** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml post --message-id '<b...`
123. **install beta-conflict.article** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/b/beta-conflict.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; Qg0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogRnJpLCAyNSBTZXAgMjAyNiAyMDowNDox ; MiArMDAwMA0KTWVzc2FnZS1JRDogPGJldGFAYi5leGFtcGxlLmludmFsaWQ+DQoNCldyaXR0ZW4g ; b24gbm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXggdGhyb3VnaCB0aGUgbmF0aXZlIG9wZX...`
124. **node B outcome refused** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml post --message-id '<b...`
125. **install stream-b.article** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/b/stream-b.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IGZvciB0aGUgc3RyZWFtaW5nIG9m ; ZmVyDQpOZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBGcmksIDI1IFNlcCAyMDI2IDIwOjA0 ; OjE0ICswMDAwDQpNZXNzYWdlLUlEOiA8c3RyZWFtLWJAZXhhbXBsZS5pbnZhbGlkPg0KDQpTZWVk ; ZWQgb24gbm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXguDQo= ; FN_GATE_EOF ; chmod 644 ...`
126. **node B seed <stream-b@example.invalid>** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6/fn-host packaging/fn-native operator /tank/fn/scratch/qual-e747dbcc/matrix/stores/b/fn.toml post --message-id '<s...`
127. **node A server is alive** -- `kill -0 3701240 2>/dev/null && echo ALIVE || echo DEAD`
128. **node B server is alive** -- `kill -0 3701366 2>/dev/null && echo ALIVE || echo DEAD`
129. **nntplib interpreter** -- `for p in python3.12 python3 ; do command -v $p >/dev/null 2>&1 && $p -c 'import nntplib' 2>/dev/null && { echo USE $p; exit 0; }; done; echo NONE`
130. **install independent.py** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/independent.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJBIHN0ZGxpYi1ubnRwbGliIHJlYWRlciBhZ2FpbnN0 ; IGEgbGl2ZSBmbiBub2RlLiAgTm8gZm4gbW9kdWxlIGlzIGltcG9ydGVkLAphbmQgbm8gZnJhbWlu ; ZywgZm9sZGluZyBvciByZXNwb25zZSBwYXJzaW5nIGluIHRoaXMgZmlsZSBpcyBmbidzOiBubnRw ; bGliCmRvZXMgYWxsIG9mIGl0LiAgVGhlIGZpeHR1cmUgaXMgcGFzc2VkIGluLCBzby...`
131. **independent nntplib client on node A** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3.12 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/independent.py --port 11190 --group fn.letters --msgid '<native-matrix-c93c0fc7545f-a@example.invalid>' --absent '<absent@example.invalid>' --user '' --secret ''`
132. **independent nntplib client on node B** -- `cd $HOME/fn-deploy/native-e747dbcc-d78ee77 || exit 9 ; python3.12 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/independent.py --port 11191 --group fn.letters --msgid '<native-matrix-38a65a1b0259-b@example.invalid>' --absent '<absent@example.invalid>' --user '' --secret ''`
133. **install .newsrc** -- `base64 -d > $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc <<'FN_GATE_EOF' ; Zm4ubGV0dGVyczoK ; FN_GATE_EOF ; chmod 644 $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc`
134. **stop server node A (main)** -- `if [ -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-e747dbcc-d78ee77/a/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/server.pid ; fi ; echo stopped`
135. **stop the tap in front of node A** -- `if [ -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/tap.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-e747dbcc-d78ee77/a/tap.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 10); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/a/tap.pid ; fi ; echo stopped`
136. **stop server node B (main)** -- `if [ -f $HOME/fn-deploy/native-e747dbcc-d78ee77/b/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-e747dbcc-d78ee77/b/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/b/server.pid ; fi ; echo stopped`
137. **stop the tap in front of node B** -- `if [ -f $HOME/fn-deploy/native-e747dbcc-d78ee77/b/tap.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-e747dbcc-d78ee77/b/tap.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 10); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-e747dbcc-d78ee77/b/tap.pid ; fi ; echo stopped`
138. **stray fn processes** -- `pgrep -f 'fn-deploy/native-e747dbcc-d78ee77' >/dev/null 2>&1 && echo STRAY || echo CLEAN`
139. **release deploy lock** -- `rmdir $HOME/fn-deploy/.locks/native-e747dbcc-d78ee77.lock`

## Findings

One row per stated assertion. `held` and `violated` are the two that
DECIDE it; `inconclusive` means this run could not decide it and so
establishes nothing; `not-exercised` and `not-built` mean it was not
reached and why; `limitation` is a scope boundary no run of this
harness crosses.

The process exit is 1 for a violation, 3 for an inconclusive run with no violation, 2 when the gate stopped early, 0 otherwise.

Verdict of this run: **violated** (1 limitation).

| assertion | verdict | what it says |
| --- | --- | --- |
| the-gate-stopped-early-could-not-install-home-fn-deploy-native-e747dbcc-d78ee77- | limitation | the gate stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne |

## What was NOT exercised

- the gate stopped early: could not install $HOME/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.ne

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
os=Ubuntu 24.10 kernel=Linux 6.11.0-29-generic arch=x86_64 cores=24
python3=Python 3.12.7
alt=python3.12 Python 3.12.7
client slrn=ABSENT
client tin=/home/hbox/.cargo/bin/tin
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
NATIVE-IMAGE-DIGEST 432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505
NATIVE-RUNTIME-DIGEST b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5
NATIVE-CORE-DIGEST 0c96e554fae5ed7345b6ac2be89a9975430e879afae0ba5ccb072720dbd38d08
usage: fn operator CONFIG run [--once]
accepted operator help
--- 9 node A native run directory (rc=0)
--- 10 node A native config exists (rc=0)
--- 11 node A native operator status (rc=0)
transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment
profile format=8 max-transactions=128 max-history-octets=25165824 max-record-octets=17138486 max-article-octets=32768 max-groups-per-article=65535 max-group-name-octets=256 max-open-suffix=128 max-consumers=1048576 max-bp-rows=1048576 max-config-generations=1048576 max-credentials=1048576 max-policy-members=1048576 history-marker=0
headroom transactions-used=0 transactions-budget=128 bytes-used=0 history-bound=25165824 charge-reserved=0 charge-capacity=1048576
open=full-replay reason=absent
pins=0 reserved=0 connections=0
accepted operator status
--- 12 node B native run directory (rc=0)
--- 13 node B native config exists (rc=0)
--- 14 node B native operator status (rc=0)
transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment
profile format=8 max-transactions=128 max-history-octets=25165824 max-record-octets=17138486 max-article-octets=32768 max-groups-per-article=65535 max-group-name-octets=256 max-open-suffix=128 max-consumers=1048576 max-bp-rows=1048576 max-config-generations=1048576 max-credentials=1048576 max-policy-members=1048576 history-marker=0
headroom transactions-used=0 transactions-budget=128 bytes-used=0 history-bound=25165824 charge-reserved=0 charge-capacity=1048576
open=full-replay reason=absent
pins=0 reserved=0 connections=0
accepted operator status
--- 15 loopback refusal: scratch store (rc=0)
initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/loopback/store
--- 16 loopback refusal: run (rc=5)
usage operator request (CONFIGURATION INVALID)
--- 17 node A profile scratch store (rc=0)
initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/a/profile/store
--- 18 node A profile agent refusal (rc=5)
usage operator run (UNSUPPORTED-PROFILE agent)
--- 19 start server (node A profile owner, profile-a) (rc=0)
LISTENING 11297
--- 20 install profile.article (rc=0)
--- 21 node A profile post (rc=0)
accepted operator post ACCEPTED
--- 22 stop server profile-a (rc=0)
stopped
--- 23 node A profile service log (rc=0)
accepted post path=control message-id=<profile-a@example.invalid> time=2026-09-25T20:03:25Z
--- 24 node A init scratch configuration (rc=0)
MATRIX-CONFIG-STORE /home/hbox/fn-deploy/native-e747dbcc-d78ee77/a/init/store
--- 25 node A operator init (rc=0)
initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/a/init/store
accepted operator init
--- 26 start server (node A init owner, init-a) (rc=0)
LISTENING 11295
--- 27 install init.article (rc=0)
--- 28 node A submission to the init scratch owner (rc=3)
uncertain operator post UNCERTAIN
--- 29 stop server init-a (rc=0)
stopped
--- 30 node A recover the init scratch store (rc=0)
recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none
open=full-replay reason=absent
accepted operator recover
--- 31 node A second operator init (rc=1)
refused operator init STORE-EXISTS
--- 32 node A recover after the second init (rc=0)
recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none
open=full-replay reason=absent
accepted operator recover
--- 33 node B init scratch configuration (rc=0)
MATRIX-CONFIG-STORE /home/hbox/fn-deploy/native-e747dbcc-d78ee77/b/init/store
--- 34 node B operator init (rc=0)
initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/b/init/store
accepted operator init
--- 35 start server (node B init owner, init-b) (rc=0)
LISTENING 11296
--- 36 install init.article (rc=0)
--- 37 node B submission to the init scratch owner (rc=3)
uncertain operator post UNCERTAIN
--- 38 stop server init-b (rc=0)
stopped
--- 39 node B recover the init scratch store (rc=0)
recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none
open=full-replay reason=absent
accepted operator recover
--- 40 node B second operator init (rc=1)
refused operator init STORE-EXISTS
--- 41 node B recover after the second init (rc=0)
recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none
open=full-replay reason=absent
accepted operator recover
--- 42 node A group create fn.matrix (rc=0)
configured generation=2 record=00000002.cfg verification=VERIFIED
accepted operator group
--- 43 node A group create fn.matrix.throwaway (rc=0)
configured generation=3 record=00000003.cfg verification=VERIFIED
accepted operator group
--- 44 node A group retire fn.matrix.throwaway (rc=0)
configured generation=4 record=00000004.cfg verification=VERIFIED
accepted operator group
--- 45 node A group retire an unserved group (rc=1)
refused operator group administrative configuration refused: NO-SUCH-GROUP
--- 46 node A capacity scratch store (rc=0)
initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/a/capacity/store
--- 47 node A capacity 64 (rc=0)
configured generation=2 record=00000002.cfg verification=VERIFIED
accepted operator capacity
--- 48 node A capacity 1 (rc=0)
configured generation=3 record=00000003.cfg verification=VERIFIED
accepted operator capacity
--- 49 node A capacity owner config (rc=0)
--- 50 start server (node A capacity owner, capacity-a) (rc=0)
LISTENING 11290
--- 51 install capacity.article (rc=0)
--- 52 node A post beyond the capacity (rc=1)
refused operator post REFUSED
--- 53 stop server capacity-a (rc=0)
stopped
--- 54 native AUTHINFO secret (rc=0)
SECRET-READY
--- 55 node A principal set-password matrix (rc=0)
Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true
accepted operator principal set-password effective-at-next-start
--- 56 node A principal list (rc=0)
matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true
accepted operator principal list
--- 57 node A auth-required scratch store (rc=0)
initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/a/authgate/store
--- 58 node A auth-required scratch credential (rc=0)
Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true
accepted operator principal set-password effective-at-next-start
--- 59 start server (node A auth-required owner, authgate-a) (rc=0)
LISTENING 11292
--- 60 node A auth-required AUTHINFO gate (rc=0)
{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "OVER", "HDR", "XPAT", "NEWNEWS", "LIST", "IMPLEMENTATION", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BEFORE": "480 authentication required", "AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "CAPABILITIES AFTER": "101 capability list follows", "advertised_after": ["VERSION", "READER", "POST", "OVER", "HDR", "XPAT", "NEWNEWS", "LIST", "IMPLEMENTATION"], "AUTHINFO WITHDRAWN": true, "POST AFTER": "340 send article to be posted", "POST AFTER COMMIT": "240 article received OK", "AUTHINFO WRONG": "481 authentication failed", "ok": true}
--- 61 stop server authgate-a (rc=0)
stopped
--- 62 node B group create fn.matrix (rc=0)
configured generation=2 record=00000002.cfg verification=VERIFIED
accepted operator group
--- 63 node B group create fn.matrix.throwaway (rc=0)
configured generation=3 record=00000003.cfg verification=VERIFIED
accepted operator group
--- 64 node B group retire fn.matrix.throwaway (rc=0)
configured generation=4 record=00000004.cfg verification=VERIFIED
accepted operator group
--- 65 node B group retire an unserved group (rc=1)
refused operator group administrative configuration refused: NO-SUCH-GROUP
--- 66 node B capacity scratch store (rc=0)
initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/b/capacity/store
--- 67 node B capacity 64 (rc=0)
configured generation=2 record=00000002.cfg verification=VERIFIED
accepted operator capacity
--- 68 node B capacity 1 (rc=0)
configured generation=3 record=00000003.cfg verification=VERIFIED
accepted operator capacity
--- 69 node B capacity owner config (rc=0)
--- 70 start server (node B capacity owner, capacity-b) (rc=0)
LISTENING 11291
--- 71 install capacity.article (rc=0)
--- 72 node B post beyond the capacity (rc=1)
refused operator post REFUSED
--- 73 stop server capacity-b (rc=0)
stopped
--- 74 node B principal set-password matrix (rc=0)
Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true
accepted operator principal set-password effective-at-next-start
--- 75 node B principal list (rc=0)
matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true
accepted operator principal list
--- 76 node B auth-required scratch store (rc=0)
initialized /home/hbox/fn-deploy/native-e747dbcc-d78ee77/b/authgate/store
--- 77 node B auth-required scratch credential (rc=0)
Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true
accepted operator principal set-password effective-at-next-start
--- 78 start server (node B auth-required owner, authgate-b) (rc=0)
LISTENING 11293
--- 79 node B auth-required AUTHINFO gate (rc=0)
{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "OVER", "HDR", "XPAT", "NEWNEWS", "LIST", "IMPLEMENTATION", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BEFORE": "480 authentication required", "AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "CAPABILITIES AFTER": "101 capability list follows", "advertised_after": ["VERSION", "READER", "POST", "OVER", "HDR", "XPAT", "NEWNEWS", "LIST", "IMPLEMENTATION"], "AUTHINFO WITHDRAWN": true, "POST AFTER": "340 send article to be posted", "POST AFTER COMMIT": "240 article received OK", "AUTHINFO WRONG": "481 authentication failed", "ok": true}
--- 80 stop server authgate-b (rc=0)
stopped
--- 81 node A path-identity (rc=0)
configured generation=5 record=00000005.cfg verification=VERIFIED
accepted operator policy
--- 82 node B path-identity (rc=0)
configured generation=5 record=00000005.cfg verification=VERIFIED
accepted operator policy
--- 83 node B configured port (rc=0)
11191
--- 84 node A peer record for B (rc=0)
configured generation=6 record=00000006.cfg verification=VERIFIED
accepted operator peer
--- 85 node A lists its peers (rc=0)
b path-identity=b.gate.example.invalid address=127.0.0.1 port=11191 security=clear inbound=fn.* outbound=- auth=source-address:127.0.0.1
accepted operator peer
--- 86 node A configured port (rc=0)
11190
--- 87 node B peer record for A (rc=0)
configured generation=6 record=00000006.cfg verification=VERIFIED
accepted operator peer
--- 88 node B lists its peers (rc=0)
a path-identity=a.gate.example.invalid address=127.0.0.1 port=11190 security=clear inbound=fn.* outbound=- auth=source-address:127.0.0.1
accepted operator peer
--- 89 start server (node A (native-operator), a-main) (rc=0)
LISTENING 11190
--- 90 node A pid (rc=0)
3701240
--- 91 start server (node B (native-operator), b-main) (rc=0)
LISTENING 11191
--- 92 node B pid (rc=0)
3701366
--- 93 node A server is alive (rc=0)
ALIVE
--- 94 node A serves fn.matrix (rc=0)
{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}
--- 95 node A server is alive (rc=0)
ALIVE
--- 96 node A POST cycle (rc=0)
{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-c93c0fc7545f-a@example.invalid> article follows", "DUPLICATE POST": "340 send article to be posted", "DUPLICATE": "441 posting failed; this article is already stored here", "DATE AFTER DUPLICATE": "111 20260925200404", "FROM POST": "340 send article to be posted", "FROM": "441 posting failed; From is not a valid mailbox list", "FROM ARTICLE": "430 no article with that message-id", "counted": true, "ok": true}
--- 97 node A server is alive (rc=0)
ALIVE
--- 98 node A reader surface (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "XPAT", "NEWNEWS", "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "MODE READER": "200 posting allowed", "LIST ACTIVE": "215 list of active newsgroups follows", "LIST NEWSGROUPS": "215 list of newsgroups follows", "LIST OVERVIEW.FMT": "215 order of fields in overview database", "LIST ACTIVE.TIMES": "215 information follows", "LIST HEADERS": "215 field list follows", "LIST NEWSGROUPS WILDMAT": "215 list of newsgroups follows", "GROUP": "211 1 1 1 fn.letters", "group_count": 1, "group_first": 1, "group_last": 1, "LISTGROUP": "211 1 1 1 fn.letters list follows", "ARTICLE": "220 1 <native-matrix-c93c0fc7545f-a@example.invalid> article follows", "HEAD": "221 1 <native-matrix-c93c0fc7545f-a@example.invalid> headers follow", "BODY": "222 1 <native-matrix-c93c0fc7545f-a@example.invalid> body follows", "STAT": "223 1 <native-matrix-c93c0fc7545f-a@example.invalid> retrieved", "ARTICLE MSGID": "220 1 <native-matrix-c93c0fc7545f-a@example.invalid> article follows", "ARTICLE ABSENT": "430 no article with that message-id", "OVER": "224 overview information follows", "OVER RANGE": "224 overview information follows", "HDR": "225 headers follow", "XOVER": "224 overview information follows", "XHDR": "221 header follows", "XPAT": "221 header follows", "NEWNEWS": "230 list of new articles by message-id follows", "NEWNEWS STAMP TARGET": true, "NEWNEWS FUTURE": "230 list of new articles by message-id follows", "NEWNEWS SYNTAX": "501 syntax error", "NEXT": "421 no next article", "LAST": "422 no previous article", "DATE": "111 20260925200405", "HELP": "100 help text follows", "UNKNOWN": "500 command not recognized", "FRAMING": "111 20260925200405", "FRAMING SAME": true, "ok": true}
--- 99 node A server is alive (rc=0)
ALIVE
--- 100 node A AUTHINFO session (rc=0)
{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "POST", "OVER", "HDR", "XPAT", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BEFORE": "340 send article to be posted", "POST BEFORE CLOSE": "441 posting failed; the article is not valid syntax", "AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "CAPABILITIES AFTER": "101 capability list follows", "advertised_after": ["VERSION", "READER", "POST", "OVER", "HDR", "XPAT", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING"], "AUTHINFO WITHDRAWN": true, "POST AFTER": "340 send article to be posted", "POST AFTER COMMIT": "240 article received OK", "AUTHINFO WRONG": "481 authentication failed", "ok": true}
--- 101 node A server is alive (rc=0)
ALIVE
--- 102 install alpha.article (rc=0)
--- 103 node A outcome accepted (rc=0)
accepted operator post ACCEPTED
--- 104 install alpha.article (rc=0)
--- 105 node A outcome duplicate (rc=0)
accepted operator post DUPLICATE
--- 106 install alpha-conflict.article (rc=0)
--- 107 node A outcome refused (rc=1)
refused operator post REFUSED
--- 108 install stream-a.article (rc=0)
--- 109 node A seed <stream-a@example.invalid> (rc=0)
accepted operator post ACCEPTED
--- 110 node B server is alive (rc=0)
ALIVE
--- 111 node B serves fn.matrix (rc=0)
{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}
--- 112 node B server is alive (rc=0)
ALIVE
--- 113 node B POST cycle (rc=0)
{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-38a65a1b0259-b@example.invalid> article follows", "DUPLICATE POST": "340 send article to be posted", "DUPLICATE": "441 posting failed; this article is already stored here", "DATE AFTER DUPLICATE": "111 20260925200411", "FROM POST": "340 send article to be posted", "FROM": "441 posting failed; From is not a valid mailbox list", "FROM ARTICLE": "430 no article with that message-id", "counted": true, "ok": true}
--- 114 node B server is alive (rc=0)
ALIVE
--- 115 node B reader surface (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "XPAT", "NEWNEWS", "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "MODE READER": "200 posting allowed", "LIST ACTIVE": "215 list of active newsgroups follows", "LIST NEWSGROUPS": "215 list of newsgroups follows", "LIST OVERVIEW.FMT": "215 order of fields in overview database", "LIST ACTIVE.TIMES": "215 information follows", "LIST HEADERS": "215 field list follows", "LIST NEWSGROUPS WILDMAT": "215 list of newsgroups follows", "GROUP": "211 1 1 1 fn.letters", "group_count": 1, "group_first": 1, "group_last": 1, "LISTGROUP": "211 1 1 1 fn.letters list follows", "ARTICLE": "220 1 <native-matrix-38a65a1b0259-b@example.invalid> article follows", "HEAD": "221 1 <native-matrix-38a65a1b0259-b@example.invalid> headers follow", "BODY": "222 1 <native-matrix-38a65a1b0259-b@example.invalid> body follows", "STAT": "223 1 <native-matrix-38a65a1b0259-b@example.invalid> retrieved", "ARTICLE MSGID": "220 1 <native-matrix-38a65a1b0259-b@example.invalid> article follows", "ARTICLE ABSENT": "430 no article with that message-id", "OVER": "224 overview information follows", "OVER RANGE": "224 overview information follows", "HDR": "225 headers follow", "XOVER": "224 overview information follows", "XHDR": "221 header follows", "XPAT": "221 header follows", "NEWNEWS": "230 list of new articles by message-id follows", "NEWNEWS STAMP TARGET": true, "NEWNEWS FUTURE": "230 list of new articles by message-id follows", "NEWNEWS SYNTAX": "501 syntax error", "NEXT": "421 no next article", "LAST": "422 no previous article", "DATE": "111 20260925200411", "HELP": "100 help text follows", "UNKNOWN": "500 command not recognized", "FRAMING": "111 20260925200411", "FRAMING SAME": true, "ok": true}
--- 116 node B server is alive (rc=0)
ALIVE
--- 117 node B AUTHINFO session (rc=0)
{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "POST", "OVER", "HDR", "XPAT", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BEFORE": "340 send article to be posted", "POST BEFORE CLOSE": "441 posting failed; the article is not valid syntax", "AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "CAPABILITIES AFTER": "101 capability list follows", "advertised_after": ["VERSION", "READER", "POST", "OVER", "HDR", "XPAT", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING"], "AUTHINFO WITHDRAWN": true, "POST AFTER": "340 send article to be posted", "POST AFTER COMMIT": "240 article received OK", "AUTHINFO WRONG": "481 authentication failed", "ok": true}
--- 118 node B server is alive (rc=0)
ALIVE
--- 119 install beta.article (rc=0)
--- 120 node B outcome accepted (rc=0)
accepted operator post ACCEPTED
--- 121 install beta.article (rc=0)
--- 122 node B outcome duplicate (rc=0)
accepted operator post DUPLICATE
--- 123 install beta-conflict.article (rc=0)
--- 124 node B outcome refused (rc=1)
refused operator post REFUSED
--- 125 install stream-b.article (rc=0)
--- 126 node B seed <stream-b@example.invalid> (rc=0)
accepted operator post ACCEPTED
--- 127 node A server is alive (rc=0)
ALIVE
--- 128 node B server is alive (rc=0)
ALIVE
--- 129 nntplib interpreter (rc=0)
USE python3.12
--- 130 install independent.py (rc=0)
--- 131 independent nntplib client on node A (rc=0)
/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/independent.py:6: DeprecationWarning: 'nntplib' is deprecated and slated for removal in Python 3.13
  import argparse, json, nntplib, platform, sys
{"absent": "430 no article with that message-id", "article_has_msgid": true, "article_lines": 10, "body_lines": 1, "capabilities": ["AUTHINFO", "HDR", "IHAVE", "IMPLEMENTATION", "LIST", "NEWNEWS", "OVER", "POST", "READER", "STREAMING", "VERSION", "XPAT"], "client": "stdlib nntplib", "commands": ["CAPABILITIES", "GROUP", "STAT", "ARTICLE", "HEAD", "BODY", "OVER", "LIST", "ARTICLE (absent)", "QUIT"], "group": {"count": 4, "first": 1, "last": 4, "name": "fn.letters"}, "head_lines": 8, "list_groups": ["fn.letters", "fn.matrix", "fn.matrix.throwaway"], "ok": true, "over_rows": 4, "python": "3.12.7", "quit": "205 closing connection", "stat": [1, "<native-matrix-c93c0fc7545f-a@example.invalid>"], "welcome": "200 fn-nntp experimental server ready"}
--- 132 independent nntplib client on node B (rc=0)
/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/independent.py:6: DeprecationWarning: 'nntplib' is deprecated and slated for removal in Python 3.13
  import argparse, json, nntplib, platform, sys
{"absent": "430 no article with that message-id", "article_has_msgid": true, "article_lines": 10, "body_lines": 1, "capabilities": ["AUTHINFO", "HDR", "IHAVE", "IMPLEMENTATION", "LIST", "NEWNEWS", "OVER", "POST", "READER", "STREAMING", "VERSION", "XPAT"], "client": "stdlib nntplib", "commands": ["CAPABILITIES", "GROUP", "STAT", "ARTICLE", "HEAD", "BODY", "OVER", "LIST", "ARTICLE (absent)", "QUIT"], "group": {"count": 4, "first": 1, "last": 4, "name": "fn.letters"}, "head_lines": 8, "list_groups": ["fn.letters", "fn.matrix", "fn.matrix.throwaway"], "ok": true, "over_rows": 4, "python": "3.12.7", "quit": "205 closing connection", "stat": [1, "<native-matrix-38a65a1b0259-b@example.invalid>"], "welcome": "200 fn-nntp experimental server ready"}
--- 133 install .newsrc (rc=1)
bash: line 3: /home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc: No such file or directory
chmod: cannot access '/home/hbox/fn-deploy/native-e747dbcc-d78ee77/gate-run/tin-home/.newsrc': No such file or directory
--- 134 stop server node A (main) (rc=0)
stopped
--- 135 stop the tap in front of node A (rc=0)
stopped
--- 136 stop server node B (main) (rc=0)
stopped
--- 137 stop the tap in front of node B (rc=0)
stopped
--- 138 stray fn processes (rc=0)
CLEAN
--- 139 release deploy lock (rc=0)
```
