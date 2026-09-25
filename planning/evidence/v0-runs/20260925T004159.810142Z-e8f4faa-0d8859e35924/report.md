# v0 matrix: e8f4faa on hbox

v0 is every feature of fn usable between two peered fn nodes. This is that
question asked feature by feature against one commit on one box, with five
verdicts and no pass/fail collapse: accepted, refused and uncertain are the
three outcomes and each is a real observation; not-exercised names what
blocked the row; not-built names the lane that owns the missing feature.
It establishes nothing about the books beyond which certificates ACL2 read.

## What ran

| fact | value |
| --- | --- |
| commit | `e8f4faa` (e8f4faa5152f32821b3554c680483769a75b0b9b) |
| tree | `native-c3420013` |
| host | `hbox` |
| started | 2026-09-25T00:41:59Z |
| wall time | 215.9 s |
| gate tool | `tools/v0_matrix.py` |
| os | Ubuntu 24.10 kernel=Linux 6.11.0-29-generic arch=x86_64 cores=24 |
| python3 | Python 3.12.7 |
| acl2version | + ACL2 Version 8.7                                                     + |
| certificates | not acquired by this slice; it consumes the explicitly named saved image |
| node a | native-operator on port 11190 (main), store $HOME/fn-deploy/native-c3420013-e8f4faa/a/store |
| node b | native-operator on port 11191 (main), store $HOME/fn-deploy/native-c3420013-e8f4faa/b/store |
| server entry point | native-operator |
| three outcomes a | accepted=0 refused=1 uncertain=3 (uncertain is the init scratch node's, not this one's) |
| three outcomes b | accepted=0 refused=1 uncertain=3 (uncertain is the init scratch node's, not this one's) |
| transit | IHAVE -> '335 send it; end with <CR-LF>.<CR-LF>'; CAPABILITIES lists IHAVE: True |
| rows | 220 rows: 140 accepted, 46 refused, 2 uncertain, 31 not exercised, 1 not built, 2 disagreed, 0 faulted |
| alt | python3.12 Python 3.12.7 |
| duplicate resubmission a | identical octets: rc=0 accepted operator post DUPLICATE / different octets under the same Message-ID: rc=1 refused operator post REFUSED |
| duplicate resubmission b | identical octets: rc=0 accepted operator post DUPLICATE / different octets under the same Message-ID: rc=1 refused operator post REFUSED |
| execution backend | native-operator |
| execution image | launcher sha256=ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142; image sha256=432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505; declared runtime=b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5; sidecar core sha256=7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8 (static only before a live-owner witness); source correspondence unestablished |
| execution source | e8f4faa |
| server | node B (native-operator) on port 11191 (b-main) |
| host clients | expect=ABSENT, inews=ABSENT, nn=ABSENT, script=/usr/bin/script, slrn=ABSENT, tin=ABSENT, trn=ABSENT |

## The v0 matrix

**Execution subject.** Backend `native-operator`; deployed source `e8f4faa`; runtime image `launcher sha256=ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142; image sha256=432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505; declared runtime=b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5; sidecar core sha256=7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8 (static only before a live-owner witness); source correspondence unestablished; live owners observed via /proc runtime sha256=b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5 and core sha256=7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8`. These are separate labels: naming the source and hashing an externally supplied image does not prove they correspond.

220 rows: 140 accepted, 46 refused, 2 uncertain, 31 not exercised, 1 not built; 2 row(s) did not do what they were designed to do, and 0 exited with a host fault or usage error, which is not an outcome and is counted among the not exercised. Every count here is `tools/v0_matrix.py`'s over the rows below, and `planning/evidence/v0-runs/20260925T004159.810142Z-e8f4faa-0d8859e35924/matrix.json` carries the same rows with their digest.


**Who saw it.** 12 of the 188 outcome rows were observed by something that is not fn's own code; 176 were observed by fn talking to fn. A feature that only fn's own client has ever seen is a weaker claim than "usable between two peered servers" reads, and every row carries the client that saw it in its `client` field. Clients in this run: InterNetNews (10); fn CLI (exit code) (41); stdlib nntplib on python3.12 (2); the matrix's raw-socket driver (136).

| feature | accepted | refused | uncertain | not exercised | not built | disagreed |
| --- | --- | --- | --- | --- | --- | --- |
| node init, configuration, start and stop (F-NODE) | 13 | 2 | 0 | 1 | 0 | 0 |
| the three outcomes on the operator surface (F-OUT) | 4 | 2 | 2 | 0 | 0 | 0 |
| groups, capacity, peers and live reconfiguration (F-GROUP) | 14 | 6 | 0 | 0 | 0 | 0 |
| principals, AUTHINFO and posting permission (F-AUTH) | 12 | 4 | 0 | 0 | 1 | 0 |
| POST and its read-back (F-POST) | 11 | 4 | 0 | 0 | 0 | 0 |
| the reader profile on each node (F-READ) | 54 | 10 | 0 | 0 | 0 | 0 |
| capability truthfulness (F-PIN) | 4 | 0 | 0 | 0 | 0 | 0 |
| transit inbound, A to B and B to A (F-TRANSIT) | 18 | 12 | 0 | 2 | 0 | 0 |
| the owner-driven outbound feed (F-FEED) | 4 | 0 | 0 | 0 | 0 | 0 |
| checkpoint, recovery and the process-death cut table (F-CRASH) | 0 | 0 | 0 | 9 | 0 | 0 |
| BP over TCPCLv4 between the two nodes (F-BP) | 0 | 0 | 0 | 8 | 0 | 0 |
| statement sign and verify across the pair (F-STX) | 0 | 0 | 0 | 6 | 0 | 0 |
| the carried-media letter (F-MEDIA) | 0 | 0 | 0 | 3 | 0 | 0 |
| scale (F-SCALE) | 0 | 0 | 0 | 1 | 0 | 0 |
| INN as a third node (F-INN) | 4 | 6 | 0 | 0 | 0 | 2 |
| independent newsreader clients (F-CLIENT) | 2 | 0 | 0 | 1 | 0 | 0 |

### Every row

| row | title | verdict | expected | agrees | independent | observed |
| --- | --- | --- | --- | --- | --- | --- |
| `V0-NODE-INIT-A` | fn init creates the store and writes fn.toml | **accepted** | accepted | yes | fn only | rc=0 initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/a/init/store |
| `V0-NODE-INIT-B` | fn init creates the store and writes fn.toml | **accepted** | accepted | yes | fn only | rc=0 initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/b/init/store |
| `V0-NODE-CONFIG-A` | the native operator initializes the store named by fn.toml [store] path | **accepted** | accepted | yes | fn only | initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/a/init/store |
| `V0-NODE-CONFIG-B` | the native operator initializes the store named by fn.toml [store] path | **accepted** | accepted | yes | fn only | initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/b/init/store |
| `V0-NODE-REINIT-A` | what a second fn init over a store that already holds articles does | **refused** | - | - | fn only | rc=1 refused operator init STORE-EXISTS |
| `V0-NODE-REINIT-B` | what a second fn init over a store that already holds articles does | **refused** | - | - | fn only | rc=1 refused operator init STORE-EXISTS |
| `V0-NODE-REINIT-SAFE-A` | the articles the store already held are still there after the second init | **accepted** | accepted | yes | fn only | before: recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none / after: recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none |
| `V0-NODE-REINIT-SAFE-B` | the articles the store already held are still there after the second init | **accepted** | accepted | yes | fn only | before: recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none / after: recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none |
| `V0-NODE-STATUS-A` | fn status reports generation and article count | **accepted** | accepted | yes | fn only | rc=0 transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment |
| `V0-NODE-STATUS-B` | fn status reports generation and article count | **accepted** | accepted | yes | fn only | rc=0 transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment |
| `V0-NODE-START-A` | the service starts and reaches LISTENING | **accepted** | accepted | yes | fn only | `native-operator` reached LISTENING |
| `V0-NODE-START-B` | the service starts and reaches LISTENING | **accepted** | accepted | yes | fn only | `native-operator` reached LISTENING |
| `V0-NODE-STOP-A` | the service stops and releases the store | **accepted** | accepted | yes | fn only | stop rc=0; native status afterwards rc=0 transactions=7 articles=7 staging-orphans=0 unsigned-legacy-experiment |
| `V0-NODE-STOP-B` | the service stops and releases the store | **accepted** | accepted | yes | fn only | stop rc=0; native status afterwards rc=0 transactions=6 articles=6 staging-orphans=0 unsigned-legacy-experiment |
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
| `V0-PEER-ABSENT` | fn peer remove of a peer that is not there is refused | **refused** | refused | yes | fn only | rc=1 refused operator peer administrative configuration refused: NO-SUCH-PEER |
| `V0-PEER-REMOVE` | fn peer remove of a configured peer is accepted | **accepted** | accepted | yes | fn only | rc=0 configured generation=8 record=00000008.cfg verification=VERIFIED |
| `V0-CFG-LIVE` | a group declared on the running service's control channel reaches the served configuration | **accepted** | accepted | yes | fn only | rc=0 accepted operator group; GROUP fn.matrix.live -> 211 0 1 0 fn.matrix.live |
| `V0-CFG-LIVE-REFUSE` | an offline configuration command is refused while the service holds the store | **refused** | refused | yes | fn only | rc=1 refused operator group store is already locked |
| `V0-AUTH-NEW` | fn principal new derives a principal id from a seed | **not-built** | accepted | - | - | (not run) |
| `V0-AUTH-PASSWORD-A` | fn principal set-password records an AUTHINFO credential | **accepted** | accepted | yes | fn only | rc=0 matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true |
| `V0-AUTH-PASSWORD-B` | fn principal set-password records an AUTHINFO credential | **accepted** | accepted | yes | fn only | rc=0 Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true |
| `V0-AUTH-LIST-A` | fn principal list shows the credential | **accepted** | accepted | yes | fn only | rc=0 matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true; lists matrix: True |
| `V0-AUTH-LIST-B` | fn principal list shows the credential | **accepted** | accepted | yes | fn only | rc=0 matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true; lists matrix: True |
| `V0-AUTH-ADVERTISED-A` | AUTHINFO USER is advertised while the connection is unauthenticated | **accepted** | accepted | yes | fn only | CAPABILITIES before the login: VERSION, READER, POST, OVER, HDR, NEWNEWS, LIST, IMPLEMENTATION, IHAVE, STREAMING, AUTHINFO |
| `V0-AUTH-ADVERTISED-B` | AUTHINFO USER is advertised while the connection is unauthenticated | **accepted** | accepted | yes | fn only | CAPABILITIES before the login: VERSION, READER, POST, OVER, HDR, NEWNEWS, LIST, IMPLEMENTATION, IHAVE, STREAMING, AUTHINFO |
| `V0-AUTH-GATED-A` | POST before a login is refused, not performed | **refused** | refused | yes | fn only | 480 authentication required |
| `V0-AUTH-GATED-B` | POST before a login is refused, not performed | **refused** | refused | yes | fn only | 480 authentication required |
| `V0-AUTH-LOGIN-A` | AUTHINFO USER then PASS answers 281 | **accepted** | accepted | yes | fn only | 281 authentication accepted |
| `V0-AUTH-LOGIN-B` | AUTHINFO USER then PASS answers 281 | **accepted** | accepted | yes | fn only | 281 authentication accepted |
| `V0-AUTH-WITHDRAWN-A` | AUTHINFO is no longer advertised once the connection is authenticated | **accepted** | accepted | yes | fn only | CAPABILITIES after the login: VERSION, READER, POST, OVER, HDR, NEWNEWS, LIST, IMPLEMENTATION, IHAVE, STREAMING |
| `V0-AUTH-WITHDRAWN-B` | AUTHINFO is no longer advertised once the connection is authenticated | **accepted** | accepted | yes | fn only | CAPABILITIES after the login: VERSION, READER, POST, OVER, HDR, NEWNEWS, LIST, IMPLEMENTATION, IHAVE, STREAMING |
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
| `V0-POST-FRESH-A` | a fresh connection reads it back by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <native-matrix-50709493a7c8-a@example.invalid> article follows |
| `V0-POST-FRESH-B` | a fresh connection reads it back by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <native-matrix-41a756d84051-b@example.invalid> article follows |
| `V0-POST-DUPLICATE-A` | a second POST of the same Message-ID is refused and allocates nothing | **refused** | refused | yes | fn only | 441 posting failed; this article is already stored here |
| `V0-POST-DUPLICATE-B` | a second POST of the same Message-ID is refused and allocates nothing | **refused** | refused | yes | fn only | 441 posting failed; this article is already stored here |
| `V0-POST-CLOCK-A` | a duplicate POST is refused as an article and does not cost the node its clock | **accepted** | accepted | yes | fn only | the duplicate answered '441 posting failed; this article is already stored here' and DATE afterwards answered '111 20260925004317' |
| `V0-POST-CLOCK-B` | a duplicate POST is refused as an article and does not cost the node its clock | **accepted** | accepted | yes | fn only | the duplicate answered '441 posting failed; this article is already stored here' and DATE afterwards answered '111 20260925004325' |
| `V0-POST-FROM-MAILBOX-A` | a POST whose From names no address (`From: yue`) is refused with 441 and is not served | **refused** | refused | yes | fn only | POST of `From: yue` answered '441 posting failed; From is not a valid mailbox list'; STAT of its Message-ID answered '430 no article with that message-id' |
| `V0-POST-FROM-MAILBOX-B` | a POST whose From names no address (`From: yue`) is refused with 441 and is not served | **refused** | refused | yes | fn only | POST of `From: yue` answered '441 posting failed; From is not a valid mailbox list'; STAT of its Message-ID answered '430 no article with that message-id' |
| `V0-POST-CONCURRENT` | a second reader stays live across another connection's whole POST | **accepted** | accepted | yes | fn only | watcher mid-post=211 6 1 6 fn.letters commit=240 article received OK |
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
| `V0-READ-ARTICLE-A` | ARTICLE by number | **accepted** | accepted | yes | fn only | 220 1 <native-matrix-50709493a7c8-a@example.invalid> article follows |
| `V0-READ-ARTICLE-B` | ARTICLE by number | **accepted** | accepted | yes | fn only | 220 1 <native-matrix-41a756d84051-b@example.invalid> article follows |
| `V0-READ-HEAD-A` | HEAD by number | **accepted** | accepted | yes | fn only | 221 1 <native-matrix-50709493a7c8-a@example.invalid> headers follow |
| `V0-READ-HEAD-B` | HEAD by number | **accepted** | accepted | yes | fn only | 221 1 <native-matrix-41a756d84051-b@example.invalid> headers follow |
| `V0-READ-BODY-A` | BODY by number | **accepted** | accepted | yes | fn only | 222 1 <native-matrix-50709493a7c8-a@example.invalid> body follows |
| `V0-READ-BODY-B` | BODY by number | **accepted** | accepted | yes | fn only | 222 1 <native-matrix-41a756d84051-b@example.invalid> body follows |
| `V0-READ-STAT-A` | STAT by number | **accepted** | accepted | yes | fn only | 223 1 <native-matrix-50709493a7c8-a@example.invalid> retrieved |
| `V0-READ-STAT-B` | STAT by number | **accepted** | accepted | yes | fn only | 223 1 <native-matrix-41a756d84051-b@example.invalid> retrieved |
| `V0-READ-ARTICLE-MSGID-A` | ARTICLE by Message-ID | **accepted** | accepted | yes | fn only | 220 1 <native-matrix-50709493a7c8-a@example.invalid> article follows |
| `V0-READ-ARTICLE-MSGID-B` | ARTICLE by Message-ID | **accepted** | accepted | yes | fn only | 220 1 <native-matrix-41a756d84051-b@example.invalid> article follows |
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
| `V0-READ-NEWNEWS-STAMP-A` | NEWNEWS since 1970 includes this node's accepted article even when its payload date differs from its acceptance | **accepted** | accepted | yes | fn only | whole-history NEWNEWS contains target <native-matrix-50709493a7c8-a@example.invalid>: True |
| `V0-READ-NEWNEWS-STAMP-B` | NEWNEWS since 1970 includes this node's accepted article even when its payload date differs from its acceptance | **accepted** | accepted | yes | fn only | whole-history NEWNEWS contains target <native-matrix-41a756d84051-b@example.invalid>: True |
| `V0-READ-NEWNEWS-FUTURE-A` | NEWNEWS since a future instant returns the empty block | **accepted** | accepted | yes | fn only | 230 list of new articles by message-id follows |
| `V0-READ-NEWNEWS-FUTURE-B` | NEWNEWS since a future instant returns the empty block | **accepted** | accepted | yes | fn only | 230 list of new articles by message-id follows |
| `V0-READ-NEWNEWS-SYNTAX-A` | NEWNEWS with a malformed wildmat is refused with 501 | **refused** | refused | yes | fn only | 501 syntax error |
| `V0-READ-NEWNEWS-SYNTAX-B` | NEWNEWS with a malformed wildmat is refused with 501 | **refused** | refused | yes | fn only | 501 syntax error |
| `V0-READ-DATE-A` | DATE | **accepted** | accepted | yes | fn only | 111 20260925004317 |
| `V0-READ-DATE-B` | DATE | **accepted** | accepted | yes | fn only | 111 20260925004326 |
| `V0-READ-HELP-A` | HELP | **accepted** | accepted | yes | fn only | 100 help text follows |
| `V0-READ-HELP-B` | HELP | **accepted** | accepted | yes | fn only | 100 help text follows |
| `V0-READ-UNKNOWN-A` | an unknown command is refused with 500 | **refused** | refused | yes | fn only | 500 command not recognized |
| `V0-READ-UNKNOWN-B` | an unknown command is refused with 500 | **refused** | refused | yes | fn only | 500 command not recognized |
| `V0-READ-FRAMING-A` | a command split across two TCP segments is answered once, the same way | **accepted** | accepted | yes | fn only | DATE split across two segments answered '111 20260925004317' against '111 20260925004317' |
| `V0-READ-FRAMING-B` | a command split across two TCP segments is answered once, the same way | **accepted** | accepted | yes | fn only | DATE split across two segments answered '111 20260925004326' against '111 20260925004326' |
| `V0-PIN-DISPATCHED-A` | every capability the node advertises is dispatched by the node | **accepted** | accepted | yes | fn only | advertised=VERSION,READER,POST,OVER,HDR,NEWNEWS,LIST,IMPLEMENTATION,IHAVE,STREAMING,AUTHINFO not dispatched=(none) |
| `V0-PIN-DISPATCHED-B` | every capability the node advertises is dispatched by the node | **accepted** | accepted | yes | fn only | advertised=VERSION,READER,POST,OVER,HDR,NEWNEWS,LIST,IMPLEMENTATION,IHAVE,STREAMING,AUTHINFO not dispatched=(none) |
| `V0-PIN-ADVERTISED-A` | every command the node dispatches is advertised in CAPABILITIES | **accepted** | accepted | yes | fn only | dispatched=READER,POST,IHAVE,STREAMING,OVER,HDR,LIST,NEWNEWS,AUTHINFO,STARTTLS,MODE-READER,XOVER,XHDR,XPAT,LISTGROUP,CHECK,TAKETHIS not advertised=(none) |
| `V0-PIN-ADVERTISED-B` | every command the node dispatches is advertised in CAPABILITIES | **accepted** | accepted | yes | fn only | dispatched=READER,POST,IHAVE,STREAMING,OVER,HDR,LIST,NEWNEWS,AUTHINFO,STARTTLS,MODE-READER,XOVER,XHDR,XPAT,LISTGROUP,CHECK,TAKETHIS not advertised=(none) |
| `V0-TRANSIT-IDENTITY-A` | the node has an RFC 5537 <path-identity> of its own | **accepted** | accepted | yes | fn only | rc=0 configured generation=5 record=00000005.cfg verification=VERIFIED |
| `V0-TRANSIT-IDENTITY-B` | the node has an RFC 5537 <path-identity> of its own | **accepted** | accepted | yes | fn only | rc=0 configured generation=5 record=00000005.cfg verification=VERIFIED |
| `V0-TRANSIT-INDEPENDENT-A` | each node serves its own seeded articles and 43x for the other's seeds | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-INDEPENDENT-B` | each node serves its own seeded articles and 43x for the other's seeds | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-MODE-STREAM-AB` | MODE STREAM is accepted on the peer connection | **accepted** | accepted | yes | fn only | 203 streaming permitted |
| `V0-TRANSIT-MODE-STREAM-BA` | MODE STREAM is accepted on the peer connection | **accepted** | accepted | yes | fn only | 203 streaming permitted |
| `V0-TRANSIT-OFFER-AB` | IHAVE of a wanted article answers 335 | **accepted** | accepted | yes | fn only | 335 send it; end with <CR-LF>.<CR-LF> |
| `V0-TRANSIT-OFFER-BA` | IHAVE of a wanted article answers 335 | **accepted** | accepted | yes | fn only | 335 send it; end with <CR-LF>.<CR-LF> |
| `V0-TRANSIT-TRANSFER-AB` | the transferred article is taken with 235 | **accepted** | accepted | yes | fn only | 235 article transferred OK |
| `V0-TRANSIT-TRANSFER-BA` | the transferred article is taken with 235 | **accepted** | accepted | yes | fn only | 235 article transferred OK |
| `V0-TRANSIT-IDENTICAL-AB` | the far side serves the source's octets with its own path identity and the diagnostic prepended to Path and no Xref, every other line identical | **accepted** | accepted | yes | fn only | reread=220 0 <alpha@a.example.invalid> article follows served 'Path: b.gate.example.invalid!!a.gate.example.invalid!not-for-mail'; the posted article with the Path update and no Xref, every other line |
| `V0-TRANSIT-IDENTICAL-BA` | the far side serves the source's octets with its own path identity and the diagnostic prepended to Path and no Xref, every other line identical | **accepted** | accepted | yes | fn only | reread=220 0 <beta@b.example.invalid> article follows served 'Path: a.gate.example.invalid!!b.gate.example.invalid!not-for-mail'; the posted article with the Path update and no Xref, every other line  |
| `V0-TRANSIT-DUPLICATE-AB` | a second IHAVE of the same Message-ID is refused with 435 | **refused** | refused | yes | fn only | 435 duplicate |
| `V0-TRANSIT-DUPLICATE-BA` | a second IHAVE of the same Message-ID is refused with 435 | **refused** | refused | yes | fn only | 435 duplicate |
| `V0-TRANSIT-LOOP-AB` | an article whose Path already names the target is refused after its 335 | **refused** | refused | yes | fn only | 437 transfer rejected; path loop |
| `V0-TRANSIT-LOOP-BA` | an article whose Path already names the target is refused after its 335 | **refused** | refused | yes | fn only | 437 transfer rejected; path loop |
| `V0-TRANSIT-LOOP-ABSENT-AB` | the refused loop article is not served by the target afterwards | **refused** | refused | yes | fn only | 430 no article with that message-id |
| `V0-TRANSIT-LOOP-ABSENT-BA` | the refused loop article is not served by the target afterwards | **refused** | refused | yes | fn only | 430 no article with that message-id |
| `V0-TRANSIT-CHECK-FRESH-AB` | CHECK of a Message-ID the target has not seen answers 238 | **accepted** | accepted | yes | fn only | 238 <stream-a@example.invalid> |
| `V0-TRANSIT-CHECK-FRESH-BA` | CHECK of a Message-ID the target has not seen answers 238 | **accepted** | accepted | yes | fn only | 238 <stream-b@example.invalid> |
| `V0-TRANSIT-TAKETHIS-AB` | TAKETHIS of that wanted article answers 239 | **accepted** | accepted | yes | fn only | 239 <stream-a@example.invalid> |
| `V0-TRANSIT-TAKETHIS-BA` | TAKETHIS of that wanted article answers 239 | **accepted** | accepted | yes | fn only | 239 <stream-b@example.invalid> |
| `V0-TRANSIT-CHECK-DUP-AB` | CHECK of an article the target holds answers 438 | **refused** | refused | yes | fn only | 438 <alpha@a.example.invalid> |
| `V0-TRANSIT-CHECK-DUP-BA` | CHECK of an article the target holds answers 438 | **refused** | refused | yes | fn only | 438 <beta@b.example.invalid> |
| `V0-TRANSIT-TAKETHIS-DUP-AB` | TAKETHIS that ignores that advice answers 439, never a 2xx and never a retry | **refused** | refused | yes | fn only | 439 <alpha@a.example.invalid> |
| `V0-TRANSIT-TAKETHIS-DUP-BA` | TAKETHIS that ignores that advice answers 439, never a 2xx and never a retry | **refused** | refused | yes | fn only | 439 <beta@b.example.invalid> |
| `V0-TRANSIT-TLS-AB` | the owner's feed reaches the peer over STARTTLS, the peer's certificate verified against the record's anchor and server name | **accepted** | accepted | yes | fn only | {"reconnect": {"identical": true}, "transit": {"identical": true, "unauthenticated_offer": "502 transit is not permitted on this connection"}} |
| `V0-TRANSIT-TLS-BA` | the owner's feed reaches the peer over STARTTLS, the peer's certificate verified against the record's anchor and server name | **accepted** | accepted | yes | fn only | {"reconnect": {"identical": true}, "transit": {"identical": true, "unauthenticated_offer": "502 transit is not permitted on this connection"}} |
| `V0-TRANSIT-AUTHINFO-AB` | the owner's feed logs in with AUTHINFO as the principal the peer's record binds before it offers, and the peer takes the offer in that role | **accepted** | accepted | yes | fn only | {"reconnect": {"identical": true}, "transit": {"identical": true, "unauthenticated_offer": "502 transit is not permitted on this connection"}} |
| `V0-TRANSIT-AUTHINFO-BA` | the owner's feed logs in with AUTHINFO as the principal the peer's record binds before it offers, and the peer takes the offer in that role | **accepted** | accepted | yes | fn only | {"reconnect": {"identical": true}, "transit": {"identical": true, "unauthenticated_offer": "502 transit is not permitted on this connection"}} |
| `V0-TRANSIT-TLS-WRONG-ANCHOR` | a feed whose record names an anchor that did not issue the peer's certificate delivers nothing, and both owners stay up | **refused** | refused | yes | fn only | {"case": "wrong-anchor", "delivered": false, "identity": {"a": {"core": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host.core", "core_sha256": "7a124c6f70e072dbd0a8ade9b29b756bbdad |
| `V0-TRANSIT-AUTHINFO-WRONG` | a feed whose profile carries a wrong password delivers nothing, and both owners stay up | **refused** | refused | yes | fn only | {"case": "wrong-password", "delivered": false, "identity": {"a": {"core": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host.core", "core_sha256": "7a124c6f70e072dbd0a8ade9b29b756bbd |
| `V0-FEED-QUEUE` | an article accepted on the source enters the matching peer's outbound queue | **accepted** | accepted | yes | fn only | {"duplicate": "435", "identity": {"restart-a": {"core": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host.core", "core_sha256": "7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234 |
| `V0-FEED-OFFER` | the owner opens the session and offers it, with no hand-driven socket | **accepted** | accepted | yes | fn only | {"ab": {"duplicate": "435", "identical": true}, "ba": {"duplicate": "435", "identical": true}} |
| `V0-FEED-ONCE` | an acknowledged transfer is not offered a second time | **accepted** | accepted | yes | fn only | {"acknowledged": {"after": {"attempts": 0, "inflight": "nil", "next_attempt": 2, "queue_length": 1, "records": {"feed-commit": 1, "feed-intent": 1, "feed-offer": 1, "feed-outcome": 1, "feed-restart":  |
| `V0-FEED-JOURNAL` | the feed journal records the transfer and survives a restart | **accepted** | accepted | yes | fn only | {"duplicate": "435", "identity": {"restart-a": {"core": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host.core", "core_sha256": "7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234 |
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
| `V0-INN-INTEROP` | a real INN server exchanges with an fn node as a third peer | **refused** | accepted | NO | yes | the lab's verdict: violated (32 held, 1 violated) |
| `V0-INN-FEED-OUT` | an article POSTed to fn reaches INN through fn's outbound feed (IHAVE 335/235) and nnrpd serves it changed only in Path and Xref | **accepted** | accepted | yes | yes | fn-post-240=held (340 send article to be posted / 240 article received OK); fn-feeds-inn=held (IHAVE: 335 Send it / 235 Article transferred OK); inn-serves-fn-article=held (changed: path; only in the  |
| `V0-INN-FEED-IN` | INN's innfeed delivers an article to fn (CHECK 238, TAKETHIS 239) and fn serves it changed at most in Path and Xref | **accepted** | accepted | yes | yes | innfeed-feeds-fn=held (CHECK+TAKETHIS: 238 <inn-lab-fed-e8f4faa-20260925T004443Z@example.invalid> / 239 <inn-lab-fed-e8f4faa-20260925T004443Z@example.invalid>); fn-serves-inn-article=held (changed: pa |
| `V0-INN-DUPLICATE-INN` | INN refuses a second IHAVE of the article fn fed it with 435 | **refused** | refused | yes | yes | inn-duplicate-435[fn-article]=held (435 Duplicate) |
| `V0-INN-DUPLICATE-FN` | fn refuses a second IHAVE of each article it holds (INN's and its own) with 435 | **refused** | refused | yes | yes | fn-duplicate-435[inn-article]=held (435 duplicate); fn-duplicate-435[fn-article]=held (435 duplicate) |
| `V0-INN-LOOP-INN` | INN refuses an article whose Path names it with 437 | **refused** | refused | yes | yes | inn-loop-437=held (437 Unwanted site inn.hbox.test in path) |
| `V0-INN-LOOP-FN` | fn refuses an article whose Path names its own path identity, and does not serve it | **refused** | refused | yes | yes | fn-loop-refused=held (335 send it; end with <CR-LF>.<CR-LF> / 437 transfer rejected; path loop / 430 no article with that message-id) |
| `V0-INN-RESTART` | INN's history survives a SIGKILL of innd, and fn's articles survive a SIGTERM, recover and restart byte-identical | **accepted** | accepted | yes | yes | fn-term-stopped=held (OWNER-GONE); fn-recover=held (rc=0 recovered transactions=3 articles=3 staging-orphans=0 anchor=none checkpoint=none); fn-articles-survived-term[fn-article]=held (220 0 <inn-lab- |
| `V0-INN-SERVING-AGENT` | an article fn took from INN is served with fn's path identity in Path and without INN's Xref (RFC 5537 3.7 steps 6 and 7) | **accepted** | accepted | yes | yes | fn-serves-own-path-identity=held (Path: fnA.hbox.test!!inn.hbox.test!lab.example.invalid!not-for-mail); fn-serves-no-sender-xref=held (Xref: (none)) |
| `V0-INN-OPERATOR-POST` | an article submitted through `operator post` reaches INN through fn's feed, injected with fn's Path (IHAVE 335/235) | **refused** | accepted | NO | yes | operator-post-feeds-inn=violated (IHAVE: 335 Send it / 235 Article transferred OK) |
| `V0-CLIENT-NNTPLIB-A` | an independent stdlib nntplib client reads a group and an article | **accepted** | accepted | yes | yes | nntplib 3.12.7 drove CAPABILITIES, GROUP, STAT, ARTICLE, HEAD, BODY, OVER, LIST, ARTICLE (absent), QUIT; login=(not attempted) authinfo-advertised=None group={'count': 4, 'first': 1, 'last': 4, 'name' |
| `V0-CLIENT-NNTPLIB-B` | an independent stdlib nntplib client reads a group and an article | **accepted** | accepted | yes | yes | nntplib 3.12.7 drove CAPABILITIES, GROUP, STAT, ARTICLE, HEAD, BODY, OVER, LIST, ARTICLE (absent), QUIT; login=(not attempted) authinfo-advertised=None group={'count': 4, 'first': 1, 'last': 4, 'name' |
| `V0-CLIENT-SLRN` | slrn reads a group and an article | **not-exercised** | accepted | - | - | (slrn is not installed) |

### What every row that is not an outcome is waiting for

- `V0-NODE-LOOPBACK` (not-exercised): the command exited 5, a usage error, which is not one of the three outcomes (docs/operator.md: 0 accepted, 1 refused, 3 uncertain)
- `V0-AUTH-NEW` (not-built): the packaged native operator has no `principal new`: the local principal id is derived by ACL2 inside `set-password` (`fn-native-auth-admin-principal`, books/native-auth-admin.lisp) and no public verb derives one from a seed -- owned by `native principal derivation surface`
- `V0-TRANSIT-INDEPENDENT-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-TRANSIT-INDEPENDENT-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
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
- `V0-NODE-STOP-A`: the stop is the harness's SIGTERM, not an operator verb; the store reopening for the offline operator is the writer lock being gone; no in-flight session was observed across the stop
- `V0-NODE-STOP-B`: the stop is the harness's SIGTERM, not an operator verb; the store reopening for the offline operator is the writer lock being gone; no in-flight session was observed across the stop
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
- `V0-PEER-REMOVE`: run after the owners stopped, so it says nothing about removing a peer from a live service
- `V0-CFG-LIVE`: one group declared on one live owner: the operator verb's exit code is the acceptance and the service is then asked over its own socket whether the group reached the served configuration. No concurrent reader was observed across the change, and nothing here says the change survives a restart
- `V0-CFG-LIVE-REFUSE`: a second configuration over node A's OWN store whose `[control] path` names a socket nothing has bound, so the verb takes the offline executor while the live owner (asked alive just before) holds the writer lock; the refusal is that lock's and a server that does not take it would not produce it. The supplied configuration is unchanged, and with its own live control path the same words reach the live owner instead -- which is the row above
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
- `V0-POST-CONCURRENT`: two connections on one box; this is not concurrent load
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
- `V0-PIN-DISPATCHED-A`: only the 11 labels with a probe command are checked; VERSION and IMPLEMENTATION have none
- `V0-PIN-DISPATCHED-B`: only the 11 labels with a probe command are checked; VERSION and IMPLEMENTATION have none
- `V0-PIN-ADVERTISED-A`: only the 11 labels with a probe command are checked; VERSION and IMPLEMENTATION have none; RFC 3977 section 5.2.2 requires the capability exactly when the command is available
- `V0-PIN-ADVERTISED-B`: only the 11 labels with a probe command are checked; VERSION and IMPLEMENTATION have none; RFC 3977 section 5.2.2 requires the capability exactly when the command is available
- `V0-TRANSIT-IDENTITY-A`: `fn-peer-local-identity` reads the `path-identity` policy slot and an unset slot is the empty string, which `fn-path-names-p` never matches: a node without this answers no loop, so V0-TRANSIT-LOOP rests on it; a `:set-policy` configuration record; the loop rows below are what shows the owner read it
- `V0-TRANSIT-IDENTITY-B`: `fn-peer-local-identity` reads the `path-identity` policy slot and an unset slot is the empty string, which `fn-path-names-p` never matches: a node without this answers no loop, so V0-TRANSIT-LOOP rests on it; a `:set-policy` configuration record; the loop rows below are what shows the owner read it
- `V0-TRANSIT-MODE-STREAM-AB`: node B is `native-operator`; the peer record on it names a
- `V0-TRANSIT-MODE-STREAM-BA`: node A is `native-operator`; the peer record on it names b
- `V0-TRANSIT-OFFER-AB`: node B is `native-operator`; the peer record on it names a
- `V0-TRANSIT-OFFER-BA`: node A is `native-operator`; the peer record on it names b
- `V0-TRANSIT-TRANSFER-AB`: node B is `native-operator`; the peer record on it names a
- `V0-TRANSIT-TRANSFER-BA`: node A is `native-operator`; the peer record on it names b
- `V0-TRANSIT-IDENTICAL-AB`: the posted and served lines are compared against fn-peer-relayed-octets' keystones (change-only-path-and-xref, carry-no-xref, name-this-node-in-every-path) with node B's configured path-identity b.gate.example.invalid; which diagnostic applies is fn-path-diagnostic's and either rendering is admitted, the served Path shows which; local article numbers are not compared
- `V0-TRANSIT-IDENTICAL-BA`: the posted and served lines are compared against fn-peer-relayed-octets' keystones (change-only-path-and-xref, carry-no-xref, name-this-node-in-every-path) with node A's configured path-identity a.gate.example.invalid; which diagnostic applies is fn-path-diagnostic's and either rendering is admitted, the served Path shows which; local article numbers are not compared
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
- `V0-TRANSIT-TLS-AB`: the article's arrival under a target that refuses AUTHINFO before TLS and denies unauthenticated transit with 502 is what shows the channel; the matrix does not see the feed's own socket, and OpenSSL's chain and hostname checks are trusted integration (PRF-047); the article arrived, and again after both owners restarted, at a target with `protected_only`; the chain and hostname check is OpenSSL's
- `V0-TRANSIT-TLS-BA`: the article's arrival under a target that refuses AUTHINFO before TLS and denies unauthenticated transit with 502 is what shows the channel; the matrix does not see the feed's own socket, and OpenSSL's chain and hostname checks are trusted integration (PRF-047); the article arrived, and again after both owners restarted, at a target with `protected_only`; the chain and hostname check is OpenSSL's
- `V0-TRANSIT-AUTHINFO-AB`: the same arrival: an unauthenticated offer of the same article is 502 on the target, so the feed's offer came on a connection that logged in; PRF-051's keystones are what say the feed sends no offer before the 281; the target answered the same offer 502 on a connection that did not log in
- `V0-TRANSIT-AUTHINFO-BA`: the same arrival: an unauthenticated offer of the same article is 502 on the target, so the feed's offer came on a connection that logged in; PRF-051's keystones are what say the feed sends no offer before the 281; the target answered the same offer 502 on a connection that did not log in
- `V0-TRANSIT-TLS-WRONG-ANCHOR`: absence is observed for three seconds through a protected reader session; a longer delay is not excluded
- `V0-TRANSIT-AUTHINFO-WRONG`: absence is observed for three seconds through a protected reader session; a longer delay is not excluded
- `V0-FEED-QUEUE`: the restart witness found FNFD intent
- `V0-FEED-OFFER`: the public owner delivered both directions
- `V0-FEED-ONCE`: the ACL2 FNFD scanner/replay found :done before and after sender SIGKILL/restart; offer/sent record counts did not grow over two seconds; a developer cut killed the sender after durable :feed-sent, and a fresh protected owner settled its requeued attempt with one recipient article
- `V0-FEED-JOURNAL`: intent survived source death and restart
- `V0-CRASH-KILL`: what the client saw is recorded; an acknowledgement after the kill would be the defect, and its absence is the assertion
- `V0-SCALE-CEILING`: a measured ceiling on one box with one payload grid; it is not a bound and not a proof
- `V0-INN-INTEROP`: one INN version on one box over loopback, through the lab's byte-transparent relay; not a Usenet conformance audit
- `V0-INN-FEED-OUT`: one INN version on one box over loopback, through the lab's byte-transparent relay; not a Usenet conformance audit
- `V0-INN-FEED-IN`: one INN version on one box over loopback, through the lab's byte-transparent relay; not a Usenet conformance audit
- `V0-INN-DUPLICATE-INN`: one INN version on one box over loopback, through the lab's byte-transparent relay; not a Usenet conformance audit
- `V0-INN-DUPLICATE-FN`: one INN version on one box over loopback, through the lab's byte-transparent relay; not a Usenet conformance audit
- `V0-INN-LOOP-INN`: one INN version on one box over loopback, through the lab's byte-transparent relay; not a Usenet conformance audit
- `V0-INN-LOOP-FN`: one INN version on one box over loopback, through the lab's byte-transparent relay; not a Usenet conformance audit
- `V0-INN-RESTART`: one INN version on one box over loopback, through the lab's byte-transparent relay; not a Usenet conformance audit
- `V0-INN-SERVING-AGENT`: fn updates Path and removes Xref once, when it accepts the transfer, and stores what it serves (specs/peering.md 2.3, books/path-update.lisp); the reader path is what this row measures, and the outbound render to a second peer is not exercised by a lab with one peer; one INN version on one box over loopback, through the lab's byte-transparent relay; not a Usenet conformance audit
- `V0-INN-OPERATOR-POST`: one INN version on one box over loopback, through the lab's byte-transparent relay; not a Usenet conformance audit
- `V0-CLIENT-NNTPLIB-A`: one client library, and it reads: nothing here is posted or fed by a foreign client. Its framing, folding and response parsing are the standard library's, not fn's, which is the point of the row
- `V0-CLIENT-NNTPLIB-B`: one client library, and it reads: nothing here is posted or fed by a foreign client. Its framing, folding and response parsing are the standard library's, not fn's, which is the point of the row

### The exact invocation of every row

- `V0-NODE-INIT-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/init/fn.toml init fn.letters`
- `V0-NODE-INIT-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/init/fn.toml init fn.letters`
- `V0-NODE-CONFIG-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/init/fn.toml init fn.letters`
- `V0-NODE-CONFIG-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/init/fn.toml init fn.letters`
- `V0-NODE-REINIT-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/init/fn.toml init fn.letters`
- `V0-NODE-REINIT-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/init/fn.toml init fn.letters`
- `V0-NODE-REINIT-SAFE-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/init/fn.toml init fn.letters
cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PR`
- `V0-NODE-REINIT-SAFE-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/init/fn.toml init fn.letters
cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PR`
- `V0-NODE-STATUS-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml status`
- `V0-NODE-STATUS-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml status`
- `V0-NODE-START-A`: `env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml run`
- `V0-NODE-START-B`: `env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml run`
- `V0-NODE-STOP-A`: `kill -TERM <owner pid> (harness) ; cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml status`
- `V0-NODE-STOP-B`: `kill -TERM <owner pid> (harness) ; cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml status`
- `V0-NODE-LOOPBACK`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; mkdir -p $HOME/fn-deploy/native-c3420013-e8f4faa/loopback && env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native store $HOME/fn-deploy/native-c3420013-e8f4faa/loopback/store init fn.letters && printf '...`
- `V0-NODE-PROFILE`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; mkdir -p $HOME/fn-deploy/native-c3420013-e8f4faa/a/profile && rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/profile/service.log && env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native store $HOME/fn-d...`
- `V0-OUT-ACCEPTED-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml post --message-id '<alpha@a.example.invalid>' --payload $HOME/fn-deploy/native-c34200...`
- `V0-OUT-ACCEPTED-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml post --message-id '<beta@b.example.invalid>' --payload $HOME/fn-deploy/native-c342001...`
- `V0-OUT-REFUSED-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml post --message-id '<alpha@a.example.invalid>' --payload $HOME/fn-deploy/native-c34200...`
- `V0-OUT-REFUSED-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml post --message-id '<beta@b.example.invalid>' --payload $HOME/fn-deploy/native-c342001...`
- `V0-OUT-UNCERTAIN-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/init/fn.toml post --message-id '<init-a@example.invalid>' --payload $HOME/fn-deploy/native-c342001...`
- `V0-OUT-UNCERTAIN-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/init/fn.toml post --message-id '<init-b@example.invalid>' --payload $HOME/fn-deploy/native-c342001...`
- `V0-OUT-RECOVER-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/init/fn.toml recover`
- `V0-OUT-RECOVER-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/init/fn.toml recover`
- `V0-GROUP-CREATE-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml group create fn.matrix`
- `V0-GROUP-CREATE-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml group create fn.matrix`
- `V0-GROUP-SERVED-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py presence --port 11190 --groups fn.matrix`
- `V0-GROUP-SERVED-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py presence --port 11191 --groups fn.matrix`
- `V0-GROUP-RETIRE-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml group retire fn.matrix.throwaway`
- `V0-GROUP-RETIRE-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml group retire fn.matrix.throwaway`
- `V0-GROUP-UNKNOWN-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml group retire fn.not.served`
- `V0-GROUP-UNKNOWN-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml group retire fn.not.served`
- `V0-CAP-SET-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/capacity/fn.toml capacity 64`
- `V0-CAP-SET-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/capacity/fn.toml capacity 64`
- `V0-CAP-REFUSE-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/capacity/fn.toml post --message-id '<capacity-a@example.invalid>' --payload $HOME/fn-deploy/native...`
- `V0-CAP-REFUSE-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/capacity/fn.toml post --message-id '<capacity-b@example.invalid>' --payload $HOME/fn-deploy/native...`
- `V0-PEER-ADD-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml peer add b b.gate.example.invalid 127.0.0.1 11191 'fn.*' - 127.0.0.1 true`
- `V0-PEER-ADD-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml peer add a a.gate.example.invalid 127.0.0.1 11190 'fn.*' - 127.0.0.1 true`
- `V0-PEER-LIST-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml peer list`
- `V0-PEER-LIST-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml peer list`
- `V0-PEER-ABSENT`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml peer remove no-such-peer`
- `V0-PEER-REMOVE`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml peer remove b`
- `V0-CFG-LIVE`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml group create fn.matrix.live
cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; pytho`
- `V0-CFG-LIVE-REFUSE`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/offline/fn.toml group create fn.matrix.offline`
- `V0-AUTH-NEW`: `packaging/fn-native operator CONFIG principal new --seed FILE`
- `V0-AUTH-PASSWORD-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; timeout 120 env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml principal set-password matrix < $HOME/fn-deploy/native-c3420013-e8f4faa/g...`
- `V0-AUTH-PASSWORD-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; timeout 120 env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml principal set-password matrix < $HOME/fn-deploy/native-c3420013-e8f4faa/g...`
- `V0-AUTH-LIST-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml principal list`
- `V0-AUTH-LIST-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml principal list`
- `V0-AUTH-ADVERTISED-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-ADVERTISED-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
- `V0-AUTH-GATED-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py auth --port 11292 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret --msgid '<auth-gate-a@example.invalid>'`
- `V0-AUTH-GATED-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py auth --port 11293 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret --msgid '<auth-gate-b@example.invalid>'`
- `V0-AUTH-LOGIN-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-LOGIN-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
- `V0-AUTH-WITHDRAWN-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-WITHDRAWN-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
- `V0-AUTH-POST-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-POST-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
- `V0-AUTH-WRONG-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-WRONG-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
- `V0-POST-OPEN-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --user '' --secret ''`
- `V0-POST-OPEN-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --user '' --secret ''`
- `V0-POST-COMMIT-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --user '' --secret ''`
- `V0-POST-COMMIT-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --user '' --secret ''`
- `V0-POST-READBACK-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --user '' --secret ''`
- `V0-POST-READBACK-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --user '' --secret ''`
- `V0-POST-FRESH-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --user '' --secret ''`
- `V0-POST-FRESH-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --user '' --secret ''`
- `V0-POST-DUPLICATE-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --user '' --secret ''`
- `V0-POST-DUPLICATE-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --user '' --secret ''`
- `V0-POST-CLOCK-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --user '' --secret ''`
- `V0-POST-CLOCK-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --user '' --secret ''`
- `V0-POST-FROM-MAILBOX-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --user '' --secret ''`
- `V0-POST-FROM-MAILBOX-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --user '' --secret ''`
- `V0-POST-CONCURRENT`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py concurrent --port 11190 --group fn.letters --msgid '<concurrent@example.invalid>' --user '' --secret ''`
- `V0-READ-CAPABILITIES-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-CAPABILITIES-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-MODE-READER-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-MODE-READER-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-WILDMAT-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-WILDMAT-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-OVERVIEW-FMT-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-OVERVIEW-FMT-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-TIMES-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-TIMES-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-HEADERS-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-HEADERS-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-GROUP-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-GROUP-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LISTGROUP-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LISTGROUP-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HEAD-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HEAD-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-BODY-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-BODY-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-STAT-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-STAT-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-MSGID-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-MSGID-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-ABSENT-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-ABSENT-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-RANGE-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-RANGE-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HDR-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HDR-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XOVER-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XOVER-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XHDR-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XHDR-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XPAT-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XPAT-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEXT-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEXT-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LAST-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LAST-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-STAMP-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-STAMP-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-FUTURE-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-FUTURE-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-SYNTAX-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-SYNTAX-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-DATE-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-DATE-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HELP-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HELP-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-UNKNOWN-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-UNKNOWN-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-FRAMING-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-FRAMING-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-PIN-DISPATCHED-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py pins --port 11190 --group fn.letters --user '' --secret ''`
- `V0-PIN-DISPATCHED-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py pins --port 11191 --group fn.letters --user '' --secret ''`
- `V0-PIN-ADVERTISED-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py pins --port 11190 --group fn.letters --user '' --secret ''`
- `V0-PIN-ADVERTISED-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py pins --port 11191 --group fn.letters --user '' --secret ''`
- `V0-TRANSIT-IDENTITY-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml policy set path-identity a.gate.example.invalid`
- `V0-TRANSIT-IDENTITY-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml policy set path-identity b.gate.example.invalid`
- `V0-TRANSIT-INDEPENDENT-A`: `(none)`
- `V0-TRANSIT-INDEPENDENT-B`: `(none)`
- `V0-TRANSIT-MODE-STREAM-AB`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-MODE-STREAM-BA`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-OFFER-AB`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-OFFER-BA`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-TRANSFER-AB`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-TRANSFER-BA`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-IDENTICAL-AB`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-IDENTICAL-BA`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-DUPLICATE-AB`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-DUPLICATE-BA`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-LOOP-AB`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-LOOP-BA`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-LOOP-ABSENT-AB`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-LOOP-ABSENT-BA`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-CHECK-FRESH-AB`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py stream --from-port 11190 --to-port 11191 --msgid '<stream-a@example.invalid>'`
- `V0-TRANSIT-CHECK-FRESH-BA`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py stream --from-port 11191 --to-port 11190 --msgid '<stream-b@example.invalid>'`
- `V0-TRANSIT-TAKETHIS-AB`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py stream --from-port 11190 --to-port 11191 --msgid '<stream-a@example.invalid>'`
- `V0-TRANSIT-TAKETHIS-BA`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py stream --from-port 11191 --to-port 11190 --msgid '<stream-b@example.invalid>'`
- `V0-TRANSIT-CHECK-DUP-AB`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-CHECK-DUP-BA`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-TAKETHIS-DUP-AB`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-TAKETHIS-DUP-BA`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-TLS-AB`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; image=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; runtime_path=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl ; test -x "$runtime_path" || exi...`
- `V0-TRANSIT-TLS-BA`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; image=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; runtime_path=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl ; test -x "$runtime_path" || exi...`
- `V0-TRANSIT-AUTHINFO-AB`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; image=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; runtime_path=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl ; test -x "$runtime_path" || exi...`
- `V0-TRANSIT-AUTHINFO-BA`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; image=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; runtime_path=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl ; test -x "$runtime_path" || exi...`
- `V0-TRANSIT-TLS-WRONG-ANCHOR`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; image=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; runtime_path=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl ; test -x "$runtime_path" || exi...`
- `V0-TRANSIT-AUTHINFO-WRONG`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; image=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; runtime_path=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl ; test -x "$runtime_path" || exi...`
- `V0-FEED-QUEUE`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; image=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_before=$(digest "$image.core"...`
- `V0-FEED-OFFER`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; image=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_before=$(digest "$image.core"...`
- `V0-FEED-ONCE`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; image=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; runtime_path=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl ; test -x "$runtime_path" || exi...`
- `V0-FEED-JOURNAL`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; image=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_before=$(digest "$image.core"...`
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
- `V0-INN-INTEROP`: `/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/ember/dev/fn/build/lanes/qual-c3420013/tools/inn_lab.py e8f4faa5152f32821b3554c680483769a75b0b9b --host hbox --native-image /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host --native-openssl-prefix /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl --evidence /Users/ember/dev/fn/build/lanes/qual-c3420013/plannin`
- `V0-INN-FEED-OUT`: `/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/ember/dev/fn/build/lanes/qual-c3420013/tools/inn_lab.py e8f4faa5152f32821b3554c680483769a75b0b9b --host hbox --native-image /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host --native-openssl-prefix /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl --evidence /Users/ember/dev/fn/build/lanes/qual-c3420013/plannin`
- `V0-INN-FEED-IN`: `/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/ember/dev/fn/build/lanes/qual-c3420013/tools/inn_lab.py e8f4faa5152f32821b3554c680483769a75b0b9b --host hbox --native-image /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host --native-openssl-prefix /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl --evidence /Users/ember/dev/fn/build/lanes/qual-c3420013/plannin`
- `V0-INN-DUPLICATE-INN`: `/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/ember/dev/fn/build/lanes/qual-c3420013/tools/inn_lab.py e8f4faa5152f32821b3554c680483769a75b0b9b --host hbox --native-image /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host --native-openssl-prefix /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl --evidence /Users/ember/dev/fn/build/lanes/qual-c3420013/plannin`
- `V0-INN-DUPLICATE-FN`: `/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/ember/dev/fn/build/lanes/qual-c3420013/tools/inn_lab.py e8f4faa5152f32821b3554c680483769a75b0b9b --host hbox --native-image /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host --native-openssl-prefix /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl --evidence /Users/ember/dev/fn/build/lanes/qual-c3420013/plannin`
- `V0-INN-LOOP-INN`: `/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/ember/dev/fn/build/lanes/qual-c3420013/tools/inn_lab.py e8f4faa5152f32821b3554c680483769a75b0b9b --host hbox --native-image /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host --native-openssl-prefix /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl --evidence /Users/ember/dev/fn/build/lanes/qual-c3420013/plannin`
- `V0-INN-LOOP-FN`: `/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/ember/dev/fn/build/lanes/qual-c3420013/tools/inn_lab.py e8f4faa5152f32821b3554c680483769a75b0b9b --host hbox --native-image /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host --native-openssl-prefix /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl --evidence /Users/ember/dev/fn/build/lanes/qual-c3420013/plannin`
- `V0-INN-RESTART`: `/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/ember/dev/fn/build/lanes/qual-c3420013/tools/inn_lab.py e8f4faa5152f32821b3554c680483769a75b0b9b --host hbox --native-image /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host --native-openssl-prefix /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl --evidence /Users/ember/dev/fn/build/lanes/qual-c3420013/plannin`
- `V0-INN-SERVING-AGENT`: `/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/ember/dev/fn/build/lanes/qual-c3420013/tools/inn_lab.py e8f4faa5152f32821b3554c680483769a75b0b9b --host hbox --native-image /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host --native-openssl-prefix /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl --evidence /Users/ember/dev/fn/build/lanes/qual-c3420013/plannin`
- `V0-INN-OPERATOR-POST`: `/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/ember/dev/fn/build/lanes/qual-c3420013/tools/inn_lab.py e8f4faa5152f32821b3554c680483769a75b0b9b --host hbox --native-image /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host --native-openssl-prefix /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl --evidence /Users/ember/dev/fn/build/lanes/qual-c3420013/plannin`
- `V0-CLIENT-NNTPLIB-A`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3.12 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/independent.py --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>' --user '' --secret ''`
- `V0-CLIENT-NNTPLIB-B`: `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3.12 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/independent.py --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>' --user '' --secret ''`
- `V0-CLIENT-SLRN`: `slrn -h <host> -p <port>`

## Every command

| # | step | rc | first line | s |
| --- | --- | --- | --- | --- |
| 1 | preflight | 0 | `os=Ubuntu 24.10 kernel=Linux 6.11.0-29-generic arch=x86_64 cores=24` | 3.9 |
| 2 | acquire deploy lock | 0 | `` | 0.4 |
| 3 | ship archive | 0 | `` | 8.1 |
| 4 | make run dir | 0 | `` | 0.3 |
| 5 | install drive.py | 0 | `` | 0.3 |
| 6 | install feed.py | 0 | `` | 0.4 |
| 7 | install matrix.py | 0 | `` | 0.5 |
| 8 | native packaged operator subject | 0 | `NATIVE-LAUNCHER-DIGEST ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142` | 0.6 |
| 9 | node A native run directory | 0 | `` | 0.3 |
| 10 | node A native config exists | 0 | `` | 0.3 |
| 11 | node A native operator status | 0 | `transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment` | 0.5 |
| 12 | node B native run directory | 0 | `` | 0.5 |
| 13 | node B native config exists | 0 | `` | 0.5 |
| 14 | node B native operator status | 0 | `transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment` | 0.6 |
| 15 | loopback refusal: scratch store | 0 | `initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/loopback/store` | 0.4 |
| 16 | loopback refusal: run | 5 | `usage operator request (CONFIGURATION INVALID)` | 0.4 |
| 17 | node A profile scratch store | 0 | `initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/a/profile/store` | 0.4 |
| 18 | node A profile agent refusal | 5 | `usage operator run (UNSUPPORTED-PROFILE agent)` | 0.5 |
| 19 | start server (node A profile owner, profile-a) | 0 | `LISTENING 11297` | 1.4 |
| 20 | install profile.article | 0 | `` | 0.4 |
| 21 | node A profile post | 0 | `accepted operator post ACCEPTED` | 0.5 |
| 22 | stop server profile-a | 0 | `stopped` | 1.4 |
| 23 | node A profile service log | 0 | `accepted post path=control message-id=<profile-a@example.invalid> time=2026-09-25T00:42:20Z` | 0.3 |
| 24 | node A init scratch configuration | 0 | `MATRIX-CONFIG-STORE /home/hbox/fn-deploy/native-c3420013-e8f4faa/a/init/store` | 0.5 |
| 25 | node A operator init | 0 | `initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/a/init/store` | 0.6 |
| 26 | start server (node A init owner, init-a) | 0 | `LISTENING 11295` | 1.5 |
| 27 | install init.article | 0 | `` | 0.4 |
| 28 | node A submission to the init scratch owner | 3 | `uncertain operator post UNCERTAIN` | 0.5 |
| 29 | stop server init-a | 0 | `stopped` | 0.6 |
| 30 | node A recover the init scratch store | 0 | `recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none` | 1.5 |
| 31 | node A second operator init | 1 | `refused operator init STORE-EXISTS` | 1.1 |
| 32 | node A recover after the second init | 0 | `recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none` | 1.6 |
| 33 | node B init scratch configuration | 0 | `MATRIX-CONFIG-STORE /home/hbox/fn-deploy/native-c3420013-e8f4faa/b/init/store` | 1.0 |
| 34 | node B operator init | 0 | `initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/b/init/store` | 0.6 |
| 35 | start server (node B init owner, init-b) | 0 | `LISTENING 11296` | 1.6 |
| 36 | install init.article | 0 | `` | 0.5 |
| 37 | node B submission to the init scratch owner | 3 | `uncertain operator post UNCERTAIN` | 0.6 |
| 38 | stop server init-b | 0 | `stopped` | 0.5 |
| 39 | node B recover the init scratch store | 0 | `recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none` | 0.7 |
| 40 | node B second operator init | 1 | `refused operator init STORE-EXISTS` | 0.5 |
| 41 | node B recover after the second init | 0 | `recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none` | 0.5 |
| 42 | node A group create fn.matrix | 0 | `configured generation=2 record=00000002.cfg verification=VERIFIED` | 0.7 |
| 43 | node A group create fn.matrix.throwaway | 0 | `configured generation=3 record=00000003.cfg verification=VERIFIED` | 0.7 |
| 44 | node A group retire fn.matrix.throwaway | 0 | `configured generation=4 record=00000004.cfg verification=VERIFIED` | 0.7 |
| 45 | node A group retire an unserved group | 1 | `refused operator group administrative configuration refused: NO-SUCH-GROUP` | 0.5 |
| 46 | node A capacity scratch store | 0 | `initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/a/capacity/store` | 0.5 |
| 47 | node A capacity 64 | 0 | `configured generation=2 record=00000002.cfg verification=VERIFIED` | 0.5 |
| 48 | node A capacity 1 | 0 | `configured generation=3 record=00000003.cfg verification=VERIFIED` | 0.7 |
| 49 | node A capacity owner config | 0 | `` | 0.4 |
| 50 | start server (node A capacity owner, capacity-a) | 0 | `LISTENING 11290` | 1.5 |
| 51 | install capacity.article | 0 | `` | 0.5 |
| 52 | node A post beyond the capacity | 1 | `refused operator post REFUSED` | 0.5 |
| 53 | stop server capacity-a | 0 | `stopped` | 1.6 |
| 54 | native AUTHINFO secret | 0 | `SECRET-READY` | 0.6 |
| 55 | node A principal set-password matrix | 0 | `matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.7 |
| 56 | node A principal list | 0 | `matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.5 |
| 57 | node A auth-required scratch store | 0 | `initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/a/authgate/store` | 0.5 |
| 58 | node A auth-required scratch credential | 0 | `matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.5 |
| 59 | start server (node A auth-required owner, authgate-a) | 0 | `LISTENING 11292` | 1.4 |
| 60 | node A auth-required AUTHINFO gate | 0 | `{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BE` | 0.5 |
| 61 | stop server authgate-a | 0 | `stopped` | 1.4 |
| 62 | node B group create fn.matrix | 0 | `configured generation=2 record=00000002.cfg verification=VERIFIED` | 0.6 |
| 63 | node B group create fn.matrix.throwaway | 0 | `configured generation=3 record=00000003.cfg verification=VERIFIED` | 0.7 |
| 64 | node B group retire fn.matrix.throwaway | 0 | `configured generation=4 record=00000004.cfg verification=VERIFIED` | 0.7 |
| 65 | node B group retire an unserved group | 1 | `refused operator group administrative configuration refused: NO-SUCH-GROUP` | 0.6 |
| 66 | node B capacity scratch store | 0 | `initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/b/capacity/store` | 0.6 |
| 67 | node B capacity 64 | 0 | `configured generation=2 record=00000002.cfg verification=VERIFIED` | 0.6 |
| 68 | node B capacity 1 | 0 | `configured generation=3 record=00000003.cfg verification=VERIFIED` | 0.7 |
| 69 | node B capacity owner config | 0 | `` | 0.5 |
| 70 | start server (node B capacity owner, capacity-b) | 0 | `LISTENING 11291` | 1.6 |
| 71 | install capacity.article | 0 | `` | 0.5 |
| 72 | node B post beyond the capacity | 1 | `refused operator post REFUSED` | 0.7 |
| 73 | stop server capacity-b | 0 | `stopped` | 1.4 |
| 74 | node B principal set-password matrix | 0 | `Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.6 |
| 75 | node B principal list | 0 | `matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.4 |
| 76 | node B auth-required scratch store | 0 | `initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/b/authgate/store` | 0.5 |
| 77 | node B auth-required scratch credential | 0 | `matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.5 |
| 78 | start server (node B auth-required owner, authgate-b) | 0 | `LISTENING 11293` | 1.4 |
| 79 | node B auth-required AUTHINFO gate | 0 | `{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BE` | 0.5 |
| 80 | stop server authgate-b | 0 | `stopped` | 1.5 |
| 81 | node A path-identity | 0 | `configured generation=5 record=00000005.cfg verification=VERIFIED` | 0.6 |
| 82 | node B path-identity | 0 | `configured generation=5 record=00000005.cfg verification=VERIFIED` | 0.6 |
| 83 | node B configured port | 0 | `11191` | 0.4 |
| 84 | node A peer record for B | 0 | `configured generation=6 record=00000006.cfg verification=VERIFIED` | 0.6 |
| 85 | node A lists its peers | 0 | `b path-identity=b.gate.example.invalid address=127.0.0.1 port=11191 security=clear inbound=fn.* outbound=- auth=source-address:127.0.0.1` | 0.6 |
| 86 | node A configured port | 0 | `11190` | 0.5 |
| 87 | node B peer record for A | 0 | `configured generation=6 record=00000006.cfg verification=VERIFIED` | 0.6 |
| 88 | node B lists its peers | 0 | `a path-identity=a.gate.example.invalid address=127.0.0.1 port=11190 security=clear inbound=fn.* outbound=- auth=source-address:127.0.0.1` | 0.6 |
| 89 | start server (node A (native-operator), a-main) | 0 | `LISTENING 11190` | 1.4 |
| 90 | node A pid | 0 | `2258595` | 0.4 |
| 91 | start server (node B (native-operator), b-main) | 0 | `LISTENING 11191` | 1.4 |
| 92 | node B pid | 0 | `2258733` | 0.4 |
| 93 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 94 | node A serves fn.matrix | 0 | `{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}` | 0.4 |
| 95 | node A server is alive | 0 | `ALIVE` | 0.4 |
| 96 | node A POST cycle | 0 | `{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-507` | 0.6 |
| 97 | node A server is alive | 0 | `ALIVE` | 0.4 |
| 98 | node A reader surface | 0 | `{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE AC` | 0.8 |
| 99 | node A server is alive | 0 | `ALIVE` | 0.4 |
| 100 | node A AUTHINFO session | 0 | `{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "AUTHIN` | 0.6 |
| 101 | node A server is alive | 0 | `ALIVE` | 0.5 |
| 102 | install alpha.article | 0 | `` | 0.4 |
| 103 | node A outcome accepted | 0 | `accepted operator post ACCEPTED` | 0.7 |
| 104 | install alpha.article | 0 | `` | 0.4 |
| 105 | node A outcome duplicate | 0 | `accepted operator post DUPLICATE` | 0.5 |
| 106 | install alpha-conflict.article | 0 | `` | 0.3 |
| 107 | node A outcome refused | 1 | `refused operator post REFUSED` | 0.5 |
| 108 | install stream-a.article | 0 | `` | 0.4 |
| 109 | node A seed <stream-a@example.invalid> | 0 | `accepted operator post ACCEPTED` | 0.8 |
| 110 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 111 | node B serves fn.matrix | 0 | `{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}` | 0.4 |
| 112 | node B server is alive | 0 | `ALIVE` | 0.4 |
| 113 | node B POST cycle | 0 | `{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-41a` | 0.6 |
| 114 | node B server is alive | 0 | `ALIVE` | 0.4 |
| 115 | node B reader surface | 0 | `{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE AC` | 0.9 |
| 116 | node B server is alive | 0 | `ALIVE` | 0.4 |
| 117 | node B AUTHINFO session | 0 | `{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "AUTHIN` | 1.4 |
| 118 | node B server is alive | 0 | `ALIVE` | 0.9 |
| 119 | install beta.article | 0 | `` | 0.5 |
| 120 | node B outcome accepted | 0 | `accepted operator post ACCEPTED` | 1.0 |
| 121 | install beta.article | 0 | `` | 0.6 |
| 122 | node B outcome duplicate | 0 | `accepted operator post DUPLICATE` | 0.5 |
| 123 | install beta-conflict.article | 0 | `` | 0.4 |
| 124 | node B outcome refused | 1 | `refused operator post REFUSED` | 0.5 |
| 125 | install stream-b.article | 0 | `` | 0.4 |
| 126 | node B seed <stream-b@example.invalid> | 0 | `accepted operator post ACCEPTED` | 0.6 |
| 127 | node A server is alive | 0 | `ALIVE` | 0.4 |
| 128 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 129 | nntplib interpreter | 0 | `USE python3.12` | 0.3 |
| 130 | install independent.py | 0 | `` | 0.4 |
| 131 | independent nntplib client on node A | 0 | `/home/hbox/fn-deploy/native-c3420013-e8f4faa/gate-run/independent.py:6: DeprecationWarning: 'nntplib' is deprecated and slated for removal in Python 3.13` | 0.4 |
| 132 | independent nntplib client on node B | 0 | `/home/hbox/fn-deploy/native-c3420013-e8f4faa/gate-run/independent.py:6: DeprecationWarning: 'nntplib' is deprecated and slated for removal in Python 3.13` | 0.5 |
| 133 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 134 | transit AB: offer <alpha@a.example.invalid> from A to B | 1 | `{"msgid": "<alpha@a.example.invalid>", "source": "220 0 <alpha@a.example.invalid> article follows", "source_lines": 9, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "` | 0.7 |
| 135 | transit AB: CHECK/TAKETHIS <stream-a@example.invalid> from A to B | 1 | `{"SOURCE": "220 0 <stream-a@example.invalid> article follows", "MODE STREAM": "203 streaming permitted", "CHECK": "238 <stream-a@example.invalid>", "TAKETHIS": "239 <stream-a@example.invalid>", "CHECK` | 0.6 |
| 136 | node A server is alive | 0 | `ALIVE` | 0.4 |
| 137 | transit BA: offer <beta@b.example.invalid> from B to A | 1 | `{"msgid": "<beta@b.example.invalid>", "source": "220 0 <beta@b.example.invalid> article follows", "source_lines": 9, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LI` | 0.5 |
| 138 | transit BA: CHECK/TAKETHIS <stream-b@example.invalid> from B to A | 1 | `{"SOURCE": "220 0 <stream-b@example.invalid> article follows", "MODE STREAM": "203 streaming permitted", "CHECK": "238 <stream-b@example.invalid>", "TAKETHIS": "239 <stream-b@example.invalid>", "CHECK` | 0.7 |
| 139 | node A server is alive | 0 | `ALIVE` | 0.4 |
| 140 | node A capability pins | 0 | `{"advertised": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "answered": {"READER": "211 6 1 6 fn.letters", "POST": "340 send art` | 0.4 |
| 141 | node B server is alive | 0 | `ALIVE` | 0.4 |
| 142 | node B capability pins | 0 | `{"advertised": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "answered": {"READER": "211 6 1 6 fn.letters", "POST": "340 send art` | 0.5 |
| 143 | node A server is alive | 0 | `ALIVE` | 0.5 |
| 144 | node B server is alive | 0 | `ALIVE` | 0.4 |
| 145 | a second reader across node A's POST | 0 | `{"WATCHER BEFORE": "211 6 1 6 fn.letters", "POST": "340 send article to be posted", "WATCHER MID": "211 6 1 6 fn.letters", "WATCHER ARTICLE MID": "223 1 <native-matrix-50709493a7c8-a@example.invalid> ` | 0.7 |
| 146 | node A server is alive | 0 | `ALIVE` | 0.4 |
| 147 | node B server is alive | 0 | `ALIVE` | 0.4 |
| 148 | live reconfiguration: declare fn.matrix.live on node A | 0 | `accepted operator group` | 0.6 |
| 149 | node A serves fn.matrix.live without a restart | 0 | `{"groups": {"fn.matrix.live": "211 0 1 0 fn.matrix.live"}, "present": {}, "absent": {}, "ok": true}` | 0.4 |
| 150 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 151 | node A configured store | 0 | `/tank/fn/scratch/qual-c3420013/matrix/stores/a/store` | 0.4 |
| 152 | offline configuration over node A's store | 0 | `` | 0.4 |
| 153 | offline group create while the owner holds the store | 1 | `refused operator group store is already locked` | 0.5 |
| 154 | native public peering/restart witness | 0 | `NATIVE-PEERING-EXPECTED-RUNTIME b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5` | 4.8 |
| 155 | native protected peering witness | 0 | `NATIVE-PROTECTED-EXPECTED-RUNTIME b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5` | 44.7 |
| 156 | stop server node A (main) | 0 | `stopped` | 1.5 |
| 157 | node A store after the stop | 0 | `transactions=7 articles=7 staging-orphans=0 unsigned-legacy-experiment` | 0.6 |
| 158 | node A recover after the stop | 0 | `recovered transactions=7 articles=7 staging-orphans=0 anchor=none checkpoint=none` | 0.5 |
| 159 | node A log tail | 0 | `accepted peer connection=34 peer=b time=2026-09-25T00:43:40Z` | 0.5 |
| 160 | stop server node B (main) | 0 | `stopped` | 1.4 |
| 161 | node B store after the stop | 0 | `transactions=6 articles=6 staging-orphans=0 unsigned-legacy-experiment` | 0.5 |
| 162 | node B recover after the stop | 0 | `recovered transactions=6 articles=6 staging-orphans=0 anchor=none checkpoint=none` | 0.3 |
| 163 | node B log tail | 0 | `accepted peer connection=30 peer=a time=2026-09-25T00:43:41Z` | 0.4 |
| 164 | peer remove a peer that is not there | 1 | `refused operator peer administrative configuration refused: NO-SUCH-PEER` | 0.5 |
| 165 | peer remove the configured peer | 0 | `configured generation=8 record=00000008.cfg verification=VERIFIED` | 0.6 |
| 166 | inn lab | 1 | `evidence: /Users/ember/dev/fn/build/lanes/qual-c3420013/planning/evidence/v0-runs/20260925T004159.810142Z-e8f4faa-0d8859e35924/inn-lab.md` | 51.4 |
| 167 | stop server node A (main) | 0 | `stopped` | 0.2 |
| 168 | stop the tap in front of node A | 0 | `stopped` | 0.3 |
| 169 | stop server node B (main) | 0 | `stopped` | 0.2 |
| 170 | stop the tap in front of node B | 0 | `stopped` | 0.2 |
| 171 | stray fn processes | 0 | `CLEAN` | 0.3 |
| 172 | release deploy lock | 0 | `` | 0.2 |

### Commands in full

1. **preflight** -- `. /etc/os-release 2>/dev/null || true ; echo "os=${PRETTY_NAME:-unknown} kernel=$(uname -sr) arch=$(uname -m) cores=$(nproc 2>/dev/null || echo ?)" ; echo "python3=$(python3 -V 2>&1)" ; for p in python3.9 python3.10 python3.11 python3.12; do ; command -v $p >/dev/null && echo "alt=$p $($p -V 2>&1)" ; done ; for c in slrn tin nn trn inews expect script; do ; printf 'client %s=%s\n' "$c" "$(comma...`
2. **acquire deploy lock** -- `mkdir -p $HOME/fn-deploy/.locks ; if ! mkdir $HOME/fn-deploy/.locks/native-c3420013-e8f4faa.lock 2>/dev/null; then ; echo "deploy identity is already active: native-c3420013-e8f4faa" ; exit 73 ; fi`
3. **ship archive** -- `git archive e8f4faa | tar -x -C $HOME/fn-deploy/native-c3420013-e8f4faa`
4. **make run dir** -- `mkdir -p $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run`
5. **install drive.py** -- `base64 -d > $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/drive.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJJbmRlcGVuZGVudCBOTlRQIGRyaXZpbmcgZm9yIHRo ; ZSBkZXBsb3kgZ2F0ZTsgbm8gZm4gbW9kdWxlIGlzIGltcG9ydGVkLiIiIgppbXBvcnQgYXJncGFy ; c2UsIGpzb24sIG9zLCBzb2NrZXQsIHN5cywgdGltZQoKCmNsYXNzIENvbm46CiAgICBkZWYgX19p ; bml0X18oc2VsZiwgcG9ydCwgdGltZW91dD0zMCk6CiAgICAgICAgc2VsZi5zb2NrID0gc29j...`
6. **install feed.py** -- `base64 -d > $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJUaGUgdHdvLW5vZGUgcGhhc2VzLiAgTm8gZm4gbW9k ; dWxlIGlzIGltcG9ydGVkOyBDb25uIGlzIGRlcGxveV9nYXRlJ3MuCgpgcHJlc2VuY2VgIGlzIHRo ; ZSBjb250cm9sIGFuZCB0aGUgcmVyZWFkOiB3aGF0IGEgbm9kZSBob2xkcyBhbmQgd2hhdCBpdCBt ; dXN0Cm5vdC4gIGByZWxheWAgaXMgUkZDIDM5NzcgNi4zLjIgZHJpdmVuIGJ5IGhhbmQgb3Zlc...`
7. **install matrix.py** -- `base64 -d > $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJUaGUgdjAgbWF0cml4J3Mgb3duIE5OVFAgcGhhc2Vz ; LiAgTm8gZm4gbW9kdWxlIGlzIGltcG9ydGVkOyBDb25uIGlzCnRvb2xzL2RlcGxveV9nYXRlLnB5 ; J3MgZHJpdmVyLCBzaGlwcGVkIGJlc2lkZSB0aGlzIGZpbGUgYXMgZHJpdmUucHkuCgpFdmVyeSBw ; aGFzZSBwcmludHMgT05FIGpzb24gb2JqZWN0IHdob3NlIGtleXMgYXJlIGNvbW1hbmQgbmF...`
8. **native packaged operator subject** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; image=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host ; wrapper=packaging/fn-native ; runtime=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl ; test -x "$image" || { echo "NATIVE-IMAGE-MISSING $image"; exit 4; } ; test -x "$wrapper" || { echo NATIVE-WRAPPER-MISSING; exit 4; } ; test -s "$image.co...`
9. **node A native run directory** -- `mkdir -p $HOME/fn-deploy/native-c3420013-e8f4faa/a`
10. **node A native config exists** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; test -f /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml`
11. **node A native operator status** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml status`
12. **node B native run directory** -- `mkdir -p $HOME/fn-deploy/native-c3420013-e8f4faa/b`
13. **node B native config exists** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; test -f /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml`
14. **node B native operator status** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml status`
15. **loopback refusal: scratch store** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; mkdir -p $HOME/fn-deploy/native-c3420013-e8f4faa/loopback && env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native store $HOME/fn-deploy/native-c3420013-e8f4faa/loopback/store init fn.letters && printf '...`
16. **loopback refusal: run** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; timeout 60 env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/loopback/fn.toml run`
17. **node A profile scratch store** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; mkdir -p $HOME/fn-deploy/native-c3420013-e8f4faa/a/profile && rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/profile/service.log && env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native store $HOME/fn-d...`
18. **node A profile agent refusal** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; timeout 60 env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/profile/agent.toml run`
19. **start server (node A profile owner, profile-a)** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/profile/server-profile-a.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/profile/fn.to...`
20. **install profile.article** -- `base64 -d > $HOME/fn-deploy/native-c3420013-e8f4faa/a/profile/profile.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IHByb2ZpbGUNCk5ld3Nncm91cHM6 ; IGZuLmxldHRlcnMNCkRhdGU6IEZyaSwgMjUgU2VwIDIwMjYgMDA6NDI6MjAgKzAwMDANCk1lc3Nh ; Z2UtSUQ6IDxwcm9maWxlLWFAZXhhbXBsZS5pbnZhbGlkPg0KDQpUaGUgb3BlcmF0b3IgbG9nIGxp ; bmUgZm9yIHRoaXMgcG9zdC4NCg== ; FN_GATE_EOF ; chmod 644 $HOME/fn-...`
21. **node A profile post** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/profile/fn.toml post --message-id '<profile-a@example.invalid>' --payload $HOME/fn-deploy/native-c...`
22. **stop server profile-a** -- `if [ -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/profile/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-c3420013-e8f4faa/a/profile/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/profile/server.pid ; fi ; echo stopped`
23. **node A profile service log** -- `cat $HOME/fn-deploy/native-c3420013-e8f4faa/a/profile/service.log 2>/dev/null || echo NO-LOG-FILE`
24. **node A init scratch configuration** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; mkdir -p $HOME/fn-deploy/native-c3420013-e8f4faa/a/init && printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = 11295\n[control]\npath = "%s"\n' "$HOME/fn-deploy/native-c3420013-e8f4faa/a/init/store" "$HOME/fn-deploy/native-c3420013-e8f4faa/a/init/control.sock" > $HOME/fn-deploy/native-c3420013-e8f4faa/a/init/fn.toml && prin...`
25. **node A operator init** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/init/fn.toml init fn.letters`
26. **start server (node A init owner, init-a)** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/init/server-init-a.log ; nohup env FN_NATIVE_CONTROL_FAULT=postpublish FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host-developer packaging/fn-native operator $HOME/fn-deploy...`
27. **install init.article** -- `base64 -d > $HOME/fn-deploy/native-c3420013-e8f4faa/a/init/init.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG9uZSBkdXJhYmxlIG91dGNvbWUN ; Ck5ld3Nncm91cHM6IGZuLmxldHRlcnMNCkRhdGU6IEZyaSwgMjUgU2VwIDIwMjYgMDA6NDI6MjUg ; KzAwMDANCk1lc3NhZ2UtSUQ6IDxpbml0LWFAZXhhbXBsZS5pbnZhbGlkPg0KDQpTdWJtaXR0ZWQg ; b24gdGhlIEEgaW5pdCBzY3JhdGNoIG5vZGUgYnkgdGhlIHYwIG1hdHJpeC4NCg== ; FN_...`
28. **node A submission to the init scratch owner** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/init/fn.toml post --message-id '<init-a@example.invalid>' --payload $HOME/fn-deploy/native-c342001...`
29. **stop server init-a** -- `if [ -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/init/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-c3420013-e8f4faa/a/init/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/init/server.pid ; fi ; echo stopped`
30. **node A recover the init scratch store** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/init/fn.toml recover`
31. **node A second operator init** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/init/fn.toml init fn.letters`
32. **node A recover after the second init** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/init/fn.toml recover`
33. **node B init scratch configuration** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; mkdir -p $HOME/fn-deploy/native-c3420013-e8f4faa/b/init && printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = 11296\n[control]\npath = "%s"\n' "$HOME/fn-deploy/native-c3420013-e8f4faa/b/init/store" "$HOME/fn-deploy/native-c3420013-e8f4faa/b/init/control.sock" > $HOME/fn-deploy/native-c3420013-e8f4faa/b/init/fn.toml && prin...`
34. **node B operator init** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/init/fn.toml init fn.letters`
35. **start server (node B init owner, init-b)** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/b/init/server-init-b.log ; nohup env FN_NATIVE_CONTROL_FAULT=postpublish FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host-developer packaging/fn-native operator $HOME/fn-deploy...`
36. **install init.article** -- `base64 -d > $HOME/fn-deploy/native-c3420013-e8f4faa/b/init/init.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG9uZSBkdXJhYmxlIG91dGNvbWUN ; Ck5ld3Nncm91cHM6IGZuLmxldHRlcnMNCkRhdGU6IEZyaSwgMjUgU2VwIDIwMjYgMDA6NDI6MzQg ; KzAwMDANCk1lc3NhZ2UtSUQ6IDxpbml0LWJAZXhhbXBsZS5pbnZhbGlkPg0KDQpTdWJtaXR0ZWQg ; b24gdGhlIEIgaW5pdCBzY3JhdGNoIG5vZGUgYnkgdGhlIHYwIG1hdHJpeC4NCg== ; FN_...`
37. **node B submission to the init scratch owner** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/init/fn.toml post --message-id '<init-b@example.invalid>' --payload $HOME/fn-deploy/native-c342001...`
38. **stop server init-b** -- `if [ -f $HOME/fn-deploy/native-c3420013-e8f4faa/b/init/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-c3420013-e8f4faa/b/init/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/b/init/server.pid ; fi ; echo stopped`
39. **node B recover the init scratch store** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/init/fn.toml recover`
40. **node B second operator init** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/init/fn.toml init fn.letters`
41. **node B recover after the second init** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/init/fn.toml recover`
42. **node A group create fn.matrix** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml group create fn.matrix`
43. **node A group create fn.matrix.throwaway** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml group create fn.matrix.throwaway`
44. **node A group retire fn.matrix.throwaway** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml group retire fn.matrix.throwaway`
45. **node A group retire an unserved group** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml group retire fn.not.served`
46. **node A capacity scratch store** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; mkdir -p $HOME/fn-deploy/native-c3420013-e8f4faa/a/capacity && env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native store $HOME/fn-deploy/native-c3420013-e8f4faa/a/capacity/store init fn.letters && prin...`
47. **node A capacity 64** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/capacity/fn.toml capacity 64`
48. **node A capacity 1** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/capacity/fn.toml capacity 1`
49. **node A capacity owner config** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; printf '[listener]\nhost = "127.0.0.1"\nport = 11290\n[control]\npath = "%s"\n' $HOME/fn-deploy/native-c3420013-e8f4faa/a/capacity/control.sock >> $HOME/fn-deploy/native-c3420013-e8f4faa/a/capacity/fn.toml`
50. **start server (node A capacity owner, capacity-a)** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/capacity/server-capacity-a.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/capacity/fn...`
51. **install capacity.article** -- `base64 -d > $HOME/fn-deploy/native-c3420013-e8f4faa/a/capacity/capacity.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG92ZXIgdGhlIGNhcGFjaXR5DQpO ; ZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBGcmksIDI1IFNlcCAyMDI2IDAwOjQyOjQzICsw ; MDAwDQpNZXNzYWdlLUlEOiA8Y2FwYWNpdHktYUBleGFtcGxlLmludmFsaWQ+DQoNCnh4eHh4eHh4 ; eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eH...`
52. **node A post beyond the capacity** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/capacity/fn.toml post --message-id '<capacity-a@example.invalid>' --payload $HOME/fn-deploy/native...`
53. **stop server capacity-a** -- `if [ -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/capacity/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-c3420013-e8f4faa/a/capacity/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/capacity/server.pid ; fi ; echo stopped`
54. **native AUTHINFO secret** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; umask 077 && od -An -tx1 -N16 /dev/urandom | tr -d ' \n' > $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret && printf '%s\n%s\n' "$(cat $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret)" "$(cat $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret)" > $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secre...`
55. **node A principal set-password matrix** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; timeout 120 env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml principal set-password matrix < $HOME/fn-deploy/native-c3420013-e8f4faa/g...`
56. **node A principal list** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml principal list`
57. **node A auth-required scratch store** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; mkdir -p $HOME/fn-deploy/native-c3420013-e8f4faa/a/authgate && env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native store $HOME/fn-deploy/native-c3420013-e8f4faa/a/authgate/store init fn.letters && prin...`
58. **node A auth-required scratch credential** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; timeout 120 env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/authgate/fn.toml principal set-password matrix < $HOME/fn-deploy/native-c3420013-e8f4f...`
59. **start server (node A auth-required owner, authgate-a)** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/authgate/server-authgate-a.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/authgate/fn...`
60. **node A auth-required AUTHINFO gate** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py auth --port 11292 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret --msgid '<auth-gate-a@example.invalid>'`
61. **stop server authgate-a** -- `if [ -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/authgate/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-c3420013-e8f4faa/a/authgate/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/authgate/server.pid ; fi ; echo stopped`
62. **node B group create fn.matrix** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml group create fn.matrix`
63. **node B group create fn.matrix.throwaway** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml group create fn.matrix.throwaway`
64. **node B group retire fn.matrix.throwaway** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml group retire fn.matrix.throwaway`
65. **node B group retire an unserved group** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml group retire fn.not.served`
66. **node B capacity scratch store** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; mkdir -p $HOME/fn-deploy/native-c3420013-e8f4faa/b/capacity && env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native store $HOME/fn-deploy/native-c3420013-e8f4faa/b/capacity/store init fn.letters && prin...`
67. **node B capacity 64** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/capacity/fn.toml capacity 64`
68. **node B capacity 1** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/capacity/fn.toml capacity 1`
69. **node B capacity owner config** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; printf '[listener]\nhost = "127.0.0.1"\nport = 11291\n[control]\npath = "%s"\n' $HOME/fn-deploy/native-c3420013-e8f4faa/b/capacity/control.sock >> $HOME/fn-deploy/native-c3420013-e8f4faa/b/capacity/fn.toml`
70. **start server (node B capacity owner, capacity-b)** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/b/capacity/server-capacity-b.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/capacity/fn...`
71. **install capacity.article** -- `base64 -d > $HOME/fn-deploy/native-c3420013-e8f4faa/b/capacity/capacity.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG92ZXIgdGhlIGNhcGFjaXR5DQpO ; ZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBGcmksIDI1IFNlcCAyMDI2IDAwOjQyOjU5ICsw ; MDAwDQpNZXNzYWdlLUlEOiA8Y2FwYWNpdHktYkBleGFtcGxlLmludmFsaWQ+DQoNCnh4eHh4eHh4 ; eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eH...`
72. **node B post beyond the capacity** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/capacity/fn.toml post --message-id '<capacity-b@example.invalid>' --payload $HOME/fn-deploy/native...`
73. **stop server capacity-b** -- `if [ -f $HOME/fn-deploy/native-c3420013-e8f4faa/b/capacity/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-c3420013-e8f4faa/b/capacity/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/b/capacity/server.pid ; fi ; echo stopped`
74. **node B principal set-password matrix** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; timeout 120 env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml principal set-password matrix < $HOME/fn-deploy/native-c3420013-e8f4faa/g...`
75. **node B principal list** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml principal list`
76. **node B auth-required scratch store** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; mkdir -p $HOME/fn-deploy/native-c3420013-e8f4faa/b/authgate && env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native store $HOME/fn-deploy/native-c3420013-e8f4faa/b/authgate/store init fn.letters && prin...`
77. **node B auth-required scratch credential** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; timeout 120 env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/authgate/fn.toml principal set-password matrix < $HOME/fn-deploy/native-c3420013-e8f4f...`
78. **start server (node B auth-required owner, authgate-b)** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/b/authgate/server-authgate-b.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/b/authgate/fn...`
79. **node B auth-required AUTHINFO gate** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py auth --port 11293 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret --msgid '<auth-gate-b@example.invalid>'`
80. **stop server authgate-b** -- `if [ -f $HOME/fn-deploy/native-c3420013-e8f4faa/b/authgate/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-c3420013-e8f4faa/b/authgate/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/b/authgate/server.pid ; fi ; echo stopped`
81. **node A path-identity** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml policy set path-identity a.gate.example.invalid`
82. **node B path-identity** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml policy set path-identity b.gate.example.invalid`
83. **node B configured port** -- `sed -n 's/^port *= *\([0-9][0-9]*\).*/\1/p' /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml | head -1`
84. **node A peer record for B** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml peer add b b.gate.example.invalid 127.0.0.1 11191 'fn.*' - 127.0.0.1 true`
85. **node A lists its peers** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml peer list`
86. **node A configured port** -- `sed -n 's/^port *= *\([0-9][0-9]*\).*/\1/p' /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml | head -1`
87. **node B peer record for A** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml peer add a a.gate.example.invalid 127.0.0.1 11190 'fn.*' - 127.0.0.1 true`
88. **node B lists its peers** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml peer list`
89. **start server (node A (native-operator), a-main)** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/server-a-main.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml run > $HOME...`
90. **node A pid** -- `cat $HOME/fn-deploy/native-c3420013-e8f4faa/a/server.pid`
91. **start server (node B (native-operator), b-main)** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/b/server-b-main.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml run > $HOME...`
92. **node B pid** -- `cat $HOME/fn-deploy/native-c3420013-e8f4faa/b/server.pid`
93. **node A server is alive** -- `kill -0 2258595 2>/dev/null && echo ALIVE || echo DEAD`
94. **node A serves fn.matrix** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py presence --port 11190 --groups fn.matrix`
95. **node A server is alive** -- `kill -0 2258595 2>/dev/null && echo ALIVE || echo DEAD`
96. **node A POST cycle** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --user '' --secret ''`
97. **node A server is alive** -- `kill -0 2258595 2>/dev/null && echo ALIVE || echo DEAD`
98. **node A reader surface** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>'`
99. **node A server is alive** -- `kill -0 2258595 2>/dev/null && echo ALIVE || echo DEAD`
100. **node A AUTHINFO session** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
101. **node A server is alive** -- `kill -0 2258595 2>/dev/null && echo ALIVE || echo DEAD`
102. **install alpha.article** -- `base64 -d > $HOME/fn-deploy/native-c3420013-e8f4faa/a/alpha.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; QQ0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogRnJpLCAyNSBTZXAgMjAyNiAwMDo0Mzox ; OSArMDAwMA0KTWVzc2FnZS1JRDogPGFscGhhQGEuZXhhbXBsZS5pbnZhbGlkPg0KDQpXcml0dGVu ; IG9uIG5vZGUgQSBieSB0aGUgdjAgbWF0cml4IHRocm91Z2ggdGhlIG5hdGl2ZSBvcGVyYXRvci...`
103. **node A outcome accepted** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml post --message-id '<alpha@a.example.invalid>' --payload $HOME/fn-deploy/native-c34200...`
104. **install alpha.article** -- `base64 -d > $HOME/fn-deploy/native-c3420013-e8f4faa/a/alpha.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; QQ0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogRnJpLCAyNSBTZXAgMjAyNiAwMDo0Mzox ; OSArMDAwMA0KTWVzc2FnZS1JRDogPGFscGhhQGEuZXhhbXBsZS5pbnZhbGlkPg0KDQpXcml0dGVu ; IG9uIG5vZGUgQSBieSB0aGUgdjAgbWF0cml4IHRocm91Z2ggdGhlIG5hdGl2ZSBvcGVyYXRvci...`
105. **node A outcome duplicate** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml post --message-id '<alpha@a.example.invalid>' --payload $HOME/fn-deploy/native-c34200...`
106. **install alpha-conflict.article** -- `base64 -d > $HOME/fn-deploy/native-c3420013-e8f4faa/a/alpha-conflict.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; QQ0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogRnJpLCAyNSBTZXAgMjAyNiAwMDo0Mzox ; OSArMDAwMA0KTWVzc2FnZS1JRDogPGFscGhhQGEuZXhhbXBsZS5pbnZhbGlkPg0KDQpXcml0dGVu ; IG9uIG5vZGUgQSBieSB0aGUgdjAgbWF0cml4IHRocm91Z2ggdGhlIG5hdGl2ZSBvc...`
107. **node A outcome refused** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml post --message-id '<alpha@a.example.invalid>' --payload $HOME/fn-deploy/native-c34200...`
108. **install stream-a.article** -- `base64 -d > $HOME/fn-deploy/native-c3420013-e8f4faa/a/stream-a.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IGZvciB0aGUgc3RyZWFtaW5nIG9m ; ZmVyDQpOZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBGcmksIDI1IFNlcCAyMDI2IDAwOjQz ; OjIyICswMDAwDQpNZXNzYWdlLUlEOiA8c3RyZWFtLWFAZXhhbXBsZS5pbnZhbGlkPg0KDQpTZWVk ; ZWQgb24gbm9kZSBBIGJ5IHRoZSB2MCBtYXRyaXguDQo= ; FN_GATE_EOF ; chmod 644 ...`
109. **node A seed <stream-a@example.invalid>** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml post --message-id '<stream-a@example.invalid>' --payload $HOME/fn-deploy/native-c3420...`
110. **node B server is alive** -- `kill -0 2258733 2>/dev/null && echo ALIVE || echo DEAD`
111. **node B serves fn.matrix** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py presence --port 11191 --groups fn.matrix`
112. **node B server is alive** -- `kill -0 2258733 2>/dev/null && echo ALIVE || echo DEAD`
113. **node B POST cycle** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --user '' --secret ''`
114. **node B server is alive** -- `kill -0 2258733 2>/dev/null && echo ALIVE || echo DEAD`
115. **node B reader surface** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>'`
116. **node B server is alive** -- `kill -0 2258733 2>/dev/null && echo ALIVE || echo DEAD`
117. **node B AUTHINFO session** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
118. **node B server is alive** -- `kill -0 2258733 2>/dev/null && echo ALIVE || echo DEAD`
119. **install beta.article** -- `base64 -d > $HOME/fn-deploy/native-c3420013-e8f4faa/b/beta.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; Qg0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogRnJpLCAyNSBTZXAgMjAyNiAwMDo0Mzoy ; OSArMDAwMA0KTWVzc2FnZS1JRDogPGJldGFAYi5leGFtcGxlLmludmFsaWQ+DQoNCldyaXR0ZW4g ; b24gbm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXggdGhyb3VnaCB0aGUgbmF0aXZlIG9wZXJhdG9yLg0...`
120. **node B outcome accepted** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml post --message-id '<beta@b.example.invalid>' --payload $HOME/fn-deploy/native-c342001...`
121. **install beta.article** -- `base64 -d > $HOME/fn-deploy/native-c3420013-e8f4faa/b/beta.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; Qg0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogRnJpLCAyNSBTZXAgMjAyNiAwMDo0Mzoy ; OSArMDAwMA0KTWVzc2FnZS1JRDogPGJldGFAYi5leGFtcGxlLmludmFsaWQ+DQoNCldyaXR0ZW4g ; b24gbm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXggdGhyb3VnaCB0aGUgbmF0aXZlIG9wZXJhdG9yLg0...`
122. **node B outcome duplicate** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml post --message-id '<beta@b.example.invalid>' --payload $HOME/fn-deploy/native-c342001...`
123. **install beta-conflict.article** -- `base64 -d > $HOME/fn-deploy/native-c3420013-e8f4faa/b/beta-conflict.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; Qg0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogRnJpLCAyNSBTZXAgMjAyNiAwMDo0Mzoy ; OSArMDAwMA0KTWVzc2FnZS1JRDogPGJldGFAYi5leGFtcGxlLmludmFsaWQ+DQoNCldyaXR0ZW4g ; b24gbm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXggdGhyb3VnaCB0aGUgbmF0aXZlIG9wZX...`
124. **node B outcome refused** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml post --message-id '<beta@b.example.invalid>' --payload $HOME/fn-deploy/native-c342001...`
125. **install stream-b.article** -- `base64 -d > $HOME/fn-deploy/native-c3420013-e8f4faa/b/stream-b.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IGZvciB0aGUgc3RyZWFtaW5nIG9m ; ZmVyDQpOZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBGcmksIDI1IFNlcCAyMDI2IDAwOjQz ; OjMzICswMDAwDQpNZXNzYWdlLUlEOiA8c3RyZWFtLWJAZXhhbXBsZS5pbnZhbGlkPg0KDQpTZWVk ; ZWQgb24gbm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXguDQo= ; FN_GATE_EOF ; chmod 644 ...`
126. **node B seed <stream-b@example.invalid>** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml post --message-id '<stream-b@example.invalid>' --payload $HOME/fn-deploy/native-c3420...`
127. **node A server is alive** -- `kill -0 2258595 2>/dev/null && echo ALIVE || echo DEAD`
128. **node B server is alive** -- `kill -0 2258733 2>/dev/null && echo ALIVE || echo DEAD`
129. **nntplib interpreter** -- `for p in python3.12 python3 ; do command -v $p >/dev/null 2>&1 && $p -c 'import nntplib' 2>/dev/null && { echo USE $p; exit 0; }; done; echo NONE`
130. **install independent.py** -- `base64 -d > $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/independent.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJBIHN0ZGxpYi1ubnRwbGliIHJlYWRlciBhZ2FpbnN0 ; IGEgbGl2ZSBmbiBub2RlLiAgTm8gZm4gbW9kdWxlIGlzIGltcG9ydGVkLAphbmQgbm8gZnJhbWlu ; ZywgZm9sZGluZyBvciByZXNwb25zZSBwYXJzaW5nIGluIHRoaXMgZmlsZSBpcyBmbidzOiBubnRw ; bGliCmRvZXMgYWxsIG9mIGl0LiAgVGhlIGZpeHR1cmUgaXMgcGFzc2VkIGluLCBzby...`
131. **independent nntplib client on node A** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3.12 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/independent.py --port 11190 --group fn.letters --msgid '<native-matrix-50709493a7c8-a@example.invalid>' --absent '<absent@example.invalid>' --user '' --secret ''`
132. **independent nntplib client on node B** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3.12 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/independent.py --port 11191 --group fn.letters --msgid '<native-matrix-41a756d84051-b@example.invalid>' --absent '<absent@example.invalid>' --user '' --secret ''`
133. **node B server is alive** -- `kill -0 2258733 2>/dev/null && echo ALIVE || echo DEAD`
134. **transit AB: offer <alpha@a.example.invalid> from A to B** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
135. **transit AB: CHECK/TAKETHIS <stream-a@example.invalid> from A to B** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py stream --from-port 11190 --to-port 11191 --msgid '<stream-a@example.invalid>'`
136. **node A server is alive** -- `kill -0 2258595 2>/dev/null && echo ALIVE || echo DEAD`
137. **transit BA: offer <beta@b.example.invalid> from B to A** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
138. **transit BA: CHECK/TAKETHIS <stream-b@example.invalid> from B to A** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py stream --from-port 11191 --to-port 11190 --msgid '<stream-b@example.invalid>'`
139. **node A server is alive** -- `kill -0 2258595 2>/dev/null && echo ALIVE || echo DEAD`
140. **node A capability pins** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py pins --port 11190 --group fn.letters --user '' --secret ''`
141. **node B server is alive** -- `kill -0 2258733 2>/dev/null && echo ALIVE || echo DEAD`
142. **node B capability pins** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py pins --port 11191 --group fn.letters --user '' --secret ''`
143. **node A server is alive** -- `kill -0 2258595 2>/dev/null && echo ALIVE || echo DEAD`
144. **node B server is alive** -- `kill -0 2258733 2>/dev/null && echo ALIVE || echo DEAD`
145. **a second reader across node A's POST** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/matrix.py concurrent --port 11190 --group fn.letters --msgid '<concurrent@example.invalid>' --user '' --secret ''`
146. **node A server is alive** -- `kill -0 2258595 2>/dev/null && echo ALIVE || echo DEAD`
147. **node B server is alive** -- `kill -0 2258733 2>/dev/null && echo ALIVE || echo DEAD`
148. **live reconfiguration: declare fn.matrix.live on node A** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml group create fn.matrix.live`
149. **node A serves fn.matrix.live without a restart** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; python3 $HOME/fn-deploy/native-c3420013-e8f4faa/gate-run/feed.py presence --port 11190 --groups fn.matrix.live`
150. **node A server is alive** -- `kill -0 2258595 2>/dev/null && echo ALIVE || echo DEAD`
151. **node A configured store** -- `awk '/^\[/ {t=$0} t=="[store]" && /^path *=/ {sub(/^path *= *"/, ""); sub(/".*$/, ""); print; exit}' /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml`
152. **offline configuration over node A's store** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; mkdir -p $HOME/fn-deploy/native-c3420013-e8f4faa/a/offline && printf '[store]\npath = "%s"\n[control]\npath = "%s"\n' /tank/fn/scratch/qual-c3420013/matrix/stores/a/store "$HOME/fn-deploy/native-c3420013-e8f4faa/a/offline/never-bound.sock" > $HOME/fn-deploy/native-c3420013-e8f4faa/a/offline/fn.toml`
153. **offline group create while the owner holds the store** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator $HOME/fn-deploy/native-c3420013-e8f4faa/a/offline/fn.toml group create fn.matrix.offline`
154. **native public peering/restart witness** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; image=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_before=$(digest "$image.core"...`
155. **native protected peering witness** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; image=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; runtime_path=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl ; test -x "$runtime_path" || exi...`
156. **stop server node A (main)** -- `if [ -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-c3420013-e8f4faa/a/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/server.pid ; fi ; echo stopped`
157. **node A store after the stop** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml status`
158. **node A recover after the stop** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml recover`
159. **node A log tail** -- `tail -12 $HOME/fn-deploy/native-c3420013-e8f4faa/a/server-a-main.log 2>/dev/null || echo NO-LOG`
160. **stop server node B (main)** -- `if [ -f $HOME/fn-deploy/native-c3420013-e8f4faa/b/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-c3420013-e8f4faa/b/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/b/server.pid ; fi ; echo stopped`
161. **node B store after the stop** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml status`
162. **node B recover after the stop** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/b/fn.toml recover`
163. **node B log tail** -- `tail -12 $HOME/fn-deploy/native-c3420013-e8f4faa/b/server-b-main.log 2>/dev/null || echo NO-LOG`
164. **peer remove a peer that is not there** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml peer remove no-such-peer`
165. **peer remove the configured peer** -- `cd $HOME/fn-deploy/native-c3420013-e8f4faa || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host packaging/fn-native operator /tank/fn/scratch/qual-c3420013/matrix/stores/a/fn.toml peer remove b`
166. **inn lab** -- `/opt/homebrew/opt/python@3.14/bin/python3.14 /Users/ember/dev/fn/build/lanes/qual-c3420013/tools/inn_lab.py e8f4faa5152f32821b3554c680483769a75b0b9b --host hbox --native-image /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host --native-openssl-prefix /tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/openssl --evidence /Users/ember/dev/fn/build/lanes/qual-c3420013/planning/evidence/v0-runs/20260925T004159.810142Z-e8f4faa-0d8859e35924/inn-lab.md`
167. **stop server node A (main)** -- `if [ -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-c3420013-e8f4faa/a/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/server.pid ; fi ; echo stopped`
168. **stop the tap in front of node A** -- `if [ -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/tap.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-c3420013-e8f4faa/a/tap.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 10); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/a/tap.pid ; fi ; echo stopped`
169. **stop server node B (main)** -- `if [ -f $HOME/fn-deploy/native-c3420013-e8f4faa/b/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-c3420013-e8f4faa/b/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/b/server.pid ; fi ; echo stopped`
170. **stop the tap in front of node B** -- `if [ -f $HOME/fn-deploy/native-c3420013-e8f4faa/b/tap.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-c3420013-e8f4faa/b/tap.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 10); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-c3420013-e8f4faa/b/tap.pid ; fi ; echo stopped`
171. **stray fn processes** -- `pgrep -f 'fn-deploy/native-c3420013-e8f4faa' >/dev/null 2>&1 && echo STRAY || echo CLEAN`
172. **release deploy lock** -- `rmdir $HOME/fn-deploy/.locks/native-c3420013-e8f4faa.lock`

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
os=Ubuntu 24.10 kernel=Linux 6.11.0-29-generic arch=x86_64 cores=24
python3=Python 3.12.7
alt=python3.12 Python 3.12.7
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
NATIVE-IMAGE-DIGEST 432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505
NATIVE-RUNTIME-DIGEST b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5
NATIVE-CORE-DIGEST 7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8
usage: fn operator CONFIG run [--once]
accepted operator help
--- 9 node A native run directory (rc=0)
--- 10 node A native config exists (rc=0)
--- 11 node A native operator status (rc=0)
transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment
headroom transactions-used=0 transactions-budget=128 charge-reserved=0 charge-capacity=1048576
accepted operator status
--- 12 node B native run directory (rc=0)
--- 13 node B native config exists (rc=0)
--- 14 node B native operator status (rc=0)
transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment
headroom transactions-used=0 transactions-budget=128 charge-reserved=0 charge-capacity=1048576
accepted operator status
--- 15 loopback refusal: scratch store (rc=0)
initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/loopback/store
--- 16 loopback refusal: run (rc=5)
usage operator request (CONFIGURATION INVALID)
--- 17 node A profile scratch store (rc=0)
initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/a/profile/store
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
accepted post path=control message-id=<profile-a@example.invalid> time=2026-09-25T00:42:20Z
--- 24 node A init scratch configuration (rc=0)
MATRIX-CONFIG-STORE /home/hbox/fn-deploy/native-c3420013-e8f4faa/a/init/store
--- 25 node A operator init (rc=0)
initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/a/init/store
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
accepted operator recover
--- 31 node A second operator init (rc=1)
refused operator init STORE-EXISTS
--- 32 node A recover after the second init (rc=0)
recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none
accepted operator recover
--- 33 node B init scratch configuration (rc=0)
MATRIX-CONFIG-STORE /home/hbox/fn-deploy/native-c3420013-e8f4faa/b/init/store
--- 34 node B operator init (rc=0)
initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/b/init/store
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
accepted operator recover
--- 40 node B second operator init (rc=1)
refused operator init STORE-EXISTS
--- 41 node B recover after the second init (rc=0)
recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none
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
initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/a/capacity/store
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
matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true
Password: Confirm password: accepted operator principal set-password restart-required
--- 56 node A principal list (rc=0)
matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true
accepted operator principal list
--- 57 node A auth-required scratch store (rc=0)
initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/a/authgate/store
--- 58 node A auth-required scratch credential (rc=0)
matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true
Password: Confirm password: accepted operator principal set-password restart-required
--- 59 start server (node A auth-required owner, authgate-a) (rc=0)
LISTENING 11292
--- 60 node A auth-required AUTHINFO gate (rc=0)
{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BEFORE": "480 authentication required", "AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "CAPABILITIES AFTER": "101 capability list follows", "advertised_after": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION"], "AUTHINFO WITHDRAWN": true, "POST AFTER": "340 send article to be posted", "POST AFTER COMMIT": "240 article received OK", "AUTHINFO WRONG": "481 authentication failed", "ok": true}
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
initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/b/capacity/store
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
accepted operator principal set-password restart-required
--- 75 node B principal list (rc=0)
matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true
accepted operator principal list
--- 76 node B auth-required scratch store (rc=0)
initialized /home/hbox/fn-deploy/native-c3420013-e8f4faa/b/authgate/store
--- 77 node B auth-required scratch credential (rc=0)
matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true
Password: Confirm password: accepted operator principal set-password restart-required
--- 78 start server (node B auth-required owner, authgate-b) (rc=0)
LISTENING 11293
--- 79 node B auth-required AUTHINFO gate (rc=0)
{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BEFORE": "480 authentication required", "AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "CAPABILITIES AFTER": "101 capability list follows", "advertised_after": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION"], "AUTHINFO WITHDRAWN": true, "POST AFTER": "340 send article to be posted", "POST AFTER COMMIT": "240 article received OK", "AUTHINFO WRONG": "481 authentication failed", "ok": true}
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
2258595
--- 91 start server (node B (native-operator), b-main) (rc=0)
LISTENING 11191
--- 92 node B pid (rc=0)
2258733
--- 93 node A server is alive (rc=0)
ALIVE
--- 94 node A serves fn.matrix (rc=0)
{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}
--- 95 node A server is alive (rc=0)
ALIVE
--- 96 node A POST cycle (rc=0)
{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-50709493a7c8-a@example.invalid> article follows", "DUPLICATE POST": "340 send article to be posted", "DUPLICATE": "441 posting failed; this article is already stored here", "DATE AFTER DUPLICATE": "111 20260925004317", "FROM POST": "340 send article to be posted", "FROM": "441 posting failed; From is not a valid mailbox list", "FROM ARTICLE": "430 no article with that message-id", "counted": true, "ok": true}
--- 97 node A server is alive (rc=0)
ALIVE
--- 98 node A reader surface (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "MODE READER": "200 posting allowed", "LIST ACTIVE": "215 list of active newsgroups follows", "LIST NEWSGROUPS": "215 list of newsgroups follows", "LIST OVERVIEW.FMT": "215 order of fields in overview database", "LIST ACTIVE.TIMES": "215 information follows", "LIST HEADERS": "215 field list follows", "LIST NEWSGROUPS WILDMAT": "215 list of newsgroups follows", "GROUP": "211 1 1 1 fn.letters", "group_count": 1, "group_first": 1, "group_last": 1, "LISTGROUP": "211 1 1 1 fn.letters list follows", "ARTICLE": "220 1 <native-matrix-50709493a7c8-a@example.invalid> article follows", "HEAD": "221 1 <native-matrix-50709493a7c8-a@example.invalid> headers follow", "BODY": "222 1 <native-matrix-50709493a7c8-a@example.invalid> body follows", "STAT": "223 1 <native-matrix-50709493a7c8-a@example.invalid> retrieved", "ARTICLE MSGID": "220 1 <native-matrix-50709493a7c8-a@example.invalid> article follows", "ARTICLE ABSENT": "430 no article with that message-id", "OVER": "224 overview information follows", "OVER RANGE": "224 overview information follows", "HDR": "225 headers follow", "XOVER": "224 overview information follows", "XHDR": "221 header follows", "XPAT": "221 header follows", "NEWNEWS": "230 list of new articles by message-id follows", "NEWNEWS STAMP TARGET": true, "NEWNEWS FUTURE": "230 list of new articles by message-id follows", "NEWNEWS SYNTAX": "501 syntax error", "NEXT": "421 no next article", "LAST": "422 no previous article", "DATE": "111 20260925004317", "HELP": "100 help text follows", "UNKNOWN": "500 command not recognized", "FRAMING": "111 20260925004317", "FRAMING SAME": true, "ok": true}
--- 99 node A server is alive (rc=0)
ALIVE
--- 100 node A AUTHINFO session (rc=0)
{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BEFORE": "340 send article to be posted", "POST BEFORE CLOSE": "441 posting failed; the article is not valid syntax", "AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "CAPABILITIES AFTER": "101 capability list follows", "advertised_after": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING"], "AUTHINFO WITHDRAWN": true, "POST AFTER": "340 send article to be posted", "POST AFTER COMMIT": "240 article received OK", "AUTHINFO WRONG": "481 authentication failed", "ok": true}
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
{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-41a756d84051-b@example.invalid> article follows", "DUPLICATE POST": "340 send article to be posted", "DUPLICATE": "441 posting failed; this article is already stored here", "DATE AFTER DUPLICATE": "111 20260925004325", "FROM POST": "340 send article to be posted", "FROM": "441 posting failed; From is not a valid mailbox list", "FROM ARTICLE": "430 no article with that message-id", "counted": true, "ok": true}
--- 114 node B server is alive (rc=0)
ALIVE
--- 115 node B reader surface (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "MODE READER": "200 posting allowed", "LIST ACTIVE": "215 list of active newsgroups follows", "LIST NEWSGROUPS": "215 list of newsgroups follows", "LIST OVERVIEW.FMT": "215 order of fields in overview database", "LIST ACTIVE.TIMES": "215 information follows", "LIST HEADERS": "215 field list follows", "LIST NEWSGROUPS WILDMAT": "215 list of newsgroups follows", "GROUP": "211 1 1 1 fn.letters", "group_count": 1, "group_first": 1, "group_last": 1, "LISTGROUP": "211 1 1 1 fn.letters list follows", "ARTICLE": "220 1 <native-matrix-41a756d84051-b@example.invalid> article follows", "HEAD": "221 1 <native-matrix-41a756d84051-b@example.invalid> headers follow", "BODY": "222 1 <native-matrix-41a756d84051-b@example.invalid> body follows", "STAT": "223 1 <native-matrix-41a756d84051-b@example.invalid> retrieved", "ARTICLE MSGID": "220 1 <native-matrix-41a756d84051-b@example.invalid> article follows", "ARTICLE ABSENT": "430 no article with that message-id", "OVER": "224 overview information follows", "OVER RANGE": "224 overview information follows", "HDR": "225 headers follow", "XOVER": "224 overview information follows", "XHDR": "221 header follows", "XPAT": "221 header follows", "NEWNEWS": "230 list of new articles by message-id follows", "NEWNEWS STAMP TARGET": true, "NEWNEWS FUTURE": "230 list of new articles by message-id follows", "NEWNEWS SYNTAX": "501 syntax error", "NEXT": "421 no next article", "LAST": "422 no previous article", "DATE": "111 20260925004326", "HELP": "100 help text follows", "UNKNOWN": "500 command not recognized", "FRAMING": "111 20260925004326", "FRAMING SAME": true, "ok": true}
--- 116 node B server is alive (rc=0)
ALIVE
--- 117 node B AUTHINFO session (rc=0)
{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BEFORE": "340 send article to be posted", "POST BEFORE CLOSE": "441 posting failed; the article is not valid syntax", "AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "CAPABILITIES AFTER": "101 capability list follows", "advertised_after": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING"], "AUTHINFO WITHDRAWN": true, "POST AFTER": "340 send article to be posted", "POST AFTER COMMIT": "240 article received OK", "AUTHINFO WRONG": "481 authentication failed", "ok": true}
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
/home/hbox/fn-deploy/native-c3420013-e8f4faa/gate-run/independent.py:6: DeprecationWarning: 'nntplib' is deprecated and slated for removal in Python 3.13
  import argparse, json, nntplib, platform, sys
{"absent": "430 no article with that message-id", "article_has_msgid": true, "article_lines": 10, "body_lines": 1, "capabilities": ["AUTHINFO", "HDR", "IHAVE", "IMPLEMENTATION", "LIST", "NEWNEWS", "OVER", "POST", "READER", "STREAMING", "VERSION"], "client": "stdlib nntplib", "commands": ["CAPABILITIES", "GROUP", "STAT", "ARTICLE", "HEAD", "BODY", "OVER", "LIST", "ARTICLE (absent)", "QUIT"], "group": {"count": 4, "first": 1, "last": 4, "name": "fn.letters"}, "head_lines": 8, "list_groups": ["fn.letters", "fn.matrix", "fn.matrix.throwaway"], "ok": true, "over_rows": 4, "python": "3.12.7", "quit": "205 closing connection", "stat": [1, "<native-matrix-50709493a7c8-a@example.invalid>"], "welcome": "200 fn-nntp experimental server ready"}
--- 132 independent nntplib client on node B (rc=0)
/home/hbox/fn-deploy/native-c3420013-e8f4faa/gate-run/independent.py:6: DeprecationWarning: 'nntplib' is deprecated and slated for removal in Python 3.13
  import argparse, json, nntplib, platform, sys
{"absent": "430 no article with that message-id", "article_has_msgid": true, "article_lines": 10, "body_lines": 1, "capabilities": ["AUTHINFO", "HDR", "IHAVE", "IMPLEMENTATION", "LIST", "NEWNEWS", "OVER", "POST", "READER", "STREAMING", "VERSION"], "client": "stdlib nntplib", "commands": ["CAPABILITIES", "GROUP", "STAT", "ARTICLE", "HEAD", "BODY", "OVER", "LIST", "ARTICLE (absent)", "QUIT"], "group": {"count": 4, "first": 1, "last": 4, "name": "fn.letters"}, "head_lines": 8, "list_groups": ["fn.letters", "fn.matrix", "fn.matrix.throwaway"], "ok": true, "over_rows": 4, "python": "3.12.7", "quit": "205 closing connection", "stat": [1, "<native-matrix-41a756d84051-b@example.invalid>"], "welcome": "200 fn-nntp experimental server ready"}
--- 133 node B server is alive (rc=0)
ALIVE
--- 134 transit AB: offer <alpha@a.example.invalid> from A to B (rc=1)
{"msgid": "<alpha@a.example.invalid>", "source": "220 0 <alpha@a.example.invalid> article follows", "source_lines": 9, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "ihave_advertised": true, "streaming_advertised": true, "mode_stream": "203 streaming permitted", "offer": "335 send it; end with <CR-LF>.<CR-LF>", "transit": true, "transfer": "235 article transferred OK", "duplicate": "435 duplicate", "loop_offer": "335 send it; end with <CR-LF>.<CR-LF>", "loop_result": "437 transfer rejected; path loop", "check_duplicate": "438 <alpha@a.example.invalid>", "takethis_duplicate": "439 <alpha@a.example.invalid>", "check_fresh": "238 <fresh.check@gate.example.invalid>", "reread": "220 0 <alpha@a.example.invalid> article follows", "identical": false, "sent_lines": ["Path: a.gate.example.invalid!not-for-mail", "Injection-Info: a.gate.example.invalid", "From: gate@example.invalid", "Subject: outcome, written on A", "Newsgroups: fn.letters", "Date: Fri, 25 Sep 2026 00:43:19 +0000", "Message-ID: <alpha@a.example.invalid>", "", "Written on node A by the v0 matrix through the native operator."], "reread_lines": ["Path: b.gate.example.invalid!!a.gate.example.invalid!not-for-mail", "Injection-Info: a.gate.example.invalid", "From: gate@example.invalid", "Subject: outcome, written on A", "Newsgroups: fn.letters", "Date: Fri, 25 Sep 2026 00:43:19 +0000", "Message-ID: <alpha@a.example.invalid>", "", "Written on node A by the v0 matrix through the native operator."], "loop_absent": "430 no article with that message-id", "streaming_ok": true, "ok": false}
--- 135 transit AB: CHECK/TAKETHIS <stream-a@example.invalid> from A to B (rc=1)
{"SOURCE": "220 0 <stream-a@example.invalid> article follows", "MODE STREAM": "203 streaming permitted", "CHECK": "238 <stream-a@example.invalid>", "TAKETHIS": "239 <stream-a@example.invalid>", "CHECK AGAIN": "438 <stream-a@example.invalid>", "TAKETHIS AGAIN": "439 <stream-a@example.invalid>", "REREAD": "220 0 <stream-a@example.invalid> article follows", "IDENTICAL": false, "ok": false}
--- 136 node A server is alive (rc=0)
ALIVE
--- 137 transit BA: offer <beta@b.example.invalid> from B to A (rc=1)
{"msgid": "<beta@b.example.invalid>", "source": "220 0 <beta@b.example.invalid> article follows", "source_lines": 9, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "ihave_advertised": true, "streaming_advertised": true, "mode_stream": "203 streaming permitted", "offer": "335 send it; end with <CR-LF>.<CR-LF>", "transit": true, "transfer": "235 article transferred OK", "duplicate": "435 duplicate", "loop_offer": "335 send it; end with <CR-LF>.<CR-LF>", "loop_result": "437 transfer rejected; path loop", "check_duplicate": "438 <beta@b.example.invalid>", "takethis_duplicate": "439 <beta@b.example.invalid>", "check_fresh": "238 <fresh.check@gate.example.invalid>", "reread": "220 0 <beta@b.example.invalid> article follows", "identical": false, "sent_lines": ["Path: b.gate.example.invalid!not-for-mail", "Injection-Info: b.gate.example.invalid", "From: gate@example.invalid", "Subject: outcome, written on B", "Newsgroups: fn.letters", "Date: Fri, 25 Sep 2026 00:43:29 +0000", "Message-ID: <beta@b.example.invalid>", "", "Written on node B by the v0 matrix through the native operator."], "reread_lines": ["Path: a.gate.example.invalid!!b.gate.example.invalid!not-for-mail", "Injection-Info: b.gate.example.invalid", "From: gate@example.invalid", "Subject: outcome, written on B", "Newsgroups: fn.letters", "Date: Fri, 25 Sep 2026 00:43:29 +0000", "Message-ID: <beta@b.example.invalid>", "", "Written on node B by the v0 matrix through the native operator."], "loop_absent": "430 no article with that message-id", "streaming_ok": true, "ok": false}
--- 138 transit BA: CHECK/TAKETHIS <stream-b@example.invalid> from B to A (rc=1)
{"SOURCE": "220 0 <stream-b@example.invalid> article follows", "MODE STREAM": "203 streaming permitted", "CHECK": "238 <stream-b@example.invalid>", "TAKETHIS": "239 <stream-b@example.invalid>", "CHECK AGAIN": "438 <stream-b@example.invalid>", "TAKETHIS AGAIN": "439 <stream-b@example.invalid>", "REREAD": "220 0 <stream-b@example.invalid> article follows", "IDENTICAL": false, "ok": false}
--- 139 node A server is alive (rc=0)
ALIVE
--- 140 node A capability pins (rc=0)
{"advertised": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "answered": {"READER": "211 6 1 6 fn.letters", "POST": "340 send article to be posted", "POST CLOSE": "441 posting failed; the article is not valid syntax", "IHAVE": "335 send it; end with <CR-LF>.<CR-LF>", "IHAVE CLOSE": "437 transfer rejected; not a valid article", "STREAMING": "203 streaming permitted", "OVER": "412 no newsgroup selected", "HDR": "412 no newsgroup selected", "LIST": "215 list of active newsgroups follows", "NEWNEWS": "230 list of new articles by message-id follows", "AUTHINFO": "381 password required", "STARTTLS": "580 can not initiate TLS negotiation", "MODE-READER": "200 posting allowed", "XOVER": "412 no newsgroup selected", "XHDR": "412 no newsgroup selected", "XPAT": "412 no newsgroup selected", "LISTGROUP": "211 6 1 6 fn.letters list follows", "CHECK": "238 <pin.check@matrix.example.invalid>", "TAKETHIS": "439 <pin.take@matrix.example.invalid>"}, "dispatched": ["READER", "POST", "IHAVE", "STREAMING", "OVER", "HDR", "LIST", "NEWNEWS", "AUTHINFO", "STARTTLS", "MODE-READER", "XOVER", "XHDR", "XPAT", "LISTGROUP", "CHECK", "TAKETHIS"], "login": {}, "advertised_not_dispatched": [], "dispatched_not_advertised": [], "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "ok": true}
--- 141 node B server is alive (rc=0)
ALIVE
--- 142 node B capability pins (rc=0)
{"advertised": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "answered": {"READER": "211 6 1 6 fn.letters", "POST": "340 send article to be posted", "POST CLOSE": "441 posting failed; the article is not valid syntax", "IHAVE": "335 send it; end with <CR-LF>.<CR-LF>", "IHAVE CLOSE": "437 transfer rejected; not a valid article", "STREAMING": "203 streaming permitted", "OVER": "412 no newsgroup selected", "HDR": "412 no newsgroup selected", "LIST": "215 list of active newsgroups follows", "NEWNEWS": "230 list of new articles by message-id follows", "AUTHINFO": "381 password required", "STARTTLS": "580 can not initiate TLS negotiation", "MODE-READER": "200 posting allowed", "XOVER": "412 no newsgroup selected", "XHDR": "412 no newsgroup selected", "XPAT": "412 no newsgroup selected", "LISTGROUP": "211 6 1 6 fn.letters list follows", "CHECK": "238 <pin.check@matrix.example.invalid>", "TAKETHIS": "439 <pin.take@matrix.example.invalid>"}, "dispatched": ["READER", "POST", "IHAVE", "STREAMING", "OVER", "HDR", "LIST", "NEWNEWS", "AUTHINFO", "STARTTLS", "MODE-READER", "XOVER", "XHDR", "XPAT", "LISTGROUP", "CHECK", "TAKETHIS"], "login": {}, "advertised_not_dispatched": [], "dispatched_not_advertised": [], "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "ok": true}
--- 143 node A server is alive (rc=0)
ALIVE
--- 144 node B server is alive (rc=0)
ALIVE
--- 145 a second reader across node A's POST (rc=0)
{"WATCHER BEFORE": "211 6 1 6 fn.letters", "POST": "340 send article to be posted", "WATCHER MID": "211 6 1 6 fn.letters", "WATCHER ARTICLE MID": "223 1 <native-matrix-50709493a7c8-a@example.invalid> retrieved", "COMMIT": "240 article received OK", "WATCHER AFTER": "211 6 1 6 fn.letters", "ok": true}
--- 146 node A server is alive (rc=0)
ALIVE
--- 147 node B server is alive (rc=0)
ALIVE
--- 148 live reconfiguration: declare fn.matrix.live on node A (rc=0)
accepted operator group
--- 149 node A serves fn.matrix.live without a restart (rc=0)
{"groups": {"fn.matrix.live": "211 0 1 0 fn.matrix.live"}, "present": {}, "absent": {}, "ok": true}
--- 150 node A server is alive (rc=0)
ALIVE
--- 151 node A configured store (rc=0)
/tank/fn/scratch/qual-c3420013/matrix/stores/a/store
--- 152 offline configuration over node A's store (rc=0)
--- 153 offline group create while the owner holds the store (rc=1)
refused operator group store is already locked
--- 154 native public peering/restart witness (rc=0)
NATIVE-PEERING-EXPECTED-RUNTIME b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5
NATIVE-PEERING-EXPECTED-CORE 7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8
test_public_native_nodes_exchange_both_ways_and_suppress_duplicate (tests.test_native_peering.NativePeeringTests.test_public_native_nodes_exchange_both_ways_and_suppress_duplicate) ... ok
test_durable_feed_requeues_after_source_process_death (tests.test_native_peering.NativePeeringTests.test_durable_feed_requeues_after_source_process_death) ... ok

----------------------------------------------------------------------
Ran 2 tests in 3.764s

OK
native-peering launcher-sha256=432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505 core-sha256=7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8 declared-source=c34200132b2b0c725a93672fc4ba93a528817e18
NATIVE-PEERING-WITNESS {"feed": {"ab": {"duplicate": "435", "identical": true}, "ba": {"duplicate": "435", "identical": true}}, "identity": {"a": {"core": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host.core", "core_sha256": "7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8", "runtime": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}, "b": {"core": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host.core", "core_sha256": "7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8", "runtime": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}}, "kind": "transit-and-feed", "transit": {"ab": {"duplicate": "435", "identical": true, "offer": "335", "transfer": "235"}, "ba": {"duplicate": "435", "identical": true, "offer": "335", "transfer": "235"}}}
NATIVE-PEERING-WITNESS {"duplicate": "435", "identity": {"restart-a": {"core": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host.core", "core_sha256": "7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8", "runtime": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}, "restart-b": {"core": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host.core", "core_sha256": "7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8", "runtime": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}}, "journal": true, "kind": "requeue-restart", "source_killed": true, "source_restarted": true, "target_identical": true}
--- 155 native protected peering witness (rc=0)
NATIVE-PROTECTED-EXPECTED-RUNTIME b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5
NATIVE-PROTECTED-EXPECTED-CORE 7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8
NATIVE-PROTECTED-EXPECTED-DEVELOPER-CORE b22251d8db73ba46ca77ef8c075ad1d83985ab544183265f413a1faa8039e41e
test_reciprocal_starttls_authinfo_transfer_and_reconnect (tests.test_native_protected_peering.NativeProtectedPeeringTests.test_reciprocal_starttls_authinfo_transfer_and_reconnect) ... native-protected-peering launcher-sha256=432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505 core-sha256=7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8 source=c34200132b2b0c725a93672fc4ba93a528817e18
NATIVE-PROTECTED-WITNESS {"auth": "authinfo", "identity": {"a": {"core": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host.core", "core_sha256": "7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8", "runtime": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}, "b": {"core": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host.core", "core_sha256": "7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8", "runtime": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}}, "kind": "protected-feed", "reconnect": {"ab": {"identical": true}, "ba": {"identical": true}}, "security": "starttls", "target_policy": {"protected_only": true, "required": true}, "transit": {"ab": {"identical": true, "unauthenticated_offer": "502 transit is not permitted on this connection"}, "ba": {"identical": true, "unauthenticated_offer": "502 transit is not permitted on this connection"}}}
ok
test_bad_outbound_password_yields_authenticated_430_observation (tests.test_native_protected_peering.NativeProtectedPeeringTests.test_bad_outbound_password_yields_authenticated_430_observation) ... NATIVE-PROTECTED-WITNESS {"case": "wrong-password", "delivered": false, "identity": {"a": {"core": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host.core", "core_sha256": "7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8", "runtime": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}, "b": {"core": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host.core", "core_sha256": "7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8", "runtime": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}}, "kind": "protected-refusal", "source_alive": true, "target_alive": true}
ok
test_untrusted_certificate_yields_430_and_feed_journal_evidence (tests.test_native_protected_peering.NativeProtectedPeeringTests.test_untrusted_certificate_yields_430_and_feed_journal_evidence) ... NATIVE-PROTECTED-WITNESS {"case": "wrong-anchor", "delivered": false, "identity": {"a": {"core": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host.core", "core_sha256": "7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8", "runtime": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}, "b": {"core": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host.core", "core_sha256": "7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8", "runtime": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}}, "journal": true, "kind": "protected-refusal", "source_alive": true, "target_alive": true}
ok
test_acknowledged_protected_feed_does_not_reoffer_after_source_death (tests.test_native_protected_peering.NativeProtectedPeeringTests.test_acknowledged_protected_feed_does_not_reoffer_after_source_death) ... NATIVE-PROTECTED-WITNESS {"after": {"attempts": 0, "inflight": "nil", "next_attempt": 2, "queue_length": 1, "records": {"feed-commit": 1, "feed-intent": 1, "feed-offer": 1, "feed-outcome": 1, "feed-restart": 2, "feed-sent": 1}, "sent_before_restart": "nil", "state_after_restart": "done", "state_before_restart": "done"}, "auth": "authinfo", "before": {"attempts": 0, "inflight": "nil", "next_attempt": 2, "queue_length": 1, "records": {"feed-commit": 1, "feed-intent": 1, "feed-offer": 1, "feed-outcome": 1, "feed-restart": 1, "feed-sent": 1}, "sent_before_restart": "nil", "state_after_restart": "done", "state_before_restart": "done"}, "identity": {"a": {"core": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host.core", "core_sha256": "7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8", "runtime": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}, "b": {"core": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host.core", "core_sha256": "7a124c6f70e072dbd0a8ade9b29b756bbdad8b821dc801c1f234826b242a9ec8", "runtime": "/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/runtime/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}}, "kind": "feed-once", "recipient_articles": 1, "security": "starttls", "source_killed": true, "source_restarted": true}
ok
--- 156 stop server node A (main) (rc=0)
stopped
--- 157 node A store after the stop (rc=0)
transactions=7 articles=7 staging-orphans=0 unsigned-legacy-experiment
headroom transactions-used=7 transactions-budget=128 charge-reserved=14 charge-capacity=1048576
accepted operator status
--- 158 node A recover after the stop (rc=0)
recovered transactions=7 articles=7 staging-orphans=0 anchor=none checkpoint=none
accepted operator recover
--- 159 node A log tail (rc=0)
accepted peer connection=34 peer=b time=2026-09-25T00:43:40Z
accepted peer connection=35 peer=b time=2026-09-25T00:43:40Z
accepted peer connection=36 peer=b time=2026-09-25T00:43:40Z
accepted peer connection=37 peer=b time=2026-09-25T00:43:40Z
accepted peer connection=38 peer=b time=2026-09-25T00:43:40Z
accepted peer connection=39 peer=b time=2026-09-25T00:43:40Z
refused transit connection=39 message-id=<pin.take@matrix.example.invalid> code=439 decision=refuse reason=proto-article detail=none time=2026-09-25T00:43:40Z
accepted peer connection=40 peer=b time=2026-09-25T00:43:42Z
accepted peer connection=41 peer=b time=2026-09-25T00:43:42Z
accepted post path=served connection=41 message-id=<concurrent@example.invalid> agent=a.gate.example.invalid time=2026-09-25T00:43:42Z
accepted peer connection=43 peer=b time=2026-09-25T00:43:44Z
accepted operator run
--- 160 stop server node B (main) (rc=0)
stopped
--- 161 node B store after the stop (rc=0)
transactions=6 articles=6 staging-orphans=0 unsigned-legacy-experiment
headroom transactions-used=6 transactions-budget=128 charge-reserved=12 charge-capacity=1048576
accepted operator status
--- 162 node B recover after the stop (rc=0)
recovered transactions=6 articles=6 staging-orphans=0 anchor=none checkpoint=none
accepted operator recover
--- 163 node B log tail (rc=0)
accepted peer connection=30 peer=a time=2026-09-25T00:43:41Z
accepted peer connection=31 peer=a time=2026-09-25T00:43:41Z
accepted peer connection=32 peer=a time=2026-09-25T00:43:41Z
accepted peer connection=33 peer=a time=2026-09-25T00:43:41Z
accepted peer connection=34 peer=a time=2026-09-25T00:43:41Z
accepted peer connection=35 peer=a time=2026-09-25T00:43:41Z
accepted peer connection=36 peer=a time=2026-09-25T00:43:41Z
accepted peer connection=37 peer=a time=2026-09-25T00:43:41Z
accepted peer connection=38 peer=a time=2026-09-25T00:43:41Z
accepted peer connection=39 peer=a time=2026-09-25T00:43:41Z
refused transit connection=39 message-id=<pin.take@matrix.example.invalid> code=439 decision=refuse reason=proto-article detail=none time=2026-09-25T00:43:41Z
accepted operator run
--- 164 peer remove a peer that is not there (rc=1)
refused operator peer administrative configuration refused: NO-SUCH-PEER
--- 165 peer remove the configured peer (rc=0)
configured generation=8 record=00000008.cfg verification=VERIFIED
accepted operator peer
--- 166 inn lab (rc=1)
evidence: /Users/ember/dev/fn/build/lanes/qual-c3420013/planning/evidence/v0-runs/20260925T004159.810142Z-e8f4faa-0d8859e35924/inn-lab.md
steps=82 failed=0 not-exercised=0 violated=1 inconclusive=0
verdict=violated findings=held=32 violated=1
  FAILED assertion operator-post-feeds-inn: `operator post` accepted <inn-lab-fn-operator-e8f4faa-20260925T004443Z@example.invalid> (rc=0) and fn's feed offered it to innd, which answered IHAVE: 335 Send it / 235 Article transferred OK. The octets fed carry a `fnA.hbox.test!not-for-mail` Path header. `operator post` is a posting agent's submi
--- 167 stop server node A (main) (rc=0)
stopped
--- 168 stop the tap in front of node A (rc=0)
stopped
--- 169 stop server node B (main) (rc=0)
stopped
--- 170 stop the tap in front of node B (rc=0)
stopped
--- 171 stray fn processes (rc=0)
CLEAN
--- 172 release deploy lock (rc=0)
```
