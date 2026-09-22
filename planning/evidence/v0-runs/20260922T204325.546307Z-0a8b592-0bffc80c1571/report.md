# v0 matrix: 0a8b592 on hbox

v0 is every feature of fn usable between two peered fn nodes. This is that
question asked feature by feature against one commit on one box, with five
verdicts and no pass/fail collapse: accepted, refused and uncertain are the
three outcomes and each is a real observation; not-exercised names what
blocked the row; not-built names the lane that owns the missing feature.
It establishes nothing about the books beyond which certificates ACL2 read.

## What ran

| fact | value |
| --- | --- |
| commit | `0a8b592` (0a8b592b1fa350c8f90e416a188b8e43c0c12afd) |
| tree | `native-dabebb84` |
| host | `hbox` |
| started | 2026-09-22T20:43:25Z |
| wall time | 162.3 s |
| gate tool | `tools/v0_matrix.py` |
| os | Ubuntu 24.10 kernel=Linux 6.11.0-29-generic arch=x86_64 cores=24 |
| python3 | Python 3.12.7 |
| acl2version | + ACL2 Version 8.7                                                     + |
| certificates | not acquired by this slice; it consumes the explicitly named saved image |
| node a | native-operator on port 11190 (main), store $HOME/fn-deploy/native-dabebb84-0a8b592/a/store |
| node b | native-operator on port 11191 (main), store $HOME/fn-deploy/native-dabebb84-0a8b592/b/store |
| server entry point | native-operator |
| three outcomes a | accepted=0 refused=1 uncertain=3 (uncertain is the init scratch node's, not this one's) |
| three outcomes b | accepted=0 refused=1 uncertain=3 (uncertain is the init scratch node's, not this one's) |
| transit | IHAVE -> '335 send it; end with <CR-LF>.<CR-LF>'; CAPABILITIES lists IHAVE: True |
| rows | 206 rows: 126 accepted, 34 refused, 3 uncertain, 38 not exercised, 5 not built, 2 disagreed, 1 faulted |
| alt | python3.12 Python 3.12.7 |
| duplicate resubmission a | identical octets: rc=0 accepted operator post DUPLICATE / different octets under the same Message-ID: rc=1 refused operator post REFUSED |
| duplicate resubmission b | identical octets: rc=0 accepted operator post DUPLICATE / different octets under the same Message-ID: rc=1 refused operator post REFUSED |
| execution backend | native-operator |
| execution image | launcher sha256=ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142; image sha256=21ba38c1a66d96c32c8e50269b852cabd07ae15548306781aafa084cb0e6af32; declared runtime=b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5; sidecar core sha256=6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf (static only before a live-owner witness); source correspondence unestablished |
| execution source | 0a8b592 |
| server | node B (native-operator) on port 11191 (b-main) |
| host clients | expect=ABSENT, inews=ABSENT, nn=ABSENT, script=/usr/bin/script, slrn=ABSENT, tin=ABSENT, trn=ABSENT |

## The v0 matrix

**Execution subject.** Backend `native-operator`; deployed source `0a8b592`; runtime image `launcher sha256=ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142; image sha256=21ba38c1a66d96c32c8e50269b852cabd07ae15548306781aafa084cb0e6af32; declared runtime=b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5; sidecar core sha256=6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf (static only before a live-owner witness); source correspondence unestablished; live owners observed via /proc runtime sha256=b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5 and core sha256=6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf`. These are separate labels: naming the source and hashing an externally supplied image does not prove they correspond.

206 rows: 126 accepted, 34 refused, 3 uncertain, 38 not exercised, 5 not built; 2 row(s) did not do what they were designed to do, and 1 exited with a host fault or usage error, which is not an outcome and is counted among the not exercised. Every count here is `tools/v0_matrix.py`'s over the rows below, and `planning/evidence/v0-runs/20260922T204325.546307Z-0a8b592-0bffc80c1571/matrix.json` carries the same rows with their digest.


**Who saw it.** 2 of the 163 outcome rows were observed by something that is not fn's own code; 161 were observed by fn talking to fn. A feature that only fn's own client has ever seen is a weaker claim than "usable between two peered servers" reads, and every row carries the client that saw it in its `client` field. Clients in this run: fn CLI (exit code) (41); stdlib nntplib on python3.12 (2); the matrix's raw-socket driver (121).

| feature | accepted | refused | uncertain | not exercised | not built | disagreed |
| --- | --- | --- | --- | --- | --- | --- |
| node init, configuration, start and stop (F-NODE) | 10 | 2 | 0 | 1 | 2 | 0 |
| the three outcomes on the operator surface (F-OUT) | 4 | 2 | 2 | 0 | 0 | 0 |
| groups, capacity, peers and live reconfiguration (F-GROUP) | 14 | 5 | 1 | 0 | 0 | 2 |
| principals, AUTHINFO and posting permission (F-AUTH) | 12 | 4 | 0 | 0 | 1 | 0 |
| POST and its read-back (F-POST) | 11 | 2 | 0 | 0 | 0 | 0 |
| the reader profile on each node (F-READ) | 52 | 8 | 0 | 0 | 2 | 0 |
| capability truthfulness (F-PIN) | 4 | 0 | 0 | 0 | 0 | 0 |
| transit inbound, A to B and B to A (F-TRANSIT) | 14 | 11 | 0 | 7 | 0 | 0 |
| the owner-driven outbound feed (F-FEED) | 3 | 0 | 0 | 1 | 0 | 0 |
| checkpoint, recovery and the process-death cut table (F-CRASH) | 0 | 0 | 0 | 9 | 0 | 0 |
| BP over TCPCLv4 between the two nodes (F-BP) | 0 | 0 | 0 | 8 | 0 | 0 |
| statement sign and verify across the pair (F-STX) | 0 | 0 | 0 | 6 | 0 | 0 |
| the carried-media letter (F-MEDIA) | 0 | 0 | 0 | 3 | 0 | 0 |
| scale (F-SCALE) | 0 | 0 | 0 | 1 | 0 | 0 |
| INN as a third node (F-INN) | 0 | 0 | 0 | 1 | 0 | 0 |
| independent newsreader clients (F-CLIENT) | 2 | 0 | 0 | 1 | 0 | 0 |

### Every row

| row | title | verdict | expected | agrees | independent | observed |
| --- | --- | --- | --- | --- | --- | --- |
| `V0-NODE-INIT-A` | fn init creates the store and writes fn.toml | **accepted** | accepted | yes | fn only | rc=0 initialized /home/hbox/fn-deploy/native-dabebb84-0a8b592/a/init/store |
| `V0-NODE-INIT-B` | fn init creates the store and writes fn.toml | **accepted** | accepted | yes | fn only | rc=0 initialized /home/hbox/fn-deploy/native-dabebb84-0a8b592/b/init/store |
| `V0-NODE-CONFIG-A` | fn.toml carries [store] path and [acl2] path | **not-built** | accepted | - | - | (not run) |
| `V0-NODE-CONFIG-B` | fn.toml carries [store] path and [acl2] path | **not-built** | accepted | - | - | (not run) |
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
| `V0-NODE-LOOPBACK` | a non-loopback listener host is refused rather than silently bound | **not-exercised** | refused | - | - | rc=5 usage operator request (CONFIGURATION INVALID) |
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
| `V0-CFG-LIVE` | a group declared on the running service's control channel reaches the served configuration | **uncertain** | accepted | NO | fn only | rc=3 uncertain operator group; GROUP fn.matrix.live -> (no reply) |
| `V0-CFG-LIVE-REFUSE` | an offline configuration command is refused while the service holds the store | **accepted** | refused | NO | fn only | rc=0 configured generation=7 record=00000007.cfg verification=VERIFIED |
| `V0-AUTH-NEW` | fn principal new derives a principal id from a seed | **not-built** | accepted | - | - | (not run) |
| `V0-AUTH-PASSWORD-A` | fn principal set-password records an AUTHINFO credential | **accepted** | accepted | yes | fn only | rc=0 Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true |
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
| `V0-POST-FRESH-A` | a fresh connection reads it back by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <native-matrix-e5b62b396a22-a@example.invalid> article follows |
| `V0-POST-FRESH-B` | a fresh connection reads it back by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <native-matrix-0fcd55edd32d-b@example.invalid> article follows |
| `V0-POST-DUPLICATE-A` | a second POST of the same Message-ID is refused and allocates nothing | **refused** | refused | yes | fn only | 441 posting failed; the article was refused |
| `V0-POST-DUPLICATE-B` | a second POST of the same Message-ID is refused and allocates nothing | **refused** | refused | yes | fn only | 441 posting failed; the article was refused |
| `V0-POST-CLOCK-A` | a duplicate POST is refused as an article and does not cost the node its clock | **accepted** | accepted | yes | fn only | the duplicate answered '441 posting failed; the article was refused' and DATE afterwards answered '111 20260922204420' |
| `V0-POST-CLOCK-B` | a duplicate POST is refused as an article and does not cost the node its clock | **accepted** | accepted | yes | fn only | the duplicate answered '441 posting failed; the article was refused' and DATE afterwards answered '111 20260922204428' |
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
| `V0-READ-ARTICLE-A` | ARTICLE by number | **accepted** | accepted | yes | fn only | 220 1 <native-matrix-e5b62b396a22-a@example.invalid> article follows |
| `V0-READ-ARTICLE-B` | ARTICLE by number | **accepted** | accepted | yes | fn only | 220 1 <native-matrix-0fcd55edd32d-b@example.invalid> article follows |
| `V0-READ-HEAD-A` | HEAD by number | **accepted** | accepted | yes | fn only | 221 1 <native-matrix-e5b62b396a22-a@example.invalid> headers follow |
| `V0-READ-HEAD-B` | HEAD by number | **accepted** | accepted | yes | fn only | 221 1 <native-matrix-0fcd55edd32d-b@example.invalid> headers follow |
| `V0-READ-BODY-A` | BODY by number | **accepted** | accepted | yes | fn only | 222 1 <native-matrix-e5b62b396a22-a@example.invalid> body follows |
| `V0-READ-BODY-B` | BODY by number | **accepted** | accepted | yes | fn only | 222 1 <native-matrix-0fcd55edd32d-b@example.invalid> body follows |
| `V0-READ-STAT-A` | STAT by number | **accepted** | accepted | yes | fn only | 223 1 <native-matrix-e5b62b396a22-a@example.invalid> retrieved |
| `V0-READ-STAT-B` | STAT by number | **accepted** | accepted | yes | fn only | 223 1 <native-matrix-0fcd55edd32d-b@example.invalid> retrieved |
| `V0-READ-ARTICLE-MSGID-A` | ARTICLE by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <native-matrix-e5b62b396a22-a@example.invalid> article follows |
| `V0-READ-ARTICLE-MSGID-B` | ARTICLE by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <native-matrix-0fcd55edd32d-b@example.invalid> article follows |
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
| `V0-READ-NEWNEWS-FUTURE-A` | NEWNEWS since a future instant returns the empty block | **accepted** | accepted | yes | fn only | 230 list of new articles by message-id follows |
| `V0-READ-NEWNEWS-FUTURE-B` | NEWNEWS since a future instant returns the empty block | **accepted** | accepted | yes | fn only | 230 list of new articles by message-id follows |
| `V0-READ-NEWNEWS-SYNTAX-A` | NEWNEWS with a malformed wildmat is refused with 501 | **not-built** | refused | - | - | 501 syntax error |
| `V0-READ-NEWNEWS-SYNTAX-B` | NEWNEWS with a malformed wildmat is refused with 501 | **not-built** | refused | - | - | 501 syntax error |
| `V0-READ-DATE-A` | DATE | **accepted** | accepted | yes | fn only | 111 20260922204421 |
| `V0-READ-DATE-B` | DATE | **accepted** | accepted | yes | fn only | 111 20260922204429 |
| `V0-READ-HELP-A` | HELP | **accepted** | accepted | yes | fn only | 100 help text follows |
| `V0-READ-HELP-B` | HELP | **accepted** | accepted | yes | fn only | 100 help text follows |
| `V0-READ-UNKNOWN-A` | an unknown command is refused with 500 | **refused** | refused | yes | fn only | 500 command not recognized |
| `V0-READ-UNKNOWN-B` | an unknown command is refused with 500 | **refused** | refused | yes | fn only | 500 command not recognized |
| `V0-READ-FRAMING-A` | a command split across two TCP segments is answered once, the same way | **accepted** | accepted | yes | fn only | DATE split across two segments answered '111 20260922204421' against '111 20260922204421' |
| `V0-READ-FRAMING-B` | a command split across two TCP segments is answered once, the same way | **accepted** | accepted | yes | fn only | DATE split across two segments answered '111 20260922204429' against '111 20260922204429' |
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
| `V0-TRANSIT-IDENTICAL-AB` | the far side serves the same octets the source served | **accepted** | accepted | yes | fn only | reread=220 0 <alpha@a.example.invalid> article follows identical=True |
| `V0-TRANSIT-IDENTICAL-BA` | the far side serves the same octets the source served | **accepted** | accepted | yes | fn only | reread=220 0 <beta@b.example.invalid> article follows identical=True |
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
| `V0-TRANSIT-TLS-AB` | the owner's feed reaches the peer over STARTTLS, the peer's certificate verified against the record's anchor and server name | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-TLS-BA` | the owner's feed reaches the peer over STARTTLS, the peer's certificate verified against the record's anchor and server name | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-AUTHINFO-AB` | the owner's feed logs in with AUTHINFO as the principal the peer's record binds before it offers, and the peer takes the offer in that role | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-AUTHINFO-BA` | the owner's feed logs in with AUTHINFO as the principal the peer's record binds before it offers, and the peer takes the offer in that role | **not-exercised** | accepted | - | - | (not run) |
| `V0-TRANSIT-TLS-WRONG-ANCHOR` | a feed whose record names an anchor that did not issue the peer's certificate delivers nothing, and both owners stay up | **not-exercised** | refused | - | - | (not run) |
| `V0-TRANSIT-AUTHINFO-WRONG` | a feed whose profile carries a wrong password delivers nothing, and both owners stay up | **refused** | refused | yes | fn only | {"case": "wrong-password", "delivered": false, "identity": {"a": {"core": "/tank/fn/gates/freeze-dev-28fb4bd0/build/fn-host.core", "core_sha256": "6e9ab804cd88ba1758229a76694503e667f210974c50c78dc2088 |
| `V0-FEED-QUEUE` | an article accepted on the source enters the matching peer's outbound queue | **accepted** | accepted | yes | fn only | {"duplicate": "435", "identity": {"restart-a": {"core": "/tank/fn/gates/freeze-dev-28fb4bd0/build/fn-host.core", "core_sha256": "6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf", "run |
| `V0-FEED-OFFER` | the owner opens the session and offers it, with no hand-driven socket | **accepted** | accepted | yes | fn only | {"ab": {"duplicate": "435", "identical": true}, "ba": {"duplicate": "435", "identical": true}} |
| `V0-FEED-ONCE` | an acknowledged transfer is not offered a second time | **not-exercised** | accepted | - | - | (not run) |
| `V0-FEED-JOURNAL` | the feed journal records the transfer and survives a restart | **accepted** | accepted | yes | fn only | {"duplicate": "435", "identity": {"restart-a": {"core": "/tank/fn/gates/freeze-dev-28fb4bd0/build/fn-host.core", "core_sha256": "6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf", "run |
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
| `V0-CLIENT-NNTPLIB-A` | an independent stdlib nntplib client reads a group and an article | **accepted** | accepted | yes | yes | nntplib 3.12.7 drove CAPABILITIES, GROUP, STAT, ARTICLE, HEAD, BODY, OVER, LIST, ARTICLE (absent), QUIT; login=(not attempted) authinfo-advertised=None group={'count': 4, 'first': 1, 'last': 4, 'name' |
| `V0-CLIENT-NNTPLIB-B` | an independent stdlib nntplib client reads a group and an article | **accepted** | accepted | yes | yes | nntplib 3.12.7 drove CAPABILITIES, GROUP, STAT, ARTICLE, HEAD, BODY, OVER, LIST, ARTICLE (absent), QUIT; login=(not attempted) authinfo-advertised=None group={'count': 4, 'first': 1, 'last': 4, 'name' |
| `V0-CLIENT-SLRN` | slrn reads a group and an article | **not-exercised** | accepted | - | - | (slrn is not installed) |

### What every row that is not an outcome is waiting for

- `V0-NODE-CONFIG-A` (not-built): the native configuration has no `[acl2] path`: ACL2 is inside the image, so half of this row has no native subject. The `[store] path` half is what the row above consumed, and no native verb writes an fn.toml -- owned by `native configuration schema`
- `V0-NODE-CONFIG-B` (not-built): the native configuration has no `[acl2] path`: ACL2 is inside the image, so half of this row has no native subject. The `[store] path` half is what the row above consumed, and no native verb writes an fn.toml -- owned by `native configuration schema`
- `V0-NODE-LOOPBACK` (not-exercised): the command exited 5, a usage error, which is not one of the three outcomes (docs/operator.md: 0 accepted, 1 refused, 3 uncertain)
- `V0-AUTH-NEW` (not-built): the packaged native operator has no `principal new`: the local principal id is derived by ACL2 inside `set-password` (`fn-native-auth-admin-principal`, books/native-auth-admin.lisp) and no public verb derives one from a seed -- owned by `native principal derivation surface`
- `V0-READ-NEWNEWS-SYNTAX-A` (not-built): `NEWNEWS SYNTAX` answered '501 syntax error' on this commit; the entry point that started is `native-operator`
- `V0-READ-NEWNEWS-SYNTAX-B` (not-built): `NEWNEWS SYNTAX` answered '501 syntax error' on this commit; the entry point that started is `native-operator`
- `V0-TRANSIT-INDEPENDENT-A` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-TRANSIT-INDEPENDENT-B` (not-exercised): the run reached its end without this row; the phase that owns it raised or was skipped, and the gap list above says which
- `V0-TRANSIT-TLS-AB` (not-exercised): the protected peering witness produced no protected-feed observation whose two live owners are this run's image (witnesses=1 rc=1)
- `V0-TRANSIT-TLS-BA` (not-exercised): the protected peering witness produced no protected-feed observation whose two live owners are this run's image (witnesses=1 rc=1)
- `V0-TRANSIT-AUTHINFO-AB` (not-exercised): the protected peering witness produced no protected-feed observation whose two live owners are this run's image (witnesses=1 rc=1)
- `V0-TRANSIT-AUTHINFO-BA` (not-exercised): the protected peering witness produced no protected-feed observation whose two live owners are this run's image (witnesses=1 rc=1)
- `V0-TRANSIT-TLS-WRONG-ANCHOR` (not-exercised): the protected peering witness produced no wrong-anchor observation whose two live owners are this run's image (witnesses=1 rc=1)
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
- `V0-CLIENT-SLRN` (not-exercised): slrn is not installed on hbox (nor on hbox, measured 2026-09-20); tests/interop_slrn.py has never run against an fn node

### What each row does not show

- `V0-NODE-INIT-A`: the store `[store] path` names, created by the public operator verb rather than by the image's low-level `store ROOT init` diagnostic; the groups are the ones this command named and there is no default table, so an `init` with no group is a usage error and not a store nobody chose the contents of. A scratch node beside the served one: nothing here changes what the node serves
- `V0-NODE-INIT-B`: the store `[store] path` names, created by the public operator verb rather than by the image's low-level `store ROOT init` diagnostic; the groups are the ones this command named and there is no default table, so an `init` with no group is a usage error and not a store nobody chose the contents of. A scratch node beside the served one: nothing here changes what the node serves
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
- `V0-NODE-LOOPBACK`: the wildcard is refused at configuration admission (`fn-native-config-listener-hostp`, books/native-config.lisp), not at bind: `0.0.0.0` never reaches a listener, and the operator reports an inadmissible configuration as a usage error (5) rather than as one of the three outcomes -- so unless the image answers 1 this row is not-exercised with that code named, and the refusal it wanted has still happened at admission. A numeric non-loopback IPv4 address is ADMITTED by design and would be bound: this row is about the wildcard, not about fn declining to serve a network interface. Nothing here tests a bind the kernel would refuse for a different reason
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
- `V0-CFG-LIVE`: one group declared on one live owner: the operator verb's exit code is the acceptance and the service is then asked over its own socket whether the group reached the served configuration. No concurrent reader was observed across the change, and nothing here says the change survives a restart; the verb did not accept, so the socket reply above is the state the node was left in
- `V0-CFG-LIVE-REFUSE`: a second configuration over node A's OWN store whose `[control] path` names a socket nothing has bound, so the verb takes the offline executor while the live owner holds the writer lock; the refusal is that lock's and a server that does not take it would not produce it. The supplied configuration is unchanged, and with its own live control path the same words reach the live owner instead -- which is the row above
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
- `V0-READ-NEWNEWS-A`: the node under test may hold no article whose Injection-Date or Date fn can decode, in which case 230 with an empty block is the correct answer and the row records the framing, not a reported identifier; served by `native-operator` on port 11190
- `V0-READ-NEWNEWS-B`: the node under test may hold no article whose Injection-Date or Date fn can decode, in which case 230 with an empty block is the correct answer and the row records the framing, not a reported identifier; served by `native-operator` on port 11191
- `V0-READ-NEWNEWS-FUTURE-A`: served by `native-operator` on port 11190
- `V0-READ-NEWNEWS-FUTURE-B`: served by `native-operator` on port 11191
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
- `V0-TRANSIT-TLS-AB`: the article's arrival under a target that refuses AUTHINFO before TLS and answers an unauthenticated IHAVE 480 is what shows the channel; the matrix does not see the feed's own socket, and OpenSSL's chain and hostname checks are trusted integration (PRF-047)
- `V0-TRANSIT-TLS-BA`: the article's arrival under a target that refuses AUTHINFO before TLS and answers an unauthenticated IHAVE 480 is what shows the channel; the matrix does not see the feed's own socket, and OpenSSL's chain and hostname checks are trusted integration (PRF-047)
- `V0-TRANSIT-AUTHINFO-AB`: the same arrival: an unauthenticated offer of the same article is 480 on the target, so the feed's offer came on a connection that logged in; PRF-051's keystones are what say the feed sends no offer before the 281
- `V0-TRANSIT-AUTHINFO-BA`: the same arrival: an unauthenticated offer of the same article is 480 on the target, so the feed's offer came on a connection that logged in; PRF-051's keystones are what say the feed sends no offer before the 281
- `V0-TRANSIT-AUTHINFO-WRONG`: absence is observed for three seconds through a protected reader session; a longer delay is not excluded
- `V0-FEED-QUEUE`: the restart witness found FNFD intent
- `V0-FEED-OFFER`: the public owner delivered both directions
- `V0-FEED-JOURNAL`: intent survived source death and restart
- `V0-CRASH-KILL`: what the client saw is recorded; an acknowledgement after the kill would be the defect, and its absence is the assertion
- `V0-SCALE-CEILING`: a measured ceiling on one box with one payload grid; it is not a bound and not a proof
- `V0-CLIENT-NNTPLIB-A`: one client library, and it reads: nothing here is posted or fed by a foreign client. Its framing, folding and response parsing are the standard library's, not fn's, which is the point of the row
- `V0-CLIENT-NNTPLIB-B`: one client library, and it reads: nothing here is posted or fed by a foreign client. Its framing, folding and response parsing are the standard library's, not fn's, which is the point of the row

### The exact invocation of every row

- `V0-NODE-INIT-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/fn.toml init fn.letters`
- `V0-NODE-INIT-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/fn.toml init fn.letters`
- `V0-NODE-CONFIG-A`: `env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/fn.toml init fn.letters`
- `V0-NODE-CONFIG-B`: `env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/fn.toml init fn.letters`
- `V0-NODE-REINIT-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/fn.toml init fn.letters`
- `V0-NODE-REINIT-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/fn.toml init fn.letters`
- `V0-NODE-REINIT-SAFE-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/fn.toml init fn.letters
cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb8`
- `V0-NODE-REINIT-SAFE-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/fn.toml init fn.letters
cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb8`
- `V0-NODE-STATUS-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml status`
- `V0-NODE-STATUS-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml status`
- `V0-NODE-START-A`: `env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml run`
- `V0-NODE-START-B`: `env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml run`
- `V0-NODE-STOP-A`: `kill -TERM <owner pid> (harness) ; cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml status`
- `V0-NODE-STOP-B`: `kill -TERM <owner pid> (harness) ; cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml status`
- `V0-NODE-LOOPBACK`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; mkdir -p $HOME/fn-deploy/native-dabebb84-0a8b592/loopback && env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native store $HOME/fn-deploy/native-dabebb84-0a8b592/loopback/store init fn.letters && printf '[store]\npath = "%s"\n[listener]\nhost = "0.0.0.0"\nport ...`
- `V0-OUT-ACCEPTED-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml post --message-id '<alpha@a.example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/a/alpha.article --group fn.letters`
- `V0-OUT-ACCEPTED-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml post --message-id '<beta@b.example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/b/beta.article --group fn.letters`
- `V0-OUT-REFUSED-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml post --message-id '<alpha@a.example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/a/alpha-conflict.article --group fn.letters`
- `V0-OUT-REFUSED-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml post --message-id '<beta@b.example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/b/beta-conflict.article --group fn.letters`
- `V0-OUT-UNCERTAIN-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/fn.toml post --message-id '<init-a@example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/init.article --group fn.letters`
- `V0-OUT-UNCERTAIN-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/fn.toml post --message-id '<init-b@example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/init.article --group fn.letters`
- `V0-OUT-RECOVER-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/fn.toml recover`
- `V0-OUT-RECOVER-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/fn.toml recover`
- `V0-GROUP-CREATE-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml group create fn.matrix`
- `V0-GROUP-CREATE-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml group create fn.matrix`
- `V0-GROUP-SERVED-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py presence --port 11190 --groups fn.matrix`
- `V0-GROUP-SERVED-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py presence --port 11191 --groups fn.matrix`
- `V0-GROUP-RETIRE-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml group retire fn.matrix.throwaway`
- `V0-GROUP-RETIRE-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml group retire fn.matrix.throwaway`
- `V0-GROUP-UNKNOWN-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml group retire fn.not.served`
- `V0-GROUP-UNKNOWN-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml group retire fn.not.served`
- `V0-CAP-SET-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/capacity/fn.toml capacity 64`
- `V0-CAP-SET-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/capacity/fn.toml capacity 64`
- `V0-CAP-REFUSE-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/capacity/fn.toml post --message-id '<capacity-a@example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/a/capacity/capacity.article --group fn....`
- `V0-CAP-REFUSE-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/capacity/fn.toml post --message-id '<capacity-b@example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/b/capacity/capacity.article --group fn....`
- `V0-PEER-ADD-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml peer add b b.gate.example.invalid 127.0.0.1 11191 'fn.*' - 127.0.0.1 true`
- `V0-PEER-ADD-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml peer add a a.gate.example.invalid 127.0.0.1 11190 'fn.*' - 127.0.0.1 true`
- `V0-PEER-LIST-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml peer list`
- `V0-PEER-LIST-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml peer list`
- `V0-PEER-ABSENT`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml peer remove no-such-peer`
- `V0-PEER-REMOVE`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml peer remove b`
- `V0-CFG-LIVE`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml group create fn.matrix.live
cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py presence --por`
- `V0-CFG-LIVE-REFUSE`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/offline/fn.toml group create fn.matrix.offline`
- `V0-AUTH-NEW`: `packaging/fn-native operator CONFIG principal new --seed FILE`
- `V0-AUTH-PASSWORD-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; timeout 120 env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml principal set-password matrix < $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret.pair`
- `V0-AUTH-PASSWORD-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; timeout 120 env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml principal set-password matrix < $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret.pair`
- `V0-AUTH-LIST-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml principal list`
- `V0-AUTH-LIST-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml principal list`
- `V0-AUTH-ADVERTISED-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-ADVERTISED-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
- `V0-AUTH-GATED-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py auth --port 11292 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret --msgid '<auth-gate-a@example.invalid>'`
- `V0-AUTH-GATED-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py auth --port 11293 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret --msgid '<auth-gate-b@example.invalid>'`
- `V0-AUTH-LOGIN-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-LOGIN-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
- `V0-AUTH-WITHDRAWN-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-WITHDRAWN-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
- `V0-AUTH-POST-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-POST-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
- `V0-AUTH-WRONG-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-WRONG-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
- `V0-POST-OPEN-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --user '' --secret ''`
- `V0-POST-OPEN-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --user '' --secret ''`
- `V0-POST-COMMIT-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --user '' --secret ''`
- `V0-POST-COMMIT-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --user '' --secret ''`
- `V0-POST-READBACK-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --user '' --secret ''`
- `V0-POST-READBACK-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --user '' --secret ''`
- `V0-POST-FRESH-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --user '' --secret ''`
- `V0-POST-FRESH-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --user '' --secret ''`
- `V0-POST-DUPLICATE-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --user '' --secret ''`
- `V0-POST-DUPLICATE-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --user '' --secret ''`
- `V0-POST-CLOCK-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --user '' --secret ''`
- `V0-POST-CLOCK-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --user '' --secret ''`
- `V0-POST-CONCURRENT`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py concurrent --port 11190 --group fn.letters --msgid '<concurrent@example.invalid>' --user '' --secret ''`
- `V0-READ-CAPABILITIES-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-CAPABILITIES-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-MODE-READER-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-MODE-READER-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-WILDMAT-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-WILDMAT-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-OVERVIEW-FMT-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-OVERVIEW-FMT-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-TIMES-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-TIMES-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-HEADERS-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-HEADERS-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-GROUP-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-GROUP-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LISTGROUP-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LISTGROUP-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HEAD-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HEAD-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-BODY-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-BODY-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-STAT-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-STAT-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-MSGID-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-MSGID-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-ABSENT-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-ABSENT-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-RANGE-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-RANGE-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HDR-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HDR-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XOVER-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XOVER-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XHDR-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XHDR-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XPAT-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XPAT-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEXT-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEXT-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LAST-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LAST-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-FUTURE-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-FUTURE-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-SYNTAX-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEWNEWS-SYNTAX-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-DATE-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-DATE-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HELP-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HELP-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-UNKNOWN-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-UNKNOWN-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-FRAMING-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-FRAMING-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
- `V0-PIN-DISPATCHED-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py pins --port 11190 --group fn.letters --user '' --secret ''`
- `V0-PIN-DISPATCHED-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py pins --port 11191 --group fn.letters --user '' --secret ''`
- `V0-PIN-ADVERTISED-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py pins --port 11190 --group fn.letters --user '' --secret ''`
- `V0-PIN-ADVERTISED-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py pins --port 11191 --group fn.letters --user '' --secret ''`
- `V0-TRANSIT-IDENTITY-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml policy set path-identity a.gate.example.invalid`
- `V0-TRANSIT-IDENTITY-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml policy set path-identity b.gate.example.invalid`
- `V0-TRANSIT-INDEPENDENT-A`: `(none)`
- `V0-TRANSIT-INDEPENDENT-B`: `(none)`
- `V0-TRANSIT-MODE-STREAM-AB`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-MODE-STREAM-BA`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-OFFER-AB`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-OFFER-BA`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-TRANSFER-AB`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-TRANSFER-BA`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-IDENTICAL-AB`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-IDENTICAL-BA`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-DUPLICATE-AB`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-DUPLICATE-BA`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-LOOP-AB`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-LOOP-BA`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-LOOP-ABSENT-AB`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-LOOP-ABSENT-BA`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-CHECK-FRESH-AB`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py stream --from-port 11190 --to-port 11191 --msgid '<stream-a@example.invalid>'`
- `V0-TRANSIT-CHECK-FRESH-BA`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py stream --from-port 11191 --to-port 11190 --msgid '<stream-b@example.invalid>'`
- `V0-TRANSIT-TAKETHIS-AB`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py stream --from-port 11190 --to-port 11191 --msgid '<stream-a@example.invalid>'`
- `V0-TRANSIT-TAKETHIS-BA`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py stream --from-port 11191 --to-port 11190 --msgid '<stream-b@example.invalid>'`
- `V0-TRANSIT-CHECK-DUP-AB`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-CHECK-DUP-BA`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-TAKETHIS-DUP-AB`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-TAKETHIS-DUP-BA`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-TLS-AB`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; image=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; runtime_path=/tank/fn/sbcl/bin/sbcl ; test -x "$runtime_path" || exit 4 ; runtime_expecte...`
- `V0-TRANSIT-TLS-BA`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; image=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; runtime_path=/tank/fn/sbcl/bin/sbcl ; test -x "$runtime_path" || exit 4 ; runtime_expecte...`
- `V0-TRANSIT-AUTHINFO-AB`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; image=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; runtime_path=/tank/fn/sbcl/bin/sbcl ; test -x "$runtime_path" || exit 4 ; runtime_expecte...`
- `V0-TRANSIT-AUTHINFO-BA`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; image=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; runtime_path=/tank/fn/sbcl/bin/sbcl ; test -x "$runtime_path" || exit 4 ; runtime_expecte...`
- `V0-TRANSIT-TLS-WRONG-ANCHOR`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; image=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; runtime_path=/tank/fn/sbcl/bin/sbcl ; test -x "$runtime_path" || exit 4 ; runtime_expecte...`
- `V0-TRANSIT-AUTHINFO-WRONG`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; image=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; runtime_path=/tank/fn/sbcl/bin/sbcl ; test -x "$runtime_path" || exit 4 ; runtime_expecte...`
- `V0-FEED-QUEUE`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; image=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_...`
- `V0-FEED-OFFER`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; image=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_...`
- `V0-FEED-ONCE`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; image=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_...`
- `V0-FEED-JOURNAL`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; image=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_...`
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
- `V0-CLIENT-NNTPLIB-A`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3.12 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/independent.py --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>' --user '' --secret ''`
- `V0-CLIENT-NNTPLIB-B`: `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3.12 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/independent.py --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>' --user '' --secret ''`
- `V0-CLIENT-SLRN`: `slrn -h <host> -p <port>`

## Every command

| # | step | rc | first line | s |
| --- | --- | --- | --- | --- |
| 1 | preflight | 0 | `os=Ubuntu 24.10 kernel=Linux 6.11.0-29-generic arch=x86_64 cores=24` | 0.4 |
| 2 | acquire deploy lock | 0 | `` | 0.4 |
| 3 | ship archive | 0 | `` | 3.4 |
| 4 | make run dir | 0 | `` | 0.4 |
| 5 | install drive.py | 0 | `` | 0.4 |
| 6 | install feed.py | 0 | `` | 0.4 |
| 7 | install matrix.py | 0 | `` | 0.4 |
| 8 | native packaged operator subject | 0 | `NATIVE-LAUNCHER-DIGEST ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142` | 0.6 |
| 9 | node A native run directory | 0 | `` | 0.3 |
| 10 | node A native config exists | 0 | `` | 0.4 |
| 11 | node A native operator status | 0 | `transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment` | 0.5 |
| 12 | node B native run directory | 0 | `` | 0.3 |
| 13 | node B native config exists | 0 | `` | 0.3 |
| 14 | node B native operator status | 0 | `transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment` | 0.5 |
| 15 | loopback refusal: scratch store | 0 | `initialized /home/hbox/fn-deploy/native-dabebb84-0a8b592/loopback/store` | 0.5 |
| 16 | loopback refusal: run | 5 | `usage operator request (CONFIGURATION INVALID)` | 0.5 |
| 17 | node A init scratch configuration | 0 | `` | 0.4 |
| 18 | node A operator init | 0 | `initialized /home/hbox/fn-deploy/native-dabebb84-0a8b592/a/init/store` | 0.5 |
| 19 | start server (node A init owner, init-a) | 0 | `LISTENING 11295` | 1.4 |
| 20 | install init.article | 0 | `` | 0.6 |
| 21 | node A submission to the init scratch owner | 3 | `uncertain operator post UNCERTAIN` | 0.6 |
| 22 | stop server init-a | 0 | `stopped` | 0.4 |
| 23 | node A recover the init scratch store | 0 | `recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none` | 0.8 |
| 24 | node A second operator init | 1 | `refused operator init STORE-EXISTS` | 0.5 |
| 25 | node A recover after the second init | 0 | `recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none` | 0.6 |
| 26 | node B init scratch configuration | 0 | `` | 0.5 |
| 27 | node B operator init | 0 | `initialized /home/hbox/fn-deploy/native-dabebb84-0a8b592/b/init/store` | 0.5 |
| 28 | start server (node B init owner, init-b) | 0 | `LISTENING 11296` | 1.4 |
| 29 | install init.article | 0 | `` | 0.4 |
| 30 | node B submission to the init scratch owner | 3 | `uncertain operator post UNCERTAIN` | 0.5 |
| 31 | stop server init-b | 0 | `stopped` | 0.3 |
| 32 | node B recover the init scratch store | 0 | `recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none` | 0.5 |
| 33 | node B second operator init | 1 | `refused operator init STORE-EXISTS` | 0.5 |
| 34 | node B recover after the second init | 0 | `recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none` | 0.4 |
| 35 | node A group create fn.matrix | 0 | `configured generation=2 record=00000002.cfg verification=VERIFIED` | 0.5 |
| 36 | node A group create fn.matrix.throwaway | 0 | `configured generation=3 record=00000003.cfg verification=VERIFIED` | 0.5 |
| 37 | node A group retire fn.matrix.throwaway | 0 | `configured generation=4 record=00000004.cfg verification=VERIFIED` | 0.5 |
| 38 | node A group retire an unserved group | 1 | `refused operator group administrative configuration refused: NO-SUCH-GROUP` | 0.4 |
| 39 | node A capacity scratch store | 0 | `initialized /home/hbox/fn-deploy/native-dabebb84-0a8b592/a/capacity/store` | 0.5 |
| 40 | node A capacity 64 | 0 | `configured generation=2 record=00000002.cfg verification=VERIFIED` | 0.4 |
| 41 | node A capacity 1 | 0 | `configured generation=3 record=00000003.cfg verification=VERIFIED` | 0.5 |
| 42 | node A capacity owner config | 0 | `` | 0.4 |
| 43 | start server (node A capacity owner, capacity-a) | 0 | `LISTENING 11290` | 1.3 |
| 44 | install capacity.article | 0 | `` | 0.4 |
| 45 | node A post beyond the capacity | 1 | `refused operator post REFUSED` | 0.5 |
| 46 | stop server capacity-a | 0 | `stopped` | 1.4 |
| 47 | native AUTHINFO secret | 0 | `SECRET-READY` | 0.4 |
| 48 | node A principal set-password matrix | 0 | `Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.5 |
| 49 | node A principal list | 0 | `matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.4 |
| 50 | node A auth-required scratch store | 0 | `initialized /home/hbox/fn-deploy/native-dabebb84-0a8b592/a/authgate/store` | 0.5 |
| 51 | node A auth-required scratch credential | 0 | `Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.4 |
| 52 | start server (node A auth-required owner, authgate-a) | 0 | `LISTENING 11292` | 1.4 |
| 53 | node A auth-required AUTHINFO gate | 0 | `{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BE` | 0.5 |
| 54 | stop server authgate-a | 0 | `stopped` | 1.3 |
| 55 | node B group create fn.matrix | 0 | `configured generation=2 record=00000002.cfg verification=VERIFIED` | 0.5 |
| 56 | node B group create fn.matrix.throwaway | 0 | `configured generation=3 record=00000003.cfg verification=VERIFIED` | 0.4 |
| 57 | node B group retire fn.matrix.throwaway | 0 | `configured generation=4 record=00000004.cfg verification=VERIFIED` | 0.5 |
| 58 | node B group retire an unserved group | 1 | `refused operator group administrative configuration refused: NO-SUCH-GROUP` | 0.5 |
| 59 | node B capacity scratch store | 0 | `initialized /home/hbox/fn-deploy/native-dabebb84-0a8b592/b/capacity/store` | 0.5 |
| 60 | node B capacity 64 | 0 | `configured generation=2 record=00000002.cfg verification=VERIFIED` | 0.5 |
| 61 | node B capacity 1 | 0 | `configured generation=3 record=00000003.cfg verification=VERIFIED` | 0.5 |
| 62 | node B capacity owner config | 0 | `` | 0.4 |
| 63 | start server (node B capacity owner, capacity-b) | 0 | `LISTENING 11291` | 1.4 |
| 64 | install capacity.article | 0 | `` | 0.4 |
| 65 | node B post beyond the capacity | 1 | `refused operator post REFUSED` | 0.5 |
| 66 | stop server capacity-b | 0 | `stopped` | 1.3 |
| 67 | node B principal set-password matrix | 0 | `Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.5 |
| 68 | node B principal list | 0 | `matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.5 |
| 69 | node B auth-required scratch store | 0 | `initialized /home/hbox/fn-deploy/native-dabebb84-0a8b592/b/authgate/store` | 0.5 |
| 70 | node B auth-required scratch credential | 0 | `Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true` | 0.4 |
| 71 | start server (node B auth-required owner, authgate-b) | 0 | `LISTENING 11293` | 1.4 |
| 72 | node B auth-required AUTHINFO gate | 0 | `{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BE` | 0.4 |
| 73 | stop server authgate-b | 0 | `stopped` | 1.4 |
| 74 | node A path-identity | 0 | `configured generation=5 record=00000005.cfg verification=VERIFIED` | 0.6 |
| 75 | node B path-identity | 0 | `configured generation=5 record=00000005.cfg verification=VERIFIED` | 0.5 |
| 76 | node B configured port | 0 | `11191` | 0.5 |
| 77 | node A peer record for B | 0 | `configured generation=6 record=00000006.cfg verification=VERIFIED` | 0.6 |
| 78 | node A lists its peers | 0 | `b path-identity=b.gate.example.invalid address=127.0.0.1 port=11191 security=clear inbound=fn.* outbound=- auth=source-address:127.0.0.1` | 0.4 |
| 79 | node A configured port | 0 | `11190` | 0.3 |
| 80 | node B peer record for A | 0 | `configured generation=6 record=00000006.cfg verification=VERIFIED` | 0.4 |
| 81 | node B lists its peers | 0 | `a path-identity=a.gate.example.invalid address=127.0.0.1 port=11190 security=clear inbound=fn.* outbound=- auth=source-address:127.0.0.1` | 0.5 |
| 82 | start server (node A (native-operator), a-main) | 0 | `LISTENING 11190` | 1.4 |
| 83 | node A pid | 0 | `3269368` | 0.4 |
| 84 | start server (node B (native-operator), b-main) | 0 | `LISTENING 11191` | 1.4 |
| 85 | node B pid | 0 | `3269509` | 0.3 |
| 86 | node A server is alive | 0 | `ALIVE` | 0.4 |
| 87 | node A serves fn.matrix | 0 | `{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}` | 0.4 |
| 88 | node A server is alive | 0 | `ALIVE` | 0.4 |
| 89 | node A POST cycle | 0 | `{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-e5b` | 0.5 |
| 90 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 91 | node A reader surface | 0 | `{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE AC` | 0.8 |
| 92 | node A server is alive | 0 | `ALIVE` | 0.4 |
| 93 | node A AUTHINFO session | 0 | `{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "AUTHIN` | 0.5 |
| 94 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 95 | install alpha.article | 0 | `` | 0.4 |
| 96 | node A outcome accepted | 0 | `accepted operator post ACCEPTED` | 0.5 |
| 97 | install alpha.article | 0 | `` | 0.4 |
| 98 | node A outcome duplicate | 0 | `accepted operator post DUPLICATE` | 0.4 |
| 99 | install alpha-conflict.article | 0 | `` | 0.4 |
| 100 | node A outcome refused | 1 | `refused operator post REFUSED` | 0.4 |
| 101 | install stream-a.article | 0 | `` | 0.4 |
| 102 | node A seed <stream-a@example.invalid> | 0 | `accepted operator post ACCEPTED` | 0.5 |
| 103 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 104 | node B serves fn.matrix | 0 | `{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}` | 0.4 |
| 105 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 106 | node B POST cycle | 0 | `{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-0fc` | 0.5 |
| 107 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 108 | node B reader surface | 0 | `{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE AC` | 0.8 |
| 109 | node B server is alive | 0 | `ALIVE` | 0.4 |
| 110 | node B AUTHINFO session | 0 | `{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "AUTHIN` | 0.4 |
| 111 | node B server is alive | 0 | `ALIVE` | 0.4 |
| 112 | install beta.article | 0 | `` | 0.4 |
| 113 | node B outcome accepted | 0 | `accepted operator post ACCEPTED` | 0.5 |
| 114 | install beta.article | 0 | `` | 0.4 |
| 115 | node B outcome duplicate | 0 | `accepted operator post DUPLICATE` | 0.5 |
| 116 | install beta-conflict.article | 0 | `` | 0.3 |
| 117 | node B outcome refused | 1 | `refused operator post REFUSED` | 0.5 |
| 118 | install stream-b.article | 0 | `` | 0.3 |
| 119 | node B seed <stream-b@example.invalid> | 0 | `accepted operator post ACCEPTED` | 0.4 |
| 120 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 121 | node B server is alive | 0 | `ALIVE` | 0.4 |
| 122 | nntplib interpreter | 0 | `USE python3.12` | 0.4 |
| 123 | install independent.py | 0 | `` | 0.4 |
| 124 | independent nntplib client on node A | 0 | `/home/hbox/fn-deploy/native-dabebb84-0a8b592/gate-run/independent.py:6: DeprecationWarning: 'nntplib' is deprecated and slated for removal in Python 3.13` | 0.4 |
| 125 | independent nntplib client on node B | 0 | `/home/hbox/fn-deploy/native-dabebb84-0a8b592/gate-run/independent.py:6: DeprecationWarning: 'nntplib' is deprecated and slated for removal in Python 3.13` | 0.5 |
| 126 | node B server is alive | 0 | `ALIVE` | 0.4 |
| 127 | transit AB: offer <alpha@a.example.invalid> from A to B | 0 | `{"msgid": "<alpha@a.example.invalid>", "source": "220 0 <alpha@a.example.invalid> article follows", "source_lines": 7, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "` | 0.5 |
| 128 | transit AB: CHECK/TAKETHIS <stream-a@example.invalid> from A to B | 0 | `{"SOURCE": "220 0 <stream-a@example.invalid> article follows", "MODE STREAM": "203 streaming permitted", "CHECK": "238 <stream-a@example.invalid>", "TAKETHIS": "239 <stream-a@example.invalid>", "CHECK` | 0.5 |
| 129 | node A server is alive | 0 | `ALIVE` | 0.4 |
| 130 | transit BA: offer <beta@b.example.invalid> from B to A | 0 | `{"msgid": "<beta@b.example.invalid>", "source": "220 0 <beta@b.example.invalid> article follows", "source_lines": 7, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LI` | 0.5 |
| 131 | transit BA: CHECK/TAKETHIS <stream-b@example.invalid> from B to A | 0 | `{"SOURCE": "220 0 <stream-b@example.invalid> article follows", "MODE STREAM": "203 streaming permitted", "CHECK": "238 <stream-b@example.invalid>", "TAKETHIS": "239 <stream-b@example.invalid>", "CHECK` | 0.5 |
| 132 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 133 | node A capability pins | 0 | `{"advertised": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "answered": {"READER": "211 6 1 6 fn.letters", "POST": "340 send art` | 0.4 |
| 134 | node B server is alive | 0 | `ALIVE` | 0.4 |
| 135 | node B capability pins | 0 | `{"advertised": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "answered": {"READER": "211 6 1 6 fn.letters", "POST": "340 send art` | 0.5 |
| 136 | node A server is alive | 0 | `ALIVE` | 0.4 |
| 137 | node B server is alive | 0 | `ALIVE` | 0.4 |
| 138 | a second reader across node A's POST | 0 | `{"WATCHER BEFORE": "211 6 1 6 fn.letters", "POST": "340 send article to be posted", "WATCHER MID": "211 6 1 6 fn.letters", "WATCHER ARTICLE MID": "223 1 <native-matrix-e5b62b396a22-a@example.invalid> ` | 0.5 |
| 139 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 140 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 141 | live reconfiguration: declare fn.matrix.live on node A | 3 | `uncertain operator group` | 0.6 |
| 142 | node A serves fn.matrix.live without a restart | 1 | `{"ok": false, "port": 11190, "error": "ConnectionRefusedError: [Errno 111] Connection refused"}` | 0.4 |
| 143 | node A configured store | 0 | `/home/hbox/fn-native-matrix/a/store` | 0.3 |
| 144 | offline configuration over node A's store | 0 | `` | 0.2 |
| 145 | offline group create while the owner holds the store | 0 | `configured generation=7 record=00000007.cfg verification=VERIFIED` | 0.5 |
| 146 | native public peering/restart witness | 0 | `NATIVE-PEERING-EXPECTED-RUNTIME b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5` | 4.4 |
| 147 | native protected peering witness | 1 | `NATIVE-PROTECTED-EXPECTED-RUNTIME b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5` | 70.3 |
| 148 | stop server node A (main) | 0 | `stopped` | 0.3 |
| 149 | node A store after the stop | 0 | `transactions=7 articles=7 staging-orphans=0 unsigned-legacy-experiment` | 0.5 |
| 150 | node A recover after the stop | 0 | `recovered transactions=7 articles=7 staging-orphans=0 anchor=none checkpoint=none` | 0.5 |
| 151 | node A log tail | 0 | `CONTROL /home/hbox/fn-native-matrix/a/control.sock` | 0.4 |
| 152 | stop server node B (main) | 0 | `stopped` | 1.4 |
| 153 | node B store after the stop | 0 | `transactions=6 articles=6 staging-orphans=0 unsigned-legacy-experiment` | 0.5 |
| 154 | node B recover after the stop | 0 | `recovered transactions=6 articles=6 staging-orphans=0 anchor=none checkpoint=none` | 0.5 |
| 155 | node B log tail | 0 | `CONTROL /home/hbox/fn-native-matrix/b/control.sock` | 0.3 |
| 156 | peer remove a peer that is not there | 1 | `refused operator peer administrative configuration refused: NO-SUCH-PEER` | 0.5 |
| 157 | peer remove the configured peer | 0 | `configured generation=8 record=00000008.cfg verification=VERIFIED` | 0.6 |
| 158 | stop server node A (main) | 0 | `stopped` | 0.4 |
| 159 | stop the tap in front of node A | 0 | `stopped` | 0.3 |
| 160 | stop server node B (main) | 0 | `stopped` | 0.3 |
| 161 | stop the tap in front of node B | 0 | `stopped` | 0.4 |
| 162 | stray fn processes | 0 | `CLEAN` | 0.4 |
| 163 | remove the deploy tree | 0 | `` | 0.3 |
| 164 | release deploy lock | 0 | `` | 0.4 |

### Commands in full

1. **preflight** -- `. /etc/os-release 2>/dev/null || true ; echo "os=${PRETTY_NAME:-unknown} kernel=$(uname -sr) arch=$(uname -m) cores=$(nproc 2>/dev/null || echo ?)" ; echo "python3=$(python3 -V 2>&1)" ; for p in python3.9 python3.10 python3.11 python3.12; do ; command -v $p >/dev/null && echo "alt=$p $($p -V 2>&1)" ; done ; for c in slrn tin nn trn inews expect script; do ; printf 'client %s=%s\n' "$c" "$(comma...`
2. **acquire deploy lock** -- `mkdir -p $HOME/fn-deploy/.locks ; if ! mkdir $HOME/fn-deploy/.locks/native-dabebb84-0a8b592.lock 2>/dev/null; then ; echo "deploy identity is already active: native-dabebb84-0a8b592" ; exit 73 ; fi`
3. **ship archive** -- `git archive 0a8b592 | tar -x -C $HOME/fn-deploy/native-dabebb84-0a8b592`
4. **make run dir** -- `mkdir -p $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run`
5. **install drive.py** -- `base64 -d > $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/drive.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJJbmRlcGVuZGVudCBOTlRQIGRyaXZpbmcgZm9yIHRo ; ZSBkZXBsb3kgZ2F0ZTsgbm8gZm4gbW9kdWxlIGlzIGltcG9ydGVkLiIiIgppbXBvcnQgYXJncGFy ; c2UsIGpzb24sIG9zLCBzb2NrZXQsIHN5cywgdGltZQoKCmNsYXNzIENvbm46CiAgICBkZWYgX19p ; bml0X18oc2VsZiwgcG9ydCwgdGltZW91dD0zMCk6CiAgICAgICAgc2VsZi5zb2NrID0gc29j...`
6. **install feed.py** -- `base64 -d > $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJUaGUgdHdvLW5vZGUgcGhhc2VzLiAgTm8gZm4gbW9k ; dWxlIGlzIGltcG9ydGVkOyBDb25uIGlzIGRlcGxveV9nYXRlJ3MuCgpgcHJlc2VuY2VgIGlzIHRo ; ZSBjb250cm9sIGFuZCB0aGUgcmVyZWFkOiB3aGF0IGEgbm9kZSBob2xkcyBhbmQgd2hhdCBpdCBt ; dXN0Cm5vdC4gIGByZWxheWAgaXMgUkZDIDM5NzcgNi4zLjIgZHJpdmVuIGJ5IGhhbmQgb3Zlc...`
7. **install matrix.py** -- `base64 -d > $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJUaGUgdjAgbWF0cml4J3Mgb3duIE5OVFAgcGhhc2Vz ; LiAgTm8gZm4gbW9kdWxlIGlzIGltcG9ydGVkOyBDb25uIGlzCnRvb2xzL2RlcGxveV9nYXRlLnB5 ; J3MgZHJpdmVyLCBzaGlwcGVkIGJlc2lkZSB0aGlzIGZpbGUgYXMgZHJpdmUucHkuCgpFdmVyeSBw ; aGFzZSBwcmludHMgT05FIGpzb24gb2JqZWN0IHdob3NlIGtleXMgYXJlIGNvbW1hbmQgbmF...`
8. **native packaged operator subject** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; image=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host ; wrapper=packaging/fn-native ; runtime=/tank/fn/sbcl/bin/sbcl ; test -x "$image" || { echo "NATIVE-IMAGE-MISSING $image"; exit 4; } ; test -x "$wrapper" || { echo NATIVE-WRAPPER-MISSING; exit 4; } ; test -s "$image.core" || { echo NATIVE-...`
9. **node A native run directory** -- `mkdir -p $HOME/fn-deploy/native-dabebb84-0a8b592/a`
10. **node A native config exists** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; test -f /home/hbox/fn-native-matrix/a/fn.toml`
11. **node A native operator status** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml status`
12. **node B native run directory** -- `mkdir -p $HOME/fn-deploy/native-dabebb84-0a8b592/b`
13. **node B native config exists** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; test -f /home/hbox/fn-native-matrix/b/fn.toml`
14. **node B native operator status** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml status`
15. **loopback refusal: scratch store** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; mkdir -p $HOME/fn-deploy/native-dabebb84-0a8b592/loopback && env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native store $HOME/fn-deploy/native-dabebb84-0a8b592/loopback/store init fn.letters && printf '[store]\npath = "%s"\n[listener]\nhost = "0.0.0.0"\nport ...`
16. **loopback refusal: run** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; timeout 60 env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/loopback/fn.toml run`
17. **node A init scratch configuration** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; mkdir -p $HOME/fn-deploy/native-dabebb84-0a8b592/a/init && printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = 11295\n[control]\npath = "%s"\n' "$HOME/fn-deploy/native-dabebb84-0a8b592/a/init/store" "$HOME/fn-deploy/native-dabebb84-0a8b592/a/init/control.sock" > $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/fn.toml`
18. **node A operator init** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/fn.toml init fn.letters`
19. **start server (node A init owner, init-a)** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/server-init-a.log ; nohup env FN_NATIVE_CONTROL_FAULT=postpublish FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host-developer packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/fn.toml run > $HOME/fn-de...`
20. **install init.article** -- `base64 -d > $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/init.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG9uZSBkdXJhYmxlIG91dGNvbWUN ; Ck5ld3Nncm91cHM6IGZuLmxldHRlcnMNCkRhdGU6IFR1ZSwgMjIgU2VwIDIwMjYgMjA6NDM6Mzcg ; KzAwMDANCk1lc3NhZ2UtSUQ6IDxpbml0LWFAZXhhbXBsZS5pbnZhbGlkPg0KDQpTdWJtaXR0ZWQg ; b24gdGhlIEEgaW5pdCBzY3JhdGNoIG5vZGUgYnkgdGhlIHYwIG1hdHJpeC4NCg== ; FN_...`
21. **node A submission to the init scratch owner** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/fn.toml post --message-id '<init-a@example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/init.article --group fn.letters`
22. **stop server init-a** -- `if [ -f $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/server.pid ; fi ; echo stopped`
23. **node A recover the init scratch store** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/fn.toml recover`
24. **node A second operator init** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/fn.toml init fn.letters`
25. **node A recover after the second init** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/init/fn.toml recover`
26. **node B init scratch configuration** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; mkdir -p $HOME/fn-deploy/native-dabebb84-0a8b592/b/init && printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = 11296\n[control]\npath = "%s"\n' "$HOME/fn-deploy/native-dabebb84-0a8b592/b/init/store" "$HOME/fn-deploy/native-dabebb84-0a8b592/b/init/control.sock" > $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/fn.toml`
27. **node B operator init** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/fn.toml init fn.letters`
28. **start server (node B init owner, init-b)** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/server-init-b.log ; nohup env FN_NATIVE_CONTROL_FAULT=postpublish FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host-developer packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/fn.toml run > $HOME/fn-de...`
29. **install init.article** -- `base64 -d > $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/init.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG9uZSBkdXJhYmxlIG91dGNvbWUN ; Ck5ld3Nncm91cHM6IGZuLmxldHRlcnMNCkRhdGU6IFR1ZSwgMjIgU2VwIDIwMjYgMjA6NDM6NDMg ; KzAwMDANCk1lc3NhZ2UtSUQ6IDxpbml0LWJAZXhhbXBsZS5pbnZhbGlkPg0KDQpTdWJtaXR0ZWQg ; b24gdGhlIEIgaW5pdCBzY3JhdGNoIG5vZGUgYnkgdGhlIHYwIG1hdHJpeC4NCg== ; FN_...`
30. **node B submission to the init scratch owner** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/fn.toml post --message-id '<init-b@example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/init.article --group fn.letters`
31. **stop server init-b** -- `if [ -f $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/server.pid ; fi ; echo stopped`
32. **node B recover the init scratch store** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/fn.toml recover`
33. **node B second operator init** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/fn.toml init fn.letters`
34. **node B recover after the second init** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/init/fn.toml recover`
35. **node A group create fn.matrix** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml group create fn.matrix`
36. **node A group create fn.matrix.throwaway** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml group create fn.matrix.throwaway`
37. **node A group retire fn.matrix.throwaway** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml group retire fn.matrix.throwaway`
38. **node A group retire an unserved group** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml group retire fn.not.served`
39. **node A capacity scratch store** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; mkdir -p $HOME/fn-deploy/native-dabebb84-0a8b592/a/capacity && env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native store $HOME/fn-deploy/native-dabebb84-0a8b592/a/capacity/store init fn.letters && printf '[store]\npath = "%s"\n' "$HOME/fn-deploy/native-dabeb...`
40. **node A capacity 64** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/capacity/fn.toml capacity 64`
41. **node A capacity 1** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/capacity/fn.toml capacity 1`
42. **node A capacity owner config** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; printf '[listener]\nhost = "127.0.0.1"\nport = 11290\n[control]\npath = "%s"\n' $HOME/fn-deploy/native-dabebb84-0a8b592/a/capacity/control.sock >> $HOME/fn-deploy/native-dabebb84-0a8b592/a/capacity/fn.toml`
43. **start server (node A capacity owner, capacity-a)** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/a/capacity/server-capacity-a.log ; nohup env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/capacity/fn.toml run > $HOME/fn-deploy/native-dabebb84-0a8b592/a/cap...`
44. **install capacity.article** -- `base64 -d > $HOME/fn-deploy/native-dabebb84-0a8b592/a/capacity/capacity.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG92ZXIgdGhlIGNhcGFjaXR5DQpO ; ZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDIwOjQzOjUxICsw ; MDAwDQpNZXNzYWdlLUlEOiA8Y2FwYWNpdHktYUBleGFtcGxlLmludmFsaWQ+DQoNCnh4eHh4eHh4 ; eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eH...`
45. **node A post beyond the capacity** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/capacity/fn.toml post --message-id '<capacity-a@example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/a/capacity/capacity.article --group fn....`
46. **stop server capacity-a** -- `if [ -f $HOME/fn-deploy/native-dabebb84-0a8b592/a/capacity/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-dabebb84-0a8b592/a/capacity/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/a/capacity/server.pid ; fi ; echo stopped`
47. **native AUTHINFO secret** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; umask 077 && od -An -tx1 -N16 /dev/urandom | tr -d ' \n' > $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret && printf '%s\n%s\n' "$(cat $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret)" "$(cat $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret)" > $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secre...`
48. **node A principal set-password matrix** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; timeout 120 env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml principal set-password matrix < $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret.pair`
49. **node A principal list** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml principal list`
50. **node A auth-required scratch store** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; mkdir -p $HOME/fn-deploy/native-dabebb84-0a8b592/a/authgate && env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native store $HOME/fn-deploy/native-dabebb84-0a8b592/a/authgate/store init fn.letters && printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\...`
51. **node A auth-required scratch credential** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; timeout 120 env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/authgate/fn.toml principal set-password matrix < $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret.pair`
52. **start server (node A auth-required owner, authgate-a)** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/a/authgate/server-authgate-a.log ; nohup env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/authgate/fn.toml run > $HOME/fn-deploy/native-dabebb84-0a8b592/a/aut...`
53. **node A auth-required AUTHINFO gate** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py auth --port 11292 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret --msgid '<auth-gate-a@example.invalid>'`
54. **stop server authgate-a** -- `if [ -f $HOME/fn-deploy/native-dabebb84-0a8b592/a/authgate/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-dabebb84-0a8b592/a/authgate/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/a/authgate/server.pid ; fi ; echo stopped`
55. **node B group create fn.matrix** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml group create fn.matrix`
56. **node B group create fn.matrix.throwaway** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml group create fn.matrix.throwaway`
57. **node B group retire fn.matrix.throwaway** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml group retire fn.matrix.throwaway`
58. **node B group retire an unserved group** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml group retire fn.not.served`
59. **node B capacity scratch store** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; mkdir -p $HOME/fn-deploy/native-dabebb84-0a8b592/b/capacity && env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native store $HOME/fn-deploy/native-dabebb84-0a8b592/b/capacity/store init fn.letters && printf '[store]\npath = "%s"\n' "$HOME/fn-deploy/native-dabeb...`
60. **node B capacity 64** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/capacity/fn.toml capacity 64`
61. **node B capacity 1** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/capacity/fn.toml capacity 1`
62. **node B capacity owner config** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; printf '[listener]\nhost = "127.0.0.1"\nport = 11291\n[control]\npath = "%s"\n' $HOME/fn-deploy/native-dabebb84-0a8b592/b/capacity/control.sock >> $HOME/fn-deploy/native-dabebb84-0a8b592/b/capacity/fn.toml`
63. **start server (node B capacity owner, capacity-b)** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/b/capacity/server-capacity-b.log ; nohup env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/capacity/fn.toml run > $HOME/fn-deploy/native-dabebb84-0a8b592/b/cap...`
64. **install capacity.article** -- `base64 -d > $HOME/fn-deploy/native-dabebb84-0a8b592/b/capacity/capacity.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG92ZXIgdGhlIGNhcGFjaXR5DQpO ; ZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDIwOjQ0OjA0ICsw ; MDAwDQpNZXNzYWdlLUlEOiA8Y2FwYWNpdHktYkBleGFtcGxlLmludmFsaWQ+DQoNCnh4eHh4eHh4 ; eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eH...`
65. **node B post beyond the capacity** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/capacity/fn.toml post --message-id '<capacity-b@example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/b/capacity/capacity.article --group fn....`
66. **stop server capacity-b** -- `if [ -f $HOME/fn-deploy/native-dabebb84-0a8b592/b/capacity/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-dabebb84-0a8b592/b/capacity/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/b/capacity/server.pid ; fi ; echo stopped`
67. **node B principal set-password matrix** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; timeout 120 env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml principal set-password matrix < $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret.pair`
68. **node B principal list** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml principal list`
69. **node B auth-required scratch store** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; mkdir -p $HOME/fn-deploy/native-dabebb84-0a8b592/b/authgate && env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native store $HOME/fn-deploy/native-dabebb84-0a8b592/b/authgate/store init fn.letters && printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\...`
70. **node B auth-required scratch credential** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; timeout 120 env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/authgate/fn.toml principal set-password matrix < $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret.pair`
71. **start server (node B auth-required owner, authgate-b)** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/b/authgate/server-authgate-b.log ; nohup env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/b/authgate/fn.toml run > $HOME/fn-deploy/native-dabebb84-0a8b592/b/aut...`
72. **node B auth-required AUTHINFO gate** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py auth --port 11293 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret --msgid '<auth-gate-b@example.invalid>'`
73. **stop server authgate-b** -- `if [ -f $HOME/fn-deploy/native-dabebb84-0a8b592/b/authgate/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-dabebb84-0a8b592/b/authgate/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/b/authgate/server.pid ; fi ; echo stopped`
74. **node A path-identity** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml policy set path-identity a.gate.example.invalid`
75. **node B path-identity** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml policy set path-identity b.gate.example.invalid`
76. **node B configured port** -- `sed -n 's/^port *= *\([0-9][0-9]*\).*/\1/p' /home/hbox/fn-native-matrix/b/fn.toml | head -1`
77. **node A peer record for B** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml peer add b b.gate.example.invalid 127.0.0.1 11191 'fn.*' - 127.0.0.1 true`
78. **node A lists its peers** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml peer list`
79. **node A configured port** -- `sed -n 's/^port *= *\([0-9][0-9]*\).*/\1/p' /home/hbox/fn-native-matrix/a/fn.toml | head -1`
80. **node B peer record for A** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml peer add a a.gate.example.invalid 127.0.0.1 11190 'fn.*' - 127.0.0.1 true`
81. **node B lists its peers** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml peer list`
82. **start server (node A (native-operator), a-main)** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/a/server-a-main.log ; nohup env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml run > $HOME/fn-deploy/native-dabebb84-0a8b592/a/server-a-main.log 2>&1 < /dev/null & ...`
83. **node A pid** -- `cat $HOME/fn-deploy/native-dabebb84-0a8b592/a/server.pid`
84. **start server (node B (native-operator), b-main)** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/b/server-b-main.log ; nohup env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml run > $HOME/fn-deploy/native-dabebb84-0a8b592/b/server-b-main.log 2>&1 < /dev/null & ...`
85. **node B pid** -- `cat $HOME/fn-deploy/native-dabebb84-0a8b592/b/server.pid`
86. **node A server is alive** -- `kill -0 3269368 2>/dev/null && echo ALIVE || echo DEAD`
87. **node A serves fn.matrix** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py presence --port 11190 --groups fn.matrix`
88. **node A server is alive** -- `kill -0 3269368 2>/dev/null && echo ALIVE || echo DEAD`
89. **node A POST cycle** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py postcycle --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --user '' --secret ''`
90. **node A server is alive** -- `kill -0 3269368 2>/dev/null && echo ALIVE || echo DEAD`
91. **node A reader surface** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>'`
92. **node A server is alive** -- `kill -0 3269368 2>/dev/null && echo ALIVE || echo DEAD`
93. **node A AUTHINFO session** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py auth --port 11190 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret --msgid '<auth-a@example.invalid>'`
94. **node A server is alive** -- `kill -0 3269368 2>/dev/null && echo ALIVE || echo DEAD`
95. **install alpha.article** -- `base64 -d > $HOME/fn-deploy/native-dabebb84-0a8b592/a/alpha.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; QQ0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogVHVlLCAyMiBTZXAgMjAyNiAyMDo0NDoy ; MyArMDAwMA0KTWVzc2FnZS1JRDogPGFscGhhQGEuZXhhbXBsZS5pbnZhbGlkPg0KDQpXcml0dGVu ; IG9uIG5vZGUgQSBieSB0aGUgdjAgbWF0cml4IHRocm91Z2ggdGhlIG5hdGl2ZSBvcGVyYXRvci...`
96. **node A outcome accepted** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml post --message-id '<alpha@a.example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/a/alpha.article --group fn.letters`
97. **install alpha.article** -- `base64 -d > $HOME/fn-deploy/native-dabebb84-0a8b592/a/alpha.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; QQ0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogVHVlLCAyMiBTZXAgMjAyNiAyMDo0NDoy ; MyArMDAwMA0KTWVzc2FnZS1JRDogPGFscGhhQGEuZXhhbXBsZS5pbnZhbGlkPg0KDQpXcml0dGVu ; IG9uIG5vZGUgQSBieSB0aGUgdjAgbWF0cml4IHRocm91Z2ggdGhlIG5hdGl2ZSBvcGVyYXRvci...`
98. **node A outcome duplicate** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml post --message-id '<alpha@a.example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/a/alpha.article --group fn.letters`
99. **install alpha-conflict.article** -- `base64 -d > $HOME/fn-deploy/native-dabebb84-0a8b592/a/alpha-conflict.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; QQ0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogVHVlLCAyMiBTZXAgMjAyNiAyMDo0NDoy ; MyArMDAwMA0KTWVzc2FnZS1JRDogPGFscGhhQGEuZXhhbXBsZS5pbnZhbGlkPg0KDQpXcml0dGVu ; IG9uIG5vZGUgQSBieSB0aGUgdjAgbWF0cml4IHRocm91Z2ggdGhlIG5hdGl2ZSBvc...`
100. **node A outcome refused** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml post --message-id '<alpha@a.example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/a/alpha-conflict.article --group fn.letters`
101. **install stream-a.article** -- `base64 -d > $HOME/fn-deploy/native-dabebb84-0a8b592/a/stream-a.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IGZvciB0aGUgc3RyZWFtaW5nIG9m ; ZmVyDQpOZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDIwOjQ0 ; OjI1ICswMDAwDQpNZXNzYWdlLUlEOiA8c3RyZWFtLWFAZXhhbXBsZS5pbnZhbGlkPg0KDQpTZWVk ; ZWQgb24gbm9kZSBBIGJ5IHRoZSB2MCBtYXRyaXguDQo= ; FN_GATE_EOF ; chmod 644 ...`
102. **node A seed <stream-a@example.invalid>** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml post --message-id '<stream-a@example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/a/stream-a.article --group fn.letters`
103. **node B server is alive** -- `kill -0 3269509 2>/dev/null && echo ALIVE || echo DEAD`
104. **node B serves fn.matrix** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py presence --port 11191 --groups fn.matrix`
105. **node B server is alive** -- `kill -0 3269509 2>/dev/null && echo ALIVE || echo DEAD`
106. **node B POST cycle** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py postcycle --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --user '' --secret ''`
107. **node B server is alive** -- `kill -0 3269509 2>/dev/null && echo ALIVE || echo DEAD`
108. **node B reader surface** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py surface --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>'`
109. **node B server is alive** -- `kill -0 3269509 2>/dev/null && echo ALIVE || echo DEAD`
110. **node B AUTHINFO session** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py auth --port 11191 --group fn.letters --user matrix --secret-file $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/auth.secret --msgid '<auth-b@example.invalid>'`
111. **node B server is alive** -- `kill -0 3269509 2>/dev/null && echo ALIVE || echo DEAD`
112. **install beta.article** -- `base64 -d > $HOME/fn-deploy/native-dabebb84-0a8b592/b/beta.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; Qg0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogVHVlLCAyMiBTZXAgMjAyNiAyMDo0NDoz ; MCArMDAwMA0KTWVzc2FnZS1JRDogPGJldGFAYi5leGFtcGxlLmludmFsaWQ+DQoNCldyaXR0ZW4g ; b24gbm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXggdGhyb3VnaCB0aGUgbmF0aXZlIG9wZXJhdG9yLg0...`
113. **node B outcome accepted** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml post --message-id '<beta@b.example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/b/beta.article --group fn.letters`
114. **install beta.article** -- `base64 -d > $HOME/fn-deploy/native-dabebb84-0a8b592/b/beta.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; Qg0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogVHVlLCAyMiBTZXAgMjAyNiAyMDo0NDoz ; MCArMDAwMA0KTWVzc2FnZS1JRDogPGJldGFAYi5leGFtcGxlLmludmFsaWQ+DQoNCldyaXR0ZW4g ; b24gbm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXggdGhyb3VnaCB0aGUgbmF0aXZlIG9wZXJhdG9yLg0...`
115. **node B outcome duplicate** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml post --message-id '<beta@b.example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/b/beta.article --group fn.letters`
116. **install beta-conflict.article** -- `base64 -d > $HOME/fn-deploy/native-dabebb84-0a8b592/b/beta-conflict.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG91dGNvbWUsIHdyaXR0ZW4gb24g ; Qg0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogVHVlLCAyMiBTZXAgMjAyNiAyMDo0NDoz ; MCArMDAwMA0KTWVzc2FnZS1JRDogPGJldGFAYi5leGFtcGxlLmludmFsaWQ+DQoNCldyaXR0ZW4g ; b24gbm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXggdGhyb3VnaCB0aGUgbmF0aXZlIG9wZX...`
117. **node B outcome refused** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml post --message-id '<beta@b.example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/b/beta-conflict.article --group fn.letters`
118. **install stream-b.article** -- `base64 -d > $HOME/fn-deploy/native-dabebb84-0a8b592/b/stream-b.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IGZvciB0aGUgc3RyZWFtaW5nIG9m ; ZmVyDQpOZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDIwOjQ0 ; OjMzICswMDAwDQpNZXNzYWdlLUlEOiA8c3RyZWFtLWJAZXhhbXBsZS5pbnZhbGlkPg0KDQpTZWVk ; ZWQgb24gbm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXguDQo= ; FN_GATE_EOF ; chmod 644 ...`
119. **node B seed <stream-b@example.invalid>** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml post --message-id '<stream-b@example.invalid>' --payload $HOME/fn-deploy/native-dabebb84-0a8b592/b/stream-b.article --group fn.letters`
120. **node A server is alive** -- `kill -0 3269368 2>/dev/null && echo ALIVE || echo DEAD`
121. **node B server is alive** -- `kill -0 3269509 2>/dev/null && echo ALIVE || echo DEAD`
122. **nntplib interpreter** -- `for p in python3.12 python3 ; do command -v $p >/dev/null 2>&1 && $p -c 'import nntplib' 2>/dev/null && { echo USE $p; exit 0; }; done; echo NONE`
123. **install independent.py** -- `base64 -d > $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/independent.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJBIHN0ZGxpYi1ubnRwbGliIHJlYWRlciBhZ2FpbnN0 ; IGEgbGl2ZSBmbiBub2RlLiAgTm8gZm4gbW9kdWxlIGlzIGltcG9ydGVkLAphbmQgbm8gZnJhbWlu ; ZywgZm9sZGluZyBvciByZXNwb25zZSBwYXJzaW5nIGluIHRoaXMgZmlsZSBpcyBmbidzOiBubnRw ; bGliCmRvZXMgYWxsIG9mIGl0LiAgVGhlIGZpeHR1cmUgaXMgcGFzc2VkIGluLCBzby...`
124. **independent nntplib client on node A** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3.12 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/independent.py --port 11190 --group fn.letters --msgid '<native-matrix-e5b62b396a22-a@example.invalid>' --absent '<absent@example.invalid>' --user '' --secret ''`
125. **independent nntplib client on node B** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3.12 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/independent.py --port 11191 --group fn.letters --msgid '<native-matrix-0fcd55edd32d-b@example.invalid>' --absent '<absent@example.invalid>' --user '' --secret ''`
126. **node B server is alive** -- `kill -0 3269509 2>/dev/null && echo ALIVE || echo DEAD`
127. **transit AB: offer <alpha@a.example.invalid> from A to B** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11190 --to-port 11191 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
128. **transit AB: CHECK/TAKETHIS <stream-a@example.invalid> from A to B** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py stream --from-port 11190 --to-port 11191 --msgid '<stream-a@example.invalid>'`
129. **node A server is alive** -- `kill -0 3269368 2>/dev/null && echo ALIVE || echo DEAD`
130. **transit BA: offer <beta@b.example.invalid> from B to A** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py relay --from-port 11191 --to-port 11190 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
131. **transit BA: CHECK/TAKETHIS <stream-b@example.invalid> from B to A** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py stream --from-port 11191 --to-port 11190 --msgid '<stream-b@example.invalid>'`
132. **node A server is alive** -- `kill -0 3269368 2>/dev/null && echo ALIVE || echo DEAD`
133. **node A capability pins** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py pins --port 11190 --group fn.letters --user '' --secret ''`
134. **node B server is alive** -- `kill -0 3269509 2>/dev/null && echo ALIVE || echo DEAD`
135. **node B capability pins** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py pins --port 11191 --group fn.letters --user '' --secret ''`
136. **node A server is alive** -- `kill -0 3269368 2>/dev/null && echo ALIVE || echo DEAD`
137. **node B server is alive** -- `kill -0 3269509 2>/dev/null && echo ALIVE || echo DEAD`
138. **a second reader across node A's POST** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/matrix.py concurrent --port 11190 --group fn.letters --msgid '<concurrent@example.invalid>' --user '' --secret ''`
139. **node A server is alive** -- `kill -0 3269368 2>/dev/null && echo ALIVE || echo DEAD`
140. **node B server is alive** -- `kill -0 3269509 2>/dev/null && echo ALIVE || echo DEAD`
141. **live reconfiguration: declare fn.matrix.live on node A** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml group create fn.matrix.live`
142. **node A serves fn.matrix.live without a restart** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; python3 $HOME/fn-deploy/native-dabebb84-0a8b592/gate-run/feed.py presence --port 11190 --groups fn.matrix.live`
143. **node A configured store** -- `awk '/^\[/ {t=$0} t=="[store]" && /^path *=/ {sub(/^path *= *"/, ""); sub(/".*$/, ""); print; exit}' /home/hbox/fn-native-matrix/a/fn.toml`
144. **offline configuration over node A's store** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; mkdir -p $HOME/fn-deploy/native-dabebb84-0a8b592/a/offline && printf '[store]\npath = "%s"\n[control]\npath = "%s"\n' /home/hbox/fn-native-matrix/a/store "$HOME/fn-deploy/native-dabebb84-0a8b592/a/offline/never-bound.sock" > $HOME/fn-deploy/native-dabebb84-0a8b592/a/offline/fn.toml`
145. **offline group create while the owner holds the store** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-deploy/native-dabebb84-0a8b592/a/offline/fn.toml group create fn.matrix.offline`
146. **native public peering/restart witness** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; image=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; launcher_before=$(digest packaging/fn-native) ; runtime_before=$(digest "$image") ; core_...`
147. **native protected peering witness** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; image=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host ; digest() { ; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}' ; else shasum -a 256 "$1" | awk '{print $1}'; fi ; } ; runtime_path=/tank/fn/sbcl/bin/sbcl ; test -x "$runtime_path" || exit 4 ; runtime_expecte...`
148. **stop server node A (main)** -- `if [ -f $HOME/fn-deploy/native-dabebb84-0a8b592/a/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-dabebb84-0a8b592/a/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/a/server.pid ; fi ; echo stopped`
149. **node A store after the stop** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml status`
150. **node A recover after the stop** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml recover`
151. **node A log tail** -- `tail -12 $HOME/fn-deploy/native-dabebb84-0a8b592/a/server-a-main.log 2>/dev/null || echo NO-LOG`
152. **stop server node B (main)** -- `if [ -f $HOME/fn-deploy/native-dabebb84-0a8b592/b/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-dabebb84-0a8b592/b/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/b/server.pid ; fi ; echo stopped`
153. **node B store after the stop** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml status`
154. **node B recover after the stop** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/b/fn.toml recover`
155. **node B log tail** -- `tail -12 $HOME/fn-deploy/native-dabebb84-0a8b592/b/server-b-main.log 2>/dev/null || echo NO-LOG`
156. **peer remove a peer that is not there** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml peer remove no-such-peer`
157. **peer remove the configured peer** -- `cd $HOME/fn-deploy/native-dabebb84-0a8b592 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator /home/hbox/fn-native-matrix/a/fn.toml peer remove b`
158. **stop server node A (main)** -- `if [ -f $HOME/fn-deploy/native-dabebb84-0a8b592/a/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-dabebb84-0a8b592/a/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/a/server.pid ; fi ; echo stopped`
159. **stop the tap in front of node A** -- `if [ -f $HOME/fn-deploy/native-dabebb84-0a8b592/a/tap.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-dabebb84-0a8b592/a/tap.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 10); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/a/tap.pid ; fi ; echo stopped`
160. **stop server node B (main)** -- `if [ -f $HOME/fn-deploy/native-dabebb84-0a8b592/b/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-dabebb84-0a8b592/b/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/b/server.pid ; fi ; echo stopped`
161. **stop the tap in front of node B** -- `if [ -f $HOME/fn-deploy/native-dabebb84-0a8b592/b/tap.pid ]; then ; pid=$(cat $HOME/fn-deploy/native-dabebb84-0a8b592/b/tap.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 10); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/native-dabebb84-0a8b592/b/tap.pid ; fi ; echo stopped`
162. **stray fn processes** -- `pgrep -f 'fn-deploy/native-dabebb84-0a8b592' >/dev/null 2>&1 && echo STRAY || echo CLEAN`
163. **remove the deploy tree** -- `rm -rf $HOME/fn-deploy/native-dabebb84-0a8b592`
164. **release deploy lock** -- `rmdir $HOME/fn-deploy/.locks/native-dabebb84-0a8b592.lock`

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
NATIVE-IMAGE-DIGEST 21ba38c1a66d96c32c8e50269b852cabd07ae15548306781aafa084cb0e6af32
NATIVE-RUNTIME-DIGEST b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5
NATIVE-CORE-DIGEST 6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf
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
--- 15 loopback refusal: scratch store (rc=0)
initialized /home/hbox/fn-deploy/native-dabebb84-0a8b592/loopback/store
--- 16 loopback refusal: run (rc=5)
usage operator request (CONFIGURATION INVALID)
--- 17 node A init scratch configuration (rc=0)
--- 18 node A operator init (rc=0)
initialized /home/hbox/fn-deploy/native-dabebb84-0a8b592/a/init/store
accepted operator init
--- 19 start server (node A init owner, init-a) (rc=0)
LISTENING 11295
--- 20 install init.article (rc=0)
--- 21 node A submission to the init scratch owner (rc=3)
uncertain operator post UNCERTAIN
--- 22 stop server init-a (rc=0)
stopped
--- 23 node A recover the init scratch store (rc=0)
recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none
accepted operator RECOVER
--- 24 node A second operator init (rc=1)
refused operator init STORE-EXISTS
--- 25 node A recover after the second init (rc=0)
recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none
accepted operator RECOVER
--- 26 node B init scratch configuration (rc=0)
--- 27 node B operator init (rc=0)
initialized /home/hbox/fn-deploy/native-dabebb84-0a8b592/b/init/store
accepted operator init
--- 28 start server (node B init owner, init-b) (rc=0)
LISTENING 11296
--- 29 install init.article (rc=0)
--- 30 node B submission to the init scratch owner (rc=3)
uncertain operator post UNCERTAIN
--- 31 stop server init-b (rc=0)
stopped
--- 32 node B recover the init scratch store (rc=0)
recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none
accepted operator RECOVER
--- 33 node B second operator init (rc=1)
refused operator init STORE-EXISTS
--- 34 node B recover after the second init (rc=0)
recovered transactions=1 articles=1 staging-orphans=0 anchor=none checkpoint=none
accepted operator RECOVER
--- 35 node A group create fn.matrix (rc=0)
configured generation=2 record=00000002.cfg verification=VERIFIED
accepted operator group
--- 36 node A group create fn.matrix.throwaway (rc=0)
configured generation=3 record=00000003.cfg verification=VERIFIED
accepted operator group
--- 37 node A group retire fn.matrix.throwaway (rc=0)
configured generation=4 record=00000004.cfg verification=VERIFIED
accepted operator group
--- 38 node A group retire an unserved group (rc=1)
refused operator group administrative configuration refused: NO-SUCH-GROUP
--- 39 node A capacity scratch store (rc=0)
initialized /home/hbox/fn-deploy/native-dabebb84-0a8b592/a/capacity/store
--- 40 node A capacity 64 (rc=0)
configured generation=2 record=00000002.cfg verification=VERIFIED
accepted operator capacity
--- 41 node A capacity 1 (rc=0)
configured generation=3 record=00000003.cfg verification=VERIFIED
accepted operator capacity
--- 42 node A capacity owner config (rc=0)
--- 43 start server (node A capacity owner, capacity-a) (rc=0)
LISTENING 11290
--- 44 install capacity.article (rc=0)
--- 45 node A post beyond the capacity (rc=1)
refused operator post REFUSED
--- 46 stop server capacity-a (rc=0)
stopped
--- 47 native AUTHINFO secret (rc=0)
SECRET-READY
--- 48 node A principal set-password matrix (rc=0)
Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true
accepted operator principal set-password restart-required
--- 49 node A principal list (rc=0)
matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true
accepted operator principal list
--- 50 node A auth-required scratch store (rc=0)
initialized /home/hbox/fn-deploy/native-dabebb84-0a8b592/a/authgate/store
--- 51 node A auth-required scratch credential (rc=0)
Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true
accepted operator principal set-password restart-required
--- 52 start server (node A auth-required owner, authgate-a) (rc=0)
LISTENING 11292
--- 53 node A auth-required AUTHINFO gate (rc=0)
{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BEFORE": "480 authentication required", "AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "CAPABILITIES AFTER": "101 capability list follows", "advertised_after": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION"], "AUTHINFO WITHDRAWN": true, "POST AFTER": "340 send article to be posted", "POST AFTER COMMIT": "240 article received OK", "AUTHINFO WRONG": "481 authentication failed", "ok": true}
--- 54 stop server authgate-a (rc=0)
stopped
--- 55 node B group create fn.matrix (rc=0)
configured generation=2 record=00000002.cfg verification=VERIFIED
accepted operator group
--- 56 node B group create fn.matrix.throwaway (rc=0)
configured generation=3 record=00000003.cfg verification=VERIFIED
accepted operator group
--- 57 node B group retire fn.matrix.throwaway (rc=0)
configured generation=4 record=00000004.cfg verification=VERIFIED
accepted operator group
--- 58 node B group retire an unserved group (rc=1)
refused operator group administrative configuration refused: NO-SUCH-GROUP
--- 59 node B capacity scratch store (rc=0)
initialized /home/hbox/fn-deploy/native-dabebb84-0a8b592/b/capacity/store
--- 60 node B capacity 64 (rc=0)
configured generation=2 record=00000002.cfg verification=VERIFIED
accepted operator capacity
--- 61 node B capacity 1 (rc=0)
configured generation=3 record=00000003.cfg verification=VERIFIED
accepted operator capacity
--- 62 node B capacity owner config (rc=0)
--- 63 start server (node B capacity owner, capacity-b) (rc=0)
LISTENING 11291
--- 64 install capacity.article (rc=0)
--- 65 node B post beyond the capacity (rc=1)
refused operator post REFUSED
--- 66 stop server capacity-b (rc=0)
stopped
--- 67 node B principal set-password matrix (rc=0)
Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true
accepted operator principal set-password restart-required
--- 68 node B principal list (rc=0)
matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true
accepted operator principal list
--- 69 node B auth-required scratch store (rc=0)
initialized /home/hbox/fn-deploy/native-dabebb84-0a8b592/b/authgate/store
--- 70 node B auth-required scratch credential (rc=0)
Password: Confirm password: matrix principal=a51e6e0486cb040737b29d0d8d52465c8c850156ca110b9b23973c03a8cc1ac3 posting=true
accepted operator principal set-password restart-required
--- 71 start server (node B auth-required owner, authgate-b) (rc=0)
LISTENING 11293
--- 72 node B auth-required AUTHINFO gate (rc=0)
{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BEFORE": "480 authentication required", "AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "CAPABILITIES AFTER": "101 capability list follows", "advertised_after": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION"], "AUTHINFO WITHDRAWN": true, "POST AFTER": "340 send article to be posted", "POST AFTER COMMIT": "240 article received OK", "AUTHINFO WRONG": "481 authentication failed", "ok": true}
--- 73 stop server authgate-b (rc=0)
stopped
--- 74 node A path-identity (rc=0)
configured generation=5 record=00000005.cfg verification=VERIFIED
accepted operator policy
--- 75 node B path-identity (rc=0)
configured generation=5 record=00000005.cfg verification=VERIFIED
accepted operator policy
--- 76 node B configured port (rc=0)
11191
--- 77 node A peer record for B (rc=0)
configured generation=6 record=00000006.cfg verification=VERIFIED
accepted operator peer
--- 78 node A lists its peers (rc=0)
b path-identity=b.gate.example.invalid address=127.0.0.1 port=11191 security=clear inbound=fn.* outbound=- auth=source-address:127.0.0.1
accepted operator peer
--- 79 node A configured port (rc=0)
11190
--- 80 node B peer record for A (rc=0)
configured generation=6 record=00000006.cfg verification=VERIFIED
accepted operator peer
--- 81 node B lists its peers (rc=0)
a path-identity=a.gate.example.invalid address=127.0.0.1 port=11190 security=clear inbound=fn.* outbound=- auth=source-address:127.0.0.1
accepted operator peer
--- 82 start server (node A (native-operator), a-main) (rc=0)
LISTENING 11190
--- 83 node A pid (rc=0)
3269368
--- 84 start server (node B (native-operator), b-main) (rc=0)
LISTENING 11191
--- 85 node B pid (rc=0)
3269509
--- 86 node A server is alive (rc=0)
ALIVE
--- 87 node A serves fn.matrix (rc=0)
{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}
--- 88 node A server is alive (rc=0)
ALIVE
--- 89 node A POST cycle (rc=0)
{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-e5b62b396a22-a@example.invalid> article follows", "DUPLICATE POST": "340 send article to be posted", "DUPLICATE": "441 posting failed; the article was refused", "DATE AFTER DUPLICATE": "111 20260922204420", "counted": true, "ok": true}
--- 90 node A server is alive (rc=0)
ALIVE
--- 91 node A reader surface (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "MODE READER": "200 posting allowed", "LIST ACTIVE": "215 list of active newsgroups follows", "LIST NEWSGROUPS": "215 list of newsgroups follows", "LIST OVERVIEW.FMT": "215 order of fields in overview database", "LIST ACTIVE.TIMES": "215 information follows", "LIST HEADERS": "215 field list follows", "LIST NEWSGROUPS WILDMAT": "215 list of newsgroups follows", "GROUP": "211 1 1 1 fn.letters", "group_count": 1, "group_first": 1, "group_last": 1, "LISTGROUP": "211 1 1 1 fn.letters list follows", "ARTICLE": "220 1 <native-matrix-e5b62b396a22-a@example.invalid> article follows", "HEAD": "221 1 <native-matrix-e5b62b396a22-a@example.invalid> headers follow", "BODY": "222 1 <native-matrix-e5b62b396a22-a@example.invalid> body follows", "STAT": "223 1 <native-matrix-e5b62b396a22-a@example.invalid> retrieved", "ARTICLE MSGID": "220 0 <native-matrix-e5b62b396a22-a@example.invalid> article follows", "ARTICLE ABSENT": "430 no article with that message-id", "OVER": "224 overview information follows", "OVER RANGE": "224 overview information follows", "HDR": "225 headers follow", "XOVER": "224 overview information follows", "XHDR": "221 header follows", "XPAT": "221 header follows", "NEWNEWS": "230 list of new articles by message-id follows", "NEWNEWS FUTURE": "230 list of new articles by message-id follows", "NEWNEWS SYNTAX": "501 syntax error", "NEXT": "421 no next article", "LAST": "422 no previous article", "DATE": "111 20260922204421", "HELP": "100 help text follows", "UNKNOWN": "500 command not recognized", "FRAMING": "111 20260922204421", "FRAMING SAME": true, "ok": true}
--- 92 node A server is alive (rc=0)
ALIVE
--- 93 node A AUTHINFO session (rc=0)
{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BEFORE": "340 send article to be posted", "POST BEFORE CLOSE": "441 posting failed; the article is not valid syntax", "AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "CAPABILITIES AFTER": "101 capability list follows", "advertised_after": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING"], "AUTHINFO WITHDRAWN": true, "POST AFTER": "340 send article to be posted", "POST AFTER COMMIT": "240 article received OK", "AUTHINFO WRONG": "481 authentication failed", "ok": true}
--- 94 node A server is alive (rc=0)
ALIVE
--- 95 install alpha.article (rc=0)
--- 96 node A outcome accepted (rc=0)
accepted operator post ACCEPTED
--- 97 install alpha.article (rc=0)
--- 98 node A outcome duplicate (rc=0)
accepted operator post DUPLICATE
--- 99 install alpha-conflict.article (rc=0)
--- 100 node A outcome refused (rc=1)
refused operator post REFUSED
--- 101 install stream-a.article (rc=0)
--- 102 node A seed <stream-a@example.invalid> (rc=0)
accepted operator post ACCEPTED
--- 103 node B server is alive (rc=0)
ALIVE
--- 104 node B serves fn.matrix (rc=0)
{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}
--- 105 node B server is alive (rc=0)
ALIVE
--- 106 node B POST cycle (rc=0)
{"GROUP BEFORE": "211 0 1 0 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 1 1 1 fn.letters", "FRESH ARTICLE": "220 0 <native-matrix-0fcd55edd32d-b@example.invalid> article follows", "DUPLICATE POST": "340 send article to be posted", "DUPLICATE": "441 posting failed; the article was refused", "DATE AFTER DUPLICATE": "111 20260922204428", "counted": true, "ok": true}
--- 107 node B server is alive (rc=0)
ALIVE
--- 108 node B reader surface (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "MODE READER": "200 posting allowed", "LIST ACTIVE": "215 list of active newsgroups follows", "LIST NEWSGROUPS": "215 list of newsgroups follows", "LIST OVERVIEW.FMT": "215 order of fields in overview database", "LIST ACTIVE.TIMES": "215 information follows", "LIST HEADERS": "215 field list follows", "LIST NEWSGROUPS WILDMAT": "215 list of newsgroups follows", "GROUP": "211 1 1 1 fn.letters", "group_count": 1, "group_first": 1, "group_last": 1, "LISTGROUP": "211 1 1 1 fn.letters list follows", "ARTICLE": "220 1 <native-matrix-0fcd55edd32d-b@example.invalid> article follows", "HEAD": "221 1 <native-matrix-0fcd55edd32d-b@example.invalid> headers follow", "BODY": "222 1 <native-matrix-0fcd55edd32d-b@example.invalid> body follows", "STAT": "223 1 <native-matrix-0fcd55edd32d-b@example.invalid> retrieved", "ARTICLE MSGID": "220 0 <native-matrix-0fcd55edd32d-b@example.invalid> article follows", "ARTICLE ABSENT": "430 no article with that message-id", "OVER": "224 overview information follows", "OVER RANGE": "224 overview information follows", "HDR": "225 headers follow", "XOVER": "224 overview information follows", "XHDR": "221 header follows", "XPAT": "221 header follows", "NEWNEWS": "230 list of new articles by message-id follows", "NEWNEWS FUTURE": "230 list of new articles by message-id follows", "NEWNEWS SYNTAX": "501 syntax error", "NEXT": "421 no next article", "LAST": "422 no previous article", "DATE": "111 20260922204429", "HELP": "100 help text follows", "UNKNOWN": "500 command not recognized", "FRAMING": "111 20260922204429", "FRAMING SAME": true, "ok": true}
--- 109 node B server is alive (rc=0)
ALIVE
--- 110 node B AUTHINFO session (rc=0)
{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BEFORE": "340 send article to be posted", "POST BEFORE CLOSE": "441 posting failed; the article is not valid syntax", "AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "CAPABILITIES AFTER": "101 capability list follows", "advertised_after": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING"], "AUTHINFO WITHDRAWN": true, "POST AFTER": "340 send article to be posted", "POST AFTER COMMIT": "240 article received OK", "AUTHINFO WRONG": "481 authentication failed", "ok": true}
--- 111 node B server is alive (rc=0)
ALIVE
--- 112 install beta.article (rc=0)
--- 113 node B outcome accepted (rc=0)
accepted operator post ACCEPTED
--- 114 install beta.article (rc=0)
--- 115 node B outcome duplicate (rc=0)
accepted operator post DUPLICATE
--- 116 install beta-conflict.article (rc=0)
--- 117 node B outcome refused (rc=1)
refused operator post REFUSED
--- 118 install stream-b.article (rc=0)
--- 119 node B seed <stream-b@example.invalid> (rc=0)
accepted operator post ACCEPTED
--- 120 node A server is alive (rc=0)
ALIVE
--- 121 node B server is alive (rc=0)
ALIVE
--- 122 nntplib interpreter (rc=0)
USE python3.12
--- 123 install independent.py (rc=0)
--- 124 independent nntplib client on node A (rc=0)
/home/hbox/fn-deploy/native-dabebb84-0a8b592/gate-run/independent.py:6: DeprecationWarning: 'nntplib' is deprecated and slated for removal in Python 3.13
  import argparse, json, nntplib, platform, sys
{"absent": "430 no article with that message-id", "article_has_msgid": true, "article_lines": 10, "body_lines": 1, "capabilities": ["AUTHINFO", "HDR", "IHAVE", "IMPLEMENTATION", "LIST", "NEWNEWS", "OVER", "POST", "READER", "STREAMING", "VERSION"], "client": "stdlib nntplib", "commands": ["CAPABILITIES", "GROUP", "STAT", "ARTICLE", "HEAD", "BODY", "OVER", "LIST", "ARTICLE (absent)", "QUIT"], "group": {"count": 4, "first": 1, "last": 4, "name": "fn.letters"}, "head_lines": 8, "list_groups": ["fn.letters", "fn.matrix", "fn.matrix.throwaway"], "ok": true, "over_rows": 4, "python": "3.12.7", "quit": "205 closing connection", "stat": [1, "<native-matrix-e5b62b396a22-a@example.invalid>"], "welcome": "200 fn-nntp experimental server ready"}
--- 125 independent nntplib client on node B (rc=0)
/home/hbox/fn-deploy/native-dabebb84-0a8b592/gate-run/independent.py:6: DeprecationWarning: 'nntplib' is deprecated and slated for removal in Python 3.13
  import argparse, json, nntplib, platform, sys
{"absent": "430 no article with that message-id", "article_has_msgid": true, "article_lines": 10, "body_lines": 1, "capabilities": ["AUTHINFO", "HDR", "IHAVE", "IMPLEMENTATION", "LIST", "NEWNEWS", "OVER", "POST", "READER", "STREAMING", "VERSION"], "client": "stdlib nntplib", "commands": ["CAPABILITIES", "GROUP", "STAT", "ARTICLE", "HEAD", "BODY", "OVER", "LIST", "ARTICLE (absent)", "QUIT"], "group": {"count": 4, "first": 1, "last": 4, "name": "fn.letters"}, "head_lines": 8, "list_groups": ["fn.letters", "fn.matrix", "fn.matrix.throwaway"], "ok": true, "over_rows": 4, "python": "3.12.7", "quit": "205 closing connection", "stat": [1, "<native-matrix-0fcd55edd32d-b@example.invalid>"], "welcome": "200 fn-nntp experimental server ready"}
--- 126 node B server is alive (rc=0)
ALIVE
--- 127 transit AB: offer <alpha@a.example.invalid> from A to B (rc=0)
{"msgid": "<alpha@a.example.invalid>", "source": "220 0 <alpha@a.example.invalid> article follows", "source_lines": 7, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "ihave_advertised": true, "streaming_advertised": true, "mode_stream": "203 streaming permitted", "offer": "335 send it; end with <CR-LF>.<CR-LF>", "transit": true, "transfer": "235 article transferred OK", "duplicate": "435 duplicate", "loop_offer": "335 send it; end with <CR-LF>.<CR-LF>", "loop_result": "437 transfer rejected; path loop", "check_duplicate": "438 <alpha@a.example.invalid>", "takethis_duplicate": "439 <alpha@a.example.invalid>", "check_fresh": "238 <fresh.check@gate.example.invalid>", "reread": "220 0 <alpha@a.example.invalid> article follows", "identical": true, "loop_absent": "430 no article with that message-id", "streaming_ok": true, "ok": true}
--- 128 transit AB: CHECK/TAKETHIS <stream-a@example.invalid> from A to B (rc=0)
{"SOURCE": "220 0 <stream-a@example.invalid> article follows", "MODE STREAM": "203 streaming permitted", "CHECK": "238 <stream-a@example.invalid>", "TAKETHIS": "239 <stream-a@example.invalid>", "CHECK AGAIN": "438 <stream-a@example.invalid>", "TAKETHIS AGAIN": "439 <stream-a@example.invalid>", "REREAD": "220 0 <stream-a@example.invalid> article follows", "IDENTICAL": true, "ok": true}
--- 129 node A server is alive (rc=0)
ALIVE
--- 130 transit BA: offer <beta@b.example.invalid> from B to A (rc=0)
{"msgid": "<beta@b.example.invalid>", "source": "220 0 <beta@b.example.invalid> article follows", "source_lines": 7, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "ihave_advertised": true, "streaming_advertised": true, "mode_stream": "203 streaming permitted", "offer": "335 send it; end with <CR-LF>.<CR-LF>", "transit": true, "transfer": "235 article transferred OK", "duplicate": "435 duplicate", "loop_offer": "335 send it; end with <CR-LF>.<CR-LF>", "loop_result": "437 transfer rejected; path loop", "check_duplicate": "438 <beta@b.example.invalid>", "takethis_duplicate": "439 <beta@b.example.invalid>", "check_fresh": "238 <fresh.check@gate.example.invalid>", "reread": "220 0 <beta@b.example.invalid> article follows", "identical": true, "loop_absent": "430 no article with that message-id", "streaming_ok": true, "ok": true}
--- 131 transit BA: CHECK/TAKETHIS <stream-b@example.invalid> from B to A (rc=0)
{"SOURCE": "220 0 <stream-b@example.invalid> article follows", "MODE STREAM": "203 streaming permitted", "CHECK": "238 <stream-b@example.invalid>", "TAKETHIS": "239 <stream-b@example.invalid>", "CHECK AGAIN": "438 <stream-b@example.invalid>", "TAKETHIS AGAIN": "439 <stream-b@example.invalid>", "REREAD": "220 0 <stream-b@example.invalid> article follows", "IDENTICAL": true, "ok": true}
--- 132 node A server is alive (rc=0)
ALIVE
--- 133 node A capability pins (rc=0)
{"advertised": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "answered": {"READER": "211 6 1 6 fn.letters", "POST": "340 send article to be posted", "POST CLOSE": "441 posting failed; the article is not valid syntax", "IHAVE": "335 send it; end with <CR-LF>.<CR-LF>", "IHAVE CLOSE": "437 transfer rejected; not a valid article", "STREAMING": "203 streaming permitted", "OVER": "412 no newsgroup selected", "HDR": "412 no newsgroup selected", "LIST": "215 list of active newsgroups follows", "NEWNEWS": "230 list of new articles by message-id follows", "AUTHINFO": "381 password required", "STARTTLS": "580 can not initiate TLS negotiation", "MODE-READER": "200 posting allowed", "XOVER": "412 no newsgroup selected", "XHDR": "412 no newsgroup selected", "XPAT": "412 no newsgroup selected", "LISTGROUP": "211 6 1 6 fn.letters list follows", "CHECK": "238 <pin.check@matrix.example.invalid>", "TAKETHIS": "439 <pin.take@matrix.example.invalid>"}, "dispatched": ["READER", "POST", "IHAVE", "STREAMING", "OVER", "HDR", "LIST", "NEWNEWS", "AUTHINFO", "STARTTLS", "MODE-READER", "XOVER", "XHDR", "XPAT", "LISTGROUP", "CHECK", "TAKETHIS"], "login": {}, "advertised_not_dispatched": [], "dispatched_not_advertised": [], "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "ok": true}
--- 134 node B server is alive (rc=0)
ALIVE
--- 135 node B capability pins (rc=0)
{"advertised": ["VERSION", "READER", "POST", "OVER", "HDR", "NEWNEWS", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "answered": {"READER": "211 6 1 6 fn.letters", "POST": "340 send article to be posted", "POST CLOSE": "441 posting failed; the article is not valid syntax", "IHAVE": "335 send it; end with <CR-LF>.<CR-LF>", "IHAVE CLOSE": "437 transfer rejected; not a valid article", "STREAMING": "203 streaming permitted", "OVER": "412 no newsgroup selected", "HDR": "412 no newsgroup selected", "LIST": "215 list of active newsgroups follows", "NEWNEWS": "230 list of new articles by message-id follows", "AUTHINFO": "381 password required", "STARTTLS": "580 can not initiate TLS negotiation", "MODE-READER": "200 posting allowed", "XOVER": "412 no newsgroup selected", "XHDR": "412 no newsgroup selected", "XPAT": "412 no newsgroup selected", "LISTGROUP": "211 6 1 6 fn.letters list follows", "CHECK": "238 <pin.check@matrix.example.invalid>", "TAKETHIS": "439 <pin.take@matrix.example.invalid>"}, "dispatched": ["READER", "POST", "IHAVE", "STREAMING", "OVER", "HDR", "LIST", "NEWNEWS", "AUTHINFO", "STARTTLS", "MODE-READER", "XOVER", "XHDR", "XPAT", "LISTGROUP", "CHECK", "TAKETHIS"], "login": {}, "advertised_not_dispatched": [], "dispatched_not_advertised": [], "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "ok": true}
--- 136 node A server is alive (rc=0)
ALIVE
--- 137 node B server is alive (rc=0)
ALIVE
--- 138 a second reader across node A's POST (rc=0)
{"WATCHER BEFORE": "211 6 1 6 fn.letters", "POST": "340 send article to be posted", "WATCHER MID": "211 6 1 6 fn.letters", "WATCHER ARTICLE MID": "223 1 <native-matrix-e5b62b396a22-a@example.invalid> retrieved", "COMMIT": "240 article received OK", "WATCHER AFTER": "211 6 1 6 fn.letters", "ok": true}
--- 139 node A server is alive (rc=0)
ALIVE
--- 140 node B server is alive (rc=0)
ALIVE
--- 141 live reconfiguration: declare fn.matrix.live on node A (rc=3)
uncertain operator group
--- 142 node A serves fn.matrix.live without a restart (rc=1)
{"ok": false, "port": 11190, "error": "ConnectionRefusedError: [Errno 111] Connection refused"}
--- 143 node A configured store (rc=0)
/home/hbox/fn-native-matrix/a/store
--- 144 offline configuration over node A's store (rc=0)
--- 145 offline group create while the owner holds the store (rc=0)
configured generation=7 record=00000007.cfg verification=VERIFIED
accepted operator group
--- 146 native public peering/restart witness (rc=0)
NATIVE-PEERING-EXPECTED-RUNTIME b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5
NATIVE-PEERING-EXPECTED-CORE 6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf
test_public_native_nodes_exchange_both_ways_and_suppress_duplicate (tests.test_native_peering.NativePeeringTests.test_public_native_nodes_exchange_both_ways_and_suppress_duplicate) ... ok
test_durable_feed_requeues_after_source_process_death (tests.test_native_peering.NativePeeringTests.test_durable_feed_requeues_after_source_process_death) ... ok

----------------------------------------------------------------------
Ran 2 tests in 3.318s

native-peering launcher-sha256=21ba38c1a66d96c32c8e50269b852cabd07ae15548306781aafa084cb0e6af32 core-sha256=6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf declared-source=source-commit=dabebb845adc3e3d6e8dc93c620782f54e6b106a source-manifest-sha256=56f7e3d013e457633ea0b0fa86bf06ed6fa69179ed4408f2385aeb340c57ba12
NATIVE-PEERING-WITNESS {"feed": {"ab": {"duplicate": "435", "identical": true}, "ba": {"duplicate": "435", "identical": true}}, "identity": {"a": {"core": "/tank/fn/gates/freeze-dev-28fb4bd0/build/fn-host.core", "core_sha256": "6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf", "runtime": "/tank/fn/sbcl/bin/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}, "b": {"core": "/tank/fn/gates/freeze-dev-28fb4bd0/build/fn-host.core", "core_sha256": "6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf", "runtime": "/tank/fn/sbcl/bin/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}}, "kind": "transit-and-feed", "transit": {"ab": {"duplicate": "435", "identical": true, "offer": "335", "transfer": "235"}, "ba": {"duplicate": "435", "identical": true, "offer": "335", "transfer": "235"}}}
NATIVE-PEERING-WITNESS {"duplicate": "435", "identity": {"restart-a": {"core": "/tank/fn/gates/freeze-dev-28fb4bd0/build/fn-host.core", "core_sha256": "6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf", "runtime": "/tank/fn/sbcl/bin/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}, "restart-b": {"core": "/tank/fn/gates/freeze-dev-28fb4bd0/build/fn-host.core", "core_sha256": "6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf", "runtime": "/tank/fn/sbcl/bin/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}}, "journal": true, "kind": "requeue-restart", "source_killed": true, "source_restarted": true, "target_identical": true}
OK
--- 147 native protected peering witness (rc=1)
NATIVE-PROTECTED-EXPECTED-RUNTIME b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5
NATIVE-PROTECTED-EXPECTED-CORE 6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf
test_reciprocal_starttls_authinfo_transfer_and_reconnect (tests.test_native_protected_peering.NativeProtectedPeeringTests.test_reciprocal_starttls_authinfo_transfer_and_reconnect) ... FAIL
test_bad_outbound_password_yields_authenticated_430_observation (tests.test_native_protected_peering.NativeProtectedPeeringTests.test_bad_outbound_password_yields_authenticated_430_observation) ... native-protected-peering launcher-sha256=21ba38c1a66d96c32c8e50269b852cabd07ae15548306781aafa084cb0e6af32 core-sha256=6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf source=source-commit=dabebb845adc3e3d6e8dc93c620782f54e6b106a source-manifest-sha256=56f7e3d013e457633ea0b0fa86bf06ed6fa69179ed4408f2385aeb340c57ba12
NATIVE-PROTECTED-WITNESS {"case": "wrong-password", "delivered": false, "identity": {"a": {"core": "/tank/fn/gates/freeze-dev-28fb4bd0/build/fn-host.core", "core_sha256": "6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf", "runtime": "/tank/fn/sbcl/bin/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}, "b": {"core": "/tank/fn/gates/freeze-dev-28fb4bd0/build/fn-host.core", "core_sha256": "6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf", "runtime": "/tank/fn/sbcl/bin/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}}, "kind": "protected-refusal", "source_alive": true, "target_alive": true}
ok
test_untrusted_certificate_yields_430_and_feed_journal_evidence (tests.test_native_protected_peering.NativeProtectedPeeringTests.test_untrusted_certificate_yields_430_and_feed_journal_evidence) ... NATIVE-PROTECTED-WITNESS {"case": "wrong-anchor", "delivered": false, "identity": {"a": {"core": "/tank/fn/gates/freeze-dev-28fb4bd0/build/fn-host.core", "core_sha256": "6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf", "runtime": "/tank/fn/sbcl/bin/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}, "b": {"core": "/tank/fn/gates/freeze-dev-28fb4bd0/build/fn-host.core", "core_sha256": "6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf", "runtime": "/tank/fn/sbcl/bin/sbcl", "runtime_sha256": "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5", "status": "observed"}}, "journal": true, "kind": "protected-refusal", "source_alive": true, "target_alive": true}
ok

======================================================================
FAIL: test_reciprocal_starttls_authinfo_transfer_and_reconnect (tests.test_native_protected_peering.NativeProtectedPeeringTests.test_reciprocal_starttls_authinfo_transfer_and_reconnect)
----------------------------------------------------------------------
--- 148 stop server node A (main) (rc=0)
stopped
--- 149 node A store after the stop (rc=0)
transactions=7 articles=7 staging-orphans=0 unsigned-legacy-experiment
accepted operator STATUS
--- 150 node A recover after the stop (rc=0)
recovered transactions=7 articles=7 staging-orphans=0 anchor=none checkpoint=none
accepted operator RECOVER
--- 151 node A log tail (rc=0)
CONTROL /home/hbox/fn-native-matrix/a/control.sock
LISTENING 11190
fault operator run
--- 152 stop server node B (main) (rc=0)
stopped
--- 153 node B store after the stop (rc=0)
transactions=6 articles=6 staging-orphans=0 unsigned-legacy-experiment
accepted operator STATUS
--- 154 node B recover after the stop (rc=0)
recovered transactions=6 articles=6 staging-orphans=0 anchor=none checkpoint=none
accepted operator RECOVER
--- 155 node B log tail (rc=0)
CONTROL /home/hbox/fn-native-matrix/b/control.sock
LISTENING 11191
accepted operator run
--- 156 peer remove a peer that is not there (rc=1)
refused operator peer administrative configuration refused: NO-SUCH-PEER
--- 157 peer remove the configured peer (rc=0)
configured generation=8 record=00000008.cfg verification=VERIFIED
accepted operator peer
--- 158 stop server node A (main) (rc=0)
stopped
--- 159 stop the tap in front of node A (rc=0)
stopped
--- 160 stop server node B (main) (rc=0)
stopped
--- 161 stop the tap in front of node B (rc=0)
stopped
--- 162 stray fn processes (rc=0)
CLEAN
--- 163 remove the deploy tree (rc=0)
--- 164 release deploy lock (rc=0)
```
