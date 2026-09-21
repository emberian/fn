# v0 matrix: cdbd6b2 on hbox

v0 is every feature of fn usable between two peered fn nodes. This is that
question asked feature by feature against one commit on one box, with five
verdicts and no pass/fail collapse: accepted, refused and uncertain are the
three outcomes and each is a real observation; not-exercised names what
blocked the row; not-built names the lane that owns the missing feature.
It establishes nothing about the books beyond which certificates ACL2 read.

## What ran

| fact | value |
| --- | --- |
| commit | `cdbd6b2` (cdbd6b285542110616dc96bfd3d037d410dfc20a) |
| tree | `w12-integrated-cdb` |
| host | `hbox` |
| started | 2026-09-21T06:49:56Z |
| wall time | 1137.5 s |
| gate tool | `tools/v0_matrix.py` |
| os | Ubuntu 24.10 kernel=Linux 6.11.0-29-generic arch=x86_64 cores=24 |
| python3 | Python 3.12.7 |
| acl2version | + ACL2 Version 8.7                                                     + |
| certificates | cache acquisition rc=1; bounded certification rc=0; load rc=0: profile=default image=build/fn-host roots=24 result=loaded |
| feature probe | cert-checkpoint=no cert-nntp-auth-invariants=no feed-tool=no nntplib=python3.12 reader-post=no slrn=no |
| assigned ports | a=45143 b=33765 |
| node a | fn on port 45143 (main), store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store |
| node b | fn on port 33765 (after-recovery), store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store |
| server entry point | fn |
| peer records | store-peer |
| three outcomes a | accepted=0 refused=1 uncertain=3 (expected (0, 1, 3)) |
| three outcomes b | accepted=0 refused=1 uncertain=3 (expected (0, 1, 3)) |
| transit | IHAVE -> '335 send it; end with <CR-LF>.<CR-LF>'; CAPABILITIES lists IHAVE: True |
| kill | mode=transit ConnectionResetError: [Errno 104] Connection reset by peer |
| tcpcl | passed=none failed=none |
| rows | 192 rows: 149 accepted, 32 refused, 2 uncertain, 8 not exercised, 1 not built, 3 disagreed |
| alt | python3.12 Python 3.12.7 |
| native artifact profile | default |
| node A path-identity | a.gate.example.invalid |
| node B path-identity | b.gate.example.invalid |
| owner feed | A->B True ; B->A True |
| owner feed <fed-ab@example.invalid> | status=220 0 <fed-ab@example.invalid> article follows attempts=1 octets identical to the source=True |
| owner feed <fed-ba@example.invalid> | status=220 0 <fed-ba@example.invalid> article follows attempts=1 octets identical to the source=True |
| owner feed ab duplicate | ihave=435 duplicate check=438 <fed-ab@example.invalid> takethis=439 <fed-ab@example.invalid> |
| owner feed ba duplicate | ihave=435 duplicate check=438 <fed-ba@example.invalid> takethis=439 <fed-ba@example.invalid> |
| owner feed wire | nothing recorded |
| server | node B (fn) on port 33765 (b-after-recovery) |
| host clients | expect=ABSENT, inews=ABSENT, nn=ABSENT, script=/usr/bin/script, slrn=ABSENT, tin=ABSENT, trn=ABSENT |

## The v0 matrix

192 rows: 149 accepted, 32 refused, 2 uncertain, 8 not exercised, 1 not built; 3 row(s) did not do what they were designed to do. Every count here is `tools/v0_matrix.py`'s over the rows below, and `planning/evidence/v0-runs/20260921T064956.625126Z-cdbd6b2-11d907e01b5e/matrix.json` carries the same rows with their digest.


**Who saw it.** 2 of the 183 outcome rows were observed by something that is not fn's own code; 181 were observed by fn talking to fn. A feature that only fn's own client has ever seen is a weaker claim than "usable between two peered servers" reads, and every row carries the client that saw it in its `client` field. Clients in this run: an fn harness (tcpcl_lab, campaign, scale_gate) (6); fn CLI (exit code) (40); stdlib nntplib on python3.12 (2); the matrix's raw-socket driver (135).

| feature | accepted | refused | uncertain | not exercised | not built | disagreed |
| --- | --- | --- | --- | --- | --- | --- |
| node init, configuration, start and stop (F-NODE) | 14 | 1 | 0 | 0 | 0 | 0 |
| the three outcomes on the operator surface (F-OUT) | 4 | 2 | 2 | 0 | 0 | 0 |
| groups, capacity, peers and live reconfiguration (F-GROUP) | 14 | 6 | 0 | 0 | 0 | 0 |
| principals, AUTHINFO and posting permission (F-AUTH) | 15 | 2 | 0 | 0 | 0 | 2 |
| POST and its read-back (F-POST) | 11 | 2 | 0 | 0 | 0 | 0 |
| the reader profile on each node (F-READ) | 50 | 4 | 0 | 0 | 0 | 0 |
| capability truthfulness (F-PIN) | 4 | 0 | 0 | 0 | 0 | 0 |
| transit inbound, A to B and B to A (F-TRANSIT) | 16 | 10 | 0 | 0 | 0 | 0 |
| the owner-driven outbound feed (F-FEED) | 4 | 0 | 0 | 0 | 0 | 0 |
| checkpoint, recovery and the process-death cut table (F-CRASH) | 7 | 2 | 0 | 0 | 0 | 0 |
| BP over TCPCLv4 between the two nodes (F-BP) | 4 | 2 | 0 | 2 | 0 | 1 |
| statement sign and verify across the pair (F-STX) | 4 | 1 | 0 | 0 | 1 | 0 |
| the carried-media letter (F-MEDIA) | 0 | 0 | 0 | 3 | 0 | 0 |
| scale (F-SCALE) | 0 | 0 | 0 | 1 | 0 | 0 |
| INN as a third node (F-INN) | 0 | 0 | 0 | 1 | 0 | 0 |
| independent newsreader clients (F-CLIENT) | 2 | 0 | 0 | 1 | 0 | 0 |

### Every row

| row | title | verdict | expected | agrees | independent | observed |
| --- | --- | --- | --- | --- | --- | --- |
| `V0-NODE-INIT-A` | fn init creates the store and writes fn.toml | **accepted** | accepted | yes | fn only | rc=0 initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store |
| `V0-NODE-INIT-B` | fn init creates the store and writes fn.toml | **accepted** | accepted | yes | fn only | rc=0 initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store |
| `V0-NODE-CONFIG-A` | fn.toml carries [store] path and [acl2] path | **accepted** | accepted | yes | fn only | [store]=True [acl2]=True [listener]=True |
| `V0-NODE-CONFIG-B` | fn.toml carries [store] path and [acl2] path | **accepted** | accepted | yes | fn only | [store]=True [acl2]=True [listener]=True |
| `V0-NODE-REINIT-A` | what a second fn init over a store that already holds articles does | **accepted** | - | - | fn only | rc=0 initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store |
| `V0-NODE-REINIT-B` | what a second fn init over a store that already holds articles does | **accepted** | - | - | fn only | rc=0 initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store |
| `V0-NODE-REINIT-SAFE-A` | the articles the store already held are still there after the second init | **accepted** | accepted | yes | fn only | every one of the 3 articles the store held before the second init was still there |
| `V0-NODE-REINIT-SAFE-B` | the articles the store already held are still there after the second init | **accepted** | accepted | yes | fn only | every one of the 3 articles the store held before the second init was still there |
| `V0-NODE-STATUS-A` | fn status reports generation and article count | **accepted** | accepted | yes | fn only | rc=0 owner=absent generation=1 transactions=0 articles=0 staging-orphans=0 anchor=none |
| `V0-NODE-STATUS-B` | fn status reports generation and article count | **accepted** | accepted | yes | fn only | rc=0 owner=absent generation=1 transactions=0 articles=0 staging-orphans=0 anchor=none |
| `V0-NODE-START-A` | the service starts and reaches LISTENING | **accepted** | accepted | yes | fn only | `fn` reached LISTENING |
| `V0-NODE-START-B` | the service starts and reaches LISTENING | **accepted** | accepted | yes | fn only | `fn` reached LISTENING |
| `V0-NODE-STOP-A` | the service stops and releases the store | **accepted** | accepted | yes | fn only | stop rc=0; reopening the store afterwards rc=0 |
| `V0-NODE-STOP-B` | the service stops and releases the store | **accepted** | accepted | yes | fn only | stop rc=0; reopening the store afterwards rc=0 |
| `V0-NODE-LOOPBACK` | a non-loopback listener host is refused rather than silently bound | **refused** | refused | yes | fn only | rc=1 refused run listener host '10.99.0.1' is not loopback; the owner binds 127.0.0.1 only (docs/architecture.md) |
| `V0-OUT-ACCEPTED-A` | an accepted post exits 0 | **accepted** | accepted | yes | fn only | rc=0 committed sequence=0 charge=2 |
| `V0-OUT-ACCEPTED-B` | an accepted post exits 0 | **accepted** | accepted | yes | fn only | rc=0 committed sequence=0 charge=2 |
| `V0-OUT-REFUSED-A` | a lookup of an article the node does not hold exits 1 | **refused** | refused | yes | fn only | rc=1 (no output) |
| `V0-OUT-REFUSED-B` | a lookup of an article the node does not hold exits 1 | **refused** | refused | yes | fn only | rc=1 (no output) |
| `V0-OUT-UNCERTAIN-A` | a post interrupted after publication exits 3 and fences the store | **uncertain** | uncertain | yes | fn only | rc=3 store: indeterminate injected failure after final publication |
| `V0-OUT-UNCERTAIN-B` | a post interrupted after publication exits 3 and fences the store | **uncertain** | uncertain | yes | fn only | rc=3 store: indeterminate injected failure after final publication |
| `V0-OUT-RECOVER-A` | recover after the uncertain publication exits 0 | **accepted** | accepted | yes | fn only | rc=0 recovered transactions=2 articles=2 staging-orphans=0 anchor=none checkpoint=none |
| `V0-OUT-RECOVER-B` | recover after the uncertain publication exits 0 | **accepted** | accepted | yes | fn only | rc=0 recovered transactions=2 articles=2 staging-orphans=0 anchor=none checkpoint=none |
| `V0-GROUP-CREATE-A` | fn group create adds a served group | **accepted** | accepted | yes | fn only | rc=0 group created name=fn.matrix generation=2 |
| `V0-GROUP-CREATE-B` | fn group create adds a served group | **accepted** | accepted | yes | fn only | rc=0 group created name=fn.matrix generation=2 |
| `V0-GROUP-SERVED-A` | the new group is served over the socket | **accepted** | accepted | yes | fn only | 211 0 1 0 fn.matrix |
| `V0-GROUP-SERVED-B` | the new group is served over the socket | **accepted** | accepted | yes | fn only | 211 0 1 0 fn.matrix |
| `V0-GROUP-RETIRE-A` | fn group retire removes it again | **accepted** | accepted | yes | fn only | rc=0 group retired name=fn.matrix.throwaway generation=4 |
| `V0-GROUP-RETIRE-B` | fn group retire removes it again | **accepted** | accepted | yes | fn only | rc=0 group retired name=fn.matrix.throwaway generation=4 |
| `V0-GROUP-UNKNOWN-A` | retiring a group the node does not serve is refused | **refused** | refused | yes | fn only | rc=1 refused group retire fn.not.served store: refused group retire: no-such-group |
| `V0-GROUP-UNKNOWN-B` | retiring a group the node does not serve is refused | **refused** | refused | yes | fn only | rc=1 refused group retire fn.not.served store: refused group retire: no-such-group |
| `V0-CAP-SET-A` | fn capacity sets the retention capacity | **accepted** | accepted | yes | fn only | rc=0 capacity set n=64 generation=2 |
| `V0-CAP-SET-B` | fn capacity sets the retention capacity | **accepted** | accepted | yes | fn only | rc=0 capacity set n=64 generation=2 |
| `V0-CAP-REFUSE-A` | an article that does not fit the capacity is refused before it is written | **refused** | refused | yes | fn only | rc=1 store: ACL2 refused post: refused |
| `V0-CAP-REFUSE-B` | an article that does not fit the capacity is refused before it is written | **refused** | refused | yes | fn only | rc=1 store: ACL2 refused post: refused |
| `V0-PEER-ADD-A` | fn peer add writes a transit peer record | **accepted** | accepted | yes | fn only | rc=0 peer added name=b generation=6 |
| `V0-PEER-ADD-B` | fn peer add writes a transit peer record | **accepted** | accepted | yes | fn only | rc=0 peer added name=a generation=6 |
| `V0-PEER-LIST-A` | fn peer list reads the record back | **accepted** | accepted | yes | fn only | rc=0 lists b: True |
| `V0-PEER-LIST-B` | fn peer list reads the record back | **accepted** | accepted | yes | fn only | rc=0 lists a: True |
| `V0-PEER-ABSENT` | fn peer remove of a peer that is not there is refused | **refused** | refused | yes | fn only | rc=1 store: refused peer remove: no-such-peer |
| `V0-PEER-REMOVE` | fn peer remove of a configured peer is accepted | **accepted** | accepted | yes | fn only | rc=0 peer removed name=b generation=7 |
| `V0-CFG-LIVE` | a group declared on the running service's control channel reaches the served configuration | **accepted** | accepted | yes | fn only | declared |
| `V0-CFG-LIVE-REFUSE` | an offline configuration command is refused while the service holds the store | **refused** | refused | yes | fn only | rc=1 refused group create fn.matrix.offline an owner is live on /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/control.sock; a configuration record needs the writer lock, so stop the service first |
| `V0-AUTH-NEW` | fn principal new derives a principal id from a seed | **accepted** | accepted | yes | fn only | rc=0 id 86c30609295a4cc0198f20cb5399865eaab7cbd863bdf41714e205f2c8019a24 |
| `V0-AUTH-PASSWORD-A` | fn principal set-password records an AUTHINFO credential | **accepted** | accepted | yes | fn only | rc=0 accepted wrote /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store/auth.toml (mode 0600) with login 'matrix', principal 86c30609295a4cc0..., posting allowed.  The stored value is a salted dig |
| `V0-AUTH-PASSWORD-B` | fn principal set-password records an AUTHINFO credential | **accepted** | accepted | yes | fn only | rc=0 accepted wrote /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store/auth.toml (mode 0600) with login 'matrix', principal 86c30609295a4cc0..., posting allowed.  The stored value is a salted dig |
| `V0-AUTH-LIST-A` | fn principal list shows the credential | **accepted** | accepted | yes | fn only | rc=0 lists matrix: True |
| `V0-AUTH-LIST-B` | fn principal list shows the credential | **accepted** | accepted | yes | fn only | rc=0 lists matrix: True |
| `V0-AUTH-ADVERTISED-A` | AUTHINFO USER is advertised while the connection is unauthenticated | **accepted** | accepted | yes | fn only | CAPABILITIES before the login: VERSION, READER, POST, OVER, HDR, LIST, IMPLEMENTATION, IHAVE, STREAMING, AUTHINFO |
| `V0-AUTH-ADVERTISED-B` | AUTHINFO USER is advertised while the connection is unauthenticated | **accepted** | accepted | yes | fn only | CAPABILITIES before the login: VERSION, READER, POST, OVER, HDR, LIST, IMPLEMENTATION, IHAVE, STREAMING, AUTHINFO |
| `V0-AUTH-GATED-A` | POST before a login is refused, not performed | **accepted** | refused | NO | fn only | 340 send article to be posted |
| `V0-AUTH-GATED-B` | POST before a login is refused, not performed | **accepted** | refused | NO | fn only | 340 send article to be posted |
| `V0-AUTH-LOGIN-A` | AUTHINFO USER then PASS answers 281 | **accepted** | accepted | yes | fn only | 281 authentication accepted |
| `V0-AUTH-LOGIN-B` | AUTHINFO USER then PASS answers 281 | **accepted** | accepted | yes | fn only | 281 authentication accepted |
| `V0-AUTH-WITHDRAWN-A` | AUTHINFO is no longer advertised once the connection is authenticated | **accepted** | accepted | yes | fn only | CAPABILITIES after the login: VERSION, READER, POST, OVER, HDR, LIST, IMPLEMENTATION, IHAVE, STREAMING |
| `V0-AUTH-WITHDRAWN-B` | AUTHINFO is no longer advertised once the connection is authenticated | **accepted** | accepted | yes | fn only | CAPABILITIES after the login: VERSION, READER, POST, OVER, HDR, LIST, IMPLEMENTATION, IHAVE, STREAMING |
| `V0-AUTH-POST-A` | POST after the login is accepted | **accepted** | accepted | yes | fn only | 240 article received OK |
| `V0-AUTH-POST-B` | POST after the login is accepted | **accepted** | accepted | yes | fn only | 240 article received OK |
| `V0-AUTH-WRONG-A` | a wrong password answers 481 and grants nothing | **refused** | refused | yes | fn only | 481 authentication failed |
| `V0-AUTH-WRONG-B` | a wrong password answers 481 and grants nothing | **refused** | refused | yes | fn only | 481 authentication failed |
| `V0-POST-OPEN-A` | POST on the served socket answers 340 | **accepted** | accepted | yes | fn only | 340 send article to be posted |
| `V0-POST-OPEN-B` | POST on the served socket answers 340 | **accepted** | accepted | yes | fn only | 340 send article to be posted |
| `V0-POST-COMMIT-A` | the article is accepted with 240 | **accepted** | accepted | yes | fn only | 240 article received OK |
| `V0-POST-COMMIT-B` | the article is accepted with 240 | **accepted** | accepted | yes | fn only | 240 article received OK |
| `V0-POST-READBACK-A` | the posting connection's next GROUP already counts the article | **accepted** | accepted | yes | fn only | GROUP before=211 5 1 5 fn.letters after=211 6 1 6 fn.letters |
| `V0-POST-READBACK-B` | the posting connection's next GROUP already counts the article | **accepted** | accepted | yes | fn only | GROUP before=211 7 1 7 fn.letters after=211 8 1 8 fn.letters |
| `V0-POST-FRESH-A` | a fresh connection reads it back by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <socket-a@example.invalid> article follows |
| `V0-POST-FRESH-B` | a fresh connection reads it back by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <socket-b@example.invalid> article follows |
| `V0-POST-DUPLICATE-A` | a second POST of the same Message-ID is refused and allocates nothing | **refused** | refused | yes | fn only | 441 posting failed; the article was refused |
| `V0-POST-DUPLICATE-B` | a second POST of the same Message-ID is refused and allocates nothing | **refused** | refused | yes | fn only | 441 posting failed; the article was refused |
| `V0-POST-CLOCK-A` | a duplicate POST is refused as an article and does not cost the node its clock | **accepted** | accepted | yes | fn only | the duplicate answered '441 posting failed; the article was refused' and DATE afterwards answered '111 20260921065633' |
| `V0-POST-CLOCK-B` | a duplicate POST is refused as an article and does not cost the node its clock | **accepted** | accepted | yes | fn only | the duplicate answered '441 posting failed; the article was refused' and DATE afterwards answered '111 20260921065635' |
| `V0-POST-CONCURRENT` | a second reader stays live across another connection's whole POST | **accepted** | accepted | yes | fn only | watcher mid-post=211 10 1 10 fn.letters commit=240 article received OK |
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
| `V0-READ-GROUP-A` | GROUP | **accepted** | accepted | yes | fn only | 211 4 1 4 fn.letters |
| `V0-READ-GROUP-B` | GROUP | **accepted** | accepted | yes | fn only | 211 6 1 6 fn.letters |
| `V0-READ-LISTGROUP-A` | LISTGROUP with a range | **accepted** | accepted | yes | fn only | 211 4 1 4 fn.letters list follows |
| `V0-READ-LISTGROUP-B` | LISTGROUP with a range | **accepted** | accepted | yes | fn only | 211 6 1 6 fn.letters list follows |
| `V0-READ-ARTICLE-A` | ARTICLE by number | **accepted** | accepted | yes | fn only | 220 1 <alpha@a.example.invalid> article follows |
| `V0-READ-ARTICLE-B` | ARTICLE by number | **accepted** | accepted | yes | fn only | 220 1 <beta@b.example.invalid> article follows |
| `V0-READ-HEAD-A` | HEAD by number | **accepted** | accepted | yes | fn only | 221 1 <alpha@a.example.invalid> headers follow |
| `V0-READ-HEAD-B` | HEAD by number | **accepted** | accepted | yes | fn only | 221 1 <beta@b.example.invalid> headers follow |
| `V0-READ-BODY-A` | BODY by number | **accepted** | accepted | yes | fn only | 222 1 <alpha@a.example.invalid> body follows |
| `V0-READ-BODY-B` | BODY by number | **accepted** | accepted | yes | fn only | 222 1 <beta@b.example.invalid> body follows |
| `V0-READ-STAT-A` | STAT by number | **accepted** | accepted | yes | fn only | 223 1 <alpha@a.example.invalid> retrieved |
| `V0-READ-STAT-B` | STAT by number | **accepted** | accepted | yes | fn only | 223 1 <beta@b.example.invalid> retrieved |
| `V0-READ-ARTICLE-MSGID-A` | ARTICLE by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <alpha@a.example.invalid> article follows |
| `V0-READ-ARTICLE-MSGID-B` | ARTICLE by Message-ID | **accepted** | accepted | yes | fn only | 220 0 <beta@b.example.invalid> article follows |
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
| `V0-READ-NEXT-A` | NEXT moves the cursor | **accepted** | - | - | fn only | 223 2 <uncertain-a@example.invalid> retrieved |
| `V0-READ-NEXT-B` | NEXT moves the cursor | **accepted** | - | - | fn only | 223 2 <uncertain-b@example.invalid> retrieved |
| `V0-READ-LAST-A` | LAST moves the cursor back | **accepted** | - | - | fn only | 223 1 <alpha@a.example.invalid> retrieved |
| `V0-READ-LAST-B` | LAST moves the cursor back | **accepted** | - | - | fn only | 223 1 <beta@b.example.invalid> retrieved |
| `V0-READ-DATE-A` | DATE | **accepted** | accepted | yes | fn only | 111 20260921065631 |
| `V0-READ-DATE-B` | DATE | **accepted** | accepted | yes | fn only | 111 20260921065634 |
| `V0-READ-HELP-A` | HELP | **accepted** | accepted | yes | fn only | 100 help text follows |
| `V0-READ-HELP-B` | HELP | **accepted** | accepted | yes | fn only | 100 help text follows |
| `V0-READ-UNKNOWN-A` | an unknown command is refused with 500 | **refused** | refused | yes | fn only | 500 command not recognized |
| `V0-READ-UNKNOWN-B` | an unknown command is refused with 500 | **refused** | refused | yes | fn only | 500 command not recognized |
| `V0-READ-FRAMING-A` | a command split across two TCP segments is answered once, the same way | **accepted** | accepted | yes | fn only | DATE split across two segments answered '111 20260921065631' against '111 20260921065631' |
| `V0-READ-FRAMING-B` | a command split across two TCP segments is answered once, the same way | **accepted** | accepted | yes | fn only | DATE split across two segments answered '111 20260921065634' against '111 20260921065634' |
| `V0-PIN-DISPATCHED-A` | every capability the node advertises is dispatched by the node | **accepted** | accepted | yes | fn only | advertised=VERSION,READER,POST,OVER,HDR,LIST,IMPLEMENTATION,IHAVE,STREAMING not dispatched=(none) |
| `V0-PIN-DISPATCHED-B` | every capability the node advertises is dispatched by the node | **accepted** | accepted | yes | fn only | advertised=VERSION,READER,POST,OVER,HDR,LIST,IMPLEMENTATION,IHAVE,STREAMING not dispatched=(none) |
| `V0-PIN-ADVERTISED-A` | every command the node dispatches is advertised in CAPABILITIES | **accepted** | accepted | yes | fn only | dispatched=READER,POST,IHAVE,STREAMING,OVER,HDR,LIST,AUTHINFO,STARTTLS,MODE-READER,XOVER,XHDR,XPAT,LISTGROUP,CHECK not advertised=(none) |
| `V0-PIN-ADVERTISED-B` | every command the node dispatches is advertised in CAPABILITIES | **accepted** | accepted | yes | fn only | dispatched=READER,POST,IHAVE,STREAMING,OVER,HDR,LIST,AUTHINFO,STARTTLS,MODE-READER,XOVER,XHDR,XPAT,LISTGROUP,CHECK not advertised=(none) |
| `V0-TRANSIT-IDENTITY-A` | the node has an RFC 5537 <path-identity> of its own | **accepted** | accepted | yes | fn only | rc=0 policy set path-identity=a.gate.example.invalid generation=5 |
| `V0-TRANSIT-IDENTITY-B` | the node has an RFC 5537 <path-identity> of its own | **accepted** | accepted | yes | fn only | rc=0 policy set path-identity=b.gate.example.invalid generation=5 |
| `V0-TRANSIT-INDEPENDENT-A` | each node serves its own seeded articles and 43x for the other's seeds | **accepted** | accepted | yes | fn only | groups={'fn.letters': '211 8 1 8 fn.letters', 'fn.test': '211 0 1 0 fn.test'} present={'<alpha@a.example.invalid>': '220 0 <alpha@a.example.invalid> article follows', '<stream-a@example.invalid>': '22 |
| `V0-TRANSIT-INDEPENDENT-B` | each node serves its own seeded articles and 43x for the other's seeds | **accepted** | accepted | yes | fn only | groups={'fn.letters': '211 8 1 8 fn.letters', 'fn.test': '211 0 1 0 fn.test'} present={'<beta@b.example.invalid>': '220 0 <beta@b.example.invalid> article follows', '<stream-b@example.invalid>': '220  |
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
| `V0-FEED-QUEUE` | an article accepted on the source enters the matching peer's outbound queue | **accepted** | accepted | yes | fn only | 2 of 2 POSTs through the running server were accepted (240 article received OK ; 240 article received OK), so the feed had something durable to offer |
| `V0-FEED-OFFER` | the owner opens the session and offers it, with no hand-driven socket | **accepted** | accepted | yes | fn only | A->B True ; B->A True; owner feed <fed-ab@example.invalid>: status=220 0 <fed-ab@example.invalid> article follows attempts=1 octets identical to the source=True / owner feed <fed-ba@example.invalid>:  |
| `V0-FEED-ONCE` | an acknowledged transfer is not offered a second time | **accepted** | accepted | yes | fn only | ihave=435 duplicate check=438 <fed-ab@example.invalid> takethis=439 <fed-ab@example.invalid> / ihave=435 duplicate check=438 <fed-ba@example.invalid> takethis=439 <fed-ba@example.invalid> |
| `V0-FEED-JOURNAL` | the feed journal records the transfer and survives a restart | **accepted** | accepted | yes | fn only | total 4 |
| `V0-CRASH-CHECKPOINT` | a checkpoint is published and the store reopens from it | **accepted** | accepted | yes | fn only | anchor rc=0 (anchor accepted server=int08h midpoint_us=1789974525088003 radius_us=5000000 incarnation=0); reopen rc=0 |
| `V0-CRASH-KILL` | node B is SIGKILLed inside a transfer it had already agreed to take | **refused** | - | - | fn only | mode=transit after the kill: ConnectionResetError: [Errno 104] Connection reset by peer |
| `V0-CRASH-SURVIVOR` | node A is unaffected by node B's death | **accepted** | accepted | yes | fn only | ALIVE |
| `V0-CRASH-RECOVER` | node B recovers through the real recovery path | **accepted** | accepted | yes | fn only | rc=0 recovered transactions=13 articles=13 staging-orphans=0 anchor=none checkpoint=none |
| `V0-CRASH-ACKNOWLEDGED` | everything node B acknowledged is still there after the recovery | **accepted** | accepted | yes | fn only | all 9 acknowledged Message-IDs re-inspected: every one exited 0 |
| `V0-CRASH-INTERRUPTED` | the interrupted transfer is not there after the recovery | **refused** | refused | yes | fn only | rc=1 (no output) |
| `V0-CRASH-RESTART` | node B serves again after the recovery | **accepted** | accepted | yes | fn only | rc=0 {"groups": {"fn.letters": "211 13 1 13 fn.letters", "fn.test": "211 0 1 0 fn.test"}, "present": {"<beta@b.example.invalid>": "220 0 <beta@b.example.invalid> article follows", "<stream-b@example.i |
| `V0-CRASH-CUT-TABLE` | the declared cut table still matches the fault points in the host | **accepted** | accepted | yes | fn only | TABLE OK 54 |
| `V0-CRASH-CAMPAIGN` | the process-death campaign runs its cuts and each recovers to a state the model expresses | **accepted** | accepted | yes | fn only | sender-enqueue   workflow:postlink                     5.3s ok \| report: /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/campaign.json \| pairs=22 failures=0 seconds=179.8 |
| `V0-BP-IMAGE` | the native image carrying the convergence layer builds | **accepted** | accepted | yes | fn only | built build/fn-host (260M core) |
| `V0-BP-EXCHANGE` | one bundle each way inside one TCPCLv4 session | **accepted** | accepted | yes | fn only | a_holds_b_bundle=True, acks_from_a=2, acks_from_b=2, active_events=8, active_outcomes=[['accepted', 'xfer=0 path=/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/tcpcl-lab/exchange/active-spool/active- |
| `V0-BP-REFUSED` | a contact the layer refuses is refused | **refused** | refused | yes | fn only | outcomes=[['refused', 'outbound reason=exceeds-transfer-mtu']], segments=0, sender_rc=1, staged=[] |
| `V0-BP-KEEPALIVE` | the session keepalive holds an idle contact open | **accepted** | accepted | yes | fn only | active_keepalives=3, active_terms=0, passive_keepalives=3, passive_terms=0, still_up=True |
| `V0-BP-CRASH` | an interrupted contact loses and duplicates nothing | **refused** | accepted | NO | fn only | acks_before_kill=118, durable_after=True, durable_before=True, first_rc=0, interrupted_absent=False, no_partials=False, reconnect_rc=0, staged=['.incoming-1728016-dda1835cc3233affa2496ddb', 'passive-0 |
| `V0-BP-PROFILE` | the session profile is the one the layer declared | **accepted** | accepted | yes | fn only | large={'intact': True, 'rc': 0}, large_octets=262144, large_seconds=0.132, ratio=1.51, size_ratio=4, small={'intact': True, 'rc': 0}, small_octets=65536, small_seconds=0.088 |
| `V0-BP-REPLAY` | the transfer replays from the session log | **not-exercised** | accepted | - | - | (no row) |
| `V0-BP-NODE` | a BP node behind the layer carries an fn article between the two nodes | **not-exercised** | accepted | - | - | books/bp-node.lisp and tests/bp-dtn7/run_fn_bp_interop.py are both on this commit |
| `V0-STX-SIGN` | fn statement sign produces a canonical FN-Statement field | **accepted** | accepted | yes | fn only | rc=0 verified statement sign creator 86c30609295a4cc0198f20cb5399865eaab7cbd863bdf41714e205f2c8019a24 ed25519 signature over the ACL2 signing preimage: 52c34bd3a360e5abeab1a17ab8a0789ec34d478e5d0ed964 |
| `V0-STX-ATTACH` | the field is attached to an article as a header line | **accepted** | accepted | yes | fn only | rc=0 verified statement attach |
| `V0-STX-CROSS` | the statement-bearing article crosses to the other node unchanged | **accepted** | accepted | yes | fn only | 220 0 <statement-a@example.invalid> article follows |
| `V0-STX-VERIFY` | the receiving node computes its own verdict on it | **accepted** | accepted | yes | fn only | rc=0 (verified) verified 86c30609295a4cc0198f20cb5399865eaab7cbd863bdf41714e205f2c8019a24 keyring 0 |
| `V0-STX-UNVERIFIED` | a tampered statement is unverified, distinct from absent | **refused** | refused | yes | fn only | rc=3 unverified statement verify |
| `V0-STX-READER` | the reader exposes the statement octets and the recorded verdict | **not-built** | accepted | - | - | (not run) |
| `V0-MEDIA-EXPORT` | a carried volume is written from one node's store | **not-exercised** | accepted | - | - | usage: media export [-h] --media MEDIA --media-id MEDIA_ID [--bundle ID=PATH] |
| `V0-MEDIA-VERIFY` | the volume's copy check passes on its own | **not-exercised** | accepted | - | - | usage: media export [-h] --media MEDIA --media-id MEDIA_ID [--bundle ID=PATH] |
| `V0-MEDIA-IMPORT` | the other node imports it as a network receipt | **not-exercised** | accepted | - | - | usage: media export [-h] --media MEDIA --media-id MEDIA_ID [--bundle ID=PATH] |
| `V0-SCALE-CEILING` | the store size at which a post or a recover crosses its deadline | **not-exercised** | accepted | - | - | (not run: --scale was not given) |
| `V0-INN-INTEROP` | a real INN server exchanges with an fn node as a third peer | **not-exercised** | accepted | - | - | (not run: --inn was not given) |
| `V0-CLIENT-NNTPLIB-A` | an independent stdlib nntplib client reads a group and an article | **accepted** | accepted | yes | yes | nntplib 3.12.7 drove CAPABILITIES, AUTHINFO USER/PASS, GROUP, STAT, ARTICLE, HEAD, BODY, OVER, LIST, ARTICLE (absent), QUIT; login=accepted authinfo-advertised=True group={'count': 8, 'first': 1, 'las |
| `V0-CLIENT-NNTPLIB-B` | an independent stdlib nntplib client reads a group and an article | **accepted** | accepted | yes | yes | nntplib 3.12.7 drove CAPABILITIES, AUTHINFO USER/PASS, GROUP, STAT, ARTICLE, HEAD, BODY, OVER, LIST, ARTICLE (absent), QUIT; login=accepted authinfo-advertised=True group={'count': 8, 'first': 1, 'las |
| `V0-CLIENT-SLRN` | slrn reads a group and an article | **not-exercised** | accepted | - | - | (slrn is not installed) |

### What every row that is not an outcome is waiting for

- `V0-BP-REPLAY` (not-exercised): the lab produced no result for the `replay` scenario
- `V0-BP-NODE` (not-exercised): the BP node is BUILT -- `books/bp-node.lisp` encodes and decodes whole BPv7 bundles and `tests/bp-dtn7/run_fn_bp_interop.py` runs fn against dtn7-rs both ways -- but this matrix does not run it: it needs the pinned dtn7-rs build beside the native image, which is a second harness with its own box requirements. Run it and the row becomes an outcome -- owned by `w9/dtn-2`
- `V0-STX-READER` (not-built): the reader exposes no `:fn-verified` header on this commit: books/nntp-responses.lisp carries the seam and the board records it as deliberately not half-wired (SUB-006) -- owned by `w10/provenance`
- `V0-MEDIA-EXPORT` (not-exercised): `tools/media.py export` requires a `--bundle <id>=<path>` and a `--bp-bundle <id>=<path>` for every carried identity, because the importing node reads the identity and the expiry out of the BPv7 bundle octets rather than deciding them locally. No BPv7 bundle is produced anywhere in this run: the TCPCLv4 layer carries opaque octets and no BP node is wired behind it, so there is nothing to put in a volume -- owned by `w9/dtn-2`
- `V0-MEDIA-VERIFY` (not-exercised): `tools/media.py export` requires a `--bundle <id>=<path>` and a `--bp-bundle <id>=<path>` for every carried identity, because the importing node reads the identity and the expiry out of the BPv7 bundle octets rather than deciding them locally. No BPv7 bundle is produced anywhere in this run: the TCPCLv4 layer carries opaque octets and no BP node is wired behind it, so there is nothing to put in a volume -- owned by `w9/dtn-2`
- `V0-MEDIA-IMPORT` (not-exercised): `tools/media.py export` requires a `--bundle <id>=<path>` and a `--bp-bundle <id>=<path>` for every carried identity, because the importing node reads the identity and the expiry out of the BPv7 bundle octets rather than deciding them locally. No BPv7 bundle is produced anywhere in this run: the TCPCLv4 layer carries opaque octets and no BP node is wired behind it, so there is nothing to put in a volume -- owned by `w9/dtn-2`
- `V0-SCALE-CEILING` (not-exercised): the scale gate grows a store by doubling and takes an hour or more; it is a separate harness and this run did not take that budget. Quote its numbers from planning/evidence/scale-0e9a421-2026-09-20.md WITH their scope (one box, that payload grid, those ceilings), never as a bound
- `V0-INN-INTEROP` (not-exercised): the INN install is a lab that lives on hbox at /tank/fn/inn/2.7.4 and is not shipped; this run is on hbox, which has no INN. The last recorded run is planning/evidence/inn-lab-f4e8272-2026-09-20.md
- `V0-CLIENT-SLRN` (not-exercised): slrn is not installed on hbox (nor on hbox, measured 2026-09-20); tests/interop_slrn.py has never run against an fn node

### What each row does not show

- `V0-NODE-INIT-A`: one store on one box; the configuration is this gate's, not an operator's
- `V0-NODE-INIT-B`: one store on one box; the configuration is this gate's, not an operator's
- `V0-NODE-CONFIG-A`: the file's sections are read as text; nothing here loads it the way a tool would
- `V0-NODE-CONFIG-B`: the file's sections are read as text; nothing here loads it the way a tool would
- `V0-NODE-REINIT-A`: nothing in docs/operator.md says whether a second `init` adopts the store or refuses, so this row records the outcome rather than asserting one; the property that matters is the next row; one existing store holding 3 article(s); no concurrent initializer
- `V0-NODE-REINIT-B`: nothing in docs/operator.md says whether a second `init` adopts the store or refuses, so this row records the outcome rather than asserting one; the property that matters is the next row; one existing store holding 3 article(s); no concurrent initializer
- `V0-NODE-REINIT-SAFE-A`: exact Message-ID lookups over what this run posted, not a comparison of the store's octets
- `V0-NODE-REINIT-SAFE-B`: exact Message-ID lookups over what this run posted, not a comparison of the store's octets
- `V0-NODE-STATUS-A`: the store is not held by a service at this point
- `V0-NODE-STATUS-B`: the store is not held by a service at this point
- `V0-NODE-START-A`: the entry point that started is `fn`; every served row for this node is about that process, not about the ones above it in the list, which was given --max-connections 64
- `V0-NODE-START-B`: the entry point that started is `fn`; every served row for this node is about that process, not about the ones above it in the list, which was given --max-connections 64
- `V0-NODE-STOP-A`: the store reopens, which is the writer lock being gone; no in-flight session was observed across the stop
- `V0-NODE-STOP-B`: the store reopens, which is the writer lock being gone; no in-flight session was observed across the stop
- `V0-NODE-LOOPBACK`: one non-loopback address; nothing here tests a bind that the kernel would refuse for a different reason
- `V0-OUT-ACCEPTED-A`: one article; the exit code is the observation, the durability claim is books/store-files-invariants'
- `V0-OUT-ACCEPTED-B`: one article; the exit code is the observation, the durability claim is books/store-files-invariants'
- `V0-OUT-UNCERTAIN-A`: an injected fault at one publication boundary; it is not a power loss and the article is asserted in neither direction afterwards
- `V0-OUT-UNCERTAIN-B`: an injected fault at one publication boundary; it is not a power loss and the article is asserted in neither direction afterwards
- `V0-GROUP-CREATE-A`: one group on a store no service holds
- `V0-GROUP-CREATE-B`: one group on a store no service holds
- `V0-GROUP-SERVED-A`: the group was created before the service started
- `V0-GROUP-SERVED-B`: the group was created before the service started
- `V0-CAP-SET-A`: a scratch store beside the served one, so a refusal here cannot change what the node serves
- `V0-CAP-SET-B`: a scratch store beside the served one, so a refusal here cannot change what the node serves
- `V0-CAP-REFUSE-A`: the capacity was set to 1 (rc=0) and the article's own charge is what has to exceed it; the charge is ACL2's, and a 4 KiB article charged 3 on this tree
- `V0-CAP-REFUSE-B`: the capacity was set to 1 (rc=0) and the article's own charge is what has to exceed it; the charge is ACL2's, and a 4 KiB article charged 3 on this tree
- `V0-PEER-ADD-A`: a peer record is configuration, not authorization: nothing on this tree authenticates the peer it names. `--inbound-max-octets 32768` is passed explicitly because the CLI default of 1048576 is refused
- `V0-PEER-ADD-B`: a peer record is configuration, not authorization: nothing on this tree authenticates the peer it names. `--inbound-max-octets 32768` is passed explicitly because the CLI default of 1048576 is refused
- `V0-PEER-LIST-A`: the name is read out of the listing's text
- `V0-PEER-LIST-B`: the name is read out of the listing's text
- `V0-PEER-REMOVE`: run after the servers stopped, so it says nothing about removing a peer from a live service
- `V0-CFG-LIVE`: one group declared on one live service; no concurrent reader was observed across the change
- `V0-CFG-LIVE-REFUSE`: the refusal is the store lock's; a different server that does not take the writer lock would not produce it
- `V0-AUTH-NEW`: one seed; the derivation is tools/stx.py's and ACL2's, not this gate's
- `V0-AUTH-PASSWORD-A`: what is stored is books/auth-secret.lisp's salted verifier, derived in an ACL2 session; this row is about the CLI writing it, not about the strength of the digest or the secret's protection on the wire
- `V0-AUTH-PASSWORD-B`: what is stored is books/auth-secret.lisp's salted verifier, derived in an ACL2 session; this row is about the CLI writing it, not about the strength of the digest or the secret's protection on the wire
- `V0-AUTH-LIST-A`: one registry: `set-password` writes and `list` reads the credential file ([auth] path, else <store>/auth.toml), which is the same file the running service loads. The listing prints the login, its principal and its posting flag and never the verifier
- `V0-AUTH-LIST-B`: one registry: `set-password` writes and `list` reads the credential file ([auth] path, else <store>/auth.toml), which is the same file the running service loads. The listing prints the login, its principal and its posting flag and never the verifier
- `V0-AUTH-GATED-A`: one gated command; RFC 4643 section 2.3 does not require the same code for every gated verb. The gate is the NODE POLICY (`fn init --auth-required`, [auth] required) and these two nodes do not set it: a node that serves readers unauthenticated and a transit peer on the same loopback address cannot, because fn-auth-restricted-keywordp gates the reader verbs and IHAVE alike. tests/test_auth.py ServedCredentialTests.test_post_is_gated_by_the_configured_policy is the same question asked of a node that does set it
- `V0-AUTH-GATED-B`: one gated command; RFC 4643 section 2.3 does not require the same code for every gated verb. The gate is the NODE POLICY (`fn init --auth-required`, [auth] required) and these two nodes do not set it: a node that serves readers unauthenticated and a transit peer on the same loopback address cannot, because fn-auth-restricted-keywordp gates the reader verbs and IHAVE alike. tests/test_auth.py ServedCredentialTests.test_post_is_gated_by_the_configured_policy is the same question asked of a node that does set it
- `V0-AUTH-LOGIN-A`: USER/PASS over an unprotected loopback connection
- `V0-AUTH-LOGIN-B`: USER/PASS over an unprotected loopback connection
- `V0-AUTH-WRONG-A`: one wrong password; no rate limit or lockout is tested
- `V0-AUTH-WRONG-B`: one wrong password; no rate limit or lockout is tested
- `V0-POST-COMMIT-A`: one article; the durability behind the 240 is the store's, asserted by the recovery rows below
- `V0-POST-COMMIT-B`: one article; the durability behind the 240 is the store's, asserted by the recovery rows below
- `V0-POST-DUPLICATE-A`: the duplicate is offered on a fresh connection because one clock observation is pinned per connection at accept
- `V0-POST-DUPLICATE-B`: the duplicate is offered on a fresh connection because one clock observation is pinned per connection at accept
- `V0-POST-CLOCK-A`: a 441 for an article the node already holds and a 441 for a clock the node no longer has are the same code; DATE is what separates them from outside, because a refused reading costs the owner its clock (D10-a) and DATE then answers 503. This row does not INDUCE a clock fault -- it checks that an ordinary duplicate did not cause one
- `V0-POST-CLOCK-B`: a 441 for an article the node already holds and a 441 for a clock the node no longer has are the same code; DATE is what separates them from outside, because a refused reading costs the owner its clock (D10-a) and DATE then answers 503. This row does not INDUCE a clock fault -- it checks that an ordinary duplicate did not cause one
- `V0-POST-CONCURRENT`: two connections on one box; this is not concurrent load
- `V0-READ-CAPABILITIES-A`: served by `fn` on port 45143
- `V0-READ-CAPABILITIES-B`: served by `fn` on port 33765
- `V0-READ-MODE-READER-A`: served by `fn` on port 45143
- `V0-READ-MODE-READER-B`: served by `fn` on port 33765
- `V0-READ-LIST-ACTIVE-A`: served by `fn` on port 45143
- `V0-READ-LIST-ACTIVE-B`: served by `fn` on port 33765
- `V0-READ-LIST-NEWSGROUPS-A`: served by `fn` on port 45143
- `V0-READ-LIST-NEWSGROUPS-B`: served by `fn` on port 33765
- `V0-READ-LIST-OVERVIEW-FMT-A`: served by `fn` on port 45143
- `V0-READ-LIST-OVERVIEW-FMT-B`: served by `fn` on port 33765
- `V0-READ-LIST-ACTIVE-TIMES-A`: served by `fn` on port 45143
- `V0-READ-LIST-ACTIVE-TIMES-B`: served by `fn` on port 33765
- `V0-READ-LIST-HEADERS-A`: served by `fn` on port 45143
- `V0-READ-LIST-HEADERS-B`: served by `fn` on port 33765
- `V0-READ-GROUP-A`: served by `fn` on port 45143
- `V0-READ-GROUP-B`: served by `fn` on port 33765
- `V0-READ-LISTGROUP-A`: served by `fn` on port 45143
- `V0-READ-LISTGROUP-B`: served by `fn` on port 33765
- `V0-READ-ARTICLE-A`: served by `fn` on port 45143
- `V0-READ-ARTICLE-B`: served by `fn` on port 33765
- `V0-READ-HEAD-A`: served by `fn` on port 45143
- `V0-READ-HEAD-B`: served by `fn` on port 33765
- `V0-READ-BODY-A`: served by `fn` on port 45143
- `V0-READ-BODY-B`: served by `fn` on port 33765
- `V0-READ-STAT-A`: served by `fn` on port 45143
- `V0-READ-STAT-B`: served by `fn` on port 33765
- `V0-READ-ARTICLE-MSGID-A`: served by `fn` on port 45143
- `V0-READ-ARTICLE-MSGID-B`: served by `fn` on port 33765
- `V0-READ-ARTICLE-ABSENT-A`: served by `fn` on port 45143
- `V0-READ-ARTICLE-ABSENT-B`: served by `fn` on port 33765
- `V0-READ-OVER-A`: served by `fn` on port 45143
- `V0-READ-OVER-B`: served by `fn` on port 33765
- `V0-READ-OVER-RANGE-A`: served by `fn` on port 45143
- `V0-READ-OVER-RANGE-B`: served by `fn` on port 33765
- `V0-READ-HDR-A`: served by `fn` on port 45143
- `V0-READ-HDR-B`: served by `fn` on port 33765
- `V0-READ-XOVER-A`: served by `fn` on port 45143
- `V0-READ-XOVER-B`: served by `fn` on port 33765
- `V0-READ-XHDR-A`: served by `fn` on port 45143
- `V0-READ-XHDR-B`: served by `fn` on port 33765
- `V0-READ-XPAT-A`: served by `fn` on port 45143
- `V0-READ-XPAT-B`: served by `fn` on port 33765
- `V0-READ-NEXT-A`: the expected outcome depends on how many articles the group holds; the row records the count it was run against; served by `fn` on port 45143; the group held 4 article(s) when this ran, and with one article 421/422 is the correct answer
- `V0-READ-NEXT-B`: the expected outcome depends on how many articles the group holds; the row records the count it was run against; served by `fn` on port 33765; the group held 6 article(s) when this ran, and with one article 421/422 is the correct answer
- `V0-READ-LAST-A`: the expected outcome depends on where the cursor was; served by `fn` on port 45143; the group held 4 article(s) when this ran, and with one article 421/422 is the correct answer
- `V0-READ-LAST-B`: the expected outcome depends on where the cursor was; served by `fn` on port 33765; the group held 6 article(s) when this ran, and with one article 421/422 is the correct answer
- `V0-READ-DATE-A`: served by `fn` on port 45143
- `V0-READ-DATE-B`: served by `fn` on port 33765
- `V0-READ-HELP-A`: served by `fn` on port 45143
- `V0-READ-HELP-B`: served by `fn` on port 33765
- `V0-READ-UNKNOWN-A`: served by `fn` on port 45143
- `V0-READ-UNKNOWN-B`: served by `fn` on port 33765
- `V0-READ-FRAMING-A`: one command split at one point; the chunk-independence keystone is books/wire-invariants', not this row
- `V0-READ-FRAMING-B`: one command split at one point; the chunk-independence keystone is books/wire-invariants', not this row
- `V0-PIN-DISPATCHED-A`: only the 9 labels with a probe command are checked; VERSION and IMPLEMENTATION have none
- `V0-PIN-DISPATCHED-B`: only the 9 labels with a probe command are checked; VERSION and IMPLEMENTATION have none
- `V0-PIN-ADVERTISED-A`: only the 9 labels with a probe command are checked; VERSION and IMPLEMENTATION have none; RFC 3977 section 5.2.2 requires the capability exactly when the command is available
- `V0-PIN-ADVERTISED-B`: only the 9 labels with a probe command are checked; VERSION and IMPLEMENTATION have none; RFC 3977 section 5.2.2 requires the capability exactly when the command is available
- `V0-TRANSIT-IDENTITY-A`: `fn-peer-local-identity` reads the `path-identity` policy slot and an unset slot is the empty string, which `fn-path-names-p` never matches: a node without this answers no loop, so V0-TRANSIT-LOOP rests on it; the loop rows below are unfounded without it
- `V0-TRANSIT-IDENTITY-B`: `fn-peer-local-identity` reads the `path-identity` policy slot and an unset slot is the empty string, which `fn-path-names-p` never matches: a node without this answers no loop, so V0-TRANSIT-LOOP rests on it; the loop rows below are unfounded without it
- `V0-TRANSIT-INDEPENDENT-A`: this is the control: every later claim that an article reached a node rests on it. The absent set is the other node's articles as of before either listener started; the outbound feed carries what a running server accepts and its crossings are measured by F-FEED, not here
- `V0-TRANSIT-INDEPENDENT-B`: this is the control: every later claim that an article reached a node rests on it. The absent set is the other node's articles as of before either listener started; the outbound feed carries what a running server accepts and its crossings are measured by F-FEED, not here
- `V0-TRANSIT-MODE-STREAM-AB`: node B is `fn`; the peer record on it names a
- `V0-TRANSIT-MODE-STREAM-BA`: node A is `fn`; the peer record on it names b
- `V0-TRANSIT-OFFER-AB`: node B is `fn`; the peer record on it names a
- `V0-TRANSIT-OFFER-BA`: node A is `fn`; the peer record on it names b
- `V0-TRANSIT-TRANSFER-AB`: node B is `fn`; the peer record on it names a
- `V0-TRANSIT-TRANSFER-BA`: node A is `fn`; the peer record on it names b
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
- `V0-FEED-QUEUE`: both nodes are on one host over loopback, and the offering side is the owner's feed table, not this harness's socket client
- `V0-FEED-OFFER`: both nodes are on one host over loopback, and the offering side is the owner's feed table, not this harness's socket client
- `V0-FEED-ONCE`: both nodes are on one host over loopback, and the offering side is the owner's feed table, not this harness's socket client; one re-offer per direction, which is the history answer that makes a restart-by-offer safe, not a proof of exactly-once
- `V0-FEED-JOURNAL`: the journal's presence on disk, not its contents: the FNFD record shapes are books/owner-feed's and the restart property (K5) is tools/twonode_gate.py's scenario_feed_restart, which this matrix does not run because it kills node A
- `V0-CRASH-CHECKPOINT`: a freshness anchor and a reopen; the checkpoint codec of books/checkpoint-codec is not certified on this commit, so this row is about the store reopening, not about a published checkpoint's equivalence
- `V0-CRASH-KILL`: what the client saw is recorded; an acknowledgement after the kill would be the defect, and its absence is the assertion; a SIGKILL is not a power loss, and this is one cut; the enumerated table is tests/campaign/cuts.py. An acknowledgement here would be the defect, so 'refused' is the wanted reading
- `V0-CRASH-SURVIVOR`: one process killed on one box; this is not a partition
- `V0-CRASH-RECOVER`: the real recovery path over the real store directory
- `V0-CRASH-ACKNOWLEDGED`: exact Message-ID lookups, not a full comparison of octets
- `V0-CRASH-CUT-TABLE`: the table is checked against the fault points the host declares, not against the crash model
- `V0-CRASH-CAMPAIGN`: --quick: a subset of the enumerated cuts, each a process death, none of them a power loss
- `V0-BP-IMAGE`: the DTN-only build list; the image is not the served path
- `V0-BP-EXCHANGE`: every assertion is over the event digests the two images printed; the lab does not speak TCPCL, and the octets it carries are opaque, not BPv7 bundles
- `V0-BP-REFUSED`: every assertion is over the event digests the two images printed; the lab does not speak TCPCL, and the octets it carries are opaque, not BPv7 bundles
- `V0-BP-KEEPALIVE`: every assertion is over the event digests the two images printed; the lab does not speak TCPCL, and the octets it carries are opaque, not BPv7 bundles
- `V0-BP-CRASH`: every assertion is over the event digests the two images printed; the lab does not speak TCPCL, and the octets it carries are opaque, not BPv7 bundles
- `V0-BP-PROFILE`: every assertion is over the event digests the two images printed; the lab does not speak TCPCL, and the octets it carries are opaque, not BPv7 bundles
- `V0-STX-SIGN`: the signing realiser on this tree is the toy one of tests/acl2/crypto-seam-tests.lisp, and `--ed25519` prints a real signature that is NOT attached (D09); this row is about the field's production, not about cryptography
- `V0-STX-ATTACH`: one field line prepended to one article
- `V0-STX-CROSS`: the article node A holds for this row was posted with its FN-Statement field already on it, so what crosses is the field; whether the far side's octets are identical is the transit row, not this one
- `V0-STX-VERIFY`: the octets verified are the signed file on the box, not what node B served: the transit row above says whether the article reached B at all. The keyring holds the creator and its public key; the realiser behind the signature is the toy one of tests/acl2/crypto-seam-tests.lisp, so a `verified` here is the node's own verdict function agreeing with its own signer, not a cryptographic claim
- `V0-STX-UNVERIFIED`: one tampered octet range; the row asserts that the verdict is a decision (unverified or absent) and not silence
- `V0-SCALE-CEILING`: a measured ceiling on one box with one payload grid; it is not a bound and not a proof
- `V0-CLIENT-NNTPLIB-A`: one client library, and it reads: nothing here is posted or fed by a foreign client. Its framing, folding and response parsing are the standard library's, not fn's, which is the point of the row
- `V0-CLIENT-NNTPLIB-B`: one client library, and it reads: nothing here is posted or fed by a foreign client. Its framing, folding and response parsing are the standard library's, not fn's, which is the point of the row

### The exact invocation of every row

- `V0-NODE-INIT-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml init --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store --group fn.letters --group fn.test --listen 127.0.0.1:45143 --control $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/control.sock --log $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.log --acl2 "$FN_...`
- `V0-NODE-INIT-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml init --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store --group fn.letters --group fn.test --listen 127.0.0.1:33765 --control $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/control.sock --log $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.log --acl2 "$FN_...`
- `V0-NODE-CONFIG-A`: `cat $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml`
- `V0-NODE-CONFIG-B`: `cat $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml`
- `V0-NODE-REINIT-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn2.toml init --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store --group fn.letters --group fn.test`
- `V0-NODE-REINIT-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn2.toml init --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store --group fn.letters --group fn.test`
- `V0-NODE-REINIT-SAFE-A`: `run_store.py --store <a> inspect --message-id <each of 3>`
- `V0-NODE-REINIT-SAFE-B`: `run_store.py --store <b> inspect --message-id <each of 3>`
- `V0-NODE-STATUS-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml status`
- `V0-NODE-STATUS-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml status`
- `V0-NODE-START-A`: `python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml run --control $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/control.sock --max-connections 64`
- `V0-NODE-START-B`: `python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml run --control $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/control.sock --max-connections 64`
- `V0-NODE-STOP-A`: `if [ -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/server.pid ; fi ; echo stopped`
- `V0-NODE-STOP-B`: `if [ -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/server.pid ; fi ; echo stopped`
- `V0-NODE-LOOPBACK`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; timeout 60 python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/loopback/fn.toml run --control $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/loopback/control.sock`
- `V0-OUT-ACCEPTED-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store post --message-id '<alpha@a.example.invalid>' --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/seed.article --group fn.letters`
- `V0-OUT-ACCEPTED-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store post --message-id '<beta@b.example.invalid>' --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/seed.article --group fn.letters`
- `V0-OUT-REFUSED-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store inspect --message-id '<absent@example.invalid>'`
- `V0-OUT-REFUSED-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store inspect --message-id '<absent@example.invalid>'`
- `V0-OUT-UNCERTAIN-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store post --message-id '<uncertain-a@example.invalid>' --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/seed.article --group fn.letters --inject-fault postpublish`
- `V0-OUT-UNCERTAIN-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store post --message-id '<uncertain-b@example.invalid>' --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/seed.article --group fn.letters --inject-fault postpublish`
- `V0-OUT-RECOVER-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store recover`
- `V0-OUT-RECOVER-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store recover`
- `V0-GROUP-CREATE-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml group create fn.matrix`
- `V0-GROUP-CREATE-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml group create fn.matrix`
- `V0-GROUP-SERVED-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py presence --port 45143 --groups fn.matrix`
- `V0-GROUP-SERVED-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py presence --port 33765 --groups fn.matrix`
- `V0-GROUP-RETIRE-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml group retire fn.matrix.throwaway`
- `V0-GROUP-RETIRE-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml group retire fn.matrix.throwaway`
- `V0-GROUP-UNKNOWN-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml group retire fn.not.served`
- `V0-GROUP-UNKNOWN-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml group retire fn.not.served`
- `V0-CAP-SET-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/capacity-store capacity 64`
- `V0-CAP-SET-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/capacity-store capacity 64`
- `V0-CAP-REFUSE-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/capacity-store post --message-id '<capacity-a@example.invalid>' --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/capacity.article --group fn.letters`
- `V0-CAP-REFUSE-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/capacity-store post --message-id '<capacity-b@example.invalid>' --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/capacity.article --group fn.letters`
- `V0-PEER-ADD-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store peer add b --path-identity b.gate.example.invalid --nntp 127.0.0.1:33765 --inbound-groups 'fn.*' --inbound-max-octets 32768 --outbound-groups 'fn.*' --streaming --source-address 127.0.0.1`
- `V0-PEER-ADD-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store peer add a --path-identity a.gate.example.invalid --nntp 127.0.0.1:45143 --inbound-groups 'fn.*' --inbound-max-octets 32768 --outbound-groups 'fn.*' --streaming --source-address 127.0.0.1`
- `V0-PEER-LIST-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store peer list`
- `V0-PEER-LIST-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store peer list`
- `V0-PEER-ABSENT`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store peer remove no-such-peer`
- `V0-PEER-REMOVE`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store peer remove b`
- `V0-CFG-LIVE`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py control --socket $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/control.sock --line 'DECLARE-GROUP fn.matrix.live'`
- `V0-CFG-LIVE-REFUSE`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml group create fn.matrix.offline`
- `V0-AUTH-NEW`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml principal new --seed $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/seed.hex`
- `V0-AUTH-PASSWORD-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml principal set-password matrix --password matrix-secret-8f21 --principal 86c30609295a4cc0198f20cb5399865eaab7cbd863bdf41714e205f2c8019a24`
- `V0-AUTH-PASSWORD-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml principal set-password matrix --password matrix-secret-8f21 --principal 86c30609295a4cc0198f20cb5399865eaab7cbd863bdf41714e205f2c8019a24`
- `V0-AUTH-LIST-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml principal list`
- `V0-AUTH-LIST-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml principal list`
- `V0-AUTH-ADVERTISED-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py auth --port 45143 --group fn.letters --user matrix --secret matrix-secret-8f21 --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-ADVERTISED-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py auth --port 33765 --group fn.letters --user matrix --secret matrix-secret-8f21 --msgid '<auth-b@example.invalid>'`
- `V0-AUTH-GATED-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py auth --port 45143 --group fn.letters --user matrix --secret matrix-secret-8f21 --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-GATED-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py auth --port 33765 --group fn.letters --user matrix --secret matrix-secret-8f21 --msgid '<auth-b@example.invalid>'`
- `V0-AUTH-LOGIN-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py auth --port 45143 --group fn.letters --user matrix --secret matrix-secret-8f21 --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-LOGIN-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py auth --port 33765 --group fn.letters --user matrix --secret matrix-secret-8f21 --msgid '<auth-b@example.invalid>'`
- `V0-AUTH-WITHDRAWN-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py auth --port 45143 --group fn.letters --user matrix --secret matrix-secret-8f21 --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-WITHDRAWN-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py auth --port 33765 --group fn.letters --user matrix --secret matrix-secret-8f21 --msgid '<auth-b@example.invalid>'`
- `V0-AUTH-POST-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py auth --port 45143 --group fn.letters --user matrix --secret matrix-secret-8f21 --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-POST-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py auth --port 33765 --group fn.letters --user matrix --secret matrix-secret-8f21 --msgid '<auth-b@example.invalid>'`
- `V0-AUTH-WRONG-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py auth --port 45143 --group fn.letters --user matrix --secret matrix-secret-8f21 --msgid '<auth-a@example.invalid>'`
- `V0-AUTH-WRONG-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py auth --port 33765 --group fn.letters --user matrix --secret matrix-secret-8f21 --msgid '<auth-b@example.invalid>'`
- `V0-POST-OPEN-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py postcycle --port 45143 --group fn.letters --msgid '<socket-a@example.invalid>' --user matrix --secret matrix-secret-8f21`
- `V0-POST-OPEN-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py postcycle --port 33765 --group fn.letters --msgid '<socket-b@example.invalid>' --user matrix --secret matrix-secret-8f21`
- `V0-POST-COMMIT-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py postcycle --port 45143 --group fn.letters --msgid '<socket-a@example.invalid>' --user matrix --secret matrix-secret-8f21`
- `V0-POST-COMMIT-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py postcycle --port 33765 --group fn.letters --msgid '<socket-b@example.invalid>' --user matrix --secret matrix-secret-8f21`
- `V0-POST-READBACK-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py postcycle --port 45143 --group fn.letters --msgid '<socket-a@example.invalid>' --user matrix --secret matrix-secret-8f21`
- `V0-POST-READBACK-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py postcycle --port 33765 --group fn.letters --msgid '<socket-b@example.invalid>' --user matrix --secret matrix-secret-8f21`
- `V0-POST-FRESH-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py postcycle --port 45143 --group fn.letters --msgid '<socket-a@example.invalid>' --user matrix --secret matrix-secret-8f21`
- `V0-POST-FRESH-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py postcycle --port 33765 --group fn.letters --msgid '<socket-b@example.invalid>' --user matrix --secret matrix-secret-8f21`
- `V0-POST-DUPLICATE-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py postcycle --port 45143 --group fn.letters --msgid '<socket-a@example.invalid>' --user matrix --secret matrix-secret-8f21`
- `V0-POST-DUPLICATE-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py postcycle --port 33765 --group fn.letters --msgid '<socket-b@example.invalid>' --user matrix --secret matrix-secret-8f21`
- `V0-POST-CLOCK-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py postcycle --port 45143 --group fn.letters --msgid '<socket-a@example.invalid>' --user matrix --secret matrix-secret-8f21`
- `V0-POST-CLOCK-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py postcycle --port 33765 --group fn.letters --msgid '<socket-b@example.invalid>' --user matrix --secret matrix-secret-8f21`
- `V0-POST-CONCURRENT`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py concurrent --port 45143 --group fn.letters --msgid '<concurrent@example.invalid>' --user matrix --secret matrix-secret-8f21`
- `V0-READ-CAPABILITIES-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-CAPABILITIES-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-MODE-READER-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-MODE-READER-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-NEWSGROUPS-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-OVERVIEW-FMT-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-OVERVIEW-FMT-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-TIMES-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-ACTIVE-TIMES-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-HEADERS-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LIST-HEADERS-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-GROUP-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-GROUP-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LISTGROUP-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LISTGROUP-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HEAD-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HEAD-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-BODY-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-BODY-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-STAT-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-STAT-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-MSGID-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-MSGID-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-ABSENT-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-ARTICLE-ABSENT-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-RANGE-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-OVER-RANGE-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HDR-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HDR-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XOVER-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XOVER-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XHDR-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XHDR-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XPAT-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-XPAT-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEXT-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-NEXT-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LAST-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-LAST-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-DATE-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-DATE-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HELP-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-HELP-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-UNKNOWN-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-UNKNOWN-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-FRAMING-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-READ-FRAMING-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
- `V0-PIN-DISPATCHED-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py pins --port 45143 --group fn.letters --user matrix --secret matrix-secret-8f21`
- `V0-PIN-DISPATCHED-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py pins --port 33765 --group fn.letters --user matrix --secret matrix-secret-8f21`
- `V0-PIN-ADVERTISED-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py pins --port 45143 --group fn.letters --user matrix --secret matrix-secret-8f21`
- `V0-PIN-ADVERTISED-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py pins --port 33765 --group fn.letters --user matrix --secret matrix-secret-8f21`
- `V0-TRANSIT-IDENTITY-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store policy set path-identity a.gate.example.invalid`
- `V0-TRANSIT-IDENTITY-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store policy set path-identity b.gate.example.invalid`
- `V0-TRANSIT-INDEPENDENT-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py presence --port 45143 --groups fn.letters,fn.test --present '<alpha@a.example.invalid>,<stream-a@example.invalid>,<statement-a@example.invalid>,<auth-a@example.invalid>,<socket-a@example.invalid>' --absent '<beta@b.example.invalid>,<stream-b@example.invalid>,<statement-b...`
- `V0-TRANSIT-INDEPENDENT-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py presence --port 33765 --groups fn.letters,fn.test --present '<beta@b.example.invalid>,<stream-b@example.invalid>,<statement-b@example.invalid>,<auth-b@example.invalid>,<socket-b@example.invalid>' --absent '<alpha@a.example.invalid>,<stream-a@example.invalid>,<statement-a...`
- `V0-TRANSIT-MODE-STREAM-AB`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 45143 --to-port 33765 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-MODE-STREAM-BA`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 33765 --to-port 45143 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-OFFER-AB`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 45143 --to-port 33765 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-OFFER-BA`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 33765 --to-port 45143 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-TRANSFER-AB`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 45143 --to-port 33765 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-TRANSFER-BA`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 33765 --to-port 45143 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-IDENTICAL-AB`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 45143 --to-port 33765 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-IDENTICAL-BA`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 33765 --to-port 45143 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-DUPLICATE-AB`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 45143 --to-port 33765 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-DUPLICATE-BA`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 33765 --to-port 45143 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-LOOP-AB`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 45143 --to-port 33765 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-LOOP-BA`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 33765 --to-port 45143 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-LOOP-ABSENT-AB`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 45143 --to-port 33765 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-LOOP-ABSENT-BA`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 33765 --to-port 45143 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-CHECK-FRESH-AB`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py stream --from-port 45143 --to-port 33765 --msgid '<stream-a@example.invalid>'`
- `V0-TRANSIT-CHECK-FRESH-BA`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py stream --from-port 33765 --to-port 45143 --msgid '<stream-b@example.invalid>'`
- `V0-TRANSIT-TAKETHIS-AB`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py stream --from-port 45143 --to-port 33765 --msgid '<stream-a@example.invalid>'`
- `V0-TRANSIT-TAKETHIS-BA`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py stream --from-port 33765 --to-port 45143 --msgid '<stream-b@example.invalid>'`
- `V0-TRANSIT-CHECK-DUP-AB`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 45143 --to-port 33765 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-CHECK-DUP-BA`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 33765 --to-port 45143 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-TRANSIT-TAKETHIS-DUP-AB`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 45143 --to-port 33765 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-TRANSIT-TAKETHIS-DUP-BA`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 33765 --to-port 45143 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
- `V0-FEED-QUEUE`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py post --port 45143 --msgid '<fed-ab@example.invalid>' --group fn.letters`
- `V0-FEED-OFFER`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py wait --port 33765 --from-port 45143 --msgid '<fed-ab@example.invalid>' --seconds 60`
- `V0-FEED-ONCE`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 45143 --to-port 33765 --msgid '<fed-ab@example.invalid>' --group fn.letters --loop-msgid '<loop@a.example.invalid>' --loop-identity b.gate.example.invalid`
- `V0-FEED-JOURNAL`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; ls -l $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store/feed 2>/dev/null | head -8 || true`
- `V0-CRASH-CHECKPOINT`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store anchor`
- `V0-CRASH-KILL`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py cut --to-port 33765 --mode transit --group fn.letters --msgid '<interrupted@example.invalid>' --pid 1696855`
- `V0-CRASH-SURVIVOR`: `kill -0 1696651 2>/dev/null && echo ALIVE || echo DEAD`
- `V0-CRASH-RECOVER`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store recover`
- `V0-CRASH-ACKNOWLEDGED`: `run_store.py --store <B> inspect --message-id <each of 9>`
- `V0-CRASH-INTERRUPTED`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store inspect --message-id '<interrupted@example.invalid>'`
- `V0-CRASH-RESTART`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py presence --port 33765 --groups fn.letters,fn.test --present '<beta@b.example.invalid>,<stream-b@example.invalid>,<statement-b@example.invalid>,<auth-b@example.invalid>,<socket-b@example.invalid>,<alpha@a.example.invalid>,<stream-a@example.invalid>,<fed-ab@example.invalid...`
- `V0-CRASH-CUT-TABLE`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 -c 'import sys; sys.path.insert(0, "."); from tests.campaign import cuts; cuts.verify_table(); print("TABLE OK", len(cuts.CUTS))'`
- `V0-CRASH-CAMPAIGN`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 -m tests.campaign.campaign --quick --json $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/campaign.json 2>&1 | tail -30`
- `V0-BP-IMAGE`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; FN_ACL2=${FN_ACL2:-$HOME/fn-tools/acl2-8.7/saved_acl2} swarm-build sh tools/build_native_host.sh 2>&1 | tail -20`
- `V0-BP-EXCHANGE`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/tcpcl_lab.py --image build/fn-host --work $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/tcpcl-lab`
- `V0-BP-REFUSED`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/tcpcl_lab.py --image build/fn-host --work $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/tcpcl-lab`
- `V0-BP-KEEPALIVE`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/tcpcl_lab.py --image build/fn-host --work $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/tcpcl-lab`
- `V0-BP-CRASH`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/tcpcl_lab.py --image build/fn-host --work $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/tcpcl-lab`
- `V0-BP-PROFILE`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/tcpcl_lab.py --image build/fn-host --work $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/tcpcl-lab`
- `V0-BP-REPLAY`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/tcpcl_lab.py --image build/fn-host --work $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/tcpcl-lab`
- `V0-BP-NODE`: `python3 tests/bp-dtn7/run_fn_bp_interop.py`
- `V0-STX-SIGN`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml statement sign --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.article --seed $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/seed.hex --ed25519 > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.field`
- `V0-STX-ATTACH`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml statement attach --field $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.field --article $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.article > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.signed`
- `V0-STX-CROSS`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py presence --port 33765 --groups fn.letters --present '<statement-a@example.invalid>'`
- `V0-STX-VERIFY`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml statement verify --article $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.signed --keyring $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/keyring`
- `V0-STX-UNVERIFIED`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml statement verify --article $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.tampered --keyring $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/keyring`
- `V0-STX-READER`: `HDR :fn-verified over the served path`
- `V0-MEDIA-EXPORT`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/media.py export --help 2>&1 | head -20`
- `V0-MEDIA-VERIFY`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/media.py export --help 2>&1 | head -20`
- `V0-MEDIA-IMPORT`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/media.py export --help 2>&1 | head -20`
- `V0-SCALE-CEILING`: `python3 tools/scale_gate.py cdbd6b2 --host hbox`
- `V0-INN-INTEROP`: `python3 tools/inn_lab.py cdbd6b2 --host hbox`
- `V0-CLIENT-NNTPLIB-A`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3.12 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/independent.py --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>' --user matrix --secret matrix-secret-8f21`
- `V0-CLIENT-NNTPLIB-B`: `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3.12 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/independent.py --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>' --user matrix --secret matrix-secret-8f21`
- `V0-CLIENT-SLRN`: `slrn -h <host> -p <port>`

## Every command

| # | step | rc | first line | s |
| --- | --- | --- | --- | --- |
| 1 | preflight | 0 | `os=Ubuntu 24.10 kernel=Linux 6.11.0-29-generic arch=x86_64 cores=24` | 0.4 |
| 2 | acquire deploy lock | 0 | `` | 0.2 |
| 3 | ship archive | 0 | `` | 3.7 |
| 4 | make run dir | 0 | `` | 0.3 |
| 5 | install drive.py | 0 | `` | 0.2 |
| 6 | install feed.py | 0 | `` | 0.2 |
| 7 | install matrix.py | 0 | `` | 0.3 |
| 8 | acquire certificate artifact set | 1 | `profile=default image=build/fn-host result=no complete current artifact set passed an ACL2 load rejected=0` | 1.0 |
| 9 | certify declared artifact closure | 0 | `ACL2 certification passed: books/cbor, books/wildmat, books/cbor-invariants, books/frame-octets, books/frame-fields, books/frame-journal, books/frame, books/frame-invariants, books/defrecord, books/cl` | 271.6 |
| 10 | load declared artifact closure | 0 | `profile=default image=build/fn-host roots=24 result=loaded` | 1.1 |
| 11 | feature probe | 0 | `fn-init=yes` | 0.8 |
| 12 | free ports | 0 | `45143 33765` | 0.4 |
| 13 | node A directories | 0 | `` | 0.3 |
| 14 | node A fn init | 0 | `initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store` | 1.2 |
| 15 | node A fn.toml | 0 | `# fn configuration; see docs/operator.md and packaging/fn.toml.example` | 0.2 |
| 16 | node A fn status | 0 | `owner=absent generation=1 transactions=0 articles=0 staging-orphans=0 anchor=none` | 2.0 |
| 17 | node A store config | 0 | `generation=1 served=fn.letters,fn.test domain=fn.letters,fn.test` | 2.0 |
| 18 | node A has a configuration | 0 | `YES` | 0.4 |
| 19 | node B directories | 0 | `` | 0.2 |
| 20 | node B fn init | 0 | `initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store` | 1.1 |
| 21 | node B fn.toml | 0 | `# fn configuration; see docs/operator.md and packaging/fn.toml.example` | 0.2 |
| 22 | node B fn status | 0 | `owner=absent generation=1 transactions=0 articles=0 staging-orphans=0 anchor=none` | 1.9 |
| 23 | node B store config | 0 | `generation=1 served=fn.letters,fn.test domain=fn.letters,fn.test` | 1.9 |
| 24 | node B has a configuration | 0 | `YES` | 0.3 |
| 25 | loopback refusal: init | 0 | `initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/loopback/store` | 1.1 |
| 26 | loopback refusal: run | 1 | `refused run listener host '10.99.0.1' is not loopback; the owner binds 127.0.0.1 only (docs/architecture.md)` | 0.3 |
| 27 | install seed.hex | 0 | `` | 0.3 |
| 28 | principal new | 0 | `id 86c30609295a4cc0198f20cb5399865eaab7cbd863bdf41714e205f2c8019a24` | 1.2 |
| 29 | node A principal set-password | 0 | `accepted wrote /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store/auth.toml (mode 0600) with login 'matrix', principal 86c30609295a4cc0..., posting allowed.  The stored value is a salted digest (` | 0.6 |
| 30 | node A principal list | 0 | `matrix principal=86c30609295a4cc0198f20cb5399865eaab7cbd863bdf41714e205f2c8019a24 posting=true` | 0.4 |
| 31 | node B principal set-password | 0 | `accepted wrote /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store/auth.toml (mode 0600) with login 'matrix', principal 86c30609295a4cc0..., posting allowed.  The stored value is a salted digest (` | 0.5 |
| 32 | node B principal list | 0 | `accepted principal list registry=/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store/auth.toml count=1` | 0.3 |
| 33 | install statement.article | 0 | `` | 0.4 |
| 34 | statement sign | 0 | `verified statement sign creator 86c30609295a4cc0198f20cb5399865eaab7cbd863bdf41714e205f2c8019a24 ed25519 signature over the ACL2 signing preimage: 52c34bd3a360e5abeab1a17ab8a0789ec34d478e5d0ed964b1c23` | 1.2 |
| 35 | statement attach | 0 | `verified statement attach` | 0.3 |
| 36 | install seed.article | 0 | `` | 0.2 |
| 37 | node A outcome accepted | 0 | `committed sequence=0 charge=2` | 2.0 |
| 38 | node A outcome refused | 1 | `` | 2.0 |
| 39 | node A outcome uncertain | 3 | `store: indeterminate injected failure after final publication` | 1.9 |
| 40 | node A recover after the uncertain publication | 0 | `recovered transactions=2 articles=2 staging-orphans=0 anchor=none checkpoint=none` | 1.9 |
| 41 | node A after recovery: the uncertain <uncertain-a@example.invalid> | 0 | `From: gate@example.invalid` | 1.9 |
| 42 | install seed.article | 0 | `` | 0.3 |
| 43 | node B outcome accepted | 0 | `committed sequence=0 charge=2` | 1.9 |
| 44 | node B outcome refused | 1 | `` | 1.9 |
| 45 | node B outcome uncertain | 3 | `store: indeterminate injected failure after final publication` | 2.0 |
| 46 | node B recover after the uncertain publication | 0 | `recovered transactions=2 articles=2 staging-orphans=0 anchor=none checkpoint=none` | 2.1 |
| 47 | node B after recovery: the uncertain <uncertain-b@example.invalid> | 0 | `From: gate@example.invalid` | 1.9 |
| 48 | install stream-a.article | 0 | `` | 0.4 |
| 49 | node A seed <stream-a@example.invalid> | 0 | `committed sequence=2 charge=2` | 1.9 |
| 50 | node A seed <statement-a@example.invalid> | 0 | `committed sequence=3 charge=2` | 1.9 |
| 51 | node A fn init again | 0 | `initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store` | 0.3 |
| 52 | node A still holds <alpha@a.example.invalid> after the second init | 0 | `From: gate@example.invalid` | 2.2 |
| 53 | node A still holds <stream-a@example.invalid> after the second init | 0 | `From: gate@example.invalid` | 2.2 |
| 54 | node A still holds <statement-a@example.invalid> after the second init | 0 | `FN-Statement: AVgghsMGCSlaTMAZjyDLU5mGXqq3y9hjvfQXFOIF8sgBmiQAAAABWCA56HsxFwaTKnD1gu3bdDkBri5rDUFt4WN+LwX4qRoTLVggG+Ml0glvglfAVXS3HYFJYDpqXE1BE7cHzQ8OIGXLKmM=` | 2.0 |
| 55 | node A group create fn.matrix | 0 | `group created name=fn.matrix generation=2` | 1.9 |
| 56 | node A group create fn.matrix.throwaway | 0 | `group created name=fn.matrix.throwaway generation=3` | 1.9 |
| 57 | node A group retire fn.matrix.throwaway | 0 | `group retired name=fn.matrix.throwaway generation=4` | 2.1 |
| 58 | node A group retire an unserved group | 1 | `refused group retire fn.not.served store: refused group retire: no-such-group` | 2.0 |
| 59 | node A capacity store | 0 | `initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/capacity-store` | 1.4 |
| 60 | node A capacity 64 | 0 | `capacity set n=64 generation=2` | 2.8 |
| 61 | node A capacity 1 | 0 | `capacity set n=1 generation=3` | 4.6 |
| 62 | install capacity.article | 0 | `` | 0.3 |
| 63 | node A post beyond the capacity | 1 | `store: ACL2 refused post: refused` | 2.0 |
| 64 | install stream-b.article | 0 | `` | 0.2 |
| 65 | node B seed <stream-b@example.invalid> | 0 | `committed sequence=2 charge=2` | 2.0 |
| 66 | install statement-b.article | 0 | `` | 0.4 |
| 67 | node B seed <statement-b@example.invalid> | 0 | `committed sequence=3 charge=2` | 2.1 |
| 68 | node B fn init again | 0 | `initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store` | 0.5 |
| 69 | node B still holds <beta@b.example.invalid> after the second init | 0 | `From: gate@example.invalid` | 2.0 |
| 70 | node B still holds <stream-b@example.invalid> after the second init | 0 | `From: gate@example.invalid` | 1.9 |
| 71 | node B still holds <statement-b@example.invalid> after the second init | 0 | `From: gate@example.invalid` | 2.0 |
| 72 | node B group create fn.matrix | 0 | `group created name=fn.matrix generation=2` | 2.1 |
| 73 | node B group create fn.matrix.throwaway | 0 | `group created name=fn.matrix.throwaway generation=3` | 2.0 |
| 74 | node B group retire fn.matrix.throwaway | 0 | `group retired name=fn.matrix.throwaway generation=4` | 2.0 |
| 75 | node B group retire an unserved group | 1 | `refused group retire fn.not.served store: refused group retire: no-such-group` | 1.9 |
| 76 | node B capacity store | 0 | `initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/capacity-store` | 1.1 |
| 77 | node B capacity 64 | 0 | `capacity set n=64 generation=2` | 2.9 |
| 78 | node B capacity 1 | 0 | `capacity set n=1 generation=3` | 2.8 |
| 79 | install capacity.article | 0 | `` | 0.3 |
| 80 | node B post beyond the capacity | 1 | `store: ACL2 refused post: refused` | 2.0 |
| 81 | peer record CLI | 0 | `STORE-PEER` | 0.3 |
| 82 | node A path-identity | 0 | `policy set path-identity=a.gate.example.invalid generation=5` | 1.9 |
| 83 | node B path-identity | 0 | `policy set path-identity=b.gate.example.invalid generation=5` | 2.0 |
| 84 | node A peer record for B | 0 | `peer added name=b generation=6` | 1.9 |
| 85 | node A lists its peers | 0 | `name=b path-identity=b.gate.example.invalid transport=127.0.0.1:33765 inbound=fn.* max-octets=32768 max-inflight=16 outbound=fn.* max-queue=1024 streaming=yes backoff-ms=1000 auth=source-address:127.0` | 2.0 |
| 86 | node B peer record for A | 0 | `peer added name=a generation=6` | 2.3 |
| 87 | node B lists its peers | 0 | `name=a path-identity=a.gate.example.invalid transport=127.0.0.1:45143 inbound=fn.* max-octets=32768 max-inflight=16 outbound=fn.* max-queue=1024 streaming=yes backoff-ms=1000 auth=source-address:127.0` | 2.0 |
| 88 | start server (node A (fn), a-main) | 0 | `LISTENING 45143` | 2.3 |
| 89 | node A pid | 0 | `1696651` | 0.2 |
| 90 | start server (node B (fn), b-main) | 0 | `LISTENING 33765` | 2.2 |
| 91 | node B pid | 0 | `1696855` | 0.2 |
| 92 | node A server is alive | 0 | `ALIVE` | 0.2 |
| 93 | node A serves fn.matrix | 0 | `{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}` | 0.4 |
| 94 | node A server is alive | 0 | `ALIVE` | 0.2 |
| 95 | node A reader surface | 0 | `{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES ` | 0.7 |
| 96 | node A server is alive | 0 | `ALIVE` | 0.2 |
| 97 | node A AUTHINFO session | 0 | `{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "POST", "OVER", "HDR", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "AUTHINFO ADVERTIS` | 0.3 |
| 98 | node A server is alive | 0 | `ALIVE` | 0.2 |
| 99 | node A POST cycle | 0 | `{"AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "GROUP BEFORE": "211 5 1 5 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article recei` | 0.4 |
| 100 | node B server is alive | 0 | `ALIVE` | 0.2 |
| 101 | node B serves fn.matrix | 0 | `{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}` | 0.2 |
| 102 | node B server is alive | 0 | `ALIVE` | 0.2 |
| 103 | node B reader surface | 0 | `{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES ` | 0.8 |
| 104 | node B server is alive | 0 | `ALIVE` | 0.2 |
| 105 | node B AUTHINFO session | 0 | `{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "POST", "OVER", "HDR", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "AUTHINFO ADVERTIS` | 0.3 |
| 106 | node B server is alive | 0 | `ALIVE` | 0.2 |
| 107 | node B POST cycle | 0 | `{"AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "GROUP BEFORE": "211 7 1 7 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article recei` | 0.4 |
| 108 | node A server is alive | 0 | `ALIVE` | 0.2 |
| 109 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 110 | install independent.py | 0 | `` | 0.2 |
| 111 | independent nntplib client on node A | 0 | `/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/independent.py:6: DeprecationWarning: 'nntplib' is deprecated and slated for removal in Python 3.13` | 0.3 |
| 112 | independent nntplib client on node B | 0 | `/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/independent.py:6: DeprecationWarning: 'nntplib' is deprecated and slated for removal in Python 3.13` | 0.3 |
| 113 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 114 | node B server is alive | 0 | `ALIVE` | 0.2 |
| 115 | independence: node A holds its own and not B's seeds | 0 | `{"groups": {"fn.letters": "211 8 1 8 fn.letters", "fn.test": "211 0 1 0 fn.test"}, "present": {"<alpha@a.example.invalid>": "220 0 <alpha@a.example.invalid> article follows", "<stream-a@example.invali` | 0.2 |
| 116 | independence: node B holds its own and not A's seeds | 0 | `{"groups": {"fn.letters": "211 8 1 8 fn.letters", "fn.test": "211 0 1 0 fn.test"}, "present": {"<beta@b.example.invalid>": "220 0 <beta@b.example.invalid> article follows", "<stream-b@example.invalid>` | 0.4 |
| 117 | node B server is alive | 0 | `ALIVE` | 0.2 |
| 118 | transit AB: offer <alpha@a.example.invalid> from A to B | 0 | `{"msgid": "<alpha@a.example.invalid>", "source": "220 0 <alpha@a.example.invalid> article follows", "source_lines": 7, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE` | 0.3 |
| 119 | transit AB: CHECK/TAKETHIS <stream-a@example.invalid> from A to B | 0 | `{"SOURCE": "220 0 <stream-a@example.invalid> article follows", "MODE STREAM": "203 streaming permitted", "CHECK": "238 <stream-a@example.invalid>", "TAKETHIS": "239 <stream-a@example.invalid>", "CHECK` | 0.4 |
| 120 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 121 | transit BA: offer <beta@b.example.invalid> from B to A | 0 | `{"msgid": "<beta@b.example.invalid>", "source": "220 0 <beta@b.example.invalid> article follows", "source_lines": 7, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE A` | 0.3 |
| 122 | transit BA: CHECK/TAKETHIS <stream-b@example.invalid> from B to A | 0 | `{"SOURCE": "220 0 <stream-b@example.invalid> article follows", "MODE STREAM": "203 streaming permitted", "CHECK": "238 <stream-b@example.invalid>", "TAKETHIS": "239 <stream-b@example.invalid>", "CHECK` | 0.4 |
| 123 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 124 | node A capability pins | 0 | `{"advertised": ["VERSION", "READER", "POST", "OVER", "HDR", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING"], "answered": {"READER": "211 10 1 10 fn.letters", "POST": "340 send article to be posted", "` | 240.4 |
| 125 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 126 | node B capability pins | 0 | `{"advertised": ["VERSION", "READER", "POST", "OVER", "HDR", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING"], "answered": {"READER": "211 10 1 10 fn.letters", "POST": "340 send article to be posted", "` | 240.4 |
| 127 | node A server is alive | 0 | `ALIVE` | 0.5 |
| 128 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 129 | a second reader across node A's POST | 0 | `{"WATCHER BEFORE": "211 10 1 10 fn.letters", "AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "POST": "340 send article to be posted", "WATCHER MID": "211 10 1` | 0.3 |
| 130 | node A server is alive | 0 | `ALIVE` | 0.3 |
| 131 | node B server is alive | 0 | `ALIVE` | 0.2 |
| 132 | node A control socket | 0 | `SOCKET` | 0.2 |
| 133 | live reconfiguration: declare a group on node A | 0 | `{"line": "DECLARE-GROUP fn.matrix.live", "reply": "declared", "ok": true}` | 0.2 |
| 134 | offline group create while the service holds the store | 1 | `refused group create fn.matrix.offline an owner is live on /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/control.sock; a configuration record needs the writer lock, so stop the service first` | 0.3 |
| 135 | node A server is alive | 0 | `ALIVE` | 0.2 |
| 136 | node B server is alive | 0 | `ALIVE` | 0.2 |
| 137 | owner feed: A posts <fed-ab@example.invalid> | 0 | `{"greeting": "200 fn-nntp experimental server ready", "post": "340 send article to be posted", "result": "240 article received OK", "ok": true}` | 0.4 |
| 138 | owner feed: B receives <fed-ab@example.invalid> from A's feed | 0 | `{"msgid": "<fed-ab@example.invalid>", "seconds": 60.0, "ok": true, "status": "220 0 <fed-ab@example.invalid> article follows", "attempts": 1, "lines": 11, "source": "220 0 <fed-ab@example.invalid> art` | 0.3 |
| 139 | owner feed: B serves <fed-ab@example.invalid> byte for byte as A does | 0 | `{"msgid": "<fed-ab@example.invalid>", "seconds": 60.0, "ok": true, "status": "220 0 <fed-ab@example.invalid> article follows", "attempts": 1, "lines": 11, "source": "220 0 <fed-ab@example.invalid> art` | 0.0 |
| 140 | owner feed: A's feed offered <fed-ab@example.invalid> with IHAVE | 1 | `` | 0.2 |
| 141 | owner feed: a second offer of <fed-ab@example.invalid> draws 435/438 | 1 | `{"msgid": "<fed-ab@example.invalid>", "source": "220 0 <fed-ab@example.invalid> article follows", "source_lines": 11, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ` | 0.4 |
| 142 | owner feed: B posts <fed-ba@example.invalid> | 0 | `{"greeting": "200 fn-nntp experimental server ready", "post": "340 send article to be posted", "result": "240 article received OK", "ok": true}` | 0.3 |
| 143 | owner feed: A receives <fed-ba@example.invalid> from B's feed | 0 | `{"msgid": "<fed-ba@example.invalid>", "seconds": 60.0, "ok": true, "status": "220 0 <fed-ba@example.invalid> article follows", "attempts": 1, "lines": 11, "source": "220 0 <fed-ba@example.invalid> art` | 0.3 |
| 144 | owner feed: A serves <fed-ba@example.invalid> byte for byte as B does | 0 | `{"msgid": "<fed-ba@example.invalid>", "seconds": 60.0, "ok": true, "status": "220 0 <fed-ba@example.invalid> article follows", "attempts": 1, "lines": 11, "source": "220 0 <fed-ba@example.invalid> art` | 0.0 |
| 145 | owner feed: B's feed offered <fed-ba@example.invalid> with IHAVE | 1 | `` | 0.3 |
| 146 | owner feed: a second offer of <fed-ba@example.invalid> draws 435/438 | 1 | `{"msgid": "<fed-ba@example.invalid>", "source": "220 0 <fed-ba@example.invalid> article follows", "source_lines": 11, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ` | 0.3 |
| 147 | feed: the journal on node A | 0 | `total 4` | 0.3 |
| 148 | node A server is alive | 0 | `ALIVE` | 0.2 |
| 149 | node B server is alive | 0 | `ALIVE` | 0.3 |
| 150 | kill -9 node B mid-transit | 0 | `{"mode": "transit", "open": "335 send it; end with <CR-LF>.<CR-LF>", "opened": true, "killed_pid": 1696855, "after_kill": "ConnectionResetError: [Errno 104] Connection reset by peer", "ok": true}` | 0.7 |
| 151 | node A survived node B's death | 0 | `ALIVE` | 0.3 |
| 152 | node B recover after the kill | 0 | `recovered transactions=13 articles=13 staging-orphans=0 anchor=none checkpoint=none` | 2.0 |
| 153 | node B status after recovery | 0 | `transactions=13 articles=13 staging-orphans=0 unsigned-legacy-experiment` | 1.9 |
| 154 | node B still holds <beta@b.example.invalid> after recovery | 0 | `From: gate@example.invalid` | 2.1 |
| 155 | node B still holds <stream-b@example.invalid> after recovery | 0 | `From: gate@example.invalid` | 2.0 |
| 156 | node B still holds <statement-b@example.invalid> after recovery | 0 | `From: gate@example.invalid` | 2.1 |
| 157 | node B still holds <auth-b@example.invalid> after recovery | 0 | `Path: b.gate.example.invalid!not-for-mail` | 2.1 |
| 158 | node B still holds <socket-b@example.invalid> after recovery | 0 | `Path: b.gate.example.invalid!not-for-mail` | 2.3 |
| 159 | node B still holds <alpha@a.example.invalid> after recovery | 0 | `From: gate@example.invalid` | 2.0 |
| 160 | node B still holds <stream-a@example.invalid> after recovery | 0 | `From: gate@example.invalid` | 2.1 |
| 161 | node B still holds <fed-ab@example.invalid> after recovery | 0 | `Path: a.gate.example.invalid!not-for-mail` | 2.3 |
| 162 | node B still holds <fed-ba@example.invalid> after recovery | 0 | `Path: b.gate.example.invalid!not-for-mail` | 2.1 |
| 163 | node B does not hold the interrupted <interrupted@example.invalid> | 1 | `` | 2.1 |
| 164 | start server (node B (fn), b-after-recovery) | 0 | `LISTENING 33765` | 2.4 |
| 165 | node B pid | 0 | `1718666` | 0.4 |
| 166 | reread node B after recovery | 0 | `{"groups": {"fn.letters": "211 13 1 13 fn.letters", "fn.test": "211 0 1 0 fn.test"}, "present": {"<beta@b.example.invalid>": "220 0 <beta@b.example.invalid> article follows", "<stream-b@example.invali` | 0.4 |
| 167 | campaign: the cut table matches the injector | 0 | `TABLE OK 54` | 0.3 |
| 168 | campaign: run the cuts | 0 | `committed sequence=1 charge=2` | 180.2 |
| 169 | native image for the tcpcl layer | 0 | `built build/fn-host (260M core)` | 4.4 |
| 170 | tcpcl lab | 1 | `{"a_holds_b_bundle": true, "acks_from_a": 2, "acks_from_b": 2, "active_events": 8, "active_outcomes": [["accepted", "xfer=0 path=/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/tcpcl-lab/exchange/acti` | 8.5 |
| 171 | statement: offer the statement-bearing article from A to B | 0 | `{"msgid": "<statement-a@example.invalid>", "source": "220 0 <statement-a@example.invalid> article follows", "source_lines": 8, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIS` | 0.5 |
| 172 | statement: node B serves the statement-bearing article | 0 | `{"groups": {"fn.letters": "211 14 1 14 fn.letters"}, "present": {"<statement-a@example.invalid>": "220 0 <statement-a@example.invalid> article follows"}, "absent": {}, "ok": true}` | 0.4 |
| 173 | install keyring | 0 | `` | 0.6 |
| 174 | statement verify on node B's copy | 0 | `verified 86c30609295a4cc0198f20cb5399865eaab7cbd863bdf41714e205f2c8019a24 keyring 0` | 1.3 |
| 175 | statement tamper | 0 | `` | 0.4 |
| 176 | statement verify on the tampered copy | 3 | `unverified statement verify` | 1.3 |
| 177 | media export usage | 0 | `usage: media export [-h] --media MEDIA --media-id MEDIA_ID [--bundle ID=PATH]` | 0.6 |
| 178 | stop server node A (main) | 0 | `stopped` | 1.3 |
| 179 | node A store after the stop | 0 | `transactions=13 articles=13 staging-orphans=0 unsigned-legacy-experiment` | 2.1 |
| 180 | node A log tail | 0 | `LISTENING 45143` | 0.6 |
| 181 | stop server node B (main) | 0 | `stopped` | 1.4 |
| 182 | node B store after the stop | 0 | `transactions=14 articles=14 staging-orphans=0 unsigned-legacy-experiment` | 2.4 |
| 183 | node B log tail | 0 | `LISTENING 33765` | 0.3 |
| 184 | checkpoint on node A | 0 | `anchor accepted server=int08h midpoint_us=1789974525088003 radius_us=5000000 incarnation=0` | 1.3 |
| 185 | node A reopens after the checkpoint | 0 | `transactions=13 articles=13 staging-orphans=0 unsigned-legacy-experiment` | 2.0 |
| 186 | peer remove a peer that is not there | 1 | `store: refused peer remove: no-such-peer` | 2.0 |
| 187 | peer remove the configured peer | 0 | `peer removed name=b generation=7` | 2.3 |
| 188 | stop server node A (main) | 0 | `stopped` | 0.4 |
| 189 | stop the tap in front of node A | 0 | `stopped` | 0.4 |
| 190 | stop server node B (main) | 0 | `stopped` | 0.5 |
| 191 | stop the tap in front of node B | 0 | `stopped` | 0.5 |
| 192 | stray fn processes | 0 | `CLEAN` | 0.4 |
| 193 | release deploy lock | 0 | `` | 0.4 |

### Commands in full

1. **preflight** -- `. /etc/os-release 2>/dev/null || true ; echo "os=${PRETTY_NAME:-unknown} kernel=$(uname -sr) arch=$(uname -m) cores=$(nproc 2>/dev/null || echo ?)" ; echo "python3=$(python3 -V 2>&1)" ; for p in python3.9 python3.10 python3.11 python3.12; do ; command -v $p >/dev/null && echo "alt=$p $($p -V 2>&1)" ; done ; for c in slrn tin nn trn inews expect script; do ; printf 'client %s=%s\n' "$c" "$(comma...`
2. **acquire deploy lock** -- `mkdir -p $HOME/fn-deploy/.locks ; if ! mkdir $HOME/fn-deploy/.locks/w12-integrated-cdb-cdbd6b2.lock 2>/dev/null; then ; echo "deploy identity is already active: w12-integrated-cdb-cdbd6b2" ; exit 73 ; fi`
3. **ship archive** -- `git archive cdbd6b2 | tar -x -C $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2`
4. **make run dir** -- `mkdir -p $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run`
5. **install drive.py** -- `base64 -d > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/drive.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJJbmRlcGVuZGVudCBOTlRQIGRyaXZpbmcgZm9yIHRo ; ZSBkZXBsb3kgZ2F0ZTsgbm8gZm4gbW9kdWxlIGlzIGltcG9ydGVkLiIiIgppbXBvcnQgYXJncGFy ; c2UsIGpzb24sIG9zLCBzb2NrZXQsIHN5cywgdGltZQoKCmNsYXNzIENvbm46CiAgICBkZWYgX19p ; bml0X18oc2VsZiwgcG9ydCwgdGltZW91dD0zMCk6CiAgICAgICAgc2VsZi5zb2NrID0gc...`
6. **install feed.py** -- `base64 -d > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJUaGUgdHdvLW5vZGUgcGhhc2VzLiAgTm8gZm4gbW9k ; dWxlIGlzIGltcG9ydGVkOyBDb25uIGlzIGRlcGxveV9nYXRlJ3MuCgpgcHJlc2VuY2VgIGlzIHRo ; ZSBjb250cm9sIGFuZCB0aGUgcmVyZWFkOiB3aGF0IGEgbm9kZSBob2xkcyBhbmQgd2hhdCBpdCBt ; dXN0Cm5vdC4gIGByZWxheWAgaXMgUkZDIDM5NzcgNi4zLjIgZHJpdmVuIGJ5IGhhbmQgb3...`
7. **install matrix.py** -- `base64 -d > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJUaGUgdjAgbWF0cml4J3Mgb3duIE5OVFAgcGhhc2Vz ; LiAgTm8gZm4gbW9kdWxlIGlzIGltcG9ydGVkOyBDb25uIGlzCnRvb2xzL2RlcGxveV9nYXRlLnB5 ; J3MgZHJpdmVyLCBzaGlwcGVkIGJlc2lkZSB0aGlzIGZpbGUgYXMgZHJpdmUucHkuCgpFdmVyeSBw ; aGFzZSBwcmludHMgT05FIGpzb24gb2JqZWN0IHdob3NlIGtleXMgYXJlIGNvbW1hbmQg...`
8. **acquire certificate artifact set** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/proof_artifacts.py acquire --profile default --root $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 --cache /tank/fn/certcache --acl2 "$FN_ACL2"`
   - one absolute origin, one ACL2 executable digest, then an actual ACL2 load
9. **certify declared artifact closure** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; export FN_CERT_CACHE=/tank/fn/certcache ; export FN_CERT_ORIGIN_KIND=gate ; python3 tools/certify_books.py --jobs 4 --closure $(python3 tools/proof_artifacts.py roots --profile default)`
   - bounded to the selected native image and deployed entry points
10. **load declared artifact closure** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/proof_artifacts.py validate --profile default --root $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 --acl2 "$FN_ACL2"`
11. **feature probe** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; for s in init run post group capacity status recover anchor principal peer statement; do ; if python3 bin/fn $s --help >/dev/null 2>&1; then echo "fn-$s=yes"; else echo "fn-$s=no"; fi ; done ; python3 tools/run_reader.py --help 2>&1 | grep -q -- '--post' \ ; && echo reader-post=yes || echo reader-post=no ; [ -f tools/run_feed.py ] && ech...`
12. **free ports** -- `python3 -c 'import socket; s=[socket.socket() for _ in range(2)]; [x.bind(("127.0.0.1", 0)) for x in s]; print(" ".join(str(x.getsockname()[1]) for x in s)); [x.close() for x in s]'`
13. **node A directories** -- `mkdir -p $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/peers`
14. **node A fn init** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml init --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store --group fn.letters --group fn.test --listen 127.0.0.1:45143 --control $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/control.sock --log $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.log --acl2 "$FN_...`
15. **node A fn.toml** -- `cat $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml 2>/dev/null || echo NO-CONFIG`
16. **node A fn status** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml status`
17. **node A store config** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store config`
18. **node A has a configuration** -- `test -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml && echo YES || echo NO`
19. **node B directories** -- `mkdir -p $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/peers`
20. **node B fn init** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml init --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store --group fn.letters --group fn.test --listen 127.0.0.1:33765 --control $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/control.sock --log $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.log --acl2 "$FN_...`
21. **node B fn.toml** -- `cat $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml 2>/dev/null || echo NO-CONFIG`
22. **node B fn status** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml status`
23. **node B store config** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store config`
24. **node B has a configuration** -- `test -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml && echo YES || echo NO`
25. **loopback refusal: init** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; mkdir -p $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/loopback && python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/loopback/fn.toml init --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/loopback/store --group fn.letters --listen 10.99.0.1:1119`
26. **loopback refusal: run** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; timeout 60 python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/loopback/fn.toml run --control $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/loopback/control.sock`
27. **install seed.hex** -- `base64 -d > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/seed.hex <<'FN_GATE_EOF' ; NWY1ZjVmNWY1ZjVmNWY1ZjVmNWY1ZjVmNWY1ZjVmNWY1ZjVmNWY1ZjVmNWY1ZjVmNWY1ZjVmNWY1 ; ZjVmNWY1Zgo= ; FN_GATE_EOF ; chmod 644 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/seed.hex`
28. **principal new** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml principal new --seed $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/seed.hex`
29. **node A principal set-password** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml principal set-password matrix --password matrix-secret-8f21 --principal 86c30609295a4cc0198f20cb5399865eaab7cbd863bdf41714e205f2c8019a24`
30. **node A principal list** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml principal list`
31. **node B principal set-password** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml principal set-password matrix --password matrix-secret-8f21 --principal 86c30609295a4cc0198f20cb5399865eaab7cbd863bdf41714e205f2c8019a24`
32. **node B principal list** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml principal list`
33. **install statement.article** -- `base64 -d > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IGEgY2FycmllZCBzdGF0ZW1lbnQN ; Ck5ld3Nncm91cHM6IGZuLmxldHRlcnMNCkRhdGU6IE1vbiwgMjEgU2VwIDIwMjYgMDY6NTQ6NTMg ; KzAwMDANCk1lc3NhZ2UtSUQ6IDxzdGF0ZW1lbnQtYUBleGFtcGxlLmludmFsaWQ+DQoNCkEgc3Rh ; dGVtZW50IGNhcnJpZWQgYmV0d2VlbiB0d28gZm4gbm9kZXMuDQo= ; FN_GATE_EOF ; ...`
34. **statement sign** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml statement sign --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.article --seed $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/seed.hex --ed25519 > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.field`
35. **statement attach** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml statement attach --field $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.field --article $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.article > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.signed`
36. **install seed.article** -- `base64 -d > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/seed.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IGFscGhhLCB3cml0dGVuIG9uIEEN ; Ck5ld3Nncm91cHM6IGZuLmxldHRlcnMNCkRhdGU6IE1vbiwgMjEgU2VwIDIwMjYgMDY6NTQ6NTUg ; KzAwMDANCk1lc3NhZ2UtSUQ6IDxhbHBoYUBhLmV4YW1wbGUuaW52YWxpZD4NCg0KV3JpdHRlbiBv ; biBub2RlIEEgYnkgdGhlIHYwIG1hdHJpeC4NCg== ; FN_GATE_EOF ; chmod 644 $HOME...`
37. **node A outcome accepted** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store post --message-id '<alpha@a.example.invalid>' --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/seed.article --group fn.letters`
38. **node A outcome refused** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store inspect --message-id '<absent@example.invalid>'`
39. **node A outcome uncertain** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store post --message-id '<uncertain-a@example.invalid>' --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/seed.article --group fn.letters --inject-fault postpublish`
40. **node A recover after the uncertain publication** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store recover`
41. **node A after recovery: the uncertain <uncertain-a@example.invalid>** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store inspect --message-id '<uncertain-a@example.invalid>'`
42. **install seed.article** -- `base64 -d > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/seed.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IGJldGEsIHdyaXR0ZW4gb24gQg0K ; TmV3c2dyb3VwczogZm4ubGV0dGVycw0KRGF0ZTogTW9uLCAyMSBTZXAgMjAyNiAwNjo1NTowNCAr ; MDAwMA0KTWVzc2FnZS1JRDogPGJldGFAYi5leGFtcGxlLmludmFsaWQ+DQoNCldyaXR0ZW4gb24g ; bm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXguDQo= ; FN_GATE_EOF ; chmod 644 $HOME/fn-...`
43. **node B outcome accepted** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store post --message-id '<beta@b.example.invalid>' --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/seed.article --group fn.letters`
44. **node B outcome refused** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store inspect --message-id '<absent@example.invalid>'`
45. **node B outcome uncertain** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store post --message-id '<uncertain-b@example.invalid>' --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/seed.article --group fn.letters --inject-fault postpublish`
46. **node B recover after the uncertain publication** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store recover`
47. **node B after recovery: the uncertain <uncertain-b@example.invalid>** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store inspect --message-id '<uncertain-b@example.invalid>'`
48. **install stream-a.article** -- `base64 -d > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/stream-a.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IGZvciB0aGUgc3RyZWFtaW5nIG9m ; ZmVyDQpOZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBNb24sIDIxIFNlcCAyMDI2IDA2OjU1 ; OjE1ICswMDAwDQpNZXNzYWdlLUlEOiA8c3RyZWFtLWFAZXhhbXBsZS5pbnZhbGlkPg0KDQpTZWVk ; ZWQgb24gbm9kZSBBIGJ5IHRoZSB2MCBtYXRyaXguDQo= ; FN_GATE_EOF ; chmod 6...`
49. **node A seed <stream-a@example.invalid>** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store post --message-id '<stream-a@example.invalid>' --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/stream-a.article --group fn.letters`
50. **node A seed <statement-a@example.invalid>** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store post --message-id '<statement-a@example.invalid>' --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.signed --group fn.letters`
51. **node A fn init again** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn2.toml init --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store --group fn.letters --group fn.test`
52. **node A still holds <alpha@a.example.invalid> after the second init** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store inspect --message-id '<alpha@a.example.invalid>'`
53. **node A still holds <stream-a@example.invalid> after the second init** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store inspect --message-id '<stream-a@example.invalid>'`
54. **node A still holds <statement-a@example.invalid> after the second init** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store inspect --message-id '<statement-a@example.invalid>'`
55. **node A group create fn.matrix** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml group create fn.matrix`
56. **node A group create fn.matrix.throwaway** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml group create fn.matrix.throwaway`
57. **node A group retire fn.matrix.throwaway** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml group retire fn.matrix.throwaway`
58. **node A group retire an unserved group** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml group retire fn.not.served`
59. **node A capacity store** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/capacity-store init --group fn.letters`
60. **node A capacity 64** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/capacity-store capacity 64`
61. **node A capacity 1** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/capacity-store capacity 1`
62. **install capacity.article** -- `base64 -d > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/capacity.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG92ZXIgdGhlIGNhcGFjaXR5DQpO ; ZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBNb24sIDIxIFNlcCAyMDI2IDA2OjU1OjQyICsw ; MDAwDQpNZXNzYWdlLUlEOiA8Y2FwYWNpdHktYUBleGFtcGxlLmludmFsaWQ+DQoNCnh4eHh4eHh4 ; eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4...`
63. **node A post beyond the capacity** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/capacity-store post --message-id '<capacity-a@example.invalid>' --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/capacity.article --group fn.letters`
64. **install stream-b.article** -- `base64 -d > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/stream-b.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IGZvciB0aGUgc3RyZWFtaW5nIG9m ; ZmVyDQpOZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBNb24sIDIxIFNlcCAyMDI2IDA2OjU1 ; OjQ0ICswMDAwDQpNZXNzYWdlLUlEOiA8c3RyZWFtLWJAZXhhbXBsZS5pbnZhbGlkPg0KDQpTZWVk ; ZWQgb24gbm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXguDQo= ; FN_GATE_EOF ; chmod 6...`
65. **node B seed <stream-b@example.invalid>** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store post --message-id '<stream-b@example.invalid>' --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/stream-b.article --group fn.letters`
66. **install statement-b.article** -- `base64 -d > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/statement-b.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IGZvciB0aGUgc3RhdGVtZW50IGV4 ; Y2hhbmdlDQpOZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBNb24sIDIxIFNlcCAyMDI2IDA2 ; OjU1OjQ3ICswMDAwDQpNZXNzYWdlLUlEOiA8c3RhdGVtZW50LWJAZXhhbXBsZS5pbnZhbGlkPg0K ; DQpTZWVkZWQgb24gbm9kZSBCIGJ5IHRoZSB2MCBtYXRyaXguDQo= ; FN_GATE_EO...`
67. **node B seed <statement-b@example.invalid>** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store post --message-id '<statement-b@example.invalid>' --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/statement-b.article --group fn.letters`
68. **node B fn init again** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn2.toml init --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store --group fn.letters --group fn.test`
69. **node B still holds <beta@b.example.invalid> after the second init** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store inspect --message-id '<beta@b.example.invalid>'`
70. **node B still holds <stream-b@example.invalid> after the second init** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store inspect --message-id '<stream-b@example.invalid>'`
71. **node B still holds <statement-b@example.invalid> after the second init** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store inspect --message-id '<statement-b@example.invalid>'`
72. **node B group create fn.matrix** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml group create fn.matrix`
73. **node B group create fn.matrix.throwaway** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml group create fn.matrix.throwaway`
74. **node B group retire fn.matrix.throwaway** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml group retire fn.matrix.throwaway`
75. **node B group retire an unserved group** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml group retire fn.not.served`
76. **node B capacity store** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/capacity-store init --group fn.letters`
77. **node B capacity 64** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/capacity-store capacity 64`
78. **node B capacity 1** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/capacity-store capacity 1`
79. **install capacity.article** -- `base64 -d > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/capacity.article <<'FN_GATE_EOF' ; RnJvbTogZ2F0ZUBleGFtcGxlLmludmFsaWQNClN1YmplY3Q6IG92ZXIgdGhlIGNhcGFjaXR5DQpO ; ZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpEYXRlOiBNb24sIDIxIFNlcCAyMDI2IDA2OjU2OjEwICsw ; MDAwDQpNZXNzYWdlLUlEOiA8Y2FwYWNpdHktYkBleGFtcGxlLmludmFsaWQ+DQoNCnh4eHh4eHh4 ; eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4...`
80. **node B post beyond the capacity** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/capacity-store post --message-id '<capacity-b@example.invalid>' --payload $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/capacity.article --group fn.letters`
81. **peer record CLI** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; if python3 tools/run_store.py --store /nonexistent peer --help >/dev/null 2>&1; then ; echo STORE-PEER ; elif [ -x bin/fn ] && python3 bin/fn peer --help >/dev/null 2>&1; then echo FN-PEER ; else echo NONE; fi`
82. **node A path-identity** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store policy set path-identity a.gate.example.invalid`
83. **node B path-identity** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store policy set path-identity b.gate.example.invalid`
84. **node A peer record for B** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store peer add b --path-identity b.gate.example.invalid --nntp 127.0.0.1:33765 --inbound-groups 'fn.*' --inbound-max-octets 32768 --outbound-groups 'fn.*' --streaming --source-address 127.0.0.1`
85. **node A lists its peers** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store peer list`
86. **node B peer record for A** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store peer add a --path-identity a.gate.example.invalid --nntp 127.0.0.1:45143 --inbound-groups 'fn.*' --inbound-max-octets 32768 --outbound-groups 'fn.*' --streaming --source-address 127.0.0.1`
87. **node B lists its peers** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store peer list`
88. **start server (node A (fn), a-main)** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; rm -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/server-a-main.log ; nohup python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml run --control $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/control.sock --max-connections 64 > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/server-a-main.log 2>&1 < /dev/null & ; echo $...`
89. **node A pid** -- `cat $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/server.pid`
90. **start server (node B (fn), b-main)** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; rm -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/server-b-main.log ; nohup python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml run --control $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/control.sock --max-connections 64 > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/server-b-main.log 2>&1 < /dev/null & ; echo $...`
91. **node B pid** -- `cat $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/server.pid`
92. **node A server is alive** -- `kill -0 1696651 2>/dev/null && echo ALIVE || echo DEAD`
93. **node A serves fn.matrix** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py presence --port 45143 --groups fn.matrix`
94. **node A server is alive** -- `kill -0 1696651 2>/dev/null && echo ALIVE || echo DEAD`
95. **node A reader surface** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>'`
96. **node A server is alive** -- `kill -0 1696651 2>/dev/null && echo ALIVE || echo DEAD`
97. **node A AUTHINFO session** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py auth --port 45143 --group fn.letters --user matrix --secret matrix-secret-8f21 --msgid '<auth-a@example.invalid>'`
98. **node A server is alive** -- `kill -0 1696651 2>/dev/null && echo ALIVE || echo DEAD`
99. **node A POST cycle** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py postcycle --port 45143 --group fn.letters --msgid '<socket-a@example.invalid>' --user matrix --secret matrix-secret-8f21`
100. **node B server is alive** -- `kill -0 1696855 2>/dev/null && echo ALIVE || echo DEAD`
101. **node B serves fn.matrix** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py presence --port 33765 --groups fn.matrix`
102. **node B server is alive** -- `kill -0 1696855 2>/dev/null && echo ALIVE || echo DEAD`
103. **node B reader surface** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py surface --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>'`
104. **node B server is alive** -- `kill -0 1696855 2>/dev/null && echo ALIVE || echo DEAD`
105. **node B AUTHINFO session** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py auth --port 33765 --group fn.letters --user matrix --secret matrix-secret-8f21 --msgid '<auth-b@example.invalid>'`
106. **node B server is alive** -- `kill -0 1696855 2>/dev/null && echo ALIVE || echo DEAD`
107. **node B POST cycle** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py postcycle --port 33765 --group fn.letters --msgid '<socket-b@example.invalid>' --user matrix --secret matrix-secret-8f21`
108. **node A server is alive** -- `kill -0 1696651 2>/dev/null && echo ALIVE || echo DEAD`
109. **node B server is alive** -- `kill -0 1696855 2>/dev/null && echo ALIVE || echo DEAD`
110. **install independent.py** -- `base64 -d > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/independent.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJBIHN0ZGxpYi1ubnRwbGliIHJlYWRlciBhZ2FpbnN0 ; IGEgbGl2ZSBmbiBub2RlLiAgTm8gZm4gbW9kdWxlIGlzIGltcG9ydGVkLAphbmQgbm8gZnJhbWlu ; ZywgZm9sZGluZyBvciByZXNwb25zZSBwYXJzaW5nIGluIHRoaXMgZmlsZSBpcyBmbidzOiBubnRw ; bGliCmRvZXMgYWxsIG9mIGl0LiAgVGhlIGZpeHR1cmUgaXMgcGFzc2VkIGluLCB...`
111. **independent nntplib client on node A** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3.12 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/independent.py --port 45143 --group fn.letters --msgid '<alpha@a.example.invalid>' --absent '<absent@example.invalid>' --user matrix --secret matrix-secret-8f21`
112. **independent nntplib client on node B** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3.12 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/independent.py --port 33765 --group fn.letters --msgid '<beta@b.example.invalid>' --absent '<absent@example.invalid>' --user matrix --secret matrix-secret-8f21`
113. **node A server is alive** -- `kill -0 1696651 2>/dev/null && echo ALIVE || echo DEAD`
114. **node B server is alive** -- `kill -0 1696855 2>/dev/null && echo ALIVE || echo DEAD`
115. **independence: node A holds its own and not B's seeds** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py presence --port 45143 --groups fn.letters,fn.test --present '<alpha@a.example.invalid>,<stream-a@example.invalid>,<statement-a@example.invalid>,<auth-a@example.invalid>,<socket-a@example.invalid>' --absent '<beta@b.example.invalid>,<stream-b@example.invalid>,<statement-b...`
116. **independence: node B holds its own and not A's seeds** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py presence --port 33765 --groups fn.letters,fn.test --present '<beta@b.example.invalid>,<stream-b@example.invalid>,<statement-b@example.invalid>,<auth-b@example.invalid>,<socket-b@example.invalid>' --absent '<alpha@a.example.invalid>,<stream-a@example.invalid>,<statement-a...`
117. **node B server is alive** -- `kill -0 1696855 2>/dev/null && echo ALIVE || echo DEAD`
118. **transit AB: offer <alpha@a.example.invalid> from A to B** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 45143 --to-port 33765 --msgid '<alpha@a.example.invalid>' --group fn.letters --loop-msgid '<loop-ab@example.invalid>' --loop-identity b.gate.example.invalid`
119. **transit AB: CHECK/TAKETHIS <stream-a@example.invalid> from A to B** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py stream --from-port 45143 --to-port 33765 --msgid '<stream-a@example.invalid>'`
120. **node A server is alive** -- `kill -0 1696651 2>/dev/null && echo ALIVE || echo DEAD`
121. **transit BA: offer <beta@b.example.invalid> from B to A** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 33765 --to-port 45143 --msgid '<beta@b.example.invalid>' --group fn.letters --loop-msgid '<loop-ba@example.invalid>' --loop-identity a.gate.example.invalid`
122. **transit BA: CHECK/TAKETHIS <stream-b@example.invalid> from B to A** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py stream --from-port 33765 --to-port 45143 --msgid '<stream-b@example.invalid>'`
123. **node A server is alive** -- `kill -0 1696651 2>/dev/null && echo ALIVE || echo DEAD`
124. **node A capability pins** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py pins --port 45143 --group fn.letters --user matrix --secret matrix-secret-8f21`
125. **node B server is alive** -- `kill -0 1696855 2>/dev/null && echo ALIVE || echo DEAD`
126. **node B capability pins** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py pins --port 33765 --group fn.letters --user matrix --secret matrix-secret-8f21`
127. **node A server is alive** -- `kill -0 1696651 2>/dev/null && echo ALIVE || echo DEAD`
128. **node B server is alive** -- `kill -0 1696855 2>/dev/null && echo ALIVE || echo DEAD`
129. **a second reader across node A's POST** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py concurrent --port 45143 --group fn.letters --msgid '<concurrent@example.invalid>' --user matrix --secret matrix-secret-8f21`
130. **node A server is alive** -- `kill -0 1696651 2>/dev/null && echo ALIVE || echo DEAD`
131. **node B server is alive** -- `kill -0 1696855 2>/dev/null && echo ALIVE || echo DEAD`
132. **node A control socket** -- `test -S $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/control.sock && echo SOCKET || echo NO-SOCKET`
133. **live reconfiguration: declare a group on node A** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/matrix.py control --socket $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/control.sock --line 'DECLARE-GROUP fn.matrix.live'`
134. **offline group create while the service holds the store** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml group create fn.matrix.offline`
135. **node A server is alive** -- `kill -0 1696651 2>/dev/null && echo ALIVE || echo DEAD`
136. **node B server is alive** -- `kill -0 1696855 2>/dev/null && echo ALIVE || echo DEAD`
137. **owner feed: A posts <fed-ab@example.invalid>** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py post --port 45143 --msgid '<fed-ab@example.invalid>' --group fn.letters`
138. **owner feed: B receives <fed-ab@example.invalid> from A's feed** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py wait --port 33765 --from-port 45143 --msgid '<fed-ab@example.invalid>' --seconds 60`
139. **owner feed: B serves <fed-ab@example.invalid> byte for byte as A does** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py wait --port 33765 --from-port 45143 --msgid '<fed-ab@example.invalid>' --seconds 60`
   - the ARTICLE block node B returns is compared line for line with the one node A returns; identical=True
140. **owner feed: A's feed offered <fed-ab@example.invalid> with IHAVE** -- `tail -n +1 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/tap.log 2>/dev/null | grep -E '^C> (IHAVE|CHECK|TAKETHIS|MODE STREAM)|^S< [0-9][0-9][0-9] ' | tail -60`
141. **owner feed: a second offer of <fed-ab@example.invalid> draws 435/438** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 45143 --to-port 33765 --msgid '<fed-ab@example.invalid>' --group fn.letters --loop-msgid '<loop@a.example.invalid>' --loop-identity b.gate.example.invalid`
142. **owner feed: B posts <fed-ba@example.invalid>** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py post --port 33765 --msgid '<fed-ba@example.invalid>' --group fn.letters`
143. **owner feed: A receives <fed-ba@example.invalid> from B's feed** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py wait --port 45143 --from-port 33765 --msgid '<fed-ba@example.invalid>' --seconds 60`
144. **owner feed: A serves <fed-ba@example.invalid> byte for byte as B does** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py wait --port 45143 --from-port 33765 --msgid '<fed-ba@example.invalid>' --seconds 60`
   - the ARTICLE block node A returns is compared line for line with the one node B returns; identical=True
145. **owner feed: B's feed offered <fed-ba@example.invalid> with IHAVE** -- `tail -n +1 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/tap.log 2>/dev/null | grep -E '^C> (IHAVE|CHECK|TAKETHIS|MODE STREAM)|^S< [0-9][0-9][0-9] ' | tail -60`
146. **owner feed: a second offer of <fed-ba@example.invalid> draws 435/438** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 33765 --to-port 45143 --msgid '<fed-ba@example.invalid>' --group fn.letters --loop-msgid '<loop@a.example.invalid>' --loop-identity a.gate.example.invalid`
147. **feed: the journal on node A** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; ls -l $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store/feed 2>/dev/null | head -8 || true`
148. **node A server is alive** -- `kill -0 1696651 2>/dev/null && echo ALIVE || echo DEAD`
149. **node B server is alive** -- `kill -0 1696855 2>/dev/null && echo ALIVE || echo DEAD`
150. **kill -9 node B mid-transit** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py cut --to-port 33765 --mode transit --group fn.letters --msgid '<interrupted@example.invalid>' --pid 1696855`
151. **node A survived node B's death** -- `kill -0 1696651 2>/dev/null && echo ALIVE || echo DEAD`
152. **node B recover after the kill** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store recover`
153. **node B status after recovery** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store status`
154. **node B still holds <beta@b.example.invalid> after recovery** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store inspect --message-id '<beta@b.example.invalid>'`
155. **node B still holds <stream-b@example.invalid> after recovery** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store inspect --message-id '<stream-b@example.invalid>'`
156. **node B still holds <statement-b@example.invalid> after recovery** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store inspect --message-id '<statement-b@example.invalid>'`
157. **node B still holds <auth-b@example.invalid> after recovery** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store inspect --message-id '<auth-b@example.invalid>'`
158. **node B still holds <socket-b@example.invalid> after recovery** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store inspect --message-id '<socket-b@example.invalid>'`
159. **node B still holds <alpha@a.example.invalid> after recovery** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store inspect --message-id '<alpha@a.example.invalid>'`
160. **node B still holds <stream-a@example.invalid> after recovery** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store inspect --message-id '<stream-a@example.invalid>'`
161. **node B still holds <fed-ab@example.invalid> after recovery** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store inspect --message-id '<fed-ab@example.invalid>'`
162. **node B still holds <fed-ba@example.invalid> after recovery** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store inspect --message-id '<fed-ba@example.invalid>'`
163. **node B does not hold the interrupted <interrupted@example.invalid>** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store inspect --message-id '<interrupted@example.invalid>'`
164. **start server (node B (fn), b-after-recovery)** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; rm -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/server-b-after-recovery.log ; nohup python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml run --control $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/control.sock --max-connections 64 > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/server-b-after-recovery.log 2>&1 < ...`
165. **node B pid** -- `cat $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/server.pid`
166. **reread node B after recovery** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py presence --port 33765 --groups fn.letters,fn.test --present '<beta@b.example.invalid>,<stream-b@example.invalid>,<statement-b@example.invalid>,<auth-b@example.invalid>,<socket-b@example.invalid>,<alpha@a.example.invalid>,<stream-a@example.invalid>,<fed-ab@example.invalid...`
167. **campaign: the cut table matches the injector** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 -c 'import sys; sys.path.insert(0, "."); from tests.campaign import cuts; cuts.verify_table(); print("TABLE OK", len(cuts.CUTS))'`
168. **campaign: run the cuts** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 -m tests.campaign.campaign --quick --json $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/campaign.json 2>&1 | tail -30`
169. **native image for the tcpcl layer** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; FN_ACL2=${FN_ACL2:-$HOME/fn-tools/acl2-8.7/saved_acl2} swarm-build sh tools/build_native_host.sh 2>&1 | tail -20`
170. **tcpcl lab** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/tcpcl_lab.py --image build/fn-host --work $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/tcpcl-lab`
171. **statement: offer the statement-bearing article from A to B** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py relay --from-port 45143 --to-port 33765 --msgid '<statement-a@example.invalid>' --group fn.letters --loop-msgid '<statement-loop@example.invalid>' --loop-identity b.gate.example.invalid`
172. **statement: node B serves the statement-bearing article** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/feed.py presence --port 33765 --groups fn.letters --present '<statement-a@example.invalid>'`
173. **install keyring** -- `base64 -d > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/keyring <<'FN_GATE_EOF' ; ODZjMzA2MDkyOTVhNGNjMDE5OGYyMGNiNTM5OTg2NWVhYWI3Y2JkODYzYmRmNDE3MTRlMjA1ZjJj ; ODAxOWEyNCA1ZjVmNWY1ZjVmNWY1ZjVmNWY1ZjVmNWY1ZjVmNWY1ZjVmNWY1ZjVmNWY1ZjVmNWY1 ; ZjVmNWY1ZjVmNWY1ZjVmCg== ; FN_GATE_EOF ; chmod 644 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/keyring`
174. **statement verify on node B's copy** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml statement verify --article $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.signed --keyring $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/keyring`
175. **statement tamper** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; sed 's/A statement carried/A statement altered/' $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.signed > $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.tampered`
176. **statement verify on the tampered copy** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 bin/fn --config $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml statement verify --article $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/statement.tampered --keyring $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/keyring`
177. **media export usage** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/media.py export --help 2>&1 | head -20`
178. **stop server node A (main)** -- `if [ -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/server.pid ; fi ; echo stopped`
179. **node A store after the stop** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store status`
180. **node A log tail** -- `tail -12 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/server-a-main.log 2>/dev/null || echo NO-LOG`
181. **stop server node B (main)** -- `if [ -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/server.pid ; fi ; echo stopped`
182. **node B store after the stop** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store status`
183. **node B log tail** -- `tail -12 $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/server-b-main.log 2>/dev/null || echo NO-LOG`
184. **checkpoint on node A** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store anchor`
185. **node A reopens after the checkpoint** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store status`
186. **peer remove a peer that is not there** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store peer remove no-such-peer`
187. **peer remove the configured peer** -- `cd $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2 || exit 9 ; python3 tools/run_store.py --store $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store peer remove b`
188. **stop server node A (main)** -- `if [ -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/server.pid ; fi ; echo stopped`
189. **stop the tap in front of node A** -- `if [ -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/tap.pid ]; then ; pid=$(cat $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/tap.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 10); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/a/tap.pid ; fi ; echo stopped`
190. **stop server node B (main)** -- `if [ -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/server.pid ]; then ; pid=$(cat $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/server.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/server.pid ; fi ; echo stopped`
191. **stop the tap in front of node B** -- `if [ -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/tap.pid ]; then ; pid=$(cat $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/tap.pid) ; kill $pid 2>/dev/null || true ; for i in $(seq 1 10); do kill -0 $pid 2>/dev/null || break; sleep 1; done ; kill -9 $pid 2>/dev/null || true ; rm -f $HOME/fn-deploy/w12-integrated-cdb-cdbd6b2/b/tap.pid ; fi ; echo stopped`
192. **stray fn processes** -- `pgrep -f 'fn-deploy/w12-integrated-cdb-cdbd6b2' >/dev/null 2>&1 && echo STRAY || echo CLEAN`
193. **release deploy lock** -- `rmdir $HOME/fn-deploy/.locks/w12-integrated-cdb-cdbd6b2.lock`

## Findings

One row per stated assertion. `held` and `violated` are the two that
DECIDE it; `inconclusive` means this run could not decide it and so
establishes nothing; `not-exercised` and `not-built` mean it was not
reached and why; `limitation` is a scope boundary no run of this
harness crosses.

The process exit is 1 for a violation, 3 for an inconclusive run with no violation, 2 when the gate stopped early, 0 otherwise.

Verdict of this run: **inconclusive** (11 held, 2 inconclusive, 3 limitation).

| assertion | verdict | what it says |
| --- | --- | --- |
| certificates-match | held | the selected native image and deployed entry-point closure was certified on this host and then loaded without ACL2 errors or uncertified warnings |
| node-a-the-injected-uncertain-publication-uncertain-a-example-invalid-is-asserte | limitation | node A: the injected uncertain publication <uncertain-a@example.invalid> is asserted in neither direction; `inspect` exited 0 for it after recovery. An indeterminate outcome is evidence about the report, not about the article. |
| node-b-the-injected-uncertain-publication-uncertain-b-example-invalid-is-asserte | limitation | node B: the injected uncertain publication <uncertain-b@example.invalid> is asserted in neither direction; `inspect` exited 0 for it after recovery. An indeterminate outcome is evidence about the report, not about the article. |
| feed-post-durable[ab] | held | the article the feed is to carry became durable on the sending node |
| feed-arrival[ab] | held | the receiving node served the article the sending node's own feed offered |
| feed-identical[ab] | held | the receiving node serves the same octets the sender does, Path and Xref aside (RFC 5537 3.6) |
| feed-offer-command[ab] | inconclusive | owner feed: the tap in front of node B recorded no `IHAVE` from node A's feed, so this run does not establish which offer command carried <fed-ab@example.invalid>. What it recorded was: nothing |
| feed-reoffer-435[ab] | held | re-offering a delivered article draws 435, which is what makes a restart-by-offer safe |
| feed-reoffer-438[ab] | held | CHECK of a delivered article draws 438 |
| feed-post-durable[ba] | held | the article the feed is to carry became durable on the sending node |
| feed-arrival[ba] | held | the receiving node served the article the sending node's own feed offered |
| feed-identical[ba] | held | the receiving node serves the same octets the sender does, Path and Xref aside (RFC 5537 3.6) |
| feed-offer-command[ba] | inconclusive | owner feed: the tap in front of node A recorded no `IHAVE` from node B's feed, so this run does not establish which offer command carried <fed-ba@example.invalid>. What it recorded was: nothing |
| feed-reoffer-435[ba] | held | re-offering a delivered article draws 435, which is what makes a restart-by-offer safe |
| feed-reoffer-438[ba] | held | CHECK of a delivered article draws 438 |
| fn-statement-verify-uses-exit-3-for-unverified-which-is-d13-s-uncertain-code-eve | limitation | `fn statement verify` uses exit 3 for `unverified`, which is D13's uncertain code everywhere else on the operator surface (docs/operator.md). The matrix reads it with the statement vocabulary and records the overload rather than hiding it. |

## What was NOT exercised

- node A: the injected uncertain publication <uncertain-a@example.invalid> is asserted in neither direction; `inspect` exited 0 for it after recovery. An indeterminate outcome is evidence about the report, not about the article.
- node B: the injected uncertain publication <uncertain-b@example.invalid> is asserted in neither direction; `inspect` exited 0 for it after recovery. An indeterminate outcome is evidence about the report, not about the article.
- owner feed: the tap in front of node B recorded no `IHAVE` from node A's feed, so this run does not establish which offer command carried <fed-ab@example.invalid>. What it recorded was: nothing
- owner feed: the tap in front of node A recorded no `IHAVE` from node B's feed, so this run does not establish which offer command carried <fed-ba@example.invalid>. What it recorded was: nothing
- `fn statement verify` uses exit 3 for `unverified`, which is D13's uncertain code everywhere else on the operator surface (docs/operator.md). The matrix reads it with the statement vocabulary and records the overload rather than hiding it.

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
--- 8 acquire certificate artifact set (rc=1)
profile=default image=build/fn-host result=no complete current artifact set passed an ACL2 load rejected=0
--- 9 certify declared artifact closure (rc=0)
ACL2 certification passed: books/cbor, books/wildmat, books/cbor-invariants, books/frame-octets, books/frame-fields, books/frame-journal, books/frame, books/frame-invariants, books/defrecord, books/clock, books/anchor, books/anchor-record, books/anchor-invariants, books/article, books/article-fields, books/acceptance-alloc, books/provenance, books/retention, books/acceptance, books/node, books/records, books/records-invariants, books/crypto-seam, books/statement, books/statement-invariants, books/lace, books/lace-invariants, books/principal, books/stx-carrier, books/stx-verify, books/stx-lace, books/stx-index, books/acceptance-invariants, books/node-invariants, books/replay, books/store-files, books/store-files-invariants, books/store-node, books/store-node-invariants, books/article-invariants, books/article-properties, books/bp-ingress, books/bp-adu, books/bp-receipt, books/bp-receipt-records, books/bp-workflow, books/bp-workflow-records, books/sha256, books/crypto-attach, books/frame-trailer, books/scheduler, books/peer-feed, books/feed-journal, books/identity, books/wire, books/nntp-syntax, books/nntp-session, books/nntp-projection, books/nntp-responses, books/nntp, books/nntp-overview, books/nntp-legacy, books/nntp-invariants, books/nntp-effects, books/config, books/config-records, books/config-invariants, books/node-config, books/path, books/peer-config, books/peer-feed-invariants, books/owner-feed, books/auth-secret, books/identity-invariants, books/records-canonicality, books/provenance-codec, books/injection, books/injection-invariants, books/nntp-post, books/peer-inbound, books/nntp-auth, books/wire-invariants, books/served, books/store-files-traces, books/store-node-traces, books/store-node-resolution, books/store-observed, books/owner, books/owner-invariants, books/owner-fault, books/store-config, books/store-observed-traces, books/store-sweep, books/tcpcl-records, books/tcpcl-octets, books/deftransition, books/tcpcl-session
Certification evidence: build/acl2/certify-20260921T065003Z-1681307
--- 10 load declared artifact closure (rc=0)
profile=default image=build/fn-host roots=24 result=loaded
--- 11 feature probe (rc=0)
fn-init=yes
fn-run=yes
fn-post=yes
fn-group=yes
fn-capacity=yes
fn-status=yes
fn-recover=yes
fn-anchor=yes
fn-principal=yes
fn-peer=yes
fn-statement=yes
reader-post=no
--- 12 free ports (rc=0)
45143 33765
--- 13 node A directories (rc=0)
--- 14 node A fn init (rc=0)
initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store
accepted init store=/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store config=/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn.toml groups=fn.letters,fn.test
--- 15 node A fn.toml (rc=0)
# fn configuration; see docs/operator.md and packaging/fn.toml.example

[store]
path = "/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store"

[listener]
# loopback only: architecture.md does not authorize a public listener
host = "127.0.0.1"
port = 45143

[posting]
enabled = true
--- 16 node A fn status (rc=0)
owner=absent generation=1 transactions=0 articles=0 staging-orphans=0 anchor=none
accepted status owner=absent
--- 17 node A store config (rc=0)
generation=1 served=fn.letters,fn.test domain=fn.letters,fn.test
--- 18 node A has a configuration (rc=0)
YES
--- 19 node B directories (rc=0)
--- 20 node B fn init (rc=0)
initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store
accepted init store=/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store config=/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn.toml groups=fn.letters,fn.test
--- 21 node B fn.toml (rc=0)
# fn configuration; see docs/operator.md and packaging/fn.toml.example

[store]
path = "/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store"

[listener]
# loopback only: architecture.md does not authorize a public listener
host = "127.0.0.1"
port = 33765

[posting]
enabled = true
--- 22 node B fn status (rc=0)
owner=absent generation=1 transactions=0 articles=0 staging-orphans=0 anchor=none
accepted status owner=absent
--- 23 node B store config (rc=0)
generation=1 served=fn.letters,fn.test domain=fn.letters,fn.test
--- 24 node B has a configuration (rc=0)
YES
--- 25 loopback refusal: init (rc=0)
initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/loopback/store
accepted init store=/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/loopback/store config=/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/loopback/fn.toml groups=fn.letters
--- 26 loopback refusal: run (rc=1)
refused run listener host '10.99.0.1' is not loopback; the owner binds 127.0.0.1 only (docs/architecture.md)
--- 27 install seed.hex (rc=0)
--- 28 principal new (rc=0)
id 86c30609295a4cc0198f20cb5399865eaab7cbd863bdf41714e205f2c8019a24
public-key 5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f
token fn
accepted principal new toy realiser (tests/acl2/crypto-seam-tests.lisp): not a cryptographic key
--- 29 node A principal set-password (rc=0)
accepted wrote /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store/auth.toml (mode 0600) with login 'matrix', principal 86c30609295a4cc0..., posting allowed.  The stored value is a salted digest (books/auth-secret); the secret itself is not in the file.  AUTHINFO still sends it in the clear, so set [auth] protected_only = true and configure TLS.
--- 30 node A principal list (rc=0)
matrix principal=86c30609295a4cc0198f20cb5399865eaab7cbd863bdf41714e205f2c8019a24 posting=true
accepted principal list registry=/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store/auth.toml count=1
--- 31 node B principal set-password (rc=0)
accepted wrote /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store/auth.toml (mode 0600) with login 'matrix', principal 86c30609295a4cc0..., posting allowed.  The stored value is a salted digest (books/auth-secret); the secret itself is not in the file.  AUTHINFO still sends it in the clear, so set [auth] protected_only = true and configure TLS.
--- 32 node B principal list (rc=0)
accepted principal list registry=/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store/auth.toml count=1
matrix principal=86c30609295a4cc0198f20cb5399865eaab7cbd863bdf41714e205f2c8019a24 posting=true
--- 33 install statement.article (rc=0)
--- 34 statement sign (rc=0)
verified statement sign creator 86c30609295a4cc0198f20cb5399865eaab7cbd863bdf41714e205f2c8019a24 ed25519 signature over the ACL2 signing preimage: 52c34bd3a360e5abeab1a17ab8a0789ec34d478e5d0ed964b1c23d4415bdaa74fdfeeaba14a3facbba062d8735e8286d2a6d5dae436a61d55c4d188ceafc6009 not attached: the deployed digest realiser is open (D09)
--- 35 statement attach (rc=0)
verified statement attach
--- 36 install seed.article (rc=0)
--- 37 node A outcome accepted (rc=0)
committed sequence=0 charge=2
--- 38 node A outcome refused (rc=1)
--- 39 node A outcome uncertain (rc=3)
store: indeterminate injected failure after final publication
--- 40 node A recover after the uncertain publication (rc=0)
recovered transactions=2 articles=2 staging-orphans=0 anchor=none checkpoint=none
--- 41 node A after recovery: the uncertain <uncertain-a@example.invalid> (rc=0)
From: gate@example.invalid
Subject: alpha, written on A
Newsgroups: fn.letters
Date: Mon, 21 Sep 2026 06:54:55 +0000
Message-ID: <alpha@a.example.invalid>

Written on node A by the v0 matrix.
--- 42 install seed.article (rc=0)
--- 43 node B outcome accepted (rc=0)
committed sequence=0 charge=2
--- 44 node B outcome refused (rc=1)
--- 45 node B outcome uncertain (rc=3)
store: indeterminate injected failure after final publication
--- 46 node B recover after the uncertain publication (rc=0)
recovered transactions=2 articles=2 staging-orphans=0 anchor=none checkpoint=none
--- 47 node B after recovery: the uncertain <uncertain-b@example.invalid> (rc=0)
From: gate@example.invalid
Subject: beta, written on B
Newsgroups: fn.letters
Date: Mon, 21 Sep 2026 06:55:04 +0000
Message-ID: <beta@b.example.invalid>

Written on node B by the v0 matrix.
--- 48 install stream-a.article (rc=0)
--- 49 node A seed <stream-a@example.invalid> (rc=0)
committed sequence=2 charge=2
--- 50 node A seed <statement-a@example.invalid> (rc=0)
committed sequence=3 charge=2
--- 51 node A fn init again (rc=0)
initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store
accepted init store=/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/store config=/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/fn2.toml groups=fn.letters,fn.test
--- 52 node A still holds <alpha@a.example.invalid> after the second init (rc=0)
From: gate@example.invalid
Subject: alpha, written on A
Newsgroups: fn.letters
Date: Mon, 21 Sep 2026 06:54:55 +0000
Message-ID: <alpha@a.example.invalid>

Written on node A by the v0 matrix.
--- 53 node A still holds <stream-a@example.invalid> after the second init (rc=0)
From: gate@example.invalid
Subject: for the streaming offer
Newsgroups: fn.letters
Date: Mon, 21 Sep 2026 06:55:15 +0000
Message-ID: <stream-a@example.invalid>

Seeded on node A by the v0 matrix.
--- 54 node A still holds <statement-a@example.invalid> after the second init (rc=0)
FN-Statement: AVgghsMGCSlaTMAZjyDLU5mGXqq3y9hjvfQXFOIF8sgBmiQAAAABWCA56HsxFwaTKnD1gu3bdDkBri5rDUFt4WN+LwX4qRoTLVggG+Ml0glvglfAVXS3HYFJYDpqXE1BE7cHzQ8OIGXLKmM=
From: gate@example.invalid
Subject: a carried statement
Newsgroups: fn.letters
Date: Mon, 21 Sep 2026 06:54:53 +0000
Message-ID: <statement-a@example.invalid>

A statement carried between two fn nodes.
--- 55 node A group create fn.matrix (rc=0)
group created name=fn.matrix generation=2
accepted group create fn.matrix
--- 56 node A group create fn.matrix.throwaway (rc=0)
group created name=fn.matrix.throwaway generation=3
accepted group create fn.matrix.throwaway
--- 57 node A group retire fn.matrix.throwaway (rc=0)
group retired name=fn.matrix.throwaway generation=4
accepted group retire fn.matrix.throwaway
--- 58 node A group retire an unserved group (rc=1)
refused group retire fn.not.served store: refused group retire: no-such-group
--- 59 node A capacity store (rc=0)
initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/capacity-store
--- 60 node A capacity 64 (rc=0)
capacity set n=64 generation=2
--- 61 node A capacity 1 (rc=0)
capacity set n=1 generation=3
--- 62 install capacity.article (rc=0)
--- 63 node A post beyond the capacity (rc=1)
store: ACL2 refused post: refused
--- 64 install stream-b.article (rc=0)
--- 65 node B seed <stream-b@example.invalid> (rc=0)
committed sequence=2 charge=2
--- 66 install statement-b.article (rc=0)
--- 67 node B seed <statement-b@example.invalid> (rc=0)
committed sequence=3 charge=2
--- 68 node B fn init again (rc=0)
initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store
accepted init store=/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/store config=/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/fn2.toml groups=fn.letters,fn.test
--- 69 node B still holds <beta@b.example.invalid> after the second init (rc=0)
From: gate@example.invalid
Subject: beta, written on B
Newsgroups: fn.letters
Date: Mon, 21 Sep 2026 06:55:04 +0000
Message-ID: <beta@b.example.invalid>

Written on node B by the v0 matrix.
--- 70 node B still holds <stream-b@example.invalid> after the second init (rc=0)
From: gate@example.invalid
Subject: for the streaming offer
Newsgroups: fn.letters
Date: Mon, 21 Sep 2026 06:55:44 +0000
Message-ID: <stream-b@example.invalid>

Seeded on node B by the v0 matrix.
--- 71 node B still holds <statement-b@example.invalid> after the second init (rc=0)
From: gate@example.invalid
Subject: for the statement exchange
Newsgroups: fn.letters
Date: Mon, 21 Sep 2026 06:55:47 +0000
Message-ID: <statement-b@example.invalid>

Seeded on node B by the v0 matrix.
--- 72 node B group create fn.matrix (rc=0)
group created name=fn.matrix generation=2
accepted group create fn.matrix
--- 73 node B group create fn.matrix.throwaway (rc=0)
group created name=fn.matrix.throwaway generation=3
accepted group create fn.matrix.throwaway
--- 74 node B group retire fn.matrix.throwaway (rc=0)
group retired name=fn.matrix.throwaway generation=4
accepted group retire fn.matrix.throwaway
--- 75 node B group retire an unserved group (rc=1)
refused group retire fn.not.served store: refused group retire: no-such-group
--- 76 node B capacity store (rc=0)
initialized /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/capacity-store
--- 77 node B capacity 64 (rc=0)
capacity set n=64 generation=2
--- 78 node B capacity 1 (rc=0)
capacity set n=1 generation=3
--- 79 install capacity.article (rc=0)
--- 80 node B post beyond the capacity (rc=1)
store: ACL2 refused post: refused
--- 81 peer record CLI (rc=0)
STORE-PEER
--- 82 node A path-identity (rc=0)
policy set path-identity=a.gate.example.invalid generation=5
--- 83 node B path-identity (rc=0)
policy set path-identity=b.gate.example.invalid generation=5
--- 84 node A peer record for B (rc=0)
peer added name=b generation=6
--- 85 node A lists its peers (rc=0)
name=b path-identity=b.gate.example.invalid transport=127.0.0.1:33765 inbound=fn.* max-octets=32768 max-inflight=16 outbound=fn.* max-queue=1024 streaming=yes backoff-ms=1000 auth=source-address:127.0.0.1
--- 86 node B peer record for A (rc=0)
peer added name=a generation=6
--- 87 node B lists its peers (rc=0)
name=a path-identity=a.gate.example.invalid transport=127.0.0.1:45143 inbound=fn.* max-octets=32768 max-inflight=16 outbound=fn.* max-queue=1024 streaming=yes backoff-ms=1000 auth=source-address:127.0.0.1
--- 88 start server (node A (fn), a-main) (rc=0)
LISTENING 45143
--- 89 node A pid (rc=0)
1696651
--- 90 start server (node B (fn), b-main) (rc=0)
LISTENING 33765
--- 91 node B pid (rc=0)
1696855
--- 92 node A server is alive (rc=0)
ALIVE
--- 93 node A serves fn.matrix (rc=0)
{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}
--- 94 node A server is alive (rc=0)
ALIVE
--- 95 node A reader surface (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "MODE READER": "200 posting allowed", "LIST ACTIVE": "215 list of active newsgroups follows", "LIST NEWSGROUPS": "215 list of newsgroups follows", "LIST OVERVIEW.FMT": "215 order of fields in overview database", "LIST ACTIVE.TIMES": "215 information follows", "LIST HEADERS": "215 field list follows", "GROUP": "211 4 1 4 fn.letters", "group_count": 4, "group_first": 1, "group_last": 4, "LISTGROUP": "211 4 1 4 fn.letters list follows", "ARTICLE": "220 1 <alpha@a.example.invalid> article follows", "HEAD": "221 1 <alpha@a.example.invalid> headers follow", "BODY": "222 1 <alpha@a.example.invalid> body follows", "STAT": "223 1 <alpha@a.example.invalid> retrieved", "ARTICLE MSGID": "220 0 <alpha@a.example.invalid> article follows", "ARTICLE ABSENT": "430 no article with that message-id", "OVER": "224 overview information follows", "OVER RANGE": "224 overview information follows", "HDR": "225 headers follow", "XOVER": "224 overview information follows", "XHDR": "221 header follows", "XPAT": "221 header follows", "NEXT": "223 2 <uncertain-a@example.invalid> retrieved", "LAST": "223 1 <alpha@a.example.invalid> retrieved", "DATE": "111 20260921065631", "HELP": "100 help text follows", "UNKNOWN": "500 command not recognized", "FRAMING": "111 20260921065631", "FRAMING SAME": true, "ok": true}
--- 96 node A server is alive (rc=0)
ALIVE
--- 97 node A AUTHINFO session (rc=0)
{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "POST", "OVER", "HDR", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BEFORE": "340 send article to be posted", "AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "CAPABILITIES AFTER": "101 capability list follows", "advertised_after": ["VERSION", "READER", "POST", "OVER", "HDR", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING"], "AUTHINFO WITHDRAWN": true, "POST AFTER": "340 send article to be posted", "POST AFTER COMMIT": "240 article received OK", "AUTHINFO WRONG": "481 authentication failed", "ok": true}
--- 98 node A server is alive (rc=0)
ALIVE
--- 99 node A POST cycle (rc=0)
{"AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "GROUP BEFORE": "211 5 1 5 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 6 1 6 fn.letters", "FRESH ARTICLE": "220 0 <socket-a@example.invalid> article follows", "DUPLICATE POST": "340 send article to be posted", "DUPLICATE": "441 posting failed; the article was refused", "DATE AFTER DUPLICATE": "111 20260921065633", "counted": true, "ok": true}
--- 100 node B server is alive (rc=0)
ALIVE
--- 101 node B serves fn.matrix (rc=0)
{"groups": {"fn.matrix": "211 0 1 0 fn.matrix"}, "present": {}, "absent": {}, "ok": true}
--- 102 node B server is alive (rc=0)
ALIVE
--- 103 node B reader surface (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "CAPABILITIES": "101 capability list follows", "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "MODE READER": "200 posting allowed", "LIST ACTIVE": "215 list of active newsgroups follows", "LIST NEWSGROUPS": "215 list of newsgroups follows", "LIST OVERVIEW.FMT": "215 order of fields in overview database", "LIST ACTIVE.TIMES": "215 information follows", "LIST HEADERS": "215 field list follows", "GROUP": "211 6 1 6 fn.letters", "group_count": 6, "group_first": 1, "group_last": 6, "LISTGROUP": "211 6 1 6 fn.letters list follows", "ARTICLE": "220 1 <beta@b.example.invalid> article follows", "HEAD": "221 1 <beta@b.example.invalid> headers follow", "BODY": "222 1 <beta@b.example.invalid> body follows", "STAT": "223 1 <beta@b.example.invalid> retrieved", "ARTICLE MSGID": "220 0 <beta@b.example.invalid> article follows", "ARTICLE ABSENT": "430 no article with that message-id", "OVER": "224 overview information follows", "OVER RANGE": "224 overview information follows", "HDR": "225 headers follow", "XOVER": "224 overview information follows", "XHDR": "221 header follows", "XPAT": "221 header follows", "NEXT": "223 2 <uncertain-b@example.invalid> retrieved", "LAST": "223 1 <beta@b.example.invalid> retrieved", "DATE": "111 20260921065634", "HELP": "100 help text follows", "UNKNOWN": "500 command not recognized", "FRAMING": "111 20260921065634", "FRAMING SAME": true, "ok": true}
--- 104 node B server is alive (rc=0)
ALIVE
--- 105 node B AUTHINFO session (rc=0)
{"CAPABILITIES BEFORE": "101 capability list follows", "advertised_before": ["VERSION", "READER", "POST", "OVER", "HDR", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING", "AUTHINFO"], "AUTHINFO ADVERTISED": true, "POST BEFORE": "340 send article to be posted", "AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "CAPABILITIES AFTER": "101 capability list follows", "advertised_after": ["VERSION", "READER", "POST", "OVER", "HDR", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING"], "AUTHINFO WITHDRAWN": true, "POST AFTER": "340 send article to be posted", "POST AFTER COMMIT": "240 article received OK", "AUTHINFO WRONG": "481 authentication failed", "ok": true}
--- 106 node B server is alive (rc=0)
ALIVE
--- 107 node B POST cycle (rc=0)
{"AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "GROUP BEFORE": "211 7 1 7 fn.letters", "POST": "340 send article to be posted", "COMMIT": "240 article received OK", "GROUP AFTER": "211 8 1 8 fn.letters", "FRESH ARTICLE": "220 0 <socket-b@example.invalid> article follows", "DUPLICATE POST": "340 send article to be posted", "DUPLICATE": "441 posting failed; the article was refused", "DATE AFTER DUPLICATE": "111 20260921065635", "counted": true, "ok": true}
--- 108 node A server is alive (rc=0)
ALIVE
--- 109 node B server is alive (rc=0)
ALIVE
--- 110 install independent.py (rc=0)
--- 111 independent nntplib client on node A (rc=0)
/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/independent.py:6: DeprecationWarning: 'nntplib' is deprecated and slated for removal in Python 3.13
  import argparse, json, nntplib, platform, sys
{"absent": "430 no article with that message-id", "article_has_msgid": true, "article_lines": 7, "authinfo_advertised": true, "body_lines": 1, "capabilities": ["AUTHINFO", "HDR", "IHAVE", "IMPLEMENTATION", "LIST", "OVER", "POST", "READER", "STREAMING", "VERSION"], "capabilities_after_login": ["HDR", "IHAVE", "IMPLEMENTATION", "LIST", "OVER", "POST", "READER", "STREAMING", "VERSION"], "client": "stdlib nntplib", "commands": ["CAPABILITIES", "AUTHINFO USER/PASS", "GROUP", "STAT", "ARTICLE", "HEAD", "BODY", "OVER", "LIST", "ARTICLE (absent)", "QUIT"], "group": {"count": 8, "first": 1, "last": 8, "name": "fn.letters"}, "head_lines": 5, "list_groups": ["fn.letters", "fn.matrix", "fn.matrix.throwaway", "fn.test"], "login": "accepted", "ok": true, "over_rows": 8, "python": "3.12.7", "quit": "205 closing connection", "stat": [1, "<alpha@a.example.invalid>"], "welcome": "200 fn-nntp experimental server ready"}
--- 112 independent nntplib client on node B (rc=0)
/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/gate-run/independent.py:6: DeprecationWarning: 'nntplib' is deprecated and slated for removal in Python 3.13
  import argparse, json, nntplib, platform, sys
{"absent": "430 no article with that message-id", "article_has_msgid": true, "article_lines": 7, "authinfo_advertised": true, "body_lines": 1, "capabilities": ["AUTHINFO", "HDR", "IHAVE", "IMPLEMENTATION", "LIST", "OVER", "POST", "READER", "STREAMING", "VERSION"], "capabilities_after_login": ["HDR", "IHAVE", "IMPLEMENTATION", "LIST", "OVER", "POST", "READER", "STREAMING", "VERSION"], "client": "stdlib nntplib", "commands": ["CAPABILITIES", "AUTHINFO USER/PASS", "GROUP", "STAT", "ARTICLE", "HEAD", "BODY", "OVER", "LIST", "ARTICLE (absent)", "QUIT"], "group": {"count": 8, "first": 1, "last": 8, "name": "fn.letters"}, "head_lines": 5, "list_groups": ["fn.letters", "fn.matrix", "fn.matrix.throwaway", "fn.test"], "login": "accepted", "ok": true, "over_rows": 8, "python": "3.12.7", "quit": "205 closing connection", "stat": [1, "<beta@b.example.invalid>"], "welcome": "200 fn-nntp experimental server ready"}
--- 113 node A server is alive (rc=0)
ALIVE
--- 114 node B server is alive (rc=0)
ALIVE
--- 115 independence: node A holds its own and not B's seeds (rc=0)
{"groups": {"fn.letters": "211 8 1 8 fn.letters", "fn.test": "211 0 1 0 fn.test"}, "present": {"<alpha@a.example.invalid>": "220 0 <alpha@a.example.invalid> article follows", "<stream-a@example.invalid>": "220 0 <stream-a@example.invalid> article follows", "<statement-a@example.invalid>": "220 0 <statement-a@example.invalid> article follows", "<auth-a@example.invalid>": "220 0 <auth-a@example.invalid> article follows", "<socket-a@example.invalid>": "220 0 <socket-a@example.invalid> article follows"}, "absent": {"<beta@b.example.invalid>": "430 no article with that message-id", "<stream-b@example.invalid>": "430 no article with that message-id", "<statement-b@example.invalid>": "430 no article with that message-id"}, "ok": true}
--- 116 independence: node B holds its own and not A's seeds (rc=0)
{"groups": {"fn.letters": "211 8 1 8 fn.letters", "fn.test": "211 0 1 0 fn.test"}, "present": {"<beta@b.example.invalid>": "220 0 <beta@b.example.invalid> article follows", "<stream-b@example.invalid>": "220 0 <stream-b@example.invalid> article follows", "<statement-b@example.invalid>": "220 0 <statement-b@example.invalid> article follows", "<auth-b@example.invalid>": "220 0 <auth-b@example.invalid> article follows", "<socket-b@example.invalid>": "220 0 <socket-b@example.invalid> article follows"}, "absent": {"<alpha@a.example.invalid>": "430 no article with that message-id", "<stream-a@example.invalid>": "430 no article with that message-id", "<statement-a@example.invalid>": "430 no article with that message-id"}, "ok": true}
--- 117 node B server is alive (rc=0)
ALIVE
--- 118 transit AB: offer <alpha@a.example.invalid> from A to B (rc=0)
{"msgid": "<alpha@a.example.invalid>", "source": "220 0 <alpha@a.example.invalid> article follows", "source_lines": 7, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "ihave_advertised": true, "streaming_advertised": true, "mode_stream": "203 streaming permitted", "offer": "335 send it; end with <CR-LF>.<CR-LF>", "transit": true, "transfer": "235 article transferred OK", "duplicate": "435 duplicate", "loop_offer": "335 send it; end with <CR-LF>.<CR-LF>", "loop_result": "437 transfer rejected; path loop", "check_duplicate": "438 <alpha@a.example.invalid>", "takethis_duplicate": "439 <alpha@a.example.invalid>", "check_fresh": "238 <fresh.check@gate.example.invalid>", "reread": "220 0 <alpha@a.example.invalid> article follows", "identical": true, "loop_absent": "430 no article with that message-id", "streaming_ok": true, "ok": true}
--- 119 transit AB: CHECK/TAKETHIS <stream-a@example.invalid> from A to B (rc=0)
{"SOURCE": "220 0 <stream-a@example.invalid> article follows", "MODE STREAM": "203 streaming permitted", "CHECK": "238 <stream-a@example.invalid>", "TAKETHIS": "239 <stream-a@example.invalid>", "CHECK AGAIN": "438 <stream-a@example.invalid>", "TAKETHIS AGAIN": "439 <stream-a@example.invalid>", "REREAD": "220 0 <stream-a@example.invalid> article follows", "IDENTICAL": true, "ok": true}
--- 120 node A server is alive (rc=0)
ALIVE
--- 121 transit BA: offer <beta@b.example.invalid> from B to A (rc=0)
{"msgid": "<beta@b.example.invalid>", "source": "220 0 <beta@b.example.invalid> article follows", "source_lines": 7, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "ihave_advertised": true, "streaming_advertised": true, "mode_stream": "203 streaming permitted", "offer": "335 send it; end with <CR-LF>.<CR-LF>", "transit": true, "transfer": "235 article transferred OK", "duplicate": "435 duplicate", "loop_offer": "335 send it; end with <CR-LF>.<CR-LF>", "loop_result": "437 transfer rejected; path loop", "check_duplicate": "438 <beta@b.example.invalid>", "takethis_duplicate": "439 <beta@b.example.invalid>", "check_fresh": "238 <fresh.check@gate.example.invalid>", "reread": "220 0 <beta@b.example.invalid> article follows", "identical": true, "loop_absent": "430 no article with that message-id", "streaming_ok": true, "ok": true}
--- 122 transit BA: CHECK/TAKETHIS <stream-b@example.invalid> from B to A (rc=0)
{"SOURCE": "220 0 <stream-b@example.invalid> article follows", "MODE STREAM": "203 streaming permitted", "CHECK": "238 <stream-b@example.invalid>", "TAKETHIS": "239 <stream-b@example.invalid>", "CHECK AGAIN": "438 <stream-b@example.invalid>", "TAKETHIS AGAIN": "439 <stream-b@example.invalid>", "REREAD": "220 0 <stream-b@example.invalid> article follows", "IDENTICAL": true, "ok": true}
--- 123 node A server is alive (rc=0)
ALIVE
--- 124 node A capability pins (rc=0)
{"advertised": ["VERSION", "READER", "POST", "OVER", "HDR", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING"], "answered": {"READER": "211 10 1 10 fn.letters", "POST": "340 send article to be posted", "POST CLOSE": "441 posting failed; the article is not valid syntax", "IHAVE": "335 send it; end with <CR-LF>.<CR-LF>", "IHAVE CLOSE": "437 transfer rejected; not a valid article", "STREAMING": "203 streaming permitted", "OVER": "412 no newsgroup selected", "HDR": "412 no newsgroup selected", "LIST": "215 list of active newsgroups follows", "NEWNEWS": "500 command not recognized", "AUTHINFO": "381 password required", "STARTTLS": "580 can not initiate TLS negotiation", "MODE-READER": "200 posting allowed", "XOVER": "412 no newsgroup selected", "XHDR": "412 no newsgroup selected", "XPAT": "412 no newsgroup selected", "LISTGROUP": "211 10 1 10 fn.letters list follows", "CHECK": "238 <pin.check@matrix.example.invalid>", "TAKETHIS": "TimeoutError: timed out"}, "dispatched": ["READER", "POST", "IHAVE", "STREAMING", "OVER", "HDR", "LIST", "AUTHINFO", "STARTTLS", "MODE-READER", "XOVER", "XHDR", "XPAT", "LISTGROUP", "CHECK"], "login": {"AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted"}, "advertised_not_dispatched": [], "dispatched_not_advertised": [], "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING"], "ok": true}
--- 125 node B server is alive (rc=0)
ALIVE
--- 126 node B capability pins (rc=0)
{"advertised": ["VERSION", "READER", "POST", "OVER", "HDR", "LIST", "IMPLEMENTATION", "IHAVE", "STREAMING"], "answered": {"READER": "211 10 1 10 fn.letters", "POST": "340 send article to be posted", "POST CLOSE": "441 posting failed; the article is not valid syntax", "IHAVE": "335 send it; end with <CR-LF>.<CR-LF>", "IHAVE CLOSE": "437 transfer rejected; not a valid article", "STREAMING": "203 streaming permitted", "OVER": "412 no newsgroup selected", "HDR": "412 no newsgroup selected", "LIST": "215 list of active newsgroups follows", "NEWNEWS": "500 command not recognized", "AUTHINFO": "381 password required", "STARTTLS": "580 can not initiate TLS negotiation", "MODE-READER": "200 posting allowed", "XOVER": "412 no newsgroup selected", "XHDR": "412 no newsgroup selected", "XPAT": "412 no newsgroup selected", "LISTGROUP": "211 10 1 10 fn.letters list follows", "CHECK": "238 <pin.check@matrix.example.invalid>", "TAKETHIS": "TimeoutError: timed out"}, "dispatched": ["READER", "POST", "IHAVE", "STREAMING", "OVER", "HDR", "LIST", "AUTHINFO", "STARTTLS", "MODE-READER", "XOVER", "XHDR", "XPAT", "LISTGROUP", "CHECK"], "login": {"AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted"}, "advertised_not_dispatched": [], "dispatched_not_advertised": [], "capability_lines": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING"], "ok": true}
--- 127 node A server is alive (rc=0)
ALIVE
--- 128 node B server is alive (rc=0)
ALIVE
--- 129 a second reader across node A's POST (rc=0)
{"WATCHER BEFORE": "211 10 1 10 fn.letters", "AUTHINFO USER": "381 password required", "AUTHINFO PASS": "281 authentication accepted", "POST": "340 send article to be posted", "WATCHER MID": "211 10 1 10 fn.letters", "WATCHER ARTICLE MID": "223 1 <alpha@a.example.invalid> retrieved", "COMMIT": "240 article received OK", "WATCHER AFTER": "211 10 1 10 fn.letters", "ok": true}
--- 130 node A server is alive (rc=0)
ALIVE
--- 131 node B server is alive (rc=0)
ALIVE
--- 132 node A control socket (rc=0)
SOCKET
--- 133 live reconfiguration: declare a group on node A (rc=0)
{"line": "DECLARE-GROUP fn.matrix.live", "reply": "declared", "ok": true}
--- 134 offline group create while the service holds the store (rc=1)
refused group create fn.matrix.offline an owner is live on /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/control.sock; a configuration record needs the writer lock, so stop the service first
--- 135 node A server is alive (rc=0)
ALIVE
--- 136 node B server is alive (rc=0)
ALIVE
--- 137 owner feed: A posts <fed-ab@example.invalid> (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "post": "340 send article to be posted", "result": "240 article received OK", "ok": true}
--- 138 owner feed: B receives <fed-ab@example.invalid> from A's feed (rc=0)
{"msgid": "<fed-ab@example.invalid>", "seconds": 60.0, "ok": true, "status": "220 0 <fed-ab@example.invalid> article follows", "attempts": 1, "lines": 11, "source": "220 0 <fed-ab@example.invalid> article follows", "source_lines": 11, "target_lines": 11, "identical": true}
--- 139 owner feed: B serves <fed-ab@example.invalid> byte for byte as A does (rc=0)
{"msgid": "<fed-ab@example.invalid>", "seconds": 60.0, "ok": true, "status": "220 0 <fed-ab@example.invalid> article follows", "attempts": 1, "lines": 11, "source": "220 0 <fed-ab@example.invalid> article follows", "source_lines": 11, "target_lines": 11, "identical": true}
--- 140 owner feed: A's feed offered <fed-ab@example.invalid> with IHAVE (rc=1)
--- 141 owner feed: a second offer of <fed-ab@example.invalid> draws 435/438 (rc=1)
{"msgid": "<fed-ab@example.invalid>", "source": "220 0 <fed-ab@example.invalid> article follows", "source_lines": 11, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "ihave_advertised": true, "streaming_advertised": true, "mode_stream": "203 streaming permitted", "offer": "435 duplicate", "transit": true, "transfer": "(nothing sent: the offer drew 435 duplicate)", "duplicate": "435 duplicate", "loop_offer": "335 send it; end with <CR-LF>.<CR-LF>", "loop_result": "437 transfer rejected; path loop", "check_duplicate": "438 <fed-ab@example.invalid>", "takethis_duplicate": "439 <fed-ab@example.invalid>", "check_fresh": "238 <fresh.check@gate.example.invalid>", "reread": "220 0 <fed-ab@example.invalid> article follows", "identical": true, "loop_absent": "430 no article with that message-id", "streaming_ok": true, "ok": false}
--- 142 owner feed: B posts <fed-ba@example.invalid> (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "post": "340 send article to be posted", "result": "240 article received OK", "ok": true}
--- 143 owner feed: A receives <fed-ba@example.invalid> from B's feed (rc=0)
{"msgid": "<fed-ba@example.invalid>", "seconds": 60.0, "ok": true, "status": "220 0 <fed-ba@example.invalid> article follows", "attempts": 1, "lines": 11, "source": "220 0 <fed-ba@example.invalid> article follows", "source_lines": 11, "target_lines": 11, "identical": true}
--- 144 owner feed: A serves <fed-ba@example.invalid> byte for byte as B does (rc=0)
{"msgid": "<fed-ba@example.invalid>", "seconds": 60.0, "ok": true, "status": "220 0 <fed-ba@example.invalid> article follows", "attempts": 1, "lines": 11, "source": "220 0 <fed-ba@example.invalid> article follows", "source_lines": 11, "target_lines": 11, "identical": true}
--- 145 owner feed: B's feed offered <fed-ba@example.invalid> with IHAVE (rc=1)
--- 146 owner feed: a second offer of <fed-ba@example.invalid> draws 435/438 (rc=1)
{"msgid": "<fed-ba@example.invalid>", "source": "220 0 <fed-ba@example.invalid> article follows", "source_lines": 11, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "ihave_advertised": true, "streaming_advertised": true, "mode_stream": "203 streaming permitted", "offer": "435 duplicate", "transit": true, "transfer": "(nothing sent: the offer drew 435 duplicate)", "duplicate": "435 duplicate", "loop_offer": "335 send it; end with <CR-LF>.<CR-LF>", "loop_result": "437 transfer rejected; path loop", "check_duplicate": "438 <fed-ba@example.invalid>", "takethis_duplicate": "439 <fed-ba@example.invalid>", "check_fresh": "238 <fresh.check@gate.example.invalid>", "reread": "220 0 <fed-ba@example.invalid> article follows", "identical": true, "loop_absent": "430 no article with that message-id", "streaming_ok": true, "ok": false}
--- 147 feed: the journal on node A (rc=0)
total 4
-rw------- 1 hbox hbox 1465 Sep 21 03:04 b.fnfd
--- 148 node A server is alive (rc=0)
ALIVE
--- 149 node B server is alive (rc=0)
ALIVE
--- 150 kill -9 node B mid-transit (rc=0)
{"mode": "transit", "open": "335 send it; end with <CR-LF>.<CR-LF>", "opened": true, "killed_pid": 1696855, "after_kill": "ConnectionResetError: [Errno 104] Connection reset by peer", "ok": true}
--- 151 node A survived node B's death (rc=0)
ALIVE
--- 152 node B recover after the kill (rc=0)
recovered transactions=13 articles=13 staging-orphans=0 anchor=none checkpoint=none
--- 153 node B status after recovery (rc=0)
transactions=13 articles=13 staging-orphans=0 unsigned-legacy-experiment
--- 154 node B still holds <beta@b.example.invalid> after recovery (rc=0)
From: gate@example.invalid
Subject: beta, written on B
Newsgroups: fn.letters
Date: Mon, 21 Sep 2026 06:55:04 +0000
Message-ID: <beta@b.example.invalid>

Written on node B by the v0 matrix.
--- 155 node B still holds <stream-b@example.invalid> after recovery (rc=0)
From: gate@example.invalid
Subject: for the streaming offer
Newsgroups: fn.letters
Date: Mon, 21 Sep 2026 06:55:44 +0000
Message-ID: <stream-b@example.invalid>

Seeded on node B by the v0 matrix.
--- 156 node B still holds <statement-b@example.invalid> after recovery (rc=0)
From: gate@example.invalid
Subject: for the statement exchange
Newsgroups: fn.letters
Date: Mon, 21 Sep 2026 06:55:47 +0000
Message-ID: <statement-b@example.invalid>

Seeded on node B by the v0 matrix.
--- 157 node B still holds <auth-b@example.invalid> after recovery (rc=0)
Path: b.gate.example.invalid!not-for-mail
Injection-Date: Mon, 21 Sep 2026 06:56:34 +0000
Injection-Info: b.gate.example.invalid
Date: Mon, 21 Sep 2026 06:56:34 +0000
From: matrix@example.invalid
Subject: authenticated post
Newsgroups: fn.letters
Message-ID: <auth-b@example.invalid>

Posted after an AUTHINFO login.
--- 158 node B still holds <socket-b@example.invalid> after recovery (rc=0)
Path: b.gate.example.invalid!not-for-mail
Injection-Date: Mon, 21 Sep 2026 06:56:35 +0000
Injection-Info: b.gate.example.invalid
Date: Mon, 21 Sep 2026 06:56:35 +0000
From: matrix@example.invalid
Subject: matrix post
Newsgroups: fn.letters
Message-ID: <socket-b@example.invalid>

Posted by tools/v0_matrix.py.
--- 159 node B still holds <alpha@a.example.invalid> after recovery (rc=0)
From: gate@example.invalid
Subject: alpha, written on A
Newsgroups: fn.letters
Date: Mon, 21 Sep 2026 06:54:55 +0000
Message-ID: <alpha@a.example.invalid>

Written on node A by the v0 matrix.
--- 160 node B still holds <stream-a@example.invalid> after recovery (rc=0)
From: gate@example.invalid
Subject: for the streaming offer
Newsgroups: fn.letters
Date: Mon, 21 Sep 2026 06:55:15 +0000
Message-ID: <stream-a@example.invalid>

Seeded on node A by the v0 matrix.
--- 161 node B still holds <fed-ab@example.invalid> after recovery (rc=0)
Path: a.gate.example.invalid!not-for-mail
Injection-Date: Mon, 21 Sep 2026 07:04:44 +0000
Injection-Info: a.gate.example.invalid
From: gate@example.invalid
Subject: owner-feed
Newsgroups: fn.letters
Date: Mon, 21 Sep 2026 07:04:44 +0000
Message-ID: <fed-ab@example.invalid>

Posted through the server.

--- 162 node B still holds <fed-ba@example.invalid> after recovery (rc=0)
Path: b.gate.example.invalid!not-for-mail
Injection-Date: Mon, 21 Sep 2026 07:04:46 +0000
Injection-Info: b.gate.example.invalid
From: gate@example.invalid
Subject: owner-feed
Newsgroups: fn.letters
Date: Mon, 21 Sep 2026 07:04:46 +0000
Message-ID: <fed-ba@example.invalid>

Posted through the server.

--- 163 node B does not hold the interrupted <interrupted@example.invalid> (rc=1)
--- 164 start server (node B (fn), b-after-recovery) (rc=0)
LISTENING 33765
--- 165 node B pid (rc=0)
1718666
--- 166 reread node B after recovery (rc=0)
{"groups": {"fn.letters": "211 13 1 13 fn.letters", "fn.test": "211 0 1 0 fn.test"}, "present": {"<beta@b.example.invalid>": "220 0 <beta@b.example.invalid> article follows", "<stream-b@example.invalid>": "220 0 <stream-b@example.invalid> article follows", "<statement-b@example.invalid>": "220 0 <statement-b@example.invalid> article follows", "<auth-b@example.invalid>": "220 0 <auth-b@example.invalid> article follows", "<socket-b@example.invalid>": "220 0 <socket-b@example.invalid> article follows", "<alpha@a.example.invalid>": "220 0 <alpha@a.example.invalid> article follows", "<stream-a@example.invalid>": "220 0 <stream-a@example.invalid> article follows", "<fed-ab@example.invalid>": "220 0 <fed-ab@example.invalid> article follows", "<fed-ba@example.invalid>": "220 0 <fed-ba@example.invalid> article follows"}, "absent": {"<loop-ab@example.invalid>": "430 no article with that message-id", "<interrupted@example.invalid>": "430 no article with that message-id"}, "ok": true}
--- 167 campaign: the cut table matches the injector (rc=0)
TABLE OK 54
--- 168 campaign: run the cuts (rc=0)
committed sequence=1 charge=2
duplicate
cross-post       store:recover-barrier                 7.1s ok
template bp-receive built in 3.9s
reference bp-receive: accepted StoreState(records=2, articles=2, pins=2, baseline_present=True, campaign_present=True, replay='recovering')
bp-receive       workflow:inbound-staged-durable      13.6s ok
bp-receive       receipt:receipt-staged-durable        7.6s ok
bp-receive       receipt:postlink                      7.6s ok
bp-receive       receive:staged                        6.7s ok
bp-receive       receive:store-published               7.7s ok
bp-receive       receive:receipt-intent                8.6s ok
bp-receive       receive:bpa-deleted                   7.7s ok
--- 169 native image for the tcpcl layer (rc=0)
built build/fn-host (260M core)
--- 170 tcpcl lab (rc=1)
{"a_holds_b_bundle": true, "acks_from_a": 2, "acks_from_b": 2, "active_events": 8, "active_outcomes": [["accepted", "xfer=0 path=/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/tcpcl-lab/exchange/active-spool/active-0.bundle"], ["accepted", "outbound xfer=0"]], "b_holds_a_bundle": true, "contact": 1, "listener_rc": 0, "ok": true, "passive_events": 10, "passive_outcomes": [["accepted", "xfer=0 path=/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/tcpcl-lab/exchange/passive-spool/passive-0.bundle"], ["accepted", "outbound xfer=0"]], "scenario": "exchange", "segments_to_a": 2, "segments_to_b": 2, "sender_rc": 0, "sess_init": 1, "sess_term": 1, "trace_bytes": 1683}
{"ok": true, "outcomes": [["refused", "outbound reason=exceeds-transfer-mtu"]], "scenario": "refused", "segments": 0, "sender_rc": 1, "staged": []}
{"active_keepalives": 3, "active_terms": 0, "ok": true, "passive_keepalives": 3, "passive_terms": 0, "scenario": "keepalive", "still_up": true}
{"acks_before_kill": 118, "durable_after": true, "durable_before": true, "first_rc": 0, "interrupted_absent": false, "no_partials": false, "ok": false, "reconnect_rc": 0, "scenario": "crash", "staged": [".incoming-1728016-dda1835cc3233affa2496ddb", "passive-0.bundle"]}
{"large": {"intact": true, "rc": 0}, "large_octets": 262144, "large_seconds": 0.132, "ok": true, "ratio": 1.51, "scenario": "profile", "size_ratio": 4, "small": {"intact": true, "rc": 0}, "small_octets": 65536, "small_seconds": 0.088}
Traceback (most recent call last):
  File "/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/tools/tcpcl_lab.py", line 590, in <module>
    sys.exit(main())
             ^^^^^^
  File "/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/tools/tcpcl_lab.py", line 586, in main
    return Lab(str(image), args.work).run(args.scenario)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
--- 171 statement: offer the statement-bearing article from A to B (rc=0)
{"msgid": "<statement-a@example.invalid>", "source": "220 0 <statement-a@example.invalid> article follows", "source_lines": 8, "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING", "AUTHINFO USER"], "ihave_advertised": true, "streaming_advertised": true, "mode_stream": "203 streaming permitted", "offer": "335 send it; end with <CR-LF>.<CR-LF>", "transit": true, "transfer": "235 article transferred OK", "duplicate": "435 duplicate", "loop_offer": "335 send it; end with <CR-LF>.<CR-LF>", "loop_result": "437 transfer rejected; path loop", "check_duplicate": "438 <statement-a@example.invalid>", "takethis_duplicate": "439 <statement-a@example.invalid>", "check_fresh": "238 <fresh.check@gate.example.invalid>", "reread": "220 0 <statement-a@example.invalid> article follows", "identical": true, "loop_absent": "430 no article with that message-id", "streaming_ok": true, "ok": true}
--- 172 statement: node B serves the statement-bearing article (rc=0)
{"groups": {"fn.letters": "211 14 1 14 fn.letters"}, "present": {"<statement-a@example.invalid>": "220 0 <statement-a@example.invalid> article follows"}, "absent": {}, "ok": true}
--- 173 install keyring (rc=0)
--- 174 statement verify on node B's copy (rc=0)
verified 86c30609295a4cc0198f20cb5399865eaab7cbd863bdf41714e205f2c8019a24 keyring 0
(toy crypto realiser; not a cryptographic verdict)
verified statement verify
--- 175 statement tamper (rc=0)
--- 176 statement verify on the tampered copy (rc=3)
unverified statement verify
unverified ref-mismatch keyring 0
(toy crypto realiser; not a cryptographic verdict)
--- 177 media export usage (rc=0)
usage: media export [-h] --media MEDIA --media-id MEDIA_ID [--bundle ID=PATH]
                    [--bp-bundle ID=PATH]

options:
  -h, --help           show this help message and exit
  --media MEDIA        volume root; must not exist
  --media-id MEDIA_ID
  --bundle ID=PATH     one projected request ADU
  --bp-bundle ID=PATH  the BPv7 bundle octets carrying that ADU; ACL2 reads
                       the carried identity and expiry from them
--- 178 stop server node A (main) (rc=0)
stopped
--- 179 node A store after the stop (rc=0)
transactions=13 articles=13 staging-orphans=0 unsigned-legacy-experiment
--- 180 node A log tail (rc=0)
LISTENING 45143
CONTROL /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/a/control.sock
FEED b replayed 0
accepted run stopped on SIGTERM; store released
--- 181 stop server node B (main) (rc=0)
stopped
--- 182 node B store after the stop (rc=0)
transactions=14 articles=14 staging-orphans=0 unsigned-legacy-experiment
--- 183 node B log tail (rc=0)
LISTENING 33765
CONTROL /home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2/b/control.sock
FEED a replayed 0
--- 184 checkpoint on node A (rc=0)
anchor accepted server=int08h midpoint_us=1789974525088003 radius_us=5000000 incarnation=0
--- 185 node A reopens after the checkpoint (rc=0)
transactions=13 articles=13 staging-orphans=0 unsigned-legacy-experiment
--- 186 peer remove a peer that is not there (rc=1)
store: refused peer remove: no-such-peer
--- 187 peer remove the configured peer (rc=0)
peer removed name=b generation=7
--- 188 stop server node A (main) (rc=0)
stopped
--- 189 stop the tap in front of node A (rc=0)
stopped
--- 190 stop server node B (main) (rc=0)
stopped
--- 191 stop the tap in front of node B (rc=0)
stopped
--- 192 stray fn processes (rc=0)
CLEAN
--- 193 release deploy lock (rc=0)
```
