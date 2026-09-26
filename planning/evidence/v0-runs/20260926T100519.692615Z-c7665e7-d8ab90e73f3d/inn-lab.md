# INN interop lab: c7665e7 on hbox

A real InterNetNews server, built from the release tarball pinned below and
left installed on the box, peered with one fn node run from the saved native
image named below through its public entry. This records what ran. INN's
replies are INN's; fn's are fn's; each is quoted from the relay that carried
it. A row that could not run is a skip carrying the reason, never a weaker
scenario under the same name.

## What ran

| fact | value |
| --- | --- |
| commit | `c7665e7` (c7665e73c98c96bb7d27b8903502464e5224ee10) |
| tree | `dev` |
| host | `hbox` |
| started | 2026-09-26T10:09:00Z |
| wall time | 92.1 s |
| gate tool | `tools/inn_lab.py` |
| os | Ubuntu 24.10 kernel=Linux 6.11.0-29-generic arch=x86_64 cores=24 |
| python3 | Python 3.12.7 |
| native image | /tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host-developer e4eeefd290450e7497dade96e2c4089e0caacfa88f72c737f51a92b2f3b2ba18 |
| native launcher | packaging/fn-native 61f6f46445717262df794a786e9d8a705e547e6fb8f0b3e8bbbba5872298a8cd |
| native core | /tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host-developer.core 2e8d46071cb1803725233b70c3508a0ca176a2747147477715be43bdf60f3dc6 (the sidecar beside the image has the same digest) |
| native runtime | unmeasured |
| certificates | not acquired: the lab consumes the saved image it was given, as the v0 matrix's native slice does |
| inn version | INN 2.7.4 |
| inn tarball sha256 | 80fc7e801e1996cb17bb430d104dd9c5b29aa571fd4b29a9c821b4fadb051d3b  inn-2.7.4.tar.gz |
| inn prefix | /tank/fn/inn/2.7.4 |
| ports | innd 11419 (transit), nnrpd 11420 (reader), fn owner 11490, relay 11418 -> innd (fn's peer record names it), relay 11417 -> fn (innfeed.conf names it) |
| inn server | innd pid 1325584 on port 11419, nnrpd on port 11420 |
| fn node | native owner pid 1332100 on port 11490 (after-term), store $HOME/fn-inn-lab/dev-c7665e7/node/store |
| fn path identity | fnA.hbox.test (rc=0, accepted operator policy) |
| fn peer record | inn path-identity=inn.hbox.test address=127.0.0.1 port=11418 security=clear inbound=fn.* outbound=fn.* auth=source-address:127.0.0.1 |
| fn post | POST='340 send article to be posted' article='240 article received OK' ARTICLE='220 0 <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> article follows' |
| fn feed to inn | IHAVE: 335 Send it / 235 Article transferred OK; the octets fed are identical to what fn serves |
| inn read of fn's article | GROUP='211 83 1 83 fn.letters' ARTICLE='220 0 <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> article' absent='430 No such article' |
| fn post vs fn served | only in the second: injection-info, path; body identical; the injected Path is `fnA.hbox.test!not-for-mail` |
| fn served vs inn served | changed: path; only in the second: xref; body identical; Path fn=`fnA.hbox.test!not-for-mail` inn=`inn.hbox.test!fnA.hbox.test!not-for-mail`; Xref inn=`inn.hbox.test fn.letters:83` |
| operator post feed | post rc=0 (accepted operator post ACCEPTED); IHAVE: 335 Send it / 235 Article transferred OK; the fed article's Path is `fnA.hbox.test!not-for-mail` |
| inn control | MODE STREAM='203 Streaming permitted' IHAVE='335 Send it' transfer='235 Article transferred OK' duplicate='435 Duplicate' loop='437 Unwanted site inn.hbox.test in path' CHECK(new)='238 <inn-lab-absent-c7665e7-20260926T100900Z@example.invalid> Send it' CHECK(dup)='438 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> Duplicate' |
| innfeed to fn | CHECK+TAKETHIS: 238 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> / 239 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> |
| inn served vs fn served | changed: path; only in the first: xref; body identical; Path inn=`inn.hbox.test!lab.example.invalid!not-for-mail` fn=`fnA.hbox.test!!inn.hbox.test!lab.example.invalid!not-for-mail`; Xref inn=`inn.hbox.test fn.letters:86` fn=`` |
| duplicates | inn-article: IHAVE='435 duplicate'; fn-article: IHAVE='435 duplicate' |
| fn loop | IHAVE='335 send it; end with <CR-LF>.<CR-LF>' transfer='437 transfer rejected; path loop' ARTICLE after='430 no article with that message-id' |
| fn term | OWNER-GONE; recover rc=0; transactions=4 articles=4 staging-orphans=0 unsigned-legacy-experiment; fn-article identical, inn-article identical |
| innd cut | inn-article IHAVE='435 Duplicate'; fn-article IHAVE='435 Duplicate' |
| acl2version | + ACL2 Version 8.7                                                     + |
| alt | python3.12 Python 3.12.7 |
| fn post from yue | POST='340 send article to be posted' article='441 posting failed; From is not a valid mailbox list' ARTICLE='430 no article with that message-id' |
| fn post supplied path | POST='340 send article to be posted' article='240 article received OK' ARTICLE='220 0 <inn-lab-fn-path-c7665e7-20260926T100900Z@example.invalid> article follows' |
| operator post injection | expected Path=yes, Injection-Date=no, Injection-Info=yes; fed Path=yes, Injection-Date=no, Injection-Info=yes |
| operator post vs fed | only in the second: injection-info, path; body identical; the fed Path is `fnA.hbox.test!not-for-mail` |
| host clients | expect=ABSENT, inews=ABSENT, nn=ABSENT, script=/usr/bin/script, slrn=ABSENT, tin=/home/hbox/.cargo/bin/tin, trn=ABSENT |

## Every command

| # | step | rc | first line | s |
| --- | --- | --- | --- | --- |
| 1 | preflight | 0 | `os=Ubuntu 24.10 kernel=Linux 6.11.0-29-generic arch=x86_64 cores=24` | 1.1 |
| 2 | INN install | 0 | `innd=INN 2.7.4` | 0.9 |
| 3 | acquire deploy lock | 0 | `` | 0.8 |
| 4 | ship archive | 0 | `` | 46.7 |
| 5 | make run dir | 0 | `` | 0.7 |
| 6 | install inn.py | 0 | `` | 0.7 |
| 7 | install tap.py | 0 | `` | 0.9 |
| 8 | native subject | 0 | `NATIVE-LAUNCHER packaging/fn-native 61f6f46445717262df794a786e9d8a705e547e6fb8f0b3e8bbbba5872298a8cd` | 1.2 |
| 9 | fn store init | 0 | `initialized /home/hbox/fn-inn-lab/dev-c7665e7/node/store` | 0.8 |
| 10 | fn.toml | 0 | `[store]` | 0.7 |
| 11 | fn policy set path-identity | 0 | `configured generation=2 record=00000002.cfg verification=VERIFIED` | 0.9 |
| 12 | fn peer record for INN | 0 | `configured generation=3 record=00000003.cfg verification=VERIFIED` | 0.8 |
| 13 | fn peer list | 0 | `inn path-identity=inn.hbox.test address=127.0.0.1 port=11418 security=clear inbound=fn.* outbound=fn.* auth=source-address:127.0.0.1` | 0.8 |
| 14 | fn status before the owner starts | 0 | `transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment` | 0.8 |
| 15 | INN news user | 0 | `user=hbox group=hbox` | 0.6 |
| 16 | INN directories | 0 | `` | 0.7 |
| 17 | install inn.conf | 0 | `` | 0.6 |
| 18 | install incoming.conf | 0 | `` | 0.7 |
| 19 | install newsfeeds | 0 | `` | 0.5 |
| 20 | install innfeed.conf | 0 | `` | 0.3 |
| 21 | install readers.conf | 0 | `` | 0.3 |
| 22 | truncate innfeed's log | 0 | `` | 0.3 |
| 23 | INN history cold start | 0 | `active` | 0.4 |
| 24 | inncheck | 1 | `/tank/fn/inn/2.7.4/etc/newsfeeds:4: ME has exclusions` | 0.8 |
| 25 | INN inn.conf as written | 0 | `# fn INN interop lab -- generated by tools/inn_lab.py.  Loopback only.` | 0.4 |
| 26 | INN incoming.conf as written | 0 | `# fn INN interop lab -- INN accepts transit from the fn node over loopback.` | 0.4 |
| 27 | INN newsfeeds as written | 0 | `# fn INN interop lab -- generated by tools/inn_lab.py.` | 0.3 |
| 28 | INN innfeed.conf as written | 0 | `# fn INN interop lab -- the outbound half: INN offers fn.* to the fn node,` | 0.4 |
| 29 | INN readers.conf as written | 0 | `# fn INN interop lab -- nnrpd reads back what innd stored.  Loopback only.` | 0.3 |
| 30 | start innd | 0 | `INND-UP pid=1325584` | 1.3 |
| 31 | ctlinnd newgroup fn.letters | 0 | `Group status unchanged` | 0.2 |
| 32 | ctlinnd newgroup fn.test | 0 | `Group status unchanged` | 0.2 |
| 33 | INN active | 0 | `control 0000000000 0000000001 n` | 0.2 |
| 34 | ctlinnd reload newsfeeds | 0 | `Ok` | 3.3 |
| 35 | start nnrpd | 0 | `NNRPD-UP pid=1327111` | 1.3 |
| 36 | start the relay | 0 | `TAP-UP pid=1327462` | 0.3 |
| 37 | start the native owner (main) | 0 | `LISTENING 11490` | 1.2 |
| 38 | fn CAPABILITIES | 0 | `{"greeting": "200 fn-nntp experimental server ready", "status": "101 capability list follows", "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "XPAT", "NEWNEWS", "LIST ACTIVE ACTI` | 0.3 |
| 39 | install fn-post.article | 0 | `` | 0.2 |
| 40 | POST <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> to the fn owner | 0 | `{"greeting": "200 fn-nntp experimental server ready", "post": "340 send article to be posted", "result": "240 article received OK", "article": "220 0 <inn-lab-fn-post-c7665e7-20260926T100900Z@example.` | 0.3 |
| 41 | relay log: fn's feed offers <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> to innd | 0 | `IHAVE on 11418>11419: 335 Send it / 235 Article transferred OK` | 2.5 |
| 42 | read <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> back from INN's nnrpd | 0 | `{"greeting": "200 inn.hbox.test InterNetNews NNRP server INN 2.7.4 ready (posting ok)", "group": "211 83 1 83 fn.letters", "article": "220 0 <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> ` | 0.4 |
| 43 | IHAVE <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> into innd again | 0 | `{"greeting": "200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)", "offer": "435 Duplicate", "result": "", "ok": true}` | 0.3 |
| 44 | install fn-operator.article | 0 | `` | 0.2 |
| 45 | operator post <inn-lab-fn-operator-c7665e7-20260926T100900Z@example.invalid> | 0 | `accepted operator post ACCEPTED` | 0.4 |
| 46 | relay log: fn's feed offers <inn-lab-fn-operator-c7665e7-20260926T100900Z@example.invalid> to innd | 0 | `IHAVE on 11418>11419: 335 Send it / 235 Article transferred OK` | 0.3 |
| 47 | install fn-from.article | 0 | `` | 0.2 |
| 48 | POST <inn-lab-fn-from-c7665e7-20260926T100900Z@example.invalid> (From: yue) to the fn owner | 1 | `{"greeting": "200 fn-nntp experimental server ready", "post": "340 send article to be posted", "result": "441 posting failed; From is not a valid mailbox list", "article": "430 no article with that me` | 0.3 |
| 49 | install fn-path.article | 0 | `` | 0.2 |
| 50 | POST <inn-lab-fn-path-c7665e7-20260926T100900Z@example.invalid> (Path: not-for-mail) to the fn owner | 0 | `{"greeting": "200 fn-nntp experimental server ready", "post": "340 send article to be posted", "result": "240 article received OK", "article": "220 0 <inn-lab-fn-path-c7665e7-20260926T100900Z@example.` | 0.3 |
| 51 | install fed.article | 0 | `` | 0.2 |
| 52 | install inn-loop.article | 0 | `` | 0.2 |
| 53 | IHAVE <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> into innd | 0 | `{"greeting": "200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)", "mode_stream": "203 Streaming permitted", "offer": "335 Send it", "transfer": "235 Article transferred OK", "duplic` | 0.3 |
| 54 | INN history for <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> | 0 | `@050000000007000000000000005600000000@` | 0.2 |
| 55 | ctlinnd flush fn | 0 | `Ok` | 0.2 |
| 56 | relay log: innfeed offers <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> to fn | 0 | `CHECK+TAKETHIS on 11417>11490: 238 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> / 239 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid>` | 0.2 |
| 57 | innfeed log | 0 | `2026-09-26T06:10:07.668546-04:00 hbox innfeed[1325757]: ME finishing at Sat Sep 26 06:10:07 2026` | 0.3 |
| 58 | read <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> back from the fn owner | 0 | `{"greeting": "200 fn-nntp experimental server ready", "article": "220 0 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> article follows", "octets": "UGF0aDogZm5BLmhib3gudGVzdCEhaW5uLmhib3gudGVz` | 0.3 |
| 59 | read <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> back from INN's nnrpd | 0 | `{"greeting": "200 inn.hbox.test InterNetNews NNRP server INN 2.7.4 ready (posting ok)", "group": "211 86 1 86 fn.letters", "article": "220 0 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> arti` | 0.3 |
| 60 | IHAVE <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> to fn again | 0 | `{"greeting": "200 fn-nntp experimental server ready", "offer": "435 duplicate", "result": "", "after": "220 0 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> article follows", "octets": "UGF0aD` | 0.3 |
| 61 | IHAVE <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> to fn again | 0 | `{"greeting": "200 fn-nntp experimental server ready", "offer": "435 duplicate", "result": "", "after": "220 0 <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> article follows", "octets": "UG` | 0.2 |
| 62 | install fn-loop.article | 0 | `` | 0.2 |
| 63 | IHAVE <inn-lab-fn-loop-c7665e7-20260926T100900Z@example.invalid> (Path names fnA.hbox.test) to fn | 0 | `{"greeting": "200 fn-nntp experimental server ready", "offer": "335 send it; end with <CR-LF>.<CR-LF>", "result": "437 transfer rejected; path loop", "after": "430 no article with that message-id", "o` | 0.3 |
| 64 | SIGTERM the fn owner | 0 | `OWNER-GONE` | 1.3 |
| 65 | innd survived the fn owner's stop | 0 | `Server running` | 0.2 |
| 66 | owner log (main) | 0 | `accepted peer connection=3 peer=inn time=2026-09-26T10:10:18Z` | 0.2 |
| 67 | fn recover | 0 | `recovered transactions=4 articles=4 staging-orphans=0 anchor=none checkpoint=none` | 0.3 |
| 68 | fn status after recover | 0 | `transactions=4 articles=4 staging-orphans=0 unsigned-legacy-experiment` | 0.3 |
| 69 | start the native owner (after-term) | 0 | `LISTENING 11490` | 1.2 |
| 70 | reread <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> from fn after the restart | 0 | `{"greeting": "200 fn-nntp experimental server ready", "article": "220 0 <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> article follows", "octets": "UGF0aDogZm5BLmhib3gudGVzdCFub3QtZm9yLW1h` | 0.3 |
| 71 | reread <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> from fn after the restart | 0 | `{"greeting": "200 fn-nntp experimental server ready", "article": "220 0 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> article follows", "octets": "UGF0aDogZm5BLmhib3gudGVzdCEhaW5uLmhib3gudGVz` | 0.2 |
| 72 | kill -9 innd | 0 | `INND-GONE` | 0.2 |
| 73 | restart innd after the kill | 0 | `INND-UP pid=1332681` | 1.2 |
| 74 | after innd's restart, IHAVE <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> | 0 | `{"greeting": "200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)", "offer": "435 Duplicate", "result": "", "ok": true}` | 0.3 |
| 75 | after innd's restart, IHAVE <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> | 0 | `{"greeting": "200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)", "offer": "435 Duplicate", "result": "", "ok": true}` | 0.3 |
| 76 | stop the fn owner | 0 | `OWNER-GONE` | 1.2 |
| 77 | stop the relay | 0 | `stopped` | 0.2 |
| 78 | stop nnrpd | 0 | `stopped` | 0.2 |
| 79 | ctlinnd shutdown | 0 | `` | 0.2 |
| 80 | innd and innfeed are gone | 0 | `INND-GONE` | 1.2 |
| 81 | stray lab processes | 0 | `CLEAN` | 0.2 |
| 82 | remove the deploy tree | 0 | `` | 0.3 |
| 83 | release deploy lock | 0 | `` | 0.2 |
| 84 | the INN install is left in place | 0 | `/tank/fn/inn/2.7.4` | 0.2 |

### Commands in full

1. **preflight** -- `. /etc/os-release 2>/dev/null || true ; echo "os=${PRETTY_NAME:-unknown} kernel=$(uname -sr) arch=$(uname -m) cores=$(nproc 2>/dev/null || echo ?)" ; echo "python3=$(python3 -V 2>&1)" ; for p in python3.9 python3.10 python3.11 python3.12; do ; command -v $p >/dev/null && echo "alt=$p $($p -V 2>&1)" ; done ; for c in slrn tin nn trn inews expect script; do ; printf 'client %s=%s\n' "$c" "$(comma...`
2. **INN install** -- `P=/tank/fn/inn/2.7.4 ; if [ ! -x $P/bin/innd ]; then echo "NO-INN $P"; exit 1; fi ; echo "innd=$($P/bin/innconfval version 2>&1 | head -1)" ; echo "tarball=$(cat $(dirname $P)/src/inn-2.7.4.tar.gz.sha256 2>/dev/null | head -1)" ; for p in 11419 11420 11490 11418 11417; do ; if python3 -c "import socket,sys; s=socket.socket(); s.settimeout(2); sys.exit(0 if s.connect_ex(('127.0.0.1',$p))==0 else...`
3. **acquire deploy lock** -- `mkdir -p $HOME/fn-inn-lab/.locks ; if ! mkdir $HOME/fn-inn-lab/.locks/dev-c7665e7.lock 2>/dev/null; then ; echo "deploy identity is already active: dev-c7665e7" ; exit 73 ; fi`
4. **ship archive** -- `git archive c7665e7 | tar -x -C $HOME/fn-inn-lab/dev-c7665e7`
5. **make run dir** -- `mkdir -p $HOME/fn-inn-lab/dev-c7665e7/gate-run $HOME/fn-inn-lab/dev-c7665e7/node`
6. **install inn.py** -- `base64 -d > $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJUaGUgSU5OIGxhYidzIHNvY2tldCBwaGFzZXMuICBO ; byBmbiBtb2R1bGUgaXMgaW1wb3J0ZWQuCgpQeXRob24gMy4xMyByZW1vdmVkIG5udHBsaWIgKFBF ; UCA1OTQpLCBzbyBldmVyeSBOTlRQIGV4Y2hhbmdlIGhlcmUgaXMgYSByYXcKc29ja2V0LCBhbmQg ; ZXZlcnkgYXJ0aWNsZSBpcyBzZW50IGFuZCByZWFkIGFzIG9jdGV0czogYSB0cmFuc2l0IGNsaWVu ; dAp3cm...`
7. **install tap.py** -- `base64 -d > $HOME/fn-inn-lab/dev-c7665e7/gate-run/tap.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwppbXBvcnQgYmFzZTY0LCBqc29uLCBzb2NrZXQsIHN5cywg ; dGhyZWFkaW5nLCB0aW1lCgpsb2cgPSBvcGVuKHN5cy5hcmd2WzFdLCAiYSIsIGJ1ZmZlcmluZz0x ; KQpsb2NrID0gdGhyZWFkaW5nLkxvY2soKQoKCmRlZiBub3RlKCoqZmllbGRzKToKICAgIHdpdGgg ; bG9jazoKICAgICAgICBsb2cud3JpdGUoanNvbi5kdW1wcyhmaWVsZHMpICsgIlxuIikKCgpkZWYg ; cHVtcC...`
8. **native subject** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; image=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host-developer ; test -x "$image" || { echo "NATIVE-IMAGE-MISSING $image"; exit 4; } ; test -x packaging/fn-native || { echo NATIVE-WRAPPER-MISSING; exit 4; } ; if command -v sha256sum >/dev/null 2>&1; then ; digest() { sha256sum "$1" | awk '{print $1}...`
9. **fn store init** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host-developer packaging/fn-native store $HOME/fn-inn-lab/dev-c7665e7/node/store init fn.letters`
10. **fn.toml** -- `cat > $HOME/fn-inn-lab/dev-c7665e7/node/fn.toml <<FN_TOML ; [store] ; path = "$HOME/fn-inn-lab/dev-c7665e7/node/store" ; [listener] ; host = "127.0.0.1" ; port = 11490 ; [posting] ; enabled = true ; [control] ; path = "$HOME/fn-inn-lab/dev-c7665e7/node/control.sock" ; FN_TOML ; cat $HOME/fn-inn-lab/dev-c7665e7/node/fn.toml`
11. **fn policy set path-identity** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host-developer packaging/fn-native operator $HOME/fn-inn-lab/dev-c7665e7/node/fn.toml policy set path-identity fnA.hbox.test`
12. **fn peer record for INN** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host-developer packaging/fn-native operator $HOME/fn-inn-lab/dev-c7665e7/node/fn.toml peer add inn inn.hbox.test 127.0.0....`
13. **fn peer list** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host-developer packaging/fn-native operator $HOME/fn-inn-lab/dev-c7665e7/node/fn.toml peer list`
14. **fn status before the owner starts** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host-developer packaging/fn-native operator $HOME/fn-inn-lab/dev-c7665e7/node/fn.toml status`
15. **INN news user** -- `echo user=$(id -un) group=$(id -gn)`
16. **INN directories** -- `mkdir -p /tank/fn/inn/2.7.4/etc /tank/fn/inn/2.7.4/bin /tank/fn/inn/2.7.4/spool/articles /tank/fn/inn/2.7.4/spool/incoming /tank/fn/inn/2.7.4/spool/outgoing /tank/fn/inn/2.7.4/spool/overview /tank/fn/inn/2.7.4/spool/tmp /tank/fn/inn/2.7.4/spool/innfeed /tank/fn/inn/2.7.4/db /tank/fn/inn/2.7.4/log /tank/fn/inn/2.7.4/run /tank/fn/inn/2.7.4/tmp`
17. **install inn.conf** -- `base64 -d > /tank/fn/inn/2.7.4/etc/inn.conf <<'FN_GATE_EOF' ; IyBmbiBJTk4gaW50ZXJvcCBsYWIgLS0gZ2VuZXJhdGVkIGJ5IHRvb2xzL2lubl9sYWIucHkuICBM ; b29wYmFjayBvbmx5LgpwYXRoaG9zdDogICAgICAgICAgICAgICBpbm4uaGJveC50ZXN0CmRvbWFp ; bjogICAgICAgICAgICAgICAgIGhib3gudGVzdApvcmdhbml6YXRpb246ICAgICAgICAgICAiZm4g ; aW50ZXJvcCBsYWIiCnNlcnZlcjogICAgICAgICAgICAgICAgIDEyNy4wLjAuMQpwb3J0OiAgICAg ; ICAgICAgICAgICAgICA...`
18. **install incoming.conf** -- `base64 -d > /tank/fn/inn/2.7.4/etc/incoming.conf <<'FN_GATE_EOF' ; IyBmbiBJTk4gaW50ZXJvcCBsYWIgLS0gSU5OIGFjY2VwdHMgdHJhbnNpdCBmcm9tIHRoZSBmbiBu ; b2RlIG92ZXIgbG9vcGJhY2suCnN0cmVhbWluZzogICAgICB0cnVlCm1heC1jb25uZWN0aW9uczog ; OAoKcGVlciBmbiB7CiAgICBob3N0bmFtZTogICAgICAgIDEyNy4wLjAuMQogICAgcGF0dGVybnM6 ; ICAgICAgICBmbi4qCiAgICBzdHJlYW1pbmc6ICAgICAgIHRydWUKICAgIG1heC1jb25uZWN0aW9u ; czogNAp9Cg== ;...`
19. **install newsfeeds** -- `base64 -d > /tank/fn/inn/2.7.4/etc/newsfeeds <<'FN_GATE_EOF' ; IyBmbiBJTk4gaW50ZXJvcCBsYWIgLS0gZ2VuZXJhdGVkIGJ5IHRvb2xzL2lubl9sYWIucHkuCiMg ; TUUncyBleGNsdXNpb24gc3ViLWZpZWxkOiBhbiBpbmNvbWluZyBhcnRpY2xlIHdob3NlIFBhdGgg ; bmFtZXMgb25lIG9mIHRoZXNlCiMgc2l0ZXMgaXMgcmVmdXNlZCA0MzcgKGlubmQvYXJ0LmMgTUUu ; RXhjbHVzaW9ucykuCk1FL2lubi5oYm94LnRlc3Q6Kjo6CmlubmZlZWQhOiEqOlRjLFdubSo6L3Rh ; bmsvZm4vaW5uLzIuNy...`
20. **install innfeed.conf** -- `base64 -d > /tank/fn/inn/2.7.4/etc/innfeed.conf <<'FN_GATE_EOF' ; IyBmbiBJTk4gaW50ZXJvcCBsYWIgLS0gdGhlIG91dGJvdW5kIGhhbGY6IElOTiBvZmZlcnMgZm4u ; KiB0byB0aGUgZm4gbm9kZSwKIyB0aHJvdWdoIHRoZSBsYWIncyByZWxheSBvbiBwb3J0IDExNDE3 ; LCB3aGljaCBmb3J3YXJkcyB0byB0aGUgb3duZXIuCnBpZC1maWxlOiAgICAgICAgaW5uZmVlZC5w ; aWQKbG9nLWZpbGU6ICAgICAgICBpbm5mZWVkLmxvZwpzdGF0dXMtZmlsZTogICAgIGlubmZlZWQu ; c3RhdHVzCmJhY2t...`
21. **install readers.conf** -- `base64 -d > /tank/fn/inn/2.7.4/etc/readers.conf <<'FN_GATE_EOF' ; IyBmbiBJTk4gaW50ZXJvcCBsYWIgLS0gbm5ycGQgcmVhZHMgYmFjayB3aGF0IGlubmQgc3RvcmVk ; LiAgTG9vcGJhY2sgb25seS4KYXV0aCAibG9jYWxob3N0IiB7CiAgICBob3N0czogImxvY2FsaG9z ; dCwgMTI3LjAuMC4xLCA6OjEiCiAgICBkZWZhdWx0OiAiPGxvY2FsaG9zdD4iCn0KYWNjZXNzICJs ; b2NhbGhvc3QiIHsKICAgIHVzZXJzOiAiPGxvY2FsaG9zdD4iCiAgICBuZXdzZ3JvdXBzOiAiKiIK ; ICAgIGFjY2Vzczo...`
22. **truncate innfeed's log** -- `: > /tank/fn/inn/2.7.4/log/innfeed.log`
23. **INN history cold start** -- `P=/tank/fn/inn/2.7.4 ; if [ ! -f $P/db/history.dir ]; then ; : > $P/db/history ; $P/bin/makedbz -i -f $P/db/history ; mv $P/db/history.n.dir $P/db/history.dir ; mv $P/db/history.n.hash $P/db/history.hash ; mv $P/db/history.n.index $P/db/history.index ; fi ; if [ ! -f $P/db/active ]; then ; printf 'control 0000000000 0000000001 n\njunk 0000000000 0000000001 n\n' > $P/db/active ; : > $P/db/active...`
24. **inncheck** -- `/tank/fn/inn/2.7.4/bin/inncheck 2>&1 | head -20`
25. **INN inn.conf as written** -- `cat /tank/fn/inn/2.7.4/etc/inn.conf`
26. **INN incoming.conf as written** -- `cat /tank/fn/inn/2.7.4/etc/incoming.conf`
27. **INN newsfeeds as written** -- `cat /tank/fn/inn/2.7.4/etc/newsfeeds`
28. **INN innfeed.conf as written** -- `cat /tank/fn/inn/2.7.4/etc/innfeed.conf`
29. **INN readers.conf as written** -- `cat /tank/fn/inn/2.7.4/etc/readers.conf`
30. **start innd** -- `P=/tank/fn/inn/2.7.4 ; rm -f $P/log/innd-stdout.log ; nohup $P/bin/innd -d >> $P/log/innd-stdout.log 2>&1 < /dev/null & ; for i in $(seq 1 60); do ; if $P/bin/ctlinnd -t 2 mode 2>/dev/null | grep -q 'Server running'; then ; echo "INND-UP pid=$(cat $P/run/innd.pid 2>/dev/null)"; exit 0 ; fi ; sleep 1 ; done ; echo INND-TIMEOUT; tail -20 $P/log/innd-stdout.log; exit 1`
31. **ctlinnd newgroup fn.letters** -- `/tank/fn/inn/2.7.4/bin/ctlinnd newgroup fn.letters y $(id -un)`
32. **ctlinnd newgroup fn.test** -- `/tank/fn/inn/2.7.4/bin/ctlinnd newgroup fn.test y $(id -un)`
33. **INN active** -- `cat /tank/fn/inn/2.7.4/db/active`
34. **ctlinnd reload newsfeeds** -- `/tank/fn/inn/2.7.4/bin/ctlinnd -t 10 reload newsfeeds 'inn lab' 2>&1; sleep 3; cat /tank/fn/inn/2.7.4/run/innfeed.pid 2>/dev/null || echo NO-INNFEED-PID`
35. **start nnrpd** -- `P=/tank/fn/inn/2.7.4 ; nohup $P/bin/nnrpd -D -p 11420 > $P/log/nnrpd-stdout.log 2>&1 < /dev/null & ; for i in $(seq 1 30); do ; if python3 -c "import socket,sys; s=socket.socket(); s.settimeout(2); sys.exit(0 if s.connect_ex(('127.0.0.1',11420))==0 else 1)"; then ; echo "NNRPD-UP pid=$(cat $P/run/nnrpd-11420.pid 2>/dev/null)"; exit 0; fi ; sleep 1 ; done ; echo NNRPD-TIMEOUT; tail -10 $P/log/nn...`
36. **start the relay** -- `: > $HOME/fn-inn-lab/dev-c7665e7/gate-run/tap.log ; nohup python3 $HOME/fn-inn-lab/dev-c7665e7/gate-run/tap.py $HOME/fn-inn-lab/dev-c7665e7/gate-run/tap.log 11418:11419 11417:11490 > $HOME/fn-inn-lab/dev-c7665e7/gate-run/tap.stdout 2>&1 < /dev/null & ; echo $! > $HOME/fn-inn-lab/dev-c7665e7/gate-run/tap.pid ; for i in $(seq 1 20); do ; up=0 ; for p in 11418 11417; do ; python3 -c "import socket...`
37. **start the native owner (main)** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; rm -f $HOME/fn-inn-lab/dev-c7665e7/node/owner-main.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host-developer packaging/fn-native operator $HOME/fn-inn-l...`
38. **fn CAPABILITIES** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; python3 $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn.py caps --port 11490`
39. **install fn-post.article** -- `base64 -d > $HOME/fn-inn-lab/dev-c7665e7/gate-run/fn-post.article <<'FN_GATE_EOF' ; RnJvbTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVj ; dDogcG9zdGVkIG9uIGZuLCBmZWQgdG8gSU5ODQpEYXRlOiBTYXQsIDI2IFNlcCAyMDI2IDEwOjA5 ; OjAwIC0wMDAwDQpNZXNzYWdlLUlEOiA8aW5uLWxhYi1mbi1wb3N0LWM3NjY1ZTctMjAyNjA5MjZU ; MTAwOTAwWkBleGFtcGxlLmludmFsaWQ+DQoNCkZyb20gdGhlIGZuIElOTiBpbnRlcm9wIGxhYi4N...`
40. **POST <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> to the fn owner** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; python3 $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn.py post --port 11490 --msgid '<inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid>' --file $HOME/fn-inn-lab/dev-c7665e7/gate-run/fn-post.article`
41. **relay log: fn's feed offers <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> to innd** -- `cat $HOME/fn-inn-lab/dev-c7665e7/gate-run/tap.log (polled 2 times, pair 11418>11419)`
42. **read <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> back from INN's nnrpd** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; python3 $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn.py read --port 11420 --group fn.letters --msgid '<inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid>' --absent '<inn-lab-absent-c7665e7-20260926T100900Z@example.invalid>'`
43. **IHAVE <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> into innd again** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; python3 $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn.py offer --port 11419 --msgid '<inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid>' --file $HOME/fn-inn-lab/dev-c7665e7/gate-run/fn-post.article`
44. **install fn-operator.article** -- `base64 -d > $HOME/fn-inn-lab/dev-c7665e7/gate-run/fn-operator.article <<'FN_GATE_EOF' ; RnJvbTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVj ; dDogc3VibWl0dGVkIHRocm91Z2ggb3BlcmF0b3IgcG9zdA0KRGF0ZTogU2F0LCAyNiBTZXAgMjAy ; NiAxMDowOTowMCAtMDAwMA0KTWVzc2FnZS1JRDogPGlubi1sYWItZm4tb3BlcmF0b3ItYzc2NjVl ; Ny0yMDI2MDkyNlQxMDA5MDBaQGV4YW1wbGUuaW52YWxpZD4NCg0KRnJvbSB0aGUgZm4gSU5O...`
45. **operator post <inn-lab-fn-operator-c7665e7-20260926T100900Z@example.invalid>** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host-developer packaging/fn-native operator $HOME/fn-inn-lab/dev-c7665e7/node/fn.toml post --message-id '<inn-lab-fn-oper...`
46. **relay log: fn's feed offers <inn-lab-fn-operator-c7665e7-20260926T100900Z@example.invalid> to innd** -- `cat $HOME/fn-inn-lab/dev-c7665e7/gate-run/tap.log (polled 1 times, pair 11418>11419)`
47. **install fn-from.article** -- `base64 -d > $HOME/fn-inn-lab/dev-c7665e7/gate-run/fn-from.article <<'FN_GATE_EOF' ; RnJvbTogeXVlDQpOZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpTdWJqZWN0OiBhIEZyb20gdGhhdCBu ; YW1lcyBubyBhZGRyZXNzDQpEYXRlOiBTYXQsIDI2IFNlcCAyMDI2IDEwOjA5OjAwIC0wMDAwDQpN ; ZXNzYWdlLUlEOiA8aW5uLWxhYi1mbi1mcm9tLWM3NjY1ZTctMjAyNjA5MjZUMTAwOTAwWkBleGFt ; cGxlLmludmFsaWQ+DQoNCkZyb20gdGhlIGZuIElOTiBpbnRlcm9wIGxhYi4NCg== ; FN_GATE_E...`
48. **POST <inn-lab-fn-from-c7665e7-20260926T100900Z@example.invalid> (From: yue) to the fn owner** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; python3 $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn.py post --port 11490 --msgid '<inn-lab-fn-from-c7665e7-20260926T100900Z@example.invalid>' --file $HOME/fn-inn-lab/dev-c7665e7/gate-run/fn-from.article`
49. **install fn-path.article** -- `base64 -d > $HOME/fn-inn-lab/dev-c7665e7/gate-run/fn-path.article <<'FN_GATE_EOF' ; UGF0aDogbm90LWZvci1tYWlsDQpGcm9tOiBsYWJAZXhhbXBsZS5pbnZhbGlkDQpOZXdzZ3JvdXBz ; OiBmbi5sZXR0ZXJzDQpTdWJqZWN0OiBhIFBhdGggdGhlIHBvc3RpbmcgYWdlbnQgc3VwcGxpZWQN ; CkRhdGU6IFNhdCwgMjYgU2VwIDIwMjYgMTA6MDk6MDAgLTAwMDANCk1lc3NhZ2UtSUQ6IDxpbm4t ; bGFiLWZuLXBhdGgtYzc2NjVlNy0yMDI2MDkyNlQxMDA5MDBaQGV4YW1wbGUuaW52YWxpZD4NCg0K...`
50. **POST <inn-lab-fn-path-c7665e7-20260926T100900Z@example.invalid> (Path: not-for-mail) to the fn owner** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; python3 $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn.py post --port 11490 --msgid '<inn-lab-fn-path-c7665e7-20260926T100900Z@example.invalid>' --file $HOME/fn-inn-lab/dev-c7665e7/gate-run/fn-path.article`
51. **install fed.article** -- `base64 -d > $HOME/fn-inn-lab/dev-c7665e7/gate-run/fed.article <<'FN_GATE_EOF' ; UGF0aDogbGFiLmV4YW1wbGUuaW52YWxpZCFub3QtZm9yLW1haWwNCkZyb206IGxhYkBleGFtcGxl ; LmludmFsaWQNCk5ld3Nncm91cHM6IGZuLmxldHRlcnMNClN1YmplY3Q6IGhhbmRlZCB0byBJTk4s ; IGZlZCBvbiB0byBmbg0KRGF0ZTogU2F0LCAyNiBTZXAgMjAyNiAxMDowOTowMCAtMDAwMA0KTWVz ; c2FnZS1JRDogPGlubi1sYWItZmVkLWM3NjY1ZTctMjAyNjA5MjZUMTAwOTAwWkBleGFtcGxlLmlu ; d...`
52. **install inn-loop.article** -- `base64 -d > $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn-loop.article <<'FN_GATE_EOF' ; UGF0aDogaW5uLmhib3gudGVzdCFsYWIuZXhhbXBsZS5pbnZhbGlkIW5vdC1mb3ItbWFpbA0KRnJv ; bTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVjdDog ; YSBQYXRoIHRoYXQgbmFtZXMgSU5ODQpEYXRlOiBTYXQsIDI2IFNlcCAyMDI2IDEwOjA5OjAwIC0w ; MDAwDQpNZXNzYWdlLUlEOiA8aW5uLWxhYi1sb29wLWM3NjY1ZTctMjAyNjA5MjZUMTAwOTAwWkB...`
53. **IHAVE <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> into innd** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; python3 $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn.py ihave --port 11419 --msgid '<inn-lab-fed-c7665e7-20260926T100900Z@example.invalid>' --file $HOME/fn-inn-lab/dev-c7665e7/gate-run/fed.article --loop-msgid '<inn-lab-loop-c7665e7-20260926T100900Z@example.invalid>' --loop-file $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn-loop.article --absent '<inn-lab-ab...`
54. **INN history for <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid>** -- `/tank/fn/inn/2.7.4/bin/grephistory '<inn-lab-fed-c7665e7-20260926T100900Z@example.invalid>' 2>&1 | head -3`
55. **ctlinnd flush fn** -- `/tank/fn/inn/2.7.4/bin/ctlinnd -t 10 flush fn 2>&1 || true`
56. **relay log: innfeed offers <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> to fn** -- `cat $HOME/fn-inn-lab/dev-c7665e7/gate-run/tap.log (polled 1 times, pair 11417>11490)`
57. **innfeed log** -- `tail -20 /tank/fn/inn/2.7.4/log/innfeed.log 2>/dev/null; grep -h 'innfeed' /var/log/syslog 2>/dev/null | tail -8 || true`
58. **read <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> back from the fn owner** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; python3 $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn.py fetch --port 11490 --msgid '<inn-lab-fed-c7665e7-20260926T100900Z@example.invalid>'`
59. **read <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> back from INN's nnrpd** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; python3 $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn.py read --port 11420 --group fn.letters --msgid '<inn-lab-fed-c7665e7-20260926T100900Z@example.invalid>' --absent '<inn-lab-absent-c7665e7-20260926T100900Z@example.invalid>'`
60. **IHAVE <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> to fn again** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; python3 $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn.py offer --port 11490 --msgid '<inn-lab-fed-c7665e7-20260926T100900Z@example.invalid>' --file $HOME/fn-inn-lab/dev-c7665e7/gate-run/fed.article --read`
61. **IHAVE <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> to fn again** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; python3 $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn.py offer --port 11490 --msgid '<inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid>' --file $HOME/fn-inn-lab/dev-c7665e7/gate-run/fn-post.article --read`
62. **install fn-loop.article** -- `base64 -d > $HOME/fn-inn-lab/dev-c7665e7/gate-run/fn-loop.article <<'FN_GATE_EOF' ; UGF0aDogZm5BLmhib3gudGVzdCFsYWIuZXhhbXBsZS5pbnZhbGlkIW5vdC1mb3ItbWFpbA0KRnJv ; bTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVjdDog ; YSBQYXRoIHRoYXQgbmFtZXMgZm4NCkRhdGU6IFNhdCwgMjYgU2VwIDIwMjYgMTA6MDk6MDAgLTAw ; MDANCk1lc3NhZ2UtSUQ6IDxpbm4tbGFiLWZuLWxvb3AtYzc2NjVlNy0yMDI2MDkyNlQxMDA5MDBa...`
63. **IHAVE <inn-lab-fn-loop-c7665e7-20260926T100900Z@example.invalid> (Path names fnA.hbox.test) to fn** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; python3 $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn.py offer --port 11490 --msgid '<inn-lab-fn-loop-c7665e7-20260926T100900Z@example.invalid>' --file $HOME/fn-inn-lab/dev-c7665e7/gate-run/fn-loop.article --read`
64. **SIGTERM the fn owner** -- `kill -TERM 1327579 2>/dev/null || true ; for i in $(seq 1 60); do kill -0 1327579 2>/dev/null || break; sleep 1; done ; if kill -0 1327579 2>/dev/null; then kill -9 1327579; echo "OWNER-KILLED-AFTER-60S"; else echo OWNER-GONE; fi`
65. **innd survived the fn owner's stop** -- `/tank/fn/inn/2.7.4/bin/ctlinnd -t 5 mode 2>&1 | head -2`
66. **owner log (main)** -- `tail -12 $HOME/fn-inn-lab/dev-c7665e7/node/owner-main.log`
67. **fn recover** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host-developer packaging/fn-native operator $HOME/fn-inn-lab/dev-c7665e7/node/fn.toml recover`
68. **fn status after recover** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host-developer packaging/fn-native operator $HOME/fn-inn-lab/dev-c7665e7/node/fn.toml status`
69. **start the native owner (after-term)** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; rm -f $HOME/fn-inn-lab/dev-c7665e7/node/owner-after-term.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/openssl FN_NATIVE_HOST=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host-developer packaging/fn-native operator $HOME/fn...`
70. **reread <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> from fn after the restart** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; python3 $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn.py fetch --port 11490 --msgid '<inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid>'`
71. **reread <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> from fn after the restart** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; python3 $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn.py fetch --port 11490 --msgid '<inn-lab-fed-c7665e7-20260926T100900Z@example.invalid>'`
72. **kill -9 innd** -- `kill -9 1325584 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 1325584 2>/dev/null || break; sleep 1; done ; kill -0 1325584 2>/dev/null && echo INND-ALIVE || echo INND-GONE ; rm -f /tank/fn/inn/2.7.4/run/innd.pid /tank/fn/inn/2.7.4/run/control.ctl`
73. **restart innd after the kill** -- `P=/tank/fn/inn/2.7.4 ; nohup $P/bin/innd -d >> $P/log/innd-stdout.log 2>&1 < /dev/null & ; for i in $(seq 1 60); do ; if $P/bin/ctlinnd -t 2 mode 2>/dev/null | grep -q 'Server running'; then ; echo "INND-UP pid=$(cat $P/run/innd.pid 2>/dev/null)"; exit 0 ; fi ; sleep 1 ; done ; echo INND-TIMEOUT; tail -20 $P/log/innd-stdout.log; exit 1`
74. **after innd's restart, IHAVE <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid>** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; python3 $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn.py offer --port 11419 --msgid '<inn-lab-fed-c7665e7-20260926T100900Z@example.invalid>' --file $HOME/fn-inn-lab/dev-c7665e7/gate-run/fed.article`
75. **after innd's restart, IHAVE <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid>** -- `cd $HOME/fn-inn-lab/dev-c7665e7 || exit 9 ; python3 $HOME/fn-inn-lab/dev-c7665e7/gate-run/inn.py offer --port 11419 --msgid '<inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid>' --file $HOME/fn-inn-lab/dev-c7665e7/gate-run/fn-post.article`
76. **stop the fn owner** -- `kill -TERM 1332100 2>/dev/null || true ; for i in $(seq 1 60); do kill -0 1332100 2>/dev/null || break; sleep 1; done ; if kill -0 1332100 2>/dev/null; then kill -9 1332100; echo "OWNER-KILLED-AFTER-60S"; else echo OWNER-GONE; fi`
77. **stop the relay** -- `kill 1327462 2>/dev/null || true; echo stopped`
78. **stop nnrpd** -- `kill 1327111 2>/dev/null || true; echo stopped`
79. **ctlinnd shutdown** -- `/tank/fn/inn/2.7.4/bin/ctlinnd -t 5 shutdown 'inn lab done' 2>&1 || true`
80. **innd and innfeed are gone** -- `for i in $(seq 1 20); do ; kill -0 1332681 2>/dev/null || break; sleep 1 ; done ; kill -0 1332681 2>/dev/null && echo INND-ALIVE || echo INND-GONE ; pid=$(cat /tank/fn/inn/2.7.4/run/innfeed.pid 2>/dev/null || echo -1) ; kill -0 $pid 2>/dev/null && echo INNFEED-ALIVE || echo INNFEED-GONE`
81. **stray lab processes** -- `if pgrep -f -- "$HOME/fn-inn-lab/dev-c7665e7/" >/dev/null 2>&1; then echo STRAY; pgrep -af -- "$HOME/fn-inn-lab/dev-c7665e7/"; else echo CLEAN; fi`
82. **remove the deploy tree** -- `rm -rf $HOME/fn-inn-lab/dev-c7665e7`
83. **release deploy lock** -- `rmdir $HOME/fn-inn-lab/.locks/dev-c7665e7.lock`
84. **the INN install is left in place** -- `ls -d /tank/fn/inn/2.7.4 && echo INN-KEPT`

## Findings

One row per stated assertion. `held` and `violated` are the two that
DECIDE it; `inconclusive` means this run could not decide it and so
establishes nothing; `not-exercised` and `not-built` mean it was not
reached and why; `limitation` is a scope boundary no run of this
harness crosses.

The process exit is 1 for a violation, 3 for an inconclusive run with no violation, 2 when the gate stopped early, 0 otherwise.

Verdict of this run: **held** (34 held).

| assertion | verdict | what it says |
| --- | --- | --- |
| ports-free | held | the ports the lab needs were free before it started |
| native-subject-measured | held | the launcher, the image, the core it loads and the runtime were digested before anything ran |
| path-identity-set | held | `policy set path-identity` was accepted, so fn can recognise its own name in a Path (RFC 5537 3.2) |
| peer-record-accepted | held | the fn node holds a peer record naming INN, read back by `peer list` |
| innd-up | held | innd came up |
| nnrpd-up | held | nnrpd came up on its port |
| tap-up | held | the relay listened on both of its ports |
| entry-point-listening | held | the native owner (`packaging/fn-native operator CONFIG run`) reached LISTENING on the port the lab configured |
| fn-post-240 | held | POST to the fn owner drew 340 then 240, and the article reads back by Message-ID |
| fn-feeds-inn | held | fn's outbound feed offered the posted article to innd by IHAVE, and innd answered 335 then 235 |
| inn-serves-fn-article | held | nnrpd serves the article fn fed, changed only where RFC 5537 3.6 permits a relay to change it (Path, Xref) |
| inn-duplicate-435[fn-article] | held | a second IHAVE of an article innd holds draws 435 |
| operator-post-feeds-inn | held | an article submitted through `operator post` reaches innd through fn's outbound feed, injected: Path naming fn and Injection-Info, and Injection-Date only when the submission lacked Date or Message-ID (RFC 5537 3.5 item 11) |
| fn-post-from-invalid-441 | held | a POST whose From names no address (`From: yue`) draws 441 from fn and is not served (RFC 5536 3.1.2) |
| fn-post-supplied-path-240 | held | a POST that supplies `Path: not-for-mail`, as tin sends, draws 240 and reads back (D32; RFC 5537 3.4.1 and 3.2.1: the injecting agent prefixes its identity) |
| inn-transfer-235 | held | a hand-made IHAVE into innd draws 335 then 235 |
| inn-duplicate-435 | held | a second IHAVE of an article innd holds draws 435 |
| inn-loop-437 | held | an article whose Path names INN draws 437 from innd |
| innfeed-feeds-fn | held | INN's innfeed offered an article to fn and fn took it (238/239 or 335/235) |
| fn-serves-inn-article | held | fn serves the article innfeed transferred with every octet but Path and Xref as it arrived (RFC 5537 3.7: a serving agent alters nothing else) |
| fn-serves-own-path-identity | held | the Path fn serves for an article it took by transit names fn's own path identity (RFC 5537 3.7 step 6, by way of 3.2.1) |
| fn-serves-no-sender-xref | held | fn does not serve the sending server's Xref on an article it took by transit (RFC 5537 3.7 step 7; specs/peering.md 2.3, `Xref` is never stored) |
| fn-duplicate-435[inn-article] | held | a second IHAVE of an article fn holds draws 435 from fn |
| fn-duplicate-435[fn-article] | held | a second IHAVE of an article fn holds draws 435 from fn |
| fn-loop-refused | held | an article whose Path names fn's own path identity is refused by fn (RFC 5537 3.6 step 3; 435 or 437) and is not served |
| fn-term-stopped | held | the owner exited on SIGTERM |
| innd-survived-fn-term | held | innd was still running after the fn owner was stopped |
| fn-recover | held | `operator CONFIG recover` exited 0 after the SIGTERM |
| fn-articles-survived-term[fn-article] | held | after SIGTERM, recover and restart, fn serves the articles it held byte-identical |
| fn-articles-survived-term[inn-article] | held | after SIGTERM, recover and restart, fn serves the articles it held byte-identical |
| innd-died | held | innd died on SIGKILL, so the control really cut |
| innd-restarted | held | innd came back after the SIGKILL |
| inn-history-survived-kill[inn-article] | held | after innd's SIGKILL and restart, a second IHAVE of an article it acknowledged before draws 435 |
| inn-history-survived-kill[fn-article] | held | after innd's SIGKILL and restart, a second IHAVE of an article it acknowledged before draws 435 |

## What was NOT exercised

Nothing was skipped in this run.

Standing gaps of the gate itself, independent of this run:

- INN and fn are on ONE host, over loopback. Nothing here exercises a real
  network, a partition, latency, or two machines' clocks disagreeing.
- Both transit connections pass through the lab's relay (tap.py). It forwards
  octets unchanged and in order, and both servers see it as 127.0.0.1, the
  address each peer record admits; it is still a hop neither would have.
- No TLS, no AUTHINFO, no Distribution header, no control messages, no
  cancel and no expiry: incoming.conf and fn's peer record authorise by
  source address only, which on loopback authorises everything local.
- A SIGKILL of innd and a SIGTERM of the owner are process deaths, not power
  loss, and killing one server is not a partition.
- No RFC 3977/4644/5537 conformance audit. The assertions are this driver's,
  and a held row says the two programs interoperated on that exchange.
- The native image is consumed as named; nothing here re-establishes which
  source or which certificates it was built from.

## The relay's transcript

Every octet each server sent the other on the two transit
connections, as `tap.py` logged it. `C:` is the side that
connected, `S:` the side that listened; article lines are
indented and dot-unstuffed.

### fn's feed -> innd (relay 11418>11419), connection 1

```
S: 200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)
```

### fn's feed -> innd (relay 11418>11419), connection 2

```
S: 200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)
C: IHAVE <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid>
S: 335 Send it
C:   Path: fnA.hbox.test!not-for-mail
C:   Injection-Info: fnA.hbox.test
C:   From: lab@example.invalid
C:   Newsgroups: fn.letters
C:   Subject: posted on fn, fed to INN
C:   Date: Sat, 26 Sep 2026 10:09:00 -0000
C:   Message-ID: <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid>
C:   
C:   From the fn INN interop lab.
C: .
S: 235 Article transferred OK
C: IHAVE <inn-lab-fn-operator-c7665e7-20260926T100900Z@example.invalid>
S: 335 Send it
C:   Path: fnA.hbox.test!not-for-mail
C:   Injection-Info: fnA.hbox.test
C:   From: lab@example.invalid
C:   Newsgroups: fn.letters
C:   Subject: submitted through operator post
C:   Date: Sat, 26 Sep 2026 10:09:00 -0000
C:   Message-ID: <inn-lab-fn-operator-c7665e7-20260926T100900Z@example.invalid>
C:   
C:   From the fn INN interop lab.
C: .
S: 235 Article transferred OK
C: IHAVE <inn-lab-fn-path-c7665e7-20260926T100900Z@example.invalid>
S: 335 Send it
C:   Injection-Info: fnA.hbox.test
C:   Path: fnA.hbox.test!not-for-mail
C:   From: lab@example.invalid
C:   Newsgroups: fn.letters
C:   Subject: a Path the posting agent supplied
C:   Date: Sat, 26 Sep 2026 10:09:00 -0000
C:   Message-ID: <inn-lab-fn-path-c7665e7-20260926T100900Z@example.invalid>
C:   
C:   From the fn INN interop lab.
C: .
S: 235 Article transferred OK
```

### innfeed -> fn (relay 11417>11490), connection 1

```
S: 200 fn-nntp experimental server ready
C: MODE STREAM
S: 203 streaming permitted
C: CHECK <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid>
S: 238 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid>
C: TAKETHIS <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid>
C:   Path: inn.hbox.test!lab.example.invalid!not-for-mail
C:   From: lab@example.invalid
C:   Newsgroups: fn.letters
C:   Subject: handed to INN, fed on to fn
C:   Date: Sat, 26 Sep 2026 10:09:00 -0000
C:   Message-ID: <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid>
C:   Xref: inn.hbox.test fn.letters:86
C:   
C:   From the fn INN interop lab.
C: .
S: 239 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid>
```

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
--- 2 INN install (rc=0)
innd=INN 2.7.4
tarball=80fc7e801e1996cb17bb430d104dd9c5b29aa571fd4b29a9c821b4fadb051d3b  inn-2.7.4.tar.gz
port 11419 free
port 11420 free
port 11490 free
port 11418 free
port 11417 free
--- 3 acquire deploy lock (rc=0)
--- 4 ship archive (rc=0)
--- 5 make run dir (rc=0)
--- 6 install inn.py (rc=0)
--- 7 install tap.py (rc=0)
--- 8 native subject (rc=0)
NATIVE-LAUNCHER packaging/fn-native 61f6f46445717262df794a786e9d8a705e547e6fb8f0b3e8bbbba5872298a8cd
NATIVE-IMAGE /tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host-developer e4eeefd290450e7497dade96e2c4089e0caacfa88f72c737f51a92b2f3b2ba18
NATIVE-SIDECAR /tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host-developer.core 2e8d46071cb1803725233b70c3508a0ca176a2747147477715be43bdf60f3dc6
NATIVE-CORE /tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80/fn-host-developer.core 2e8d46071cb1803725233b70c3508a0ca176a2747147477715be43bdf60f3dc6
NATIVE-RUNTIME unmeasured
--- 9 fn store init (rc=0)
initialized /home/hbox/fn-inn-lab/dev-c7665e7/node/store
--- 10 fn.toml (rc=0)
[store]
path = "/home/hbox/fn-inn-lab/dev-c7665e7/node/store"

[listener]
host = "127.0.0.1"
port = 11490

[posting]
enabled = true

[control]
path = "/home/hbox/fn-inn-lab/dev-c7665e7/node/control.sock"
--- 11 fn policy set path-identity (rc=0)
configured generation=2 record=00000002.cfg verification=VERIFIED
accepted operator policy
--- 12 fn peer record for INN (rc=0)
configured generation=3 record=00000003.cfg verification=VERIFIED
accepted operator peer
--- 13 fn peer list (rc=0)
inn path-identity=inn.hbox.test address=127.0.0.1 port=11418 security=clear inbound=fn.* outbound=fn.* auth=source-address:127.0.0.1
accepted operator peer
--- 14 fn status before the owner starts (rc=0)
transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment
profile format=8 max-transactions=128 max-history-octets=25165824 max-record-octets=17138486 max-article-octets=32768 max-groups-per-article=65535 max-group-name-octets=256 max-open-suffix=128 max-consumers=1048576 max-bp-rows=1048576 max-config-generations=1048576 max-credentials=1048576 max-policy-members=1048576 history-marker=unmarked
open-cost replay-records=128 list-memory-octets=805306368
headroom transactions-used=0 transactions-budget=128 bytes-used=0 history-bound=25165824 charge-reserved=0 charge-capacity=1048576
maintenance-reserve octets=4096 transactions=1 held
open=full-replay reason=absent
reclaim rule=keep-forever reclaimable=0 reclaimable-octets=0 held=0 reclaimed=0 freed-octets=0
checkpoint-file=absent
pins=0 reserved=0 connections=0
accepted operator status
--- 15 INN news user (rc=0)
user=hbox group=hbox
--- 16 INN directories (rc=0)
--- 17 install inn.conf (rc=0)
--- 18 install incoming.conf (rc=0)
--- 19 install newsfeeds (rc=0)
--- 20 install innfeed.conf (rc=0)
--- 21 install readers.conf (rc=0)
--- 22 truncate innfeed's log (rc=0)
--- 23 INN history cold start (rc=0)
active
active.old
active.times
history
history.dir
history.hash
history.index
newsgroups
--- 24 inncheck (rc=1)
/tank/fn/inn/2.7.4/etc/newsfeeds:4: ME has exclusions
--- 25 INN inn.conf as written (rc=0)
# fn INN interop lab -- generated by tools/inn_lab.py.  Loopback only.
pathhost:               inn.hbox.test
domain:                 hbox.test
organization:           "fn interop lab"
server:                 127.0.0.1
port:                   11419
bindaddress:            127.0.0.1
mta:                    "/usr/sbin/sendmail -oi %s"
hismethod:              hisv6
ovmethod:               tradindexed
enableoverview:         true
allownewnews:           true
--- 26 INN incoming.conf as written (rc=0)
# fn INN interop lab -- INN accepts transit from the fn node over loopback.
streaming:      true
max-connections: 8

peer fn {
    hostname:        127.0.0.1
    patterns:        fn.*
    streaming:       true
    max-connections: 4
}
--- 27 INN newsfeeds as written (rc=0)
# fn INN interop lab -- generated by tools/inn_lab.py.
# ME's exclusion sub-field: an incoming article whose Path names one of these
# sites is refused 437 (innd/art.c ME.Exclusions).
ME/inn.hbox.test:*::
innfeed!:!*:Tc,Wnm*:/tank/fn/inn/2.7.4/bin/innfeed -y
fn/fnA.hbox.test:fn.*:Tm:innfeed!
--- 28 INN innfeed.conf as written (rc=0)
# fn INN interop lab -- the outbound half: INN offers fn.* to the fn node,
# through the lab's relay on port 11417, which forwards to the owner.
pid-file:        innfeed.pid
log-file:        innfeed.log
status-file:     innfeed.status
backlog-directory: /tank/fn/inn/2.7.4/spool/innfeed
use-mmap:        false
initial-reconnect-time: 5
max-reconnect-time:     60

peer fn {
    ip-name:             127.0.0.1
--- 29 INN readers.conf as written (rc=0)
# fn INN interop lab -- nnrpd reads back what innd stored.  Loopback only.
auth "localhost" {
    hosts: "localhost, 127.0.0.1, ::1"
    default: "<localhost>"
}
access "localhost" {
    users: "<localhost>"
    newsgroups: "*"
    access: RPA
}
--- 30 start innd (rc=0)
INND-UP pid=1325584
--- 31 ctlinnd newgroup fn.letters (rc=0)
Group status unchanged
--- 32 ctlinnd newgroup fn.test (rc=0)
Group status unchanged
--- 33 INN active (rc=0)
control 0000000000 0000000001 n
control.cancel 0000000000 0000000001 n
control.checkgroups 0000000000 0000000001 n
control.newgroup 0000000000 0000000001 n
control.rmgroup 0000000000 0000000001 n
junk 0000000000 0000000001 n
fn.letters 0000000082 0000000001 y
fn.test 0000000000 0000000001 y
--- 34 ctlinnd reload newsfeeds (rc=0)
Ok
1326274
--- 35 start nnrpd (rc=0)
NNRPD-UP pid=1327111
--- 36 start the relay (rc=0)
TAP-UP pid=1327462
--- 37 start the native owner (main) (rc=0)
LISTENING 11490
OWNER-UP pid=1327579
--- 38 fn CAPABILITIES (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "status": "101 capability list follows", "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "XPAT", "NEWNEWS", "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING"], "ok": true}
--- 39 install fn-post.article (rc=0)
--- 40 POST <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> to the fn owner (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "post": "340 send article to be posted", "result": "240 article received OK", "article": "220 0 <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> article follows", "octets": "UGF0aDogZm5BLmhib3gudGVzdCFub3QtZm9yLW1haWwNCkluamVjdGlvbi1JbmZvOiBmbkEuaGJveC50ZXN0DQpGcm9tOiBsYWJAZXhhbXBsZS5pbnZhbGlkDQpOZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpTdWJqZWN0OiBwb3N0ZWQgb24gZm4sIGZlZCB0byBJTk4NCkRhdGU6IFNhdCwgMjYgU2VwIDIwMjYgMTA6MDk6MDAgLTAwMDANCk1lc3NhZ2UtSUQ6IDxpbm4tbGFiLWZuLXBvc3QtYzc2NjVlNy0yMDI2MDkyNlQxMDA5MDBaQGV4YW1wbGUuaW52YWxpZD4NCg0KRnJvbSB0aGUgZm4gSU5OIGludGVyb3AgbGFiLg0K", "ok": true}
--- 41 relay log: fn's feed offers <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> to innd (rc=0)
IHAVE on 11418>11419: 335 Send it / 235 Article transferred OK
--- 42 read <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> back from INN's nnrpd (rc=0)
{"greeting": "200 inn.hbox.test InterNetNews NNRP server INN 2.7.4 ready (posting ok)", "group": "211 83 1 83 fn.letters", "article": "220 0 <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> article", "octets": "UGF0aDogaW5uLmhib3gudGVzdCFmbkEuaGJveC50ZXN0IW5vdC1mb3ItbWFpbA0KSW5qZWN0aW9uLUluZm86IGZuQS5oYm94LnRlc3QNCkZyb206IGxhYkBleGFtcGxlLmludmFsaWQNCk5ld3Nncm91cHM6IGZuLmxldHRlcnMNClN1YmplY3Q6IHBvc3RlZCBvbiBmbiwgZmVkIHRvIElOTg0KRGF0ZTogU2F0LCAyNiBTZXAgMjAyNiAxMDowOTowMCAtMDAwMA0KTWVzc2FnZS1JRDogPGlubi1sYWItZm4tcG9zdC1jNzY2NWU3LTIwMjYwOTI2VDEwMDkwMFpAZXhhbXBsZS5pbnZhbGlkPg0KWHJlZjogaW5uLmhib3gudGVzdCBmbi5sZXR0ZXJzOjgzDQoNCkZyb20gdGhlIGZuIElOTiBpbnRlcm9wIGxhYi4NCg==", "absent": "430 No such article", "ok": true}
--- 43 IHAVE <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> into innd again (rc=0)
{"greeting": "200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)", "offer": "435 Duplicate", "result": "", "ok": true}
--- 44 install fn-operator.article (rc=0)
--- 45 operator post <inn-lab-fn-operator-c7665e7-20260926T100900Z@example.invalid> (rc=0)
accepted operator post ACCEPTED
--- 46 relay log: fn's feed offers <inn-lab-fn-operator-c7665e7-20260926T100900Z@example.invalid> to innd (rc=0)
IHAVE on 11418>11419: 335 Send it / 235 Article transferred OK
--- 47 install fn-from.article (rc=0)
--- 48 POST <inn-lab-fn-from-c7665e7-20260926T100900Z@example.invalid> (From: yue) to the fn owner (rc=1)
{"greeting": "200 fn-nntp experimental server ready", "post": "340 send article to be posted", "result": "441 posting failed; From is not a valid mailbox list", "article": "430 no article with that message-id", "octets": "", "ok": false}
--- 49 install fn-path.article (rc=0)
--- 50 POST <inn-lab-fn-path-c7665e7-20260926T100900Z@example.invalid> (Path: not-for-mail) to the fn owner (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "post": "340 send article to be posted", "result": "240 article received OK", "article": "220 0 <inn-lab-fn-path-c7665e7-20260926T100900Z@example.invalid> article follows", "octets": "SW5qZWN0aW9uLUluZm86IGZuQS5oYm94LnRlc3QNClBhdGg6IGZuQS5oYm94LnRlc3Qhbm90LWZvci1tYWlsDQpGcm9tOiBsYWJAZXhhbXBsZS5pbnZhbGlkDQpOZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpTdWJqZWN0OiBhIFBhdGggdGhlIHBvc3RpbmcgYWdlbnQgc3VwcGxpZWQNCkRhdGU6IFNhdCwgMjYgU2VwIDIwMjYgMTA6MDk6MDAgLTAwMDANCk1lc3NhZ2UtSUQ6IDxpbm4tbGFiLWZuLXBhdGgtYzc2NjVlNy0yMDI2MDkyNlQxMDA5MDBaQGV4YW1wbGUuaW52YWxpZD4NCg0KRnJvbSB0aGUgZm4gSU5OIGludGVyb3AgbGFiLg0K", "ok": true}
--- 51 install fed.article (rc=0)
--- 52 install inn-loop.article (rc=0)
--- 53 IHAVE <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> into innd (rc=0)
{"greeting": "200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)", "mode_stream": "203 Streaming permitted", "offer": "335 Send it", "transfer": "235 Article transferred OK", "duplicate": "435 Duplicate", "duplicate_transfer": "", "loop_offer": "335 Send it", "loop_result": "437 Unwanted site inn.hbox.test in path", "check_unknown": "238 <inn-lab-absent-c7665e7-20260926T100900Z@example.invalid> Send it", "check_duplicate": "438 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> Duplicate", "ok": true}
--- 54 INN history for <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> (rc=0)
@050000000007000000000000005600000000@
--- 55 ctlinnd flush fn (rc=0)
Ok
--- 56 relay log: innfeed offers <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> to fn (rc=0)
CHECK+TAKETHIS on 11417>11490: 238 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> / 239 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid>
--- 57 innfeed log (rc=0)
2026-09-26T06:10:07.668546-04:00 hbox innfeed[1325757]: ME finishing at Sat Sep 26 06:10:07 2026
2026-09-26T06:10:07.668716-04:00 hbox innd: innfeed! exit 0 elapsed 2 pid 1325757
2026-09-26T06:10:09.200370-04:00 hbox innfeed[1326274]: fn:0 cxnsleep connect: Connection refused
2026-09-26T06:10:09.200456-04:00 hbox innfeed[1326274]: fn spooling no active connections
2026-09-26T06:10:14.226070-04:00 hbox innfeed[1326274]: fn:0 connected
2026-09-26T06:10:14.226144-04:00 hbox innfeed[1326274]: fn remote MODE STREAM
2026-09-26T06:10:14.226161-04:00 hbox innfeed[1326274]: fn checkpoint seconds 5 spooled 0 on_close 0 sleeping 0
2026-09-26T06:10:14.226178-04:00 hbox innfeed[1326274]: fn final seconds 5 spooled 0 on_close 0 sleeping 0
--- 58 read <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> back from the fn owner (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "article": "220 0 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> article follows", "octets": "UGF0aDogZm5BLmhib3gudGVzdCEhaW5uLmhib3gudGVzdCFsYWIuZXhhbXBsZS5pbnZhbGlkIW5vdC1mb3ItbWFpbA0KRnJvbTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVjdDogaGFuZGVkIHRvIElOTiwgZmVkIG9uIHRvIGZuDQpEYXRlOiBTYXQsIDI2IFNlcCAyMDI2IDEwOjA5OjAwIC0wMDAwDQpNZXNzYWdlLUlEOiA8aW5uLWxhYi1mZWQtYzc2NjVlNy0yMDI2MDkyNlQxMDA5MDBaQGV4YW1wbGUuaW52YWxpZD4NCg0KRnJvbSB0aGUgZm4gSU5OIGludGVyb3AgbGFiLg0K", "ok": true}
--- 59 read <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> back from INN's nnrpd (rc=0)
{"greeting": "200 inn.hbox.test InterNetNews NNRP server INN 2.7.4 ready (posting ok)", "group": "211 86 1 86 fn.letters", "article": "220 0 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> article", "octets": "UGF0aDogaW5uLmhib3gudGVzdCFsYWIuZXhhbXBsZS5pbnZhbGlkIW5vdC1mb3ItbWFpbA0KRnJvbTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVjdDogaGFuZGVkIHRvIElOTiwgZmVkIG9uIHRvIGZuDQpEYXRlOiBTYXQsIDI2IFNlcCAyMDI2IDEwOjA5OjAwIC0wMDAwDQpNZXNzYWdlLUlEOiA8aW5uLWxhYi1mZWQtYzc2NjVlNy0yMDI2MDkyNlQxMDA5MDBaQGV4YW1wbGUuaW52YWxpZD4NClhyZWY6IGlubi5oYm94LnRlc3QgZm4ubGV0dGVyczo4Ng0KDQpGcm9tIHRoZSBmbiBJTk4gaW50ZXJvcCBsYWIuDQo=", "absent": "430 No such article", "ok": true}
--- 60 IHAVE <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> to fn again (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "offer": "435 duplicate", "result": "", "after": "220 0 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> article follows", "octets": "UGF0aDogZm5BLmhib3gudGVzdCEhaW5uLmhib3gudGVzdCFsYWIuZXhhbXBsZS5pbnZhbGlkIW5vdC1mb3ItbWFpbA0KRnJvbTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVjdDogaGFuZGVkIHRvIElOTiwgZmVkIG9uIHRvIGZuDQpEYXRlOiBTYXQsIDI2IFNlcCAyMDI2IDEwOjA5OjAwIC0wMDAwDQpNZXNzYWdlLUlEOiA8aW5uLWxhYi1mZWQtYzc2NjVlNy0yMDI2MDkyNlQxMDA5MDBaQGV4YW1wbGUuaW52YWxpZD4NCg0KRnJvbSB0aGUgZm4gSU5OIGludGVyb3AgbGFiLg0K", "ok": true}
--- 61 IHAVE <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> to fn again (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "offer": "435 duplicate", "result": "", "after": "220 0 <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> article follows", "octets": "UGF0aDogZm5BLmhib3gudGVzdCFub3QtZm9yLW1haWwNCkluamVjdGlvbi1JbmZvOiBmbkEuaGJveC50ZXN0DQpGcm9tOiBsYWJAZXhhbXBsZS5pbnZhbGlkDQpOZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpTdWJqZWN0OiBwb3N0ZWQgb24gZm4sIGZlZCB0byBJTk4NCkRhdGU6IFNhdCwgMjYgU2VwIDIwMjYgMTA6MDk6MDAgLTAwMDANCk1lc3NhZ2UtSUQ6IDxpbm4tbGFiLWZuLXBvc3QtYzc2NjVlNy0yMDI2MDkyNlQxMDA5MDBaQGV4YW1wbGUuaW52YWxpZD4NCg0KRnJvbSB0aGUgZm4gSU5OIGludGVyb3AgbGFiLg0K", "ok": true}
--- 62 install fn-loop.article (rc=0)
--- 63 IHAVE <inn-lab-fn-loop-c7665e7-20260926T100900Z@example.invalid> (Path names fnA.hbox.test) to fn (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "offer": "335 send it; end with <CR-LF>.<CR-LF>", "result": "437 transfer rejected; path loop", "after": "430 no article with that message-id", "octets": "", "ok": true}
--- 64 SIGTERM the fn owner (rc=0)
OWNER-GONE
--- 65 innd survived the fn owner's stop (rc=0)
Server running
Allowing remote connections
--- 66 owner log (main) (rc=0)
accepted peer connection=3 peer=inn time=2026-09-26T10:10:18Z
refused post path=served connection=3 reason=from-invalid time=2026-09-26T10:10:18Z
accepted peer connection=4 peer=inn time=2026-09-26T10:10:18Z
accepted post path=served connection=4 message-id=<inn-lab-fn-path-c7665e7-20260926T100900Z@example.invalid> agent=fnA.hbox.test time=2026-09-26T10:10:18Z
accepted feed peer=inn message-id=<inn-lab-fn-path-c7665e7-20260926T100900Z@example.invalid> code=235 time=2026-09-26T10:10:18Z
accepted transit connection=2 message-id=<inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> code=239 decision=want reason=none detail=none time=2026-09-26T10:10:19Z
accepted peer connection=5 peer=inn time=2026-09-26T10:10:20Z
accepted peer connection=6 peer=inn time=2026-09-26T10:10:21Z
accepted peer connection=7 peer=inn time=2026-09-26T10:10:21Z
accepted peer connection=8 peer=inn time=2026-09-26T10:10:22Z
refused transit connection=8 message-id=<inn-lab-fn-loop-c7665e7-20260926T100900Z@example.invalid> code=437 decision=refuse reason=loop detail=none time=2026-09-26T10:10:22Z
accepted operator run
--- 67 fn recover (rc=0)
recovered transactions=4 articles=4 staging-orphans=0 anchor=none checkpoint=none
open=full-replay reason=absent
accepted operator recover
--- 68 fn status after recover (rc=0)
transactions=4 articles=4 staging-orphans=0 unsigned-legacy-experiment
profile format=8 max-transactions=128 max-history-octets=25165824 max-record-octets=17138486 max-article-octets=32768 max-groups-per-article=65535 max-group-name-octets=256 max-open-suffix=128 max-consumers=1048576 max-bp-rows=1048576 max-config-generations=1048576 max-credentials=1048576 max-policy-members=1048576 history-marker=unmarked
open-cost replay-records=128 list-memory-octets=805306368
headroom transactions-used=4 transactions-budget=128 bytes-used=2540 history-bound=25165824 charge-reserved=8 charge-capacity=1048576
maintenance-reserve octets=4096 transactions=1 held
open=full-replay reason=absent
reclaim rule=keep-forever reclaimable=0 reclaimable-octets=0 held=0 reclaimed=0 freed-octets=0
checkpoint-file=absent
pins=4 reserved=8 connections=0
accepted operator status
--- 69 start the native owner (after-term) (rc=0)
LISTENING 11490
OWNER-UP pid=1332100
--- 70 reread <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> from fn after the restart (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "article": "220 0 <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> article follows", "octets": "UGF0aDogZm5BLmhib3gudGVzdCFub3QtZm9yLW1haWwNCkluamVjdGlvbi1JbmZvOiBmbkEuaGJveC50ZXN0DQpGcm9tOiBsYWJAZXhhbXBsZS5pbnZhbGlkDQpOZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpTdWJqZWN0OiBwb3N0ZWQgb24gZm4sIGZlZCB0byBJTk4NCkRhdGU6IFNhdCwgMjYgU2VwIDIwMjYgMTA6MDk6MDAgLTAwMDANCk1lc3NhZ2UtSUQ6IDxpbm4tbGFiLWZuLXBvc3QtYzc2NjVlNy0yMDI2MDkyNlQxMDA5MDBaQGV4YW1wbGUuaW52YWxpZD4NCg0KRnJvbSB0aGUgZm4gSU5OIGludGVyb3AgbGFiLg0K", "ok": true}
--- 71 reread <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> from fn after the restart (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "article": "220 0 <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> article follows", "octets": "UGF0aDogZm5BLmhib3gudGVzdCEhaW5uLmhib3gudGVzdCFsYWIuZXhhbXBsZS5pbnZhbGlkIW5vdC1mb3ItbWFpbA0KRnJvbTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVjdDogaGFuZGVkIHRvIElOTiwgZmVkIG9uIHRvIGZuDQpEYXRlOiBTYXQsIDI2IFNlcCAyMDI2IDEwOjA5OjAwIC0wMDAwDQpNZXNzYWdlLUlEOiA8aW5uLWxhYi1mZWQtYzc2NjVlNy0yMDI2MDkyNlQxMDA5MDBaQGV4YW1wbGUuaW52YWxpZD4NCg0KRnJvbSB0aGUgZm4gSU5OIGludGVyb3AgbGFiLg0K", "ok": true}
--- 72 kill -9 innd (rc=0)
INND-GONE
--- 73 restart innd after the kill (rc=0)
INND-UP pid=1332681
--- 74 after innd's restart, IHAVE <inn-lab-fed-c7665e7-20260926T100900Z@example.invalid> (rc=0)
{"greeting": "200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)", "offer": "435 Duplicate", "result": "", "ok": true}
--- 75 after innd's restart, IHAVE <inn-lab-fn-post-c7665e7-20260926T100900Z@example.invalid> (rc=0)
{"greeting": "200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)", "offer": "435 Duplicate", "result": "", "ok": true}
--- 76 stop the fn owner (rc=0)
OWNER-GONE
--- 77 stop the relay (rc=0)
stopped
--- 78 stop nnrpd (rc=0)
stopped
--- 79 ctlinnd shutdown (rc=0)
--- 80 innd and innfeed are gone (rc=0)
INND-GONE
INNFEED-ALIVE
--- 81 stray lab processes (rc=0)
CLEAN
--- 82 remove the deploy tree (rc=0)
--- 83 release deploy lock (rc=0)
--- 84 the INN install is left in place (rc=0)
/tank/fn/inn/2.7.4
INN-KEPT
```
