# INN interop lab: 8a5f502 on hbox

A real InterNetNews server, built from the release tarball pinned below and
left installed on the box, peered with one fn node run from the saved native
image named below through its public entry. This records what ran. INN's
replies are INN's; fn's are fn's; each is quoted from the relay that carried
it. A row that could not run is a skip carrying the reason, never a weaker
scenario under the same name.

## Reading this record (lane T13-inn, by hand; everything below it is the tool's)

The subject is the saved native image built from `dabebb84` at
`/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host`
(the image the hbox node runs), through `packaging/fn-native` from the shipped
tree. Its launcher execs `/tank/fn/gates/freeze-dev-28fb4bd0/build/fn-host.core`,
whose digest equals the sidecar's; both are in the table. The previous run
(`inn-lab-f4e8272-2026-09-20.md`) had the development Python reader on the fn
side; this is the first with the native owner, and its fn side is new in every
row. The commit row is the tree that shipped the launcher and the lab's two
drivers, not the image's source.

Invocation, from `build/lanes/t13-inn` at `8a5f502a`:

    python3 tools/inn_lab.py HEAD --host hbox \
        --native-image /tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host \
        --native-openssl-prefix /tank/fn/toolchains/openssl-3.5.8 \
        --evidence planning/evidence/inn-lab-dabebb84-2026-09-22.md

What holds, each with the other server's reply from the relay: fn's feed
delivers a POSTed article to innd (`IHAVE`, `335 Send it`, `235 Article
transferred OK`); INN's innfeed delivers to fn (`CHECK` `238`, `TAKETHIS`
`239`); a second offer is `435` both ways (`435 Duplicate` from innd, `435
duplicate` from fn); a Path loop is `437 Unwanted site inn.hbox.test in path`
from innd and `335` then `437 transfer rejected; path loop` from fn, which does
not serve it afterwards (`430`); innd's history survives its SIGKILL (both
articles `435` after the restart); fn's articles survive SIGTERM, `recover`
and a restart byte-identical.

The octets, header by header:

- fn's POST input against what fn serves: fn added `Path`
  (`fnA.hbox.test!not-for-mail`), `Injection-Date` and `Injection-Info`; nothing
  else, body identical. What fn's feed sent innd is byte-identical to what fn
  serves.
- What fn serves against what INN's nnrpd serves for the same article: `Path`
  differs (INN prepended `inn.hbox.test!`) and INN added `Xref`
  (`inn.hbox.test fn.letters:<n>`); every other header and the body identical.
  So, from what the agent POSTed to what INN serves: `Path`, `Injection-Date`,
  `Injection-Info` (fn's injection) and `Xref` (INN's). RFC 5537 3.6/3.7 permit
  a relay and a server to change Path and Xref; the injection fields are 3.5's.
- The article INN fed to fn: what fn serves is byte-identical to what innfeed
  sent and to what nnrpd serves, INN's `Path` and `Xref` included.

Three fn findings, by name, each `violated` below with its reply:

1. **`operator post` relays an article with no Path.** The offline submission
   verb stores the payload as given (no Path, no Injection-Info) and the
   owner's outbound feed offers it unchanged; innd answers `335 Send it`, then
   `437 Missing "Path" header field`, a permanent refusal. Articles POSTed over
   NNTP are injected and cross; articles submitted with `operator post` (the
   verb `tests/test_native_peering.py` and the v0 matrix post with) never reach
   an INN peer. In the lane's exploration before the tool ran, the same article
   over a streaming peer record drew `238` then `439 <id>` from innd.
2. **fn serves a transit article without its own path identity in Path.** The
   article innfeed sent is served to readers with `Path:
   inn.hbox.test!lab.example.invalid!not-for-mail`; RFC 5537 3.7 step 6 has a
   serving agent update Path as 3.2.1 describes (INN served
   `inn.hbox.test!fnA.hbox.test!not-for-mail` for fn's article).
   specs/peering.md 2.3 renders the prepend when an article leaves for a peer;
   the reader path is not covered there, and whether the outbound render
   happens could not be observed (the only peer is the article's source).
3. **fn serves the sender's Xref.** The same article is served with INN's
   `Xref: inn.hbox.test fn.letters:<n>`, INN's article numbers; RFC 5537 3.7
   step 7 has a serving agent remove it, and specs/peering.md 2.3 says `Xref`
   is never stored.

Not established here: the relay is a hop neither server would have; fn's
outbound rendering of a transit article to a second peer (one peer only); no
TLS or AUTHINFO on either transit connection; the image's provenance beyond
its digests. fn's feed opened one connection to innd that carried nothing
(the greeting only) before the one that carried both articles; the transcript
shows it and nothing here says why.

## What ran

| fact | value |
| --- | --- |
| commit | `8a5f502` (8a5f502a16e6d47b8af07814b93f53a8ce73eafc) |
| tree | `dev` |
| host | `hbox` |
| started | 2026-09-22T21:26:21Z |
| wall time | 46.6 s |
| gate tool | `tools/inn_lab.py` |
| os | Ubuntu 24.10 kernel=Linux 6.11.0-29-generic arch=x86_64 cores=24 |
| python3 | Python 3.12.7 |
| native image | /tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host 21ba38c1a66d96c32c8e50269b852cabd07ae15548306781aafa084cb0e6af32 |
| native launcher | packaging/fn-native ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142 |
| native core | /tank/fn/gates/freeze-dev-28fb4bd0/build/fn-host.core 6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf (the sidecar beside the image has the same digest) |
| native runtime | /tank/fn/sbcl/bin/sbcl b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5 |
| certificates | not acquired: the lab consumes the saved image it was given, as the v0 matrix's native slice does |
| inn version | INN 2.7.4 |
| inn tarball sha256 | 80fc7e801e1996cb17bb430d104dd9c5b29aa571fd4b29a9c821b4fadb051d3b  inn-2.7.4.tar.gz |
| inn prefix | /tank/fn/inn/2.7.4 |
| ports | innd 11419 (transit), nnrpd 11420 (reader), fn owner 11490, relay 11418 -> innd (fn's peer record names it), relay 11417 -> fn (innfeed.conf names it) |
| inn server | innd pid 3314727 on port 11419, nnrpd on port 11420 |
| fn node | native owner pid 3316856 on port 11490 (after-term), store $HOME/fn-inn-lab/dev-8a5f502/node/store |
| fn path identity | fnA.hbox.test (rc=0, accepted operator policy) |
| fn peer record | inn path-identity=inn.hbox.test address=127.0.0.1 port=11418 security=clear inbound=fn.* outbound=fn.* auth=source-address:127.0.0.1 |
| fn post | POST='340 send article to be posted' article='240 article received OK' ARTICLE='220 0 <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> article follows' |
| fn feed to inn | IHAVE: 335 Send it / 235 Article transferred OK; the octets fed are identical to what fn serves |
| inn read of fn's article | GROUP='211 14 1 14 fn.letters' ARTICLE='220 0 <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> article' absent='430 No such article' |
| fn post vs fn served | only in the second: injection-date, injection-info, path; body identical; the injected Path is `fnA.hbox.test!not-for-mail` |
| fn served vs inn served | changed: path; only in the second: xref; body identical; Path fn=`fnA.hbox.test!not-for-mail` inn=`inn.hbox.test!fnA.hbox.test!not-for-mail`; Xref inn=`inn.hbox.test fn.letters:14` |
| operator post feed | post rc=0 (accepted operator post ACCEPTED); IHAVE: 335 Send it / 437 Missing "Path" header field; the fed article's Path is ABSENT |
| inn control | MODE STREAM='203 Streaming permitted' IHAVE='335 Send it' transfer='235 Article transferred OK' duplicate='435 Duplicate' loop='437 Unwanted site inn.hbox.test in path' CHECK(new)='238 <inn-lab-absent-8a5f502-20260922T212621Z@example.invalid> Send it' CHECK(dup)='438 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> Duplicate' |
| innfeed to fn | CHECK+TAKETHIS: 238 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> / 239 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> |
| inn served vs fn served | byte-identical; Path inn=`inn.hbox.test!lab.example.invalid!not-for-mail` fn=`inn.hbox.test!lab.example.invalid!not-for-mail`; Xref inn=`inn.hbox.test fn.letters:15` fn=`inn.hbox.test fn.letters:15` |
| duplicates | inn-article: IHAVE='435 duplicate'; fn-article: IHAVE='435 duplicate' |
| fn loop | IHAVE='335 send it; end with <CR-LF>.<CR-LF>' transfer='437 transfer rejected; path loop' ARTICLE after='430 no article with that message-id' |
| fn term | OWNER-GONE; recover rc=0; transactions=3 articles=3 staging-orphans=0 unsigned-legacy-experiment; fn-article identical, inn-article identical |
| innd cut | inn-article IHAVE='435 Duplicate'; fn-article IHAVE='435 Duplicate' |
| acl2version | + ACL2 Version 8.7                                                     + |
| alt | python3.12 Python 3.12.7 |
| host clients | expect=ABSENT, inews=ABSENT, nn=ABSENT, script=/usr/bin/script, slrn=ABSENT, tin=ABSENT, trn=ABSENT |

## Every command

| # | step | rc | first line | s |
| --- | --- | --- | --- | --- |
| 1 | preflight | 0 | `os=Ubuntu 24.10 kernel=Linux 6.11.0-29-generic arch=x86_64 cores=24` | 0.5 |
| 2 | INN install | 0 | `innd=INN 2.7.4` | 0.5 |
| 3 | acquire deploy lock | 0 | `` | 0.4 |
| 4 | ship archive | 0 | `` | 3.7 |
| 5 | make run dir | 0 | `` | 0.3 |
| 6 | install inn.py | 0 | `` | 0.4 |
| 7 | install tap.py | 0 | `` | 0.3 |
| 8 | native subject | 0 | `NATIVE-LAUNCHER packaging/fn-native ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142` | 0.6 |
| 9 | fn store init | 0 | `initialized /home/hbox/fn-inn-lab/dev-8a5f502/node/store` | 0.5 |
| 10 | fn.toml | 0 | `[store]` | 0.4 |
| 11 | fn policy set path-identity | 0 | `configured generation=2 record=00000002.cfg verification=VERIFIED` | 0.5 |
| 12 | fn peer record for INN | 0 | `configured generation=3 record=00000003.cfg verification=VERIFIED` | 0.5 |
| 13 | fn peer list | 0 | `inn path-identity=inn.hbox.test address=127.0.0.1 port=11418 security=clear inbound=fn.* outbound=fn.* auth=source-address:127.0.0.1` | 0.4 |
| 14 | fn status before the owner starts | 0 | `transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment` | 0.5 |
| 15 | INN news user | 0 | `user=hbox group=hbox` | 0.4 |
| 16 | INN directories | 0 | `` | 0.3 |
| 17 | install inn.conf | 0 | `` | 0.3 |
| 18 | install incoming.conf | 0 | `` | 0.3 |
| 19 | install newsfeeds | 0 | `` | 0.4 |
| 20 | install innfeed.conf | 0 | `` | 0.3 |
| 21 | install readers.conf | 0 | `` | 0.4 |
| 22 | truncate innfeed's log | 0 | `` | 0.4 |
| 23 | INN history cold start | 0 | `active` | 0.4 |
| 24 | inncheck | 1 | `/tank/fn/inn/2.7.4/etc/newsfeeds:4: ME has exclusions` | 0.4 |
| 25 | INN inn.conf as written | 0 | `# fn INN interop lab -- generated by tools/inn_lab.py.  Loopback only.` | 0.4 |
| 26 | INN incoming.conf as written | 0 | `# fn INN interop lab -- INN accepts transit from the fn node over loopback.` | 0.3 |
| 27 | INN newsfeeds as written | 0 | `# fn INN interop lab -- generated by tools/inn_lab.py.` | 0.4 |
| 28 | INN innfeed.conf as written | 0 | `# fn INN interop lab -- the outbound half: INN offers fn.* to the fn node,` | 0.4 |
| 29 | INN readers.conf as written | 0 | `# fn INN interop lab -- nnrpd reads back what innd stored.  Loopback only.` | 0.4 |
| 30 | start innd | 0 | `INND-UP pid=3314727` | 1.4 |
| 31 | ctlinnd newgroup fn.letters | 0 | `Group status unchanged` | 0.4 |
| 32 | ctlinnd newgroup fn.test | 0 | `Group status unchanged` | 0.4 |
| 33 | INN active | 0 | `control 0000000000 0000000001 n` | 0.4 |
| 34 | ctlinnd reload newsfeeds | 0 | `Ok` | 3.4 |
| 35 | start nnrpd | 0 | `NNRPD-UP pid=3315065` | 0.5 |
| 36 | start the relay | 0 | `TAP-UP pid=3315128` | 1.5 |
| 37 | start the native owner (main) | 0 | `LISTENING 11490` | 1.4 |
| 38 | fn CAPABILITIES | 0 | `{"greeting": "200 fn-nntp experimental server ready", "status": "101 capability list follows", "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE ACTIVE.TIMES` | 0.3 |
| 39 | install fn-post.article | 0 | `` | 0.4 |
| 40 | POST <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> to the fn owner | 0 | `{"greeting": "200 fn-nntp experimental server ready", "post": "340 send article to be posted", "result": "240 article received OK", "article": "220 0 <inn-lab-fn-post-8a5f502-20260922T212621Z@example.` | 0.4 |
| 41 | relay log: fn's feed offers <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> to innd | 0 | `IHAVE on 11418>11419: 335 Send it / 235 Article transferred OK` | 0.4 |
| 42 | read <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> back from INN's nnrpd | 0 | `{"greeting": "200 inn.hbox.test InterNetNews NNRP server INN 2.7.4 ready (posting ok)", "group": "211 14 1 14 fn.letters", "article": "220 0 <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> ` | 0.4 |
| 43 | IHAVE <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> into innd again | 0 | `{"greeting": "200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)", "offer": "435 Duplicate", "result": "", "ok": true}` | 0.5 |
| 44 | install fn-operator.article | 0 | `` | 0.4 |
| 45 | operator post <inn-lab-fn-operator-8a5f502-20260922T212621Z@example.invalid> | 0 | `accepted operator post ACCEPTED` | 0.4 |
| 46 | relay log: fn's feed offers <inn-lab-fn-operator-8a5f502-20260922T212621Z@example.invalid> to innd | 0 | `IHAVE on 11418>11419: 335 Send it / 437 Missing "Path" header field` | 0.4 |
| 47 | install fed.article | 0 | `` | 0.3 |
| 48 | install inn-loop.article | 0 | `` | 0.4 |
| 49 | IHAVE <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> into innd | 0 | `{"greeting": "200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)", "mode_stream": "203 Streaming permitted", "offer": "335 Send it", "transfer": "235 Article transferred OK", "duplic` | 0.4 |
| 50 | INN history for <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> | 0 | `@050000000007000000000000000F00000000@` | 0.3 |
| 51 | ctlinnd flush fn | 0 | `Ok` | 0.5 |
| 52 | relay log: innfeed offers <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> to fn | 0 | `CHECK+TAKETHIS on 11417>11490: 238 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> / 239 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>` | 0.4 |
| 53 | innfeed log | 0 | `2026-09-22T17:26:39.730065-04:00 hbox innfeed[3314991]: ME config: adding default value for key dynamic-backlog-high: 50.000000` | 0.4 |
| 54 | read <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> back from the fn owner | 0 | `{"greeting": "200 fn-nntp experimental server ready", "article": "220 0 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> article follows", "octets": "UGF0aDogaW5uLmhib3gudGVzdCFsYWIuZXhhbXBsZS5p` | 0.3 |
| 55 | read <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> back from INN's nnrpd | 0 | `{"greeting": "200 inn.hbox.test InterNetNews NNRP server INN 2.7.4 ready (posting ok)", "group": "211 15 1 15 fn.letters", "article": "220 0 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> arti` | 0.5 |
| 56 | IHAVE <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> to fn again | 0 | `{"greeting": "200 fn-nntp experimental server ready", "offer": "435 duplicate", "result": "", "after": "220 0 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> article follows", "octets": "UGF0aD` | 0.4 |
| 57 | IHAVE <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> to fn again | 0 | `{"greeting": "200 fn-nntp experimental server ready", "offer": "435 duplicate", "result": "", "after": "220 0 <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> article follows", "octets": "UG` | 0.4 |
| 58 | install fn-loop.article | 0 | `` | 0.3 |
| 59 | IHAVE <inn-lab-fn-loop-8a5f502-20260922T212621Z@example.invalid> (Path names fnA.hbox.test) to fn | 0 | `{"greeting": "200 fn-nntp experimental server ready", "offer": "335 send it; end with <CR-LF>.<CR-LF>", "result": "437 transfer rejected; path loop", "after": "430 no article with that message-id", "o` | 0.5 |
| 60 | SIGTERM the fn owner | 0 | `OWNER-GONE` | 1.5 |
| 61 | innd survived the fn owner's stop | 0 | `Server running` | 0.3 |
| 62 | owner log (main) | 0 | `CONTROL /home/hbox/fn-inn-lab/dev-8a5f502/node/control.sock` | 0.3 |
| 63 | fn recover | 0 | `recovered transactions=3 articles=3 staging-orphans=0 anchor=none checkpoint=none` | 0.5 |
| 64 | fn status after recover | 0 | `transactions=3 articles=3 staging-orphans=0 unsigned-legacy-experiment` | 0.4 |
| 65 | start the native owner (after-term) | 0 | `LISTENING 11490` | 1.3 |
| 66 | reread <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> from fn after the restart | 0 | `{"greeting": "200 fn-nntp experimental server ready", "article": "220 0 <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> article follows", "octets": "UGF0aDogZm5BLmhib3gudGVzdCFub3QtZm9yLW1h` | 0.4 |
| 67 | reread <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> from fn after the restart | 0 | `{"greeting": "200 fn-nntp experimental server ready", "article": "220 0 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> article follows", "octets": "UGF0aDogaW5uLmhib3gudGVzdCFsYWIuZXhhbXBsZS5p` | 0.5 |
| 68 | kill -9 innd | 0 | `INND-GONE` | 0.4 |
| 69 | restart innd after the kill | 0 | `INND-UP pid=3317101` | 1.4 |
| 70 | after innd's restart, IHAVE <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> | 0 | `{"greeting": "200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)", "offer": "435 Duplicate", "result": "", "ok": true}` | 0.4 |
| 71 | after innd's restart, IHAVE <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> | 0 | `{"greeting": "200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)", "offer": "435 Duplicate", "result": "", "ok": true}` | 0.4 |
| 72 | stop the fn owner | 0 | `OWNER-GONE` | 1.4 |
| 73 | stop the relay | 0 | `stopped` | 0.3 |
| 74 | stop nnrpd | 0 | `stopped` | 0.4 |
| 75 | ctlinnd shutdown | 0 | `` | 0.3 |
| 76 | innd and innfeed are gone | 0 | `INND-GONE` | 1.3 |
| 77 | stray lab processes | 0 | `CLEAN` | 0.5 |
| 78 | remove the deploy tree | 0 | `` | 0.3 |
| 79 | release deploy lock | 0 | `` | 0.3 |
| 80 | the INN install is left in place | 0 | `/tank/fn/inn/2.7.4` | 0.4 |

### Commands in full

1. **preflight** -- `. /etc/os-release 2>/dev/null || true ; echo "os=${PRETTY_NAME:-unknown} kernel=$(uname -sr) arch=$(uname -m) cores=$(nproc 2>/dev/null || echo ?)" ; echo "python3=$(python3 -V 2>&1)" ; for p in python3.9 python3.10 python3.11 python3.12; do ; command -v $p >/dev/null && echo "alt=$p $($p -V 2>&1)" ; done ; for c in slrn tin nn trn inews expect script; do ; printf 'client %s=%s\n' "$c" "$(comma...`
2. **INN install** -- `P=/tank/fn/inn/2.7.4 ; if [ ! -x $P/bin/innd ]; then echo "NO-INN $P"; exit 1; fi ; echo "innd=$($P/bin/innconfval version 2>&1 | head -1)" ; echo "tarball=$(cat $(dirname $P)/src/inn-2.7.4.tar.gz.sha256 2>/dev/null | head -1)" ; for p in 11419 11420 11490 11418 11417; do ; if python3 -c "import socket,sys; s=socket.socket(); s.settimeout(2); sys.exit(0 if s.connect_ex(('127.0.0.1',$p))==0 else...`
3. **acquire deploy lock** -- `mkdir -p $HOME/fn-inn-lab/.locks ; if ! mkdir $HOME/fn-inn-lab/.locks/dev-8a5f502.lock 2>/dev/null; then ; echo "deploy identity is already active: dev-8a5f502" ; exit 73 ; fi`
4. **ship archive** -- `git archive 8a5f502 | tar -x -C $HOME/fn-inn-lab/dev-8a5f502`
5. **make run dir** -- `mkdir -p $HOME/fn-inn-lab/dev-8a5f502/gate-run $HOME/fn-inn-lab/dev-8a5f502/node`
6. **install inn.py** -- `base64 -d > $HOME/fn-inn-lab/dev-8a5f502/gate-run/inn.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJUaGUgSU5OIGxhYidzIHNvY2tldCBwaGFzZXMuICBO ; byBmbiBtb2R1bGUgaXMgaW1wb3J0ZWQuCgpQeXRob24gMy4xMyByZW1vdmVkIG5udHBsaWIgKFBF ; UCA1OTQpLCBzbyBldmVyeSBOTlRQIGV4Y2hhbmdlIGhlcmUgaXMgYSByYXcKc29ja2V0LCBhbmQg ; ZXZlcnkgYXJ0aWNsZSBpcyBzZW50IGFuZCByZWFkIGFzIG9jdGV0czogYSB0cmFuc2l0IGNsaWVu ; dAp3cm...`
7. **install tap.py** -- `base64 -d > $HOME/fn-inn-lab/dev-8a5f502/gate-run/tap.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwppbXBvcnQgYmFzZTY0LCBqc29uLCBzb2NrZXQsIHN5cywg ; dGhyZWFkaW5nLCB0aW1lCgpsb2cgPSBvcGVuKHN5cy5hcmd2WzFdLCAiYSIsIGJ1ZmZlcmluZz0x ; KQpsb2NrID0gdGhyZWFkaW5nLkxvY2soKQoKCmRlZiBub3RlKCoqZmllbGRzKToKICAgIHdpdGgg ; bG9jazoKICAgICAgICBsb2cud3JpdGUoanNvbi5kdW1wcyhmaWVsZHMpICsgIlxuIikKCgpkZWYg ; cHVtcC...`
8. **native subject** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; image=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host ; test -x "$image" || { echo "NATIVE-IMAGE-MISSING $image"; exit 4; } ; test -x packaging/fn-native || { echo NATIVE-WRAPPER-MISSING; exit 4; } ; if command -v sha256sum >/dev/null 2>&1; then ; digest() { sha256sum "$1" | awk '{print $1}'; } ; else ;...`
9. **fn store init** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native store $HOME/fn-inn-lab/dev-8a5f502/node/store init fn.letters`
10. **fn.toml** -- `cat > $HOME/fn-inn-lab/dev-8a5f502/node/fn.toml <<FN_TOML ; [store] ; path = "$HOME/fn-inn-lab/dev-8a5f502/node/store" ; [listener] ; host = "127.0.0.1" ; port = 11490 ; [posting] ; enabled = true ; [control] ; path = "$HOME/fn-inn-lab/dev-8a5f502/node/control.sock" ; FN_TOML ; cat $HOME/fn-inn-lab/dev-8a5f502/node/fn.toml`
11. **fn policy set path-identity** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-inn-lab/dev-8a5f502/node/fn.toml policy set path-identity fnA.hbox.test`
12. **fn peer record for INN** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-inn-lab/dev-8a5f502/node/fn.toml peer add inn inn.hbox.test 127.0.0.1 11418 'fn.*' 'fn.*' 127.0.0.1 false`
13. **fn peer list** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-inn-lab/dev-8a5f502/node/fn.toml peer list`
14. **fn status before the owner starts** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-inn-lab/dev-8a5f502/node/fn.toml status`
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
36. **start the relay** -- `: > $HOME/fn-inn-lab/dev-8a5f502/gate-run/tap.log ; nohup python3 $HOME/fn-inn-lab/dev-8a5f502/gate-run/tap.py $HOME/fn-inn-lab/dev-8a5f502/gate-run/tap.log 11418:11419 11417:11490 > $HOME/fn-inn-lab/dev-8a5f502/gate-run/tap.stdout 2>&1 < /dev/null & ; echo $! > $HOME/fn-inn-lab/dev-8a5f502/gate-run/tap.pid ; for i in $(seq 1 20); do ; up=0 ; for p in 11418 11417; do ; python3 -c "import socket...`
37. **start the native owner (main)** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; rm -f $HOME/fn-inn-lab/dev-8a5f502/node/owner-main.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-inn-lab/dev-8a5f502/node/fn.toml run > $HOME/fn-inn-lab/dev-8a5f502/node/owner-main....`
38. **fn CAPABILITIES** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; python3 $HOME/fn-inn-lab/dev-8a5f502/gate-run/inn.py caps --port 11490`
39. **install fn-post.article** -- `base64 -d > $HOME/fn-inn-lab/dev-8a5f502/gate-run/fn-post.article <<'FN_GATE_EOF' ; RnJvbTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVj ; dDogcG9zdGVkIG9uIGZuLCBmZWQgdG8gSU5ODQpEYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDIxOjI2 ; OjIxIC0wMDAwDQpNZXNzYWdlLUlEOiA8aW5uLWxhYi1mbi1wb3N0LThhNWY1MDItMjAyNjA5MjJU ; MjEyNjIxWkBleGFtcGxlLmludmFsaWQ+DQoNCkZyb20gdGhlIGZuIElOTiBpbnRlcm9wIGxhYi4N...`
40. **POST <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> to the fn owner** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; python3 $HOME/fn-inn-lab/dev-8a5f502/gate-run/inn.py post --port 11490 --msgid '<inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid>' --file $HOME/fn-inn-lab/dev-8a5f502/gate-run/fn-post.article`
41. **relay log: fn's feed offers <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> to innd** -- `cat $HOME/fn-inn-lab/dev-8a5f502/gate-run/tap.log (polled 1 times, pair 11418>11419)`
42. **read <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> back from INN's nnrpd** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; python3 $HOME/fn-inn-lab/dev-8a5f502/gate-run/inn.py read --port 11420 --group fn.letters --msgid '<inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid>' --absent '<inn-lab-absent-8a5f502-20260922T212621Z@example.invalid>'`
43. **IHAVE <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> into innd again** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; python3 $HOME/fn-inn-lab/dev-8a5f502/gate-run/inn.py offer --port 11419 --msgid '<inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid>' --file $HOME/fn-inn-lab/dev-8a5f502/gate-run/fn-post.article`
44. **install fn-operator.article** -- `base64 -d > $HOME/fn-inn-lab/dev-8a5f502/gate-run/fn-operator.article <<'FN_GATE_EOF' ; RnJvbTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVj ; dDogc3VibWl0dGVkIHRocm91Z2ggb3BlcmF0b3IgcG9zdA0KRGF0ZTogVHVlLCAyMiBTZXAgMjAy ; NiAyMToyNjoyMSAtMDAwMA0KTWVzc2FnZS1JRDogPGlubi1sYWItZm4tb3BlcmF0b3ItOGE1ZjUw ; Mi0yMDI2MDkyMlQyMTI2MjFaQGV4YW1wbGUuaW52YWxpZD4NCg0KRnJvbSB0aGUgZm4gSU5O...`
45. **operator post <inn-lab-fn-operator-8a5f502-20260922T212621Z@example.invalid>** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-inn-lab/dev-8a5f502/node/fn.toml post --message-id '<inn-lab-fn-operator-8a5f502-20260922T212621Z@example.invalid>' --payload $HOME/fn-inn-lab/dev-...`
46. **relay log: fn's feed offers <inn-lab-fn-operator-8a5f502-20260922T212621Z@example.invalid> to innd** -- `cat $HOME/fn-inn-lab/dev-8a5f502/gate-run/tap.log (polled 1 times, pair 11418>11419)`
47. **install fed.article** -- `base64 -d > $HOME/fn-inn-lab/dev-8a5f502/gate-run/fed.article <<'FN_GATE_EOF' ; UGF0aDogbGFiLmV4YW1wbGUuaW52YWxpZCFub3QtZm9yLW1haWwNCkZyb206IGxhYkBleGFtcGxl ; LmludmFsaWQNCk5ld3Nncm91cHM6IGZuLmxldHRlcnMNClN1YmplY3Q6IGhhbmRlZCB0byBJTk4s ; IGZlZCBvbiB0byBmbg0KRGF0ZTogVHVlLCAyMiBTZXAgMjAyNiAyMToyNjoyMSAtMDAwMA0KTWVz ; c2FnZS1JRDogPGlubi1sYWItZmVkLThhNWY1MDItMjAyNjA5MjJUMjEyNjIxWkBleGFtcGxlLmlu ; d...`
48. **install inn-loop.article** -- `base64 -d > $HOME/fn-inn-lab/dev-8a5f502/gate-run/inn-loop.article <<'FN_GATE_EOF' ; UGF0aDogaW5uLmhib3gudGVzdCFsYWIuZXhhbXBsZS5pbnZhbGlkIW5vdC1mb3ItbWFpbA0KRnJv ; bTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVjdDog ; YSBQYXRoIHRoYXQgbmFtZXMgSU5ODQpEYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDIxOjI2OjIxIC0w ; MDAwDQpNZXNzYWdlLUlEOiA8aW5uLWxhYi1sb29wLThhNWY1MDItMjAyNjA5MjJUMjEyNjIxWkB...`
49. **IHAVE <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> into innd** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; python3 $HOME/fn-inn-lab/dev-8a5f502/gate-run/inn.py ihave --port 11419 --msgid '<inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>' --file $HOME/fn-inn-lab/dev-8a5f502/gate-run/fed.article --loop-msgid '<inn-lab-loop-8a5f502-20260922T212621Z@example.invalid>' --loop-file $HOME/fn-inn-lab/dev-8a5f502/gate-run/inn-loop.article --absent '<inn-lab-ab...`
50. **INN history for <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>** -- `/tank/fn/inn/2.7.4/bin/grephistory '<inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>' 2>&1 | head -3`
51. **ctlinnd flush fn** -- `/tank/fn/inn/2.7.4/bin/ctlinnd -t 10 flush fn 2>&1 || true`
52. **relay log: innfeed offers <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> to fn** -- `cat $HOME/fn-inn-lab/dev-8a5f502/gate-run/tap.log (polled 1 times, pair 11417>11490)`
53. **innfeed log** -- `tail -20 /tank/fn/inn/2.7.4/log/innfeed.log 2>/dev/null; grep -h 'innfeed' /var/log/syslog 2>/dev/null | tail -8 || true`
54. **read <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> back from the fn owner** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; python3 $HOME/fn-inn-lab/dev-8a5f502/gate-run/inn.py fetch --port 11490 --msgid '<inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>'`
55. **read <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> back from INN's nnrpd** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; python3 $HOME/fn-inn-lab/dev-8a5f502/gate-run/inn.py read --port 11420 --group fn.letters --msgid '<inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>' --absent '<inn-lab-absent-8a5f502-20260922T212621Z@example.invalid>'`
56. **IHAVE <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> to fn again** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; python3 $HOME/fn-inn-lab/dev-8a5f502/gate-run/inn.py offer --port 11490 --msgid '<inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>' --file $HOME/fn-inn-lab/dev-8a5f502/gate-run/fed.article --read`
57. **IHAVE <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> to fn again** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; python3 $HOME/fn-inn-lab/dev-8a5f502/gate-run/inn.py offer --port 11490 --msgid '<inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid>' --file $HOME/fn-inn-lab/dev-8a5f502/gate-run/fn-post.article --read`
58. **install fn-loop.article** -- `base64 -d > $HOME/fn-inn-lab/dev-8a5f502/gate-run/fn-loop.article <<'FN_GATE_EOF' ; UGF0aDogZm5BLmhib3gudGVzdCFsYWIuZXhhbXBsZS5pbnZhbGlkIW5vdC1mb3ItbWFpbA0KRnJv ; bTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVjdDog ; YSBQYXRoIHRoYXQgbmFtZXMgZm4NCkRhdGU6IFR1ZSwgMjIgU2VwIDIwMjYgMjE6MjY6MjEgLTAw ; MDANCk1lc3NhZ2UtSUQ6IDxpbm4tbGFiLWZuLWxvb3AtOGE1ZjUwMi0yMDI2MDkyMlQyMTI2MjFa...`
59. **IHAVE <inn-lab-fn-loop-8a5f502-20260922T212621Z@example.invalid> (Path names fnA.hbox.test) to fn** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; python3 $HOME/fn-inn-lab/dev-8a5f502/gate-run/inn.py offer --port 11490 --msgid '<inn-lab-fn-loop-8a5f502-20260922T212621Z@example.invalid>' --file $HOME/fn-inn-lab/dev-8a5f502/gate-run/fn-loop.article --read`
60. **SIGTERM the fn owner** -- `kill -TERM 3315196 2>/dev/null || true ; for i in $(seq 1 60); do kill -0 3315196 2>/dev/null || break; sleep 1; done ; if kill -0 3315196 2>/dev/null; then kill -9 3315196; echo "OWNER-KILLED-AFTER-60S"; else echo OWNER-GONE; fi`
61. **innd survived the fn owner's stop** -- `/tank/fn/inn/2.7.4/bin/ctlinnd -t 5 mode 2>&1 | head -2`
62. **owner log (main)** -- `tail -12 $HOME/fn-inn-lab/dev-8a5f502/node/owner-main.log`
63. **fn recover** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-inn-lab/dev-8a5f502/node/fn.toml recover`
64. **fn status after recover** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; env FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-inn-lab/dev-8a5f502/node/fn.toml status`
65. **start the native owner (after-term)** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; rm -f $HOME/fn-inn-lab/dev-8a5f502/node/owner-after-term.log ; nohup env FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 FN_NATIVE_HOST=/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host packaging/fn-native operator $HOME/fn-inn-lab/dev-8a5f502/node/fn.toml run > $HOME/fn-inn-lab/dev-8a5f502/node/owner...`
66. **reread <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> from fn after the restart** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; python3 $HOME/fn-inn-lab/dev-8a5f502/gate-run/inn.py fetch --port 11490 --msgid '<inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid>'`
67. **reread <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> from fn after the restart** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; python3 $HOME/fn-inn-lab/dev-8a5f502/gate-run/inn.py fetch --port 11490 --msgid '<inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>'`
68. **kill -9 innd** -- `kill -9 3314727 2>/dev/null || true ; for i in $(seq 1 20); do kill -0 3314727 2>/dev/null || break; sleep 1; done ; kill -0 3314727 2>/dev/null && echo INND-ALIVE || echo INND-GONE ; rm -f /tank/fn/inn/2.7.4/run/innd.pid /tank/fn/inn/2.7.4/run/control.ctl`
69. **restart innd after the kill** -- `P=/tank/fn/inn/2.7.4 ; nohup $P/bin/innd -d >> $P/log/innd-stdout.log 2>&1 < /dev/null & ; for i in $(seq 1 60); do ; if $P/bin/ctlinnd -t 2 mode 2>/dev/null | grep -q 'Server running'; then ; echo "INND-UP pid=$(cat $P/run/innd.pid 2>/dev/null)"; exit 0 ; fi ; sleep 1 ; done ; echo INND-TIMEOUT; tail -20 $P/log/innd-stdout.log; exit 1`
70. **after innd's restart, IHAVE <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; python3 $HOME/fn-inn-lab/dev-8a5f502/gate-run/inn.py offer --port 11419 --msgid '<inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>' --file $HOME/fn-inn-lab/dev-8a5f502/gate-run/fed.article`
71. **after innd's restart, IHAVE <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid>** -- `cd $HOME/fn-inn-lab/dev-8a5f502 || exit 9 ; python3 $HOME/fn-inn-lab/dev-8a5f502/gate-run/inn.py offer --port 11419 --msgid '<inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid>' --file $HOME/fn-inn-lab/dev-8a5f502/gate-run/fn-post.article`
72. **stop the fn owner** -- `kill -TERM 3316856 2>/dev/null || true ; for i in $(seq 1 60); do kill -0 3316856 2>/dev/null || break; sleep 1; done ; if kill -0 3316856 2>/dev/null; then kill -9 3316856; echo "OWNER-KILLED-AFTER-60S"; else echo OWNER-GONE; fi`
73. **stop the relay** -- `kill 3315128 2>/dev/null || true; echo stopped`
74. **stop nnrpd** -- `kill 3315065 2>/dev/null || true; echo stopped`
75. **ctlinnd shutdown** -- `/tank/fn/inn/2.7.4/bin/ctlinnd -t 5 shutdown 'inn lab done' 2>&1 || true`
76. **innd and innfeed are gone** -- `for i in $(seq 1 20); do ; kill -0 3317101 2>/dev/null || break; sleep 1 ; done ; kill -0 3317101 2>/dev/null && echo INND-ALIVE || echo INND-GONE ; pid=$(cat /tank/fn/inn/2.7.4/run/innfeed.pid 2>/dev/null || echo -1) ; kill -0 $pid 2>/dev/null && echo INNFEED-ALIVE || echo INNFEED-GONE`
77. **stray lab processes** -- `if pgrep -f -- "$HOME/fn-inn-lab/dev-8a5f502/" >/dev/null 2>&1; then echo STRAY; pgrep -af -- "$HOME/fn-inn-lab/dev-8a5f502/"; else echo CLEAN; fi`
78. **remove the deploy tree** -- `rm -rf $HOME/fn-inn-lab/dev-8a5f502`
79. **release deploy lock** -- `rmdir $HOME/fn-inn-lab/.locks/dev-8a5f502.lock`
80. **the INN install is left in place** -- `ls -d /tank/fn/inn/2.7.4 && echo INN-KEPT`

## Findings

One row per stated assertion. `held` and `violated` are the two that
DECIDE it; `inconclusive` means this run could not decide it and so
establishes nothing; `not-exercised` and `not-built` mean it was not
reached and why; `limitation` is a scope boundary no run of this
harness crosses.

The process exit is 1 for a violation, 3 for an inconclusive run with no violation, 2 when the gate stopped early, 0 otherwise.

Verdict of this run: **violated** (29 held, 3 violated).

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
| operator-post-feeds-inn | violated | `operator post` accepted <inn-lab-fn-operator-8a5f502-20260922T212621Z@example.invalid> (rc=0) and fn's feed offered it to innd, which answered IHAVE: 335 Send it / 437 Missing "Path" header field. The octets fed carry NO Path header: `operator post` stores the payload as submitted, with no injection (no Path, no Injection-Info; RFC 5536 3.1.6 makes Path mandatory), and the outbound feed relays it without prepending fn's path identity (RFC 5537 3.6), so INN has no Path to accept it under. |
| inn-transfer-235 | held | a hand-made IHAVE into innd draws 335 then 235 |
| inn-duplicate-435 | held | a second IHAVE of an article innd holds draws 435 |
| inn-loop-437 | held | an article whose Path names INN draws 437 from innd |
| innfeed-feeds-fn | held | INN's innfeed offered an article to fn and fn took it (238/239 or 335/235) |
| fn-serves-inn-article | held | fn serves the article innfeed transferred with every octet but Path and Xref as it arrived (RFC 5537 3.7: a serving agent alters nothing else) |
| fn-serves-own-path-identity | violated | fn serves <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> to a reader with `Path: inn.hbox.test!lab.example.invalid!not-for-mail`, which does not name its own path identity fnA.hbox.test: the Path it took by transit is served unchanged, where RFC 5537 3.7 step 6 has a serving agent update it as 3.2.1 describes (INN, the other serving agent here, served `inn.hbox.test!fnA.hbox.test!not-for-mail` for fn's article) |
| fn-serves-no-sender-xref | violated | fn serves <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> with the sender's `Xref: inn.hbox.test fn.letters:15` -- INN's article numbers, not fn's -- where RFC 5537 3.7 step 7 has a serving agent remove it and specs/peering.md 2.3 says `Xref` is never stored |
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

- `operator post` accepted <inn-lab-fn-operator-8a5f502-20260922T212621Z@example.invalid> (rc=0) and fn's feed offered it to innd, which answered IHAVE: 335 Send it / 437 Missing "Path" header field. The octets fed carry NO Path header: `operator post` stores the payload as submitted, with no injection (no Path, no Injection-Info; RFC 5536 3.1.6 makes Path mandatory), and the outbound feed relays it without prepending fn's path identity (RFC 5537 3.6), so INN has no Path to accept it under.
- fn serves <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> to a reader with `Path: inn.hbox.test!lab.example.invalid!not-for-mail`, which does not name its own path identity fnA.hbox.test: the Path it took by transit is served unchanged, where RFC 5537 3.7 step 6 has a serving agent update it as 3.2.1 describes (INN, the other serving agent here, served `inn.hbox.test!fnA.hbox.test!not-for-mail` for fn's article)
- fn serves <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> with the sender's `Xref: inn.hbox.test fn.letters:15` -- INN's article numbers, not fn's -- where RFC 5537 3.7 step 7 has a serving agent remove it and specs/peering.md 2.3 says `Xref` is never stored

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
C: IHAVE <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid>
S: 335 Send it
C:   Path: fnA.hbox.test!not-for-mail
C:   Injection-Date: Tue, 22 Sep 2026 21:26:47 +0000
C:   Injection-Info: fnA.hbox.test
C:   From: lab@example.invalid
C:   Newsgroups: fn.letters
C:   Subject: posted on fn, fed to INN
C:   Date: Tue, 22 Sep 2026 21:26:21 -0000
C:   Message-ID: <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid>
C:   
C:   From the fn INN interop lab.
C: .
S: 235 Article transferred OK
C: IHAVE <inn-lab-fn-operator-8a5f502-20260922T212621Z@example.invalid>
S: 335 Send it
C:   From: lab@example.invalid
C:   Newsgroups: fn.letters
C:   Subject: submitted through operator post
C:   Date: Tue, 22 Sep 2026 21:26:21 -0000
C:   Message-ID: <inn-lab-fn-operator-8a5f502-20260922T212621Z@example.invalid>
C:   
C:   From the fn INN interop lab.
C: .
S: 437 Missing "Path" header field
```

### innfeed -> fn (relay 11417>11490), connection 1

```
S: 200 fn-nntp experimental server ready
C: MODE STREAM
S: 203 streaming permitted
C: CHECK <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>
S: 238 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>
C: TAKETHIS <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>
C:   Path: inn.hbox.test!lab.example.invalid!not-for-mail
C:   From: lab@example.invalid
C:   Newsgroups: fn.letters
C:   Subject: handed to INN, fed on to fn
C:   Date: Tue, 22 Sep 2026 21:26:21 -0000
C:   Message-ID: <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>
C:   Xref: inn.hbox.test fn.letters:15
C:   
C:   From the fn INN interop lab.
C: .
S: 239 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>
```

### innfeed -> fn (relay 11417>11490), connection 2

```
S: 200 fn-nntp experimental server ready
C: MODE STREAM
S: 203 streaming permitted
C: QUIT
S: 205 closing connection
```

### innfeed -> fn (relay 11417>11490), connection 3

```
S: 200 fn-nntp experimental server ready
C: MODE STREAM
S: 203 streaming permitted
```

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
NATIVE-LAUNCHER packaging/fn-native ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142
NATIVE-IMAGE /tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host 21ba38c1a66d96c32c8e50269b852cabd07ae15548306781aafa084cb0e6af32
NATIVE-SIDECAR /tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/fn-host.core 6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf
NATIVE-CORE /tank/fn/gates/freeze-dev-28fb4bd0/build/fn-host.core 6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf
NATIVE-RUNTIME /tank/fn/sbcl/bin/sbcl b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5
--- 9 fn store init (rc=0)
initialized /home/hbox/fn-inn-lab/dev-8a5f502/node/store
--- 10 fn.toml (rc=0)
[store]
path = "/home/hbox/fn-inn-lab/dev-8a5f502/node/store"

[listener]
host = "127.0.0.1"
port = 11490

[posting]
enabled = true

[control]
path = "/home/hbox/fn-inn-lab/dev-8a5f502/node/control.sock"
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
accepted operator STATUS
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
INND-UP pid=3314727
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
fn.letters 0000000013 0000000001 y
fn.test 0000000000 0000000001 y
--- 34 ctlinnd reload newsfeeds (rc=0)
Ok
3314991
--- 35 start nnrpd (rc=0)
NNRPD-UP pid=3315065
--- 36 start the relay (rc=0)
TAP-UP pid=3315128
--- 37 start the native owner (main) (rc=0)
LISTENING 11490
OWNER-UP pid=3315196
--- 38 fn CAPABILITIES (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "status": "101 capability list follows", "capabilities": ["VERSION 2", "READER", "POST", "OVER MSGID", "HDR", "NEWNEWS", "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT", "IMPLEMENTATION fn-nntp-lab", "IHAVE", "STREAMING"], "ok": true}
--- 39 install fn-post.article (rc=0)
--- 40 POST <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> to the fn owner (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "post": "340 send article to be posted", "result": "240 article received OK", "article": "220 0 <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> article follows", "octets": "UGF0aDogZm5BLmhib3gudGVzdCFub3QtZm9yLW1haWwNCkluamVjdGlvbi1EYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDIxOjI2OjQ3ICswMDAwDQpJbmplY3Rpb24tSW5mbzogZm5BLmhib3gudGVzdA0KRnJvbTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVjdDogcG9zdGVkIG9uIGZuLCBmZWQgdG8gSU5ODQpEYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDIxOjI2OjIxIC0wMDAwDQpNZXNzYWdlLUlEOiA8aW5uLWxhYi1mbi1wb3N0LThhNWY1MDItMjAyNjA5MjJUMjEyNjIxWkBleGFtcGxlLmludmFsaWQ+DQoNCkZyb20gdGhlIGZuIElOTiBpbnRlcm9wIGxhYi4NCg==", "ok": true}
--- 41 relay log: fn's feed offers <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> to innd (rc=0)
IHAVE on 11418>11419: 335 Send it / 235 Article transferred OK
--- 42 read <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> back from INN's nnrpd (rc=0)
{"greeting": "200 inn.hbox.test InterNetNews NNRP server INN 2.7.4 ready (posting ok)", "group": "211 14 1 14 fn.letters", "article": "220 0 <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> article", "octets": "UGF0aDogaW5uLmhib3gudGVzdCFmbkEuaGJveC50ZXN0IW5vdC1mb3ItbWFpbA0KSW5qZWN0aW9uLURhdGU6IFR1ZSwgMjIgU2VwIDIwMjYgMjE6MjY6NDcgKzAwMDANCkluamVjdGlvbi1JbmZvOiBmbkEuaGJveC50ZXN0DQpGcm9tOiBsYWJAZXhhbXBsZS5pbnZhbGlkDQpOZXdzZ3JvdXBzOiBmbi5sZXR0ZXJzDQpTdWJqZWN0OiBwb3N0ZWQgb24gZm4sIGZlZCB0byBJTk4NCkRhdGU6IFR1ZSwgMjIgU2VwIDIwMjYgMjE6MjY6MjEgLTAwMDANCk1lc3NhZ2UtSUQ6IDxpbm4tbGFiLWZuLXBvc3QtOGE1ZjUwMi0yMDI2MDkyMlQyMTI2MjFaQGV4YW1wbGUuaW52YWxpZD4NClhyZWY6IGlubi5oYm94LnRlc3QgZm4ubGV0dGVyczoxNA0KDQpGcm9tIHRoZSBmbiBJTk4gaW50ZXJvcCBsYWIuDQo=", "absent": "430 No such article", "ok": true}
--- 43 IHAVE <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> into innd again (rc=0)
{"greeting": "200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)", "offer": "435 Duplicate", "result": "", "ok": true}
--- 44 install fn-operator.article (rc=0)
--- 45 operator post <inn-lab-fn-operator-8a5f502-20260922T212621Z@example.invalid> (rc=0)
accepted operator post ACCEPTED
--- 46 relay log: fn's feed offers <inn-lab-fn-operator-8a5f502-20260922T212621Z@example.invalid> to innd (rc=0)
IHAVE on 11418>11419: 335 Send it / 437 Missing "Path" header field
--- 47 install fed.article (rc=0)
--- 48 install inn-loop.article (rc=0)
--- 49 IHAVE <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> into innd (rc=0)
{"greeting": "200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)", "mode_stream": "203 Streaming permitted", "offer": "335 Send it", "transfer": "235 Article transferred OK", "duplicate": "435 Duplicate", "duplicate_transfer": "", "loop_offer": "335 Send it", "loop_result": "437 Unwanted site inn.hbox.test in path", "check_unknown": "238 <inn-lab-absent-8a5f502-20260922T212621Z@example.invalid> Send it", "check_duplicate": "438 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> Duplicate", "ok": true}
--- 50 INN history for <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> (rc=0)
@050000000007000000000000000F00000000@
--- 51 ctlinnd flush fn (rc=0)
Ok
--- 52 relay log: innfeed offers <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> to fn (rc=0)
CHECK+TAKETHIS on 11417>11490: 238 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> / 239 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>
--- 53 innfeed log (rc=0)
2026-09-22T17:26:39.730065-04:00 hbox innfeed[3314991]: ME config: adding default value for key dynamic-backlog-high: 50.000000
2026-09-22T17:26:41.730687-04:00 hbox innfeed[3314991]: fn:0 cxnsleep connect: Connection refused
2026-09-22T17:26:41.730929-04:00 hbox innfeed[3314991]: fn spooling no active connections
2026-09-22T17:26:44.641667-04:00 hbox innd: innfeed! exit 0 elapsed 2 pid 3314732
2026-09-22T17:26:46.758052-04:00 hbox innfeed[3314991]: fn:0 connected
2026-09-22T17:26:46.758275-04:00 hbox innfeed[3314991]: fn remote MODE STREAM
2026-09-22T17:26:46.758361-04:00 hbox innfeed[3314991]: fn checkpoint seconds 5 spooled 0 on_close 0 sleeping 0
2026-09-22T17:26:46.758432-04:00 hbox innfeed[3314991]: fn final seconds 5 spooled 0 on_close 0 sleeping 0
--- 54 read <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> back from the fn owner (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "article": "220 0 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> article follows", "octets": "UGF0aDogaW5uLmhib3gudGVzdCFsYWIuZXhhbXBsZS5pbnZhbGlkIW5vdC1mb3ItbWFpbA0KRnJvbTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVjdDogaGFuZGVkIHRvIElOTiwgZmVkIG9uIHRvIGZuDQpEYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDIxOjI2OjIxIC0wMDAwDQpNZXNzYWdlLUlEOiA8aW5uLWxhYi1mZWQtOGE1ZjUwMi0yMDI2MDkyMlQyMTI2MjFaQGV4YW1wbGUuaW52YWxpZD4NClhyZWY6IGlubi5oYm94LnRlc3QgZm4ubGV0dGVyczoxNQ0KDQpGcm9tIHRoZSBmbiBJTk4gaW50ZXJvcCBsYWIuDQo=", "ok": true}
--- 55 read <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> back from INN's nnrpd (rc=0)
{"greeting": "200 inn.hbox.test InterNetNews NNRP server INN 2.7.4 ready (posting ok)", "group": "211 15 1 15 fn.letters", "article": "220 0 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> article", "octets": "UGF0aDogaW5uLmhib3gudGVzdCFsYWIuZXhhbXBsZS5pbnZhbGlkIW5vdC1mb3ItbWFpbA0KRnJvbTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVjdDogaGFuZGVkIHRvIElOTiwgZmVkIG9uIHRvIGZuDQpEYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDIxOjI2OjIxIC0wMDAwDQpNZXNzYWdlLUlEOiA8aW5uLWxhYi1mZWQtOGE1ZjUwMi0yMDI2MDkyMlQyMTI2MjFaQGV4YW1wbGUuaW52YWxpZD4NClhyZWY6IGlubi5oYm94LnRlc3QgZm4ubGV0dGVyczoxNQ0KDQpGcm9tIHRoZSBmbiBJTk4gaW50ZXJvcCBsYWIuDQo=", "absent": "430 No such article", "ok": true}
--- 56 IHAVE <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> to fn again (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "offer": "435 duplicate", "result": "", "after": "220 0 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> article follows", "octets": "UGF0aDogaW5uLmhib3gudGVzdCFsYWIuZXhhbXBsZS5pbnZhbGlkIW5vdC1mb3ItbWFpbA0KRnJvbTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVjdDogaGFuZGVkIHRvIElOTiwgZmVkIG9uIHRvIGZuDQpEYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDIxOjI2OjIxIC0wMDAwDQpNZXNzYWdlLUlEOiA8aW5uLWxhYi1mZWQtOGE1ZjUwMi0yMDI2MDkyMlQyMTI2MjFaQGV4YW1wbGUuaW52YWxpZD4NClhyZWY6IGlubi5oYm94LnRlc3QgZm4ubGV0dGVyczoxNQ0KDQpGcm9tIHRoZSBmbiBJTk4gaW50ZXJvcCBsYWIuDQo=", "ok": true}
--- 57 IHAVE <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> to fn again (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "offer": "435 duplicate", "result": "", "after": "220 0 <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> article follows", "octets": "UGF0aDogZm5BLmhib3gudGVzdCFub3QtZm9yLW1haWwNCkluamVjdGlvbi1EYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDIxOjI2OjQ3ICswMDAwDQpJbmplY3Rpb24tSW5mbzogZm5BLmhib3gudGVzdA0KRnJvbTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVjdDogcG9zdGVkIG9uIGZuLCBmZWQgdG8gSU5ODQpEYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDIxOjI2OjIxIC0wMDAwDQpNZXNzYWdlLUlEOiA8aW5uLWxhYi1mbi1wb3N0LThhNWY1MDItMjAyNjA5MjJUMjEyNjIxWkBleGFtcGxlLmludmFsaWQ+DQoNCkZyb20gdGhlIGZuIElOTiBpbnRlcm9wIGxhYi4NCg==", "ok": true}
--- 58 install fn-loop.article (rc=0)
--- 59 IHAVE <inn-lab-fn-loop-8a5f502-20260922T212621Z@example.invalid> (Path names fnA.hbox.test) to fn (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "offer": "335 send it; end with <CR-LF>.<CR-LF>", "result": "437 transfer rejected; path loop", "after": "430 no article with that message-id", "octets": "", "ok": true}
--- 60 SIGTERM the fn owner (rc=0)
OWNER-GONE
--- 61 innd survived the fn owner's stop (rc=0)
Server running
Allowing remote connections
--- 62 owner log (main) (rc=0)
CONTROL /home/hbox/fn-inn-lab/dev-8a5f502/node/control.sock
LISTENING 11490
accepted operator run
--- 63 fn recover (rc=0)
recovered transactions=3 articles=3 staging-orphans=0 anchor=none checkpoint=none
accepted operator RECOVER
--- 64 fn status after recover (rc=0)
transactions=3 articles=3 staging-orphans=0 unsigned-legacy-experiment
accepted operator STATUS
--- 65 start the native owner (after-term) (rc=0)
LISTENING 11490
OWNER-UP pid=3316856
--- 66 reread <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> from fn after the restart (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "article": "220 0 <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> article follows", "octets": "UGF0aDogZm5BLmhib3gudGVzdCFub3QtZm9yLW1haWwNCkluamVjdGlvbi1EYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDIxOjI2OjQ3ICswMDAwDQpJbmplY3Rpb24tSW5mbzogZm5BLmhib3gudGVzdA0KRnJvbTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVjdDogcG9zdGVkIG9uIGZuLCBmZWQgdG8gSU5ODQpEYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDIxOjI2OjIxIC0wMDAwDQpNZXNzYWdlLUlEOiA8aW5uLWxhYi1mbi1wb3N0LThhNWY1MDItMjAyNjA5MjJUMjEyNjIxWkBleGFtcGxlLmludmFsaWQ+DQoNCkZyb20gdGhlIGZuIElOTiBpbnRlcm9wIGxhYi4NCg==", "ok": true}
--- 67 reread <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> from fn after the restart (rc=0)
{"greeting": "200 fn-nntp experimental server ready", "article": "220 0 <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> article follows", "octets": "UGF0aDogaW5uLmhib3gudGVzdCFsYWIuZXhhbXBsZS5pbnZhbGlkIW5vdC1mb3ItbWFpbA0KRnJvbTogbGFiQGV4YW1wbGUuaW52YWxpZA0KTmV3c2dyb3VwczogZm4ubGV0dGVycw0KU3ViamVjdDogaGFuZGVkIHRvIElOTiwgZmVkIG9uIHRvIGZuDQpEYXRlOiBUdWUsIDIyIFNlcCAyMDI2IDIxOjI2OjIxIC0wMDAwDQpNZXNzYWdlLUlEOiA8aW5uLWxhYi1mZWQtOGE1ZjUwMi0yMDI2MDkyMlQyMTI2MjFaQGV4YW1wbGUuaW52YWxpZD4NClhyZWY6IGlubi5oYm94LnRlc3QgZm4ubGV0dGVyczoxNQ0KDQpGcm9tIHRoZSBmbiBJTk4gaW50ZXJvcCBsYWIuDQo=", "ok": true}
--- 68 kill -9 innd (rc=0)
INND-GONE
--- 69 restart innd after the kill (rc=0)
INND-UP pid=3317101
--- 70 after innd's restart, IHAVE <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid> (rc=0)
{"greeting": "200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)", "offer": "435 Duplicate", "result": "", "ok": true}
--- 71 after innd's restart, IHAVE <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid> (rc=0)
{"greeting": "200 inn.hbox.test InterNetNews server INN 2.7.4 ready (transit mode)", "offer": "435 Duplicate", "result": "", "ok": true}
--- 72 stop the fn owner (rc=0)
OWNER-GONE
--- 73 stop the relay (rc=0)
stopped
--- 74 stop nnrpd (rc=0)
stopped
--- 75 ctlinnd shutdown (rc=0)
--- 76 innd and innfeed are gone (rc=0)
INND-GONE
INNFEED-ALIVE
--- 77 stray lab processes (rc=0)
CLEAN
--- 78 remove the deploy tree (rc=0)
--- 79 release deploy lock (rc=0)
--- 80 the INN install is left in place (rc=0)
/tank/fn/inn/2.7.4
INN-KEPT
```
