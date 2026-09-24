# INN interop lab: 6d3ed90 on hbox

A real InterNetNews server, built from the release tarball pinned below and
left installed on the box, peered with one fn node run from the saved native
image named below through its public entry. This records what ran. INN's
replies are INN's; fn's are fn's; each is quoted from the relay that carried
it. A row that could not run is a skip carrying the reason, never a weaker
scenario under the same name.

## What ran

| fact | value |
| --- | --- |
| commit | `6d3ed90` (6d3ed90bfdcdc2ae70a453152bdfe8045f60abd0) |
| tree | `dev` |
| host | `hbox` |
| started | 2026-09-24T14:22:33Z |
| wall time | 11.5 s |
| gate tool | `tools/inn_lab.py` |
| os | Ubuntu 24.10 kernel=Linux 6.11.0-29-generic arch=x86_64 cores=24 |
| python3 | Python 3.12.7 |
| native image | /tank/fn/gates/qual-1a9dd747-20260924/build/fn-host 60e14e2afe8703574a9d74d89dc632a6c030a668fa261a74d92dd7589bb686d9 |
| native launcher | packaging/fn-native ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142 |
| native core | /tank/fn/gates/qual-1a9dd747-20260924/build/fn-host.core 12ece6cc95f3c4bed7a5d0a1abcfa0e5ea25257855e3f5caed22007c9a7b2bdd (the sidecar beside the image has the same digest) |
| native runtime | /tank/fn/sbcl/bin/sbcl b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5 |
| certificates | not acquired: the lab consumes the saved image it was given, as the v0 matrix's native slice does |
| inn version | INN 2.7.4 |
| inn tarball sha256 | 80fc7e801e1996cb17bb430d104dd9c5b29aa571fd4b29a9c821b4fadb051d3b  inn-2.7.4.tar.gz |
| inn prefix | /tank/fn/inn/2.7.4 |
| ports | innd 11419 (transit), nnrpd 11420 (reader), fn owner 11490, relay 11418 -> innd (fn's peer record names it), relay 11417 -> fn (innfeed.conf names it) |
| acl2version | + ACL2 Version 8.7                                                     + |
| alt | python3.12 Python 3.12.7 |
| host clients | expect=ABSENT, inews=ABSENT, nn=ABSENT, script=/usr/bin/script, slrn=ABSENT, tin=ABSENT, trn=ABSENT |

## Every command

| # | step | rc | first line | s |
| --- | --- | --- | --- | --- |
| 1 | preflight | 0 | `os=Ubuntu 24.10 kernel=Linux 6.11.0-29-generic arch=x86_64 cores=24` | 0.3 |
| 2 | INN install | 0 | `innd=INN 2.7.4` | 0.9 |
| 3 | acquire deploy lock | 0 | `` | 0.3 |
| 4 | ship archive | 0 | `` | 6.9 |
| 5 | make run dir | 0 | `` | 0.3 |
| 6 | install inn.py | 0 | `` | 0.2 |
| 7 | install tap.py | 0 | `` | 0.3 |
| 8 | native subject | 0 | `NATIVE-LAUNCHER packaging/fn-native ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142` | 0.6 |
| 9 | fn store init | 1 | `* Unhandled FNN-HSIG-UNSUPPORTED in thread #<SB-THREAD:THREAD tid=1369092 "main thread" RUNNING` | 0.3 |
| 10 | stray lab processes | 0 | `CLEAN` | 0.2 |
| 11 | remove the deploy tree | 0 | `` | 0.3 |
| 12 | release deploy lock | 0 | `` | 0.3 |
| 13 | the INN install is left in place | 0 | `/tank/fn/inn/2.7.4` | 0.2 |

### Commands in full

1. **preflight** -- `. /etc/os-release 2>/dev/null || true ; echo "os=${PRETTY_NAME:-unknown} kernel=$(uname -sr) arch=$(uname -m) cores=$(nproc 2>/dev/null || echo ?)" ; echo "python3=$(python3 -V 2>&1)" ; for p in python3.9 python3.10 python3.11 python3.12; do ; command -v $p >/dev/null && echo "alt=$p $($p -V 2>&1)" ; done ; for c in slrn tin nn trn inews expect script; do ; printf 'client %s=%s\n' "$c" "$(comma...`
2. **INN install** -- `P=/tank/fn/inn/2.7.4 ; if [ ! -x $P/bin/innd ]; then echo "NO-INN $P"; exit 1; fi ; echo "innd=$($P/bin/innconfval version 2>&1 | head -1)" ; echo "tarball=$(cat $(dirname $P)/src/inn-2.7.4.tar.gz.sha256 2>/dev/null | head -1)" ; for p in 11419 11420 11490 11418 11417; do ; if python3 -c "import socket,sys; s=socket.socket(); s.settimeout(2); sys.exit(0 if s.connect_ex(('127.0.0.1',$p))==0 else...`
3. **acquire deploy lock** -- `mkdir -p $HOME/fn-inn-lab/.locks ; if ! mkdir $HOME/fn-inn-lab/.locks/dev-6d3ed90.lock 2>/dev/null; then ; echo "deploy identity is already active: dev-6d3ed90" ; exit 73 ; fi`
4. **ship archive** -- `git archive 6d3ed90 | tar -x -C $HOME/fn-inn-lab/dev-6d3ed90`
5. **make run dir** -- `mkdir -p $HOME/fn-inn-lab/dev-6d3ed90/gate-run $HOME/fn-inn-lab/dev-6d3ed90/node`
6. **install inn.py** -- `base64 -d > $HOME/fn-inn-lab/dev-6d3ed90/gate-run/inn.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJUaGUgSU5OIGxhYidzIHNvY2tldCBwaGFzZXMuICBO ; byBmbiBtb2R1bGUgaXMgaW1wb3J0ZWQuCgpQeXRob24gMy4xMyByZW1vdmVkIG5udHBsaWIgKFBF ; UCA1OTQpLCBzbyBldmVyeSBOTlRQIGV4Y2hhbmdlIGhlcmUgaXMgYSByYXcKc29ja2V0LCBhbmQg ; ZXZlcnkgYXJ0aWNsZSBpcyBzZW50IGFuZCByZWFkIGFzIG9jdGV0czogYSB0cmFuc2l0IGNsaWVu ; dAp3cm...`
7. **install tap.py** -- `base64 -d > $HOME/fn-inn-lab/dev-6d3ed90/gate-run/tap.py <<'FN_GATE_EOF' ; IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwppbXBvcnQgYmFzZTY0LCBqc29uLCBzb2NrZXQsIHN5cywg ; dGhyZWFkaW5nLCB0aW1lCgpsb2cgPSBvcGVuKHN5cy5hcmd2WzFdLCAiYSIsIGJ1ZmZlcmluZz0x ; KQpsb2NrID0gdGhyZWFkaW5nLkxvY2soKQoKCmRlZiBub3RlKCoqZmllbGRzKToKICAgIHdpdGgg ; bG9jazoKICAgICAgICBsb2cud3JpdGUoanNvbi5kdW1wcyhmaWVsZHMpICsgIlxuIikKCgpkZWYg ; cHVtcC...`
8. **native subject** -- `cd $HOME/fn-inn-lab/dev-6d3ed90 || exit 9 ; image=/tank/fn/gates/qual-1a9dd747-20260924/build/fn-host ; test -x "$image" || { echo "NATIVE-IMAGE-MISSING $image"; exit 4; } ; test -x packaging/fn-native || { echo NATIVE-WRAPPER-MISSING; exit 4; } ; if command -v sha256sum >/dev/null 2>&1; then ; digest() { sha256sum "$1" | awk '{print $1}'; } ; else ; digest() { shasum -a 256 "$1" | awk '{print ...`
9. **fn store init** -- `cd $HOME/fn-inn-lab/dev-6d3ed90 || exit 9 ; env FN_NATIVE_HOST=/tank/fn/gates/qual-1a9dd747-20260924/build/fn-host packaging/fn-native store $HOME/fn-inn-lab/dev-6d3ed90/node/store init fn.letters`
10. **stray lab processes** -- `if pgrep -f -- "$HOME/fn-inn-lab/dev-6d3ed90/" >/dev/null 2>&1; then echo STRAY; pgrep -af -- "$HOME/fn-inn-lab/dev-6d3ed90/"; else echo CLEAN; fi`
11. **remove the deploy tree** -- `rm -rf $HOME/fn-inn-lab/dev-6d3ed90`
12. **release deploy lock** -- `rmdir $HOME/fn-inn-lab/.locks/dev-6d3ed90.lock`
13. **the INN install is left in place** -- `ls -d /tank/fn/inn/2.7.4 && echo INN-KEPT`

## Findings

One row per stated assertion. `held` and `violated` are the two that
DECIDE it; `inconclusive` means this run could not decide it and so
establishes nothing; `not-exercised` and `not-built` mean it was not
reached and why; `limitation` is a scope boundary no run of this
harness crosses.

The process exit is 1 for a violation, 3 for an inconclusive run with no violation, 2 when the gate stopped early, 0 otherwise.

Verdict of this run: **held** (2 held, 31 not-exercised, 1 limitation).

| assertion | verdict | what it says |
| --- | --- | --- |
| ports-free | held | the ports the lab needs were free before it started |
| native-subject-measured | held | the launcher, the image, the core it loads and the runtime were digested before anything ran |
| lab-stopped-early | limitation | the lab stopped early: fn store init failed: * Unhandled FNN-HSIG-UNSUPPORTED in thread #<SB-THREAD:THREAD tid=1369092 "main thread" RUNNING                                             {1200068003}>:   native hybrid signature: OpenSSL 3.5 or newer is required for ML-DSA  Backtrace for: #<SB-THREAD:THREAD tid=1369092 "main thread" RUNNING {1200068003}> 0: (SB-DEBUG::DEBUGGER-DISABLED-HOOK #<FNN-HSIG-UNSUPPORTED {120F03F353}> #<unused argument |
| entry-point-listening | not-exercised | the native owner (`packaging/fn-native operator CONFIG run`) reached LISTENING on the port the lab configured: the run ended without reaching this assertion, so nothing here establishes it. |
| path-identity-set | not-exercised | `policy set path-identity` was accepted, so fn can recognise its own name in a Path (RFC 5537 3.2): the run ended without reaching this assertion, so nothing here establishes it. |
| peer-record-accepted | not-exercised | the fn node holds a peer record naming INN, read back by `peer list`: the run ended without reaching this assertion, so nothing here establishes it. |
| innd-up | not-exercised | innd came up: the run ended without reaching this assertion, so nothing here establishes it. |
| nnrpd-up | not-exercised | nnrpd came up on its port: the run ended without reaching this assertion, so nothing here establishes it. |
| tap-up | not-exercised | the relay listened on both of its ports: the run ended without reaching this assertion, so nothing here establishes it. |
| fn-post-240 | not-exercised | POST to the fn owner drew 340 then 240, and the article reads back by Message-ID: the run ended without reaching this assertion, so nothing here establishes it. |
| fn-feeds-inn | not-exercised | fn's outbound feed offered the posted article to innd by IHAVE, and innd answered 335 then 235: the run ended without reaching this assertion, so nothing here establishes it. |
| inn-serves-fn-article | not-exercised | nnrpd serves the article fn fed, changed only where RFC 5537 3.6 permits a relay to change it (Path, Xref): the run ended without reaching this assertion, so nothing here establishes it. |
| operator-post-feeds-inn | not-exercised | an article submitted through `operator post` reaches innd through fn's outbound feed, injected: Path naming fn, Injection-Date and Injection-Info: the run ended without reaching this assertion, so nothing here establishes it. |
| fn-post-from-invalid-441 | not-exercised | a POST whose From names no address (`From: yue`) draws 441 from fn and is not served (RFC 5536 3.1.2): the run ended without reaching this assertion, so nothing here establishes it. |
| inn-transfer-235 | not-exercised | a hand-made IHAVE into innd draws 335 then 235: the run ended without reaching this assertion, so nothing here establishes it. |
| inn-duplicate-435 | not-exercised | a second IHAVE of an article innd holds draws 435: the run ended without reaching this assertion, so nothing here establishes it. |
| inn-duplicate-435[fn-article] | not-exercised | a second IHAVE of an article innd holds draws 435 (fn-article): the run ended without reaching this assertion, so nothing here establishes it. |
| inn-loop-437 | not-exercised | an article whose Path names INN draws 437 from innd: the run ended without reaching this assertion, so nothing here establishes it. |
| innfeed-feeds-fn | not-exercised | INN's innfeed offered an article to fn and fn took it (238/239 or 335/235): the run ended without reaching this assertion, so nothing here establishes it. |
| fn-serves-inn-article | not-exercised | fn serves the article innfeed transferred with every octet but Path and Xref as it arrived (RFC 5537 3.7: a serving agent alters nothing else): the run ended without reaching this assertion, so nothing here establishes it. |
| fn-serves-own-path-identity | not-exercised | the Path fn serves for an article it took by transit names fn's own path identity (RFC 5537 3.7 step 6, by way of 3.2.1): the run ended without reaching this assertion, so nothing here establishes it. |
| fn-serves-no-sender-xref | not-exercised | fn does not serve the sending server's Xref on an article it took by transit (RFC 5537 3.7 step 7; specs/peering.md 2.3, `Xref` is never stored): the run ended without reaching this assertion, so nothing here establishes it. |
| fn-duplicate-435[inn-article] | not-exercised | a second IHAVE of an article fn holds draws 435 from fn (inn-article): the run ended without reaching this assertion, so nothing here establishes it. |
| fn-duplicate-435[fn-article] | not-exercised | a second IHAVE of an article fn holds draws 435 from fn (fn-article): the run ended without reaching this assertion, so nothing here establishes it. |
| fn-loop-refused | not-exercised | an article whose Path names fn's own path identity is refused by fn (RFC 5537 3.6 step 3; 435 or 437) and is not served: the run ended without reaching this assertion, so nothing here establishes it. |
| fn-term-stopped | not-exercised | the owner exited on SIGTERM: the run ended without reaching this assertion, so nothing here establishes it. |
| innd-survived-fn-term | not-exercised | innd was still running after the fn owner was stopped: the run ended without reaching this assertion, so nothing here establishes it. |
| fn-recover | not-exercised | `operator CONFIG recover` exited 0 after the SIGTERM: the run ended without reaching this assertion, so nothing here establishes it. |
| fn-articles-survived-term[fn-article] | not-exercised | after SIGTERM, recover and restart, fn serves the articles it held byte-identical (fn-article): the run ended without reaching this assertion, so nothing here establishes it. |
| fn-articles-survived-term[inn-article] | not-exercised | after SIGTERM, recover and restart, fn serves the articles it held byte-identical (inn-article): the run ended without reaching this assertion, so nothing here establishes it. |
| innd-died | not-exercised | innd died on SIGKILL, so the control really cut: the run ended without reaching this assertion, so nothing here establishes it. |
| innd-restarted | not-exercised | innd came back after the SIGKILL: the run ended without reaching this assertion, so nothing here establishes it. |
| inn-history-survived-kill[inn-article] | not-exercised | after innd's SIGKILL and restart, a second IHAVE of an article it acknowledged before draws 435 (inn-article): the run ended without reaching this assertion, so nothing here establishes it. |
| inn-history-survived-kill[fn-article] | not-exercised | after innd's SIGKILL and restart, a second IHAVE of an article it acknowledged before draws 435 (fn-article): the run ended without reaching this assertion, so nothing here establishes it. |

## What was NOT exercised

- the lab stopped early: fn store init failed: * Unhandled FNN-HSIG-UNSUPPORTED in thread #<SB-THREAD:THREAD tid=1369092 "main thread" RUNNING
                                            {1200068003}>:
  native hybrid signature: OpenSSL 3.5 or newer is required for ML-DSA

Backtrace for: #<SB-THREAD:THREAD tid=1369092 "main thread" RUNNING {1200068003}>
0: (SB-DEBUG::DEBUGGER-DISABLED-HOOK #<FNN-HSIG-UNSUPPORTED {120F03F353}> #<unused argument
- the native owner (`packaging/fn-native operator CONFIG run`) reached LISTENING on the port the lab configured: the run ended without reaching this assertion, so nothing here establishes it.
- `policy set path-identity` was accepted, so fn can recognise its own name in a Path (RFC 5537 3.2): the run ended without reaching this assertion, so nothing here establishes it.
- the fn node holds a peer record naming INN, read back by `peer list`: the run ended without reaching this assertion, so nothing here establishes it.
- innd came up: the run ended without reaching this assertion, so nothing here establishes it.
- nnrpd came up on its port: the run ended without reaching this assertion, so nothing here establishes it.
- the relay listened on both of its ports: the run ended without reaching this assertion, so nothing here establishes it.
- POST to the fn owner drew 340 then 240, and the article reads back by Message-ID: the run ended without reaching this assertion, so nothing here establishes it.
- fn's outbound feed offered the posted article to innd by IHAVE, and innd answered 335 then 235: the run ended without reaching this assertion, so nothing here establishes it.
- nnrpd serves the article fn fed, changed only where RFC 5537 3.6 permits a relay to change it (Path, Xref): the run ended without reaching this assertion, so nothing here establishes it.
- an article submitted through `operator post` reaches innd through fn's outbound feed, injected: Path naming fn, Injection-Date and Injection-Info: the run ended without reaching this assertion, so nothing here establishes it.
- a POST whose From names no address (`From: yue`) draws 441 from fn and is not served (RFC 5536 3.1.2): the run ended without reaching this assertion, so nothing here establishes it.
- a hand-made IHAVE into innd draws 335 then 235: the run ended without reaching this assertion, so nothing here establishes it.
- a second IHAVE of an article innd holds draws 435: the run ended without reaching this assertion, so nothing here establishes it.
- a second IHAVE of an article innd holds draws 435 (fn-article): the run ended without reaching this assertion, so nothing here establishes it.
- an article whose Path names INN draws 437 from innd: the run ended without reaching this assertion, so nothing here establishes it.
- INN's innfeed offered an article to fn and fn took it (238/239 or 335/235): the run ended without reaching this assertion, so nothing here establishes it.
- fn serves the article innfeed transferred with every octet but Path and Xref as it arrived (RFC 5537 3.7: a serving agent alters nothing else): the run ended without reaching this assertion, so nothing here establishes it.
- the Path fn serves for an article it took by transit names fn's own path identity (RFC 5537 3.7 step 6, by way of 3.2.1): the run ended without reaching this assertion, so nothing here establishes it.
- fn does not serve the sending server's Xref on an article it took by transit (RFC 5537 3.7 step 7; specs/peering.md 2.3, `Xref` is never stored): the run ended without reaching this assertion, so nothing here establishes it.
- a second IHAVE of an article fn holds draws 435 from fn (inn-article): the run ended without reaching this assertion, so nothing here establishes it.
- a second IHAVE of an article fn holds draws 435 from fn (fn-article): the run ended without reaching this assertion, so nothing here establishes it.
- an article whose Path names fn's own path identity is refused by fn (RFC 5537 3.6 step 3; 435 or 437) and is not served: the run ended without reaching this assertion, so nothing here establishes it.
- the owner exited on SIGTERM: the run ended without reaching this assertion, so nothing here establishes it.
- innd was still running after the fn owner was stopped: the run ended without reaching this assertion, so nothing here establishes it.
- `operator CONFIG recover` exited 0 after the SIGTERM: the run ended without reaching this assertion, so nothing here establishes it.
- after SIGTERM, recover and restart, fn serves the articles it held byte-identical (fn-article): the run ended without reaching this assertion, so nothing here establishes it.
- after SIGTERM, recover and restart, fn serves the articles it held byte-identical (inn-article): the run ended without reaching this assertion, so nothing here establishes it.
- innd died on SIGKILL, so the control really cut: the run ended without reaching this assertion, so nothing here establishes it.
- innd came back after the SIGKILL: the run ended without reaching this assertion, so nothing here establishes it.
- after innd's SIGKILL and restart, a second IHAVE of an article it acknowledged before draws 435 (inn-article): the run ended without reaching this assertion, so nothing here establishes it.
- after innd's SIGKILL and restart, a second IHAVE of an article it acknowledged before draws 435 (fn-article): the run ended without reaching this assertion, so nothing here establishes it.

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

(the relay carried nothing)

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
NATIVE-IMAGE /tank/fn/gates/qual-1a9dd747-20260924/build/fn-host 60e14e2afe8703574a9d74d89dc632a6c030a668fa261a74d92dd7589bb686d9
NATIVE-SIDECAR /tank/fn/gates/qual-1a9dd747-20260924/build/fn-host.core 12ece6cc95f3c4bed7a5d0a1abcfa0e5ea25257855e3f5caed22007c9a7b2bdd
NATIVE-CORE /tank/fn/gates/qual-1a9dd747-20260924/build/fn-host.core 12ece6cc95f3c4bed7a5d0a1abcfa0e5ea25257855e3f5caed22007c9a7b2bdd
NATIVE-RUNTIME /tank/fn/sbcl/bin/sbcl b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5
--- 9 fn store init (rc=1)
* Unhandled FNN-HSIG-UNSUPPORTED in thread #<SB-THREAD:THREAD tid=1369092 "main thread" RUNNING
                                            {1200068003}>:
  native hybrid signature: OpenSSL 3.5 or newer is required for ML-DSA

Backtrace for: #<SB-THREAD:THREAD tid=1369092 "main thread" RUNNING {1200068003}>
0: (SB-DEBUG::DEBUGGER-DISABLED-HOOK #<FNN-HSIG-UNSUPPORTED {120F03F353}> #<unused argument> :QUIT T)
1: (SB-DEBUG::RUN-HOOK SB-EXT:*INVOKE-DEBUGGER-HOOK* #<FNN-HSIG-UNSUPPORTED {120F03F353}>)
2: (INVOKE-DEBUGGER #<FNN-HSIG-UNSUPPORTED {120F03F353}>)
3: (ERROR #<FNN-HSIG-UNSUPPORTED {120F03F353}>)
4: ((FLET SB-THREAD::WITH-MUTEX-THUNK :IN FNN-HSIG-INITIALIZE))
5: ((FLET "WITHOUT-INTERRUPTS-BODY-" :IN SB-THREAD::FAST-CALL-WITH-MUTEX))
6: (SB-THREAD::FAST-CALL-WITH-MUTEX #<FUNCTION (FLET SB-THREAD::WITH-MUTEX-THUNK :IN FNN-HSIG-INITIALIZE) {B801BE054B}> #<SB-THREAD:MUTEX "fn ML-DSA provider initialization" taken owner=main thread>)
--- 10 stray lab processes (rc=0)
CLEAN
--- 11 remove the deploy tree (rc=0)
--- 12 release deploy lock (rc=0)
--- 13 the INN install is left in place (rc=0)
/tank/fn/inn/2.7.4
INN-KEPT
```
