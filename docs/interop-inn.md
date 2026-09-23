# The INN interop lab

A real [InterNetNews](https://www.eyrie.org/~eagle/software/inn/) server on
one side of the wire and an fn node on the other, on hbox, over loopback. The
fn node is the saved native image through its public entry
(`packaging/fn-native`), or the lab does not run (D07); the development
Python reader it fell back to before 2026-09-22 is retired.
It exists because every other harness in this tree tests fn against fn: the
deploy gate against one fn node, the two-node gate against two. Legacy Usenet
is the one peer whose replies we do not write, and the only place a
misreading of RFC 3977 or RFC 4644 shows up as a refusal rather than as
agreement with ourselves.

Reading order: [specs/peering.md](../specs/peering.md) §1–§3 for what fn will
speak, §5 for the scenario table this lab implements a subset of, and
[tools/deploy_gate.py](../tools/deploy_gate.py) for the machinery
`tools/inn_lab.py` subclasses.

The install is the lab. It is built once and left on the box; each run ships
one fn commit beside it (for the launcher and the lab's two drivers), stands
up a fresh store from the named image, and tears only that down.

## What runs where

| | value |
| --- | --- |
| host | `hbox` (`ssh hbox`) |
| INN | 2.7.4, from the release tarball, sha256 in [`tests/inn/pin.json`](../tests/inn/pin.json) |
| prefix | `/tank/fn/inn/2.7.4`, owned by the ordinary user; no root, no system path |
| source | `/tank/fn/inn/src/inn-2.7.4` (unpacked tarball, with `configure.log`, `make.log`, `install.log`) |
| fn | the saved native image named by `--native-image`; the commit's tree is shipped per run to `--lab-root/<tree>-<rev>` (default `~/fn-inn-lab`) for `packaging/fn-native` and the drivers |
| relay | `tap.py`, shipped with the drivers: a byte-transparent loopback relay on each transit connection that logs every octet both ways, because innd and innfeed log counts and not replies |

### The port scheme

Five ports in the 114xx decade, which is this lab's: the deployed node has
1119, the v0 matrix 11190/11191 and other lanes 113xx, so a connection to the
wrong one fails loudly instead of being answered by someone else's server.

| port | who | why that number |
| --- | --- | --- |
| `11419` | `innd` — transit: `IHAVE`, `CHECK`, `TAKETHIS` | NNTP's 119 in the lab's decade |
| `11420` | `nnrpd` — the reader daemon, read-back only | 119's reader sibling 120 |
| `11490` | the native fn owner's listener | 90, as the matrix's fn nodes are |
| `11418` | the relay into `innd`; fn's peer record names this port | just below innd's |
| `11417` | the relay into the fn owner; `innfeed.conf` names this port | just below that |

`nnrpd -D -p` listens on every address (`0.0.0.0:11420` on hbox, measured
2026-09-22), not only `127.0.0.1`; `readers.conf` admits loopback only.

## Running it

    cd <worktree>
    python3 tools/inn_lab.py HEAD --host hbox \
        --native-image /tank/fn/gates/<freeze>/build/images/<source>/fn-host \
        --native-openssl-prefix /tank/fn/toolchains/openssl-3.5.8

    # keep the deploy tree on the box for a post mortem
    python3 tools/inn_lab.py HEAD --host hbox --native-image IMG --keep

    # the whole thing against a stand-in INN and a stand-in image, no ssh
    python3 -m unittest tests.test_inn_lab

The v0 matrix runs it for its `F-INN` rows with `--backend native-operator
--native-image IMG --inn`, and reads each row from the lab's findings file.

The evidence lands in `planning/evidence/inn-lab-<rev>-<date>.md`, in the
deploy gate's shape: what ran (with the launcher, image, core and runtime
digests), every command with its exit code and first line, one finding per
assertion, what was *not* exercised and why, the relay's transcript of both
transit connections, and the raw output.

The lab writes INN's five configuration files on every run, so the
configuration is the tool's and not a box's accumulated state. It starts
`innd`, `nnrpd`, the relay and the fn owner, stops only the pids it
started, leaves the install and its spool in place, and removes the fn deploy
tree unless `--keep`.

## How INN was built

No root is needed: the prefix is user-owned and the news user is the ordinary
user. Builds on hbox go through `swarm-build`, which is the cgroup with the
enforced memory cap — hbox is shared.

    cd /tank/fn/inn/src
    curl -sSLO https://downloads.isc.org/isc/inn/inn-2.7.4.tar.gz
    sha256sum inn-2.7.4.tar.gz    # 80fc7e80...b051d3b, see tests/inn/pin.json
    tar xzf inn-2.7.4.tar.gz && cd inn-2.7.4
    swarm-build ./configure --prefix=/tank/fn/inn/2.7.4 \
        --with-news-user=hbox --with-news-group=hbox --with-news-master=hbox \
        --with-openssl=no --without-sasl --with-berkeleydb=no \
        --without-perl --with-sendmail=/usr/sbin/sendmail
    swarm-build make -j4
    make install

Three of those flags are worth their line. `--without-perl`: hbox has Perl
5.38 but `configure` cannot link `libperl` (`checking for perl_alloc... no`),
and nothing in the lab uses the Perl filter hooks. `--with-berkeleydb=no`:
the lab uses `hisv6` history and `tradindexed` overview, neither of which
needs BDB (`ovdb` would). `--with-openssl=no --without-sasl`: no TLS and no
SASL — recorded gaps, not oversights.

The history database is cold-started once, and the lab redoes it only if it
is absent:

    : > /tank/fn/inn/2.7.4/db/history
    /tank/fn/inn/2.7.4/bin/makedbz -i -f /tank/fn/inn/2.7.4/db/history
    cd /tank/fn/inn/2.7.4/db && for e in dir hash index; do mv history.n.$e history.$e; done

Groups are created through the running server, not by editing `active`:

    /tank/fn/inn/2.7.4/bin/ctlinnd newgroup fn.letters y $(id -un)
    /tank/fn/inn/2.7.4/bin/ctlinnd newgroup fn.test    y $(id -un)

## INN's configuration, verbatim

These are the five files `tools/inn_lab.py` writes into
`/tank/fn/inn/2.7.4/etc/` on every run, with `{...}` filled from the port
scheme above. They are reproduced here so a reader can audit the lab without
running it; the tool is the authority and the evidence file records what was
actually on disk.

### `inn.conf`

```
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
maxartsize:             1000000
artcutoff:              0
wanttrash:              false
nnrpdposthost:          none
runasuser:              hbox
runasgroup:             hbox
pathnews:               /tank/fn/inn/2.7.4
logipaddr:              true
xrefslave:              false
```

`artcutoff: 0` turns off the "too old" rejection so a scenario can replay an
article; `wanttrash: false` means an article for a group INN does not carry
is refused rather than filed in `junk`, which is what makes an out-of-scope
offer visible as a reply code.

### `incoming.conf`

```
streaming:      true
max-connections: 8

peer fn {
    hostname:        127.0.0.1
    patterns:        fn.*
    streaming:       true
    max-connections: 4
}
```

**A correction to specs/peering.md §5.** That section writes
`identity: fnA` in the peer block. `incoming.conf` has no `identity` key and
`inncheck` rejects it outright (`not a valid option name: identity`). INN
recognises a peer by *address*, and the name a peer is known by for feeding
purposes is its `newsfeeds` site name. On loopback, `hostname: 127.0.0.1`
authorises everything that can connect to the port: this is a lab, and the
absence of peer authentication is a recorded gap, here and in the evidence.

### `newsfeeds`

```
ME/inn.hbox.test:*::
innfeed!:!*:Tc,Wnm*:/tank/fn/inn/2.7.4/bin/innfeed -y
fn/fnA.hbox.test:fn.*:Tm:innfeed!
```

**A second correction to §5.** INN does *not* refuse an inbound article
because its `Path` names INN's own `pathhost`. The inbound loop check is the
`ME` entry's exclusion sub-field — the comma list after the slash in the site
field — which `innd` reads as `ME.Exclusions` and answers
`437 Unwanted site <site> in path` (`innd/art.c`). Without `ME/inn.hbox.test`
the loop scenario of §5 (S8) passes silently with a `235`, which is the
opposite of evidence.

The list names INN's own identity and nothing else. Adding fn's identity
would refuse every article fn ever feeds, not just a loop; a first draft did
exactly that and `tests/test_inn_lab.py` caught it before the lab was pointed
at a box.

`innfeed!` is the channel `innd` spawns; `fn/fnA.hbox.test:fn.*:Tm:innfeed!`
funnels everything in `fn.*` into it, except an article whose Path already
names fn's path identity: the `fn` site's own exclusion, which every INN
peering carries, so fn's articles are not offered straight back to it.

### `innfeed.conf`

```
pid-file:        innfeed.pid
log-file:        innfeed.log
status-file:     innfeed.status
backlog-directory: /tank/fn/inn/2.7.4/spool/innfeed
use-mmap:        false
initial-reconnect-time: 5
max-reconnect-time:     60

peer fn {
    ip-name:             127.0.0.1
    port-number:         11417
    streaming:           true
    max-connections:     1
    initial-connections: 1
    drop-deferred:       false
}
```

The key is `port-number`, not `port` (§5 writes `port: <fn port>`;
`inncheck` rejects it). `drop-deferred: false` keeps a `431`/`436` a retry
rather than a discard, which is what makes the deferral observable.

There must be no `input-file:` line: that makes `innfeed` read a file
instead of the channel `innd` gives it, and it then spins on
`open .../innfeed.input: No such file or directory` while never connecting.

### `readers.conf`

```
auth "localhost" {
    hosts: "localhost, 127.0.0.1, ::1"
    default: "<localhost>"
}
access "localhost" {
    users: "<localhost>"
    newsgroups: "*"
    access: RPA
}
```

## The scenarios, and what each one is worth

Every row quotes the reply the other server gave, from the relay's log.

| lab scenario | §5 row | what it establishes |
| --- | --- | --- |
| `POST` to the fn owner, read back | — | fn injects (Path, Injection-Date, Injection-Info) and serves the article |
| fn's feed offers it to `innd` | S1 | fn's outbound feed, by `IHAVE` (the peer record's streaming is `false`): `335`, the article, `235` |
| `nnrpd` serves it | S3 (half) | INN's copy against fn's, header by header; RFC 5537 §3.6 lets a relay change Path and Xref and nothing else |
| `operator post`, then the feed | — | the operator's submission is injected like a POST (Path naming fn, Injection-Date, Injection-Info) and innd takes it `335`/`235` |
| `POST` with `From: yue` | — | fn refuses a From that names no address (`441`) and does not serve it |
| `IHAVE ... into INN` by hand | S1 control | `235`; the same offer again `435`; a Path naming INN `437`; `CHECK` new `238`, known `438` |
| INN's `innfeed` offers to fn | S3 | `CHECK`/`TAKETHIS` into the owner, fn's replies, and fn's copy against what crossed: fn's identity prepended to Path and the sender's Xref removed (RFC 5537 §3.7 steps 6, 7) |
| a second offer to fn of each article it holds | S4 | `435` from fn |
| a Path naming fn's own identity | S8 | fn's loop suppression (`policy set path-identity`): refused, and not served |
| SIGTERM the owner, `recover`, restart, reread | S10/S11 (shape) | the articles fn held are served byte-identical |
| SIGKILL `innd`, restart, re-offer | control | INN's history: both articles it took are still `435` |

One is weaker than its name suggests, and the evidence says so:

- **Both transit connections cross the lab's relay.** It forwards octets
  unchanged and in order on loopback, and both servers see it as `127.0.0.1`,
  the address each peer record admits; it is still a hop neither would have.

## What the fn side has to answer, from innfeed's source

The reply codes an fn transit surface will meet are not a matter of taste:
`innfeed` has a switch over them, and what it does with each one decides
whether a refusal is a retry, a drop, or a sleeping connection. From
`innfeed/connection.c` in 2.7.4:

| fn answers | innfeed does | article |
| --- | --- | --- |
| `238` (CHECK: send it) | `processResponse238` → sends `TAKETHIS` | in flight |
| `431` (CHECK/TAKETHIS: try later) | `hostArticleDeferred` → requeued after `deferTimeout`; with `drop-deferred: true` it is treated as `438` instead | **retry** |
| `438` (CHECK: already have it) | `processResponse438` | dropped, and correctly so |
| `239` (TAKETHIS: OK) | `hostArticleAccepted` | done |
| `439` (TAKETHIS: rejected) | `hostArticleRejected` | **dropped, no retry** |
| `335` (IHAVE: send it) | sends the article | in flight |
| `435` (IHAVE: not wanted) | `processResponse435` | dropped |
| `436` (IHAVE: try later) | deferred, unless nothing is in flight *and* `drop-deferred` is set, when it becomes a `435` | **retry** |
| `437` (IHAVE: rejected) | `processResponse437` | **dropped, no retry** |
| `400` (stopped accepting) | `processResponse400` → the connection is blocked and slept | requeued |
| `480` / `503` | `processResponse480` / `processResponse503` → connection torn down | requeued |
| anything else | `warn("cxnsleep response unknown: %d")` then `cxnSleepOrDie` | requeued, connection sleeps |

Two consequences for fn's inbound transit surface, both load-bearing:

1. **`437`/`439` are permanent and `431`/`436` are not.** An fn refusal that
   is really "not now" (no capacity, throttled, an uncertain commit) must be
   `431`/`436`, never `437`/`439` — the difference is whether the peer ever
   offers it again. This is the wire-level shape of D13's three outcomes:
   accepted `235`/`239`, refused `435`/`437`/`438`/`439`, *uncertain*
   `431`/`436`.
2. **An unknown code is a sleeping connection, not a lost article.** That is
   what the development reader's `500` produced on 2026-09-20: innfeed logged
   `cxnsleep response unknown: 500` and retried later with the article still
   queued. The native owner answers `238`/`239` (2026-09-22).

A third, smaller: a non-`203` answer to `MODE STREAM` is *not* fatal.
`innfeed` sets `maxCheck = 1` and falls back to `IHAVE`, so an fn that speaks
`IHAVE` and refuses `MODE STREAM` still interoperates — slowly.

## What this lab does not establish

Repeated in every evidence file, and here once:

- INN and fn are on one host, over loopback. No real network, no partition,
  no latency, no clock disagreement.
- No TLS, no `AUTHINFO`, no `Distribution`, no control messages, no cancels,
  no expiry. `incoming.conf` authorises by source address, which on loopback
  authorises everything that can connect.
- No RFC 3977/4644/5537 conformance audit. The assertions are the lab
  driver's. A green run says these two programs agreed on these exchanges.
- A `SIGKILL` is not a power loss, and killing one server is not a partition.
- The native image is consumed as named; nothing here re-establishes which
  source or which certificates it was built from.
