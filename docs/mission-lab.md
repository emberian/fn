# The mission lab

Status: spike (D28, `spike/mission`). The lab is the integration harness the
spike lanes plug into: four native fn nodes on one box, peered over NNTP and
over a BP link whose connectivity the operator switches, with one demo that
walks a signed article from A to D and its receipt back, then a cancel.
Nothing here is proved; every host-side decision is marked `;; SPIKE` in the
tools and listed under [Deferrals](#deferrals). The run record is
[planning/evidence/spike-mission-2026-09-25.md](../planning/evidence/spike-mission-2026-09-25.md).

## Topology

```
   A <==NNTP==> B  ~~ r1 ~~[link]~~ r2 ~~  C <==NNTP==> D
                |                          |
             B-bp store                 C-bp store
```

| Persona | NNTP (STARTTLS) | web reader | BP node | stores |
| --- | --- | --- | --- | --- |
| A | 127.0.0.1:12101 | http://127.0.0.1:12111/ | | `A/store` |
| B | 127.0.0.1:12102 | http://127.0.0.1:12112/ | `dtn://fn-b/` on 12122 | `B/store`, `B/bp/store` |
| C | 127.0.0.1:12103 | http://127.0.0.1:12113/ | `dtn://fn-c/` on 12123 | `C/store`, `C/bp/store` |
| D | 127.0.0.1:12104 | http://127.0.0.1:12114/ | | `D/store` |

| Relay (dtn7-rs, sled, static routes) | CLA | web | dials the other relay through |
| --- | --- | --- | --- |
| r1 `dtn://dtn7-r1/` (B's side) | 12131 | 12141 | link proxy 12151 |
| r2 `dtn://dtn7-r2/` (C's side) | 12132 | 12142 | link proxy 12152 |

- A-B and C-D are peered both ways: `peer add ... principal <hex> <profile>
  false true starttls localhost <cert>` (streaming, TLS required, AUTHINFO
  with a per-direction login), inbound and outbound `fn.*,control.*`.
- Every node has the human login `ember` (posting) and one peer login; the
  passwords are in `<node>/passwords.json` (0600) under the lab root.
- One author (`author/author-*`: a 32-octet principal, Ed25519, ML-DSA-65)
  is enrolled at generation 1 in all six stores, the four NNTP stores through
  their owners' control sockets and the two BP stores through a temporary
  developer owner (the DTN image has no control socket).
- B and C each run `bp-node serve` from the DTN developer image on their BP
  store, with the relay as their neighbour boundary (`carries` and
  `releases-for` the far node), the far node under its own EID and a
  `bp-route` to it through the relay.
- The link is two TCP proxies inside `mission_lab.py link-serve`. `link down`
  closes both listeners (a dial is refused) and severs live sessions;
  `link up` listens again. The relays' 5 s janitor retries forwarding.

## Running it

On hbox, from a gate tree whose `build/images/<rev>/` holds the four frozen
images (`tools/runbooks/hbox-image-build.sh`):

```sh
cd /tank/fn/gates/<tree>
export FN_MISSION_ROOT=/tank/fn/scratch/spike-mission/lab
export FN_MISSION_IMAGES=$PWD/build/images/<rev>
export FN_MISSION_DTN7=/tank/fn/dtn7/repo            # the pinned dtn7-rs build
swarm-build python3 tools/mission_lab.py up           # provision once, start everything
python3 tools/mission_lab.py status                   # one screen
python3 tools/mission_lab.py demo                     # link up throughout
python3 tools/mission_lab.py demo --partition 60      # link down across the BP hop
python3 tools/mission_lab.py link down|up|state
python3 tools/mission_lab.py down                     # stop every PID the lab started
```

`up` is idempotent: it provisions only once (`<root>/lab.json` records
everything) and starts what is not running. `down` signals only the PIDs in
`lab.json` (SIGTERM, then SIGKILL after 30 s) and records how each stopped.
The OpenSSL with ML-DSA-65 comes from `FN_OPENSSL_PREFIX` or
`/tank/fn/toolchains/openssl-3.5.8`; the images carry their own libraries.

Ports are fixed (12101 to 12191) so the README, the status screen and the
records agree; check `ss -ltn` before `up` on a shared box.

## The demo

Each step prints its wire lines (the NNTP exchange, the image commands), the
log lines it produced (with the SHA-256 of each line) and its measurements;
the record is `<root>/demo/<tag>/demo.json`, and every command's exit,
stdout and stderr is in `commands.jsonl` beside it.

1. A: the author signs (`hybrid-sign`) and injects (`hybrid-author` on A's
   control socket) `<mission-<tag>@a.mission.invalid>` into `fn.mission`.
2. B: `ARTICLE` over STARTTLS+AUTHINFO until 220; `HDR :fn-verified` is B's
   verdict; A's feed journal for B is listed. A's obligation to B is
   discharged here, by B's streaming reply.
3. B: the article is read back over NNTP, written into B's BP store
   (`store post`), enqueued (`app-journal workflow-enqueue`), undertaken and
   requested (`bp-obligation request`) toward `dtn://fn-c/` through r1. With
   `--partition N` the link is taken down first, so r1 holds the bundle.
4. The link comes up; r1 forwards to r2, r2 to C; C's node logs
   `BP node delivery request-accepted` (or names its refusal).
5. C: `store inspect` reads the delivered article out of C's BP store and
   `operator post` submits it to C's NNTP owner; the C-D feed carries it to
   D. Verdicts on C and D; the octets are compared with B's copy.
6. C's application receipt travels r2 -> r1 -> B (through `bp-contact tick`
   if C's node has only queued it); B's node logs the receipt and the
   release; `bp-obligation status` on B shows `pinned=no`.
7. A cancel (`Control: cancel <id>`) posted on A as `ember` is filed into
   `control.cancel` on A and fed to B, bridged to C over the BP path and fed
   to D; the demo then asks every node for the original article. Today the
   answer is 220 everywhere: C1 files, C3 (withdrawal) is not implemented.
8. Latencies (author to B, to C's delivery, to D; the receipt back; the
   cancel to D) and the SHA-256 of every log.

## Status screen

`mission_lab.py status` prints, per node, whether its owner, web reader and
BP node are alive, the `fn.mission` and `control.cancel` counts over NNTP,
the verdict of the newest article, each undertaken work's `bp-obligation
status`, the BP store's pins (`store retention`), the relays' bundle stores
(`dtnquery bundles`) and the link state. Obligations and pins are offline
verbs; the screen says when the serving node's lock refused them.

## Deferrals

Every one is marked `;; SPIKE` in `tools/mission_lab.py` or
`tools/mission_demo.py`; dev owns the proof or the ACL2 decision.

- K6, one transit decision for NNTP and BP: the NNTP owner and the BP node
  each take a store's writer lock, so B and C carry two stores and the demo
  bridges them host-side (`store post`, `store inspect`, `operator post`).
- The receipt's return past B: NNTP has no application receipt, so the
  receipt releases B's BP obligation and A's obligation to B is the streaming
  reply.
- Status over the control socket: obligations, pins and headroom are offline
  verbs; the screen stops the serving node when it must read them.
- Author enrolment in a BP store through a temporary developer owner.
- The link controller is a Python proxy, not a modelled contact plan; the
  relays are dtn7-rs with static routes, not fn's scheduler.
