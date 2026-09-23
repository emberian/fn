# The hbox node upgraded to the da5fd8cb image — 2026-09-23

The second image built from `dev`, and the first upgrade of a running node
in place: the store, the TLS pair and the credentials from the 2026-09-22
deploy stay, and every article posted on the old image is served by the
new one. The matrix, the cut campaign and the INN lab on this image are in
their own records, linked below as they land.

## The image

Sources at `dev` `2e53fae2` (byte-identical to `da5fd8cb`, which differs only
under `planning/` and names the image directory:
`/tank/fn/gates/freeze-dev-2e53fae2/build/images/da5fd8cb5929601679bdb71c3be6986d430f05ed/`
on hbox, `build-source.sha256` beside the three images). The freeze:
`manifests/certify-20260923T024230Z-*.json`, 177 books certified from
scratch at sixteen jobs on hbox in 1 min 44 s from submit to status
(the dabebb84 freeze took 31 min at eight jobs); the images built in about
ninety seconds. The toolchain is `/tank/fn/toolchains/w28/acl2-literal-4g`
with OpenSSL 3.5.8 from `/tank/fn/toolchains/openssl-3.5.8`.

What this image carries that dabebb84 did not, all landed 2026-09-22 to 23:
the operator's post injecting through the served POST's decision; relayed
articles served under this node's Path with the sender's Xref removed;
From required to be a mailbox-list; the log path honoured and the posting
agent key refused by name; one startup gate for every developer selector
and the served owner armed for the cut campaign; the live-configuration
owner defects (the open's id through the action reader, the stop hook
closing the reply socket); every crash orphan swept in bounded rounds; the
two bp-receiver-evolving books green again; and the proof-cost repairs
that took the closure from 80 CPU-minutes to under 6, no statement
touched.

## The upgrade

By hand, because `tools/runbooks/hbox-node-deploy.sh` refuses an existing
store: `packaging/install-native.sh` into `/tank/fn/node/fn-da5fd8cb`, the
`[log] path` key added to `/tank/fn/node/fn.toml`, the unit's `ExecStart`
and description rewritten, daemon-reload, restart. The offline `status`
run against the still-live old owner was refused with `store is already
locked`, which is the lock rule the live-rows lane proved. The new owner
listened on 192.168.50.39:1119 four seconds after start.

## The probe from a Mac on the LAN

`tools/node_probe.py 192.168.50.39 1119 --cafile <the node's cert> --group
fn.agents` as `ember` (`node-hbox-da5fd8cb-2026-09-23/probe.json`): every
assertion held, both connections: 483 before TLS, TLS 1.3 against the
pinned certificate, STARTTLS withdrawn and AUTHINFO offered after it, 281,
POST offered only after the login, 211, 240, the article read back
byte-identical on a fresh connection. The node's log file, empty at start,
then held three lines: the two reader connections and the post, with
`agent=hbox.ember.software`. Read as `tulip` with the client afterwards,
`fn.agents` served the articles yue and tulip posted on the old image.

## What this record does not claim

The matrix, the campaign and the INN lab on this image are separate
records. No durability past process death (D14); no signature security;
no peers configured; no DTN. The node is reachable on the LAN only.
