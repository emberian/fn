# Runbook: deploying fn.fg-goose.online on the fsn1 edge (2026-09-27)

This runbook is for whoever does the real deploy after the fsn1 cutover:
ember, or a friend of ember's with root on the edge. Each step is one
command or one console action, with the result you should see. Most steps
were rehearsed on the fsn1 boxes with throwaway nodes. The rehearsal record
is [public-node-rehearsal-2026-09-27](evidence/public-node-rehearsal-2026-09-27.md).
Each section says what was rehearsed and what was not. **NOT REHEARSED**
marks a step that could not run before the cutover.

## 0. Before you start

You need all of these. Stop if any one is missing.

1. **The fsn1 cutover is done.** Every step of
   `~/dev/dregg-infra-migrate-fsn1/edge/MIGRATION-FSN1-2026-09-26.md`
   section 6 is complete, and in particular:
   - 6(a).4: the quarantine is lifted, so the boxes can reach Let's Encrypt.
   - 6(b): DNS has moved.
   - dregg-infra `main` has `migrate-fsn1` merged, then `fn-public-node-fsn1`.

   Check the egress from the anchor. It must print `200`:
   `ssh root@5.75.245.0 'curl -s -o /dev/null -w "%{http_code}\n" https://acme-v02.api.letsencrypt.org/directory'`.
2. **A release tarball and its SHA256SUMS**, from the release cut. The
   rehearsal's own build, `fn-6.7.0-linux-x86_64.tar.gz` at dev 18a7137a3
   (sha256 `54e6a363...`, on hbox under
   `/tank/fn/scratch/public-node-rehearsal/dev/release/`), is a rehearsal
   artifact, not a release. ember says which tarball.
3. **ssh as root to both boxes.** Use
   `ssh -i ~/.ssh/id_portable -o IdentitiesOnly=yes root@5.75.245.0` (the
   anchor) and `root@2.28.141.27` (the workhorse). `~/.ssh/config`'s
   `dregg-anchor` and `dregg-workhorse` still name Ashburn until
   migration 6(c)'s follow-up commit.
4. **Two decisions from ember:**
   - **The layout.** A (recommended): the anchor, native, with Caddy's
     certificate. B: the workhorse, in a container, with lego.
   - **The memory limit.** This fixes the store's size for good: raising it
     later is export, reinstall and import. Measured on the workhorse:

     | MemoryMax | init's reservation | transactions (about articles plus feed traffic) |
     | --- | --- | --- |
     | 1536M | 1,265 MB | 16,384 |
     | 2G | 1,799 MB | not recorded |
     | 3G | 2,841 MB | 65,536 |

     The anchor (cx23, 3.8 GB, about 450 MB used) takes 1536M or 2G. The
     workhorse (cx33, 7.6 GB, about 2.2 GB used) takes up to 3G.

In the commands below, `LIMIT` is that figure (for example `1536M`),
`PUBLIC` is the node's public address and `BOX` is `root@` that box:

| Layout | PUBLIC | BOX |
| --- | --- | --- |
| A | 88.99.126.35, the fsn1 floating IP | `root@5.75.245.0` |
| B | 2.28.141.27, the workhorse's primary IP | `root@2.28.141.27` |

## Layout A: the anchor, native, Caddy's certificate (recommended)

Why this layout:

- The name sits on the floating IP like every other name on the edge.
- Caddy already obtains certificates over HTTP-01, so no DNS credential
  lives on any box.
- The release runs on the anchor's Debian 12, checked in the rehearsal:
  `fn 6.7.0` ran natively there, served a POST over TLS under
  `MemoryMax=1536M`, and used 43 MiB.
- The anchor's disk measured 124 POST/s at 1 poster and 216 at 8.

### A1. Firewall (from `~/dev/dregg-infra`)

```sh
cd edge/tofu
# in terraform.tfvars:  fn_host = "anchor"
tofu plan     # MUST be exactly one in-place update: the fsn1 anchor's firewall_ids gains dregg-fn
tofu apply
tofu output fn_dns_record     # fn.fg-goose.online.  300  IN  A  88.99.126.35
```

If the plan shows anything else, stop. Re-upload the state bundle to
1Password afterwards, because the serial moves.

### A2. Caddy's site block, then DNS

- Ship the Caddyfile that carries the `fn.fg-goose.online` block:
  `./edge/deploy.sh --only headscale --no-build`. The rehearsal checked the
  block with the anchor's own Caddy 2.11.4 (`caddy adapt`: LE production,
  P-256).
- At Squarespace (fg-goose.online), add `fn  A  88.99.126.35`, TTL 300.
  This is ember's hand step: nobody else changes DNS.
- Watch for the certificate. **NOT REHEARSED** (the quarantine):

```sh
ssh BOX 'journalctl -u caddy --since -15min | grep fn.fg-goose.online | tail -3'   # "certificate obtained successfully"
ssh BOX 'ls /var/lib/caddy/.local/share/caddy/certificates/acme-v02.api.letsencrypt.org-directory/fn.fg-goose.online/'
```

### A3. Install the release

```sh
scp fn-6.7.N-linux-x86_64.tar.gz SHA256SUMS BOX:/root/
ssh BOX 'cd /root && sha256sum -c --ignore-missing SHA256SUMS && sha256sum fn-6.7.N-linux-x86_64.tar.gz'
#   compare that hash with the one ember published; they must be equal
ssh BOX 'cd /root && tar -xzf fn-6.7.N-linux-x86_64.tar.gz && sh fn/install.sh'
#   "fn 6.7.N (REV12)", "installed /opt/fn", "created account fn",
#   "installed /etc/systemd/system/fn.service"
```

The anchor already has `libssl3`, which is OpenSSL 3.0.22.

### A4. The edge's limits on the unit

`edge/fn/fn.service.edge.conf` becomes a drop-in. **Set its `MemoryMax=` to
LIMIT first**; the file says 1536M.

```sh
ssh BOX 'mkdir -p /etc/systemd/system/fn.service.d'
scp edge/fn/fn.service.edge.conf BOX:/etc/systemd/system/fn.service.d/edge.conf
ssh BOX 'systemctl daemon-reload && systemctl cat fn | grep -E "MemoryMax|AmbientCap"'
```

### A5. The certificate hand-off

`fn-cert-sync` copies Caddy's pair into the node and, on a renewal, tells the
node. The node answers `tls reload` with no restart.

```sh
scp edge/fn/fn-cert-sync BOX:/usr/local/sbin/fn-cert-sync
scp edge/fn/fn-cert-sync.service edge/fn/fn-cert-sync.path edge/fn/fn-cert-sync.timer BOX:/etc/systemd/system/
ssh BOX 'chmod 0755 /usr/local/sbin/fn-cert-sync
printf "FN_RUNTIME=native\nFN_UID=fn\nFN_TLS_DIR=/var/lib/fn/tls\nFN_UNIT=fn.service\nFN_RELOAD=verb\n" > /etc/default/fn-cert-sync
systemctl daemon-reload
/usr/local/sbin/fn-cert-sync
ls -l /var/lib/fn/tls'
#   "fn-cert-sync: installed subject=CN=fn.fg-goose.online issuer=... notAfter=..."
#   then, since the node is not started yet (A7), "node not running (...):
#   reload skipped, the node reads the pair at start" and exit 0
#   (dregg-infra fn-public-node-fsn1 a3b7518; before it, this first run
#   answered "refused operator tls" and exit 1: the deploy record's D3)
#   cert.pem 0644 and key.pem 0600, both owned by fn
```

The rehearsal ran fn-cert-sync with a lego-shaped source and a throwaway CA:

- It installed the pair.
- It refused a certificate for the wrong name, leaving the live pair
  untouched.
- On a new pair with `FN_RELOAD=verb`, the served certificate changed and
  the node was not restarted.

The `native` arms of fn-cert-sync assume `/opt/fn`, `/var/lib/fn` and the
account `fn`. Those are install.sh's defaults: keep them.

### A6. Settings, store, policy and a login

**`init` must run under the same memory limit as the service.** Run in a
plain shell, it sizes the store for the whole machine, and the service then
refuses to start:
`fn: refused machine-cannot-hold-profile heap=4577 MB machine=1536 MB`.
The rehearsal hit this on both layouts.

```sh
ssh BOX 'set -e
F="runuser -u fn -- /opt/fn/bin/fn operator /var/lib/fn/fn.toml"
cd /var/lib/fn
$F mission small-community --host 88.99.126.35 --port 119
sed -i "/^port=119\$/a tls_port=563" /var/lib/fn/fn.toml
grep -A3 "^\[listener\]" /var/lib/fn/fn.toml
systemd-run --quiet --pipe --wait -p MemoryMax=LIMIT -p User=fn -p WorkingDirectory=/var/lib/fn \
  /opt/fn/bin/fn operator /var/lib/fn/fn.toml init'
```

The `grep` should show `host="88.99.126.35"`, `port=119` and
`tls_port=563`. The last line should print
`init: ... reservation=R MB budget=B MB within-budget=yes`, where B is
LIMIT in MB.

`init` also creates the node secret, `store/keys/node-secret.key`. Do
**not** run `node-secret create` after it: it refuses because the secret
exists. That command is only for a store brought in with `store import`.

Then apply the exposure profile. `edge/fn/exposure.policy` holds the 10
slots: 31 connections, 4 per address, anonymous none, bound-logins, and
path-identity `fn.fg-goose.online`.

```sh
scp edge/fn/exposure.policy BOX:/root/exposure.policy
ssh BOX 'F="runuser -u fn -- /opt/fn/bin/fn operator /var/lib/fn/fn.toml"
grep -v -e "^#" -e "^\$" /root/exposure.policy | while read -r slot value; do $F policy set "$slot" "$value"; done'
ssh -t BOX 'runuser -u fn -- /opt/fn/bin/fn operator /var/lib/fn/fn.toml principal set-password ember --posting'
```

Each policy line should print `configured generation=N ...
verification=VERIFIED`. `set-password` asks for the password twice.

### A7. Start and check

```sh
ssh BOX 'systemctl enable --now fn; sleep 10; journalctl -u fn -n 5 --no-pager'
#   OWNER-OPEN ..., CONTROL ..., LISTENING 119, LISTENING-TLS 563
ssh BOX 'F="runuser -u fn -- /opt/fn/bin/fn operator /var/lib/fn/fn.toml"; $F health; $F status | grep -E "^capacity|^heap|^exposure"'
#   health exit=00 state=healthy; every state clear; "exposure limits ... anonymous=none"
ssh BOX 'systemctl enable --now fn-cert-sync.path fn-cert-sync.timer'
```

**NOT REHEARSED:** binding 119 and 563 on the floating IP. The rehearsal
used high ports on private addresses. The unit grants
`CAP_NET_BIND_SERVICE`. If the log says `bind ... Permission denied`, check
`systemctl cat fn | grep -i capab`.

### A8. Check it from outside (your laptop; OpenSSL 3, not macOS's LibreSSL)

```sh
O=/opt/homebrew/opt/openssl@3/bin/openssl
$O s_client -connect fn.fg-goose.online:563 -servername fn.fg-goose.online -verify_return_error -verify_hostname fn.fg-goose.online </dev/null 2>&1 | grep -E 'Verify return|^20[01]'
$O s_client -starttls nntp -connect fn.fg-goose.online:119 -servername fn.fg-goose.online -verify_return_error </dev/null 2>&1 | grep 'Verify return'
```

Both must print `Verify return code: 0 (ok)`.

- **The node must see your address.** Its log line does not name clients
  (packet B), so ask the kernel while a connection is open:
  `( sleep 8 | $O s_client -quiet -connect fn.fg-goose.online:563 >/dev/null 2>&1 & ); sleep 3; ssh BOX "ss -Htn state established '( sport = :563 )'"`.
  The peer column must be your public address. In the rehearsal it was the
  client's own address, not a gateway.
- **Post and read** with any newsreader, on 563 with TLS, logged in as
  `ember`: post to `local.test`, then read it back. The log shows
  `accepted post path=served`.
- **Before TLS**: `printf 'AUTHINFO USER x\r\nQUIT\r\n' | nc fn.fg-goose.online 119`
  must answer `483 a protected channel is required; use STARTTLS`.

### A9. Crash behaviour (optional; this was rehearsed)

`kill -9` of the node:

- systemd restarts it within 5 s.
- Every article answered 240 before the kill is still there.
- health is back to `exit=00`.

If you run this on the live node, run it before anyone else relies on it.

## Layout B: the workhorse, in a container, with lego (the fallback)

dregg-infra's `edge/fn/deploy-fn.sh` does steps A3 to A7 as a container.
The rehearsal ran its compose file end to end on the workhorse: fn-init,
up and Healthy, a read-only root, the client address kept, peering,
`tls reload`, and a crash with its restart.

**The fix it needs first (R1): add `mem_limit: LIMIT` to the `fn-init`
service** in `edge/compose/docker-compose.fn.yml`, the same value as `fn`'s
`mem_limit`. Without it, init sizes the store for 7.6 GB and `fn` loops on
`machine-cannot-hold-profile` under its limit. Set `fn`'s `mem_limit` to
LIMIT too.

Then follow `edge/fn/README.md` "Fallback: two boxes":

1. `fn_host = "workhorse"`, then tofu plan and apply as in A1.
2. Remove the Caddy block, because the name does not point at Caddy.
3. At Squarespace:
   - `fn A 2.28.141.27`
   - `_acme-challenge.fn CNAME _acme-challenge.fn-fg-goose.dregg.net.`
4. A Cloudflare token scoped to dregg.net, in
   `/opt/dregg-edge/secrets/fn-acme-cf-token` (0600).
5. `LEGO_IMAGE` pinned by tag and digest in `/opt/dregg-edge/.env`.
6. `FN_PUBLIC_IP=2.28.141.27` in `/opt/dregg-edge/.env`.
7. `FN_BOX=root@2.28.141.27 FN_CERT_SOURCE=lego ./edge/fn/deploy-fn.sh --tarball <hbox path> --sha256 <hex>`.
8. `printf 'FN_CERT_SOURCE=lego\nFN_RELOAD=verb\n' > /etc/default/fn-cert-sync`
   on the box.
9. The lego-source watch: a drop-in for `fn-cert-sync.path` with
   `PathChanged=/var/lib/dregg/fn-acme/certificates/fn.fg-goose.online.crt`.

**NOT REHEARSED:** lego and DNS-01, and `deploy-fn.sh`'s outside
verification against the real name.

The workhorse's disk measured 117 POST/s at 1 poster and 225 at 8. Its
0.47 fsyncs per POST is higher than the anchor's 0.31, and both boxes are
CPU-bound at about 12 ms of owner CPU per POST.

## Rollback

- **Before anyone relies on it**, on the box:

  ```sh
  systemctl disable --now fn fn-cert-sync.path fn-cert-sync.timer
  ```

  For layout B, run `cd /opt/dregg-edge && docker compose -f docker-compose.fn.yml stop fn`
  instead. Then:
  - In dregg-infra, `fn_host = ""` and `tofu apply`. This detaches
    `dregg-fn`, closing 119 and 563.
  - ember removes the `fn` A record at Squarespace.
  - Keep `/var/lib/fn` (or `/var/lib/dregg/fn`) until you know why you
    rolled back.
- **A full removal** (native): after the above,
  `rm -rf /opt/fn /var/lib/fn /etc/systemd/system/fn.service /etc/systemd/system/fn.service.d /usr/local/sbin/fn-cert-sync /etc/systemd/system/fn-cert-sync.* /etc/default/fn-cert-sync; systemctl daemon-reload; userdel fn`.
  The rehearsal's teardown was this, and it left the box as it found it.
- **A bad certificate.** fn-cert-sync refuses a mismatched, wrong-name or
  expired pair and leaves the live pair serving. A pair that `tls reload`
  refuses also leaves the old one serving. Read `journalctl -u fn-cert-sync`.
- **A later release** is a reinstall (D34), never an in-place upgrade:
  - stop the node and `store export`;
  - remove `/opt/fn` and install the new tarball;
  - `init` under the limit, or `store import`;
  - copy `store/keys/node-secret.key` back for an imported store (the export
    excludes `keys/`), so that old Cancel-Locks stay cancellable;
  - start.

  docs/install.md section 4, "Reinstalling", has the exact commands.
- **The edge itself.** Rolling the whole edge back to Ashburn is migration
  6(f). The fn node goes with the box. Nothing of fn's is on Ashburn.

## hbox as a private peer over the tailnet (as far as known)

**NOT REHEARSED.** hbox is logged out of the tailnet and points at
Tailscale SaaS. The fsn1 tailscaled stays disabled until the cutover. In
order:

1. **A headscale policy** (packet I1): the public box may reach
   `hbox:1119` and nothing else. Ship it with
   `./edge/deploy.sh --only headscale --no-build`.
2. **Enrol hbox**:
   `sudo tailscale up --login-server=https://headscale.dreggnet.fg-goose.online --authkey=<pre-auth key>`.
   Then note `tailscale ip -4`, written HBOX_TS below.
3. **Enrol the public box with `--shields-up`.** The anchor is logged out;
   the workhorse keeps its node key 100.64.0.3.
4. **hbox's node listens on both addresses.** In its `fn.toml`:
   `[listener] host = "192.168.50.39, HBOX_TS"`. Then restart it (ember's
   node: ember's hand).
5. **hbox's certificate must name the name the public node dials.** Re-issue
   hbox's self-signed pair with `subjectAltName=DNS:<a name>,IP:HBOX_TS`.
   The rehearsal proved DNS names in `starttls NAME`; an IP literal there is
   unrun.
6. **The exchange** follows docs/peering-with-a-friend.md, with the public
   node as the inviter:
   - `F="runuser -u fn -- /opt/fn/bin/fn operator /var/lib/fn/fn.toml"`
   - `$F peer keygen /var/lib/fn/keys`
   - `$F peer invite hbox 'local.*' HBOX_TS 1119 fn.fg-goose.online /var/lib/fn/keys /var/lib/fn/exchange/invitation-for-hbox fn.fg-goose.online 563`
   - `peer accept` on hbox, then `peer confirm` here.
   - Bound logins on both, then `peer add` on both.
   - hbox's record for the public node carries outbound `-`, so hbox never
     dials out.
   - `$F peer pull hbox 60` here.
   - Restart both nodes: `set-password` on a running node answers
     `restart-required`.
7. **The groups.** hbox's LAN node was initialised with `fn.*`, and the
   public node serves `local.*` (small-community). ember picks the shared
   hierarchy, and `group create` runs on both nodes before the first
   article.

## spwashi and pug (as far as known)

Send them `tools/runbooks/public-node/peering.md` section A, with these
corrections from the rehearsals:

- **Host names work** in `peer invite`, `peer accept` and `peer add`: the
  rehearsal ran all three by name. peering.md's CHECK AT DEPLOY on A1 is
  answered.
- **The public node's path identity** is `fn.fg-goose.online`. Their node's
  peer name for us is that node name, and ours for them is whatever we
  wrote in `peer invite`.
- **The anchor is the Let's Encrypt roots, never the leaf.** The rehearsal
  anchored on a root with an intermediate in the served chain, and the feed
  ran both ways and survived a key change (a new leaf under the same root).
  For fn.fg-goose.online the file is `ISRG_Root_X1.pem` plus
  `ISRG_Root_X2.pem`. Also **NOT REHEARSED**: the
  `peer add ... implicit - -` form (the system store) against a real public
  CA.
- **After `principal set-password` on a running node, restart it.** The
  login answers `restart-required`, and until the restart pulls fail
  `at=preamble`. On a node that has not started yet it answers
  `effective-at-next-start`.
- Their node must be reachable on the port they name, or they take the
  "behind NAT" arrangement: pull only.
- **An INN peer** cannot push to the public node (packet b). Section B's
  arrangement stands, and its pull from a remote INN is **NOT REHEARSED**.

## What to watch in the first week

- `health` on the box stays `exit=00`. `status`'s
  `capacity articles-left=N` falls with posts and with feed traffic; at 0,
  posts are refused.
- `journalctl -u fn-cert-sync` after Caddy's first renewal, about 30 days
  before expiry. It should show `installed ...` and `accepted operator tls`.
- Backups: none exist yet (packet I3). Until a timer exists, take one by
  hand: stop the node, `store export`, start it, and copy the export off
  the box.

## Until the cutover: the ACME renewal clash (D2)

The deploy opened tcp/443 egress on the anchor (`dregg-fn-acme-egress`,
dregg-infra migrate-fsn1 c339cfd) while the fsn1 quarantine holds, so the
anchor's Caddy now reaches Let's Encrypt. The anchor is a clone of the
Ashburn edge and shares its ACME account key. From about 2026-10-01 its Caddy
will try to renew the names that still point at Ashburn:
pathofangels.network, www. and beta. (notAfter 2026-10-31), and companion,
node.pathofangels, dregg.net and www.dregg.net (2026-11-02/03). HTTP-01 fails
for each (the names resolve to Ashburn), and each failure counts toward LE's
failed-validation limit per account per hostname per hour, on the account
Ashburn renews with.

- Harmless if the cutover (dregg-infra MIGRATION-FSN1 6(a)/6(b)) happens
  before 2026-10-01.
- Otherwise detach `dregg-fn-acme-egress` until the cutover: keep
  `fn_host = "anchor"` and apply with only that attachment removed. fn's own
  certificate (notAfter 2026-12-26) enters renewal only around 2026-11-26.

Record: [the deploy record](evidence/public-node-deploy-2026-09-27.md),
observation D2.
