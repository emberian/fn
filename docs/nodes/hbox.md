# The hbox node

Node #2, on ember's LAN machine hbox. It runs the 6.6.0 release
`fn 6.6.0 (a3553e6b4a23)` (source `1e396e4e7` after the history rewrite),
installed on 2026-09-28 with its store exported and re-imported into format
10. The public node is [fsn1](fsn1.md). Records:
`planning/evidence/node-migrate-2026-09-28.md` and
`planning/evidence/hbox-node-2026-09-28.md` (filed evidence;
`python3 tools/evidence_store.py cat PATH`).

The node is owned by another Claude session (breadstuffs-89). Nothing on
this page is a command to run: a stop, start, export or install on
`/tank/fn/node` is requested from that session, on ember's word.

## Where it is

| | |
| --- | --- |
| node folder | `/tank/fn/node` (`fn.toml`, `store/`, `keys/`, `tls/`, `log/fn.log`) |
| release | `/tank/fn/node/fn-a3553e6b4a23`; the previous one kept at `/tank/fn/node/fn-6702ff8b2b46` |
| unit | system unit `/etc/systemd/system/fn-node.service` (User=hbox, `Environment=HOME=/tank/fn/node`, `MemoryMax=2G`); `fn-node-health.service` and `.timer` every 5 minutes |
| ports | 119 (STARTTLS) and 563 (TLS), on the LAN address 192.168.50.39 only |
| certificate | self-signed, CN `hbox.ember.software`, at `/tank/fn/node/tls/cert.pem`; a client pins it with `--cafile` |
| path identity | `hbox.ember.software` |
| groups | local.general, local.test, control.cancel, fn.general, fn.test, fn.announce, fn.docs |
| log | `/tank/fn/node/log/fn.log`; `journalctl -u fn-node` |
| kept | the format-9 store `/tank/fn/node/store.format9-20260928T155147Z`; a stopped backup under `/tank/fn/node-backups/` |

Logins only, never before TLS. Passwords and invitation codes live in
root-only files on hbox and are never written into this tree.

## Peering

hbox dials fsn1 on 563 and pulls from it. Its push to fsn1 stalls in a
silent loop and health reports `exit=26 unavailable-peer` (PKT-882); the
fix is on `dev` and arrives with the next deploy.

## What the next deploy changes

The next deploy is a fresh install from a new release, not an upgrade
(decision D34 in `planning/decisions.md`). The steps, in order, are in
`planning/release-v6.6.0.md` §5 and `docs/install.md`: hbox first, then
fsn1 at least 30 minutes after hbox is healthy. Known defects on this
build that `dev` has fixed: PKT-880 (an invitation made while the node is
stopped is born expired; make invitations with the node running) and
PKT-882 above.
