# The public node, fsn1

`fn.fg-goose.online` (88.99.126.35), open by invitation since 2026-09-27.
It runs `fn 6.6.0 (a3553e6b4a23)`, the same release as [hbox](hbox.md),
since the format-10 migration of 2026-09-28. Records:
`planning/evidence/public-node-deploy-2026-09-27.md` and
`planning/evidence/node-migrate-2026-09-28.md` (filed evidence;
`python3 tools/evidence_store.py cat PATH`). The deploy runbook is
`planning/runbook-public-node-2026-09-27.md`.

Nothing on this page is a command to run. The node is redeployed only
on ember's word.

## Where it is

| | |
| --- | --- |
| machine | the fsn1 anchor (Debian 12, glibc 2.36), reached at 5.75.245.0; the floating IP 88.99.126.35 is the public address |
| release | `/opt/fn-a3553e6b4a23`, with `/opt/fn` a link to it (the flat layout from before `releases/`); `/opt/fn-902de4882412` and `/opt/fn-18a7137a3` kept |
| node folder | `/var/lib/fn` (`fn.toml`, `store/`, `keys/`, `tls/`); account `fn`, home `/var/lib/fn` |
| unit | `fn.service` (ExecStart through `/opt/fn/bin/fn`, `RestartSec=5`) with the drop-in `/etc/systemd/system/fn.service.d/edge.conf`; `fn-health.timer` every 5 minutes |
| ports | 119 (STARTTLS) and 563 (TLS) |
| certificate | Let's Encrypt, from the anchor's Caddy; `fn-cert-sync` copies each renewal into `/var/lib/fn/tls` and runs `tls reload` |
| groups | local.general, local.test, control.cancel, fn.general, fn.test, fn.announce, fn.docs |
| kept | the format-9 store `/var/lib/fn/store.format9-20260928T162825Z`; a stopped backup under `/root/fn-backups/` |

fn.docs holds the FAQ articles of `docs/articles/`, posted by
`tools/post_docs.py`. Passwords and invitation codes live in root-only
files on the anchor and are never written into this tree.

## Before the next deploy

`packaging/install.sh` refuses a prefix without `releases/`, so the flat
`/opt/fn` link is moved aside first. The next deploy is a fresh install
(decision D34 in `planning/decisions.md`), at least 30 minutes after hbox
is healthy on the same release. `fn-cert-sync` and the edge drop-in come
from the dregg-infra repository, not this one.
