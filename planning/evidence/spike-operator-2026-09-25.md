# Spike: the operator's surface — 2026-09-25

Lane `spike/operator` on `spike/mega` (D28). One `fn` command
([packaging/fn](../../packaging/fn), bash, host-side) over the native
image's verbs, with upgrade/rollback, backup/restore, doctor, alerts, log
rotation, `status --watch`/`top` and three missions; `install-native.sh`
now installs it as a release's `bin/fn` (raw entry: `bin/fn-native`) and
the release carries its own `share/fn/packaging/` so it can install the next.
Operator documentation: [docs/operator.md](../../docs/operator.md#operating-a-native-node-with-fn-spike-d28).

All runs on hbox under `/tank/fn/scratch/spike-operator/`, as user units
carrying `MemoryMax=24G`, on loopback ports 11931–11935; every unit, timer
and unit file was removed afterwards, and `fn-node.service` (the live node)
was only read (its store copied for the rehearsal) and stayed `active`.
Images: `c3420013` (`/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013`,
core `7a124c6f…`), `4eca4148` (`qual-4eca4148-20260924`), and `452d62cb`
(the bounds-join lane's frozen image, format 8,
`/tank/fn/scratch/bounds-join/tree/build/images/452d62cb…`, digests all OK).
Artifacts and their SHA-256 are in [spike-operator-2026-09-25/](spike-operator-2026-09-25/SHA256SUMS).

## What works (observed)

1. **One command.** `fn [--node DIR] VERB`: the image's operator verbs pass
   through with the node's config; `run` `exec`s the owner; `operator CFG …`
   and `raw VERB …` stay as the image has them, so the old unit line
   `bin/fn operator CFG run` still runs. One tagged stderr line per command,
   exits 0/1/3/4/5.
2. **Upgrade and rollback, rehearsed on a copy of the c3420013 store**
   (`rehearsal/`: 11 transactions copied from the live node, fresh
   127.0.0.1 certificate, the node's own `auth.toml`):
   - `fn upgrade <452d62cb> 452d62cb`: installed beside (digests checked),
     stopped, kept `config.json`, the new image opened the store (format 7),
     a scratch init showed the image writes format 8, so
     `store upgrade-profile` ran (`upgraded profile=current
     transactions-used=12 … previous-budget=4096`), `current` repointed,
     started, probe 101/281/205. 10.8 s wall.
   - probe `--post` on 452d62cb: accepted by control, read back 223.
   - `fn rollback`: restored the kept format-7 `config.json`, c3420013
     opened the store (including the article 452d62cb committed),
     repointed, started, probe held; a further probe `--post` read back. 1.3 s.
   - **Past one release** (`chain/`, fresh `small-community` node initialised
     by 4eca4148): 4eca4148 → c3420013 (no format change) → 452d62cb
     (7 → 8), a post read back on each; then rollback → c3420013 (config
     restored), rollback → 4eca4148, each read back its own post, and a
     third rollback was refused (`nothing to roll back`). History:
     [chain-state-history](spike-operator-2026-09-25/chain-state-history).
3. **Backup and restore.** `fn backup` on the running rehearsal node (stop,
   copy, restart, 0.32 s) opened the copy with the current image and wrote
   the tar with `MANIFEST.sha256` + `BACKUP` (`transactions=12 articles=12`)
   and a `.sha256` beside. `fn restore … --port 11934 --same-identity` into
   an empty root: both digests verified, `restored: transactions=12
   articles=12`, then `install-unit`, `start`, `probe --post` read back 223.
   Restoring into the now non-empty root was refused (exit 1).
   The default path (`checkpoint clone`, fresh incarnation) was **refused
   by ACL2** `(:REFUSED :UNBOOTSTRAPPED)` for both the c3420013 store and a
   fresh 452d62cb store: a news-only store carries no consumer incarnation,
   so restore stops and names `--same-identity` rather than choosing.
4. **Alerts.** Hook `alert-hook.sh` ([fired](spike-operator-2026-09-25/rehearsal-alerts-fired.txt)):
   `test` by `fn alert test`; `headroom` by `fn check` with the owner
   stopped and `headroom_min_percent = 100` (99 % free); `fault` by the
   chain unit reaching `failed` (seven `systemctl kill -s KILL` inside the
   start limit), after which `doctor` also fails `unit-state`.
   `refusal-rate` **did not fire and cannot yet**: 5 control-path and 3
   served-path refused POSTs (`441 … not carried here`) left no log line.
5. **Log rotation.** `log_max_bytes = 600`: `fn check` rotated `fn.log` to
   `fn.log.1.gz` (224 bytes); the live owner kept writing the truncated file
   at offset 0 (its fd stayed on the same inode).
6. **status --watch, top.** Both run; with an owner live they show unit
   state, listener, established connections, 1 m/15 m POST accepted/refused
   and connection counts from the log, and `owner-held` for the store side.
7. **Missions.** `small-community` (quickstart), `relay` and `archive`
   initialised on 452d62cb: `profile format=8 max-transactions=4294967295
   max-history-octets=1099511627776 max-record-octets=67108864
   max-article-octets=1048576 max-groups-per-article=16 …` (8 for
   small-community); relay/archive without `--group` exit 5. On 4eca4148 the
   mission fell back to `--profile scale`.
8. **Doctor.** 20 checks; on the rehearsal node 0 fail/0 warn after a
   backup; on the quickstart node 3 warnings (marker before first commit,
   no backup, no alert command).

## Findings

- **Refused POSTs are not logged** by the owner, on either path: only
  `accepted`/`duplicate` post lines and connection lines appear. The line is
  ACL2's (`fn-owner-log-line`), so a refusal-rate monitor has no signal.
- **Live status is refused** (`store is already locked`) on c3420013 and
  452d62cb, although docs/operator.md says status answers over the control
  channel while an owner runs. Headroom is unobservable while serving.
- **Clone needs a consumer incarnation**: `checkpoint clone` refuses every
  news-only store as `:unbootstrapped`, so a restore with a fresh identity
  is not available to an NNTP-only node.
- `principal set-password` answers `restart-required` even when no owner runs.
- The live node's unit points `ExecStart` at `fn-<rev>/bin/fn` directly;
  the `current` symlink layout lets upgrade and rollback be one rename.

## Deferrals (what `dev` must give an ACL2 owner)

Every one is marked `SPIKE` in `packaging/fn`.

| deferral | today | owner needed |
| --- | --- | --- |
| `[alerts]`/`[ops]` tables | stripped by bin/fn before the image reads fn.toml | the config grammar (`books/native-config.lisp`) |
| config projection | awk over the TOML subset | an `operator CONFIG show` projection |
| mission table | three rows in bash | a named, validated fn.toml + profile |
| doctor checks and thresholds | host observations, host judgments (30-day TLS, 1 GiB disk, modes) | a node-health verdict |
| alert rules | fault = unit failed or fault/uncertain line; rate over the check interval; headroom min | the same verdict, with refusals logged |
| upgrade format test | init a scratch store with the new image, compare `format=` | a `store needs-upgrade` answer |
| rollback soundness | the older image's `status` decides | the bounds-join §5 condition as a checked predicate |
| restore placement | clone, else operator's `--same-identity` | a restore verb |
| live status, obligations, pins | reported `owner-held` | a control-socket status query |
| log rotation | copy + truncate (a line can be lost) | reopen on SIGHUP in the owner |
| probe verdict | NNTP reply codes grepped | the node-probe assertions |

## Not claimed

No proof, no guard, no ACL2 change; nothing here is on `dev`. The probe is
from hbox itself over loopback. The `452d62cb` image is a lane's frozen
image, not a qualified release. Rollback past a record larger than the old
format's bound is not exercised. The script ran under bash 5 on Linux; macOS
paths (`launchd`, `ss`) are not implemented.

## The quickstart transcript

Run as [quickstart.sh](spike-operator-2026-09-25/quickstart.sh) from an
empty `/tank/fn/scratch/spike-operator/qs` (SHA-256 of the transcript
`a49522b0…`):

```

$ /tank/fn/scratch/spike-operator/tree/packaging/fn install /tank/fn/scratch/bounds-join/tree/build/images/452d62cb31fc16ea3d5cf9c2e3b48404299509ec 452d62cb
installed native fn under /tank/fn/scratch/spike-operator/qs/releases/452d62cb
accepted fn install 452d62cb at /tank/fn/scratch/spike-operator/qs/releases/452d62cb
[exit 0]

$ fn init --mission small-community --host 127.0.0.1 --port 11932
fn init: mission small-community: posting=true auth=true profile --max-article-octets 1048576 --max-groups-per-article 8
initialized /tank/fn/scratch/spike-operator/qs/store
accepted operator init
accepted fn init mission small-community
[exit 0]

$ printf "%s\n%s\n" "$PW" "$PW" | fn principal set-password alice --posting
Password: Confirm password: alice principal=4aa4777cebc73c20cba9b7b4aaa8f7e95d447b7baac8fb2240d11284e1a20ef4 posting=true
accepted operator principal set-password restart-required
[exit 0]

$ fn install-unit
accepted fn install-unit /home/hbox/.config/systemd/user/fn-qs.service and fn-qs-check.timer
[exit 0]

$ fn start
accepted fn start fn-qs.service
[exit 0]

$ fn doctor
ok        release            current -> 452d62cb
ok        image-digest       launcher+core match native-artifacts.txt
ok        store-open         owner live pid=2816162 since=Fri_2026-09-25_03:59:06_EDT
ok        store-mode         700
ok        store-profile      config.json 182 bytes; 
warn      marker             no committed-history marker (written at the first commit)
ok        disk               253838 MiB free
ok        tls-expiry         notAfter=Dec 28 07:59:04 2028 GMT
ok        tls-pair           key matches certificate
ok        tls-key-mode       600
ok        credentials        mode 600, 1 login(s)
ok        port               127.0.0.1:11932 listening
ok        unit-exec          fn-qs.service runs current
ok        unit-memory        MemoryMax=24G
ok        unit-state         active
ok        log                /tank/fn/scratch/spike-operator/qs/log/fn.log 0 bytes
warn      backup             no backup yet (fn backup)
warn      alerts             no [alerts] command
doctor fail=0 warn=3 undecided=0
accepted fn doctor 3 warning(s)
[exit 0]

$ FN_PROBE_USER=alice FN_PROBE_PASSWORD=$PW fn probe --post
accepted operator post ACCEPTED
probe post: accepted <fn-probe.20260925T075908Z.2816586@probe.invalid>
probe capabilities: 101
probe login: 281
probe read-back: 223 <fn-probe.20260925T075908Z.2816586@probe.invalid>
probe quit: 205
accepted fn probe
[exit 0]

$ fn backup
/tank/fn/scratch/spike-operator/qs/backups/fn-backup-20260925T075908Z.tar
accepted fn backup transactions=1 articles=1 -> /tank/fn/scratch/spike-operator/qs/backups/fn-backup-20260925T075908Z.tar
[exit 0]

$ fn top   (one frame)
fn top  2026-09-25T07:59:09Z  node /tank/fn/scratch/spike-operator/qs  release 452d62cb
unit    fn-qs.service active   listen 127.0.0.1:11932 up
conns   0 established
1m      posts accepted 1 refused 0   connections opened 1   faults/uncertain 0
15m     posts accepted 1 refused 0   connections opened 1   faults/uncertain 0   POST rate 0/min
head    ?% free (the smaller of the transaction budget and history bound)
store   owner live pid=2816681 since=Fri_2026-09-25_03:59:08_EDT
store   owner-held store-side fields (transactions, headroom) need the owner's control query
oblig   owner-held (no live query yet)
pins    owner-held
[exit 0]

$ fn status
owner live pid=2816681 since=Fri_2026-09-25_03:59:08_EDT
owner-held store-side fields (transactions, headroom) need the owner's control query
accepted fn status
[exit 0]
```
