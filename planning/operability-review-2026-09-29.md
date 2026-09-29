# Operability review: every operator flow, what it costs today, and its fluid version (2026-09-29)

Lane operability-review (Fable, deputised by ember). Source coordinate: dev
`f286c0204`. Everything below marked *measured* was walked by hand on hbox
(load 13 to 19 throughout) in `/tank/fn/scratch/operability-review/` with
batch BB's images of that revision (the developer launcher with
`FN_TEST_HEAP_MB`, and a release tarball frozen from the same tree,
`fn-6.6.0+f286c02041f1-linux-x86_64.tar.gz`, run through the installed
launcher with its heap probe); the walk logs are `walkA.log` to `walkF.log`
there. The live nodes were not touched. No code or documentation was changed
by this lane: the coordinator turns the table's rows into lanes. Ember's
prompt was one sentence of the FAQ, "*When the store is full:* Posts are
refused with 441; peers are told to try later. Limits are fixed at init.
Raise them with an export, then an import with --max-transactions", and the
question whether that is really the advice we give people. It is, in eleven
places (the list at the end), and it is the worst of a family.

## For ember

**The worst drags, ranked.** (1) *Changing any limit is a data move.* The
store's fifteen bounds (`max-transactions`, `max-history-octets`,
`max-article-octets`, ...) are sealed into `config.json` at `init` and the
only verb that writes a different one is `store import --FIELD N` into a
store that must not exist. So the ritual is: stop, `store export`, move the
store aside, `store import`, copy `keys/` and `auth.toml` back by hand, fix
ownership, start. Measured at 20,000 articles of 2 KiB: stop 1 s, export 31 s
(19 MB), import 140 s, first start 6.6 s (a full replay: the checkpoint does
not travel, and neither does the next start's, until enough new records make
a new one), about three minutes of downtime and six hand steps for a policy
change, and the same for a store of 100,000 is the 1,000-second class (the
full replay at `syn1m` measured 1,083 s). What else does not travel: feed
journals and pull cursors (undelivered articles to peers are lost and the node
re-peers), BP spools, the decisions journal. On top of it, the limits are not
even chosen: a `mission` sizes the store from the memory of the machine it is
run on (65,536 transactions under 8 GB, 131,072 under 12 GB, measured), so
the operator's capacity is an accident of `init`'s environment, and the heap
reservation is the *profile's* figure, not the data's, so a store made on a
big machine cannot be opened, exported or even `status`ed on a smaller one
(`refused machine-cannot-hold-profile heap=91639 MB machine=12288 MB` for a
20,000-article scale-profile store on every verb, measured). (2) *The store
being full has no remedy but (1).* Reclaim and the coming expiry free bytes,
never transactions (lane expiry's Q11 finding: a tombstone is still a
record), and the `441` text tells the poster "the node's operator can raise
it". (3) *Maintenance is downtime.* `store compact`, `checkpoint`, `reclaim`,
`export`, `inspect` and `recover` all answer `store is already locked` on a
running node (measured, every one). PKT-868 (lane operations-i4, READY, not
on dev at this revision) makes compact and checkpoint an owner request; the
rest stay offline, and expiry's lane says expiry while serving needs the
full recapture that the store-representation rows own. (4) *An upgrade is
`rm -rf /opt/fn`.* The installer refuses an existing prefix, the unit's
`ExecStart` names that prefix, and `docs/install.md` section 4 tells the
operator to export the store before removing the release. Measured gap for
an empty store, stop to LISTENING: 7.1 s (stop 1.0, rm 3.4, install 0.8,
start 1.9); at scale the gap is the open (13.6 s from a checkpoint at 40k,
55 s to 1,000 s for a full replay). There is no rollback. (5) *A full tiny
store died after a clean stop.* On a store made with `--profile development
--max-transactions 12`, eleven posts filled it; the owner's automatic
checkpoint (`CHECKPOINT auto sequence=8 ... segment=2 dropped=1`) ran, the
owner was stopped with SIGTERM (exit 0), and afterwards `status`, `recover`,
`run` and `store export` all refuse with `open refused
reason=checkpoint-damaged: the checkpoint that covers the dropped log
segments does not open`. The node has no path at all, and the export ritual
cannot even begin (the reproduction is at the end; the store is kept on hbox).
Whether it is the tiny profile or any store that checkpoints is being
characterised as this is written (walk F); either way an operator following
the FAQ's own advice meets it. (6) *The docs contradict the software*, in
both directions: `peer add`, `peer remove` and `peer feed pause` are live
(accepted on the running owner, measured) while three documents say "stop
the node"; `principal set-password` applies live (`applied`, measured) while
its own `help` says "restart to apply" and `operator.md` says "Restart the
node after you add a login"; a `SIGHUP` reopens the log (measured:
`reopened log signal=hup`) while `operator.md` says fn "never empties or
rotates it" and `mission` writes `[ops] log_max_bytes = 67108864`, `log_keep
= 7` and `keep_releases = 3`, keys nothing reads. (7) *Peering is a
thirteen-word incantation* plus a hand-written `FNAUTH1` file plus three file
exchanges, and changing one flag (streaming) is `peer remove` and the thirteen
words again. (8) *Two account systems*: `principal set-password` logins live
in `auth.toml` and are removed "by editing that file"; invitation accounts
are records with `account delete`; `account delete bob` on a principal is
`account-unknown` (measured). (9) *Backups are stop-and-copy*, an export is
"not a backup", and the atomic-snapshot backup the public node actually runs
(`tools/runbooks/public-node/fn-store-snapshot.sh`) is blessed nowhere in the
operator docs. (10) *Moving a node* is a `sed` over six absolute paths in
`fn.toml`, a unit edit (`ReadWritePaths`) and `store rebind-filesystem`; the
rebind itself is good (a clear refusal naming both filesystems, 0.07 s).
(11) *Retiring a node* has no verb: nothing drains the feeds or reports what
peers and BP obligations still hold. (12) `[alerts]` (`command`,
`headroom_min_percent`, `refusal_rate_per_minute`, `cooldown_seconds`) is
parsed by `books/native-config.lisp` and acted on by nothing in `host/`
except the headroom percent that `health` reads.

**The principle.** Limits and configuration are operator policy, recorded as
configuration events in the store (the way `policy set`, `group create`,
`account access` and `retention set` already are: a durable record, ACL2's
delta, replayed at every open, applied to the running owner at once,
measured 0.4 to 1.2 s each). A policy change is effective live, or at a
stated cheap restart, and never by moving data. The heap reservation is the
one thing fixed per process start (SBCL's dynamic space), so a change that
moves the reservation past what the running process holds is answered
"takes effect at the next restart (about N s, the last open's time), no data
moved", never "export and re-import". Anything impossible is refused by
name with what it would take (a smaller value, more memory, a bigger
machine, the next release). Every such verb is ACL2's decision over the
profile, the store's current use, the machine's observation and the running
reservation; the host writes what it is told.

**What changes.** The core is one verb, `fn operator CONFIG limits set FIELD
N` (with `limits show`), that rewrites the sealed profile frame in place:
ACL2 decides from the current profile, the store's use (`fn-sbud-used`, the
history octets, the largest stored record and article, the group count), the
requested field and the machine's observation, and answers one of: `applied`
(a field the running owner does not reserve for), `takes effect at the next
restart (about N s), no data moved` (a field in the heap figure:
`max-transactions`, `max-history-octets`, `max-article-octets`, the group
ceilings), or a refusal by name (`below-current-use field=… use=…`,
`machine-cannot-hold-profile heap=… machine=… would-take=…`). The import
path's "the archive's profile, with any field raised, is the new store's"
already contains the decision; what is new is writing it into the existing
store's `config.json` (atomic rename), keeping the checkpoint, and one
keystone: a store written under profile P opens to the same state under any
admitted P' that raises P (profile monotonicity of `fn-spo-config-open` and
the checkpoint open). With that verb the mission's silent sizing stops
mattering (start small, grow), the "store full" answer becomes a command,
and `store import --FIELD N` returns to being restore. The second change is
that every offline maintenance verb becomes an owner request, as PKT-868 did
for compact and checkpoint: `export` (a pinned root, streamed in bounded
batches off the mutex), `inspect` (a served read), `recover` as a report
(`status` already is one), then `reclaim` and expiry (the recapture and live
swap the expiry lane named; this one belongs with the store-representation
rows and is the L of the list). The third is the release layout:
`PREFIX/releases/VERSION` and `PREFIX/current`, the unit's `ExecStart`
through `current`, and `fn upgrade TARBALL` = verify, install beside, stop,
switch, start, health, with the gap stated before it begins and a refusal by
name when the format word differs (what it would take: redeploy fresh); a
rollback is the switch back. The rest are small: `peer add` with named
flags and `peer set NAME --streaming false`, `peer login NAME` writing the
`FNAUTH1` file; one account verb set over both kinds of login; `retire`;
relative paths in `fn.toml`; the `SIGHUP` line and an in-node rotation
decision or the dead `[ops]` keys deleted; `[alerts] command` implemented
or deleted; the refusal reasons that are missing (the operator's `post`
prints `REFUSED` with no reason, its log line has none, `init`'s
`MAX-HISTORY-OCTETS-BELOW-MAX-RECORD-OCTETS` names no numbers, `init
--max-transactions 12` alone is refused with a 10 TB reservation because the
unnamed fields default to the D27 profile that no machine holds).

**Order and size.** S rows are documentation and grammar truth (the wrong
advice, the help texts, the dead keys, the reasons) and the small verbs;
they can land this week without touching a wide book except
`native-operator`/`native-admin` (the grammar, 528 dependents: batch them
into one edit under the wide-book token). M rows are `limits set`, live
export/inspect, the release layout and `fn upgrade`, `retire`, the peer and
account verbs, the alerts hook. L rows are live reclaim/expiry and any
return of transaction capacity (D13's remember window). The bug in (5) is
before all of them: a node the FAQ's reader can make cannot be reopened.

**What I could not settle.** Whether raising a heap-figure field can ever be
live: the figure is decided once per process, so the honest answer today is
"next restart", and the restart is cheap exactly when the checkpoint is
kept (2.5 s at 20k from a checkpoint against 6.6 s of full replay after an
import at the same size, measured; 13.6 s against 55 s at 40k in the
evidence). A future owner that starts with headroom over its figure could
take some raises live; that is a design question for the F8 rows, not this
review. And the true cost of `install.sh`: 36 s the first time on hbox's ZFS
(the SHA256SUMS check and copy of the two cores, cold) and 0.8 s the second;
a release with one core and a warm cache is the small number.

## Measured, with scope

All on hbox (24 cores, load 13 to 19, ZFS `/tank`), images of dev
`f286c0204`, one run each unless stated; a shared, loaded box, so read them
as the order of magnitude, not the figure.

| what | measured |
| --- | --- |
| `mission small-community` | 0.2 s; the profile it picks: 65,536 transactions / 32 MiB under an 8 GB budget, 131,072 / 64 MiB under 12 GB, `reservation=1968 MB` refused under 1,536 MB |
| `init` (empty store) | 1.8 to 2.4 s; the installed launcher's heap probe adds about 0.1 s to every verb |
| start, empty store | 0.2 to 1.9 s to LISTENING; stop (SIGTERM) 0.05 to 1.0 s |
| a live configuration verb (group, account, policy, retention, motd, capacity, peer add/remove/pause) | 0.4 to 1.2 s each (a durable record); `tls reload` 0.06 s; `status`/`health` on the running owner 0.06 to 0.15 s |
| 20,000 articles of 2 KiB (chain-20000, scale profile) | open from checkpoint 2.5 to 3.1 s; clean restart gap 3.3 s; restart after `kill -9` 2.5 s; offline `recover` 2.6 s, `compact` 11.9 s, `reclaim --dry-run` 9.6 s, `export` 30.8 s (19 MB), `import --max-transactions 2000000` 140 s; first start after import 6.6 s and the second 7.0 s (both full replays: no checkpoint travels); offline `status` 2.0 s (5.3 s after the import) |
| the limit-raise ritual at 20k | stop + export + mv + import + copy keys + start: about 180 s of downtime, 6 hand steps |
| the limit-raise ritual at T = 12 (11 articles) | could not begin: `export` refused `checkpoint-damaged` after a clean stop (the bug) |
| binary upgrade, empty store | 7.1 s stop to LISTENING (stop 1.0, `rm -rf` 3.4, `install.sh` 0.8, start 1.9); `install.sh` cold 36.3 s |
| an `fn.toml` edit (add `tls_port`) | restart gap 1.3 s at an empty store; at scale, the open's time |
| backup by `cp -a` of an empty node | 11 to 16 s on that ZFS (the filesystem's cost, not fn's) |
| move to another filesystem | `status` refuses naming both filesystems; `store rebind-filesystem` 0.07 s |
| store full (T = 12) | posts 12 and 13 refused; `health` exit 23 `space-pressure held transactions=11/12`; `group create` still accepted (configuration generations are separate); the operator's `post` prints `refused operator post REFUSED` and logs `refused post path=control message-id=…` with no reason |
| from the evidence (not this lane) | 40k from checkpoint 13.6 s, full replay 55 s, `compact` 40 to 139 s at 4.6 to 7.5 GB; 10k of 32 KiB full replay 55 s; syn1m full replay 1,083 to 1,258 s |

## The flows

Legend for "today": steps are hand steps after the decision; downtime is the
node not serving; data moved names what is copied or rewritten. Sizes: S a
lane of a day (docs, grammar, a small verb, a shell change), M a lane with a
new decision, its keystone and a native test, L a lane that touches the
store representation or an open decision.

| flow | today (steps, downtime, data moved) | fluid version | what it needs (verbs, books, config events) | size |
| --- | --- | --- | --- | --- |
| install | sha256, untar, `install.sh` (root; refuses an existing prefix); 3 steps, no downtime; copies the release (36 s cold on ZFS) | the same, but into `PREFIX/releases/VERSION` with `PREFIX/current`, so a later release installs beside the running one | `packaging/install.sh`, `fn.service.in` (`ExecStart` through `current`), `docs/install.md` | S |
| first init | `mission`, a certificate by hand (`openssl` one-liner), `init`, `policy set path-identity`, `set-password`; 5 steps; the store's capacity is chosen by the machine's memory at `init`, printed as `reservation=`, never as posts; a service `MemoryMax` must be matched by `FN_INIT_BUDGET_MB` by hand | `init` prints the capacity in posts and says it can be raised later with `limits set`; the mission sizes for the service's limit (the installer writes `MemoryMax` into the unit from the same decision) instead of for the machine `init` happened to run on; `init` finishes its own half-made store (PKT-647) | `books/native-mission.lisp` (the sizing), `heap-reservation.lisp` (`init`'s line), `install.sh`; `limits set` below | S (once `limits set` exists) |
| TLS install | copy or make `tls/cert.pem`, `tls/key.pem` (mode 0600); the paths are absolute in `fn.toml`; 2 steps | the same; `install.sh --tls DIR` or `mission --cert-dir` copying a Let's Encrypt layout, as `deploy_fresh.sh --cert-dir` already does | `packaging/install.sh`, `books/native-mission.lisp` | S |
| TLS renewal | `tls reload` on the running owner, 0.06 s, no restart; a certificate for other names needs a restart (1 to 3 s small, the open at scale); the ACME hook exists (`tools/runbooks/public-node/acme/fn-cert-install.sh`) | keep; `tls reload --names-changed` to accept a renamed certificate live (the refusal `names-dropped` protects peers that pin a name, so the flag is the operator taking that) ; ship the ACME hook in `share/fn/` | `books/tls-reload.lisp` (`fn-tlsr-decide` with an operator-accepted name drop, PRF-212 amended), `packaging/` | S |
| account invite / redeem | `account invite`, send the code, `fn redeem` or the web page; live, 0.7 s; the code's expiry is printed as `pending expires 843958168900` (a millisecond reading, not a date) | keep; print the expiry as a UTC date | `books/native-admin.lisp` (the `account list` render) | S |
| password / bind | `principal set-password` reads the password twice from stdin or the tty (a `--password` flag is refused, measured); answers `applied` live or `effective-at-next-start`; its `help` says "restart to apply" and `operator.md` says "Restart the node after you add a login" | keep the live apply; fix the help and the doc; one verb set for both kinds of login (`account set-password LOGIN`, `account delete LOGIN` for principals too, writing `auth.toml` and reloading the owner as `set-password` does) | `books/native-operator.lisp` (help), `native-auth-admin.lisp`, `docs/operator.md` | S |
| account delete | `account delete` for redeemed accounts (live); a principal is removed by editing `auth.toml` and restarting | `account delete` for both, live (the `auth.toml` write + owner reload path exists) | `books/native-auth-admin.lisp`, `host/native/auth-admin.lisp` | S |
| groups (create, retire, describe, moderate, subscribe-default) | live and offline, 0.4 to 1.2 s; fine | keep | | done |
| peering, both ways | `peer keygen`, `peer invite` (9 words), send a file, `peer accept` (5 words), send a file back, `peer confirm`; then `set-password --principal`, a hand-written `FNAUTH1` file (`umask 077; printf`), `peer add` with 13 positional words, `peer pull`; the docs say to stop the node for `peer add`/`remove` (they are live, measured); changing one flag is remove + the 13 words | `peer confirm` writes the full peer record it already knows (address, identity, groups); `peer login NAME` asks the password and writes the `FNAUTH1` file; `peer add`/`peer set NAME --streaming false --tls implicit --anchor PEM --login FILE` with named flags, live (a delta over the live peer table, which exists) | `books/native-admin-peer.lisp`, `native-operator.lisp` grammar (wide: one edit), `host/native/peer-invite.lisp`; docs | M |
| changing `max-transactions` (or `max-history-octets`, `max-article-octets`, any of the 15) | stop, `store export`, `mv store`, `store import --FIELD N`, copy `keys/` and `auth.toml`, fix ownership, start; 6 steps; downtime 3 min at 20k, the 1,000-second class at 1M; data moved: the whole history twice; lost: the checkpoint (full replays until a new one), feed journals and cursors, BP spools, decisions | `fn operator CONFIG limits set max-transactions N`: ACL2 decides against the profile, the store's use and the machine; writes the sealed frame in place (atomic rename); answers `applied`, or `takes effect at the next restart (about N s), no data moved`, or refuses by name with what it would take; `limits show` prints each field, its use and the reservation it costs | new book `store-profile-set` (over `byte-store-frame.lisp`'s `fn-bs-config-frame-for-profile`, `store-profile-open.lisp`, `heap-reservation.lisp` `fn-heap-status-decide`); KEYSTONE: a store written under P opens to the same state under any raise P' (profile monotonicity of the open and the checkpoint open); grammar in `native-operator.lisp`; host `operator.lisp`; a native test with a death cut across the rename; `store import --FIELD` stays for restore | M |
| heap budget (`MemoryMax`, `FN_INIT_BUDGET_MB`) | the unit's `MemoryMax` is edited by hand and must hold the profile's figure, found at the next start (`machine-cannot-hold-profile`); a bigger machine gives no more capacity; a smaller one cannot open, export or `status` the store | `limits show` prints the figure each field costs; `limits set` refuses a raise the service's limit cannot hold, naming the `MemoryMax` it would take; a store that does not fit the machine can still be *exported* (the export needs the open's transient, not the profile's bounds: give `export` its own figure) | `heap-figure.lisp` `*fn-heap-list-actions*` (export as a list action with its own bound), `install.sh` (the unit's `MemoryMax` from `init`'s decision) | M |
| connection counts, exposure rows | `policy set exposure-*` live, memory-checked (`connections-exceed-memory`, measured), 0.7 s; the refusal names no bound; `help policy` lists 2 of the 11 keys | keep; the refusal prints `holds=B` as the run's line does; `help policy` lists every key | `books/native-admin.lisp`, `native-operator.lisp` help | S |
| other `fn.toml` keys (`tls_port`, `[listener] host`, `[web]`, `[log] path`, `[auth]`) | edit the file, restart (1.3 s empty; the open at scale); `install.sh --reader` then "restart the node" | keep the restart for listener changes, but say the gap before it (`fn operator CONFIG restart` prints "about N s" from the last open, stops and starts under the service manager); `[web]`, `[auth]` and `[log]` as configuration events applied live where nothing binds a socket | `books/native-config.lisp` (which keys are start-only), a `restart` verb over `systemctl`/`rcctl` | S/M |
| store full | posts refused `441 … the node's operator can raise it`, peers deferred `436`, `health` exit 23; the only raise is the export ritual; reclaim and expiry never return transactions (Q11) | `limits set max-transactions N` (above); the `441` text names the verb; a `remember DAYS` window returning transaction capacity by forgetting old tombstones (D13, ember's decision, the expiry lane's packet) | as `limits set`; D13 + `store-files.lisp` (`fn-sf-record-listp`, 802 dependents) for the window | M (the verb), L (the window) |
| backup | stop, `cp -a` the node folder, start (docs); the export is "not a backup" (no keys, TLS, passwords, feed queues); the public node takes hourly ZFS snapshots by a runbook the operator docs never mention | the docs bless an atomic filesystem snapshot as a valid backup (it is a power-cut image, which the open recovers by name); `store snapshot DIR` on the running owner: a fenced copy of the checkpoint, the covered segments and `config/`, `keys/` and `auth.toml`, taken in batches off the mutex, so a backup needs no stop and no ZFS | docs (S); the verb over PKT-868's request path and `store-export-stream.lisp` (M) | S + M |
| restore | stop, put the copy back, `store rebind-filesystem` if the filesystem changed, start; or `store import` (needs an absent store, the keys copied by hand, and every later start replays fully) | `store import` carries the checkpoint and the key files' *absence* is a named refusal at the end of the import ("keys/ missing: copy STORE.old/keys or run node-secret create"), not at the next start | `books/store-export.lisp`, `store-import-*.lisp` | S |
| log growth | `[log] path` grows without bound; a `SIGHUP` reopens it (measured, undocumented); `mission` writes `[ops] log_max_bytes`/`log_keep` that nothing reads; `fn.toml.example` says copytruncate | document `systemctl kill -s HUP fn` and logrotate `postrotate`; either implement the rotation the keys promise (ACL2's reopen decision `fn-olr-decide` extended with a size rule) or delete the keys | `books/owner-log-reopen.lisp`, `native-mission.lisp`, docs | S |
| compaction | `store compact` offline only (`store is already locked`, measured); 11.9 s at 20k, 40 to 139 s at 40k, 4.6 to 7.5 GB; the owner also checkpoints by itself | PKT-868's request on the running owner (lane operations-i4, READY): merge it; bound the compaction's memory by the step | merge; `owner-compact-request.lisp` | done in a lane |
| reclaim | `store reclaim` offline only; frees bytes, never transactions; 9.6 s dry run at 20k | reclaim as an owner request over the recapture-and-swap the expiry lane named; until then, say in the docs that it needs a stop and returns disk, not posts | store-representation rows (A) + `store-reclaim-*.lisp` | L |
| expiry / retention | `retention set` live; `retention expire` (lane expiry, not on dev) offline through reclaim | the owner's own periodic reclaim under the retention policy (as the checkpoint is automatic), live | as reclaim | L |
| binary upgrade 6.6.0 to 6.6.1 | stop, `rm -rf /opt/fn`, `install.sh` (which asks the release about the store first, good), start; 4 steps; 7.1 s empty, the open at scale; no rollback; `docs/install.md` section 4 adds an export first | `fn upgrade TARBALL`: verify, install beside, ask the new release about the store, print the gap ("about N s"), stop, switch `current`, start, `health`; refused by name when the store format word differs (what it would take: redeploy fresh); `fn rollback` is the switch back | `packaging/install.sh`, `fn.service.in`, a shell verb (no ACL2 decision except the format question the release already answers); docs | M |
| health / monitoring | `status`, `health` (one line per state, exit codes 18 to 28, `--watch`), good; `[alerts]` rows parsed, `command`/`refusal_rate`/`cooldown` unused; the disk line and exposure counts are good | keep; implement `[alerts] command` (the owner runs it on a held state, cooled down) or delete the three keys; a `health --json` line for scrapers | `books/native-health.lisp`, host | S/M |
| crash recovery | nothing to do: the next start replays from the checkpoint (2.5 s at 20k, measured after `kill -9`); `recover` reports first if wanted; stale sockets are removed by name; good | keep; `recover` as a running-owner report too (it is `status` with the freshness verdict) | | done |
| moving a node | stop, copy the folder, `sed` six absolute paths in `fn.toml`, edit `ReadWritePaths`, `store rebind-filesystem`, start; 6 steps | paths in `fn.toml` relative to its own directory (absolute still accepted); the unit's `ReadWritePaths` from `--node`; keep `rebind-filesystem` (it is the right acknowledgment) | `books/native-config.lisp` (`fn-ncfg-absolutep` relaxed to "absolute or relative to the config's directory", resolved by ACL2), `install.sh` | S |
| retiring a node | no verb: stop, and whatever peers and BP obligations held is silently held | `fn operator CONFIG retire [--drain SECONDS]`: refuse new connections by name, pause pulls, let feeds drain for the window, then print per peer what is undelivered and the obligation ledger, a final checkpoint, stop; the export afterwards is the archive | `books/native-admin.lisp` (a request kind), `owner-feed.lisp`, `retention.lisp` (the report) | M |
| interrupted `init` / `import` | `init` refuses `STORE-EXISTS` on its own half-made store (PKT-647); `import` names the folder to remove | `init` recognises its own unfinished store (no genesis frame, no checkpoint, no records) and finishes or clears it | `books/store-init-publication.lisp` | S |

## Documentation advice that is plainly wrong, or contradicts the software

Each with its file and the sentence; "wrong" means either the software does
otherwise today, or the advice sends the operator through a data move for a
policy change.

1. `docs/articles/fn-faq-5.txt`: "*When the store is full:* Posts are refused
   with 441; peers are told to try later. Limits are fixed at init. Raise
   them with an export, then an import with --max-transactions." — the
   sentence that started this; the fluid version is `limits set`.
2. `docs/operator.md` "When the store is full": "The store's size limits are
   fixed when it is made. To raise them, move to a new store with bigger
   limits: `store export`, a fresh install, then `store import DIR
   --max-transactions N --max-history-octets N`" — and it says "a fresh
   install", which is not even needed.
3. `docs/operator.md` "Store settings": "A store's size limits are set by
   `init` and never change" and "or raise them later with `store export` and
   `store import --max-... N`" (twice on that page).
4. `docs/operator.md` "The node does not start": "`machine-cannot-hold-profile`
   ...: Raise the limit, or move the store to settings that fit (`store
   export`, then `store import` with smaller `--max-...`)" — the export is
   refused on that machine by the same probe (measured: every verb, export
   included, answers `machine-cannot-hold-profile`).
5. `docs/install.md` section 4: "`store export` and `store import` move a
   store between installs of the same format, for example to raise a limit
   fixed at `init`" and the whole reinstall recipe that exports before
   removing the release: an upgrade keeps the store folder; the export is
   only for a limit change, which should not need it.
6. `docs/articles/fn-faq-6.txt` (generated from fn's own tables): "21
   exhausted: A counter (transactions or held space) ran out. Only an
   export and import raises it" and "23 space-pressure: ... move to larger
   limits" — the tables themselves carry the advice, so the fix is in
   `books/native-health.lisp`'s text.
7. `books/native-operator.lisp` help for `init`: "the mission fixes the
   profile; a different one is a reinstall: store export, then store import
   --FIELD N" and its usage line "To raise a bound later: fn operator CONFIG
   store export DIR, reinstall, then fn operator CONFIG store import DIR
   --FIELD N"; `docs/operator-internals.md` "Deploy a new release": "`store
   export` and `store import` move a store between installs of the same
   format (a larger profile field, a new disk)"; `specs/host.md` HST-014.
8. `docs/operator.md` section 8 and `docs/peering-with-a-friend.md` "Known
   gaps": "Stop the node, run `peer remove NAME`, add the peer again with
   `false` as the streaming word, and start the node"; and
   `docs/operator-internals.md` "Initialize": "Run these while the owner is
   stopped; the exclusive store lock refuses offline administration against
   a live owner" — `peer add`, `peer remove` and `peer feed pause` are
   accepted by the running owner (measured, 0.4 to 1.0 s each).
9. `docs/operator.md` "Passwords": "Restart the node after you add a login
   or change a password this way" contradicts the same page's "the last
   word ... says when the change applies: `applied` (now: the running node
   reloaded its logins)"; the verb's own help: "set-password reads the
   password twice from the terminal or two lines of stdin, restart to
   apply" — it answered `applied` on a running node (measured).
10. `docs/operator.md` "The log": "fn only adds to it; it never empties or
    rotates it"; `packaging/fn.toml.example`: "fn never truncates or rotates
    it, so give it to your log rotation tool (copytruncate)" — a `SIGHUP`
    reopens the file (measured; `books/owner-log-reopen.lisp`, PKT-101), so
    the standard rename-then-signal rotation works; and `mission` writes
    `[ops] log_max_bytes = 67108864`, `log_keep = 7`, `keep_releases = 3`,
    `scope = "user"`, which nothing reads (`host/` has no consumer).
11. `docs/operator.md` "Back up": "Copying while the node runs may miss the
    newest article" is true of `cp`, but the page never says that an atomic
    snapshot (ZFS, LVM) is a valid backup, while
    `tools/runbooks/public-node/fn-store-snapshot.sh` relies on exactly
    that ("the store as a power cut at that instant would leave it").
12. `docs/operator.md` "Settings file": "`[alerts] headroom_min_percent`
    (default 10)" is the only alerts key documented; `mission` writes three
    more that do nothing.
13. `docs/operator.md` section 7: "how many connections at once (31 if
    unset; each costs memory)" — fine, but the `help policy` text lists
    only `path-identity` and `posting-policy`, so an operator who asks the
    program is told the nine exposure keys and `complaints-to` do not exist.
14. `docs/public-node.md` "Peering": "this node does not peer until the fix
    lands" against `planning/now.md`: the two nodes are peered.
15. `docs/operator.md` "Other commands": "`capacity N`: the room reserved
    for held articles" — a one-line description of a verb whose effect
    (`charge-capacity` in `status`) is explained nowhere.

## Bugs found while walking (not advice)

- **A full tiny store cannot be reopened after a clean stop.** Developer
  image of `f286c0204`; `init --profile development --max-transactions 12
  local.general` (`max-open-suffix` 12); eleven `operator post`s over the
  control socket; the owner logged `CHECKPOINT auto sequence=8 suffix=8
  octets=16637 steps=6 ms=382 segment=2 dropped=1`; SIGTERM, `run stopped
  exit=00`; then `status`, `recover`, `run` and `store export` all answer
  `open refused reason=checkpoint-damaged: the checkpoint that covers the
  dropped log segments does not open`. The store is kept at
  `hbox:/tank/fn/scratch/operability-review/walkE/node/store` (with its
  `owner1.log` and `fn.log` beside it). Walk F (T = 40 default suffix, T =
  40 with `--max-open-suffix 200`, T = 2,000) says whether it is the tiny
  suffix or any automatic checkpoint; its log is `walkF.log` there.
- The operator's `post` refusal prints `refused operator post REFUSED` and
  logs `refused post path=control message-id=…` with no reason word, while
  the NNTP poster gets the full `441` sentence.
- `consumer show` prints the account list (`pending expires …`, `access
  alice …`).
- `account invite` and `account list` print the expiry as a raw millisecond
  reading.
- `init` refusals name no numbers: `MAX-HISTORY-OCTETS-BELOW-MAX-RECORD-OCTETS`,
  `MAX-RECORD-OCTETS-BELOW-AN-EVENT-KIND`; and `init --max-transactions 12
  GROUP` with no `--profile` is refused with `reservation=10493234 MB`
  because every unnamed field takes the D27 default (H = 1 TiB), which no
  machine holds (PKT-582): the default for an unnamed field should be the
  mission's or the development preset's.
- `policy set exposure-connections abc` and `policy set bogus-key 1` answer
  the two-key usage line, not "unknown key" or "not a number".
- `status`/`health` on a stopped store open it in full (2.0 s at 20k, 5.3 s
  after an import) on every call, so `status --watch` on a stopped node would replay the
  store every N seconds.

## Obstructions and asks (this lane)

- The harness's concurrent-subagent cap (20) was full at launch, so the
  document survey ran in one context; fine for a review, but a second
  Explore agent would have halved the reading.
- No published image set under `hbox:/tank/fn/images/` yet; batch BB's tree
  at the same revision had both images, which saved the 25-minute build.
  The tooling note in LANE-PREAMBLE about `--image-set` will make this the
  normal path.
- The fixtures are made with the developer launcher; the installed
  launcher's heap probe refuses every scale-profile fixture on a 12 GB
  scope. A note in `tools/fixtures.py`'s README (or a `small` profile
  fixture) would save the next lane a wasted walk.
- The mission's `init` needs 1,968 MB of budget on this image; the live hbox
  node's unit carries `MemoryMax=2G`. Worth a look by whoever redeploys it.
