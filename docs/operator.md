# Running your node

The short version is in Usenet articles: [part 4, running a node](articles/fn-faq-4.txt)
(the disk, groups, logins, certificates, exposure) and
[part 5, when things go wrong](articles/fn-faq-5.txt) (uncertain answers,
when the store is full, backups, new releases). Storage requirements are
part 4's "The disk". Every health code and refusal:
[part 6](articles/fn-faq-6.txt). The engineers' reference:
[operator-internals.md](operator-internals.md).
This page stays the full reference; what changed after the articles were
written (batch AY) is here first and folds into the articles next.

This page is for the person who looks after an fn node. It assumes you set
the node up with [Installing fn](install.md). Words you may not know are in
[the short glossary](articles/fn-faq-1.txt). The exact details, and
material for developers, are in [the engineers' reference](operator-internals.md).

In the commands, `CONFIG` is your settings file, for example
`/var/lib/fn/fn.toml`. Run commands as the service account (`fn`, or `_fn`
on OpenBSD), as in [Installing fn](install.md#2-set-up-the-first-node).
Every command ends with one of the answers in [exit codes](#exit-codes).

## 1. Choose the disk for the store

fn says an article is saved only after the disk confirms it. That promise is
only as good as the disk. The store's file system must really write data
when asked (fsync, with write barriers on):

- ext4 with its default settings. Never `barrier=0` or `nobarrier`.
- ZFS with `sync=standard`. Never `sync=disabled`.
- No drive cache that ignores flush requests, unless the drive has
  power-loss protection.
- Never tmpfs or another memory-only file system for a real node.

This was tested by cutting the power 1,281 times on ext4 with barriers: no
confirmed post was lost. With `barrier=0`, confirmed posts were lost in 36 of
40 cuts.

What fn checks for you:

- At start, and in `status` and `health`, fn warns when the store is on
  `nobarrier`, `barrier=0`, tmpfs or ramfs. It cannot see ZFS
  `sync=disabled` or a drive's cache. Those are yours to check.
- A node made with `mission` refuses to start on such a disk. To change
  that choice (and accept the risk), or to turn it back on:

  ```sh
  fn operator CONFIG store rebind-filesystem --storage-require-durable off
  ```

### Give the store its own disk

Put the store on its own volume that is mounted at boot. `init` records which
file system the store is on. If the volume is not mounted, fn refuses to
open rather than start an empty store in its place:

```
store filesystem changed: expected ext4 at /srv/fn-public from /dev/nvme1n1p1 (fsid ...), found ext4 at / from /dev/nvme0n1p4 (fsid ...); mount the node volume or run `store rebind-filesystem` after moving the store deliberately
```

1. If you did not mean to move the store: mount the volume and start again.
2. If you moved it on purpose (a new disk, a restored backup, another
   machine), stop the node and record the new place:

   ```
   fn operator /etc/fn/fn.toml store rebind-filesystem
   ```

An empty folder where the volume should be is refused as
`store filesystem unrecorded`.

### On OpenBSD

On OpenBSD 7.9, the default disk format is **not safe** for fn. Power cuts
showed this:

- **FFS2**, the installer's format for every partition, can lose the newest
  saved articles after a crash. Then the node will not open until you
  restore it.
- **A disk with a write cache** (including many virtual disks) can lose data
  on either format. OpenBSD never asks the disk to empty its cache. For a
  virtual machine, the host must write through (for qemu,
  `cache=none` or `writethrough`).
- **FFS1** (`newfs -O 1`) on a disk without a write cache lost nothing.

So before `init`, give `/var/fn` its own partition made with `newfs -O 1`.
`softdep` makes no difference. With a second, empty disk (here `sd1`: check
with `sysctl hw.disknames`; this **erases** that disk), as root, before
`install.sh`:

```sh
fdisk -iy sd1
printf 'a a\n\n\n4.2BSD\nw\nq\n' | disklabel -E sd1
newfs -O 1 /dev/rsd1a
mkdir -p /var/fn
echo '/dev/sd1a /var/fn ffs rw,nodev,nosuid 1 2' >> /etc/fstab
mount /var/fn
```

To see a partition's format, as root:
`dumpfs /dev/rsd0X | head -1` prints `FFS1` or `FFS2`. To move a store off
FFS2: `store export`, make the FFS1 partition, then `store import`
([moving data](install.md#4-reinstalling)).

Also on OpenBSD:

- fn must be installed on a file system mounted `wxallowed` (`/usr/local`
  is, by default).
- fn works out its memory from the store's size limits, and `init` prints
  the figure (`reservation=... MB`). OpenBSD caps each program's memory by
  login class (1,536 MB for `default`, 4,096 MB for `daemon`, which the
  service uses). `init` counts that cap: on a small machine it picks a
  smaller store.
- Start fn by hand only from a folder its user can read (`cd /var/fn`),
  or it stops with `getcwd: Permission denied`. The service does this for you.

## 2. Start, stop and check

Start and stop fn with the service manager:

| | Linux | OpenBSD |
| --- | --- | --- |
| start | `systemctl start fn` | `rcctl start fn` |
| stop | `systemctl stop fn` | `rcctl stop fn` |
| is it running? | `systemctl status fn` | `rcctl check fn` |

A stop is always clean: fn finishes its work, then exits. On Linux the
service restarts fn only after a failure, never after a stop.

On OpenBSD, rc.d never restarts fn: after a crash (or `kill -9`),
`rcctl check fn` says `fn(failed)` and the node stays down until you run
`rcctl start fn`. At boot `rcctl enable fn` starts it. To have it started
again within five minutes of a crash, add to root's crontab
(`crontab -e`):

```
*/5 * * * * rcctl check fn >/dev/null || rcctl start fn >/dev/null
```

If fn fails to start five times in a minute, systemd stops trying. After
that, every `restart` is quietly refused while looking like success. Run
`systemctl reset-failed fn` first.

If you move the store or log folder, add the new place to `ReadWritePaths`
in the service file. Otherwise the service cannot write there.

On a Mac, install `share/fn/launchd/net.fn.plist` as
`/Library/LaunchDaemons/net.fn.plist`, then run
`sudo launchctl bootstrap system /Library/LaunchDaemons/net.fn.plist`.

**Without root.** Install with
`sh fn/install.sh --prefix $HOME/fn --node $HOME/fn-node --no-service`, then
run `systemd-run --user --unit fn -p MemoryMax=8G $HOME/fn/bin/fn operator $HOME/fn-node/fn.toml run`.
An administrator's `loginctl enable-linger USER` keeps it running after you
log out.

### Status

```
fn operator CONFIG status
```

This shows how many articles the store holds and how much room is left
(`headroom`). It works while the node runs, and while it is stopped.
`status --watch 60` repeats every 60 seconds.

### Health

```
fn operator CONFIG health
```

You will see one line for each possible problem, then `accepted operator health`:

```
health exit=22 state=unqualified-profile
fenced clear
exhausted clear
unqualified-profile held format=9 development
space-pressure clear
no-route clear
stranded-transfer clear
unavailable-peer held peers: hub
receipt-debt clear
disk clear
accepted operator health
```

`clear` means fine. `held` means a problem. Several can be held at once.
The command ends with the code of the first problem, so scripts can use it.
The [table of codes](install.md#when-the-node-refuses-something) says what
each one means and what to do. `unobserved` means fn could not check that
line (the peer lines need the node running).

`fenced` with `reason=starting` just after a start means the node is still
opening its store. Wait a moment and ask again.

A node open to the internet adds four `exposure` lines. They show
connections, refusals and limits in force.

### The log

The log is `log/fn.log` in the node folder (on OpenBSD, syslog). fn only
adds to it; it never empties or rotates it. Each post and each connection
gets one line, starting with the outcome:

```
accepted reader connection=2 time=2026-09-22T21:04:33Z
accepted post path=served connection=2 message-id=<a@example.invalid> agent=news.example.org time=2026-09-22T21:04:34Z
accepted peer connection=3 peer=innA time=2026-09-22T21:04:35Z
```

If a reader shows up as a `peer`, its address matches a peer's address in
your settings. fn tells readers and peers apart by address alone.

## 3. Groups

Add a group, or stop serving one. The node can be running:

```
fn operator /etc/fn/fn.toml group create fn.announce
fn operator CONFIG group retire fn.announce
```

A retired group keeps its articles. Create it again and it comes back as it
was. Names are words of letters, digits, `+`, `-` and `_`, joined by single
dots. Names starting with `example` or `poster` are refused. Avoid names
starting with `to.` or `control.`, names with a part `all` or `ctl`, and
`junk`: other servers treat those specially.

One of those is made for you. A node set up with a `mission` also serves
`control.cancel`: a reader's own cancel is filed there. Keep it.

Choose which groups a new reader is offered first (with no names, all
readable groups are offered):

```text
fn operator /etc/fn/fn.toml group subscribe-default fn.announce fn.test
```

### Moderated groups

In a moderated group, posts wait for a moderator. First make a queue group,
then name the moderators by their logins:

```
fn operator /etc/fn/fn.toml group create fn.announce.moderation
fn operator /etc/fn/fn.toml group moderate fn.announce --moderators alice,bob
```

1. A post without an `Approved:` line is answered `240` but held in the
   queue group. It is not published yet.
2. A moderator reads the queue with any newsreader. Only moderators can see
   the queue, and it is never sent to peers.
3. To approve, the moderator logs in and posts the held article again with
   an `Approved:` line added.

An `Approved:` line from anyone else is refused. `--queue GROUP` names a
different queue group, and `--submission ADDRESS` records a submission
address. To see what is waiting:

```
fn operator /etc/fn/fn.toml moderation list fn.announce
```

You can also decide from the shell, naming the moderator:

```
fn operator /etc/fn/fn.toml moderation approve '<post@example.org>' --moderator alice
fn operator /etc/fn/fn.toml moderation reject '<post@example.org>' --moderator alice --reason off-topic
```

`approve` posts the article as alice's approval would. `reject` withdraws
it from the queue. Both need the node running, and `reject` needs the group
`control.cancel`.

To end moderation:

```
fn operator /etc/fn/fn.toml group moderate fn.announce --off
```

## 4. People and logins

### Passwords

Add a login, or change its password. It is asked twice:

```
fn operator CONFIG principal set-password alice --posting
```

`--no-posting` makes a login that can read but not post. Restart the node
after you add a login or change a password this way.

### Accounts and invitation codes

A friend can make their own account from a code you give them:

```
fn operator CONFIG account invite --expires 86400
fn operator CONFIG account list
```

1. `account invite` prints a code once. fn does not keep the code itself, so
   if it is lost, make a new one. Without `--expires`, a code lasts a week.
2. Send the code over a channel you trust.
3. Your friend runs `fn redeem`, from any machine with fn unpacked. It
   asks for the new password:

   ```sh
   fn redeem news.example.org CODE carol --cafile cert.pem
   ```

   `--cafile` names your node's certificate file, when it is your own
   (self-made) one. A node on another port than 119 is named with it
   (`news.example.org:11563`). Add `--tls` and the port (`news.example.org:563`) for a
   node that speaks TLS from the start. `redeemed: the account carol is
   ready` means it worked. A newsreader cannot do this step; a program can
   send `XREDEEM CODE LOGIN`, then `XREDEEM PASS PASSWORD`, over TLS.
4. From then on they log in normally. No restart is needed.

`account list` shows accounts and unused codes, never passwords or codes.

To end an account, for example a test login:

```
fn operator CONFIG account delete probe
```

- From then on nobody can log in as `probe` (the password is refused). A
  session that is already logged in keeps going until it disconnects.
- Nothing is withdrawn: the posts `probe` made stay.
- The name `probe` is never given out again, so a later friend cannot post
  under the same `posting-account` value. `account list` shows it as
  `deleted probe`.
- It is refused while something still depends on the login: a signing
  binding (`principal unbind LOGIN`), a moderator role (`group moderate`
  without it) or a consumer bound to it (`consumer unbind NAME`). Remove
  those first. Its group access rule does not block it.
- It works on a running node, and on a stopped one.
- It removes accounts made with invitation codes. A login in `auth.toml`
  is removed by editing that file.

### Private groups

By default every login sees every group. To limit a login, give it a rule:
which groups it may read, and which it may post to. `!` excludes:

```
fn operator CONFIG account access bob --read 'fn.*,!fn.private.*' --post 'fn.*,!fn.private.*'
fn operator CONFIG account access alice --read '*' --post '*'
fn operator CONFIG account access --anonymous --read 'fn.public.*' --post '*,!*'
fn operator CONFIG account access show
```

A group outside a login's rule does not exist for that login. `--anonymous`
sets the rule for people who have not logged in (`*,!*` means none).

Three limits:

- The rule is for readers on your node. Peers get whatever your peer
  settings send them. Keep private groups out of every peer's list.
- You, the operator, can read everything. Nothing is encrypted in the store.
- Message-IDs are shared by the whole node. A post reusing a hidden
  article's Message-ID is refused as a duplicate.

### What a post shows about its author

Every post by a login carries a line like this:

```
Injection-Info: news.example.org; posting-account="8c59...f172"; mail-complaints-to="abuse@example.org"
```

The `posting-account` value is the same for every post by one login. So
anyone can tell that two posts came from the same login. Nobody can work
out the login name from it without your node's secret key. Tell the
people you give logins to.

Set the address for complaints, and find the value for one login:

```
fn operator /etc/fn/fn.toml policy set complaints-to abuse@example.org
fn operator /etc/fn/fn.toml account hash alice
```

### Signed posts: tie a login to its key

A signed article is checked against the key that signed it, whatever login
posted it. To make a login post only articles signed with its own key:

```
fn operator /etc/fn/fn.toml principal bind alice PRINCIPAL-HEX  # 64 lowercase hex digits
fn operator /etc/fn/fn.toml policy set posting-policy bound-logins
```

`principal unbind alice` removes the tie. `policy set posting-policy open`
turns the rule off. The last word of `principal set-password`, `bind` and
`unbind` says when the change applies: `applied` (now: the running node
reloaded its logins), `effective-at-next-start` (the node was not running),
`restart-required` (the node runs but `fn.toml` names no `[control] path`
to reach it), or `uncertain`.

## 5. Agents' consumers

A program on the node's own machine can read through a **consumer**. An
unbound consumer reads every group, as you can. Tie each agent's consumer
to the agent's account, so it reads only what that login may read:

```
fn operator CONFIG consumer bind agent-bob --account bob
fn operator CONFIG consumer unbind agent-bob
fn operator CONFIG consumer show
```

Bind a consumer after `fn consumer register` made it: a name no consumer
has is refused (`unknown-consumer`). A bound consumer uses its account's
password. Outside the account's rule it is refused and keeps its place. See [agents](agents.md#programs-on-the-nodes-own-machine).

## 6. Certificates

When you renew the TLS certificate, tell the running node to use the new
files. No restart is needed:

```
fn operator /etc/fn/fn.toml tls reload
```

New connections get the new certificate. Open ones keep the old one until
they end. fn refuses (and keeps the old one) if the new files do not
match, the dates are wrong, or a name the old certificate had is missing.
A certificate for different names needs a restart instead. `status` shows
the certificate in use:

```
tls names=fn.fg-goose.online not-after=2026-12-25T22:23:43Z
```

## 7. Opening your node to the internet

Before you open the port:

1. Require logins, and only over TLS (`mission small-community` does this).
2. Choose the certificate: your own (people must be given it) or one from a
   public authority.
3. Do not put fn behind a TCP proxy unless the proxy limits each address
   itself. Behind a proxy, fn sees every visitor as the proxy.

A node listening outside your own machine gets safe limits by default. You
can change each limit while it runs:

```
fn operator /etc/fn/fn.toml policy set exposure-connections 200
fn operator /etc/fn/fn.toml policy set exposure-per-address 8
fn operator /etc/fn/fn.toml policy set exposure-steps-per-second 64
fn operator /etc/fn/fn.toml policy set exposure-first-seconds 60
fn operator /etc/fn/fn.toml policy set exposure-idle-seconds 600
fn operator /etc/fn/fn.toml policy set exposure-auth-failures 10
fn operator /etc/fn/fn.toml policy set exposure-posts-per-minute 60
fn operator /etc/fn/fn.toml policy set anonymous none
fn operator /etc/fn/fn.toml policy set exposure-trusted 192.168.1.0/24
```

In order, these set:

- how many connections at once (31 if unset; each costs memory);
- how many from one address;
- how fast one address may work (over it, fn slows it down; nothing is
  lost). At the default, 64, one address can send about 32 KB a second, so
  a 1 MB post takes about half a minute. `0` turns the limit off;
- how long a new connection may stay silent, then how long an idle one may;
- how many failed logins per address per minute;
- how many posts per minute;
- whether people who have not logged in may read (`none`: they may not;
  `open`: they may read, and post too if posting is on);
- address ranges exempt from the per-address limit. Name your home network
  here if your router makes every local reader look like one address.

## 8. Peers

[Peering with a friend](peering-with-a-friend.md) walks through connecting
two nodes. To see your peers:

```
fn operator CONFIG peer list
```

Send a peer only articles for the listed distributions (`*,!local` means
all but `local`):

```
fn operator /etc/fn/fn.toml peer distributions far fn,local
```

If a peer's log line says `reason=mode-stream-refused`, that peer's server
cannot stream. Stop the node, run `peer remove NAME`, add the peer again
with `false` as the streaming word, and start the node.

Every node needs its own name, set once. Without it, fn cannot spot
articles that loop back to it:

```
fn operator CONFIG policy set path-identity news.example.org
```

## 9. Backups and new releases

### Back up

1. Stop the node.
2. Copy the whole node folder: the store (with its `keys` folder), `fn.toml`
   and `tls/`.
3. Start the node.

Copying while the node runs may miss the newest article. Keep the `keys`
folder private: it holds the node's secret.

An **export** (`store export`) is different. It carries the store's history
for moving to a new store, not the node's secrets or settings. Keep backups
and exports both.

### New releases

A new release is a fresh install. There is no upgrade in place and no going
back to an older release over a newer store.

1. Stop the node.
2. Install the new release. The program folder is replaced whole.
3. Start the node. The store folder stays as it is.

A release opens only a store of its own format; there are no migrations.
If the new release refuses the store, the line says so:
`open refused reason=store-format: not an fn store of this release:
redeploy fresh`. Set the node up again with `init`; the old store's data
does not carry over. `store export` and `store import` move a store between
installs of the same format (see [moving data](install.md#4-reinstalling)).

### The node's secret key

`STORE/keys/node-secret.key` protects cancels by your users and the
`posting-account` values. `init` makes it. The node will not start while it
is missing or readable by others. A store imported without its keys needs a
new one:

```text
fn store STORE node-secret create [IDENTITY]   # once; init does it
fn store STORE node-secret rotate [IDENTITY]   # a new epoch; the old one is kept
```

`create` never replaces an existing secret. `rotate` keeps the old one, so
old posts can still be cancelled.

## 10. When something goes wrong

### "uncertain"

`uncertain` (exit code 3) means fn asked the disk to save something and got
no clear answer. It may be saved; it may not. fn will not guess.

1. **Do not retry blindly.** Retrying a post with the same Message-ID is
   safe. Posting it again under a new one may make a copy.
2. **Stop the node and run `recover`:**

   ```
   fn operator CONFIG recover
   ```

   It shows what the store really holds. An article that is there can be
   read. One that is not can be posted again.
3. **Check the hardware.** Repeated `uncertain` means the disk is failing.
4. **Keep the three answers apart** in any script: 0 accepted, 1 refused,
   3 uncertain.

### After a crash

No action is needed. fn checks and reopens its store at the next start.
Run `recover` first if you want the report before starting.

If a command says `stale control socket removed`, that is fn cleaning up
after a crash. It is fine.

If `recover` refuses with `pre-C1 control record ... run store repair-control`,
the store was made by a release before 2026-09-25 and holds a cancel filed
in an old way. Keep the store as it is and ask the developers.

### A damaged record log

A crash can only leave the last write unfinished. fn drops that write at the
next start and says so: `log torn-tail at=000001.log:OFFSET`.

If saved data is damaged and saved data follows it (a failing disk, a bad
copy), fn does not guess. `status`, `recover` and `run` all refuse:

```
refused ... reason=log-damaged at=000001.log:4096 first-valid=8192 valid-after=11 records=11 ...
```

Nothing is written, and the node does not start. First copy the whole store
somewhere safe, and check the disk. If you have a good copy of the store
(a backup, or a peer that holds the articles), use it. Otherwise you can keep
everything before the damage and drop the rest, by naming the place exactly
as the refusal names it:

```
fn operator CONFIG recover --repair truncate 000001.log:4096
```

fn keeps the damaged file as `quarantine/000001.log.damaged-at-4096` first,
then answers `log repaired at=... dropped-valid-entries=N dropped-records=M`.
The dropped articles are gone from this store; a peer may offer them again.

### The node does not start

fn never stops without saying why. The reason is one line starting
`refused`, `fault` or `uncertain`, and the exit code matches it (see
[exit codes](#exit-codes)). Under systemd it is in the journal:

```sh
journalctl -u fn -n 20
```

Without a service it is on the screen, or in `log/fn.log` when `fn.toml`
names a `[log] path`. A program that starts fn and keeps its error output
in a file must show that file: the reason is there.

`health` and `status` say so too. When nothing runs where the node should
(its control socket does not answer and nothing holds the store), `health`
answers exit 18 and `status` begins the same way:

```text
health exit=18 state=not-running (no process holds the store and nothing answers on its control socket: the node is not running)
last-stop exit=04 reason=owner core/store fault; process stopped: ...
```

The second line comes from the `[log] path` file: `run` writes `run
started` when it starts and `run stopped exit=NN reason=...` when it
stops. `last-stop none` means the last run was killed (or the machine
stopped) before it could write its stop line; `last-stop unrecorded` means
the log has no run line (the node has not run since it was set up, there
is no `[log] path`, or it last ran an older release). Under systemd, after
five failed starts in a minute the service stays down (`Start request
repeated too quickly`); once the cause is fixed, `systemctl restart fn`
starts it again.

The memory refusals, and what to do:

- `fn: refused machine-cannot-hold-profile heap=H MB machine=M MB`: the
  store's limits need more memory than this machine (or the service's
  `MemoryMax`) gives. Raise the limit, or move the store to settings that
  fit (`store export`, then `store import` with smaller `--max-...`).
- `fn: refused machine-cannot-hold-threads reservation=R MB machine=M MB`:
  the same, for the whole node with its threads. Raise the limit.
- `refused connections-exceed-memory capacity=C holds=B ...`: the node
  can hold only B of its C connections. Lower the count
  (`fn operator CONFIG policy set exposure-connections N`), or give it
  more memory. When the line goes on `base-exceeds-machine`, not even the
  store fits: this happens when fn is started without `bin/fn` (which
  sizes the memory from the store) under a limit smaller than the image's
  own size. Start it through `bin/fn`, or raise the limit.

### "no store"

```
no store at the configured [store] path: this node was never initialized; run: fn operator CONFIG init GROUP... (a mission's fn.toml: init with no group)
refused operator status NO-STORE
```

Either the node was never set up, or `[store] path` in `fn.toml` names the
wrong folder (for example, the disk is not mounted).

### A post whose answer was lost

Someone's newsreader lost the answer to a post, and trying again was
refused. With the node stopped, look the post up by its Message-ID:

```text
fn operator /path/to/fn.toml store inspect '<fn-client.20260922T034404Z.3fd1ce9e@yue.invalid>'
accepted <fn-client.20260922T034404Z.3fd1ce9e@yue.invalid> an article is stored here under this Message-ID
fn operator /path/to/fn.toml store inspect '<never-posted@fn.example.invalid>'
absent <never-posted@fn.example.invalid> nothing is stored here under this Message-ID
```

`accepted` means it was saved (even if it was later withdrawn). `absent`
means it was not. Tell the person which answer you got.

### Why was an article withdrawn?

```
fn operator /etc/fn/fn.toml control log
fn operator /etc/fn/fn.toml control evidence <c1@example.invalid>
```

`control log` lists every withdrawal and who made it. `control evidence`
explains one article.

To take an article down yourself, whoever posted it:

```
fn operator /etc/fn/fn.toml article withdraw '<spam@example.net>' --reason takedown
```

Readers stop seeing it; nothing is deleted from the store. It needs the node
running and the group `control.cancel`.

A key change a friend posted may have been declined because you had not yet
given them the right. After you grant it, decide it again:

```
fn operator /etc/fn/fn.toml control grant PRINCIPAL-HEX keys fn.keys
fn operator /etc/fn/fn.toml keys redecide <a1@example.invalid>
```

### When the store is full

`init` sizes the store for the machine: the more memory, the more room.
On a small machine that is still about seven thousand short posts.
A store `init` made always starts again on the same machine, however
full it gets: `init` counts the memory of the store at its limits, not
of the empty store. `status`
has a line `capacity articles-left=N`: about how many more posts fit.
`health` shows `space-pressure` when it gets low.

When the store is full, posts are refused with
`441 posting failed; the store is full: no capacity for this article (unaffordable); the node's operator can raise it`.
Nothing is lost. A friend's node that feeds you is told "try later"
(`436`). It keeps the articles and tries again, and its `health` shows
`unavailable-peer`.

Each group a post goes to costs room too: about 320 bytes of the
store's history per group, as well as the post itself. Posting to many
groups at once is allowed, but paid for. When the post would fit but its
groups would not, it is refused with
`441 posting failed; the store cannot pay for this article's groups: each group it is posted to is charged to the history budget, and the article alone would fit; post it to fewer groups (memberships)`.
A feeding node is told "try later" (`436`) for this too.

The store's size limits are fixed when it is made. To raise them, move to a
new store with bigger limits: `store export`, a fresh install, then
`store import DIR --max-transactions N --max-history-octets N` (see
[reinstalling](install.md#4-reinstalling) and
[store settings](#store-settings)).

The store is a log that grows with each post. Now and then the running
node saves a summary (a checkpoint) and deletes the parts of the log it
covers, so a restart reads less. You can do the same by hand, with the node
stopped. It changes no article, and the next start opens from the
checkpoint (`OWNER-OPEN open=checkpoint:N`). It needs about 4 MiB free:

```text
fn operator /path/to/fn.toml store compact
```

It answers `compacted steps=checkpoint,drop records=N`. On a store of
40,000 short articles it took under three minutes.

## 11. How much one node can handle

Measured in September 2026, on a shared server with a busy, nearly full ZFS
pool:

- A post is confirmed in about half a second (0.6 s; 0.8 s if signed).
- About two posts a second, sustained.
- Reading one article takes about half a millisecond (measured 27
  September).
- A store of 40,000 short articles (2 KiB each) opens in about 14 seconds and then uses
  about 1.3 GB of memory. The old advice to stay under 30,000 articles is
  gone: that limit was the old store format's.

Most of the post time is the disk saving the article. fn never says yes
before the article is saved. The full figures are in
[the engineers' reference](operator-internals.md#what-one-node-sustains-the-measured-envelope).

## Reference

### Exit codes

| code | word | meaning |
| --- | --- | --- |
| 0 | `accepted` | Done (or already done). |
| 1 | `refused` | Not done, for the reason named. Nothing changed. |
| 3 | `uncertain` | Not known whether it was saved. See [above](#uncertain). |
| 4 | `fault` | fn could not carry out the command. |
| 5 | `usage` | The command or the settings file is wrong. |
| 6 | `interrupted` | (BP) A connection broke. The job is kept and retried. |
| 7 | `not-connected` | (BP) No connection was made. The job stays queued. |
| 19-27 | | `health` only: see [the table](install.md#when-the-node-refuses-something). |

### Settings file (`fn.toml`)

`[store] path`; `[listener] host`, `port`, `tls_cert`, `tls_key`,
`tls_port`; `[auth] required`, `protected_only`; `[posting] enabled`;
`[control] path`; `[log] path` (absolute); `[alerts] headroom_min_percent`
(default 10). `[listener] host` takes one or more addresses, comma
separated, IPv4 or IPv6 (`[::1], 192.0.2.7`), or `localhost`; `0.0.0.0` and
`::` are refused. Groups, peers and policies are not in this file: they are
kept in the store and changed with commands. `run` refuses `[posting] agent`,
`[anchor]` and `[acl2]` (set the node's name with `policy set path-identity`).
Restart after editing the file.

### Store settings

A store's size limits are set by `init` and never change. Under a `mission`,
`init` takes group names only and picks the limits for the machine. To
choose them yourself, or to raise them later through an export:

```text
fn operator /path/to/fn.toml init --max-transactions 100000 --max-history-octets 268435456 --max-article-octets 20000 fn.letters
fn operator /path/to/fn.toml store export /srv/fn-archive
fn operator /path/to/fn.toml store import /srv/fn-archive --max-transactions 1000000
```

Limits: `--max-transactions`, `--max-history-octets`,
`--max-record-octets`, `--max-article-octets`, `--max-groups-per-article`,
`--max-open-suffix`, `--max-consumers`, `--max-config-generations`,
`--max-credentials`. `--profile scale|development|default` names a starting
set. When this machine's memory cannot hold the limits you name, `init`
refuses and makes nothing:
`fn: refused init-budget-cannot-hold-profile profile=scale sizing=requested reservation=10866 MB budget=2048 MB`
(exit code 1). The first number is what the store would need at its
limits, the second what this machine can give. Choose smaller limits, or,
to make a store for a bigger machine, name that machine's memory with
`FN_INIT_BUDGET_MB=16384`: `init` then writes it and says
`within-budget=no target-budget=16384 MB`, and fn refuses to run that
store here, with `fn: refused machine-cannot-hold-profile`.

The same variable sizes a store for a memory limit smaller than this
machine: a service under `MemoryMax=1536M` needs a store `init` made with
`FN_INIT_BUDGET_MB=1536`, or made by an `init` run under that limit. When
the named budget is below what this machine gives (an `init` run outside
the service's limit), `init` writes the store for the named budget and
warns on stderr with both numbers, exit code 0:
`fn: warning init-budget-below-machine named-budget=1536 MB machine-budget=5818 MB: the store is sized for FN_INIT_BUDGET_MB, not this machine; run init under the service's memory limit, and give the service at least 1536 MB`.

`init` with no `--profile` and no limit (and every `init` under a
`mission`) picks the largest of four sizes this machine's memory holds:
64, 32 or 16 MiB of articles, else 8 MiB. A short post to one group
takes about 1,180 bytes (860 for the post, 320 for its group), so that is
about 56,000 posts at the top and about 7,000 at the bottom. `status`
shows the limits on its `profile` line and about how many posts still fit
on its `capacity articles-left=N` line. A friend's feed uses the same room. For more, remove the `mission`
line from `fn.toml` and `init` with the limits above, or raise them later
with `store export` and `store import --max-... N`.

### Other commands

- `fn operator CONFIG help VERB`: explains any command.
- `peer pull NAME SECONDS [ROUNDS]`: fetch from a peer every SECONDS
  (0 stops).
- `peer feed NAME pause` and `peer feed NAME resume`: stop and restart
  sending to one peer without removing it. Its pull and what it sends you
  are unchanged; articles queue for it meanwhile (spec peering 3.2.2).
  Every dropped outbound link names its reason in the service log,
  `feed peer=NAME link=dropped reason=lost-eof retry-ms=4000`; the retry
  delay doubles after each consecutive failure, up to five minutes.
- `peer catch-up NAME SECONDS`: every SECONDS (0 stops), copy the peer's articles
  in batches (XFNCATCHUP), each batch checked against the peer's digest before
  any article is offered to this node's own verdict; the round resumes after a
  restart ([catching up](peering-with-a-friend.md#catching-up); spec peering 1.2.9).
- `capacity N`: the room reserved for held articles.
- `pins`, `obligations`: what the store is holding, and why.
- `run`: what the service runs.
