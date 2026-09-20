# Running fn

This is the operator's page: install fn on a box, initialize a store, run it
as a service, post and read, back it up, and recover after a crash. It
describes what `bin/fn` does today. It is not a deployment authorization and
makes no availability or flight-readiness claim; see
[architecture](architecture.md) for the boundaries and
[failures](../specs/failures.md) for what durability here assumes.

Everything below is one command, `fn`, and one configuration file.

Status at the time of writing: every store-side subcommand runs against
a real ACL2 core. `fn run` is complete and tested, but it cannot start on
this revision, because `books/owner.lisp` does not currently include: the
served connection grew two fields and the owner cluster has not caught up.
Until that repair lands, `fn post`, `fn group`, `fn status`, `fn recover`
and `fn anchor` work against a stopped store and the service section below
describes what the unit files and the CLI already do, not a node you can
leave running. See `planning/lanes/HANDOFF-w5-fn-cli.md`.

## Install

fn needs Python 3.11 or newer (for `tomllib`) and ACL2 8.7 with a certified
copy of this repository's books. The ACL2 core is not optional: every
acceptance, refusal and recovery decision below is a call into it.

1. Put the repository somewhere stable, for example `/usr/local/lib/fn`. The
   service runs from the repository root: `bin/fn` finds `tools/`, `books/`
   and `host/` relative to itself.
2. Install ACL2 8.7 and note its executable path. `fn` passes it to every
   tool as `FN_ACL2`.
3. Certify the books once on the box: `make certify`. Certification is
   memory-bound; `[acl2] slots` caps how many ACL2 processes the machine
   runs at once (`tools/acl2_slots.py`).
4. Create an unprivileged account that owns the store, for example `fn` on
   Linux or `_fn` on macOS.

## Initialize

```
fn --config /etc/fn/fn.toml init \
        --store /var/lib/fn/store \
        --group fn.letters --group fn.test \
        --listen 127.0.0.1:1119 \
        --agent "news@example.invalid" \
        --anchor-server int08h \
        --acl2 /usr/local/bin/acl2 \
        --log /var/log/fn/fn.log
```

This creates the store and writes the configuration file.
[`packaging/fn.toml.example`](../packaging/fn.toml.example) documents every
table: `[store] path`, `[listener] host port`, `[posting] enabled agent`,
`[anchor] server`, `[acl2] path slots`, `[log] path`, `[control] path`.

The groups are **not** in the configuration file. They are durable
configuration records inside the store, which ACL2 replays at every open;
`--group` seeds them once, and `fn group` changes them afterwards. The
configuration file holds only what the host needs in order to start.

`[listener] host` must be loopback. `fn run` refuses any other host rather
than binding loopback behind your back: this scaffold does not authorize a
public listener, and reaching fn from another machine is a job for an SSH
tunnel or a reverse proxy you configure yourself.

## Run it as a service

`fn run` is the service. It is a foreground process that takes the store's
**exclusive** writer lock for its whole lifetime, serves NNTP readers on the
configured port, and accepts a local Unix control socket (`[control] path`,
by default `<store>/control.sock`) for posting and administration. Exactly
one `fn run` may hold a store.

- systemd: install [`packaging/fn.service`](../packaging/fn.service) as
  `/etc/systemd/system/fn.service`, then
  `systemctl daemon-reload && systemctl enable --now fn`.
- launchd: install [`packaging/net.fn.plist`](../packaging/net.fn.plist) as
  `/Library/LaunchDaemons/net.fn.plist`, then
  `sudo launchctl bootstrap system /Library/LaunchDaemons/net.fn.plist`.

Both send `SIGTERM` to stop. That is the clean shutdown: the owner finishes
its teardown, removes the control socket and releases the writer lock, and
exits 0. Both are configured to restart only on a non-zero exit, so a
deliberate stop stays stopped.

`ProtectSystem=strict` in the unit makes the whole filesystem read-only
except the paths named in `ReadWritePaths`. If you move `[store] path` or
`[log] path`, add the new location there or the service cannot write.
`MemoryDenyWriteExecute` is deliberately absent: the Lisp runtime under ACL2
maps writable-executable pages and will not start with it set.

## Post and read

Read with any NNTP client against the configured port:

```
telnet 127.0.0.1 1119
GROUP fn.letters
ARTICLE 1
```

Post through fn, which routes to the running owner's control socket when one
is live and opens the store directly when one is not:

```
fn --config /etc/fn/fn.toml post \
   --message-id '<2026-09-19.1@example.invalid>' \
   --payload /tmp/article.txt --group fn.letters
```

Every invocation writes exactly one line on stderr whose first word is the
outcome, and exits with the code for that outcome:

| Outcome | Exit | What it means |
| --- | --- | --- |
| `accepted` | 0 | The core accepted it and the decision is durable. |
| `refused` | 1 | The core refused it. Nothing changed. Fix the input. |
| `uncertain` | 3 | Whether it is durable is not known. See below. |
| `fault` | 4 | The host could not carry out the operation. |
| `usage` | 5 | The command line or the configuration file is wrong. |

These three outcomes stay distinct everywhere: the exit code, the stderr
line, the log line, and the reply on the control socket. Never map
`uncertain` onto either of the others in a wrapper script.

The service log (`[log] path`, otherwise stderr, which under systemd is the
journal) carries one line per post and one per reader connection, with the
outcome word first:

```
accepted post path=control message-id=<a@example.invalid> agent=news@example.invalid detail=committed sequence=3 charge=41 time=2026-09-19T21:04:11Z
accepted reader connection=2 time=2026-09-19T21:04:33Z
refused post path=control message-id=<b@example.invalid> agent=news@example.invalid detail=refused: group-unknown time=2026-09-19T21:05:02Z
```

## Add a group

```
systemctl stop fn
fn --config /etc/fn/fn.toml group create fn.announce
systemctl start fn
```

The stop is required today. A group is a durable configuration record, and
writing one needs the exclusive writer lock the running owner holds, so
`fn group` refuses while the service is live and says so. `fn group retire
<name>` retires a name: the articles already bound to it and its watermark
are kept, and the name stops being served. Creating a retired name again
revives it with its numbering intact.

## Back up

Stop the service, then copy the store directory.

The store is an append-only journal of immutable transaction files plus a
small set of small metadata files (the configuration records, the allocation
frontier, the freshness anchor). A transaction file is written, made durable
and never modified afterwards, so a copy of a file is either the whole
record or absent -- there is no such thing as half-updated content inside
one. That is why a plain file copy is enough and no database-aware dump tool
is needed. Copying while the service runs can catch a transaction mid-write;
recovery on the copy will discard that partial record, which means the copy
silently loses the newest article rather than being corrupt. Stopping first
avoids the question.

What a copy does not give you is freshness. A restored image cannot tell by
itself that it is not an old snapshot, which is what `fn anchor` and the
freshness check inside `fn recover` are for. Record an anchor before the
backup and check it after the restore.

## Recover after a crash

A crash needs no special action: the next `fn run` replays the journal
through ACL2 and reopens. Run `fn recover` first when you want the report
before the service starts.

```
fn --config /etc/fn/fn.toml recover
```

It prints the recovered transaction and article counts, any staging orphans
an interrupted publication left behind (those are named, not hidden), and
the freshness verdict. Its exit code is the freshness verdict's: `accepted`
when the store is demonstrably not a stale image, `uncertain` when no anchor
server could be reached, `refused` when the anchor says the image is older
than the one its own records stand under. A refused recover is a signal to
stop and work out which image you are holding, not to retry.

`fn status` reports what the store is: the configuration generation, the
transaction and article counts, the last recorded anchor, and whether an
owner is live. While an owner holds the store no other process can take the
lock, so with the service running `fn status` reports what the control
channel answers (liveness, committed version, open connections) and names
the store-side fields `owner-held`.

## What "uncertain" means, and what to do

`uncertain` (exit 3) is not a soft failure. It means fn asked the operating
system to make something durable and did not get an answer it can act on:
the write may be on the disk or may not be. fn will not guess. It does not
roll the operation back and it does not continue as if it had committed.

When you see it:

1. **Do not retry blindly.** A retry of a post that may already be durable
   is a second attempt at the same Message-ID; fn will report it as a
   duplicate if the first one landed, which is safe, but the same is not
   true of scripts that treat exit 3 as exit 1 and take a different action.
2. **Stop the service and run `fn recover`.** Recovery replays the journal
   and tells you what is actually there. An article that reached durability
   is in the recovered counts and readable with an NNTP client; one that did
   not is absent, and you may post it again.
3. **Look at the hardware.** Repeated `uncertain` is a disk or filesystem
   reporting failures, not an fn condition. Read
   [failures](../specs/failures.md) for the assumptions the durability
   argument makes about the device.
4. **Keep the distinction in your automation.** Any wrapper, monitor or
   cron job around fn must keep 0, 1 and 3 apart. Collapsing them is how a
   node ends up reporting an article as accepted that it never stored.
