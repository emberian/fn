# Running fn

This is the operator's page: install fn on a box, initialize a store, run it
as a service, post and read, back it up, and recover after a crash. It
describes what `bin/fn` does today. It is not a deployment authorization and
makes no availability or flight-readiness claim; see
[architecture](architecture.md) for the boundaries and
[failures](../specs/failures.md) for what durability here assumes.

Everything below is one command, `fn`, and one configuration file.

Status (2026-09-21): `bin/fn` and the workflow below describe the explicit
**Python development service**. The production package uses the native saved
image and the separate installation procedure below.
The owner now certifies and runs; the earlier owner-load failure is historical.
The [frozen two-node exercise](../planning/evidence/v0-integrated-runtime-w12-2026-09-21.md)
records authentication and BP crash disagreements, not a passing release gate.

D07 requires the eventual deployed node and CLI to run without Python. That
native service migration is active, and the Python service described below does
not meet its production gate. `packaging/fn-native` directly launches the
production saved Lisp image. That image exposes the ACL2-planned operator and
the existing public BP operations, but it is not yet a drop-in replacement for
this operator CLI. See the
[native migration plan](../planning/lanes/native-cli-migration.md) for the command
parity work and [host contract](../specs/host.md#selected-production-runtime) for
the runtime boundary.

## Native component entry

The native image now has an ACL2-owned operator entry. For a compatible existing
store and a supported minimal configuration, its component commands are:

```sh
packaging/fn-native operator /path/to/fn.toml help
packaging/fn-native operator /path/to/fn.toml init fn.letters fn.test
packaging/fn-native operator /path/to/fn.toml status
packaging/fn-native operator /path/to/fn.toml recover
packaging/fn-native operator /path/to/fn.toml group create fn.announce
packaging/fn-native operator /path/to/fn.toml group retire fn.announce
packaging/fn-native operator /path/to/fn.toml capacity 1048576
packaging/fn-native operator /path/to/fn.toml peer add NAME PATH HOST PORT INBOUND|- OUTBOUND|- SOURCE true|false
packaging/fn-native operator /path/to/fn.toml peer remove NAME
packaging/fn-native operator /path/to/fn.toml peer list
packaging/fn-native operator /path/to/fn.toml policy set path-identity news.example.invalid
packaging/fn-native operator /path/to/fn.toml run
```

`init` creates the store `[store] path` names and admits the groups the
operator named, so a node is stood up with the same binary that runs it; the
image's low-level `--fn store ROOT init` entry stays a diagnostic. There is no
default group table: `init` with no group is a usage error (5) rather than a
store whose served groups nobody chose. The names it admits are the store's
own -- `fn-record-group-namep`, bounded at 128 octets, the same predicate
`group create` applies and the same duplicate rule `fn-record-groupsp`
imposes -- so this verb does not own a second idea of what a group may be
called. An `init` over a store that already
exists is refused (1), and it is refused on the presence of the store's own
entries -- `config.json`, `writer.lock`, `allocation-frontier.json`,
`transactions/`, `config/` -- so a store a live owner holds is never opened or
locked to find that out. An existing store is adopted by `run` and repaired by
`recover`; `init` does not reinitialise one.

`peer list` prints the peer records the durable configuration holds, one line
per peer, in the order `peer add` takes its arguments:

```
far path-identity=far.example address=192.0.2.44 port=1119 security=starttls inbound=fn.* outbound=fn.* auth=source-address:192.0.2.44
```

A half the record does not carry is `-`. The line is rendered by ACL2
(`fn-native-admin-peer-report`, books/native-admin.lisp) from the replayed
configuration's own peer rows. `peer list` is a read: it opens the store
without the exclusive writer lock and never reaches the live owner, so while
an owner is running it refuses (1) exactly as `status` does, and it can neither
publish a configuration record nor take the lock away from the owner.

`policy set path-identity` gives the node its own RFC 5537 section 3.2
`<path-identity>`. Until it is set, the owner cannot recognise its own name in
a `Path` header and section 3.5 loop suppression cannot fire, which the native
v0 matrix measured on 2026-09-22 as `V0-TRANSIT-LOOP` accepting the looped
article. It is a durable configuration record like a group or a peer, refused
while the owner holds the writer lock offline and applied live through the
owner otherwise.

`help` does not read the configuration file. `run` uses the normalized native
owner callback. Missing, nonregular or oversized configuration is usage (5);
a hard read/open failure remains a fault (4). Refused work (1), uncertain
persistence (3) and successful execution (0) remain distinct. `group` and
`capacity` use the same durable configuration records as the development
operator and refuse while the owner holds its writer lock. A valid profile
with settings the running native owner cannot consume still permits these
offline actions, plus `status` and `recover`; only `run` refuses that profile.
An accepted command plan alone is never reported as a successful post.

The [operator integration record](../planning/evidence/native-operator-installed-20260921T0920.md)
contains source-pinned component execution, including an actual loopback reader.
The [explicit preflight record](../planning/evidence/native-operator-preflight-2026-09-21.md)
covers the configuration-free help boundary. The later combined native service
batch is still under validation. Native `post`, control, authentication and
outbound feed operation are active implementation work; unsupported profiles
produce an explicit usage error. The entry above does not yet replace the complete
operator workflow below, and the low-level `store` diagnostic is not a second
public posting interface. The production image does not register raw
`--fn owner run` and refuses raw `--fn reader`; `operator CONFIG run` is its one
owner-service start and therefore always passes through the ACL2 native
configuration plan and authentication startup. Native SIGTERM enters the owner
stop boundary, wakes and joins connection, control, and feed workers, closes
TLS and journals, and preserves the owner's exit outcome.

### Install the native production entry

Build or select the source-pinned production `fn-host` and adjacent
`fn-host.core`, then stage an installation without starting a service:

```sh
FN_NATIVE_HOST=/path/to/fn-host FN_NATIVE_CORE=/path/to/fn-host.core \
  FN_NATIVE_SOURCE_REVISION=<image-source-commit> \
  DESTDIR=/tmp/fn-package PREFIX=/usr/local packaging/install-native.sh
```

The layout is `bin/fn`, `libexec/fn/fn-host`,
`libexec/fn/fn-host.core`, and `libexec/fn/runtime/`. The installer copies the
SBCL executable and its `SBCL_HOME` support tree out of the generated launcher,
then rewrites the launcher to use those installed paths. A system service can
therefore use a prefix outside protected home directories. The command only clears ACL2 customization variables
and execs `fn-host --fn operator CONFIG ...`; it has no Python fallback.
Before copying, the installer executes the image's disabled reader entrypoint
and accepts only its production-profile refusal. This checks the selected image
profile; it does not establish feature parity. `share/fn/native-artifacts.txt`
records launcher, core, and runtime hashes, the copied SBCL home, linked runtime
libraries, and the `libsodium` plus OpenSSL 3 libraries loaded by native crypto
code. Those crypto libraries remain system package dependencies. Rendered service files live under `share/fn/systemd` and
`share/fn/launchd`. Installation does not enable, start, or restart them.
The package does not widen the selected image's command set. In particular,
the frozen `8c` qualification image refuses public `peer add` with usage 5
because it predates the live owner callback; native peering requires a newly
qualified image built from the later integration source.

Native owner and reader component tests use a distinct saved image. Building it
is an explicit evidence action and does not replace `build/fn-host`:

```sh
FN_NATIVE_PROFILE=developer tools/build_native_host.sh
# writes build/fn-host-developer
```

`FN_NATIVE_DEVELOPER_HOST` may point those tests at another developer-profile
image. Changing `FN_NATIVE_PROFILE` when an existing saved image starts has no
effect; the profile is selected during image construction and serialized.

## Install

The development service needs Python 3.11 or newer (for `tomllib`) and ACL2 8.7 with a certified
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

Native peer records use the same offline durable administration path:

```text
fn-native --fn operator /etc/fn/fn.toml peer add NAME PATH-ID HOST PORT INBOUND|- OUTBOUND|- AUTH-KIND AUTH-VALUE true|false
fn-native --fn operator /etc/fn/fn.toml peer remove NAME
```

`AUTH-KIND` is `source-address` or `principal`. A principal is the canonical
64-digit lowercase hexadecimal principal id. The older form with only a source
address in this position remains accepted as a compatibility decode.

To authenticate the outbound feed, insert `PROFILE ALLOW-CLEAR` between
`AUTH-VALUE` and the streaming flag. `PROFILE` is the permissioned
`FNAUTH1` credential file; `ALLOW-CLEAR` is `true` or `false`. Use `false`
for TLS peers. The profile must be a regular file owned by the service user
with no group or other permission bits.

ACL2 parses the port and streaming word, supplies the inbound body/inflight
limits and outbound queue/backoff limits, builds the typed peer record and
selects the configuration delta. Run these while the owner is stopped; the
exclusive store lock refuses offline administration against a live owner.

`[listener] host` accepts loopback aliases or an explicit numeric IPv4
address. ACL2 parses the literal and supplies the exact bind address; the host
does not resolve or reinterpret it. The wildcard `0.0.0.0` remains refused so
an operator must name the interface placed in service. General IPv6 literals
remain open; `::1` is the admitted IPv6 spelling.

## Run it as a service

`fn run` is the service. It is a foreground process that takes the store's
**exclusive** writer lock for its whole lifetime, serves NNTP readers on the
configured port, and accepts a local Unix control socket (`[control] path`,
by default `<store>/control.sock`) for posting and administration. Exactly
one `fn run` may hold a store.

The control socket is an operator endpoint created with mode 0600. Its holder
may administer the node; `[posting] enabled = false` disables article posting,
not operator configuration changes. Do not give an agent this socket merely
to grant posting access; use its separately configured NNTP posting principal.

- native systemd: install the rendered `share/fn/systemd/fn.service` as
  `/etc/systemd/system/fn.service`, then
  `systemctl daemon-reload && systemctl enable --now fn`.
- native launchd: install the rendered `share/fn/launchd/net.fn.plist` as
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

Two things the unit will bite you with, both learned by running it:

- **`--config` precedes the verb.** `fn run --config <path>` exits 2 with
  `unrecognized arguments`, and under `Restart=on-failure` that is a loop. The
  shipped `ExecStart` is `fn --config <path> run`; keep that order if you edit
  it. The unit carries `StartLimitIntervalSec=60` and `StartLimitBurst=5` so a
  service that cannot start gives up instead of spinning.
- **The start limit latches.** Once a unit has hit it, every later `restart`
  is refused with `Start request repeated too quickly` **and exits 0**, which
  looks exactly like a successful start. Run `systemctl reset-failed fn`
  before you start it again.

### Without root: a user service under `~/fn-live`

Neither farm box gives us `/usr/local/lib`, `/etc/fn` or an `fn` user, so the
same unit is installed per-user with its four paths moved under `$HOME` and
the `User=`, `Group=` and `Protect*`/`Private*` directives a user manager
cannot apply removed. [`tools/live_service.py`](../tools/live_service.py)
does that and records every command it ran:

```sh
python3 tools/live_service.py install <commit> \
    --host persvati --node fnA --port 11190 \
    --host hbox     --node fnB --port 11190
python3 tools/live_service.py status --host persvati
python3 tools/live_service.py stop   --host hbox
```

It ships the commit to `~/fn-live/fn`, installs certificates from that box's
own cache (it never certifies — a book with no cached pair would be certified
*inside* the service), runs `fn init` with the groups, writes a peer record
naming the other box at `~/fn-live/peers/<name>.peer`, installs and enables
the unit, starts it and greets it over a socket. Where a box has no user
systemd it writes `~/fn-live/run.sh`, a `setsid` wrapper — that is **not** a
supervised service: nothing restarts it, nothing bounds its stop, and a
reboot loses it.

`loginctl enable-linger <user>` is what keeps a user service alive after the
last session closes; it needs an administrator, and without it the service
stops when you log out.

### Reaching it from a laptop

For a local-only listener, the way in is a tunnel:

```sh
ssh -N -L 11190:127.0.0.1:11190 persvati &
python3.12 - <<'PY'
import nntplib
n = nntplib.NNTP("127.0.0.1", 11190, timeout=30)
print(n.getwelcome())
print(n.getcapabilities())
print(n.group("fn.letters"))
n.quit()
PY
```

`nntplib` left the standard library in Python 3.13 (PEP 594), so the client
side wants a 3.12 or older interpreter; the farm boxes have 3.13 and 3.12
respectively, which is why the deploy gate records `nntplib interpreter NONE`
on persvati and drives the socket by hand instead.

For a node that listens off loopback with `[auth] required`,
`protected_only` and a TLS pair, `tools/node_probe.py` is the client to run
from the other machine. It drives the socket by hand on any Python 3, records
every status line, and asserts the policy such a node must carry: `STARTTLS`
offered before the layer, `AUTHINFO` answered `483` before it, `382` and a
handshake verified against the node's own certificate, `281` after it, then
`GROUP`, `POST`, and the article read back on a fresh connection. The
password comes from the environment only and is never written anywhere.

```sh
scp hbox:/tank/fn/node/tls/cert.pem /tmp/hbox-cert.pem
FN_PROBE_USER=ember FN_PROBE_PASSWORD="$(ssh hbox "awk '/^ember /{print \$2}' /tank/fn/node/credentials.txt")" \
  python3 tools/node_probe.py 192.168.50.39 1119 --cafile /tmp/hbox-cert.pem --group fn.agents --json probe.json
```

Its exit is the deploy gate's scale: 0 when every assertion was decided and
held, 1 when one was violated, 3 when something it meant to decide it could
not (an unreachable node exits 3, never 0), 2 for a usage error.

`tools/node_probe.py` asserts the policy; to *use* such a node -- list the
groups, read what is new since last time, post a reply -- the client is
`tools/fn_client.py`, described in [agents on an fn node](agents.md).

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
journal) carries one line per post and one per accepted connection, with the
outcome word first. A connection line says the **role** the owner gave the
connection at accept, which it decides from the peer table and not from
anything the client says: `reader`, or `peer` with the record's name.

```
accepted post path=control message-id=<a@example.invalid> agent=news@example.invalid detail=committed sequence=3 charge=41 time=2026-09-19T21:04:11Z
accepted reader connection=2 time=2026-09-19T21:04:33Z
accepted peer connection=3 peer=innA time=2026-09-19T21:04:35Z
refused post path=control message-id=<b@example.invalid> agent=news@example.invalid detail=refused: group-unknown time=2026-09-19T21:05:02Z
```

If a connection you expected to be a reader is logged as a `peer`, the
source address matched a peer record's `auth` slot: the owner matches the
address and nothing else, so a peer configured on loopback claims every
loopback client. That is what to check first when a reader behaves oddly on
a box that is also peering with itself.

## Require a login (RFC 4643)

Off by default. To turn it on, write the policy into the configuration and
enrol at least one login:

```
fn --config /etc/fn/fn.toml init --store /var/lib/fn/store --auth-required
fn --config /etc/fn/fn.toml principal set-password alice --posting
fn --config /etc/fn/fn.toml principal list
```

`set-password` prompts twice, derives the salted verifier in an ACL2 session
over `books/auth-secret.lisp`, and writes `<store>/auth.toml` at mode 0600.
The secret is not in that file and cannot be recovered from it. `principal
list` reads the same file, which is the one the running service loads, and
prints the login, its principal id and its posting flag; it never prints the
verifier.

What the policy does, and every decision below is ACL2's
(`books/nntp-auth.lisp`), not the host's:

- `AUTHINFO USER` is advertised in `CAPABILITIES` while the connection is
  unauthenticated and a credential is configured, and withdrawn once it has
  been used (RFC 4643 §2.1).
- `[auth] required = true` answers `480` to a command that changes durable
  state or discloses article content until the connection authenticates.
- Posting is the **authenticated principal's**: enrol with `--no-posting`
  and that login passes the gate and still gets `440` for POST, and the
  `POST` capability label is not offered to it.
- `[auth] protected_only = true` answers `483` to AUTHINFO until TLS is
  active. Set `[listener] tls_cert`/`tls_key` — `fn init --tls-cert --tls-key`
  writes them — and the node advertises `STARTTLS` (RFC 4642 §2.1) and drops
  the label once the layer is up. USER/PASS crosses in the clear otherwise.

The policy reaches every connection the owner opens, including one it
resolved to a peer record. A peer does not run AUTHINFO, so on a node with
`required = true` a transit peer is answered `480` for `IHAVE` as well; do
not set it on a node that is also taking a feed until that is decided
(`planning/deputies/BOARD.md`, w11/auth-live).

Restart the service after changing either the policy or the credential
file: both are read once at start-up.

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
