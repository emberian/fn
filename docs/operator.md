# Running fn

This is the operator's page: install fn on a box, initialize a store, run it
as a service, post and read, back it up, and recover after a crash. It
describes what `bin/fn` does today. It is not a deployment authorization and
makes no availability or flight-readiness claim; see
[architecture](architecture.md) for the boundaries and
[failures](../specs/failures.md) for what durability here assumes.

Everything below is one command, `fn`, and one configuration file.

**With only the release tarball** (`fn-REV-linux-x86_64.tar.gz`, made by
`packaging/release-tarball.sh`), start at
[From the release tarball](#from-the-release-tarball) and then
[peering with a friend](peering-with-a-friend.md). The sections
"Install", "Initialize" and "Require a login" further down describe the
Python development service (`bin/fn --config ...`), not the tarball's
`bin/fn`, whose verbs are `fn operator CONFIG VERB ...`.

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
packaging/fn-native operator /path/to/fn.toml init fn.letters fn.test
packaging/fn-native operator /path/to/fn.toml status
packaging/fn-native operator /path/to/fn.toml recover
packaging/fn-native operator /path/to/fn.toml group create fn.announce
packaging/fn-native operator /path/to/fn.toml group retire fn.announce
packaging/fn-native operator /path/to/fn.toml capacity 1048576
packaging/fn-native operator /path/to/fn.toml peer add NAME PATH HOST PORT INBOUND|- OUTBOUND|- SOURCE true|false
packaging/fn-native operator /path/to/fn.toml peer remove NAME
packaging/fn-native operator /path/to/fn.toml peer list
packaging/fn-native operator /path/to/fn.toml peer invite NAME GROUPS HOST PORT PATH /KEYDIR /OUT MY-HOST MY-PORT
packaging/fn-native operator /path/to/fn.toml peer accept /INVITATION /KEYDIR PATH REACHABLE /OUT
packaging/fn-native operator /path/to/fn.toml peer confirm /ACCEPTANCE /INVITATION
packaging/fn-native operator /path/to/fn.toml policy set path-identity news.example.invalid
packaging/fn-native operator /path/to/fn.toml run
```

The native author-key lifecycle is a separate local-control interface in
current development source. After starting the owner, an authorized local
operator can publish a hybrid public-key enrollment or rotation, then revoke
one principal's current local permission:

```sh
packaging/fn-native hybrid-enroll CONTROL 1 PRINCIPAL.bin ED-PUBLIC.bin ML-PUBLIC.pem
packaging/fn-native hybrid-enroll CONTROL 2 PRINCIPAL.bin NEW-ED-PUBLIC.bin NEW-ML-PUBLIC.pem
packaging/fn-native hybrid-revoke CONTROL 3 PRINCIPAL.bin
```

The generation must be the next global keyring-snapshot generation. A later
enrollment for another principal leaves the first principal active; rotation
or revocation affects only the named principal's new local `hybrid-author`
requests. Refusal exits 1; an uncertain publication is distinct and requires
reopen/inspection before retry. With the writer stopped, `hybrid-key-history
STORE` opens the replayed Store read-only and prints each generation's status
and principal, newest first. It does not print key payloads or read secrets.
The private signing keys remain with the author; none enters a Store snapshot.
Existing accepted verdicts stay pinned to their historical enrollment.
These commands have scoped ACL2 source evidence and a targeted native run on
the frozen `863c2141` image, recorded in the
[author-key lifecycle evidence](../planning/evidence/author-key-lifecycle-2026-09-24.md).
That run covers the selected CLI tests on scratch Stores; it is not a
deployed-node claim.

`init` creates the store `[store] path` names and admits the groups the
operator named, so a node is stood up with the same binary that runs it; the
image's low-level `--fn store ROOT init` entry stays a diagnostic. There is no
default group table: `init` with no group is a usage error (5) rather than a
store whose served groups nobody chose. The names it admits are the store's
own -- `fn-record-group-namep`: an RFC 5536 section 3.1.4 <newsgroup-name>
(components of letters, digits, `+`, `-` and `_` joined by single dots, so no
space and no leading, trailing or doubled dot) of at most 128 octets, the
bound being local policy, and the same predicate
`group create` applies and the same duplicate rule `fn-record-groupsp`
imposes -- so this verb does not own a second idea of what a group may be
called. An `init` over a store that already
exists is refused (1), and it is refused on the presence of the store's own
entries -- `config.json`, `writer.lock`, `allocation-frontier.json`,
`transactions/`, `config/` -- so a store a live owner holds is never opened or
locked to find that out. An existing store is adopted by `run` and repaired by
`recover`; `init` does not reinitialise one.

The converse is refused too, with its own code. Every verb that opens the
store (`run`, `post`, `status`, `pins`, `obligations`, `health`, `recover`,
`store ...`, `group`, `capacity`, `peer`, `policy`, `bp-boundary`,
`bp-route`, `retention`, `control`, `principal`) first looks for the same
five entries, by `lstat` alone. With none of them there is no store here: the
node was never initialized (or `[store] path` names the wrong directory), and
the answer is **`refused` with exit 6** and the line

```
no store at the configured [store] path: this node was never initialized; run: fn operator CONFIG init GROUP... (a mission's fn.toml: init with no group)
refused operator status NO-STORE
```

never a fault (4). ACL2 decides it (`fn-native-operator-store-outcome`,
`fn-native-operator-absent-store-is-refused`, books/native-operator.lisp);
a store with some of its entries (an interrupted `init`) is not "no store"
and goes to the open, which recovers or refuses it.

**Init under a mission.** A `fn.toml` written by `mission NAME` carries
`[ops] mission`, and the mission fixes the store profile: `init` then takes
GROUP words only, and with none a small community serves `local.general`
and `local.test` (relay and archive have no default groups and need them).
A profile flag or `--profile` there is a usage error (5) whose first line
says so:

```
under [ops] mission, init takes GROUP words only (none: the mission's default groups); the mission fixes the store profile. Raise a bound afterwards offline with: fn operator CONFIG store upgrade-profile --FIELD N (fields only rise; the presets are smaller than a mission's); or delete the mission line from fn.toml to choose a profile at init
usage operator init MISSION-FIXES-PROFILE
```

Every usage error prints ACL2's line for what the command accepts before its
result line, so `init` with a stray word shows the full `init` grammar.

**Store profile (M5, D27).** The store profile is the operator's: every
bound on the data a store holds is a field `init` writes into `config.json`
(format `fn-store-8`, `books/byte-store-frame.lisp`) and only the offline
upgrade raises. ACL2 fixes the relations between the fields
(`fn-bs-profile-validp`) and the codec ceilings no field may pass, not the
values.

| field (flag `--NAME N`) | bounds | default at `init` |
| --- | --- | --- |
| `max-transactions` (T) | committed transactions | 4,294,967,295 (the u32 txid width) |
| `max-history-octets` (H) | total committed record octets | 1 TiB |
| `max-record-octets` (R) | one encoded Store event | 196,608 (the FNST codec ceiling today) |
| `max-article-octets` (A) | one article's payload | 32,768 (the record codec's today) |
| `max-groups-per-article` (G) | newsgroups on one article | 16 (the record codec's today) |
| `max-group-name-octets` | one group name | 128 (the record codec's today) |
| `max-open-suffix` (K) | records replayed after the checkpoint | 65,536 (lowered with T) |
| `max-consumers`, `max-bp-rows`, `max-config-generations`, `max-credentials`, `max-policy-members` | namespace counts | 1,048,576 each |

The D27 defaults are 64 MiB records, 16 MiB articles, 4096 groups and
460-octet names; each default is capped at the codec ceiling the tree carries
today, and rises when that ceiling does (packet P2). The relations, each
reported by name when it fails (exit 1, nothing written): `1 <= T <= 2^32-1`;
`R <= H`; R at least the worst-case record of every Store event kind (today
exactly 196,608: the accepted-statement kind's ceiling equals the codec's);
R, A, G and the name bound within their codec ceilings; `1 <= K <= T`; each
namespace count in `1..2^32-1`.

```text
fn operator /path/to/fn.toml init --max-transactions 100000 --max-article-octets 20000 fn.letters
fn operator /path/to/fn.toml init --profile development fn.letters   # 128 transactions, 24 MiB
fn operator /path/to/fn.toml init --profile scale fn.letters         # 4096 transactions, 768 MiB
```

`--profile development|scale|default` names a base (the first two are the
pre-D27 presets, kept so existing stores and tests keep their witnesses);
flags override its fields. `status` prints the profile the store runs under
and the headroom against it:

```text
profile format=8 max-transactions=100000 max-history-octets=1099511627776 max-record-octets=196608 max-article-octets=20000 ...
headroom transactions-used=7 transactions-budget=100000 bytes-used=1834 history-bound=1099511627776 charge-reserved=... charge-capacity=...
```

Every committed transaction (an article, a retention, keyring, consumer or
topic event) takes one of T, and its record octets count against H. The owner
refuses the next POST once either is reached, and says so: `441 posting
failed; the store has no capacity for this article`, a refusal (never
uncertain, never a silent drop); an article already stored is still answered
as a duplicate. The decision is ACL2's (`fn-sbud-verdict-at`,
`books/store-budget.lisp`; `fn-sbud-prepare`, `books/owner-store-budget.lisp`),
from the profile the owner read at open, the count of the store it carries and
the record octets it carries (each record encoded once per owner process,
`fn-sbud-bytes-used-is-kernel-sum`). A POST whose payload is longer than A is
refused by name (`payload exceeds the modelled bound`). The profile cannot be
raised by a configuration record: it bounds the work of opening the store
(the transaction directory is enumerated up to T, the replay input up to H)
before any configuration record is read. Raising it is an offline step on the
existing store:

```text
fn operator /path/to/fn.toml store upgrade-profile --max-transactions 1000000
fn operator /path/to/fn.toml store upgrade-profile scale
fn operator /path/to/fn.toml store upgrade-profile          # format 7 -> 8, bounds unchanged
upgraded profile=current transactions-used=7 transactions-budget=1000000 previous-budget=100000
```

It opens the store as `recover` does, so it is refused (1, `store is already
locked`) while an owner runs: stop the unit first. ACL2 decides
(`fn-profile-upgrade-verdict`, `books/store-profile-upgrade.lisp`): the new
profile must be valid and no field may shrink (`fn-profile-upgradep`); the
same profile (`same-profile`), a shrink (`not-an-upgrade FIELD`) and a
broken relation (by its name) are refused (1) and write nothing. With no word
the base is the store's own profile, so the bare verb on a format-7 store (one
written before D27) rewrites it as format 8 with every bound unchanged
(`fn-profile-upgrade-format-7-to-8`); a format-7 store is otherwise served
under that translation until it is upgraded. Format-6 stores are no longer
opened. The new frame replaces `config.json` by stage, fsync, rename and
root fsync; a death at any point leaves the old or the new profile, never a
torn one (`fn-bs-profile-program-crash-is-old-or-new`), and an I/O error
before the rename is a refusal (1), at or after it an uncertain outcome (3)
that the next `status` resolves by reading whichever frame is there. The
retention charge capacity is a different number and IS reconfigurable
(`capacity DECIMAL-UINT32`). An unknown profile word, a repeated field or a
value that is not a decimal below 2^64 is a usage error (5).

### Settle a client's lost post: `store inspect`

A client whose POST reply was lost settles it by re-sending the same article
under the same Message-ID (docs/agents.md). When that re-send meets the gate
instead (`440` because the login lost its posting right, `480`, or the
bound-principal `441`), the client stays `unresolved`, and the one
privileged answer is this lookup on the stopped store:

```text
fn operator /path/to/fn.toml store inspect '<fn-client.20260922T034404Z.3fd1ce9e@yue.invalid>'
accepted <fn-client.20260922T034404Z.3fd1ce9e@yue.invalid> an article is stored here under this Message-ID
fn operator /path/to/fn.toml store inspect '<never-posted@fn.example.invalid>'
absent <never-posted@fn.example.invalid> nothing is stored here under this Message-ID
```

`accepted` (exit 0) means the store binds that Message-ID: the article was
committed, whatever its visibility now (a cancel or a reclaim does not
unbind it). `absent` (exit 1) means nothing is stored under it. A word that
is not a Message-ID is a usage error (5). It opens the store as `recover`
does, so it is refused (1, `store is already locked`) while an owner runs.
The store node's lookup decides and ACL2 renders the line
(`fn-native-operator-inspect-report-is-the-lookup`,
`books/native-operator.lisp`). It does not compare the stored text with the
client's copy; tell the client which answer you got.

Compaction is the other offline store step. It replaces the transaction
files of the committed history with one lossless pack:

```text
fn operator /path/to/fn.toml store compact
compacted steps=pack,select,reclaim,retire records=7 generation=0 reclaimed=7 retired=0
```

It opens the store as `recover` does, so it is refused (1, `store is already
locked`) while an owner runs. ACL2 decides what it does
(`fn-cverb-decide`, `books/store-compact-verb.lisp`) and the host carries out
exactly that:

- `pack,select,reclaim,retire`: capture every committed record's exact bytes
  into the next pack generation, publish it, select it, unlink the
  transaction files it covers and retire the older pack generations. The open
  afterwards hands replay the identical record list
  (`fn-ccp-reclaim-preserves-reconstructed-history`), so every article, number,
  watermark, retention pin and the next article number are unchanged.
- `reclaim,retire`: the selected pack already covers every committed record
  (a rerun after an interrupted compaction); no new pack is written.
- refused (1), nothing written, with the reason: `already-compact` (nothing
  to pack, reclaim or retire), `empty-history`, `temporary-space` (the new pack would not
  fit the free space of the store's filesystem, as the image observes it;
  the pack is written beside the files it replaces, so leave at least the
  history's size free), `exceeds-compaction-unit` (the
  history's pack would exceed 4 MiB, the unit one pack holds; the open reads
  a pack as one bounded read, and compacting a larger history needs chained
  packs, which do not exist yet).

A death or an I/O error at any step leaves a store the next `recover` opens
with the same history; an I/O error after a durable change is uncertain (3),
and rerunning `store compact` finishes the job. Compaction removes transaction
files, not transactions: the budget above counts committed records, and a
compacted store has the same `transactions-used` as before. A lost newest
transaction file is not detected at open (the allocation frontier is reserved
before the record is written, so the loss looks like an abandoned
reservation; `planning/evidence/m5-compact-verb-2026-09-24.md`, finding 1).

`status` prints the headroom beside the counts, from ACL2
(`fn-sbud-headroom`), not from a host count:

```
transactions=0 articles=0 staging-orphans=0 unsigned-legacy-experiment
headroom transactions-used=0 transactions-budget=128 charge-reserved=0 charge-capacity=1048576
```

`charge-reserved`/`charge-capacity` is the retention ledger in its abstract
units (one per record plus one per 4096-octet page of payload,
`fn-charge-for-payload`). With an owner running, `status` asks it (see
[Status while the owner runs](#status-while-the-owner-runs)); with none it
opens the store read-only.

`peer list` prints the peer records the durable configuration holds, one line
per peer, in the order `peer add` takes its arguments:

```
far path-identity=far.example address=192.0.2.44 port=1119 security=starttls inbound=fn.* outbound=fn.* auth=source-address:192.0.2.44
```

A half the record does not carry is `-`. The line is rendered by ACL2
(`fn-native-admin-peer-report`, books/native-admin.lisp) from the replayed
configuration's own peer rows. `peer list` is a read, answered like
`status`: by the running owner from the configuration it carries, or, with no
owner, from the store opened without the exclusive writer lock. It can neither
publish a configuration record nor take the lock away from the owner.

### Status while the owner runs

`operator CONFIG status`, `pins`, `obligations` and `peer list` print one
report, rendered by one ACL2 function (`fn-nls-report`,
books/native-live-status.lisp) whoever answers:

```
$ fn-native operator fn.toml status
transactions=12 articles=12 staging-orphans=0 unsigned-legacy-experiment
profile format=8 max-transactions=4294967295 max-history-octets=1099511627776 ... history-marker=unmarked
open-cost replay-records=4294967295 list-memory-octets=35184372088832
headroom transactions-used=12 transactions-budget=4294967295 bytes-used=5321 history-bound=1099511627776 charge-reserved=24 charge-capacity=...
open=full-replay reason=no-checkpoint
checkpoint-file=absent
pins=12 reserved=24 connections=1
connection id=3 config-generation=4
accepted operator status
$ fn-native operator fn.toml obligations
obligations=12 reserved=24
obligation id=... kind=archive charge=2 subject=...
$ fn-native operator fn.toml pins
pins=12 reserved=24 connections=1
connection id=3 config-generation=4
```

Every value prints in full decimal, and `history-marker` prints its word
(`required` or `unmarked`). `open-cost` is the profile's pessimistic open
figure, not a measurement: the worst open is a full replay of up to
`max-transactions` records (a checkpoint may be absent or refused), holding
the record payloads as octet lists, two copies at 16 octets of cons per
payload octet, so 32 × `max-history-octets`. `open=` says how this answering
process opened the store; `checkpoint-file` is the newest published state
checkpoint's size and modification time when the report was asked for
(`checkpoint-file=absent` when there is none). The owner renders a report
once per request and answers its later pages from that rendering.

`pins` is the retention ledger's count and reserved charge, then each open
connection's configuration pin (the generation it reads under);
`obligations` lists the ledger's held obligations. The BP node's forwarding
obligations are not in this report: they belong to the DTN image's
`bp-obligation status`.

When the configuration's control socket is live, the command asks the owner
over it (FNLS frames, pages of at most 128 KiB, joined by the client) and the
owner renders the report from the Store, configuration and connection pins it
carries, under its mutex, changing nothing
(`fn-nls-live-report-is-the-offline-report`: with no connection open, those
are the offline words of the same state). With no socket, or a socket nothing
accepts on, the store is opened read-only, which refuses (1) while any owner
holds it. A failure after the request was sent is uncertain (3); an owner
that is stopping refuses (1). The `open=` line names how the answering
process opened the store, so it can differ between the owner and a later
offline read.

`status --watch SECONDS` (1 to 86400) prints the report again every
SECONDS until interrupted, one tagged result line after each.

`policy set path-identity` gives the node its own RFC 5537 section 3.2
`<path-identity>`. Until it is set, the owner cannot recognise its own name in
a `Path` header and section 3.5 loop suppression cannot fire, which the native
v0 matrix measured on 2026-09-22 as `V0-TRANSIT-LOOP` accepting the looped
article. It is a durable configuration record like a group or a peer, refused
while the owner holds the writer lock offline and applied live through the
owner otherwise.

The same slot is the injecting agent: every article a served POST injects
carries `Path: IDENTITY!not-for-mail` and `Injection-Info: IDENTITY` for the
policy value in force when the connection opened (books/owner-agent.lisp,
`fn-oag-post-config`), and a store without the policy injects as
`fn.example.invalid`. There is no second place to name it. `[posting] agent`
in fn.toml is refused by `run` as `UNSUPPORTED-PROFILE agent`, whatever it
says: a value there could only disagree with Path, and a name with `@` in it
is not a `<path-identity>`. Set the policy instead.

What `run` admits of fn.toml, key by key (`fn-native-config-unsupported-key`,
books/native-config.lisp): `[store]`, `[listener]` (a numeric address or a
loopback alias, TLS paths paired), `[auth]` (`protected_only` only with a TLS
pair), `[posting] enabled`, `[control]`, and `[log] path` when it is absolute.
It refuses, naming the key, `[posting] agent`, `[anchor]`, `[acl2]` and a
relative `[log] path`: `usage operator run (UNSUPPORTED-PROFILE agent)` and
exit 5. The offline verbs above still accept such a file.

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

### Health: which of eight things is wrong

`operator CONFIG health` (HST-007) answers with one line per state, always
in this order, then exits with a code that names the first one held:

```
$ fn-native operator fn.toml health
health exit=22 state=unqualified-profile
fenced clear
exhausted clear
unqualified-profile held format=8 development
space-pressure clear
no-route clear
stranded-transfer clear
unavailable-peer held peers: hub
receipt-debt clear
accepted operator health
```

| exit | state | held when | what to do |
|---|---|---|---|
| 20 | `fenced` | a clone fence awaits its incarnation rollover; a process holds the store's writer lock and the configured control socket does not reach it; or the socket accepted and did not answer | find the process (`fuser store/writer.lock`); a clone finishes its rollover; never delete the lock |
| 21 | `exhausted` | transactions used reached the transaction-id codec ceiling (2^32 - 1), or the retention ledger's reserved charge its uint32 count | terminal for this store format: no `store upgrade-profile` raises it |
| 22 | `unqualified-profile` | the persisted profile is not format 8 (`store needs-upgrade`), or it is the development profile | `store upgrade-profile scale` or `default` (offline) |
| 23 | `space-pressure` | free headroom below `[alerts] headroom_min_percent` (default 10) on transactions, history octets or retention charge | `store upgrade-profile`, `capacity`, or release obligations |
| 24 | `no-route` | forwarding obligations are held and the configuration has no `bp-route` | `bp-route add PATTERN BOUNDARY` |
| 25 | `stranded-transfer` | an outbound feed entry was dropped at its retry bound; nothing re-offers it | fix the peer, then re-feed the article |
| 26 | `unavailable-peer` | an outbound peer has pending articles and no open connection | check the peer's host and port (`peer list`) and its reachability |
| 27 | `receipt-debt` | forwarding obligations are held, awaiting the receipt that releases them | `bp-obligation status`; the receipt releases each |
| 19 | (none held) | some state is `unobserved` | offline, the two feed states need a running owner |
| 0 | (healthy) | every state is `clear` | |

Each state is its own line, and several can hold at once; the exit code is
the first held one in the table's order, so a script can branch on it and
a person reads every line. `unobserved` is never `clear`: with no owner
running the feed table does not exist, and a fenced store is not opened, so
those lines say why they were not observed.

With the control socket live, the running owner renders the verdict from the
Store, configuration and feed table it carries, under its mutex, with the
`headroom_min_percent` of the `fn.toml` it was started with; offline the
store is opened read-only with the current `fn.toml`'s threshold. The
first line (`health exit=NN`) is what the command exits with: ACL2 renders
it and reads it back from the same octets
(`fn-nh-report-exit-of-render`, books/native-health.lisp).

### From the release tarball

`packaging/release-tarball.sh FROZEN_DIR REVISION OUT_DIR` packages one
frozen image as `fn-REV12-linux-x86_64.tar.gz` with its `.sha256`: the
installed layout below under one directory `fn-REV12/`, carrying the SBCL
runtime, OpenSSL 3.5 and libsodium beside the image, the operator documents
under `share/doc/fn/`, and `SHA256SUMS` over every file. The launcher finds
all of it relative to itself, so the directory runs wherever it is unpacked
and needs no system OpenSSL. What a stranger runs, in order (each step's
exact words and what it answers are in
[peering with a friend](peering-with-a-friend.md), section 1):

1. `sha256sum -c` the tarball's sum, unpack, `sha256sum -c SHA256SUMS`.
2. `fn operator NODE/fn.toml mission small-community --host IP --port P`
   writes `fn.toml` (login required, only after STARTTLS; TLS paths under
   `NODE/tls/`). It does **not** make the TLS pair: make one with `openssl
   req -x509 ...` whose subjectAltName is the address others dial, into the
   two paths `fn.toml` names.
3. `init` (a small community serves `local.general` and `local.test`),
   `policy set path-identity NAME`, `principal set-password LOGIN
   --posting` (the password twice, from the terminal or two lines of stdin;
   it applies at the next start).
4. For peering, the node's keys: `peer keygen KEYDIR` (an absolute path
   that does not exist yet) makes the directory mode 0700 with an Ed25519
   pair from the tarball's libsodium and an ML-DSA-65 pair from its OpenSSL
   3.5, every file 0600, and runs `peer genesis KEYDIR`, printing the
   principal. It refuses an existing directory. A directory made by hand
   with an `openssl` 3.5 command, then `peer genesis KEYDIR`, is the same.
5. `fn operator NODE/fn.toml run` under a service manager
   (`systemd-run --user --unit NAME -p MemoryMax=8G ...` on a box without
   root).

`fn operator CONFIG help VERB` prints each verb's grammar. `fn` with no
words prints the operator's usage (it is `fn operator - help`), and `fn
--version` prints the 40-digit source revision recorded beside the image's
core (`libexec/fn/source-revision`, written by the installer; exit 1 when
the image records none).

### Install the native production entry

Build or select a source-pinned frozen image with `packaging/freeze-native-image.sh`
(as in `tools/runbooks/hbox-image-build.sh`). Its production `fn-host` and
adjacent `fn-host.core` travel with their SBCL runtime and crypto libraries.
Stage an installation without starting a service:

```sh
FN_NATIVE_HOST=/path/to/fn-host FN_NATIVE_CORE=/path/to/fn-host.core \
  FN_NATIVE_SOURCE_REVISION=<image-source-commit> \
  DESTDIR=/tmp/fn-package PREFIX=/usr/local packaging/install-native.sh
```

`bin/fn` is `packaging/fn` (`packaging/fn-native` is a link to it): it finds
the image (`FN_NATIVE_HOST`, else `../libexec/fn/fn-host` beside itself, else
the checkout's `build/fn-host`) and execs it with every argument, deciding
nothing. `fn operator CONFIG VERB ...` is the operator, `fn bp-node ...` and
the other image verbs are as below. The spike's bash `fn` wrapper made its
own decisions; each is now the image's (its header lists where each went:
`mission`, `health`, `show`, `store needs-upgrade`/`rollback-check`, the
SIGHUP log reopen) or is gone.

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
code. For a frozen image, the copied libraries travel with the release; the older
generated-launcher installation form still uses system package dependencies.
Rendered service files live under `share/fn/systemd` and
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

### Developer selectors

The developer image honours the registered environment selectors and one positional
argument that arm a cut or a fault. The table is `+fnn-developer-selectors+`
in `host/native/io.lisp`; each is read only through `fnn-developer-selector`,
which answers nothing on a production image.

| selector | value | what it arms |
| --- | --- | --- |
| `FN_NATIVE_POST_FAULT` | `CUT:eio\|kill`, CUT one of `+fnn-post-model-cuts+` | the frontier, record and finish cuts of a post, in `store ROOT post` and in the served owner (`operator CONFIG run`, and the developer `owner run`) |
| `FN_NATIVE_RECOVERY_FAULT` | `CUT:eio\|kill`, CUT one of `recover-replayed`, `recover-barrier` (the first of its five sites), `recovery-stage-unlinked` | recovery's cuts, in `store ROOT recover`, `operator CONFIG recover`, `store ROOT post` and the served owner's own recovery at start |
| `FN_NATIVE_INIT_FAULT` | `CUT:eio\|kill\|eacces` | the initializer's cuts |
| `FN_NATIVE_CONTROL_FAULT` | one of `prepublish`, `postpublish`, `frontierbarrier`, `recordbarrier` | the owner's store for exactly one control submission; `postpublish` is the uncertain outcome |
| `FN_NATIVE_CONTROL_TEST_STOP` | `after-submit` | a SIGSTOP of the owner from the worker that holds the reply, after the owner answered accepted, duplicate or refused and before the reply is sent; the stop is directed at that thread (`pthread_kill`), so the reply cannot leave first |
| `FN_NATIVE_AUTH_ADMIN_FAULT` | `CUT:eio\|kill` | the AUTHINFO credential writer's cuts |
| `FN_NATIVE_KEY_STATEMENT_FAULT` | `statement-committed:kill` | the cut between a key statement's commit and its key change's (books/key-statements.lisp `fn-ks-cut`) |
| `FN_NATIVE_OWNER_TEST_SIGTERM` | `after-install` | a SIGTERM between owner recovery and listen |
| `FN_NATIVE_OWNER_TEST_PAUSE_CLEANUP` | `1` | a two-second pause inside owner cleanup |
| `store ROOT post ... FAULT ...` | one of the four `+fnn-cli-faults+` names | the same four store faults as `FN_NATIVE_CONTROL_FAULT`, for one `store post` |

The served owner and `store ROOT post` read the post and recovery selectors
through one function, `fnn-post-entry-fault`, into the one store fault slot
that every `fnn-at` cut tests; at most one of the positional FAULT,
`FN_NATIVE_POST_FAULT` and `FN_NATIVE_RECOVERY_FAULT` may be set (usage 5
otherwise). The cut sites are the `fnn-at` calls in `fnn-recover`,
`fnn-advance-frontier`, `fnn-publish` and `fnn-finish`, which both entries
call.

A production image refuses raw `store ROOT post` with usage exit 5 before
opening the Store or reading the payload, even if `FN_NATIVE_PROFILE=developer`
is set at invocation. Use `operator CONFIG post` or NNTP submission for
production posting. Raw insertion remains available on developer images;
Store inspection and recovery remain production operations.

The low-level native `--fn store ROOT retention` diagnostic opens the recovered
Store under a shared lock and prints `pins=N reserved=B` from the ACL2
retention ledger. It reports aggregate active pins and reserved charge; it does
not decide release or identify an obligation. Like `store ROOT status`, it
refuses with exit 1 if a live writer holds the Store lock.

A production image refuses to start when any selector in the registry is set in
its environment, even to the empty string, or when `store ROOT post` is given
a FAULT other than `-`. `fnn-main` runs `fnn-developer-selector-gate` before
dispatch, so the refusal is usage exit 5 naming the variable, and no store,
socket or request is reached. A running production node therefore never
meets a selector in the middle of a request: accepted, refused and uncertain
keep their meanings for every real request. The same startup gate covers the
registered BP, TCPCL, checkpoint, application-journal, and immutable-publication
test selectors. The DTN build selects and serializes the same profile, with a
separate `build/fn-host-dtn-developer` output when
`FN_NATIVE_PROFILE=developer` is supplied during construction.

### The DTN image: a BP node without the NNTP service

`host/native/build-dtn.lisp` builds `build/fn-host-dtn` (and
`build/fn-host-dtn-developer`). It is a BP node, not only a convergence
layer: it carries the node service, the Store owner and the operator's
configuration path, and leaves out the NNTP reader, the NNTP service
(TLS listener, authentication, the outbound feed service), credential
administration and the control socket. Its verbs:

| verb | what it is in this image |
| --- | --- |
| `bp-node serve PORT JOURNAL STORE RECEIPTS WORKFLOW NODE PEER DEST POLICY ISSUER CONTACT-HOST CONTACT-PORT ...` | **the node**: one FNBS machine (`fn-bpnp-step`), the kind-8 retry policy, the owner Store with FNRJ/FNWF, admission of each TCPCL session from its observed channel against the enrolled boundaries |
| `bp-node dispatch ...` | the same node without a listener |
| `bp-node resume JOURNAL NODE-ID ARRIVAL` | re-arms a stranded forwarding row (see [Stranded forwarding rows](#stranded-forwarding-rows)); run it with the node stopped |
| `bp-obligation status\|undertake\|request\|recover\|receipt` | the owner-mode forwarding obligation journal; `request` publishes ACL2's attempt for one work and hands its request ADU to the FNBS carrier; `recover` resolves an attempt fenced by a process death (see [Fenced workflow attempts](#fenced-workflow-attempts)) |
| `bp-app receive` | the application receiver over the owner |
| `operator CONFIG init\|status\|recover\|help` and the administrative plans (`policy set path-identity`, `bp-boundary add`, groups) | node configuration through the one ACL2 operator plan; `run`, `post` and `principal` exit 5 (their surfaces are not in this image) |
| `store ROOT init\|recover\|status\|retention\|config\|inspect\|probe` | Store diagnostics, as in the default image |
| `app-journal`, `bp-service`, `bp-contact`, `tcpcl` | journals, the queue service, contact windows, the convergence layer |
| `bp send`, `bp receive`, `bp decode` | the lab's transport tools, not the node: `bp send` reports a contact severed after it connected as interrupted (exit 6) and one that never connected as not-connected (exit 7), and a fence as uncertain (exit 3) and its RETRY argument re-offers a named durable `authored-N.wire` with its original identity; `bp receive`'s STORE argument admits sessions against that Store's enrolled boundaries, and without it every inbound bundle is refused at the receive boundary |

`reader` is refused and `model` faults, as the build header says, and the
developer-only `owner` verb is not registered in either DTN image.

**Relays (D23).** A BP boundary names one TCPCL neighbour. When that
neighbour is a relaying BPA (dtn7-rs, ION), list the far fn nodes whose
bundles it may carry, and enrol each far node under its own EID:

```sh
fn operator CONFIG bp-boundary add relay-r1 r1.example dtn://neighbour/ PORT carries dtn://far-node/
fn operator CONFIG bp-boundary add far-node far.example dtn://far-node/ OTHER-PORT fn.* 32768 16
```

A request or receipt from `dtn://far-node/` carried by `relay-r1` is then
judged under `far-node`'s enrolment (its path identity and inbound scope),
never the relay's. A carried source with no enrolment of its own here is
refused (`BP node source refused reason=carried-source-unenrolled`), and a
source the neighbour does not carry is refused `source-not-carried`. The far
node's PORT names a listener the far node would use if it connected
directly; it must differ from the relay's so the two boundaries stay
distinguishable on the channel.

#### Stranded forwarding rows

A forwarding attempt is **uncertain** when the peer may or may not hold the
bundle:

- its process died after the kind-8 record was durable and before its
  kind-9 result was, or
- the connection failed after the durable kind 8 and before the peer
  answered with XFER_ACK or XFER_REFUSE. The node logs

  ```
  BP forwarding transfer uncertain arrival-key=... (connection-local; retried on a later session)
  BP forwarding result durable arrival=A status=uncertain
  ```

  and keeps serving: the fault costs that connection only. ACL2 reads the
  transfer (`fn-bpnp-tcpcl-outcome`), and its kind-9 `:uncertain` record
  keeps the attempt and its count.

The node re-offers an uncertain row, with its original identity, on each
later session to the same next hop, in the same process or after a
restart, and counts every re-offer in the durable kind-8 history. Neither a
restart nor a new connection resets the count. After three such re-offers
(`*fn-bpnp-max-forward-retries*`, so four uncertain transfers in all) the
row is **stranded**, and a session to that peer that has nothing else to
offer logs

```
BP forwarding stranded arrival=A retries=3 (held; no session or restart re-offers it; bp-node resume re-arms it)
```

What that means:

- The row is kept, never dropped: its bundle and its attempt stay held, and
  `bp-node` keeps counting it in its storage and credit. Nothing was lost
  and nothing was delivered by this node's account.
- No new session, contact or restart resumes it by itself.

To resume it, stop the node and run

```sh
fn bp-node resume JOURNAL NODE-ID A
```

with the arrival number A from the stranded line. ACL2 decides:

- For a stranded row it writes a durable kind-9 `:resumed` record naming
  the row's last attempt (`BP forwarding result durable arrival=A
  status=resumed`, exit 0). The next session to the row's next hop offers
  the same bundle again, with its original source, creation timestamp and
  sequence, and the count starts again at 0. The four kind-8 rows that
  exhausted the budget, and the `:resumed` row, stay in the FNBS journal:
  the history keeps the exhaustion and records that an operator re-armed it.
- Anything else is refused with ACL2's reason and writes nothing (exit 1),
  logged as `BP forwarding resume refused arrival=A reason=R`:
  - `no-row`: no held row has that arrival.
  - `not-forward-pending`: the row was already forwarded or is not a
    forwarding row.
  - `not-attempted`: the row has no attempt to re-arm (never offered, or
    already resumed).
  - `not-stranded`: its attempt is still under the bound, or in flight.
  - `busy`, `fenced` or `no-capacity`: the machine cannot take a record now.

Before resuming, it is worth confirming out of band (the peer's logs or
store) whether the peer already holds the bundle. A re-offer of a bundle the
peer holds is acknowledged as a duplicate and settles the row, so resuming
never creates a second copy there.

A peer that answers a re-offer with TCPCL XFER_REFUSE reason code 1
(Completed) settles the row exactly as an acknowledged transfer does; any
other refusal reason is logged and recorded as that reason and the row
stays pending for a later session, without counting toward the bound.

#### Fenced workflow attempts

`bp-obligation request` publishes a work's attempt record, then its outcome.
If the process dies between the two, the next open of the workflow journal
finds the attempt pending with no outcome. The image is **fenced** on it:
status reads work (`status=outstanding pinned=yes`), but every request is
refused, and so is every receipt on that journal
(`ACL2 refused a request ...: the workflow image is fenced on an uncertain
publication`). Establish out of band whether the attempt's request left
the node (its FNBS carrier job, the peer's logs), then run

```sh
fn bp-obligation recover STORE WORKFLOW WORK ATTEMPT committed|absent
```

- `committed`: the attempt stands. The work's attempt becomes `unknown`,
  which a later `request` retries at the next generation.
- `absent`: the attempt is dropped; the work keeps its earlier state.

ACL2 decides whether WORK and ATTEMPT name the fenced attempt
(`fn-bprq-recovery-plan`) and returns the exact recovery outcome record,
which the host publishes (`BP obligation recovery durable ...`, exit 0).
The journal is then unfenced, and the next open replays the record exactly
as it was applied. A refusal writes nothing (exit 1) and names its reason:
`not-fenced` (nothing to recover), `pending-not-attempt`,
`attempt-unknown` (not that work's fenced attempt) or `outcome` (neither
`committed` nor `absent`). The obligation's pin is never touched by
recovery; only a receipt releases it.

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
table: `[store] path`, `[listener] host port`, `[posting] enabled`,
`[anchor] server`, `[acl2] path slots`, `[log] path`, `[control] path`. This
development `fn init` also writes `[posting] agent` from `--agent`, and
`[anchor]`/`[acl2]` from their flags; the native `operator CONFIG run`
refuses all three by name (see [Native component entry](#native-component-entry)),
so delete those lines from a file this command wrote before handing it to
the native image, and set `policy set path-identity` for the agent.

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

The last word is the streaming flag. `true` opens each connection with
`MODE STREAM` and offers with `CHECK`/`TAKETHIS` (RFC 4644); `false` offers
with `IHAVE` (RFC 3977 section 6.3.2). A peer that does not stream answers
`MODE STREAM` with something other than 203 (501 in practice, RFC 4644
section 2.3). The owner then stops feeding that peer for the rest of its
run and says why, once, in its log:

```
refused feed peer=hub stopped reason=mode-stream-refused (RFC 4644 2.3: the peer does not stream; this owner does not dial it again; re-add the peer with streaming false to feed it with IHAVE)
```

It does not re-dial it with `MODE STREAM` (before 2026-09-26 it did, at
every backoff, indefinitely). `health` shows the peer under
`unavailable-peer` while articles wait for it. Re-add the peer with the flag
`false` (stop the node, `peer remove NAME`, `peer add ... false`) and start
it again. The stop is ACL2's (`fn-fc-mode-stream-refusal-stops-the-dial`,
books/feed-connection.lisp) and lasts one owner process: a restart spends
one `MODE STREAM` exchange again.

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

The tunnel listens on `::1` as well as `127.0.0.1`, so `--node [::1]:PORT`
reaches the node too; `tools/fn_client.py` takes the RFC 3986 brackets.

Two things about the frozen `915d5c72` image were measured over this tunnel on
2026-09-22 ([the record](../planning/evidence/fn-client-915-2026-09-22.md)) and
belong to whoever runs it. A POST whose article passes about 32 KiB **stops the
owner process** -- `owner core/store fault; process stopped: plaintext owner
read left a suffix without TLS`, the listener goes away, and the article is not
stored; ~32 250 octets was accepted and ~33 031 was fatal. And every article
accepted during one owner run carries the same `Date` and `Injection-Date`,
taken once at start: `DATE` returns one value for the life of the process.
Neither is a client fault and neither is fixed in that image.

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

For a person, the same node in a browser: the web reader logs in over the
same verified STARTTLS, asks for the password on the terminal (or takes
`FN_CLIENT_PASSWORD`), and serves pages on `127.0.0.1` only
([the web reader](web.md)):

```sh
mkdir -p ~/.fn ~/.fn-web
scp hbox:/tank/fn/node/tls/cert.pem ~/.fn/hbox-cert.pem
python3 tools/fn_web.py --node 192.168.50.39:1119 --tls-cert ~/.fn/hbox-cert.pem \
  --user ember --outbox ~/.fn-web/outbox-hbox-ember
# then open http://127.0.0.1:8919/
```

It exits 1 if the node refuses the login or the certificate does not verify,
3 if the node cannot be reached, and 2 if no password is available.

## Post and read

Read with any NNTP client against the configured port:

```
telnet 127.0.0.1 1119
GROUP fn.letters
ARTICLE 1
```

An agent that polls rather than browses asks for what is new, by
Message-ID, with `NEWNEWS` (RFC 3977 §7.4):

```
NEWNEWS fn.* 20260919 000000 GMT
230 list of new articles by message-id follows
<2026-09-19.1@example.invalid>
.
```

Two things to know before you build a poller on it. First, the instant fn
compares against is the **store's own acceptance stamp**: the owner's whole
wall-clock second when it prepared the article, recorded with it and
independent of the article's `Injection-Date` and `Date`
(`fn-nntp-newnews-scan`, books/nntp-responses.lisp). A record written before
stamps were kept takes the nearest later stamped article's second, else the
reader's pinned wall second, else it is listed at every threshold. Second,
the answer is one pass over the committed list with no article parsed, one
line per matching article; a reclaimed article is not listed. A `501` from
`NEWNEWS` is a syntax error in the arguments, and a `503 two-digit year
needs a wall clock reading` means the date was given with two digits and the
node holds no wall-clock reading to place its century; a poller should not
retry the first.

`LIST NEWSGROUPS` lists the served groups with a description field. fn's
group table carries no description, so every line reads
`name<TAB>(no description)`; the marker is a statement about the server, and
fn does not invent a sentence about a group.

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
| `refused` | 6 | (native `fn operator`) No store at the configured `[store] path`: run `init`. |

These three outcomes stay distinct everywhere: the exit code, the stderr
line, the log line, and the reply on the control socket. Never map
`uncertain` onto either of the others in a wrapper script.

The service log (`[log] path`, otherwise stderr, which under systemd is the
journal) carries one line per post and one per accepted connection, with the
outcome word first. `run` opens `[log] path` append-only (created 0640 if it
is absent, never through a symlink) before it opens the store, so a wrong
path fails before recovery; fn never truncates or rotates it. A connection
line says the **role** the owner gave the connection at accept, which it
decides from the peer table and not from anything the client says: `reader`,
or `peer` with the record's name. A post line's word is the reply's word:
`accepted` exactly when the owner consumed a durable completion (the 240),
`refused`, `uncertain`, and for a control post `duplicate` too. A served
post names the connection and the agent its Injection-Info carries; a
control post stores an already-authored article and names no agent. Every
field is at most 256 printable octets, anything else shown as `?`, so a line
is one line whatever a client sent (books/owner-log.lisp).

```
accepted reader connection=2 time=2026-09-22T21:04:33Z
accepted post path=served connection=2 message-id=<a@example.invalid> agent=news.example.org time=2026-09-22T21:04:34Z
accepted peer connection=3 peer=innA time=2026-09-22T21:04:35Z
accepted post path=control message-id=<b@example.invalid> time=2026-09-22T21:05:01Z
refused post path=control message-id=<c@example.invalid> time=2026-09-22T21:05:02Z
```

A POST refused before it becomes a submission (a 441 from the injection
check itself) writes no post line; the connection line and the client's
reply are the record of it.

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
- `[listener] tls_port = 1563` opens a second listener beside `port` whose
  connections begin TLS at connect (the port-563 practice RFC 4642 §1
  describes; tin 2.6 and other NNTPS readers speak only this form). The
  owner prints `LISTENING-TLS 1563` after `LISTENING`. It is refused as a
  configuration (`usage`, exit 5) without `tls_cert`/`tls_key` or on the
  plaintext port, and not opened by `run --once`. A connection on it is the
  STARTTLS session after its handshake: no `STARTTLS` label, `502` to
  `STARTTLS`, AUTHINFO allowed under `protected_only` from the first
  command (`books/served-implicit-tls.lisp`).

The policy reaches every connection the owner opens, including one it
resolved to a peer record. A peer does not run AUTHINFO, so on a node with
`required = true` a transit peer is answered `480` for `IHAVE` as well; do
not set it on a node that is also taking a feed until that is decided
(`planning/deputies/BOARD.md`, w11/auth-live).

Restart the service after changing either the policy or the credential
file: both are read once at start-up.

### Bind a login to its signing principal

A signed POST is `verified` for whichever principal signed it, whatever
login posted it. To make a login post only as its own principal:

```
packaging/fn-native operator /etc/fn/fn.toml principal bind alice PRINCIPAL-HEX  # 64 lowercase hex digits
packaging/fn-native operator /etc/fn/fn.toml policy set posting-policy bound-logins
```

These are the native operator's verbs (`fn-host --fn operator CONFIG ...`);
the Python `bin/fn principal` has only `new`, `list` and `set-password`. The
native operator loads the hybrid-signature library, so it needs OpenSSL 3.5
(`FN_OPENSSL_PREFIX`), as the node does. A later `policy set posting-policy
open` takes effect: a policy slot holds the value set last
(`fn-cfg-set-policy-sets-the-policy`, books/config-invariants.lisp; until
2026-09-25 the first value set stayed in force).

`bind` writes a `signing` field into alice's table of `auth.toml` (restart to
apply, like any credential change; `principal list` shows `signing=HEX`;
`principal unbind alice` removes it). The policy is a durable configuration
record, applied live. Under it, alice's unsigned article is answered `441
posting failed; this login posts only articles signed by its bound
principal`, and one signed by another principal `441 posting failed; the
login is not bound to this signing principal`. A login without a binding,
and every login on a node whose policy is `open` (the default: `policy set
posting-policy open`), posts as before. The service log names the login of
each decision (`post login=alice bound=...`).

## Expose a node to strangers

Everything below is what runs on the branch and what the SCN-091 campaign
measured on hbox (`planning/evidence/public-exposure-2026-09-26.md`); no fn
node is exposed yet, and whether and how one is is PKT-404.

A listener outside 127.0.0.0/8 and `::1` changes the default of every
exposure row the configuration does not set. Loopback keeps the old
behaviour. The rows are durable configuration, set with `policy set` like
`path-identity`, applied to a running owner at once and replayed at every
start:

```
fn operator /etc/fn/fn.toml policy set exposure-connections 200
fn operator /etc/fn/fn.toml policy set exposure-per-address 8
fn operator /etc/fn/fn.toml policy set exposure-steps-per-second 64
fn operator /etc/fn/fn.toml policy set exposure-first-seconds 60
fn operator /etc/fn/fn.toml policy set exposure-idle-seconds 600
fn operator /etc/fn/fn.toml policy set exposure-auth-failures 10
fn operator /etc/fn/fn.toml policy set exposure-posts-per-minute 60
fn operator /etc/fn/fn.toml policy set anonymous none
```

What each does, what the client sees and the default off loopback is the
table in `specs/nntp.md` ("Public exposure"). In short:

- **Connections.** One fewer than the run's `max_connections` (32) is the
  most sockets can hold: the last is kept for your own `policy set`, which
  stages through the owner. Past the total a client reads `400 too many
  connections; try again later` and is closed; past the per-address limit,
  `400 too many connections from this address; try again later`. Under a
  flood of 500 connections from one address the owner admitted 8 and sent
  the 400 to the other 492; from 50 addresses with the per-address limit at
  1, it admitted 30 and refused 470, and a fresh connection of yours got the
  busy 400 until the flood's silent connections timed out.
- **Silence.** A connection that sends no command for
  `exposure-first-seconds`, or answers nothing for `exposure-idle-seconds`
  after that, is closed with no reply (RFC 3977 §3.1). A client trickling
  one octet a second is silence too: only an answered command or 512
  octets resets the timer. With the timer at 5 s, silent and trickling
  connections closed at 5.0 s.
- **Work.** Each source address may start `exposure-steps-per-second`
  served steps a second (a step is one read of at most one buffer). Past it
  the connection is not refused: the owner stops reading it until the next
  second, so the client slows down and loses nothing. At 20 a second an
  anonymous `STAT` loop ran at 22 a second including its first burst.
- **Failed logins.** After `exposure-auth-failures` 481 answers in a minute
  from one address, that connection reads `400 too many authentication
  failures; closing connection`, and new ones from the address read `400
  too many authentication failures from this address` until the minute
  ends.
- **Anonymous readers.** `anonymous none` (the default off loopback, and
  always when `[auth] required` is set) answers `480` to every reading and
  posting command until the client logs in; CAPABILITIES, HELP, DATE, MODE,
  QUIT, AUTHINFO and STARTTLS still answer. `anonymous open` is the old
  behaviour, and it lets an anonymous client POST if `[posting]` is
  enabled: there is no read-only anonymous level yet (PKT-405).

`operator CONFIG health` prints three `exposure` lines after its eight
states: `exposure pressure held|clear` (held at nine tenths of the total or
after any refusal, wait or close in the current minute), the counts
(`admitted`, `refused-busy`, `refused-address`, `refused-auth`, `deferred`,
`idle-closed`, `auth-closed`) and the limits in force. They do not change
the exit code.

Before you open the port: set `[auth] required = true` and `protected_only
= true` and a TLS pair (see "Require a login"), choose the certificate
(a self-signed pair pinned by your readers, or a CA's; PKT-404 compares
them), and do not put fn behind a TCP proxy unless the proxy limits per
source itself: fn does not read the PROXY protocol, so behind a proxy every
client is the proxy's address and one abuser would use up everybody's
per-address and failed-login allowance.

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

**Special-purpose names are a local agreement, not ordinary groups.** RFC
5536 section 3.1.4 names two kinds of restricted `<newsgroup-name>`. The
reserved ones (a first or only component `example`, and `poster`) are
refused at `group create` and `init`. The specific-purpose ones MUST NOT be
used as normal newsgroups but MAY be used for their purpose or by local
agreement, and `group create` admits them on that footing. They are
patterns, not a list: a first or only component `to` or `control`
(`to.peer`, `control.cancel`), any component `all` or `ctl` (`fn.all`,
`a.ctl.b`), and exactly `junk`; case is folded
(`fn-native-admin-group-name-special-purposep`, books/native-admin.lisp).
Create one only for a convention your peers have agreed to. Such a group is
not a globally compatible newsgroup name: another server may treat
`control.*` or `junk` as its own, read `all` as a wildcard, or refuse it.
In fn the name confers nothing. fn does not read control-message,
point-to-point (`to.*` with `ihave`), wildcard or junk handling from a
group's name, and the name grants no creation, moderation, deletion or
forwarding authority. The plan for creating one is exactly the plan for any
other valid name (`fn-native-admin-plan-create-ignores-special-purpose`).

## Upgrade, and what a rollback loses

Rehearse on a copy first: stop the node, `cp -a` its store, give the copy a
`fn.toml` whose paths point into the copy and whose listener is on loopback,
and run the steps below against the copy with the new release's `bin/fn`.
`packaging/upgrade-native.sh` switches a managed node's `current` release.

```
fn operator COPY/fn.toml store needs-upgrade            # needs-upgrade | current
cp -p COPY/store/config.json KEPT/config.json.format-7  # the file a lossless rollback restores
cp -a COPY/store SNAPSHOT/store                          # the pre-migration snapshot
fn operator COPY/fn.toml store upgrade-profile           # format 7 -> 8, bounds unchanged
fn operator COPY/fn.toml store upgrade-profile --max-transactions N   # raise one bound
fn operator COPY/fn.toml store rollback-check KEPT/config.json.format-7
fn operator COPY/fn.toml store rollback-check --snapshot SNAPSHOT/store
```

There are two rollbacks, and they are not the same:

- **Restoring the kept `config.json`** (the old release reads the new
  history under the old profile). `rollback-check KEPT` says `rollback sound
  transactions=N` when every committed record fits the older profile and the
  store does not require the committed-history marker; nothing is lost. It
  refuses `history-marker-required-dropped` once the store requires the
  marker: that requirement is never undone by a kept file.
- **Restoring a pre-migration snapshot** (the whole store as it was).
  **Restoring a pre-migration snapshot loses every article accepted after
  it.** `rollback-check --snapshot SNAPSHOT` counts them. Stop the node
  first: the verb takes both stores' shared writer locks and holds them while
  it compares, so a running owner's store is refused (`store is already
  locked`, 1) rather than read mid-write. It reads each store's committed
  history the way the open does (the selected pack's records, then the
  transaction files after it) and ACL2 compares the two record by record,
  octet for octet (`fn-native-operator-history-loss-is-ancestry`). When the snapshot's
  records are exactly this store's first records it answers

  ```
  rollback snapshot loses transactions=3 snapshot-transactions=11 store-transactions=14
  the snapshot's committed records are this store's first 11, compared record by record (packed records included); restoring this snapshot loses every transaction committed after it: 3, the articles accepted since it among them; the snapshot cannot give them back
  ```

  and otherwise `rollback snapshot refused snapshot-not-a-prefix` (1): the
  snapshot is not an earlier state of this store's history, and restoring
  it would replace that history, not shorten it. That includes a snapshot
  from a different store whose transactions have the same numbers and the
  same file sizes: equal counters and lengths are not the same history, and
  the verb does not treat them as one.

  What the verb does not establish: that the snapshot is the newest earlier
  state you have, or anything about the configuration history, retention
  releases or peer state a restore also brings back; and a store-local
  comparison is not a freshness witness (see `fn anchor` under Back up).

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
channel answers; since 2026-09-25 that is the owner's own status report
(see [Status while the owner runs](#status-while-the-owner-runs)), not
`owner-held`.

## Experimental offline ION/LTP submission

The experimental offline ION/LTP sender uses the native developer image's
`app-journal` verbs against one stopped owner and its Store/FNWF journal:

```
fn --fn app-journal workflow-ion-submit STORE FNWF TXID TXGEN WORK_ID ATTEMPT_ID BP_DEST_EID OWN_BP_EID PINNED_HELPER PRIVATE_OBSERVATION_DIR
fn --fn app-journal workflow-ion-status STORE FNWF WORK_ID ATTEMPT_ID ATTEMPT_GENERATION
```

`BP_DEST_EID` is the ION route destination; the application peer comes from
the durable work and is a separate EID. The helper path is a trusted pinned
ION binary, and the observation directory must be owned by the invoking user
with mode 0700. The submit command records the attempt and route before its
first network operation; a successful exit means a real ION bundle ID was
observed and durably bound, **not** that the peer accepted the application
request. `workflow-ion-status` reports that binding after restart: exit 0 for
observed, 3 for a route with uncertain send/observation, and 1 when no route
was recorded. A route with no ID must never be automatically reposted. A
returned application receipt follows the separate `workflow-receipt` command
and its explicit authorization profile; neither an LTP ACK nor a BP delivery
report releases an obligation. This experimental command awaits certified
FNWF closure and a source-matched native image before operational use.

## What "uncertain" means, and what to do

For the BP verbs (specs/host.md "BP run classes"), exit 3 keeps this
meaning; a connection lost after it existed is exit 6 and a connection
that never existed exit 7. Neither asks for recovery: the job is durable
and the next contact re-offers it under the same identity. A BP node's
held rows, held octets, largest ADU and largest bundle are raised offline
with `bp-node profile JOURNAL NODE MAX-HELD-ROWS MAX-HELD-OCTETS
[MAX-ADU-OCTETS MAX-BUNDLE-OCTETS]` (default 64, 16 MiB, 65,538 and 1 MiB;
each at most 2^24; never lowered). A bundle past the ADU or bundle bound is
refused (`BP refused reason=adu-beyond-profile` or
`bundle-beyond-profile`, exit 1); a journal opened under a profile smaller
than its rows or held octets fences with `held-beyond-profile`, and since
`bp-node profile` opens the journal too, the remedy is to restore the
profile file that was in force.

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
