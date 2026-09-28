# Running fn: the engineers' reference

This page is the detailed reference behind [the operator's guide](operator.md):
the exact decisions, the book and packet names, the measurements and the
development-image material. A person running a node reads
[the operator's guide](operator.md) and [Installing fn](install.md) first.
Sections: the operator's verbs in depth, then (appended from the
previous user guides) the peering walk of 2026-09-26.

This is the operator's page: install fn on a box, initialize a store, run it
as a service, post and read, back it up, and recover after a crash. It
describes what `bin/fn` does today. It is not a deployment authorization and
makes no availability or flight-readiness claim; see
[architecture](architecture.md) for the boundaries and
[failures](../specs/failures.md) for what durability here assumes.

**Installing from a release** (`fn-VERSION-linux-x86_64.tar.gz` or
`fn-VERSION-openbsd-amd64.tar.gz`): read [Installing fn](install.md) first. It
is the whole path from the download to a node others reach over TLS, and it
names nothing outside the release. This page is the reference for the
operator's verbs beyond it: status and health in depth, recovery, peering
details, the measured envelope.

Everything the node runs is `bin/fn` (a shell script), the frozen launcher
and the saved Lisp image it execs; no Python runs on a deployed node
(D35, `tools/runpath_check.py`). Python remains for clients on other
machines and for the tests. The sections "Install", "Initialize" and the
per-user `~/fn-live` service further down describe the older Python
development service (`bin/fn --config ...` in a checkout); a release has
none of it, and its verbs are `fn operator CONFIG VERB ...`.

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

`init` never builds the store in place (PKT-647). It builds the empty store
in a new directory `ROOT.init-XXXX` beside the configured store ROOT and
publishes it by the same program as `store import` (below; `fn-bs-imp-program`
with init's cut names, `fn-bs-init-log-program` in
`books/store-init-log-publication.lisp`): each file created exclusively, written
and fenced, the directories fenced, the staged store opened the ordinary way,
renamed onto ROOT without replacing anything, ROOT's parent fenced. A crash
at any point leaves no store at ROOT or the complete empty store
(`fn-bs-init-log-program-crash-is-no-store-or-the-complete-empty-log`),
never a partial one. Before writing anything `init` looks for a staged
directory an earlier `init` left, and ACL2 answers
(`fn-bs-init-pub-admission` over `fn-bs-imp-classify`):

- `init refused reason=interrupted-init stage=PATH` (exit 1): ROOT is absent,
  so no store was published. Remove PATH and run `init` again.
- `init refused reason=publication-uncertain stage=PATH` (exit 1): ROOT is
  present as well; run `recover`, then remove PATH.
- `init refused reason=store-path-exists` (exit 1): ROOT exists (an empty
  directory, say) without the store's entries. `init` creates the store
  directory itself and never fills or replaces an existing one: remove it or
  name another path.

An OS error before the rename is a known failure (1, `init failed before
publication: ...; remove PATH`); at or after it the outcome is uncertain (3,
`init publication uncertain state=STATE stage=PATH root=ROOT`).

The converse is refused too, with its own code. Every verb that opens the
store (`run`, `post`, `status`, `pins`, `obligations`, `health`, `recover`,
`store ...`, `group`, `capacity`, `peer`, `policy`, `bp-boundary`,
`bp-route`, `retention`, `control`, `principal`) first looks for the same
five entries, by `lstat` alone. With none of them there is no store here: the
node was never initialized (or `[store] path` names the wrong directory), and
the answer is **`refused` with exit 1**, the code of every known refusal, and
the line

```
no store at the configured [store] path: this node was never initialized; run: fn operator CONFIG init GROUP... (a mission's fn.toml: init with no group)
refused operator status NO-STORE
```

never a fault (4); the word `NO-STORE` and the `run:` line, not the code,
tell it from another refusal. ACL2 decides it (`fn-native-operator-store-outcome`,
`fn-native-operator-absent-store-is-refused`, books/native-operator.lisp);
a store with some of its entries is not "no store" and goes to the open,
which recovers or refuses it (an interrupted `init` of this release leaves
no such store: see above).

**Init under a mission.** A `fn.toml` written by `mission NAME` carries
`[ops] mission`, and the mission fixes the store profile: `init` then takes
GROUP words only, and with none a small community serves `local.general`
and `local.test` (relay and archive have no default groups and need them).
A profile flag or `--profile` there is a usage error (5) whose first line
says so:

```
under [ops] mission, init takes GROUP words only (none: the mission's default groups); the mission fixes the store profile. To raise a bound later: fn operator CONFIG store export DIR, reinstall, then fn operator CONFIG store import DIR --FIELD N; or delete the mission line from fn.toml to choose a profile at init
usage operator init MISSION-FIXES-PROFILE
```

Every usage error prints ACL2's line for what the command accepts before its
result line, so `init` with a stray word shows the full `init` grammar.

**Store profile (M5, D27).** The store profile is the operator's: every
bound on the data a store holds is a field `init` writes into `config.json`
(format `fn-store-9`, `books/byte-store-frame.lisp`, the one store format:
D34; a `fn-store-8` profile, the retired per-file layout, is refused at the
open by name, STO-028) and nothing
rewrites in place; a different profile is a reinstall and an
import. ACL2 fixes the relations between the fields
(`fn-bs-profile-validp`) and the codec ceilings no field may pass, not the
values.

| field (flag `--NAME N`) | bounds | default at `init` |
| --- | --- | --- |
| `max-transactions` (T) | committed transactions | 4,294,967,295 (the u32 txid width) |
| `max-history-octets` (H) | total committed record octets | 1 TiB |
| `max-record-octets` (R) | one encoded Store event | 67,108,864 (64 MiB; at least 196,608, the worst-case Store event) |
| `max-article-octets` (A) | one article's payload | 16,777,216 (16 MiB) |
| `max-groups-per-article` (G) | newsgroups on one article | 4,096 |
| `max-group-name-octets` | one group name (validated, not yet enforced on `group create`: PKT-435) | 256 (the record codec's and the configuration label's width today) |
| `max-open-suffix` (K) | records replayed after the checkpoint | 65,536 (lowered with T) |
| `max-consumers` | consumers registered; the next `consumer register` past it is refused | 1,048,576 |
| `max-config-generations` | configuration generations ever published | 1,048,576 |
| `max-credentials` | AUTHINFO logins in `auth.toml` | 1,048,576 |
| `max-bp-rows`, `max-policy-members` | reserved: validated (`1..2^32-1`) and read by nothing; the BP rows are the journal's (PKT-296), and 64 policy members is statement schema v1's grammar limit (PKT-229) | 1,048,576 each |

The D27 defaults are 64 MiB records, 16 MiB articles, 4096 groups and
460-octet names; each default is capped at the codec ceiling the tree carries
today, and rises when that ceiling does (packet P2). The relations, each
reported by name when it fails (exit 1, nothing written): `1 <= T <= 2^32-1`;
`R <= H`; R at least the worst-case record of every Store event kind (today
exactly 196,608: the accepted-statement kind's ceiling equals the codec's);
R, A, G and the name bound within their codec ceilings; R at most 4,294,966,940 octets, the largest Store event the consumer poll reply can carry (the Store frame's u32 less the reply's 9 header and 346 cursor octets), refused past it as `max-record-octets-above-the-poll-reply` (PKT-467);
`1 <= K <= T`; each namespace count in `1..2^32-1`.

```text
fn operator /path/to/fn.toml init --max-transactions 100000 --max-history-octets 268435456 --max-article-octets 20000 fn.letters
fn operator /path/to/fn.toml init --profile development fn.letters   # 128 transactions, 24 MiB
fn operator /path/to/fn.toml init --profile scale fn.letters         # 4096 transactions, 768 MiB
```

`--profile development|scale|default` names a base (the first two are the
pre-D27 presets, kept so existing stores and tests keep their witnesses);
flags override its fields. `status` prints the profile the store runs under
and the headroom against it:

```text
profile format=9 max-transactions=100000 max-history-octets=1099511627776 max-record-octets=196608 max-article-octets=20000 ...
headroom transactions-used=7 transactions-budget=100000 bytes-used=1834 history-bound=1099511627776 charge-reserved=... charge-capacity=...
```

**The process heap (PKT-016, HST-013).** The installed `bin/fn` gives the
node the heap its store profile needs on this machine, and refuses a profile
the machine cannot hold before anything runs (exit 1, on stderr
`fn: refused machine-cannot-hold-profile heap=MB MB machine=M MB`). The
figure is ACL2's (`fn-heap-decide`, books/heap-figure.lisp and
books/heap-store-figure.lisp): the image's dynamic content, the state of the
profile's largest store (its payloads in the paged arena, one octet each; 12
KiB a record and 320 octets a group membership, twice for the collector:
the measured live state of per-record-state and catalog-columns), the open's
transient (the open streams one entry and one 1 MiB chunk at a time: no copy
of the history), the record and header in flight, two checkpoint buffers of
three times H, and the collector's room at the trigger the host sets; the
machine is the least of its physical memory, the cgroup's `memory.max`
(Linux) and the data-size limit (`ulimit -d`; OpenBSD's login class).
`status` and `health` end with the reservation the launcher makes for the
store's next `run` over the store on disk (`fn-heap-status-decide`, the same
decision as the launcher's probe): `heap=MB MB profile=WORD machine=M MB
stack=KB KB threads=N`. The thread stacks are added by
books/heap-reservation.lisp (30 threads: 12 fixed, 2 I/O loops, 16 control
clients; a connection is no thread since connection-multiplexing). The
installed launcher ignores the caller's `SBCL_USER_ARGS` and
`FN_TEST_HEAP_MB`; a checkout's `packaging/fn` takes the tests'
`FN_TEST_HEAP_MB`. The presets' full-store figures on a 389 MB core:

| preset | T | H | R | A | G | K | heap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| small | 16,384 | 8 MiB | 196,608 | 32,768 | 16 | 128 | 1,232 MB: fits 1,536 MiB (OpenBSD's default datasize) and a 2 GB machine |
| development | 128 | 24 MiB | 17,138,486 | 32,768 | 65,535 | 128 | 7,506 MB: refused on a 2 GB machine |
| scale | 4,096 | 768 MiB | 17,138,486 | 32,768 | 65,535 | 4,096 | 173,021 MB |
| default | 2^32-1 | 1 TiB | 64 MiB | 16 MiB | 4,096 | 65,536 | about 10 PiB: refused on every machine (PKT-582) |

The development and scale figures are their group memberships: a record may
be posted to G = 65,535 groups and nothing else bounds a store's
memberships, so the state is 2 x T x 320 x G octets (scale at T = 1,048,576:
about 40 TiB). A node sized for many records names
`--max-groups-per-article` (16 in the small preset).

`init` with no `--profile` and no capacity field (and every `init` under a
`mission`, which fixes the profile) takes the largest friend-sized rung the
machine's budget holds (books/heap-reservation.lisp `fn-heap-init-decide`
over `fn-heap-friend-candidate`, PKT-707, decided 2026-09-27): the
development base with H = 64, 32 or 16 MiB, one transaction slot per 512
octets of history (T = H / 512), R raised to what the article bound needs;
else the floor, H = 8 MiB with 16,384 transactions (the small preset). A
short post with its headers is a record of about 860 octets and its one
group membership is charged 320 more (books/store-budget.lisp
`*fn-sbud-membership-octets*`, lane membership-budget), so the floor holds
about 7,100 such posts and the top rung about 56,800; a friend's feed
spends the same history. Every rung and preset is judged by its FULL store's
run (`fn-heap-reserve-full-store-decide`: the state at H and T and a replay
of all of it), so a store init admitted always reopens on the same machine
(`fn-heap-init-accepted-store-always-reopens`). `init` prints its decision
(`init: profile=custom sizing=... reservation=MB MB budget=MB MB
within-budget=yes`) and `status` prints `profile=custom`. A request naming
T, H or R, or `--profile development|scale`, is written as named and never
resized when the budget holds it; past the budget it is refused
`init-budget-cannot-hold-profile` with both figures (exit 1,
`fn-heap-init-decide-refuses-the-operators-request-past-the-budget`),
unless FN_INIT_BUDGET_MB names a target budget that holds it: then it is
written with `within-budget=no target-budget=MB MB`. A named budget below
the budget init observes without it (init run outside the service's
memory limit) is written for the named budget and warned on stderr by name
with both figures (`fn-heap-init-budget-note`, keystone
`fn-heap-init-budget-note-names-the-budget-init-sized-for`; finding R1 of
the public-node rehearsal). The
small preset has no `--profile` word (PKT-581); name its fields:
`--max-transactions 16384 --max-history-octets 8388608 --max-record-octets
196608 --max-article-octets 32768 --max-groups-per-article 16
--max-open-suffix 128`. A native test node that must hold more than
1,024 articles inside a 24 GiB test scope: `--max-transactions 20000
--max-history-octets 67108864` (reservation 8,579 MB at ea2cc5121); naming
T alone keeps the default H and R, whose full store asks 11,542,339 MB and
is refused (planning/evidence/init-reservation-2026-09-28.md has the table,
and the synthesized fixtures' profiles). A store's bounds rise only through `store export`
and `store import --FIELD N`; each command's launcher re-sizes the heap from
the store it opens, and refuses by name one whose replay the machine cannot
hold.

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
(the log's replay is bounded by T and H)
before any configuration record is read. Raising it is a reinstall (D34, fresh
deploys): export the store, remove it, and import the archive with the raised
field:

```text
fn operator /path/to/fn.toml store export /srv/fn-archive
exported records=7 configuration=1
# stop the unit, remove the store directory, install the release
fn operator /path/to/fn.toml store import /srv/fn-archive --max-transactions 1000000
imported records=7 configuration=1
```

`store export` is a Store-history export, not a node backup. It carries the
profile, the frontier (on format 9 the txid frontier the log derives), the
configuration records and the Store records (the checkpoint's records, then
the log's: the history the open recovers), and nothing else: not the node's private state and secrets (the TLS
keys, credentials, the HKDF and pseudonym roots), not peer journals, not
consumer or application state held outside the Store, and not the other
persistence domains (the BP and TCPCL stores). The MANIFEST's SHA-256 per
entry says each file is the one the export wrote; it does not establish that
the archive is the newest history of that node.

`store export DIR` takes the store's writer lock, so it is refused (1, `store
is already locked`) while an owner runs; DIR must not exist (`export refused
reason=archive-exists`). The archive is a directory: `profile` (config.json's
exact octets), `frontier`, `config/NAME` (each configuration record's
octets), `records/NAME` (each committed record's octets, in sequence
order) and `MANIFEST` (one `sha256  name` line per file, `sha256sum
-c` reads it); ACL2 renders every name and the MANIFEST
(`books/store-export.lisp`). `store import DIR [--FIELD N ...]` makes a NEW
store: the configured store must not exist (`import refused
reason=store-exists`); ACL2's plan (`fn-sxp-import-plan`) refuses a MANIFEST
that does not match (`reason=manifest-mismatch NAME`), a record out of
sequence (`reason=record-out-of-sequence N`) and a profile the codec cannot
represent (`reason=profile REASON`), each exit 1 with nothing written.

The import then publishes the store in the order of the byte program
`fn-bs-imp-program` (`books/store-import-publication.lisp`): it stages the
store in a new directory `ROOT.import-XXXX` beside the configured store ROOT
(each file created exclusively, written and fenced, then the subdirectories
and the staged directory fenced; the store is always written as format 9,
whatever format word the archive's profile carries (`fn-sxp-log-profile`),
its records appended to `journal/000001.log` through the log's own take,
append and barrier, so an archive the previous release exported from a
format-8 store imports as a format-9 store with the same history: the
migration across a reinstall), opens the staged store the ordinary way
(full replay), renames it onto ROOT with a rename that never replaces an
existing ROOT (`renameat2` with `RENAME_NOREPLACE` on Linux; on OpenBSD, which
has no such rename, see below), and fences ROOT's parent directory.

**On OpenBSD** (no `renameat2`), `store import` and `init` hold an exclusive
advisory lock (`flock`) on the sibling file `ROOT.lock` for the whole
program, and re-check under it, immediately before `rename(2)`, that ROOT is
absent; `rename(2)` itself refuses a non-empty directory or a file at ROOT.
A second fn import or init of the same ROOT is refused while the lock is
held (1, `publication refused reason=publication-locked`). The residual
window is a process that does not take the lock creating an EMPTY directory
at ROOT between that check and the rename: `rename(2)` would replace it. So
on OpenBSD, **nothing but fn may create ROOT**: do not pre-create the store
directory, and do not run another tool that makes it. `ROOT.lock` stays
beside ROOT (removing it could race a second process that already opened
it); it holds no data. A ROOT that appears before the rename is refused
(1, `import refused reason=store-exists stage=PATH`) and the staged
directory PATH is left for you to remove. An OS error before the rename is a
known failure (1, `import failed before publication: ...; remove PATH`); at
or after the rename the outcome is uncertain (3, `import publication
uncertain state=STATE stage=PATH root=ROOT`).

Before writing anything, the import looks beside ROOT for a staged directory
an earlier import left (killed, or failed), and ACL2 classifies what it finds
(`fn-bs-imp-classify`, from whether the staged directory and ROOT are
present):

- `import refused reason=interrupted-import stage=PATH` (exit 1): ROOT is
  absent, so no store was published. Remove PATH and import again.
- `import refused reason=publication-uncertain stage=PATH` (exit 1): ROOT is
  present as well. Never read this as "no store was created": run `recover`
  on the configured store, then remove PATH.

Fields only matter
upward in practice (the records were committed under the old bounds, and the
import's open refuses a history the new profile cannot hold). The retention
charge capacity is a different number and IS reconfigurable
(`capacity DECIMAL-UINT32`). A repeated field or a
value that is not a decimal below 2^64 is a usage error (5). A store saved before PKT-467 with R above 4,294,966,940 is refused by name at every open (1, `open refused reason=max-record-octets-above-the-poll-reply: ... reinstall from the release and import`), and a store of any other format (a format-8 store of the per-file layout, which every store made before 2026-09-27 is; a format-7 store; JSON metadata) likewise (`open refused reason=store-format: reinstall from the release and import`; books/store-profile-open.lisp `fn-spo-config-open`). A sealed profile of another field width (the run of u64 fields grew from 13 to 16 with header-limits-profile) is refused `open refused reason=older-release: store made by an older release (profile layout 13 fields, this release expects 16): export it with the release that made it, then import it here` (`newer-release` above 16; planning/evidence/fixtures-refresh-2026-09-27.md). Nothing is translated or repaired in place: export with the release that made the store, import with this one.

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

Compaction is the other offline store step. On the record log (format 9,
the one format) it is a state checkpoint that rotates the log, followed by
the drop of the segments that checkpoint covers
(`fnn-command-compact`, host/native/checkpoint.lisp;
`fnn-state-checkpoint-publish-steps`, host/native/io.lisp):

```text
fn operator /path/to/fn.toml store compact
compacted steps=checkpoint,drop records=N checkpoint sequence=... octets=... steps=... segment=K dropped=D open=...
```

It opens the store as `recover` does, so it is refused (1, `store is already
locked`) while an owner runs. The order: with no batch open, rotate the log
(`fnn-log-rotate`: a new segment `journal/NNNNNN.log`, preallocated,
fenced, then `journal/` fenced; cuts `rotate-created`, `rotate-fenced`,
`rotate-durable`); write and install the checkpoint, whose F row names that
segment and the trailer its first entry chains from; then unlink every
segment below it (`fnn-log-drop`; cuts `drop-unlinked`, `drop-durable`). The
running owner's automatic checkpoint does the same under the owner mutex,
so a node that runs rarely needs the verb. The open reads the checkpoint
first and scans from the segment its F row names, with the chain carried
across segments; the drop preserves the history that open replays (KEYSTONE
`fn-lgw-segment-drop-preserves-the-open`, books/store-log-stream.lisp,
PRF-270). A checkpoint ACL2 will not write is refused by name before
anything is allocated (`checkpoint deferred reason=... estimate=...
budget=...`, the profile's checkpoint budget and the free space). The open
refuses by name, exit 1: `history-short-of-checkpoint` (a segment the
checkpoint does not cover is missing), `checkpoint-damaged`,
`log-chain-broken` (a segment that validates under another predecessor);
a writable open finishes an interrupted drop. An I/O error in the drop is
uncertain (3); rerunning `store compact` finishes it.

Compaction relieves disk and the open's work, not the budget: `transactions-used`
counts committed records and is unchanged. Measured on 40,000 articles of
2 KiB: 40 to 139 s at 4.7 GB, against 2,963 s at 16.4 GB for the format-8
pack compaction it replaced (planning/evidence/log-recovery-2026-09-27.md).

`store reclaim [--dry-run]` is content reclamation over the log
(`fnn-log-reclaim-steps`): the history is streamed one record at a time into
ACL2's fold, each released article's record rewritten to a tombstone
(STO-014's per-article decision over every holder); the rewritten history is
replayed, checkpointed with the log rotated, and the covered segments
dropped, so the released payloads leave the disk with them (KEYSTONE
`fn-lgr-decide-checkpoints-the-rewrite`, books/store-log-reclaim.lisp,
PRF-271, equated with the streamed decision the host calls by
`fn-lgr-decide-stream-is-lgr-decide`). It prints `reclaimed=N
freed-octets=F ...` and one `reclaimed MSGID` line each; `--dry-run` prints
`dry-run would-reclaim=N ...` and changes nothing; nothing to do is
`reclaimed=0`. `store checkpoint` publishes the checkpoint alone (the same
rotate and drop). `store ROOT digest` opens the store read-only (refused while an
owner runs) and prints ACL2's SHA-256 digests of the state the open folded
(`fn-store-sn-replay-digest-report`, host/store-node-host.lisp, over
books/state-digest.lisp): `history` (the records as wire events, in log
order), `pool` (the payload arena's logical value), one `field` line per
Store-node field, `config`, `canonical` (history and configuration history:
what anyone holding the log recomputes) and `state` (all of them). Two opens
of one history print the same lines, by full replay or from a checkpoint, on
any box (tests/test_native_replay_determinism.py;
planning/evidence/proto-determinism-2026-09-27.md). The per-file layout's `pack`, `pack-reclaim` and
`pack-retire` refuse by name on every store an image opens
(`... refused reason=record-log: a format-9 store has no packs`).

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
far path-identity=far.example address=192.0.2.44 port=1119 security=starttls inbound=fn.* outbound=fn.* auth=source-address:192.0.2.44 budget-octets=1048576 budget-count=16
```

A half the record does not carry is `-`. A peer given a carriage budget
(`peer budget NAME OCTETS COUNT`) ends its line with `budget-octets=` (the
budget the Store charges against: whole 4096-octet pages, so `peer budget far
1048577 16` shows 1048576) and `budget-count=`; a peer without one prints
neither, and every earlier word keeps its place. The line is rendered by ACL2
(`fn-native-admin-peer-budget-report`, books/native-admin-peer-budget.lisp) from the replayed
configuration's own peer rows. `peer list` is a read, answered like
`status`: by the running owner from the configuration it carries, or, with no
owner, from the store opened without the exclusive writer lock. It can neither
publish a configuration record nor take the lock away from the owner.

A peer's feed can be limited to distributions (RFC 5537 section 3.6: an
article whose Distribution header names none of them is not offered to that
peer):

```
fn operator /etc/fn/fn.toml peer distributions far fn,local
```

The argument is a wildmat over the article's distribution names, compared
without case; a second request replaces the first. A peer without one is fed
every distribution, an article without a Distribution header is fed to every
peer, and an article whose Distribution header is malformed is fed to no
peer that has a filter. `*,!local` feeds everything except `local`.

### Status while the owner runs

`operator CONFIG status`, `pins`, `obligations` and `peer list` print one
report, rendered by one ACL2 function (`fn-nls-report`,
books/native-live-status.lisp) whoever answers:

```
$ fn-native operator fn.toml status
transactions=12 articles=12 staging-orphans=0 unsigned-legacy-experiment
profile format=9 max-transactions=4294967295 max-history-octets=1099511627776 ... history-marker=unmarked
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
figure (a full replay of up to `max-transactions` records holding the
payloads as octet lists, 32 × `max-history-octets`), not a measurement.
`open=` says how this answering process opened the store; `checkpoint-file`
is the newest published state checkpoint's size and modification time when
the report was asked for (`checkpoint-file=absent` when there is none), and
while the owner has deferred its automatic publication the same line ends
` deferred=exceeds-budget estimate=E budget=B`: the file it would write (E
octets) is past the profile's checkpoint budget B (three times
`max-history-octets` plus one segment's framing, the bound an open refuses a
checkpoint past), nothing was written, serving continues, and the
publication is retried once the budget covers E. The owner renders a report
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
unqualified-profile held format=9 development
space-pressure clear
no-route clear
stranded-transfer clear
unavailable-peer held peers: hub
receipt-debt clear
accepted operator health
```

| exit | state | held when | what to do |
|---|---|---|---|
| 20 | `fenced` | a clone fence awaits its incarnation rollover (`reason=clone-fence`); a process holds the store's writer lock and nothing answers on the configured control socket yet (`reason=starting`: an owner recovering its store before it listens, or an offline command); a process holds the lock and no control socket is configured, or the lock could not be probed (`reason=store-held`); or the socket accepted and did not answer (`reason=owner-unanswering`) | `starting`: wait and ask again, `status` answers once the owner listens; otherwise find the process (`fuser store/writer.lock`); a clone finishes its rollover; never delete the lock |
| 21 | `exhausted` | transactions used reached the transaction-id codec ceiling (2^32 - 1), or the retention ledger's reserved charge its uint32 count | terminal for this store format: no profile raises it |
| 22 | `unqualified-profile` | the persisted profile is not valid (`fn-bs-profile-validp`), or it is the development profile. The line prints the store's format (`format=9` for the record log) | reinstall: `store export`, then `store import --FIELD N` (or `init --profile scale`) |
| 23 | `space-pressure` | free headroom below `[alerts] headroom_min_percent` (default 10) on transactions, history octets or retention charge | a reinstall with a larger field (`store export`, `store import --FIELD N`), `capacity`, or release obligations |
| 24 | `no-route` | forwarding obligations are held and the configuration has no `bp-route` | `bp-route add PATTERN BOUNDARY` |
| 25 | `stranded-transfer` | an outbound feed entry was dropped at its retry bound; nothing re-offers it | fix the peer, then re-feed the article |
| 26 | `unavailable-peer` | an outbound peer has pending articles and no open connection, or it keeps deferring them (`deferred=N`: a full peer answers IHAVE/TAKETHIS `436` with `reason=unaffordable` in its log; planning/evidence/friend-blockers-2026-09-27.md, PKT-711), or its outbound feed queue is saturated (`saturated=N`: the queue holds only undelivered articles, and while one of the post's target peers has no room every POST is refused `441 ... (feed-queue-full)` and a relayed article is answered `436`; PRF-335) | check the peer's host and port (`peer list`), its reachability, and ask its operator whether its store is full |
| 27 | `receipt-debt` | forwarding obligations are held, awaiting the receipt that releases them | `bp-obligation status`; the receipt releases each |
| 19 | (none held) | some state is `unobserved` | offline, the two feed states need a running owner |
| 0 | (healthy) | every state is `clear` | |

When the fence is held, the first line also names its reason, so an owner
that is still recovering its store reads

```
health exit=20 state=fenced reason=starting (a process holds the store lock and nothing answers on the control socket yet: an owner starting or recovering, or an offline command; retry)
```

and the same command, once the owner listens, prints the owner's own report
with no fence: `starting` is a reason of the fenced state, never a code of
its own, and it clears on the one observation that listening changes
(`fn-nh-starting-clears-on-listening`).

The scale is the one exception to the fn-wide exit table (specs/host.md, "CLI
exit codes"), and it never overlaps it: the code is 0 or at least 19, and 0
is the only code it shares, with `accepted`
(`fn-nh-exit-code-is-zero-or-past-the-outcome-codes`).

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

The running owner's report ends with its service log's line,
`log-sink pending=P dropped=N written=W`. The owner never waits on its log:
a line goes to a queue that one writer thread drains, so stderr on a pipe
nobody reads, a stalled journald or a slow disk costs lines, not service.
`pending` is what the writer has not yet written (it grows while the sink
does not drain), `dropped` counts lines lost because the backlog passed
1 MiB or a write failed, and `written` those the sink took
(books/log-sink.lisp). Under systemd stderr is the journal, which drains, so
`dropped` stays 0 unless journald stalls. The line never changes the exit
code (`fn-nh-report-exit-of-render-and-more`).

### From the release tarball

[Installing fn](install.md) is the procedure. A release is built by
`packaging/release-tarball.sh PLATFORM REV OUT_DIR` on a machine of that
platform, from a `git archive` of REV: it refuses unless every book in the
default image profile's include closure is green at its digest
(`tools/green_check.py --profile default --strict`), acquires and
load-checks the certificates from the cache, builds and freezes the
production image, stages it with `packaging/install-native.sh`, checks that
no Python is on the deployed path (`tools/runpath_check.py --tree`) and that
`bin/fn --version` prints `fn VERSION (REV12)`, and packs
`fn-VERSION-PLATFORM.tar.gz` with a `SHA256SUMS` beside it. VERSION
is the one line of the file `VERSION` at the root of the tree: the image
build reads it into the image and the packaging names the tarball by it, and
the cut tags REV `vVERSION` (planning/release-v6.6.0.md is the first cut's
checklist; `tools/cut_release.sh` runs its mechanical gates). Release order
is D37's sequence (planning/release-sequence.json, decided by
`tools/release_sequence.py`): 6.6.0 to 6.6.5, the 6.7.x series, then 6.6.6
and one more `.6` per release after it. No tool compares version numbers;
the cut's gate 01 requires VERSION to be the sequence's next entry after
the newest `v*` tag. The `--frozen`
form packages an already built image as `fn-VERSION+REV12-PLATFORM.tar.gz`,
which is not a release. The tarball holds one directory `fn/`: `install.sh`,
`bin/fn`, `libexec/fn/` (the frozen launcher, the production core,
`source-revision`, the SBCL runtime, libsodium and libfn-mldsa65; the TLS
library is the system's), `share/fn/` (the service template,
`fn.toml.example`, `docs/install.md`, `release-gate.txt` with the gate's
lines, `runpath-check.txt`) and `SHA256SUMS` over every file.

**Requirements (Linux): glibc 2.36 or later**, the system's libssl (OpenSSL
3.0 or later), x86-64, and nothing else. The glibc floor is `GLIBC_FLOOR` in
`tools/runpath_check.py`, the one place it is set: the release build's
runpath check refuses a bundled ELF object (the SBCL runtime, libsodium,
libfn-mldsa65) that needs a `GLIBC_x.y` symbol version above it, and
`tests/test_release_tarball.py` checks the tarball again. A runtime built on
a newer glibc can need newer versions (SBCL 2.6.8's binary release needs
`__isoc23_strtol@GLIBC_2.38`), so a Linux release is built with
`--runtime-from DIR`, where `packaging/floor-runtime.sh SBCL SOURCE DIR`
rebuilt the same SBCL, with its build-id, in a Debian 12 container; the
freeze refuses that runtime unless it prints the same version and starts the
image's core.

`fn operator CONFIG help VERB` prints each verb's grammar. `fn` with no
words prints the operator's usage (it is `fn operator - help`), and `fn
--version` prints `fn VERSION (REV12)`: the release version built into the
image and the first twelve digits of the source revision recorded beside its
core (`libexec/fn/source-revision`; exit 1 when the image records none).

### On OpenBSD (amd64, 7.9)

The OpenBSD tarball, fn-VERSION-openbsd-amd64.tar.gz, is the same layout built on OpenBSD 7.9
(`packaging/release-tarball.sh openbsd-amd64 FROZEN_DIR REVISION OUT_DIR`,
run in the build VM). It carries the SBCL runtime with its one non-base
library (`libzstd`), libsodium and the ML-DSA-65 library (vendored PQClean,
built with the base `cc`, clang); TLS is the base system's LibreSSL. It
needs no package: no Lisp, no Python, no OpenSSL. It is built against 7.9's
libc and LibreSSL majors, so it runs on 7.9.

Four OpenBSD rules decide where it lives, how it starts and what keeps its store:

- **W^X.** The SBCL runtime is linked `wxneeded`; OpenBSD runs it only from a
  file system mounted `wxallowed`. The default install mounts `/usr/local`
  that way (check with `mount | grep wxallowed`), so unpack under
  `/usr/local`. Elsewhere it fails at start with `Cannot allocate memory`.
- **Heap.** As on Linux, the installed launcher sizes the heap from the
  store's profile and the history on disk (the `heap --` probe, PKT-016
  above) and ignores the caller's `SBCL_USER_ARGS`. OpenBSD counts the
  reservation against the login class's `datasize` (1,536 MB for
  `default`, 4,096 MB for `daemon`, the class rc.d uses), which is one of
  the machine observations the figure takes the least of, so `init` on a
  small machine picks a smaller rung. Open finding (no packet id yet;
  planning/evidence/openbsd-release-fixes-2026-09-27.md section 1): for a
  command naming no store the figure is the whole machine, here
  RLIMIT_DATA, so under a 4 GiB datasize `bin/fn --version` died with
  `mmap: Cannot allocate memory`.
- **Working directory.** The image reads its working directory at start;
  run it from a directory its user can read (`cd /var/fn`), or it halts with
  `getcwd: Permission denied`. The rc.d script starts the node in `/var/fn`
  itself (`daemon_execdir=/var/fn` in `packaging/fn.rc.in`); only a start by
  hand needs the `cd`.
- **What a power loss keeps (durability is not guaranteed by default).**
  fn's durable reply (a `240`, an `init` or `import` that exited 0) rests on
  fsync(2), and on OpenBSD 7.9 fsync does not always mean that. What an
  operator gets, measured under power cuts
  (planning/evidence/power-loss-openbsd-2026-09-26.md):
  - *The store on FFS1 (`newfs -O 1`) on a disk without a volatile write
    cache*: durable. No acknowledged article lost or changed, no store left
    unopenable, in every cut the campaign made.
  - *The store on FFS2*, the installer's format for every partition: NOT
    durable. After a crash the boot-time `fsck` can remove files that were
    created and fsynced in the last half minute or so (their inodes lie
    past the cylinder group's initialized inode blocks, a count the kernel
    writes back later). On the per-file layout the campaign measured, the
    store's newest transactions and its allocation frontier went, and the
    node refused to open (`fault ... invalid durable allocation frontier`)
    until restored from a backup or an export. The record log (format 9,
    the one format since 2026-09-27) creates fewer files, but no OpenBSD
    power-loss campaign has run on it yet (its ext4 campaign on hbox: 250
    cuts, 0 violations, planning/evidence/kernel-concrete-2-2026-09-27.md
    section 4), so FFS1 stays the only file system for an OpenBSD store.
  - *A disk, or a hypervisor's virtual disk, with a volatile write cache*:
    NOT durable, on either format. OpenBSD's fsync never asks the disk to
    flush its cache (sd(4) enables the cache at attach), so a power loss can
    drop what fsync reported written. A VM's disk qualifies only when the
    host writes through (qemu `cache=none` or `writethrough` on a host that
    honours flushes; note OpenBSD's virtio disk still reports a write cache,
    so it is the host's setting that decides).
  `softdep` changes nothing (7.9 ignores it). fn does not detect the
  format: `statfs(2)` names both `ffs`. As root, `dumpfs /dev/rsd0X | head
  -1` prints `magic 11954 (FFS1)` or `magic 19540119 (FFS2)`. For a durable
  node, give `/var/fn` its own partition made with `newfs -O 1` before
  `init`; a store already on FFS2 moves with `store export`, a new FFS1
  partition, and `store import`.

As root, with the tarball and its sum in `/tmp`:

```sh
cd /tmp && sha256 -C SHA256SUMS fn-VERSION-openbsd-amd64.tar.gz
cd /usr/local && tar xzf /tmp/fn-VERSION-openbsd-amd64.tar.gz
cd fn && sha256 -q -c SHA256SUMS                     # every file in it
F=/usr/local/fn/bin/fn
C=/var/fn/fn.toml
useradd -d /var/fn -s /sbin/nologin -c fn-node _fn
install -d -o _fn -g _fn -m 0700 /var/fn /var/fn/tls /var/fn/log
cd /var/fn
su -s /bin/sh _fn -c "$F operator $C mission small-community --host 10.0.2.15 --port 11563"
openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 3650 \
  -subj /CN=fnbsd.friends.fn.invalid -addext subjectAltName=IP:10.0.2.15 \
  -keyout /var/fn/tls/key.pem -out /var/fn/tls/cert.pem
chown _fn:_fn /var/fn/tls/*.pem && chmod 600 /var/fn/tls/key.pem
su -s /bin/sh _fn -c "$F operator $C init"
su -s /bin/sh _fn -c "$F operator $C policy set path-identity fnbsd.friends.fn.invalid"
su -s /bin/sh _fn -c "$F operator $C principal set-password ember --posting"
sed -e 's|@PREFIX@|/usr/local/fn|g' -e 's|@NODE@|/var/fn|g' -e 's|@USER@|_fn|g' \
  /usr/local/fn/share/fn/rc.d/fn.rc.in > /etc/rc.d/fn && chmod 0555 /etc/rc.d/fn
rcctl enable fn && rcctl start fn
```

The base `openssl` is LibreSSL's and makes the EC pair as shown. The rc.d
script (`packaging/fn.rc.in`, rendered with the release path) runs
`bin/fn operator /var/fn/fn.toml run` as `_fn` from `/var/fn`, in the
background, logging through syslog (`daemon.info`); `rcctl check fn` finds
the SBCL process by its `--fn operator /var/fn/fn.toml run` arguments. A link
to `bin/fn` (say `/usr/local/bin/fn`) works: the launcher follows it back
into the release.

Measured on a QEMU guest with 1 CPU and 2 GB of memory, 7.9 with no
packages (planning/evidence/release-openbsd-2026-09-26.md): the node starts
under rc.d, answers STARTTLS over LibreSSL (TLS 1.3), logs in, accepts a
post and serves it on a fresh connection to a Linux client; `peer keygen`,
`peer accept` of a Linux node's invitation and the Linux node's `peer
confirm` of the acceptance succeed. Resident size 37 MB at start and 90 MB
after 100 posts, with the then-fixed 1,024 MB reservation (the launcher now
sizes the heap from the profile). The smallest heap that served a post and
a read on a fresh development-profile node was 288 MB; 256 MB refused at
start (`dynamic space too small for core: 272320KiB required`) and 280 MB
started but died in the first session. That measurement was of a format-8
image (2026-09-26).

Release building for OpenBSD (planning/evidence/openbsd-release-fixes-2026-09-27.md):
`tools/runpath_check.py --tree` applies the target platform's rules
(`--platform linux|openbsd`, else the runtime's program interpreter), and
the libsodium and TLS candidate lists are chosen at read time, so an
OpenBSD core carries only OpenBSD's names (PKT-723); `init` and `import`
draw their stage suffix per process from the OS's entropy, so two runs of a
saved image no longer stage under the same `ROOT.init-XXXX` (PKT-819). The
gated OpenBSD rehearsal tarball of d663400f3 (VERSION then read 6.7.0,
before D37 made 6.6.0 the first release) was built this way.

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
the image and execs it with every argument, deciding nothing. An installed
`bin/fn` (a `libexec/fn/` beside its `bin/`) always runs its own release's
`libexec/fn/fn-host` and ignores `FN_NATIVE_HOST`, so an old release's
`bin/fn` runs the old image in any shell; a checkout's `packaging/fn` runs
`FN_NATIVE_HOST` when set (the tests' override), else the checkout's
`build/fn-host`. `fn operator CONFIG VERB ...` is the operator, `fn bp-node ...` and
the other image verbs are as below. The spike's bash `fn` wrapper made its
own decisions; each is now the image's (its header lists where each went:
`mission`, `health`, `show`, the
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
| `FN_NATIVE_POST_FAULT` | `CUT:eio\|kill`, CUT one of `+fnn-post-model-cuts+`; or `record-prepublish:refuse` | the frontier, record and finish cuts of a post, in `store ROOT post` and in the served owner (`operator CONFIG run`, and the developer `owner run`); `record-prepublish:refuse` is injection only (no process-death cut): every publication (`fnn-publish`, either route) is refused before its first write, which the owner resolves by ACL2's known abort (tests/test_native_known_abort.py) |
| `FN_NATIVE_RECOVERY_FAULT` | `CUT:eio\|kill`, CUT one of `recover-replayed`, `recover-barrier` (the first of its five sites), `recovery-stage-unlinked` | recovery's cuts, in `store ROOT recover`, `operator CONFIG recover`, `store ROOT post` and the served owner's own recovery at start |
| `FN_NATIVE_INIT_FAULT` | `CUT:eio\|kill\|eacces` | the initializer's cuts (`store ROOT init`), and `operator init`'s publication cuts `+fnn-init-publication-cuts+` (`fn-bs-init-log-program`, eio or kill) |
| `FN_NATIVE_IMPORT_FAULT` | `CUT:eio\|kill`, CUT one of `+fnn-import-model-cuts+` (a repeated cut at its first occurrence) | `store import`'s publication cuts (`fn-bs-imp-program`) |
| `FN_NATIVE_CONTROL_FAULT` | one of `prepublish`, `postpublish`, `frontierbarrier`, `recordbarrier` | the owner's store for exactly one control submission; `postpublish` is the uncertain outcome |
| `FN_NATIVE_CONTROL_TEST_STOP` | `after-submit` | a SIGSTOP of the owner from the worker that holds the reply, after the owner answered accepted, duplicate or refused and before the reply is sent; the stop is directed at that thread (`pthread_kill`), so the reply cannot leave first |
| `FN_NATIVE_AUTH_ADMIN_FAULT` | `CUT:eio\|kill` | the AUTHINFO credential writer's cuts |
| `FN_NATIVE_KEY_STATEMENT_FAULT` | `statement-committed:kill` | the cut between a key statement's commit and its key change's (books/key-statements.lisp `fn-ks-cut`) |
| `FN_NATIVE_OWNER_TEST_SIGTERM` | `after-install` | a SIGTERM between owner recovery and listen |
| `FN_NATIVE_OWNER_TEST_PAUSE_CLEANUP` | `1` | a two-second pause inside owner cleanup |
| `FN_NATIVE_OWNER_TEST_PAUSE_BEFORE_LISTEN` | any value | the owner holds the recovered Store and waits for SIGTERM before its control socket and listener start (`health` reads `starting`) |
| `FN_NATIVE_OWNER_TEST_BARRIER_MS` | decimal milliseconds | a sleep before each batch's barrier (`fnn-owner-commit-sync`), holding a batch in flight for the scheduler's native cases |
| `FN_NATIVE_TEST_DISK_STALL_FILE` | a path | while the file exists each batch's barrier waits before its fdatasync (`fnn-owner-commit-sync`): a stalled device for the slow-disk native case; removing the file is the device coming back |
| `FN_NATIVE_OWNER_TEST_PIPELINE_TRACE` | any value | one stderr line per START (`start: seal=S bmax=N members=K`) and per batch prepared behind a barrier (`pipeline: K members prepared behind the barrier`) |
| `FN_NATIVE_FAULT_BACKTRACE` | any value | a diagnostic, not a fault: a serious condition other than a store error inside an owner action (`fnn-owner-shared-action-locked`) prints `fault backtrace: CONDITION` and 80 frames to stderr where it is signalled, before the handler unwinds it into exit 4; a control-stack exhaustion on any thread prints `fault backtrace (thread NAME): control stack exhausted` and every frame as run-length rows `frames FUNCTION xDEPTH`, innermost first (a per-line recursion is one deep row; the rows under it are its callers) |
| `FN_NATIVE_COUNT_LOOKUPS` | any value | a diagnostic, not a fault (release row F2): the catalog and index lookup functions of `+fnn-lookup-functions+` (host/native/io.lisp: the pinned view's bisection probes `fn-scr-mid`, the catalog tables `fn-cat$c-*`, the finders `fn-cnx-view-seq` and `fn-cat-view-last-visible`, the trie `fn-midx-lookup`, and the entries of every archive walk) are wrapped with counters at startup, and each served read (`fn-owner-chunk-span`) first prints `lookups window K: NAME=N ...` to stderr, the counts of the read before it; `planning/evidence/fundamentals-2026-09-27/harness/f2_lookups.py` reads them per command |
| `FN_NATIVE_IMPORT_COMPRESS_MIN_TEST` | N | `store ROOT import` appends the archive's records through the compressed append at threshold N (books/payload-lz-append.lisp: ACL2 plans, the LZ4 encoder offers a candidate, the proved decoder checks it) instead of as they are; tools/fixtures.py's compressed fixtures |
| `store ROOT post ... FAULT ...` | one of the four `+fnn-cli-faults+` names | the same four store faults as `FN_NATIVE_CONTROL_FAULT`, for one `store post` |

`FN_NATIVE_FAULT_BACKTRACE` changes no outcome: the fence, the exit code and
the reply are the ones the image gives without it. It exists because the
handler that turns a memory fault into exit 4 has already unwound the stack
when it runs, so the log names only the condition (`Unhandled memory fault at
#x0`). With the selector the first frames name the function that faulted
(2026-09-27: frame 0 `FNN-OWNER-COMMIT-STEP-ACTION`, a stale `(first ...)` of a
keyword, found in one run). Reproduce a production fault on the developer
image of the same source revision with it set.

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
refuses with exit 1 if a live writer holds the Store lock. While an owner
runs, `operator CONFIG obligations` opens with the same two figures
(`obligations=N reserved=B`), computed by the same ACL2 functions over the
Store the owner carries.

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

## Storage requirements

A `240` is exactly as durable as the store's file system makes fsync. fn
counts an article accepted only once its records are fsynced
(`fn-assume-physical-crash` in `books/assumptions.lisp` is that obligation on
the platform), so the store's file system must honour fsync with write
barriers on:

- ext4 with its default barriers; never `barrier=0` or `nobarrier`.
- ZFS with `sync=standard`; never `sync=disabled`.
- No volatile write cache that ignores flushes, unless the drive has
  power-loss protection; no tmpfs for a store whose acceptance matters.

The power-loss campaign (`planning/evidence/power-loss-2026-09-26.md`) found
no acknowledged POST lost at any of 1,281 cuts on ext4 with barriers on; with
`barrier=0` acknowledged POSTs were lost at 36 of 40 cuts, and the file
system was unmountable or unreadable at the other 4.

What fn observes of this, and what it does (PKT-648; specs/storage.md, "The
store's filesystem"):

- The owner's start, `status` and `health` print a warning naming the
  filesystem when the store's mount has `nobarrier` or `barrier=0`, or is
  tmpfs or ramfs. ZFS `sync=disabled` and a drive's volatile cache are not
  visible to fn; they stay the operator's to check.
- The store's setting `storage-require-durable` turns that warning into a
  refusal of the owner's start (`start refused: store filesystem ... this
  store requires durable storage (storage-require-durable)`). `init` turns it
  on for a store made under a mission's configuration (the release and the
  public node) and off otherwise (tests and benchmarks run on tmpfs on
  purpose). Change it with `fn operator CONFIG store rebind-filesystem
  --storage-require-durable on` (or `off`, accepting the risk).

### The node volume

Put the store on its own provisioned volume, mounted at boot. `init` records
the identity of the filesystem the store is on (its id, type, mount point
and device), and every open checks it: when the volume is not mounted, the
store path lands on the filesystem underneath, and the open is refused by
name instead of serving or starting another history there:

```
store filesystem changed: expected ext4 at /srv/fn-public from /dev/nvme1n1p1 (fsid ...), found ext4 at / from /dev/nvme0n1p4 (fsid ...); mount the node volume or run `store rebind-filesystem` after moving the store deliberately
```

The comparison is ACL2's (books/store-mount-identity.lisp
`fn-smid-same-filesystemp`, called on every open and at the owner's start by
host/native/io.lisp `fnn-check-filesystem-identity`): type and fsid where
both fsids are reported, the mount point and source only where an fsid is
not (OpenBSD reports zeros). So the shipped systemd unit
(`ProtectSystem=strict`, `ReadWritePaths=/var/lib/fn`), whose namespace
bind-mounts `/var/lib/fn` onto itself and shows a mount point `init` never
saw, starts on the store `init` made with no rebind (PKT-820; the stranger
rehearsal's first stop, fixed and rerun on Debian 12:
planning/evidence/friend-blockers-2026-09-27.md).

An empty directory where the volume should be is refused as `store
filesystem unrecorded`. After a deliberate move (another volume, a restored
backup, a copy to another machine) record the new place:

```
fn operator /etc/fn/fn.toml store rebind-filesystem
```

It takes the writer lock (a running owner refuses it), keeps the store's
`storage-require-durable` setting unless you give one, and prints what it
recorded and what it replaced.

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
`init` seeds them once, and `fn operator CONFIG group create NAME` (or `group retire NAME`)
changes them afterwards, live or offline. Each group's creation time is
its creating record's stamp, which NEWGROUPS and LIST ACTIVE.TIMES report
(a store initialized before 2026-09-27 has none for its initial groups).
The list a new reader is offered by LIST SUBSCRIPTIONS (RFC 6048 section
2.6; slrn's first run reads it) is set in order, and cleared with no names:

```text
fn operator /etc/fn/fn.toml group subscribe-default fn.announce fn.test
```

With none set, LIST SUBSCRIPTIONS lists every group the reader may read.
The configuration file holds only what the host needs in order to start.

A peer this node pulls by NEWNEWS (RFC 3977 section 7.4) gets an interval,
and optionally how many consecutive complete rounds an article the peer
lists but cannot produce holds the pull cursor:

```text
fn-native --fn operator /etc/fn/fn.toml peer pull peer1 60 5
```

The words are NAME, SECONDS and, optionally, ROUNDS. `SECONDS` 0 stops pulling. `ROUNDS` (positive; 5 when left out) is PRF-165's
bound: a 430 to `ARTICLE` is an answer, the round goes on with the other
articles, and the owner log line of each round says what happened:
`pull peer=NAME round=done cursor=held unavailable=1` while the peer's
missing article holds the instant, then `cursor=advanced unavailable=1
dropped=<id>` in the round its count reaches `ROUNDS`. A round that failed
(`round=failed`) changes no count. The counts live in the store's `pull/`
journal (FNPL); an image older than PRF-165 refuses a journal that holds one
(PKT-432).

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

`[listener] host` is one address or a comma-separated list of them: IPv4
dotted quads, IPv6 literals (`::1`, `2001:db8::7`, or bracketed `[::1]`) and
the name `localhost`. The owner binds each on `port` (and on `tls_port` when
set), so `host = "[::1], 192.0.2.7"` serves both families. ACL2 parses every
literal and supplies the exact bind address; the host does not resolve or
reinterpret it. The wildcards `0.0.0.0` and `::` stay refused so an operator
names each interface placed in service, and an IPv4-mapped `::ffff:a.b.c.d`
is refused in favour of the IPv4 address. A refusal names the reason:
`listener-address`, `listener-unspecified`, `listener-mapped` or
`listener-duplicate` (specs/nntp.md "Listener addresses", NNT-041). A
changed `host` takes effect when the node restarts.

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
`[log] path`, add the new location there or the service cannot write. The
namespace this makes (a bind mount of `/var/lib/fn` onto itself) does not
trip the store's filesystem check, which compares type and fsid
([The node volume](#the-node-volume); PKT-820).
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

### Without root: a user service

A machine where you have no root runs the release the same way under your
own account: `sh fn/install.sh --prefix $HOME/fn --node $HOME/fn-node
--no-service` installs it and writes the rendered unit into the node
directory; `systemd-run --user --unit fn -p MemoryMax=8G $HOME/fn/bin/fn
operator $HOME/fn-node/fn.toml run` runs it supervised by your user
manager. `loginctl enable-linger <user>` (an administrator's command) keeps
a user service alive after the last session closes.

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

For a person, the same node in a browser: the node's own web face, a
`[web]` table in `fn.toml` ([Read it in your browser](web.md);
[its threat model](#the-friends-web-reader)). Each browser session is a
reader connection of the node, under the same login, `protected_only` and
exposure rules as an NNTP reader's.

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

ARTICLE and HEAD of an article this node numbers carry this node's `Xref:`
as the first header line, generated at serve time (it leads the header
block, as the injected Path does, so the stored octets, a signed source
among them, stay a suffix of what ARTICLE serves; books/nntp-reader-compat.lisp
`fn-rcompat-served-payload`, batch AR); HDR and XHDR Xref answer its value,
and a relayed article's own Xref is deleted on receipt. A test comparing
served bytes to stored ones drops that one leading line.

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
| `accepted` | 0 | Done, or already so (`DUPLICATE`: the node holds exactly this article). The decision is durable. |
| `refused` | 1 | The node refused it for the reason it names, and nothing was accepted: `CONFLICT` (a different article holds this Message-ID; post under a new one, or resend the saved bytes), `NO-STORE` (run `init`), a bound, a lock. A refusal the running owner decided carries its reason word after the status: `refused operator post REFUSED unknown-group` (a newsgroup this node does not serve), `REFUSED from-invalid` (a From with no address), `refused operator control REFUSED no-such-grant` (a revoke of a grant that is not there); `NONE` never appears, a refusal with no named reason prints the status alone. Fix what the reason names. |
| `uncertain` | 3 | Whether it is durable is not known: this node's Store must recover before anything else changes. See below. |
| `fault` | 4 | The host could not carry out the operation. |
| `usage` | 5 | The command line or the configuration file is wrong. |
| `interrupted` | 6 | (BP verbs) A connection was lost after it existed; the job is kept and re-offered under its own identity. No recovery. |
| `not-connected` | 7 | (BP verbs) No connection was made; nothing left the node and the job stays queued. |

This is the one table for every native `fn` command (specs/host.md "CLI exit
codes", HST-009): a number means the same class whatever the verb, and the
reason is the word on the line, never a code of its own. `health` is the one
exception: it exits with its verdict (below), 0 or 19 to 27.

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

Restart the service after changing the policy or a password in the
credential file: both are read once at start-up. A login's `signing` binding
is the exception (next section): `principal bind` and `unbind` apply to the
running node at once.

### Renew the certificate without a restart: `tls reload`

The owner reads `tls_cert` and `tls_key` at `run`. When a renewal (the
Let's Encrypt hook, `tools/runbooks/public-node/acme/fn-cert-install.sh`)
has replaced the two files, ask the running node to take them:

```
packaging/fn-native operator /etc/fn/fn.toml tls reload
```

The owner builds a new context from the same two paths and serves it to
every connection that starts after the command returns; a session already
open keeps the certificate it handshook with until it ends. ACL2 decides
whether to take the new pair (books/tls-reload.lisp `fn-tlsr-decide`,
PRF-212) from what the TLS library observed: it is taken exactly when the
chain and the key load, the key matches the chain's leaf, the host clock
lies between the leaf's notBefore and notAfter, its subjectAltName is
readable, and every DNS name the served certificate names is still named.
The command prints the line of the certificate now served and exits 0; the
service log says `tls reload accepted: tls names=... not-after=...`.
Otherwise it is refused by name (exit 1, `refused operator tls REASON`) and
the old certificate is still served: `chain-unreadable`, `key-unreadable`
(an encrypted key is refused here, as at `run`), `key-mismatch`,
`validity-malformed`, `not-yet-valid`, `expired`, `names-malformed`, or
`names-dropped`. A certificate for a different set of names is a restart,
not a reload: a peer that verifies this node by a name would fail its next
handshake. Without a running owner the command reaches no one and exits
non-zero.

`status` against a running owner prints one more line after its report,
the served certificate's names and notAfter (UTC):

```
tls names=fn.fg-goose.online not-after=2026-12-25T22:23:43Z
```

`tls names=none` is a leaf without DNS names (a CN-only self-signed
certificate), `tls none` a node without `tls_cert`, and `tls unknown
REASON` an owner that did not answer the question (an owner older than
this command answers `owner-lacks-tls-reload`).
### What a login's post discloses: Injection-Info's posting-account

Every article a login posts is stored with one line

```
Injection-Info: news.example.org; posting-account="8c59...f172"; mail-complaints-to="abuse@example.org"
```

(RFC 5536 §3.2.8). The `posting-account` value is 64 hex digits derived
from the login under the node secret (`STORE/keys/node-secret.key`). It is
a **linkable pseudonym**, not anonymity, and it travels with the article to
every peer and reader: anyone can see that two articles with one value came
from one login on this node. Nobody without the node secret can read the
login out of it, or its length, or test a guessed login. By enabling
authenticated posting the operator authorizes that disclosure; tell the
people you give logins to. An anonymous post (where the node allows one)
carries no `posting-account`. A new node secret gives every login a new
value; a login name you reuse for another person carries the old value.

The complaints address is a policy, set live:

```
packaging/fn-native operator /etc/fn/fn.toml policy set complaints-to abuse@example.org
```

It must be a plain `local@domain` address (dot-atoms, no quotes); anything
else is refused. To answer a complaint that quotes a `posting-account`,
compute the value for a login and compare:

```
packaging/fn-native operator /etc/fn/fn.toml account hash alice
```

It prints the value `alice`'s posts carry (it reads the node secret, with
the same permission checks as the owner; the secret itself is never
printed). Articles relayed from peers keep the peer's own `Injection-Info`
untouched. The decision is ACL2's (`books/injection-info-params.lisp`,
`specs/nntp.md` "Injection-Info parameters").

### Bind a login to its signing principal

A signed POST is `verified` for whichever principal signed it, whatever
login posted it. To make a login post only as its own principal:

```
packaging/fn-native operator /etc/fn/fn.toml principal bind alice PRINCIPAL-HEX  # 64 lowercase hex digits
packaging/fn-native operator /etc/fn/fn.toml policy set posting-policy bound-logins
```

These are the native operator's verbs (`fn-host --fn operator CONFIG ...`);
the Python `bin/fn principal` has only `new`, `list` and `set-password`. The
native operator loads the hybrid-signature library (libsodium and
`lib/libfn-mldsa65` beside the core), as the node does. A later `policy set posting-policy
open` takes effect: a policy slot holds the value set last
(`fn-cfg-set-policy-sets-the-policy`, books/config-invariants.lisp; until
2026-09-25 the first value set stayed in force).

`bind` writes a `signing` field into alice's table of `auth.toml`
(`principal list` shows `signing=HEX`; `principal unbind alice` removes it).
The node serves the binding from its configuration, not from the file: at
start it publishes the file's bindings as configuration records, and when
`bind` or `unbind` runs against a running node (the configuration names a
`[control] path`) the verb asks the owner to re-read the file and publish
the change at once (PKT-221; `books/login-binding-live.lisp`).
`principal set-password` asks the same (control request 14): the owner
rebuilds its credential table from the file with the load it ran at start
(`host/native/auth.lisp` `fnn-native-auth-reload-config`, ACL2's
`fn-native-auth-host-load`) before republishing the bindings, so a new
password is served to the next connection without a restart
(friend-path-2). The verb's
last word says which: `applied` (the running owner published it),
`effective-at-next-start` (no owner was running), `restart-required` (an
owner holds the store and did not publish it, for example no control socket
is configured), or `uncertain`. A session already authenticated keeps the
binding in force when its connection opened; the next connection is decided
under the new one. The policy is a durable configuration record, applied
live. Under it, alice's unsigned article is answered `441
posting failed; this login posts only articles signed by its bound
principal`, and one signed by another principal `441 posting failed; the
login is not bound to this signing principal`. A login without a binding,
and every login on a node whose policy is `open` (the default: `policy set
posting-policy open`), posts as before. The service log names the login of
each decision (`post login=alice bound=...`).

### Re-decide a declined key statement: `keys redecide`

A key statement (a signed succession or revocation posted to `fn.keys`) is
decided once, when the node accepts it, under the `keys` grants in force
then. One that declined (`key-statement declined no-grant` in the service
log, say, because the grant came later) stays declined across restarts: an
open re-decides nothing under later configuration (PRF-124). To decide it
again under today's grants, ask the running node:

```
packaging/fn-native operator /etc/fn/fn.toml control grant PRINCIPAL-HEX keys fn.keys
packaging/fn-native operator /etc/fn/fn.toml keys redecide <a1@example.invalid>
```

The owner decides it as a new acceptance of the stored statement under the
grants of the configuration in force at the redecide's own transaction
(books/key-statements.lisp `fn-ks-redecide-plan`, PRF-166). When it acts,
the key change (the successor's enrolment, or the revocation) is the one
durable record it writes, the service log says `key-statement redecide
enrol-successor committed`, and the command exits 0; a restart repeats
nothing. It is refused (exit 1, the Store unchanged) when the Message-ID
names no stored key statement (`key-statement redecide refused
not-a-key-statement`), when the statement's change is already made
(`refused already-acted`), or when it declines again (`key-statement
redecide declined REASON`). The verb needs the running owner: offline it is
refused, like every control verb.

### Why was an article withdrawn: `control log` and `control evidence`

A cancel, or an article whose `Supersedes` names another, is decided once,
when the node first publishes it, under the grants in force at its own
transaction. To read what was decided:

```
packaging/fn-native operator /etc/fn/fn.toml control log
packaging/fn-native operator /etc/fn/fn.toml control evidence <c1@example.invalid>
```

`control log` prints `withdrawals=N` and one line per withdrawal record the
node holds: `withdrawal target=T cause=C principal=P scope=S generation=G`,
where `scope` is the canceller's `cancel` grants when the record was decided
(`-` for none: only the author basis can apply) and `generation` the
configuration it was decided under. `control evidence MESSAGE-ID` prints
that article's first line (`stored=yes txid=N verdict=V`, or `stored=no`),
then what its own decision was: `decision=withdrawal ...` (the log's line),
`decision=declined reason=R` (for instance `unsigned`, `unverified`,
`self-target`), or `decision=none` when it names no target; then one
`withdrawn-by ... effect=E` line per record naming it as target, where `E`
is `author`, `authority`, or `declined reason=R` (`outside-namespace`,
`no-grant`, `no-groups`), and `effect=target-absent` while the target has
not arrived. With an owner running it answers from the owner's view; with
none, the offline command decides the records over the Store as recovery
does, in the same words. A Message-ID that is not one (`<...>`, printable
ASCII) is a usage error (exit 5). books/control-evidence.lisp renders every
word (PRF-185, HST-011).

## Expose a node to strangers

Everything below is what runs on the branch and what the SCN-091 campaign
measured on hbox (`planning/evidence/public-exposure-2026-09-26.md`); no fn
node is exposed yet, and whether and how one is is PKT-404. What one node sustains, and the weaker tier a disk-backed pool gives, is the measured envelope in "What one node sustains" at the end of this guide: size an exposed node's limits (`exposure-posts-per-minute`, `exposure-connections`) against it.

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
fn operator /etc/fn/fn.toml policy set exposure-trusted 192.168.1.0/24
```

What each does, what the client sees and the default off loopback is the
table in `specs/nntp.md` ("Public exposure"). In short:

- **Connections.** `exposure-connections` is the capacity: the owner holds
  exactly that many connections at once, whatever the number (up to the
  limit rows' width, 4,294,967,295), and it takes effect live. With no row
  it is 31, the figure every node ran with before. Each connection is a
  thread and its buffers, so size it to the machine (PKT-605). The
  connection your own `policy set` stages through never counts against it.
  Past the capacity a client reads `400 too many connections; try again
  later` and is closed; past the per-address limit, `400 too many
  connections from this address; try again later`.
- **Trusted range.** `exposure-trusted` names one or more address ranges
  (`192.168.1.0/24`, `fd00::/8`, comma-separated; `none` clears it) that
  the per-address limit does not apply to. Behind a home router whose NAT
  loopback hands every LAN reader the router's own address, name the LAN
  here, or those readers share one address's allowance. The capacity, the
  step budget and the failed-login limit still apply to them. Under a
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
  served steps a second. A step is one host read, of a size ACL2 decides
  (books/connection-budget.lisp `fn-cbud-step-read-octets`, lane
  input-loop-2): 512 octets under a step rate, so the rate keeps its
  meaning in octets per second (the public default 64 admits about 32 KiB a
  second per address: a 1 MiB POST takes about half a minute), and 4 KiB
  without one (loopback, or the row set to 0). Past it
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

`operator CONFIG health` prints four `exposure` lines after its eight
states: `exposure pressure held|clear` (held at nine tenths of the total or
after any refusal, wait or close in the current minute), the counts
(`admitted`, `refused-busy`, `refused-address`, `refused-auth`, `deferred`,
`idle-closed`, `auth-closed`), the limits in force, and `exposure capacity
connections=N capacity=C per-address=P trusted=RANGES`, the connections
held against the capacity, which `operator CONFIG status` also prints at the
end of its report, before the `heap=` line. They do not change the exit
code.

Before you open the port: set `[auth] required = true` and `protected_only
= true` and a TLS pair (see "Require a login"), choose the certificate
(a self-signed pair pinned by your readers, or a CA's; PKT-404 compares
them), and do not put fn behind a TCP proxy unless the proxy limits per
source itself: fn does not read the PROXY protocol, so behind a proxy every
client is the proxy's address and one abuser would use up everybody's
per-address and failed-login allowance.

## Add a group

```
fn operator /etc/fn/fn.toml group create fn.announce
```

No stop is needed. A group is a durable configuration record: with the
owner running and its `[control] path` live, the verb asks the owner, which
publishes the record as a new configuration generation at once
(`fn-native-admin-plan-deltas`, books/native-admin.lisp); with no owner
running, the verb writes it offline and `run` serves it at the next start.
`fn operator CONFIG group retire <name>` retires a name: the articles already
bound to it and its watermark are kept, and the name stops being served.
Creating a retired name again revives it with its numbering intact.

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

## Moderate a group

```
fn operator /etc/fn/fn.toml group create fn.announce.moderation
fn operator /etc/fn/fn.toml group moderate fn.announce --moderators alice,bob
fn operator /etc/fn/fn.toml group moderate fn.announce --off
```

A moderated group (RFC 5537 section 3.5.1, LIST ACTIVE status `m`) takes
local posts only through its moderators. The moderators are accounts
(`--moderators` takes their logins; `account list` shows each as
`moderator LOGIN GROUP`). A post to the group without an `Approved:` header
is answered 240 and held, not posted: the node files it in the group's
queue (`--queue QUEUE`, default `NAME.moderation`, a group you create
first) as an article of type `application/news-transmission;
usage=moderate` whose body is the post. A moderator reads the queue with
any newsreader, and approves by posting that body, with an `Approved:`
line added, while logged in as themself. An `Approved:` header from anyone
who is not a moderator of every moderated group the post names is refused
with a 441 that says so. `--submission ADDRESS` records a submission
address; `--off` ends the moderation. A relayed article in a moderated group
without `Approved:` is refused by name.

The queue is private to the moderators without further configuration: a
reader connection whose login moderates none of the groups a queue serves
(and every connection before AUTHINFO) is served a view without that group
or its articles, exactly as a group the node does not carry (the queue is
added to the login's `account access` read rule as a hidden group), and an
article filed in a queue group is never offered to a peer, whatever the
peers' feed patterns say.

To see what is waiting:

```
fn operator /etc/fn/fn.toml moderation list fn.announce
```

prints `moderation group=fn.announce queue=fn.announce.moderation held=N`
and one line per envelope in the queue, `held`, `approved` (the post's own
Message-ID is stored) or `rejected` (a withdrawal record withdraws the
envelope), with `envelope=<fn-moderate....>` and the post's `message-id=`.
It asks the running owner, or reads the store offline.

To approve or reject a held post from the operator's shell, naming the
moderator whose decision it is:

```
fn operator /etc/fn/fn.toml moderation approve '<post@example.org>' --moderator alice
fn operator /etc/fn/fn.toml moderation reject '<post@example.org>' --moderator alice --reason off-topic
```

The Message-ID is the post's or its envelope's (`<fn-moderate....>`).
`approve` posts the held article with `Approved: alice` first, exactly as
alice's approval over NNTP would (the served POST's decision under her
view). `reject` withdraws the envelope under the node's own authority (see
`article withdraw` below; the reason defaults to `rejected by the
moderator`); `moderation list` then shows it `rejected`. A login that does
not moderate the group is refused by name (`REFUSED ... not-a-moderator`,
exit 1), as is a post already approved or rejected. Both need the running
owner (the control socket); `reject` also needs `control.cancel` (below), where
its cancel, naming the envelope and the reason, is served.

### Withdrawing an article: `article withdraw`

```
fn operator /etc/fn/fn.toml article withdraw '<spam@example.net>' --reason takedown
```

withdraws a stored article from every reader view under the node's own
authority, whoever posted it and wherever it is served. The node records
the operator's decision in the configuration (`article withdraw-record`, a
row the reader never sees), then injects a cancel control article
(`Control: cancel <spam@example.net>`, Message-ID
`<fn-withdraw.spam@example.net>`), filed like every control message in
`control.cancel`, which must exist (a mission's `init` serves it,
`fn-nop-mission-init-serves-control-cancel`, PKT-708; otherwise `group
create control.cancel`; without
it the verb is refused `control-not-filed` before anything is written); a connection
opened before the cancel keeps its view until it advances, and the article
stays withdrawn after a restart. `control evidence` names such a record
`principal=node`. Nothing is deleted from the store. The reason is ASCII
text of at most 256 octets; the Message-ID must fit a configuration label
(256 octets with its `<fn-withdraw.` prefix). A second withdrawal of the
same article is refused `already-withdrawn`; one of an article the store
does not hold, `no-such-article`. It needs the running owner.

## Accounts for friends (invitation codes)

An account for a friend is made by the friend, from a code you hand them
(specs/nntp.md, "Invitation-code accounts"). With the node running or not:

```
fn operator CONFIG account invite --expires 86400
fn operator CONFIG account list
```

`account invite` prints one code, once, on stdout, after the pending row is
durable; the node keeps only its digest, so a lost code is issued again, never
recovered. Without `--expires` a code lives 604800 seconds. The friend, on a TLS
connection, sends `XREDEEM CODE LOGIN`, then `XREDEEM PASS PASSWORD`, and is
answered `281` once the account is durable; from the next connection they log
in with AUTHINFO USER/PASS as LOGIN, bound to the login's local principal, with
no auth.toml edit and no restart. A code redeems once; the same exchange after a
lost reply answers `281` again and binds nothing new. `account list` shows
`redeemed LOGIN PRINCIPAL-HEX` and `pending expires EXPIRY` lines, never a code,
digest or verifier. Redeemed accounts and auth.toml's credentials together are
bounded by the profile's `max-credentials`.

## The node's own web face: an in-node reader client

The web face (`[web]`, WEB-005) is an NNTP client that lives inside the
node, and the way it reaches the owner is the one any in-node client should
use. A browser session is a LOGICAL READER CONNECTION: the host opens it
with `fn-owner-exposure-open FAMILY ADDRESS nil` under the owner mutex
(`fnn-owner-serialized SERVICE nil ... :reader`), exactly as the I/O loop
admits a socket (`fnn-mux-admit`), so the exposure rules see the browser's
address; when ACL2 says the browser's channel is protected it calls
`fn-owner-tls-established` on the id, as a completed handshake does. Each
command is fed with `fnn-owner-handle-chunk SERVICE CID OCTETS nil :reader`
(no socket: a submission commits in the same quantum, as the pull feed's
logical connection does, `host/native/pull-service.lisp`), the reply
rendered with `fnn-owner-render-next`, and a `:defer` answer waited out and
fed again. A connection the owner no longer knows is an `fnn-store-error`
from that call. It is closed as a socket's is: `fn-owner-close`, then
`fn-owner-exposure-release`. Nothing about authentication, group access,
posting or pacing is re-implemented: it is the served machine's.

## The friends' web reader

The friends' web reader is the node's own web face (WEB-005, the section
above; docs/web.md is the operator's walk). It runs inside the node
process: no other account, service, folder or program, and no Python.
`install.sh --reader` only appends a `[web]` table to `fn.toml`
(`127.0.0.1:8920`, `proxied = true`); the node reads it when it starts
(`books/web-config.lisp` `fn-web-config-plan`, which plans the face only on
a port of its own, at an admitted address, and with `tls` only beside
`[listener]`'s certificate). The release's `clients/` keeps only the
command-line clients (`fn-client`, `fn-agent`, `fn-consumer`, `fn-verify`),
and `tools/runpath_check.py`'s clients rule refuses a service template
there. The Python readers, `tools/fn_reader.py` as its own service and
`tools/fn_web.py` on the user's computer, were retired on 2026-09-28.

Where it sits:

```
browser --HTTPS--> Caddy (443) --HTTP, 127.0.0.1--> the node's face (8920)
the face --a logical reader connection, no socket--> the node's served step
```

With `tls = true` the node serves HTTPS itself and there is no Caddy.

### Threat model

What it protects:

- **The operator's authority.** The face holds none of its own. Every
  decision is the served machine's: the node checks every password
  (AUTHINFO, `281` or `481`), makes every account (XREDEEM's `281` only once
  the account is durable), decides which groups a login sees and may post
  to (`account access`), accepts or refuses each post, and decides whose
  cancel withdraws what. The face keeps no account table and adds no
  permission; a session exists only after a `281` on its own connection
  (`fn-web-sessions-bound-by-281`, PRF-339).
- **What it trusts about the network.** It binds `127.0.0.1` unless the
  operator names another address. A browser's address is the socket's
  peer; with `proxied = true` and a loopback peer only, it is the last
  `X-Forwarded-For` entry, the one the proxy appended. A connection counts
  as protected (for `protected_only`) only when it is TLS here or its peer
  is loopback; any other gets `483` to a login on a protected-only node.
- **Friends' passwords.** Written nowhere. A password is decoded from the
  sign-in or redeem form into the command octets of that one request and
  kept in no session, file, URL, page or log.
- **Sessions.** Held in the node's memory only, so a restart signs
  everyone out. Each is a 256-bit token from the OS CSPRNG, bound to one
  owner connection and one login; the cookie is `HttpOnly`,
  `SameSite=Lax`, and `Secure` (with HSTS) when the face is TLS or proxied
  from loopback. Every signed-in POST carries the session's form token, and a POST
  whose `Sec-Fetch-Site` or `Origin` names another site is refused.
  Sessions idle out after `idle_seconds` (12 hours) and at most
  `max_sessions` (64) are kept.
- **Pages.** ACL2 renders every page from the session's own replies
  (`books/web-render.lisp`); every octet from a reply or a form is escaped
  (PRF-338). No script, no font, and `Content-Security-Policy: default-src
  'none'` (styles and images from the face only, `frame-ancestors 'none'`).
- **Guessing.** The node's own `exposure-auth-failures` pacing, for the
  browser's address: behind Caddy each browser is its own address, so no
  `exposure-trusted` entry for the proxy is needed.

What it does not protect against:

- Root on the node's machine, or the node's own account: either can read a
  password in the node's memory while its request runs.
- Caddy, which terminates HTTPS and so sees each password in transit: it is
  in the trusted base for friends' passwords. Serve nothing else under the
  face's web name (its cookies are `Path=/`).
- Another local user of the machine: 127.0.0.1:8920 is open to them. They
  can sign in only with a friend's password; with `proxied = true` they can
  choose their own `X-Forwarded-For` and so their address for the pacing.
  Do not run the face on a shared machine.
- A friend's own device: whoever holds its session cookie is that friend
  until it idles out, they sign out, or the node restarts.
- A slow browser: the face serves one connection at a time and gives each
  request up to 15 seconds.

Proofs: PRF-337 (the request parse, `books/web-request.lisp`), PRF-338 (the
escaping), PRF-339 (sessions), PRF-340 (the `[web]` plan). Tests:
tests/test_native_web.py (a native node's face), tests/web_face_drive.mjs
(a browser against a scratch node), tests/test_runpath_check.py (the
clients rule), tests/test_release_tarball.py (the layout),
tests/friends_tarball.sh (`install.sh --reader` renders the `[web]` table).

## Private groups: which login sees which group

Every login sees every group the node carries unless you give it an access
rule (specs/nntp.md, "Group access"). A rule is two wildmats, the groups the
login reads and the groups it may post to; with the node running or not:

```
fn operator CONFIG account access bob --read 'fn.*,!fn.private.*' --post 'fn.*,!fn.private.*'
fn operator CONFIG account access alice --read '*' --post '*'
fn operator CONFIG account access --anonymous --read 'fn.public.*' --post '*,!*'
fn operator CONFIG account access show
```

A group outside a login's read pattern is absent to its connections: LIST in
every variant omits it, GROUP and LISTGROUP answer `411` exactly as for a group
the node does not carry, an article all of whose groups are outside the pattern
answers `430` by Message-ID, and a cross-posted article shows only the readable
groups in its overview. A POST naming a group the login may read but not post to
answers the read-only `441` (LIST ACTIVE shows `n` to that login); one naming a
group it may neither read nor post to answers the `441` of an unknown group. A
login without a rule, and a rule of `*`, sees everything, so existing accounts
are unchanged. `--anonymous` is the rule of a connection that has not logged in (`*,!*` admits
no group; RFC 3977's wildmat cannot start with `!`);
under `[auth] required` there is none. `account access show` is the `account
list` report, whose `access LOGIN read R post P` lines are the rules. A rule
reaches a connection when the connection opens or re-pins, like every other
configuration change. What it does not do: it is this node's reader view, not
the peers'. An article in a private group is fed to a peer exactly when the
peer's feed patterns say so (`peer add`), and the peer's own readers see what
that peer allows; keep a private group out of every peer's pattern to keep it
on this node. You, the operator, read everything (`store inspect`, the Store
itself), and nothing is encrypted at rest: agents that need secrecy from the
operator encrypt their own article bodies. A Message-ID is unique across the
node, so a POST reusing a hidden article's Message-ID is refused as a duplicate.

## Agents' consumers: bind each to its account

A local consumer (`fn consumer register CONTROL NAME GROUP ...`) runs over
the owner's control socket and reads every group, as you do. Bind an agent's
consumer to the agent's account so it reads only what that login may read
(specs/consumer-progress.md, "Bound consumers"); with the node running or
not:

```
fn operator CONFIG consumer bind agent-bob --account bob
fn operator CONFIG consumer unbind agent-bob
fn operator CONFIG consumer show
```

A bound consumer polls and acks with its account's password (`fn consumer
bound-poll` / `bound-ack`, the password in a 0600 file), and is served only
while the account's read rule (`account access`) admits the consumer's group;
otherwise it is refused and keeps its position. Its plain `poll` and `ack`
are refused. `consumer show` is the `account list` report, whose `consumer
NAME account LOGIN` lines are the bindings. Unbound consumers are unchanged.

## Deploy a new release (D34: fresh deploys, no migrations)

A deploy is a reinstall of the release. There is no in-place upgrade, no
versioned release directory and no rollback of a store. The release directory
(one `libexec/fn/`) is replaced whole; the store directory is the node's
persistent private state and stays (PKT-618, the coordinator's decision under
D34). A fresh node is `init`ed instead; `init` also creates the node's key
file.

```text
# stop the unit; install the release (one libexec/fn/, replaced whole)
# start the unit                                   # the store directory stays
```

Only when the store itself must be rebuilt (a store of another format is
refused at open, below: every store made before 2026-09-27 is format 8)
does its history go through an archive, exported with the release that made
the store, before the new one is installed. The archive is
Store history, not a node backup: it never carries `STORE/keys/`, so the key
files are moved into the new store directory before its first start:

```text
fn operator NODE/fn.toml store export ARCHIVE
# stop the unit; install the release
mv NODE/store/keys NODE/keys.keep && rm -r NODE/store
fn operator NODE/fn.toml store import ARCHIVE
mv NODE/keys.keep NODE/store/keys
# start the unit
```

### The node's key files (SEC-006)

`STORE/keys/` (mode 0700) holds the node's protected root, one file per key
epoch, each mode 0600: `node-secret.key` is the current epoch and
`node-secret-E.key` each older epoch a rotation kept. The root keys the
Cancel-Lock the node writes into each account's posts (and the
posting-account value of Injection-Info); it is never printed, served,
written into a configuration record or exported. Back up `STORE/keys/`
separately from any archive, as private node state.

```text
fn --fn store STORE node-secret create [IDENTITY]   # once; init does it
fn --fn store STORE node-secret rotate [IDENTITY]   # a new epoch; the old one is kept
```

`create` answers `node-secret created epoch 1` and refuses, exit 1, with
`node secret STORE/keys/node-secret.key exists; refusing to replace it` when
a secret exists: no verb replaces a secret. IDENTITY is the node identity the
keys are bound to (`local` when omitted; a rotation keeps the current one
unless another is given). `rotate` keeps the current file as
`node-secret-E.key` and answers `node-secret rotated epoch E+1`; posts locked
under any kept epoch stay cancellable by their poster. The node refuses to
start, by name, while `node-secret.key` or a kept older epoch is missing, a
file is readable or writable by group or others, or a file does not parse;
a start never creates a secret. A store imported without its key files needs
`node-secret create`, and the posts its accounts made before then cancel only
by a signed canceller or the poster's own RFC 8315 key.

The store has one format, `fn-store-9`: its commits go to the record log,
`journal/NNNNNN.log` segments (six digits, the highest present the active
one), one fsync per batch of POSTs; a checkpoint names the first segment it
does not cover and the covered ones are dropped (`store compact` above).
A store of the per-file layout (`fn-store-8`, every store made before
2026-09-27) or of any other format is refused at open by name (`open
refused reason=store-format: reinstall from the release and import`, exit
1); its archive, exported by the release that made it, imports here as
format 9 (`fn-sxp-log-profile`). The archive carries the committed records,
the configuration records, the profile and the frontier; the store identity
and consumer state are records, so they travel with them. Feed journals and
BP spools do not: a reinstalled node re-peers. It is a Store-history
export, not a node backup: the node's secrets and private state (TLS keys,
credentials, the HKDF and pseudonym roots), peer journals and the BP and
TCPCL stores are kept separately, and the MANIFEST does not
say the archive is the node's newest history. Keep the archive until the new
node serves; it is the only copy of that history.

What an older release refuses of this store's records (facts about releases, not a rollback procedure: under D34 a deploy is a fresh install and an older release is never started over a newer store):

Once an account code is redeemed on a release with accounts, releases before
it cannot open the store; roll back only from the pre-upgrade snapshot (PKT-440:
an older image refuses configuration delta kinds 15 and 16 at decode; a store
that never issued a code is unaffected).

The same rule covers the login-binding rows (delta code 17, `principal
bind|unbind` applied live through the running node since 2026-09-26): a store
that ever published a binding is refused by releases before it; roll back only
from the pre-upgrade snapshot.

The published checkpoint names its event index only by its shape, and the
shape changed at dev a249a699 (a Message-ID trie beside the sequence trie)
and again at d0df09ed (the record count). A checkpoint published by an image
from a249a699 up to d0df09ed is refused by name by every later image with
this check: `status` and `store recover` say `open=full-replay
reason=checkpoint-index-shape`, and the first open after the upgrade is a
full replay of the history (at 20,000 articles about 170 s on hbox under
load). Never deploy an image from d0df09ed up to this check over such a
node: it opens that checkpoint as `open=checkpoint:S` with a record count of
0 and a Message-ID index that misses committed articles (PKT-395). A
checkpoint published before a249a699 is refused too, today as
`reason=checkpoint-open-refused`. In a rollback the same holds in the other
direction: older images reject a newer checkpoint file and fall back to a
full replay.

And the incremental peer rows (delta codes 18 and 19, `peer carries` and
`peer budget` since 2026-09-26, offline or live): a store whose
configuration log holds either is refused at open by releases before them
(the deployed bbf52159 image exits 4; rehearsed on a copy, planning/evidence/
caps-to-profile-2026-09-26.md), so roll back only from the pre-upgrade
snapshot. A store that never extended a peer after the upgrade is unaffected.
The same held for a checkpoint or (format-8) pack directory that published
generation 4096 or more (the numbering is a uint32 since then): an older
release refuses that directory.

## Back up

Stop the service, then copy the store directory.

The store is an append-only record log (`journal/NNNNNN.log`: each batch
one chained, trailer-checked entry, fsynced before its replies) plus a
state checkpoint and a small set of metadata files (the profile, the
configuration records, the filesystem identity, the freshness anchor).
Recovery keeps the longest prefix of entries whose chain and trailers
check and zeroes a torn tail, so a copy taken while the service runs can
silently lose the newest articles, and one taken across a compaction can
pair a checkpoint with segments it does not match, which the open refuses
by name (`history-short-of-checkpoint`, `checkpoint-damaged`); this is
reasoned from the open's recovery rules (planning/evidence/log-recovery-2026-09-27.md),
not measured on a hot copy. Stopping first avoids the question.
Keep `STORE/keys/` with the copy, privately.

What a copy does not give you is freshness. A restored image cannot tell by
itself that it is not an old snapshot, which is what `fn anchor` and the
freshness check inside `fn recover` are for. Record an anchor before the
backup and check it after the restore.

## Recover after a crash

A crash needs no special action: the next start reads the checkpoint and
replays the log after it through ACL2, streaming one entry at a time
(log-open-stream), and reopens. Run `fn recover` first when you want the report
before the service starts.

An owner killed without its cleanup (SIGKILL, a power cut) leaves its
control socket node behind. The offline `control` and `peer` verbs see the
node and a free writer lock, so no owner holds the store: they remove the
node under the control-path lease, print `stale control socket removed`, and
run offline (HST-010, `fn-native-control-liveness`). With the lock held and
no socket node they refuse `store-held` without opening the store; with both,
they ask the owner. The next `run` removes a stale node itself.

```
fn operator /etc/fn/fn.toml recover
```

It prints the recovered transaction and article counts, any staging orphans
an interrupted publication left behind (those are named, not hidden), and
the freshness verdict. Its exit code is the freshness verdict's: `accepted`
when the store is demonstrably not a stale image, `uncertain` when no anchor
server could be reached, `refused` when the anchor says the image is older
than the one its own records stand under. A refused recover is a signal to
stop and work out which image you are holding, not to retry.

(Historical: a store written by a release before 2026-09-25 is format 8,
refused at open by `reason=store-format` before this check can run.) A store
written by a release before 2026-09-25 (C1) that holds a signed control
article, such as a cancel, filed under its Newsgroups is refused by name by
every open (`recover`, `run`, `health`, `inspect`, `checkpoint`):
`pre-C1 control record (txid N, <message-id>): run store repair-control`,
exit 1. Nothing is changed or replayed. The repair verb
`fn store ROOT repair-control` exists but refuses (`repair semantics
undecided (PKT-444)`) until what such a repair means is decided; keep the
store as it is until then.

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
[MAX-ADU-OCTETS MAX-BUNDLE-OCTETS [ROTATE-RECORDS]]` (default 64, 16 MiB,
65,538 and 1 MiB; each at most 2^24; never lowered). ROTATE-RECORDS (default
4,096; it may be lowered) is when the journal rotates by itself: `bp-node
serve` and `bp-node dispatch` rotate at their open once the selected
generation holds that many records (`BP journal rotation generation=G
records=N threshold=T`, then `BP journal generation selected`), so no
operator `bp-node checkpoint` is needed to keep a node taking custody. A bundle past the ADU or bundle bound is
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

## What one node sustains: the measured envelope

### Since 2026-09-27: the record log and the paged arena

The full envelope below (2026-09-26) was taken on a per-file (format 8)
image and has not been re-run on the record log. What was measured since,
each on hbox (shared, loaded), one lane each, each figure with its scope:

- **ARTICLE, served.** Median 0.406 ms, p95 0.528 ms for a 2,048-octet
  article over loopback with a buffered client, under the throughput gate's
  matched load, against 0.445 / 0.484 ms on the baseline f370581bf; POST
  median 3.6 ms in the same run (image 1ee0953ab,
  planning/evidence/gate-regress-2026-09-27.md).
- **OVER.** A 2,000-article range 212 to 299 ms median and a 40-article
  window about 4 ms, on a 10,000-article store (images native-b3/b4, box
  load 12 to 19; planning/evidence/served-readers-2026-09-27.md), against
  317 ms p95 for 40 articles in the 2026-09-26 table below.
- **Reopen from a state checkpoint.** 40,000 articles of 2 KiB, format 9:
  13.6 s to `LISTENING` against 55.2 s for the full replay; live heap
  579 MB against 2,138 MB; peak RSS (VmHWM) 1,323 MB against 7,181 MB. The
  checkpoint verb itself took 77.5 s at 6.8 GB RSS
  (planning/evidence/checkpoint-arena-3-2026-09-27.md).
- **Full replay of the record log.** 10,000 articles of 32 KiB: 55 s, live
  heap 640 MB (about 310 MB of it the image's own world), peak RSS 1.25 GB,
  after the open began reading one entry at a time (was 4:38 and 14.1 GB;
  planning/evidence/log-open-stream-2026-09-27.md).
- **Compaction.** `store compact` at 40,000 articles of 2 KiB: 40 to 139 s
  at 4.6 to 7.5 GB peak RSS depending on the image and whether the store
  was already compacted, against 2,963 s at 16.4 GB for the format-8
  compaction; `store reclaim` of every article 348 s at 1.5 GB
  (planning/evidence/log-recovery-2026-09-27.md section 4). A compaction's
  memory is not yet bounded by the step.

`operator CONFIG health` prints the store's format: `format=9` for the
record log (`fn-nh-profile-words`, books/native-health.lisp, reads it from
the profile). Every image refuses a format-8 store at the open by name
(`open refused reason=store-format`), so a store `health` opened is format
9 (its root holds `journal/`).

### The 2026-09-26 envelope (per-file image)

These figures are measured, not promised. They were taken for one named
profile on one box, by `tools/service_envelope.py`, on 2026-09-26. Each
figure is tied to its image and its run's JSON in
`planning/evidence/service-envelope-2026-09-26.md` (SCN-109).

- **The workload.** `operator init --profile scale --max-transactions 1048576
  --max-history-octets 4294967296 --max-article-octets 16384 fn.test`, one
  group. Articles are 2 KiB; one in 256 is a hybrid-signed carrier (9.5 KiB).
  There are no pins, no relay debt and no TLS.
- **The client.** It runs on the same machine as the node, over loopback. Latency
  rows use one client at a time; the rate rows run 3 connections reading
  `ARTICLE` beside the posters.
- **The box.** hbox has 24 CPUs and is shared with other work (load average 7
  to 14 throughout).
- **The storage.** tmpfs, or the ZFS pool `tank`: 91 percent full,
  fragmentation 47 percent, no separate log device (SLOG).
- **The image.** The developer image of dev 1770d687 (after
  served-path-scale).

A loopback, scripted measurement on one machine is not a multi-machine
deployment result, not a network measurement and not a human study. Read the
tmpfs column as the node's own work, never as what a disk-backed deployment
does.

| N = 10,000 | tmpfs | ZFS (`tank`, above) | the v1 target |
| --- | ---: | ---: | ---: |
| greeting on the loaded store, p95 | 1.3 s | 1.5 s | 50 ms |
| `OVER` of a 40-article window, p95 | 317 ms | 321 ms | 50 ms |
| unsigned POST, last line to durable `240`, p95 | 6.5 ms | **607 ms** | 250 ms |
| hybrid-signed POST, p95 | 282 ms | **786 ms** | 500 ms |
| sustained POSTs, 1 connection with 3 readers | 73 /s | **1.4 /s** | 10 /s |
| sustained POSTs, 8 connections with 3 readers | 62 /s | **2.1 /s** | 10 /s |
| restart to `LISTENING`, full replay | 12.7 s | 72 s | 30 s |
| restart to `LISTENING`, from a fresh checkpoint | 11.9 s | 10.6 s | 15 s |
| peak owner memory (VmHWM), after the rate rows | 16.9 GB (N 18,260) | 3.7 GB (N 10,368) | — |

N = 100,000 (tmpfs only): **could not run**; see below. At the largest N the
node reached, 36,208 on tmpfs, the greeting's p95 was 8.5 s, `OVER` of 40
articles 4.2 s, an unsigned POST 12 ms and a signed POST 963 ms; the reopen
from a checkpoint took 51 s and the owner's heap stood at 29.7 GB.

**The published tier.** On a pool like `tank` (nearly full, no SLOG), expect:

- a durable POST reply in about half a second (p95 0.6 s unsigned, 0.8 s
  signed);
- about two POSTs a second sustained, not ten.

Almost all of that time is the durable publication, not fn's own work: the
same POST costs 16 ms of owner CPU. A separate log device, a less full pool,
or the fewer barriers that marker-sharing is building are the levers. fn will
not acknowledge a POST before it is durable to buy the difference.

**Where fn itself misses its targets.** These rows miss on every filesystem:

- **The greeting.** Each connection still walks the whole state under the
  owner's lock; PKT-455 carries this.
- **`OVER`.** About 8 ms a row; PKT-476 carries this.

The owner's memory grows with sustained posting. Watch `VmHWM`
(`/proc/PID/status`) and size the host for it.

**N = 100,000 could not run.** Neither could anything much past 36,000 while
the node was taking POSTs. An owner posting steadily from an empty store
stopped at N = 32,729 with `Heap exhausted, game over.` (SBCL's 32,000 MiB
dynamic space), inside the automatic checkpoint capture. By N = 29,453 that
capture took 90 s.

A restarted owner opened in 49 s and died the same way at N = 36,208, at its
next capture (PKT-191).

- The POST each dead owner was answering is uncertain until you ask the node
  (`STAT`) whether it was stored.
- On this image, keep a node that takes posts well under about 30,000 articles.
- Watch `VmHWM` against the dynamic space.

## Peering with a friend: the walk of 2026-09-26

This page takes a friend who has only the release tarball from a machine
with no fn on it to a node that peers with yours: one invitation each way,
articles flowing both ways over STARTTLS, each node logging in to the other
as the other's enrolled principal. Every command below ran on 2026-09-26
between two real machines on one LAN (the friend: persvati, Ubuntu 25.10;
you: an hbox scratch node, Ubuntu 24.10), from the release
`fn-8fb3768e8439-linux-x86_64.tar.gz`; the record is
[friends-peer](../planning/evidence/friends-peer-2026-09-26.md). It is a
walk of `bin/fn` as shipped, not a deployment claim.

In the commands, `ME` is your node and `FRIEND` the friend's. Replace the
addresses, ports and path identities with yours:

| | you (the inviter) | the friend |
| --- | --- | --- |
| address, port | 192.168.50.39, 11991 | 192.168.50.120, 11990 |
| path identity | `hbox-scratch.friends.fn.invalid` | `persvati.friends.fn.invalid` |
| node directory `N` | `/tank/fn/scratch/friends-peer/hnode` | `/home/ember/fn-node-friends` |

### 1. Bring a node up from the tarball (both of you)

You need Linux on x86-64 with the system's OpenSSL 3 library (`libssl3` on
Debian and Ubuntu, `openssl-libs` on Fedora; any 3.x) and, for the TLS pair
below, an `openssl` command (any version with EC keys). Nothing else: the
tarball carries its Lisp runtime, libsodium and its ML-DSA-65 library, and
runs from wherever it is unpacked.
`$F` alone prints the operator's usage; `$F --version` prints the source
revision the tarball was built from.

```sh
cd $N
sha256sum -c fn-8fb3768e8439-linux-x86_64.tar.gz.sha256    # the sum you were given
tar xzf fn-8fb3768e8439-linux-x86_64.tar.gz
(cd fn-8fb3768e8439 && sha256sum -c --quiet SHA256SUMS)   # every file in it
F=$N/fn-8fb3768e8439/bin/fn
C=$N/node/fn.toml
mkdir -p node
$F operator $C mission small-community --host 192.168.50.120 --port 11990
```

`mission` writes `fn.toml`: the listener on that address, `[auth] required`
and `protected_only` (a login is needed, and only after STARTTLS), a TLS
pair under `node/tls/`, the log under `node/log/`. It does not make the TLS
pair. Make one whose subjectAltName is the address the other node will dial
(the other node verifies the handshake against this certificate and that
name):

```sh
openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 3650 \
  -subj /CN=persvati.friends.fn.invalid -addext subjectAltName=IP:192.168.50.120 \
  -keyout node/tls/key.pem -out node/tls/cert.pem
chmod 600 node/tls/key.pem
$F operator $C init                                   # local.general, local.test
$F operator $C policy set path-identity persvati.friends.fn.invalid
printf 'PASSWORD\nPASSWORD\n' | $F operator $C principal set-password ember --posting
```

`set-password` reads the password twice, from the terminal or from two lines
of standard input. Then the node's own keys, the principal that signs its
invitation or acceptance. `peer keygen` draws both pairs through the
tarball's own libsodium and ML-DSA-65 library, so no `openssl` command is needed:

```sh
$F operator $C peer keygen $N/keys            # prints: principal HEX
systemd-run --user --unit fn-friends -p MemoryMax=8G $F operator $C run
```

`keygen` refuses a directory that exists (it never overwrites keys), makes
it mode 0700 with every file 0600, and runs `peer genesis` over it. A key
directory made by hand (the `openssl genpkey` commands for Ed25519 and
ML-DSA-65, then `peer genesis KEYDIR`) works the same.

The key directory layout (`ed-public.bin` 32 octets, `ed-secret.bin` the
32-octet seed then the public key, the two ML-DSA-65 PEM files) is what
`peer genesis`, `invite` and `accept` read. The node answers from another
machine at once: `tools/node_probe.py 192.168.50.120 11990 --cafile cert.pem
--group local.general` with `FN_PROBE_USER`/`FN_PROBE_PASSWORD` set checks
the 483 before STARTTLS, the handshake, the login and a post read back.

### 2. One invitation, one acceptance, one confirm

You invite the friend. The last two words are your own address; the
invitation carries them, signed, so the friend's node can configure you:

```sh
# ME
$F operator $C peer invite persvati 'local.*' 192.168.50.120 11990 \
    hbox-scratch.friends.fn.invalid $N/keys $N/exchange/invitation-for-persvati \
    192.168.50.39 11991
```

Send the invitation file to the friend (it holds public keys only). The
friend accepts; this enrols your principal on the friend's node and, in one
configuration record before that enrolment, configures you as a peer:

```sh
# FRIEND
$F operator $C peer accept $N/exchange/invitation-for-persvati $N/keys \
    persvati.friends.fn.invalid 192.168.50.120:11990 $N/exchange/acceptance-for-hbox
$F operator $C peer list
hbox-scratch.friends.fn.invalid path-identity=hbox-scratch.friends.fn.invalid address=192.168.50.39 port=11991 security=clear inbound=local.* outbound=- auth=principal:70fc9ddc...
```

The friend sends the acceptance back. You confirm: one record consumes the
invitation and configures the friend, then the friend's principal is
enrolled here:

```sh
# ME
$F operator $C peer confirm $N/exchange/acceptance-for-hbox $N/exchange/invitation-for-persvati
$F operator $C peer list
persvati path-identity=persvati.friends.fn.invalid address=192.168.50.120 port=11990 security=clear inbound=local.* outbound=- auth=principal:60779285...
```

An invitation made with `- -` in place of your address still enrols you at
the friend's node, and configures nothing there.

**A friend whose keys have changed since genesis.** A document binds its
principal by the keyring of the node that reads it: when your node already
holds the friend's principal (enrolled, then succeeded by a key statement or
`hybrid-enroll-next`), the friend signs the acceptance with their *current*
keys and your confirm takes it (one record consumes the invitation and
configures the friend; there is nothing to enrol, and the log says `peer
confirm: the acceptor's current keys; nothing to enrol`). An acceptance under
a key set the friend has since replaced is refused `not-current-keys`, one
from a revoked principal `revoked`. A node that has never enrolled the friend
still decides by the genesis identity and refuses current keys that are not
the genesis ones (`genesis`): no succession chain travels with the document.

The same holds the other way round. When the friend's node already holds
*your* principal at the keys your invitation is signed with, its `peer
accept` configures you as a peer and enrols nothing (its log says `peer
accept: the inviter's current keys; nothing to enrol`), and the acceptance
is written as usual. Accepting the same invitation again is refused
`already-enrolled`: there is nothing left to do.

#### An account for the friend on your node

To let the friend read and post on your node as themselves, hand them one
code (it is printed once; send it over a channel you trust):

```sh
# ME
$F operator $C account invite --expires 86400
```

The friend, over TLS (STARTTLS or the implicit-TLS listener), sends
`XREDEEM CODE LOGIN` (answered `381 send the password with XREDEEM PASS`),
then `XREDEEM PASS PASSWORD`, answered `281 account bound; authenticate with
AUTHINFO on a new connection`; from then on they log in with AUTHINFO USER/PASS
as LOGIN. `$F operator $C account list` shows the login and its principal.
Once an account code is redeemed on a release with accounts, releases before it
cannot open the store; roll back only from the pre-upgrade snapshot.

### 3. The protected feed both ways

The records `accept` and `confirm` write are clear-transport and inbound
only. Each side now gives the other a login bound to the other node's
principal (the `HEX` its `peer list` shows), keeps the password the other
side gave it in a credential profile, and replaces the peer record with its
STARTTLS form and both halves. Exchange the passwords and certificates out
of band.

```sh
# ME: a login for the friend's node, bound to its principal
printf 'PW-FOR-FRIEND\nPW-FOR-FRIEND\n' | $F operator $C principal set-password persvati-node \
    --principal 607792851af81f99899a21cb728087edcb137e42883e11d83e9fc458d4d33033 --posting
# ME: how I log in at the friend's node (the login the friend made for me)
umask 077; printf 'FNAUTH1\nhbox-node\nPW-FOR-ME\n' > $N/exchange/persvati.fnauth
$F operator $C peer add persvati persvati.friends.fn.invalid 192.168.50.120 11990 \
    'local.*' 'local.*' \
    principal 607792851af81f99899a21cb728087edcb137e42883e11d83e9fc458d4d33033 \
    $N/exchange/persvati.fnauth false true starttls 192.168.50.120 $N/exchange/persvati-cert.pem
$F operator $C peer pull persvati 20
```

`peer add` reaches the running node through its control socket and
replaces the record `accept` or `confirm` wrote without a restart (the
live reconfiguration path; observed in tests/test_native_friends_feed.py).
The friend does the mirror image (a login `hbox-node` bound to your
principal, a profile naming `persvati-node` and the password you gave, `peer
add hbox-scratch.friends.fn.invalid ... starttls 192.168.50.39 hbox-cert.pem`,
`peer pull hbox-scratch.friends.fn.invalid 20`). The words of `peer add`, in
order: name, path identity, address, port, inbound wildmat, outbound
wildmat, `principal HEX` (who the peer is when it logs in here), the
profile file this node logs in to the peer with, `false` (never send the
credential in the clear), `true` (stream with `MODE STREAM`), then `starttls
SERVER-NAME ANCHOR-PEM` (the name the peer's certificate must carry, and its
certificate as the only anchor).

**A friend with a DNS name and a public certificate** (Let's Encrypt, say)
is added by name, and anchored on the system's public roots rather than on
a leaf that changes at every renewal:

```sh
$F operator $C peer add friend friend.example.org news.friend.example 563 \
    'local.*' 'local.*' principal HEX $N/exchange/friend.fnauth false true \
    implicit - -
```

The address word may be an RFC 1123 host name or an IPv4 literal. A name is
resolved on every connection attempt (a renumbered friend is reached at the
new address on the next try); `-` as the server name is the host's own name
(a numeric address must be given the name its certificate carries), and `-`
as the anchor is the system's trust store. A certificate that does not carry
the name, and a name that does not resolve, each leave a line in `fn.log`
(`peer dial via=feed peer=friend host=news.friend.example
outcome=name-mismatch retry=yes`, or `outcome=unresolved`) and are retried;
neither stops the node. `peer invite` takes a name for HOST and MY-HOST too
(specs/peering.md section 1.2.4).

**A cancel travels with the groups it names.** A control article is filed
under `control.cancel`, and it is offered to a peer whose outbound wildmat
matches its Newsgroups names *or* its filing group (RFC 5537 sections 3.6
and 5.3; PRF-163). With `local.*` alone, the author's signed cancel of a
`local.general` article reaches the friend and withdraws the target there.
Before PRF-163 it was offered under `control.cancel` alone and never left
the origin (observed: `<friends-t1@persvati.invalid>`).

What you should then see in each `node/log/fn.log`:

```
accepted feed peer=persvati message-id=<...> code=239 ...       # pushed, TAKETHIS accepted
pull peer=persvati round=done cursor=advanced transport=tls     # pulled over STARTTLS as a principal
```

### 4. Check it

Post on one node and read on the other (`tools/fn_client.py post
local.general --node 192.168.50.120:11990 --cafile persvati-cert.pem`, then
`read local.general --all --node 192.168.50.39:11991 --cafile
hbox-cert.pem`). The article keeps its Message-ID and its authored source
(the article without Path, Xref, Injection-Date, Injection-Info and
FN-Authorship); its Path grows by the relaying node, and its local article
number is each node's own. The session's table is
`planning/evidence/friends-peer-2026-09-26/identity-after-restart.txt`.

A node restarted, or running with a skewed clock, resumes both feeds from
where they were: the push queue re-offers what the peer has not taken
(`438` for what it already has), and the pull cursor is kept in the *remote*
node's clock (the round asks the peer `DATE` first, RFC 3977 section 7.1),
so a ten-minute skew on one side neither skips nor repeats an article.
Observed with the friend's node at +10 minutes and both nodes restarted:
seven articles, each stored exactly once on each node.

A signed article withdrawn on its origin by its author's signed cancel
answers `430 withdrawn` on the other node too, once the cancel arrives
there: the other node verifies the cancel under the author's enrolled keys
(the node principals are enrolled by the exchange above).

A friend who rotates keys posts a signed succession to `fn.keys` (the
node needs a `keys` grant for the friend's principal: `operator CONFIG
control grant PRINCIPAL-HEX keys fn.keys`). If the statement arrived before
the grant, it declined; after granting, `operator CONFIG keys redecide
MESSAGE-ID` enrols the successor without a restart (docs/operator.md, "Re-decide
a declined key statement").

Each node decides a cancel again under its own grants. The author's own
cancel withdraws on both nodes; a moderator's cancel of someone else's
unsigned article withdraws only on the node where you ran `control grant`
for that moderator over the article's group, so grant it on both nodes if
you both want it honoured. The order does not matter: a cancel that
arrives before its article hides the article from its first appearance, a
restart between the two changes nothing, and a reader already connected
keeps seeing what it saw until it posts or reconnects
(`tests/test_native_control_across_peers.py`, SCN-100).

`hybrid-author` names its refusal: a signed article whose `Newsgroups`
names a group this node does not carry is refused `UNKNOWN-GROUP` (exit
1); ask your friend to create the group, or post to one you both carry.

### What is not here

- A stranger's own account on your node: today you make it
  (`principal set-password`) and tell them the password. An invitation-code
  flow (the operator issues a code, the stranger redeems it over the reader
  port) is specified, not built (PKT-401).
- A view in which every article is withdrawn (two cancels by one author
  naming each other) answers the plain `430 no article with that
  message-id` rather than `430 withdrawn`; and the BP receiver's refusal
  line of an unfiled control article reads `reason=none` (PKT-443).
- A friend whose server keeps listing an article it cannot produce (it
  answers `ARTICLE` with 430) no longer stalls your pull: the other articles
  arrive in the same round, the pull asks from the same instant for a few
  rounds (`peer pull NAME SECONDS ROUNDS`; 5 when ROUNDS is left out)
  and then moves on, logging `dropped=<id>` once. What is not here yet: a
  friend's server that refuses `MODE STREAM` is still stopped per process
  (a restart spends one `MODE STREAM` again) and is not fed with IHAVE on
  the same connection; set its peer record's streaming word to `false`
  (PKT-431).
- One credential slot per peer serves both directions, so a credentialed
  pull needs outbound groups too (PKT-431).
