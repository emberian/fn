# Lane reclaim-lifecycle-2, 2026-09-26 (STO-019, PRF-129, SCN-075, PKT-263)

Dev lane `lane/reclaim-lifecycle-2` from dev 9d687b49, Claude Opus 5.5, under
the Fable mandate (section 8, the reservation paragraph; section 15 rows
"Budget exhaustion and recovery" and "Pack/reclaim/restore"). It continues
reclaim-lifecycle (planning/evidence/reclaim-lifecycle-2026-09-25.md: PRF-119,
the verb, findings F2 and F4) and implements PKT-169 as the coordinator
decided it.

## 0. The tight store on the merged image (step 0)

Image at 9d687b49 on hbox (w28 toolchain; developer core
0a18bf5379ed5949e72efc4ad89d81ca9b46902532b0c19fee25d9ed63f79510,
production core ddbe6e688365594fbb49378c8fafc2df19b9393d831462f21b64299baa809546),
tests/reclaim_lifecycle_native.py `--headroom-only`, a store with
max_history_octets 300,000 and 1 KiB articles
(logs/tight0.jsonl sha256 073b1fc99ddf2778304c035ae974158e8d5ce5d35e798ce52fb14e9da2676c01):

- **The 191st POST is refused** (`441 ... no capacity`), at bytes-used
  297,738 of 300,000; 190 accepted. The previous image refused the 151st at
  235,018. The store opens (`status` exit 0).
- Why it moved: dev's gate (width-boundary, `fn-sbud-article-budget-for`)
  charges an article its own record ceiling, `fn-sbud-article-figure`
  = `fn-record-encoded-octets-ceiling` (payload, groups), which evaluates to
  payload + 1,344 octets for one group (evaluated on the image's books:
  1,100 -> 2,444, 1,190 -> 2,534). These articles' stored payloads are
  1,183 to 1,185 octets (served at +75 for the Xref and Path lines added at
  serve time), so the figure is **2,529** per article, where the old gate
  charged the fixed 65,538. Each committed record is about 1,567 octets.
  Check: 190th admitted at 296,171 + 2,529 = 298,700 <= 300,000; 191st
  refused at 297,738 + 2,529 = 300,267 > 300,000.
- F2 was unchanged on that image: `store compact` and `store reclaim` both
  refused `temporary-space`, exit 1, nothing written.

## 1. What now works

- A store filled to its history bound still compacts and reclaims: the
  temporary-space check is against the disk's free octets, which the image
  observes (statvfs) and ACL2 compares; a pack the disk cannot hold is
  refused by name before a byte is written.
- Admission leaves room for one release record: every admitted record other
  than a release keeps the profile's gate admitting a release after it.
  `status` prints `maintenance-reserve octets=4096 transactions=1 held`.
- A reclaimed article's retention charge comes back, less the one
  permanent history unit its pin keeps: `charge-reserved` falls.

## 2. The assurance chain

Admission: native entry host/native/owner.lisp `fnn-owner-attempt` (served
POST, BP transit) and `fnn-owner-preflight-publication` (every other served
kind) -> host/owner-host.lisp `fn-owner-prepare`, `fn-owner-prepare-buffer`
(budget `fn-smr-article-budget-for`, handed to `fn-pcar-sbud-prepare`) and
`fn-owner-publication-verdict` (`fn-smr-verdict-at`); the developer
`store post`: host/native/io.lisp `fnn-command-post` ->
host/store-node-host.lisp `fn-store-sn-article-verdict`
(`fn-smr-article-verdict-at`) -> executed ACL2 subjects in
books/store-maintenance-reserve.lisp -> representation: the committed
record octets the owner carries as (K . SUM) (`fn-sbud-bytes-used-is-kernel-sum`,
PRF of store-budget) -> maintained relation: `fn-smr-roomp profile used
bytes` (the profile's gate admits one `:release` record) -> behavioural
theorems below -> observed result section 4.

Which entry establishes the relation: init
(`fn-smr-admitted-profile-starts-reserved`, every admitted profile at
(0, 0)). Which transitions preserve it: every admitted non-release record
(`fn-smr-admission-keeps-the-reserve`, `fn-smr-prepare-keeps-the-reserve`,
`fn-smr-article-verdict-keeps-the-reserve`), a reclaim (it only lowers the
committed octets, `fn-rclp-freed-is-the-admission-count` with
`fn-smr-roomp-antitone-in-octets`), a profile upgrade
(`fn-smr-profile-upgrade-keeps-the-reserve`). A release consumes it
(`fn-smr-reserve-admits-the-release`); it holds again once the reclaim
frees at least the release record's octets. A store filled before this
rule may report `short` (it was admitted by the older gate).

Maintenance's temporary space: native entry host/native/checkpoint.lisp
`fnn-compact-steps` / `fnn-reclaim-observe` (observation
`fnn-disk-free-octets`) -> host/checkpoint-host.lisp `fn-store-compact-decide`,
`fn-store-reclaim-decide` -> `fn-cverb-decide`, `fn-rclp-decide` ->
`fn-cverb-pack-fits-the-disk`, `fn-rclp-pack-fits-the-disk`.

The configuration record of a release (`retention set`) is in the
configuration namespace (bounded by max_config_generations and the record
bound), not in H, so Store admission cannot take its room. The BP namespace
keeps its own reservation, the FNBS debt cover (books/bp-node-debt.lisp
`fn-bpnd-spend-admission-preserves-cover`, unchanged); its bundles enter the
Store through the gates above.

## 3. Theorems

books/store-maintenance-reserve.lisp (PRF-129):

- `fn-smr-admission-keeps-the-reserve`: `fn-smr-verdict-at` admits kind K
  /= :release at (used, bytes), octets natural <= K's publication ceiling
  => `fn-smr-roomp` at (used+1, bytes+octets). (The `natp used/bytes`
  hypotheses were proved redundant and removed.)
- `fn-smr-prepare-keeps-the-reserve`: the served prepare
  `fn-sbud-prepare oc record (fn-smr-article-budget-for profile
  (fn-sbud-used store-of-oc) bytes record)` changed the owner, record narrow
  => reservation at (count+1, bytes + len(encode record)) and the history
  within H.
- `fn-smr-article-verdict-keeps-the-reserve`, `fn-smr-reserve-admits-the-release`,
  `fn-smr-admission-is-within-the-profile`, `fn-smr-roomp-antitone-in-octets`,
  `fn-smr-roomp-is-within-the-bound`, `fn-smr-admitted-profile-starts-reserved`,
  `fn-smr-profile-upgrade-keeps-the-reserve`.

books/store-compact-verb.lisp: `fn-cverb-pack-fits-the-disk` replaces
`fn-cverb-pack-fits-the-profile-budget` (PRF-073's event renamed:
the decision now reads DISK-FREE instead of the file footprint), and
`fn-cverb-temporary-space-is-the-disk-by-definition`.
books/store-reclaim-pack.lisp: `fn-rclp-pack-fits-the-disk` (PRF-129);
for step 2 (PRF-119) `fn-rclp-rewritten-charge-is-the-history-unit` and
`fn-rclp-freed-charge-account`, and `fn-rclp-event-decodes-to-the-tombstoned-record`
now states the charge is `*fn-rclp-history-unit*`.

Teeth: tests/acl2/store-maintenance-reserve-tests.lisp over packet 1's
profile (H 250,000, T 4): a boundary witness (admitted at H - 8,192, the
reservation held after a 4,096-octet record with no octet to spare) and per
hypothesis a failure of the conclusion: the profile's gate alone (admits at
H - 4,096, no release after), a release (consumes it), a record over its
kind's ceiling (4,097), a non-natural length; the count slot (T = 4: the
fourth transaction is the release's); the article gates with packet 1's
400-group article, its wide record, and each of the asked counts; the
upgrade and a lowered H. tests/acl2/store-compact-verb-tests.lisp: the
disk one octet short, the unobserved disk, the exact boundary, and the
must-fail without the decision. tests/acl2/store-reclaim-pack-tests.lisp:
the same for reclaim, and the charge: the fixture article's charge is 2,
its replacement's 1, the freed charge positive and accounted; under
keep-forever the charge is not released (must-fail).

## 4. Native (hbox)

Harness tests/reclaim_lifecycle_native.py (client and harness only),
scratch /tank/fn/scratch/reclaim-lifecycle-2, `systemd-run --user -p
MemoryMax=24G`. The developer image honours `FN_NATIVE_DISK_FREE=N` (a new
developer selector; the production image refuses to start with it), which
caps the observed free octets: the small disk is simulated that way, the
real statvfs figure is what every other run used.

The tight store (logs/tight3.jsonl sha256
52172ec12c77946e94fafe4e78138121b46f88293b79878e804b82c1e3db3de0), on the
step-1 image: 7ab656a7 plus the status line of 1a370f0a (developer core
2c21300cca8305c504afe314b24fcb7ebd3577c55eafaabc10c5c6467a86462c, production
core bd4436f70ef2c3fb245581a1f74e366f8f358567017aee5213dc8855175efaff):

| Step | Observed |
| --- | --- |
| fill (H 300,000, 1 KiB) | the 189th POST refused 441 (188 accepted) at bytes-used 294,602: 294,602 + 2,529 + 4,096 = 301,227 > H |
| `status` at the bound | `maintenance-reserve octets=4096 transactions=1 held` |
| `store compact`, free space capped at 1,000 | `compaction refused: temporary-space`, exit 1, files unchanged |
| `store compact` | exit 0, `records=188 generation=0 reclaimed=188` |
| `store reclaim`, capped at 1,000 | `reclaim refused: temporary-space`, exit 1, files unchanged |
| `store reclaim` | exit 0, `reclaimed=188 freed-octets=216842 generation=1 retired=1` |
| after | bytes-used 77,760 (216,842 fewer), reservation held, next POST `240` |

N300 section: see section 5.

A behaviour change a test pinned, stated: the reservation includes the
release's transaction, so a store admits articles while used + 1 < T. On the
development profile (T = 128) the 128th article is now refused by name and
the 128th transaction stays the release's.
tests/test_native_operator_verbs.py `NativeOperatorCapacityTests` asserted
128 accepted; it now asserts 127 and says why (the decided policy, not a
relaxed expectation). hbox, the 1a370f0a image: that class (5 tests) OK,
and tests/test_native_checkpoint.py `NativeProductionCompactTests` with
`test_reclaim_keeps_served_view_watermarks_and_next_number` and
`test_reclaim_cuts_keep_served_view_and_next_number` OK (3 tests, 55.9 s).
tests/native_owner_consumer_raw.lisp reads the owner's verdict function by
name; it now reads `fn-smr-verdict-at` (the laptop run: "native owner
consumer boundary passed").

## 5. The lifecycle at N=300 with the charge release

Image at 1a370f0a (developer core
9b6ae61ef332eaf7bec34ab7da22f459b62e494e43888ade3b2cadb48c1286e9, production
core 258c14c0f132f207cfca3493ab8088214574c797b704927338801012751887bd),
`run.sh n300 300 512 67108864 --cuts`, logs/n300.jsonl sha256
9450dd9c251c0318b8b72409f2e4109bc436729a0cce2898507c5b8c2ab2c21e, harness
exit 0. As the previous record's section 5, with the charge:

| Step | Observed |
| --- | --- |
| keep-forever; release-after 1 `--dry-run` | `reclaimed=0` both, nothing written |
| released-by-all-holders `--dry-run` | `would-reclaim=300 freed-octets=192490` |
| `store compact` | 307 files to 9 (packing) |
| 18 cuts (8 stop, 5 kill, 5 EIO) | every copy reopens (`status` 0), every rerun exits 0, every EIO exits 3, all 18 converge to the clean run's pack bytes |
| `store reclaim` | exit 0 in 2.6 s, `reclaimed=300 freed-octets=192490 generation=1 retired=1` |
| after | octets 318,210 to 125,720 and bytes-used 316,750 to 124,260 (both exactly 192,490 fewer); **charge-reserved 600 to 300** (each article's pin keeps its one history unit) |
| rerun | `reclaimed=0`, same pack bytes |
| served | GROUP `211 300 1 300`; 430/423 article reclaimed; OVER 423; NEWNEWS lists none; re-POST 441 duplicate |
| tight store (same run) | as section 4, and **charge-reserved 376 to 188** after the reclaim |

The `status` reclaim line reports `freed-octets=192190`, 300 fewer than the
verb's 192,490: it is the payload measure (the D13 reclaim state sums the
payloads less their tombstones), the verb's is the record measure, and each
record's payload length head is one octet shorter for the tombstone. Both
are exact for what they name.

## 6. Certification

persvati, w25 toolchain, 2 jobs, 300 s, `--affected-by` books/store-maintenance-reserve,
books/store-compact-verb, books/store-reclaim-pack, books/native-live-status,
books/store-budget-article:

- r1 run-20260926T015114Z-c005, **certify-20260926T015147Z-3864087**
  (manifest committed): passed, 8 books, 0 failures: books/native-live-status
  3.8 s, books/store-compact-verb 1.3 s, books/store-maintenance-reserve
  1.3 s, books/store-reclaim-pack 3.8 s, tests/acl2/native-live-status-tests
  2.1 s, tests/acl2/store-compact-verb-tests 1.6 s,
  tests/acl2/store-reclaim-holders-tests 1.7 s,
  tests/acl2/store-reclaim-pack-tests 1.5 s. The new test book was not yet a
  Makefile root.
- r2 run-20260926T015527Z-3147, **certify-20260926T015552Z-3901153**
  (manifest committed): tests/acl2/store-maintenance-reserve-tests passed,
  1.5 s, after it and books/store-maintenance-reserve were added to the
  Makefile roots.
- hbox (w28): `tools/certify_books.py --incremental` over the default
  profile's roots at each image (setup.sh), cert rc 0, 369 books.

Every book under 10 s.

## 7. What is not done, and why (PKT-263)

PKT-263 (for the next continuation; nothing here needs ember):

- **Holders from feed state, FNBS rows and BP obligations (step 3).**
  `fn-rcl-store-holders` reads the Store's consumer projection only; feed
  progress and FNBS rows live outside the Store namespace the offline verb
  opens. The obstruction: the verb would have to open the BP journal
  (a separate namespace and lock) read-only and hand its held Message-IDs to
  ACL2; no such bounded offline observation exists yet.
- **A per-article release verb (step 4).** The reservation it needs is in
  place (a `:release` record is always admissible on a reserved store); the
  verb is not: the retention ledger's `:release` event releases only
  `:forward` obligations (books/store-node-retention.lisp), so a per-article
  archive release needs its own event kind or the article pin's matching
  release arm, and the node invariant that keeps every bound article under
  a live pin (`fn-node-statep`).
- **The replay proof (step 5)**, the open of the reclaiming pack equals
  `fn-rcl-reclaim-state` of the open of the history: PRF-088's open step,
  not attempted. The charge release is therefore proved at the event level
  (`fn-rclp-freed-charge-account`) and observed at the ledger (section 5),
  not proved over the replayed ledger.
- **Guards of books/store-reclaim-pack (step 6)**: still `:verify-guards
  nil`, called through the `:program` wrapper `fn-store-reclaim-decide`.
- **N=5,000 (step 7)**: owed; chained packs (pack-chain-serve) are not on
  dev at 9d687b49.
- The free-octet observation is environmental: a concurrent writer can
  take the space between the observation and the write; the write then
  fails before the selection, which the publication cuts cover.
