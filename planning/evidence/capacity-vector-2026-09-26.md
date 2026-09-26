# Lane capacity-vector, 2026-09-26 (PRF-138, STO-020, SCN-081, PKT-323)

Dev lane `lane/capacity-vector` from dev 8ca933b1 (dev 427125e6 merged at
1702d668), Claude Opus 5.5, on gpt-6's review of wave 2
(planning/review-2026-09-26-gpt6-wave2.md section 3, "the composed
statement" and "Item 3: maintenance needs resources, not permission";
section 8's second outcome). It builds on PRF-129 (reclaim-lifecycle-2) and
cites PRF-086, PRF-123, PRF-126 and PRF-129 without re-proving their
arithmetic.

## 1. What an operator can now do

- Fill a store until ordinary admission refuses (`441 ... no capacity`) and
  still complete what it already promised: an open BP forwarding obligation's
  receipt writes its release record into the full store (exit 0,
  `pinned=no`). Every open undertaking keeps its own release, and the
  maintenance release is kept besides.
- Authorize the content release (`retention set`) even when administration
  has used the configuration namespace: the last `max-config-generations`
  generation is kept for it; any other configuration record is refused it by
  name (`max-config-generations`).
- Release, compact and reclaim that full store across every publication,
  selection and retirement cut, recover, and POST again (240).
- Read the vector: `status` prints `maintenance-reserve octets=R
  transactions=N debt=D held|short`.

## 2. The composed statement and the vector (books/store-capacity-vector.lisp)

The vector, over the values the owner carries:

    committed transactions + (DEBT + 1)          <= T
    committed record octets + (DEBT + 1) * 4096  <= H   (and the release fits R)

as `fn-cvec-roomp profile used bytes debt` = PRF-129's `fn-smr-roomp` at
(used + debt, bytes + debt * 4096): the profile's gate admits DEBT + 1
release records in turn. DEBT is the completion debt, the open forward
undertakings, each owing one `:release` record (an `:undertake` record pins a
`:forward` obligation, a `:release` record removes the one it matches:
books/store-node-retention.lisp `fn-snrt-retention-of-apply-retention-event`).
The components the review names, kept apart (specs/storage.md "The capacity
vector (STO-020)" has the table):

| Component | Here |
| --- | --- |
| Encoded history octets | H, at the actual unframed record octets (`fn-sbud-record-octets`) |
| Transaction slots | T, a lifetime budget (compaction and reclaim keep the count) |
| Namespace slots | the transaction namespace is T above; the configuration namespace keeps its last generation for the retention rule (books/store-capacity-config.lisp) |
| Retained payload charge | pre-paid: a pin's charge includes its release unit; `fn-cvec-release-never-raises-the-charge` |
| Completion debt | DEBT releases, `fn-cvec-record-debt`, carried as (K . DEBT) |
| Maintenance debt | the one maintenance release (PRF-129) |
| Physical workspace | the disk: an environmental assumption (section 5) |

Theorems (PRF-138):

- `fn-cvec-admitted-history-keeps-the-vector` (the composed statement): if the
  vector holds at (used, bytes, debt), debt natural, and every record of a
  history of mixed kinds is admitted at its prefix by the gate the host calls
  for its kind (`fn-cvec-history-admittedp`: an article by
  `fn-cvec-article-verdict-at` at its own counts with a u32 charge, PRF-126's
  premise; every other kind by `fn-cvec-verdict-at` and within its
  publication ceiling; a release only against an open debt), then the vector
  holds at (used + len, bytes + `fn-sbud-record-octets` records, the
  history's debt) and `fn-profile-replay-within-boundp` holds at the actual
  committed octets: the bound the open checks per file
  (host/native/io.lisp `fnn-durable-records`). `fn-cvec-admitted-history-from-init`:
  the same from (0, 0, 0) under any admitted profile.
- `fn-cvec-record-keeps-the-vector`: one committed record of any kind.
- `fn-cvec-admission-keeps-the-vector`, `fn-cvec-release-keeps-the-vector`,
  `fn-cvec-prepare-keeps-the-vector` (the served POST / BP transit prepare),
  `fn-cvec-article-verdict-keeps-the-vector` and
  `fn-cvec-article-verdict-keeps-the-vector-at-producer-width` (developer
  `store post`), `fn-cvec-admitted-profile-starts-held` (init),
  `fn-cvec-profile-upgrade-keeps-the-vector`, `fn-cvec-roomp-antitone-in-octets`
  (reclaim), `fn-cvec-roomp-is-within-the-profile`.
- `fn-cvec-roomp-discharges-every-debt`: where the vector holds at DEBT, the
  j-th release (j <= DEBT) is admitted after j releases of at most 4,096
  octets, in any order. Full never means a promise the store cannot discharge.
- `fn-cvec-roomp-without-debt-is-the-reserve`,
  `fn-cvec-verdict-without-debt-is-the-reserve-gate`: with no open undertaking
  the vector is PRF-129's and the gate differs only for `:undertake`, which
  must keep its own release.
- `fn-cvec-debt-extend-is-the-record-debt` (the carried cache is the
  history's debt), `fn-cvec-admit-forward-adds-one-debt`,
  `fn-cvec-release-forward-removes-one-debt` (the ledger's `:forward` pins
  move as the debt does, per transition).
- books/store-capacity-config.lisp:
  `fn-cvec-config-publication-keeps-the-release-generation`: a configuration
  record other than the retention rule, authorized under
  `fn-cvec-config-generations`, is accepted only below max-config-generations.

Producers covered: articles from every producer PRF-123/PRF-126 cover (their
charge fits u32). Every other kind enters as the premise "within its
publication ceiling", which its codec's maximum bounds; the signed composite
(`:accepted-statement`) and peer-carried records are OUTSIDE the
producer-width proof and are covered here only through that premise and their
publication checks, not by a producer theorem.

## 3. The assurance chain

Native entry host/native/owner.lisp `fnn-owner-attempt` (served POST, BP
transit) and `fnn-owner-preflight-publication` (every other served kind,
BP admission's retention included) -> host/owner-host.lisp
`fn-owner-publication-verdict` (line 463, `fn-cvec-verdict-at`),
`fn-owner-prepare` (line 622) and `fn-owner-prepare-buffer` (line 697)
(`fn-cvec-article-budget-for` handed to `fn-pcar-sbud-prepare`), the debt
from `fn-owner-record-debt` (line 447, `fn-cvec-debt-extend` of the carried
(K . DEBT), reset with the octets at `fn-owner-install-profile`); developer
`store post` host/store-node-host.lisp lines 74 and 88
(`fn-cvec-verdict-at`, `fn-cvec-article-verdict-at` at
`fn-cvec-record-debt`); configuration: host/store-node-host.lisp line 186
(`fn-cvec-config-generations` handed to
`fn-native-admin-publication-authorize`, reached from host/native/admin.lisp
`fnn-admin-authorize`) -> executed subjects above -> representation: the
committed octets as (K . SUM) (`fn-sbud-bytes-used-is-kernel-sum`) and the
debt as (K . DEBT) (`fn-cvec-debt-extend-is-the-record-debt`) -> maintained
relation `fn-cvec-roomp` -> the theorems of section 2 -> section 4.

Established at init (`fn-cvec-admitted-profile-starts-held`); at open it is
the history's (`fn-cvec-admitted-history-from-init` over the records the
open replays, fn-cpo-open-observed / fn-sn-recover-from-checkpoint rebuilding
the carried sums). Preserved by every admitted record (the served POST
through `fn-cvec-article-budget-for`, `store post`, BP ingress's retention and
the other served kinds through `fn-cvec-verdict-at`, a release against an open
debt), by reclaim (octets only fall) and by a profile upgrade. A release at
debt 0 consumes the maintenance release (PRF-129's rule); a store filled
before this lane may print `short`.

`status` (books/native-live-status.lisp line 401) computes the debt with
`fn-cvec-record-debt` over the committed records, offline and live: a walk
per status query, not per admission.

## 4. Native lifecycle (SCN-081, hbox)

tests/test_native_capacity_vector.py, a harness only; scratch
/tank/fn/scratch/capacity-vector/native-r2, `systemd-run --user --scope -p
MemoryMax=24G` (tools/hbox_native.sh). Images at c62e8a2b: developer
3fff1c14ee52000c3ab6acaacd065a8e4152aa23ba0ec2ade0a4a9c4b4b357ea (core
01c6fc934af49cb0a2a0038cab79142066368cd517a4361b7acb5b4d33dace10),
production f1fcb782bec56ba136d875f7806d94395929def4affe1514cdee9bb5cea849b7
(core 2cec8f9db91fb6daab959e75b68d6bcd6959a5021a0f9b863a36c4b731201547).
The lifecycle log at 2d27051d (the same images, `--no-build`):
logs/test-tests.test_native_capacity_vector.log sha256
432809841bc2b45bc3a07b4e6df15ee5d5fb916293b41479e9d24a2e4cebe4b9, OK.
Store: H 300,000, T 4,096, record 262,144, 1 KiB articles.

| Step | Observed |
| --- | --- |
| undertake (BP forward obligation) | exit 0; `maintenance-reserve octets=8192 transactions=2 debt=1 held` |
| fill | 185 POSTs 240; the 186th `441 ... no capacity` at bytes-used 290,332 (the article figure, about 2,530, plus two releases does not fit; PRF-129 alone keeps one release and would have admitted about two more); transactions 187 of 4,096; `debt=1 held`; 192 inodes, 298,539 octets, du 782,336 |
| complete: BP exchange + `bp-obligation receipt` | sender 0, receiver 0, accepted=1; receipt exit 0 in the full store; `status=receipted pinned=no`; bytes-used 290,653 (+321, the release record); `debt=0 held` |
| release | `retention set released-by-all-holders` exit 0; dry-run names the articles |
| `store compact`, 8 stop cuts | 6 reached: every copy reopens (`status` 0), reruns exit 0, converges to the clean pack; the 2 pack-retire points are not reached by a first compaction (it retires nothing), the rerun is refused `already-compact`, exit 1 (unexercised, not counted) |
| clean compact | exit 0; 194 inodes to 8, octets 298,957 to 291,712, du 790,528 to 319,488 |
| `store reclaim`, 18 cuts (8 stop, 5 kill, 5 EIO) | every copy reopens, EIO exits 3, every rerun exits 0, all 18 converge |
| clean reclaim | exit 0; octets 291,712 to 78,238, du 319,488 to 102,400 (8 inodes); bytes-used 290,653 to 77,179; charge-reserved 373 to 187; `debt=0 held` |
| reuse | three POSTs, each 240; bytes-used 81,886; 12 inodes, du 335,872 |

The same run (r2, c62e8a2b): tests.test_native_profile_namespace OK (the
reserved generation: `group create` refused `max-config-generations` at the
last generation, `retention set` accepted there, the next refused; log
2597638107e471d6e7374bde6db934682b3df87ea2762eec99e9f33f76130d8c),
tests.test_bp_app_native OK (e3861eb91211e4eeb6eac3e3f6f3a0345209d650f2997d57f5e47358df783080),
tests.test_native_operator_verbs.NativeOperatorCapacityTests OK (5,
aaf76f3a828f6e874dac0cb6b092ed9b2246b8b9f0231494dad94ebb4cfb5294).
tests/native_owner_consumer_raw.lisp (reads `fn-cvec-verdict-at` by name):
"native owner consumer boundary passed" on the laptop.

Failures, classified:

- r1 (c1f8ef37): harness (a keyword collision in the log line). Its fill
  stopped at the transaction budget (126 used + debt 1 + maintenance 1 =
  the development profile's 128): the transaction component binding, and T
  is a lifetime budget no maintenance returns, so r2 sets T = 4,096.
- r1: tests.test_bp_obligation_native
  `test_kill_between_attempt_and_outcome_then_recover_committed` exits 1
  where it expects 0 or 3 after the dead contact. It fails identically on
  the qualified wave-2 candidate's developer image
  (/tank/fn/gates/qual-b6759850-20260926/build/fn-host-developer): not this
  lane (the BP exit table; handed to the BP lanes).
- r2: harness: the two unreached compaction stop cuts (above).

## 5. Workspace and the disk

The pack a compaction or reclaim writes is bounded by the compaction unit
(`*fn-cc-max-octets*`), and it is checked against the free octets the host
observes (PRF-129: `fn-cverb-pack-fits-the-disk`, `fn-rclp-pack-fits-the-disk`).
That observation is not ownership. ENVIRONMENTAL ASSUMPTION: no concurrent
writer takes the observed space before the pack is written. When it fails,
the write fails before the selection: the EIO cuts above show the outcome
(exit 3, the store reopens, the rerun converges): refused or uncertain,
never torn. No `encapsulate` is added: no theorem here concludes that a pack
write succeeds. A real preallocation is PKT-323 item 3. Each compaction
repacks the whole history within the unit: bounded, not incremental;
chained packs (lane/bounds-p5, not on dev) make it incremental and would
change the compaction numbers above, not the vector.

## 6. Certification

persvati, w25, 2 jobs, 300 s, `--affected-by` books/store-maintenance-reserve,
store-budget-article, store-reclaim-pack, store-capacity-vector,
store-capacity-config, native-live-status:

- r1 run-20260926T072241Z-47d6: green, 9 books, but store-capacity-vector
  74.9 s and store-capacity-config 27.6 s (one event each: a cons lemma that
  opened every event encoder, and a keystone proved in the full theory);
  fixed in 35c8235c; its manifest is not cited.
- r2 run-20260926T073035Z-848d, **certify-20260926T073035Z-2680334**
  (committed): passed, 25 books (after the dev merge), none over 10 s:
  books/store-capacity-vector 2.57 s, tests/acl2/store-capacity-vector-tests
  1.42 s, books/store-capacity-config 1.02 s,
  tests/acl2/store-capacity-config-tests 1.12 s, books/native-live-status
  3.72 s, the worst books/owner-invariants 8.20 s.
- Proof development in hbox `proof_repl` sessions (persvati's slot pool was
  held by idle sessions of other lanes).
- `make check-lane`: see the LANEDUMP (the ratchet's one failure,
  books/bp-node-job-offer 11.6 s on hbox, is dev's).

Teeth: tests/acl2/store-capacity-vector-tests.lisp, over packet 1's profile
with T = 8: for each keystone a reachable witness with no octet to spare and
the conclusion failing when each hypothesis is dropped (the vector, J within
the debt, octets within J * R, natural J and B2, the verdict, the kind, the
ceiling, the open debt, narrowness, the asked counts, a lowered H, a release
at debt 0, a non-admitted profile), and the comparison with PRF-129 (an
undertaking PRF-129 admits at H - 2R the vector refuses; an article PRF-129
admits with a debt open the vector refuses, budget 0).
tests/acl2/store-capacity-config-tests.lisp: the retention rule takes the
last generation, an ordinary record is refused it by name and accepted below
it, and the profile's own bound (the pre-PRF-138 host argument) accepts the
ordinary record at the last generation. Not toothed: the `natp debt`
hypothesis of the two history theorems (the carried debt is natural by
construction; its redundancy was not proved, so it stays).

## 7. What is not done (PKT-263) and the packet (PKT-323)

Not reached from reclaim-lifecycle-2's list (stay under PKT-263): holders
from feed state, FNBS rows and BP obligations (the obstruction is unchanged:
a bounded offline read of the BP journal, bounded by the node profile's
ROWS and OCTETS, bp-lifecycle-4); the per-article release verb; the replay
proof of the reclaimed record; guards of books/store-reclaim-pack. Finding
for the next lane: the vector already reserves the transaction and octets a
per-article release record needs, so that verb needs no new reservation, only
its event kind and the node invariant.

Also open: the history-level equality of `fn-cvec-record-debt` with the
ledger's `:forward` pin count is proved per transition, not over replay.

PKT-323 (for ember; everything above continues without it):

1. Trace: an open forward undertaking now holds one release record (4,096
   octets, one transaction) of H and T. Default taken: the release ceiling,
   as PRF-129 does. Rejected alternative: charge the release record's exact
   length (321 octets observed) at undertake time; cost: the ceiling is the
   codec's bound, the exact length depends on the eventual evidence string.
   Affected: admission of every BP-heavy store (185 articles where PRF-129
   admitted about 187 in the run above).
2. Trace: the configuration namespace keeps its last generation for the
   retention rule; ordinary administration gets max-config-generations - 1.
   Default taken. Rejected alternative: configuration-namespace compaction
   (no such verb). A profile upgrade raises the bound.
3. The disk: environmental assumption (section 5). Rejected alternative: a
   real preallocation (fallocate of the pack's size under a named platform
   contract in books/assumptions.lisp); cost: a new trusted contract, the
   BP/assumptions closure recertified on hbox, and the file-system support
   question on ZFS.
