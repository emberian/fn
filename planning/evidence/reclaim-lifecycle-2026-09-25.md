# Lane reclaim-lifecycle, 2026-09-25 (STO-017, PRF-119, SCN-065, PKT-169)

Dev lane `lane/reclaim-lifecycle` from dev 483987b1, Claude Opus 5.5, under
the Fable mandate (section 8, the reclaim and reservation paragraphs).
Continues reclaim-d13 and reclaim-host (the rule, the tombstone, the
served 423/430 and the D25 verdict), whose part two left `store reclaim`
designed (design B, reclaim through the compaction pack) and unbuilt.

## 1. What now works

`fn operator CONFIG store reclaim [--dry-run]` and
`fn operator CONFIG retention set RULE`. An operator authorizes a release
(the rule), runs the verb, and the released articles' payload octets leave
the disk when the older pack generation is unlinked; the committed-record
octets admission counts fall by the same amount; the store survives a kill
at every step; a reclaimed article is served 430/423, skipped by OVER and
NEWNEWS, and its re-POST is refused as a duplicate.

`retention set` was in the admin grammar (books/native-admin.lisp) but no
operator command reached it: `fn-nop-parse-command` routed only group,
capacity, peer, bp-boundary, bp-route, policy and control. It now routes
`retention` as well (books/native-operator.lisp), with a witness in
tests/acl2/native-operator-tests.lisp.

## 2. The assurance chain

native entry `fnn-command-reclaim` (host/native/checkpoint.lisp) ->
`fnn-reclaim-observe` calls host/checkpoint-host.lisp
`fn-store-reclaim-decide` -> executed ACL2 subject `fn-rclp-decide`
(books/store-reclaim-pack.lisp) over the replayed Store state (holders
`fn-rcl-store-holders`, verdicts `fn-sn-verdicts`, articles), the
configured rule `fn-rcl-config-rule` and the clock stamp
`fn-record-stamp-of-observation` -> representation: the committed history
as canonical octet events, the same octets the compact verb packs ->
refinement: `fn-rclp-event-decodes-to-the-tombstoned-record` (the rewritten
octets decode to the record with only the payload replaced),
`fn-rclp-freed-is-the-admission-count` (the record codec is canonical, so
the admission gate's `fn-sbud-record-octets` falls by the octets removed)
-> maintained relation: the pack's event list stays a summary event list
(`fn-rclp-events-keep-the-summary-shape`, an equality), so the ordinary
open replays it through the one Store decoder -> behavioural theorems:
`fn-rclp-events-never-touch-a-held-article`,
`fn-rclp-events-keep-every-other-kind`,
`fn-rclp-a-reclaimed-event-stays-reclaimed`,
`fn-rclp-keep-forever-writes-nothing` (and PRF-088's served and D25
theorems over the tombstone) -> observed result: section 5.

Which entry establishes the relation: the ordinary `store compact` (the
selected pack covers every committed record and no transaction file is
left); `fn-rclp-decide` answers `:compact-first` otherwise and the host
runs the compact steps before asking again. Which transitions preserve it:
publication and selection of the reclaiming generation (the pack
publication and marker machines, unchanged) and retirement of the older
generation (`fn-cprt-retire-plan`, unchanged).

## 3. Theorems (books/store-reclaim-pack.lisp, PRF-119)

Subject: `fn-rclp-decide`, called by host/checkpoint-host.lisp
`fn-store-reclaim-decide`, called by host/native/checkpoint.lisp
`fnn-reclaim-observe`.

- `fn-rclp-decide-publishes-the-rewrite` (rule-classes nil): a :reclaim
  answer has steps `*fn-rclp-steps*`, is not a dry run, the history is one
  selected pack, some record is rewritten, and the summary octets it hands
  the host are `fn-cc-encode` of `fn-cc-capture` of `fn-rclp-events` of the
  committed records.
- `fn-rclp-events-keep-the-summary-shape`: `(equal (fn-cc-octet-event-listp
  (fn-rclp-events events ctx) s l u) (fn-cc-octet-event-listp events s l
  u))`, no hypothesis.
- `fn-rclp-event-decodes-to-the-tombstoned-record`: under
  `fn-rclp-rewrites-p`, the new octets decode, to `fn-rclp-tombstoned` of
  the old record: payload `fn-rcl-tombstone-of`, the ten other fields equal.
- `fn-rclp-events-never-touch-a-held-article`: if an obligation of
  `fn-rcl-obligations h` names the I-th event's article, or its verdict
  needs the payload, or the rule is keep-forever, the I-th event is the same
  octets.
- `fn-rclp-events-keep-every-other-kind`: an event that is not a legacy
  article record (an accepted-statement composite, a keyring snapshot, a
  verdict, a retention, consumer or topic event) is the same octets. Signed
  composites and the key and policy evidence their replay needs are kept
  byte for byte.
- `fn-rclp-a-reclaimed-event-stays-reclaimed`: a rewritten event is never
  rewritten again, under any later context; `fn-rclp-events-idempotent`
  under the same context.
- `fn-rclp-freed-is-the-admission-count` and `fn-rclp-freed-octets-account`.
- `fn-rclp-keep-forever-writes-nothing` (rule-classes nil): under the
  default rule the answer is never :reclaim.
- books/native-operator.lisp: `store reclaim` is exactly the :reclaim
  native action and `store reclaim --dry-run` exactly :reclaim-dry-run
  (four keystones, cloned from the checkpoint verb's pair).

Teeth (tests/acl2/store-reclaim-pack-tests.lisp, over the owner fixture's
completed store with three articles): the history is a summary list and
all three records are rewritten under released-by-all-holders; the
rewritten record decodes to the tombstoned record and differs from the
original; a tooth with keep-forever (no rewrite, no tombstone); summary
shape kept, with a tooth on a truncated event; idempotence; each disjunct
of the held keystone (a BP obligation naming the article, an
`:unverified` verdict, keep-forever) keeps the event, and with none of
them the event changes (must-fail); every non-record event is unchanged;
the freed octets equal the encode-length difference and are positive; the
decision reclaims when packed, answers the dry run with the same
Message-IDs, answers `:compact-first` when not packed and `:none` under
keep-forever. native-operator-tests: witnesses and a must-fail per
hypothesis for the four operator keystones and for `retention set`.

## 4. Certification

persvati, w25 toolchain, 2 jobs, 300 s, `--affected-by books/store-reclaim-pack
--affected-by books/native-operator` (8 books; 179 from the cache):

- r1 run-20260926T001438Z-1203, certify-20260926T001459Z-2981001 (manifest
  committed): books passed; tests/acl2/store-reclaim-pack-tests failed
  (a `defconst` over the record codec calls an attachment; the constants
  became macros).
- r2 run-20260926T004428Z-eb41, **certify-20260926T004545Z-3272949**
  (manifest committed) at 9c5baa89: passed, 8 books, 0 failures. Per book:
  books/store-reclaim-pack 3.5 s, books/native-operator 5.0 s,
  tests/acl2/store-reclaim-pack-tests 1.5 s, tests/acl2/native-operator-tests
  1.6 s, every book under 10 s.
- hbox (w28 toolchain): `tools/certify_books.py --incremental` over the
  default profile's roots certified the image closure at each image
  (cert rc=0, 364 books); the final image is at 9c5baa89 (section 5).

Not guard-verified: every function of books/store-reclaim-pack is
`:verify-guards nil`, called through the `:program` wrapper
`fn-store-reclaim-decide`, as its siblings in books/store-compact-verb and
books/checkpoint-compaction are. Open.

## 5. Native (hbox, developer image at 9c5baa89)

Image: build/fn-host-developer.core
b6fc8d027f144e5f14430e239593f5d03f08ae9a5e5ba50d23b79dfc93202384,
build/fn-host.core c60b9ae228b70fa6b634424edbdf28d2aa2b8c22560e4a3b63d1608fb8494a40.
Harness tests/reclaim_lifecycle_native.py (a client and harness only; every
decision is the image's), scratch /tank/fn/scratch/reclaim-lifecycle, under
`systemd-run --user -p MemoryMax=24G`. Logs (JSON lines):
logs/n300d.jsonl sha256 05460ac4b729cd25896cdb9e15c81ce9c8f2a64d59579623693b92ae61761766.

N=300 articles of 512 octets in fn.letters, profile default with
max_record_octets 262144, max_article_octets 131072, 16 groups, history
bound 64 MiB:

| Step | Observed |
| --- | --- |
| keep-forever `store reclaim` | exit 0, `reclaimed=0`, nothing written (no release: the bounded answer) |
| `retention set release-after 1`, `--dry-run` | accepted; `reclaimed=0` (every article too recent) |
| `retention set released-by-all-holders`, `--dry-run` | `would-reclaim=300 freed-octets=192490`, nothing written |
| before `store compact` | 307 files, 329,820 octets |
| `store compact` | `records=300 generation=0 reclaimed=300` (the ordinary verb) |
| before reclaim | 9 files, 318,210 octets; bytes-used=316750 of 67108864 |
| `store reclaim` | exit 0 in 3.0 s, `reclaimed=300 freed-octets=192490 generation=1 retired=1` |
| after | 9 files, 125,720 octets (exactly 192,490 fewer); bytes-used=124260 (exactly 192,490 fewer); `status`: reclaimed=300 |
| rerun | `reclaimed=0`, the same pack bytes |
| served | GROUP `211 300 1 300` unchanged; ARTICLE by id `430 article reclaimed`, by number `423 article reclaimed`; OVER `423`; STAT `430`; NEWNEWS lists no reclaimed article; re-POST of the original bytes `441 ... already stored here` (D25 duplicate) |

The inodes: 300 transaction files became one pack at `store compact`
(packing); the reclaim replaces one pack generation by a smaller one, so it
returns octets, not inodes. Both are reported with the verb that did them.

Cut campaign, one copy of the compacted store per cut, 18 cuts:
kill (SIGSTOP at the cut, then SIGKILL) at candidate-file, candidate-link,
candidate-directory, selection-file, selection-replace,
selection-directory, pack-retire-unlink, pack-retire-directory; kill and
EIO at reclaim-state-checkpoint-unlink, reclaim-state-checkpoint-directory,
reclaim-pack-published, reclaim-pack-selected, reclaim-retired. Every copy
reopened (`status` exit 0), before the selection with the full history
(reclaimed=0) and from selection-replace on with the reclaimed one
(reclaimed=300); every EIO exited 3 (uncertain), every rerun exited 0, and
all 18 ended with the clean run's pack bytes.

The first campaign (logs/n300c.jsonl
a6bebc59eeca9ce53288f92182e6e548eed66bd45c29d6ced41b2416081e5aca) found a
defect, fixed at 9c5baa89: after a cut between the selection and the
retirement the rerun had nothing to rewrite, answered `reclaimed=0`, and
left the older generation, which still held every released payload, on
disk. `fn-rclp-decide` now answers `:resume-retire` then, and the rerun
retires it (`reclaimed=0 retired=1`); a witness and a tooth are in the test
book.

## 6. Findings

**F1, fixed: the served article POST ignored the history bound.**
host/native/owner.lisp `fnn-owner-preflight-publication` says an article's
budget is part of its prepare, and the prepare gate `fn-sbud-prepare`
(books/owner-store-budget.lisp) compares the transaction count only; the
committed-history octets (`max_history_octets`) were checked for every
other record kind and never for an article. On a store with a 300,000-octet
history bound, 400 POSTs of 1 KiB were all accepted (logs/n300.jsonl, the
first run), and the next open faulted: `fault operator status transaction
recovery input exceeds configured bound`. The store could not be opened.
Classification: implementation. Fix: host/owner-host.lisp
`fn-owner-article-budget` hands the prepare the profile's budget only when
`fn-sbud-verdict-at` admits one more article record by both gates, else 0,
which makes the prepare the identity (`fn-sbud-prepare-refuses-at-budget`)
and the word `:unaffordable`. Observed after the fix: the 151st POST is
refused `441 posting failed; the store has no capacity for this article`
at bytes-used 235,018 of 300,000, and the store opens. Not changed: the
developer `store post` path, and no theorem yet states that the served
article prepare respects the history bound (the gate's keystones are
parametric in the budget; the new composition is host `:program` code
over two ACL2 functions).

**F2, open (PKT-169): a store refused for history headroom can never be
compacted or reclaimed.** Admission refuses an article when committed octets
B plus the article ceiling (65,538) pass the history bound H. `store
compact` refuses `temporary-space` unless the files present plus the new
pack fit H (books/store-compact-verb `fn-cverb-decide`), about 2B <= H, and
`store reclaim` needs a compacted history first and checks the same way.
So a refused store (B > H - 65,538) compacts only if H < 131,076, below
every admissible H (the minimum record ceiling is larger). Observed: the
tight store refuses `compaction refused: temporary-space` for both verbs,
exit 1, nothing written. The mandate's reservation invariant is therefore
violated by construction: maintenance needs up to H/2 of headroom and
admission reserves none.

Packet PKT-169 (for ember). Constraints: H bounds the open's replay input
(the selected pack plus suffix), not the disk; the compaction's temporary
space is disk. Default proposal: separate them. The temporary-space check
becomes "the new pack fits H" (what the open will read), and the disk peak
(old plus new) is a named operator requirement reported by `--dry-run`,
not a profile rule; admission reserves, across Store and BP namespaces,
one configuration record (so `retention set` can always be published) and
the cleanup debt of a rotation. Rejected alternative: admission reserves
H/2 for the maintenance copy (halves every store's usable history).
Affected: books/store-compact-verb (`fn-cverb-decide` and
`fn-cverb-pack-fits-the-profile-budget`), books/store-reclaim-pack, the
admission gate (books/store-budget `fn-sbud-verdict-at`) and the BP
journal's rotation reservation. What continues without it: everything
here, on stores below half their history bound.

**F3: `retention set` was unreachable from the operator.** Fixed (section 1).

**F4, the retention charge is not released.** The article record's charge
and its archive pin are kept (`fn-rclp-tombstoned` keeps every field but the
payload), so `charge-reserved` does not fall: `status` before and after
shows `charge-reserved=600`. Releasing an archive undertaking is the node
invariant change spike/storage found (`fn-node-statep` keeps every bound
article under a live pin); it is D03's release, open.

## 7. What is not done, and why

- **N=5,000.** One pack holds at most 4,096 events and 4 MiB
  (`*fn-cc-max-events*`, `*fn-cc-max-octets*`); a history past it needs
  chained packs, held on the pack-chain-serve fix (the mandate's
  reconciliation). The scale run is at N=4,000 (section 8), inside one pack.
- **Holders from feed state, FNBS rows and BP obligations** are not read:
  the BP journal is a separate namespace the offline Store verb does not
  open. The consumer reading stays reclaim-host's conservative one (any
  lagging consumer holds every article; E2's no-pin profile would hold
  none, lane consumer-e2). A reader pin needs no durable form for an
  offline verb (reclaim-host section 5).
- **A per-article release verb.** The release here is the rule
  (released-by-all-holders or release-after). A per-article release needs a
  durable release record and the archive-pin change of F4.
- **The replay correspondence of the reclaimed record** (the open of the
  reclaiming pack equals `fn-rcl-reclaim-state` of the open of the history)
  is PRF-088's open step; native evidence: the served view and `status`
  after every cut.
- **The maintenance reservation** (item 2 of the brief): the finding and
  packet F2, not an invariant.
