# Measured scale profile (D16)

Every number here was measured by `tests/bench/generate.py` and
`tests/bench/measure.py` on one named machine, through the real acceptance,
replay and NNTP paths. Nothing here is a projection, a budget, or a capacity
claim for any other environment. Where a grid point did not complete, it says
so rather than extrapolating.

## Environment and commands

| Item | Value |
| --- | --- |
| Host | `hbox`, Linux 6.11.0-29-generic, 24 cores, 123 GiB RAM, co-tenant with another user's build |
| ACL2 | 8.7, `/tank/fn/acl2-8.7/saved_acl2`, over SBCL 2.6.8; harness on CPython 3.12.7 |
| Books | the 28-book closure of `books/replay`, `host/store-host.lisp`, `host/store-node-host.lisp` and `host/reader-host.lisp`, certified in `/tank/fn/scale` from this lane's tree |
| Tree | `w3/scale-profile`, branched from `dev` at 9321344 |
| Load average | recorded per grid point in each JSON result; between 2.7 and 5.7 for the whole campaign |

    FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 python3 tests/bench/generate.py \
        --root build/stores/n256 --articles 256 --groups 2 --fanout 2 \
        --payload 1024 --seed 1 --profile scale --json build/bench/n256-gen.json
    FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 python3 tests/bench/measure.py \
        --root build/stores/n256 --articles 256 --seed 1 --runs 3 \
        --json build/bench/n256-meas.json

`tests/bench/grid.sh` and `tests/bench/grid2.sh` are the exact loops that ran;
every point writes its own `-gen.json` and `-meas.json` with the load average
at the time and the per-article timings behind each summary. The two scripts
overlap: `grid2.sh` ran the payload, group and stress points first, at load
average 4.8 to 5.7, and `grid.sh` re-ran those same ten point names afterwards
at load average 8.4 to 9.1, overwriting their JSON files. **Every figure in the
tables below is from the first pass**; the tables, not the files now on hbox,
are the record of what was measured. The accidental second pass is useful
evidence in its own right, and the next section reports it.

Reopen, GROUP, LISTGROUP, ARTICLE and the OVER-equivalent were measured five
times per point (three at N ≥ 256, where one reopen costs more than ten
seconds); the tables give min and median of those runs. Posting a store is one
run per point: its min and median are over that point's own articles, after
discarding the first quarter (at most eight) as warm-up.

## Replication at a higher load, and what it costs

The ten payload, group and stress points were measured twice by accident: once
at load average 4.8 to 5.7 and again, 75 minutes later, at 8.4 to 9.1 on the
same host with the same tree and the same seed. That is a free replication, and
it says which figures here are stable and which are not.

| Quantity | Second pass versus first, across the ten points |
| --- | --- |
| Reopen median | +15% to +21%, every point, median +20% |
| OVER-equivalent per article, median | +18% to +47%, median +23% |
| Post seconds per article, median | −41% to +46%, no consistent sign |

Three consequences, applied to the rest of this document:

- **Absolute reopen and reader latencies carry roughly ±20% between load 5 and
  load 9 on a 24-core host.** Quote them with that, not to three significant
  figures. The N-curve was measured at load 3.6 to 4.6 throughout, so its
  points are comparable with each other.
- **Median seconds per article is too noisy to compare across points.** It
  moved by up to 46% at an unchanged configuration. The min figure alongside it
  is the stabler statistic, and the post-throughput conclusions in this
  document rest on order-of-magnitude changes (0.11 s at N=16 against 0.94 s at
  N=256), not on the third digit.
- **The ratios survive.** The folding finding — the headline hostile-input
  result — is 4.106/0.670 = 6.1x in the first pass and 5.044/0.847 = 6.0x in
  the second. A ratio taken between two points measured in the same pass is
  what this campaign can defend; a single absolute number is not.

## What the grid could cover, and what the model forbids

The packet asked for a grid up to N=10000, G=1000, P=32 KiB. Two of those three
axes are bounded by ACL2 constants, not by configuration:

- **G ≤ 2.** `books/store-config.lisp:18` defines `*fn-store-groups*` as
  exactly `("fn.letters" "fn.test")`, and the two directions of the name/code
  mapping are proved inverse against that list. G=1000 is a model change with
  its own proof obligation, not a profile. The grid therefore varies G over
  {1, 2} and, separately, groups per article over {1, 2}.
- **P ≤ 32768.** `books/article.lisp:15` sets `*fn-article-max-octets*` to
  32768 and `books/frame.lisp:720` caps an encoded record at 65538 octets
  (`*fn-frame-max-store-payload*`). The grid reaches the payload bound exactly.
- **N** is the one host-owned bound. `tools/run_store.py`'s
  `MAX_TRANSACTION_COUNT` was 128. This lane adds a second *named* profile
  rather than raising that default: `fn-store-profile-scale-1`, 4096
  transactions, with `max_recovery_record_bytes` derived from the unchanged
  model record bound. A store carries its profile name in its checksummed
  configuration, so a development store and a scale store are distinguishable
  on disk and neither is read under the other's bounds. Control: the
  development profile's configuration checksum is `49dd591a5988…` both in
  `/tank/fn/gates/dev-9321344` (pre-change) and in this tree, so every existing
  store still opens; the scale profile's checksum is `37902a4bf826…`.

N=10000 was not reached, and neither was N=512: both N=512 and N=1024 ended in
a bridge timeout inside a single prepare call, which the next section reports
as a cliff of its own rather than as a missing measurement.

## Post throughput versus N (G=2, both groups per article, P=1024)

Seconds per article, steady state, and the peak RSS of the single ACL2 process
that serves both the node and the framing/identity wrappers.

| N | profile | post min (s) | post median (s) | articles/s at median | reopen min (s) | reopen median (s) | runs | peak RSS after reopen (KiB) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 16 | dev | 0.0581 | 0.1086 | 9.21 | 0.788 | 0.793 | 5 | 375,596 |
| 32 | dev | 0.0498 | 0.0877 | 11.40 | 0.846 | 0.881 | 5 | 390,188 |
| 64 | dev | 0.0412 | 0.1128 | 8.86 | 1.132 | 1.157 | 5 | 467,948 |
| 128 | dev | 0.0749 | 0.2751 | 3.63 | 2.673 | 2.718 | 5 | 1,002,472 |
| 256 | scale | 0.0471 | 0.9365 | 1.07 | 12.540 | 12.729 | 3 | 1,881,056 |
| 512 | scale | bridge timeout during prepare after ~35 min | | | | | | |
| 1024 | scale | bridge timeout during prepare after ~36 min | | | | | | |

The pessimistic figure, with its scope: reopening a 256-record store whose
articles are 1 KiB each took 12.7 s (median of three runs, 12.5 s min) on a
24-core Linux host at load average 4 to 5, with 256 KiB of article payload in
the store. Subtracting the ~0.75 s fixed cost of starting ACL2 and loading the
books, the replay term grows by 3.2, 3.2, 4.8 and 6.1 across the four
doublings from 16 to 256 records: faster than N², approaching N³.

**N=512 and N=1024 did not fail on wall clock. They failed on the bridge's own
per-call timeout.** Both runs raised `StoreError: ACL2 prompt timeout` from
`read_prompt` inside a single `fn-store-sn-prepare` call: N=512 after about 35
minutes of posting (10:56 to 11:31), N=1024 after about 36 minutes (11:31 to
12:07, at load average 9.4). `tools/run_store.py` allows a call
`ACL2_CALL_BASE_SECONDS` = 20 s plus 0.004 s per KiB of form, so a 9 KiB
prepare form gets 20.04 s; one prepare therefore crossed twenty seconds
somewhere between 256 and 512 committed articles, with the median prepare at
N=256 still under one second. That is the per-operation cliff of §1 arriving as
an outage rather than as slowness, and it is a sixth cliff in its own right:

**Cliff 6 — the bridge's refutation bound is a capacity bound.** The 20-second
per-call timeout is documented in `tools/run_store.py` as a refutation bound
rather than a budget, and it is the right shape: a store that cannot answer a
prepare in twenty seconds should fail closed. It did fail closed — the store
refused, the generator reported the failure, and the grid moved on. But it
means the effective transaction ceiling of this build is **not** the scale
profile's 4096; it is wherever one operation first exceeds twenty seconds, and
on this host with 1 KiB articles that is between 256 and 512. Raising the
timeout without removing the per-operation recognizer would only convert the
outage back into an unbounded wait.

Neither point produced a JSON result: `generate.py` re-raises and writes no
file on failure, so a partial curve is lost. A follow-up should record the
committed count and the per-article timings before re-raising.

## Reader latency versus N (same grid, milliseconds)

| N | GROUP min/median | LISTGROUP min/median | OVER-equivalent per article min/median | ARTICLE by Message-ID min/median |
| --- | --- | --- | --- | --- |
| 16 | 0.174 / 0.192 | 0.199 / 0.215 | 0.202 / 0.223 | 0.522 / 0.552 |
| 32 | 0.218 / 0.226 | 0.296 / 0.299 | 0.204 / 0.212 | 0.544 / 0.544 |
| 64 | 0.310 / 0.325 | 0.485 / 0.522 | 0.208 / 0.214 | 0.524 / 0.549 |
| 128 | 0.521 / 0.587 | 0.978 / 1.003 | 0.212 / 0.214 | 0.536 / 0.555 |
| 256 | 0.754 / 0.908 | 1.740 / 1.762 | 0.200 / 0.202 | 0.497 / 0.507 |

`OVER` is not a command this server has: `books/nntp.lisp:1297`'s
`fn-nntp-archive-keywordp` admits GROUP, LISTGROUP, LAST, NEXT, ARTICLE, HEAD,
BODY and STAT. The OVER-equivalent measured is what a client would have to do
instead — LISTGROUP followed by `HEAD n` over a bounded consecutive range (32
articles, or N if smaller) — reported per article. That substitution is the
measurement; it is not a claim that OVER exists.

GROUP and LISTGROUP grow linearly with N: a command that only needs the group
watermarks costs 4.7x more at N=256 than at N=16. ARTICLE retrieval does not
grow with N at this range because it is dominated by marshaling the reply
octets, not by the article scan; per-position figures in the JSON show the
newest articles answering in about 0.15 ms against 0.5 ms for the oldest, which
is the list scan becoming visible but not yet dominant.

## Payload size versus cost (N=64, G=2, both groups per article)

| P (octets) | post min/median (s) | bridge octets per post | reopen min/median (s) | ARTICLE min/median (ms) | OVER-equivalent per article (ms) | peak RSS after reopen (KiB) |
| --- | --- | --- | --- | --- | --- | --- |
| 512 | 0.0930 / 0.1824 | 5,889 | 1.076 / 1.113 | 0.342 / 0.355 | 0.201 / 0.202 | 465,824 |
| 1024 | 0.0412 / 0.1128 | 9,151 | 1.132 / 1.157 | 0.524 / 0.549 | 0.208 / 0.214 | 467,948 |
| 4096 | 0.1418 / 0.2774 | 28,716 | 1.693 / 1.721 | 1.895 / 1.989 | 0.304 / 0.313 | 480,032 |
| 16384 | 0.1676 / 0.4607 | 106,931 | 3.585 / 3.639 | 6.337 / 6.809 | 0.639 / 0.670 | 528,992 |
| 32768 | 0.2582 / 0.7451 | 211,256 | 6.281 / 6.363 | 13.545 / 13.678 | 1.050 / 1.058 | 594,600 |

Bridge expansion, measured: the slope from P=512 to P=32768 is **6.37 octets
written into the ACL2 pipe per payload octet**, with a fixed 2.6 KiB per post.
A maximum-size article costs 211 KiB of pipe text on the way in. Everything on
this axis is linear in P: reopen, ARTICLE and the enumeration all track it.

## Groups (N=64, P=1024)

| Configured groups | groups per article | post min/median (s) | reopen min/median (s) | GROUP min/median (ms) | LISTGROUP min/median (ms) |
| --- | --- | --- | --- | --- | --- |
| 1 | 1 | 0.1206 / 0.2002 | 1.125 / 1.159 | 0.334 / 0.336 | 0.513 / 0.550 |
| 2 | 1 | 0.1000 / 0.1927 | 1.101 / 1.130 | 0.237 / 0.249 | 0.314 / 0.323 |
| 2 | 2 | 0.0412 / 0.1128 | 1.132 / 1.157 | 0.310 / 0.325 | 0.485 / 0.522 |

No difference on this axis exceeds the run-to-run spread, and the axis cannot
be extended: the group table has two entries. A G-versus-cost curve needs the
model change described under G above before it can be measured at all.

## Stress campaign at the bounds (N=32, five runs each)

Each row is the maximum the model admits on that axis. The comparison row is
the same N with a 1 KiB random-body article and a 27-octet Message-ID.

| Case | post min/median (s) | bridge octets/post | reopen min/median (s) | GROUP min/median (ms) | OVER-equivalent per article (ms) | ARTICLE at number 1 (ms) | peak RSS posting / reopen (KiB) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| comparison (P=1024) | 0.0498 / 0.0877 | 9,155 | 0.846 / 0.881 | 0.218 / 0.226 | 0.204 / 0.212 | 0.538 / 0.562 | 568,736 / 390,188 |
| maximum payload, P=32768 | 0.2100 / 0.4385 | 211,264 | 2.929 / 2.951 | 0.237 / 0.251 | 1.021 / 1.025 | 14.421 / 14.524 | 833,700 / 453,356 |
| maximum Message-ID, 250 octets, P=4096 | 0.1169 / 0.1747 | 30,636 | 1.117 / 1.147 | 1.043 / 1.069 | 0.494 / 0.501 | 2.020 / 2.054 | 742,508 / 407,852 |
| pathological folding, 120 header lines, P=16384 | 0.1907 / 0.2515 | 118,238 | 1.919 / 1.945 | 0.239 / 0.288 | 4.045 / 4.106 | 7.591 / 7.808 | 696,556 / 420,832 |
| all three at once, P=32768 | 0.2173 / 0.4415 | 224,379 | 2.999 / 3.035 | 1.103 / 1.163 | 4.766 / 4.782 | 14.778 / 14.983 | 981,488 / 464,864 |

Three findings, stated pessimistically with their scope:

- **Header folding is the cheapest hostile input per octet.** At the same
  payload size (16 KiB), folding the header block to 120 continuation lines
  multiplied the OVER-equivalent enumeration from 0.670 ms to 4.106 ms per
  article, a factor of 6.1, while the post path barely moved. The cost is in
  the reader's per-retrieval parse, and it is paid on every HEAD.
- **A maximum Message-ID is a group-command cost, not a storage cost.** At
  N=32, a 250-octet Message-ID took GROUP from 0.226 ms to 1.069 ms and
  LISTGROUP from 0.299 ms to 1.347 ms — 4.7x and 4.5x — because the identifier
  is carried and compared everywhere the article is.
- **Nothing refused, nothing wedged.** Every bound-case post was accepted,
  every store reopened, and the worst peak RSS in the whole stress campaign was
  981 MB for a 32-article store of maximum-size articles: about 1 MiB of
  article payload behind roughly 600 MB of process growth over the ~380 MB
  empty-image floor.

The two padded-Message-ID rows deserve one caveat: the ARTICLE-by-Message-ID
probe in `measure.py` asks for the unpadded identifier, so for those two rows
that particular figure is a full-scan miss (430), not a retrieval. Their
ARTICLE-at-number figures are retrievals and are the ones quoted above.

## Cliffs, with the model-level cause

### 1. Whole-state revalidation on every served operation

`fn-accept-prepare` (`books/acceptance.lisp:662`), `fn-accept-complete` (`:695`)
and `fn-accept-recover` (`:720`) each begin `(if (not (fn-statep s)) s ...)`.
`fn-node-prepare` (`books/node.lisp:229`) and `fn-node-recover` (`:283`) do the
same with `fn-node-statep`, which calls `fn-statep` again at
`books/node.lisp:184` and adds its own `fn-subsetp` of binding identifiers
against `fn-article-msgids` of the whole article list at `:188`.

`fn-statep` (`books/acceptance.lisp:574`) is not cheap. It runs:

- `fn-article-listp` (`:326`), whose `member-equal` over a freshly consed
  `fn-article-msgids` of the tail is Θ(n²) conses and Message-ID comparisons;
- `fn-articles-freshp` (`:399`), which compares each article's memberships
  against every later article — Θ(n²) again;
- `fn-articles-below-nextsp` (`:410`), Θ(n·groups);
- and, inside `fn-articlep` (`:309`), `fn-octet-listp` over the **entire
  payload** of every article, Θ(n·P) octet checks.

So one operation on a store of n articles costs Θ(n² + n·P) before it does any
work. This is the situation `AGENTS.md` names directly: "No whole-state
revalidation on a served path. A recognizer over the entire store … must not
run per command or per byte; carry the invariant in state and prove it
preserved." (D3.)

The preservation theorems already exist — `books/acceptance-invariants.lisp:74`,
`:195`, `:201` and `books/node-invariants.lisp:8`, `:71` prove
`fn-statep`/`fn-node-statep` preserved by prepare, complete and recover. What
is missing is the *executable* consequence: the operations still recompute the
recognizer at run time instead of taking it as a guard.

### 2. Articles held by value in the logical state

`fn-state-articles` (`books/acceptance.lisp:545`) holds articles whose
`fn-article-payload` (`:264`) is the full octet list, and
`fn-article-from-pending` (`:623`) copies that payload into the committed list
on every acceptance. An ACL2 octet list is a cons chain: 32 KiB of payload is
32768 cons cells. The measurement: a 256-article store holding 256 KiB of
payload peaked at 1.88 GB of process RSS on reopen, and the 32-article
maximum-payload store (1 MiB of payload) peaked at 981 MB while posting. Peak
RSS is a high-water mark including replay's intermediate allocation, not
steady-state retention — but it is the number that decides whether a reopen
fits in memory.

### 3. Full-payload replay on every reopen

`fn-replay-loop` (`books/replay.lisp:142`) checks `fn-node-statep` before
applying each record (`:143`) and again on the result (`:152`), and
`fn-replay-apply-record` (`:113`) calls `fn-node-prepare` and `fn-node-complete`,
each of which runs `fn-node-statep` once more. That is at least four Θ(n² +
n·P) passes per record, summed over the history: Θ(N³ + N²·P) for a reopen,
on top of decoding every record's payload. The measured reopen curve — 0.04,
0.13, 0.41, 1.97, 11.98 s of replay time above the fixed floor at N = 16, 32,
64, 128, 256 — is that shape.

### 4. The decimal-octet bridge

`Acl2Store.literal` in `tools/run_store.py` renders each octet as a decimal
numeral and a space, and `Acl2Store.recover` marshals the **entire** recovered
history as one such literal. Measured expansion is 6.37 octets of pipe text per
payload octet (the payload crosses the bridge more than once per post: content
identity, preparation and framing). A maximum-size article costs 211 KiB per
post; a 4096-record scale store at maximum payload would put roughly 850 MB of
ASCII through a pipe in a single recovery form.

### 5. Quadratic recognizers that remain

Listed in cliff 1: `fn-article-listp`'s `member-equal` against a rebuilt
`fn-article-msgids` (`books/acceptance.lisp:326`), `fn-articles-freshp`
(`:399`) and `fn-node-statep`'s `fn-subsetp` over binding identifiers
(`books/node.lisp:188`). `fn-find-article` (`books/acceptance.lisp:346`) is a
linear scan, which is visible in the per-position ARTICLE figures but is not
the dominant term at this scale.

## What the wave-3 checkpoint and index lanes will and will not fix

**Checkpoint (`books/checkpoint.lisp`) removes cliff 3 and nothing else.**
`fn-checkpoint-capture` (`:107`) stores the exact core node after a committed
prefix, so a reopen no longer re-replays it. But `fn-checkpointp` (`:63`)
includes `fn-node-statep node` at `:75`, so restoring still pays one Θ(N² +
N·P) recognizer pass, the restored node still holds every payload by value
(cliff 2), and the checkpoint bytes themselves must carry those payloads.
Checkpointing turns an N³ reopen into an N² one; it does not make a reopen
cheap, and it does not touch the per-command cost.

**Index (`books/index.lisp`) removes the GROUP/LISTGROUP growth and nothing
else.** `fn-index-build` (`:74`) materializes group/number→Message-ID entries
and the range query "scans only the materialized entries", which is exactly the
linear GROUP/LISTGROUP curve above. It does not help ARTICLE by Message-ID
(`fn-find-article` still walks the payload-carrying list), it does not reduce
memory, and its own rebuild entry point is declared
`:guard (fn-statep st)` at `books/index.lisp:81` — so if the host calls the
rebuild per command, the whole-state recognizer returns through the index's
front door. The index lane should state which of its entry points run per
command and with what guard.

Neither lane addresses cliffs 1, 2 or 4.

## Proposed next model change: articles by reference

`specs/objects.md` already separates a **content object** ("type/domain, format
version, algorithm-tagged identity, exact bytes, byte length") from an
**article record** ("exact Message-ID, source/variant references, provenance,
selected local representation") and a **blob manifest** ("ordered
content/chunk references, logical length, reconstruction profile"). The model
does not yet follow its own specification: the article *is* its bytes.

The change, concretely:

1. `fn-article-payload` becomes `fn-article-content` — the algorithm-tagged
   identity that `books/identity.lisp` already derives as
   `fn-id-content-subject` (`*fn-id-subject-octets*` = 71). The article record
   keeps Message-ID, groups, memberships and pin exactly as now.
2. The state gains a content map, keyed by that identity, whose values are
   either the octets or a blob manifest of chunk identities. The store's
   transaction record already carries both the subject and the payload, so
   recovery can populate the map without a format change; only the in-memory
   state shape changes.
3. `fn-statep` becomes Θ(n) on the article list — no payload re-validation per
   article — plus a separate, separately-invariant recognizer over the content
   map. Content octets are validated once, when the map entry is created.
4. Separately, and independently useful: give the three acceptance operations
   and the two node operations a `:guard (fn-statep s)` with the recognizer
   check under `mbe`, discharging the guard from the preservation theorems that
   already exist. That alone removes cliff 1 without changing the state shape.

The refinement obligation it carries, stated so it cannot be discharged
vacuously:

- An inflation function `fn-inflate` from the by-reference state to the current
  by-value state, and for **each** operation the host calls — `fn-accept-prepare`,
  `fn-accept-complete`, `fn-accept-recover`, `fn-node-prepare`,
  `fn-node-complete`, `fn-node-recover`, `fn-replay-apply-record` — a theorem
  `(equal (fn-inflate (op' r args)) (op (fn-inflate r) args))`, under the
  hypothesis that the content map is total over the identities the article list
  references (`fn-content-closedp`).
- A preservation theorem for `fn-content-closedp` under every one of those
  operations, since a refinement that assumes closure without preserving it
  proves nothing about a run.
- Per `AGENTS.md`, the theorem subject must be the function the host calls, and
  each hypothesis needs a `must-fail` sibling: a state whose map is missing one
  referenced identity, and a witness separating two articles that share a
  content identity but differ in Message-ID (deduplication is the point of the
  change, so the model must be shown to keep them distinct).
- The collision premise is A-CRYPTO and must be named, not assumed away:
  addressing content by digest means an apparent collision is `OBJ-001`'s
  quarantine case, and the refinement theorem's hypothesis stack must say so.
  Report the collision figure, not the second-preimage figure.

Expected effect on the measured curves, as a prediction to be refuted by the
next measurement rather than a claim: cliffs 1 and 2 are removed for the
article list, cliff 3 drops from Θ(N³ + N²·P) to Θ(N²) with checkpointing on
top of it, and cliff 4 is untouched — the bridge expansion is a separate
change (a length-prefixed binary channel, or the same content-map trick applied
to the recovery form so that payload octets cross once).

## What this profile does not establish

It is one machine, one ACL2 build, one interpreted bridge, under a load average
between 2.7 and 5.7 with another user's build on the same host. It says nothing
about a compiled path, another filesystem, another CPU, or power-loss behavior.
The scale profile's 4096-transaction bound is a host bound that the measured
reopen curve does not yet justify using in full; it is the ceiling this lane
needed to measure past 128, not a supported capacity.
