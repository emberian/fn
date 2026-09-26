# pack-chain-open, 2026-09-26 (Opus 5.5): the 20,000-record chain fixture, built once; the startup miss was the harness deadline

Lane `lane/pack-chain-open`, worktree build/lanes/pack-chain-open. Branched
from lane/bounds-p5 at 9e94523e (dev had not merged chained packs at launch),
then merged dev fa72183a (chained packs merged there at 735614d6) at bf5b2471.
Ids: SCN-064 moves to the 20,000 claim; PKT-331 records what is open;
PRF-145 is NOT taken (the chain walk is not the cost, so the coordinator's
branch was "pass served_timeout"; see below).

## The fixture, built once (the coordinator's decision)

The chain-native-8 store was gone: the scale test builds it in a
`TemporaryDirectory` that `tearDown` removes (tests/test_native_checkpoint.py
setUp and tearDown), and the failed run deleted it. It was rebuilt once, by a
standalone script, not a test hook:
planning/evidence/pack-chain-open-2026-09-26/chain_fixture.py `build` on
hbox, image of 8cc3cd4c (core sha256 375855af...; its chain code is dev's:
8dd4173e..9e94523e changes only the record and a test skip), in /dev/shm:

| Step | Seconds |
| --- | --- |
| `store probe 20000 article` (tmpfs) | 198.8 |
| served BEFORE view (owner LISTENING in 154.4 s, VmHWM 3.47 GiB, full replay and its open-time checkpoint; then GROUP, 20,000 ARTICLEs by number, 8 by Message-ID, HDR) | 430.5 |
| `operator CONFIG store compact` | 523.2 |

Result: `compacted steps=pack,select,reclaim,retire records=20000
generation=11 links=12 reclaimed=20000 retired=0`; status `pack-chain
links=12 boundary=20000 generations=11,...,0` (fixture-compact.txt,
fixture-status.txt). 12 links, where chain-native-8 reported 13 generations (not
investigated); a link is one quantum (4096 events or 4 MiB) and
`fewest_links(20000)` is 5.

Kept at hbox:/tank/fn/scratch/fixtures/chain-20000-8cc3cd4c/ (197 MB):
store/, before-view.json (57,184,746 octets), retention.txt, compact.txt,
status.txt, origin.json, SHA256SUMS (sha256 a31d5cb1...c1ad6; copy in
planning/evidence/pack-chain-open-2026-09-26/fixture-SHA256SUMS). It is never
opened in place (every open writes an open-time checkpoint): `chain_fixture.py
time` and the test copy it.

## Step 1: the classification, on a copy (image bf5b2471, /tank, not tmpfs)

`chain_fixture.py time` (time-open-img2.json):

- `store STORE recover`: 201.5 s, peak RSS 3,969,716 KiB; `open=checkpoint:20000 suffix=0`.
- `operator CONFIG run` to LISTENING: 196.0 s, VmHWM 3,969,416 KiB; stop 1.2 s.
- `store STORE status` (an open plus one more walk): 219.5 s, peak 4,216,156 KiB.

196.0 s is past the 180 s default, so a profile decided which cost it is.
sb-sprof over `store recover` on a fresh copy (prof-recover-img2-flat.txt;
full report sha256 8a51735e...cc5f on hbox), 24,546 samples at 10 ms:

- `fn-all-article-memberships` 54.8 % cumulative (with `fn-ag-rev-onto`
  22.9 %, `fn-ag-append-exec` 26.5 %), called from
  `fn-memberships-conflictsp`, whose only executed caller is
  `fn-articles-freshp` (books/acceptance.lisp), the articles conjunct of the
  `fn-state` recognizer: for each article it rebuilds the memberships of every
  later one, quadratic in the articles. `fn-pair-memberp` 22.1 %,
  `fn-retain-find-id` 13.9 %, `fn-node-find-binding` 5.9 % (linear searches
  per element, the same family checkpoint-cost named).
- The chain: `fn-ccc-framed-link` 110 samples cumulative (0.4 %).

Classification: **harness deadline**, over an open whose cost is the Store's
whole-state revalidation at 20,000 articles and is present without a chain
(154.4 s before compaction on tmpfs; the pack-chain-join lane saw the
pre-pack first open miss 180 s on /tank). The chain walk is not the cause.
So, per the coordinator: pass served_timeout; the walk is not rewritten and
PRF-145 is not taken.

## The change

- tests/test_native_checkpoint.py `run_owner`: `wait_for_announcement(...,
  timeout=getattr(self, "served_timeout", 180))`. Only
  NativePackChainTests sets served_timeout (its native_timeout, 1,800 s);
  every other class keeps 180 s.
- tests/test_native_pack_chain.py: `FN_P5_FIXTURE=DIR` runs the scale test
  from a copy of the fixture (the recorded view, retention and compaction
  output stand for the live ones); `FN_P5_SCALE=1` still builds from scratch;
  neither set, it skips with the reason.

## Step 3: the 20,000-article served-identical claim (SCN-064)

hbox, image of 089f932b (core sha256 17807b50...8ab), FN_P5_FIXTURE =
the fixture, systemd-run MemoryMax=40G:
`tests.test_native_pack_chain.NativePackChainTests.test_scale_store_compacts_into_a_chain`
**ok in 2,564.2 s** (scale-fixture-089f932b.log, sha256
9800a653a9fb72fed4b4e931073b8e039c85ee8720466586c6f9423f413af6bc).
Asserted: the compaction's record (12 links, generation 11, 20,000
reclaimed), status links=12 boundary=20000 with no transaction file,
recover reads 20,000; the served view after compaction equals the
pre-compaction view byte for byte (GROUP, all 20,000 ARTICLEs by number,
eight by Message-ID including 4095/4096/4097 across the first link seam,
HDR Subject 1-20000); retention unchanged; the next post takes high+1; the
next compaction adds one link of one record (13, 20001).

Assurance chain: native entry `operator CONFIG run` / `store recover` ->
`fnn-pack-recover-records` -> `fn-store-checkpoint-chain-observe`
(`fn-ccc-observe-chain`) -> keystone `fn-ccc-chain-reconstructs-the-history`
(bounds-p5, unchanged) -> the replayed history -> the observed served view,
equal before and after. The relation is established by the compaction
(`fn-ccc-capture-extends-the-chain`) and re-checked at each open.

## What is not done (PKT-331)

1. The open's cost: 196 s and 3.97 GB at 20,000 articles, dominated by
   `fn-articles-freshp` inside the `fn-state` recognizer at open, a
   whole-state revalidation (AGENTS: carry the invariant, prove it
   preserved). Not this lane's code; it bounds every scale open, chain or not.
2. PRF-145: the open still holds every link as octet lists (PKT-168 item 4).
   It is memory (the links' roughly 40 MB of octets as cons lists, about
   16 octets a cons), not the deadline. The arena note for rep-wave-d-4: the open's link walk is
   where a payload arena would be rebuilt (a reclaimed handle stays valid
   until the next open rebuilds it).
3. `fnn-pack-lower-bound` walks and decodes every link to learn one boundary
   at each open.
4. PKT-168 items are not retired: none of (1)-(4) was done here.

Native SHAs: images img1 8cc3cd4c core 375855af5a41eb13718ea95cfb677adbcfd9e336fde87d0970f0e026ca8d7ff0,
img2 bf5b2471 core dcddf590b9d5b23752e27d246bc1ab785ca59073448e52af4c7f4dc704a4c488,
img3 089f932b core 17807b504a95f6bfea4898ffad8bb1b8f931017d218977d057cbe9ef28f368ab
(hbox:/tank/fn/scratch/pack-chain-open/native-img{1,2,3}/SHA256SUMS). No
book changed, so no certification run.
