# Review request for gpt-6: fn as of dev 6addf294, 2026-09-26

For gpt-6, who last saw dev `df367488` (2026-09-25) and wrote the mandate
(`planning/handoff-2026-09-25-fable-mandate.md`). This page describes the tree and the
evidence as they stand at dev `6addf294`. Every sentence is taken from a file named in
it. The history is left in those files. Since the wave began (23:48 UTC on 2026-09-25)
dev has taken 78 lane merges on its first-parent line (92 merge commits in all).

The live node has not changed. It is hbox `/tank/fn/node` on `bbf52159`, format 8, marker
unmarked, LAN-only, no peers, no DTN profile
(`planning/evidence/node-hbox-bbf52159-2026-09-25.md`). Every figure below was taken on
hbox or persvati, over loopback, by a script. No human session was held, and no
power-loss, hostile-network or multi-site test was run.

## 1. What a person or agent can do now that they could not on 2026-09-25

Each line gives the record and the decisive native log (first 16 hex of its SHA-256;
the full hash is in the record). All logs are from hbox unless marked.

- Settle a lost POST reply by re-sending the frozen bytes under the same Message-ID. The node answers `441 already stored` even after the article was withdrawn, and never mints a second Message-ID. `visibility-join-2026-09-25.md`, `f5cbf08a668ec74d`.
- Two sleeping agents exchange a signed report R and a reply Q through one node, across six ownership cuts. Each consumer verifies Ed25519 and ML-DSA-65 itself. Attempts are journaled before they cross the boundary, so a later refusal never turns an accepted operation into a refused one. `consumer-e2-2026-09-25.md`, `consumer-e2-2-2026-09-26.md`, `ca68dbbe26304ca3`.
- The same exchange between two nodes peered over NNTP, with no second transition under repeated transfer, lost reply, consumer death or node restart. `consumer-exchange-2026-09-26.md`, `11a1ef0d` (the record truncates it).
- One authored article keeps one identity through POST, retry, operator post, NNTP transit, BP carriage through a dtn7-rs relay, and reopen. `source-corpus-2026-09-25.md` (`f3dffe45adbbd9a5`), `source-corpus-2-2026-09-26.md` (`55ee81ca80f4d67b`).
- A hybrid-signed report crosses four nodes and two dtn7-rs relays, and the signed reply returns: 7/7 steps. An fn relay serves every admitted neighbour at once, so the mission needs no listener turns or restarts. `mission-signed-2-2026-09-26.md` (`ff9cf70ceed04981`), `multi-peer-relay-2026-09-26.md` (`367df9adb8425c11`, bp_node 27/27).
- Read threads across withdrawn messages and search a proved scope. The reader shows five separate facts: claimed author, carried evidence, historical verdict, current enrollment, and the reader's own verification. `reader-daily-2026-09-25.md` (Playwright/tin walk, SHA256SUMS), `reader-2-2026-09-26.md` (`1c902f7c8b1796b9`).
- tin logs in over a TLS-only listener, then reads, follows up, posts and cancels. `sanding-2026-09-26.md`, `9773c4c56ddbffb3`.
- A friend installs a node from a release tarball on a second machine (persvati) and peers over STARTTLS with one invitation each way. Cancels propagate. `friends-peer-2026-09-26.md` (`f8961b4c2c6caf75`), `friends-peer-2-2026-09-26.md` (`1b27f53d9c8fccfc`).
- A friend gets an account from an invitation code (`XREDEEM` over TLS), with no auth.toml edit and no restart. `friends-accounts-2026-09-26.md`, `faebff1b979dcbd3`.
- Pull a feed over STARTTLS as a principal. A peer that keeps listing an article it cannot produce no longer stalls the pull. `peering-tls-pull-2026-09-26.md` (`57af27637e35011f`), `peer-feeds-2026-09-26.md` (`9d010fc144ef1dc4`).
- A declined key statement stays declined across restarts, and the operator re-decides it live with `keys redecide`. A POST reply names a refused key change. A login's principal binding changes live. `key-replay-fixture-2026-09-26.md` (`a978da072121fcb0`), `keys-and-accounts-2026-09-26.md` (`7d00891599f18b30`; continuation 4 `119152840f2fe3f1`).
- A cancel filed on one friend's node has D29's behaviour on the other in both arrival orders: 48 observations, 0 disagreements. `control-across-peers-2026-09-26.md`, `434436f2`.
- A reader port faces strangers under limits ACL2 decides (for example, 500 connections from one address: 8 admitted, 492 answered 400). A served ARTICLE of several MiB no longer kills the owner. `public-exposure-2026-09-26.md` (`6509ea853d7306eb`), `exposure-reply-size-2026-09-26.md` (`5b0bbeda`).
- An operator walks from no configuration to a recovered, serving node in 45 steps through the installed `fn`. `health` reports eight states plus `starting`, and `control log`/`evidence` work live. `operator-walk-2026-09-26.md`, `operator-health-2026-09-25.md` (`7088a1905b3d47a8`), `operator-daily-2026-09-26.md` (`b3b727065dbdf37e`).
- Release articles and get the disk bytes and admission headroom back. A full store can always finish its obligations and its own maintenance. `reclaim-lifecycle-2-2026-09-26.md` (`9450dd9c251c0318`, 18 cuts), `capacity-vector-2026-09-26.md` (`432809841bc2b45b`).
- Compact 20,000 articles into a 12-link chain and serve them byte-identically. A kill between links reopens to the full history. `pack-chain-open-2026-09-26.md` (`9800a653a9fb72fe`), `pack-chain-cut-2026-09-26.md` (`a92b069fe91ffbc0`).
- `store rollback-check --snapshot` compares committed records byte for byte, not counters and sizes. `rollback-history-2026-09-26.md`, `2926fb6649276679`.
- An admitted article can no longer make the store unopenable: each article is charged its own worst case. `width-producers-2-2026-09-26.md`, `4de4b1062565a378`.
- A signed POST at N = 10,000 takes 0.241 s instead of 18.92 s (tmpfs, 8d4ea42c → a888b104). `signed-history-index-2026-09-26.md`; timing rows only, no module log.
- `store checkpoint` completes and reopens at N = 10,000 × 32 KiB (it died before). A restart opens in record-linear time. `rep-wave-d-3-2026-09-26.md` and `served-path-scale-2026-09-26.md` (measurement rows).
- BP verbs answer distinct exit codes, held rows and ADU sizes are profile fields, and a fragment session costs about 60 ms, not 3.7 to 15.9 s. `bp-lifecycle-3-2026-09-26.md` (`fc37d711a5a06681`), `bp-lifecycle-5-2026-09-26.md` (`a1058ce6`).
- Every native command family exits by one ACL2 table, and a changed source prints `CONFLICT`. `outcome-algebra-2026-09-26.md`, `4dc9a0f5`.

## 2. The four coordinates today

**Proved.** Every merge batch was certified at its merged bytes (manifests cited in the
merge commits, stored under `planning/evidence/manifests/`). The whole closure was green
at `b6759850` (certify-20260926T050746Z-356474, 940 books), `dfa810fc`
(certify-20260926T124048Z-1668641, 970 books) and `69046a76`
(certify-20260926T144826Z-2113131, 965 roots, 0 failed).

At dev's own digest the generated `planning/proofs.json` reads 14 certified, 129 whose
cited manifest predates the digest, and 13 planned. `planning/current.md` shows the same
thing as "closure moved".

**Qualified.** `planning/current-view.json` has no image entry for `b6759850`, so
`current.md` still names `c3420013` in its qualified column. The column below reads the
qualification records directly.

**Deployed.** "earlier bytes" means `bbf52159` carries an older version of the
capability.

| capability | implemented (dev) | qualified | deployed |
| --- | --- | --- | --- |
| P1 protected channel | yes | b6759850 §2: 483 / 480 / 481, three wrong-principal classes kept distinct | earlier bytes |
| P2, P10 success boundary, every cut a crash point | yes | b6759850: cuts 60/60, marker 20/20, served crash model 3/3 (amendment) | earlier bytes |
| P3 pinned reader; C3 cancel orders | yes | b6759850: both orders, the pinned reader keeps its view | earlier bytes |
| P4 duplicate vs conflict; one source identity | yes | b6759850: source_corpus prod and dev, source_corpus_bp dtn and dtndev | earlier bytes |
| lost reply then withdrawal (visibility-join) | yes | b6759850 dev 2/2 (a developer selector on prod) | no |
| P9 refuse the unaffordable; per-article charge; reserve | yes | b6759850: history and count exhaustion rows; live copy below H | earlier bytes (P9 only) |
| M5 compaction and reclaim | yes | b6759850: compaction cuts 20/20, reclaim 18 cuts; **chains not in b6759850** | no |
| consumer exchange, one node / two nodes | yes | b6759850 3/3 / two nodes in 69046a76 only | no |
| P11, M4 disconnected, signed four-node mission | yes | b6759850: labs 4/4, missions 7/7 (with listener turns); multi-peer relay in 69046a76 only | no (no DTN profile) |
| signed-history index, outcome algebra, checkpoint reader | yes | dfa810fc lane (unrecorded); 69046a76 pending | no |
| friends peering, accounts, TLS-only tin, public exposure | yes | dfa810fc lane: tarball, friends_accounts 1/1, tin walk | no |
| linear open (served-path-scale), the PKT-481 fix | yes | 69046a76 pending | no |
| hot-path-scans-2, keys-and-accounts-4, hot-path-checker | yes | none (merged after 69046a76) | no |
| payload arena (PRF-118) | **no host caller** | none | no |

**Candidates.**
- **`b6759850` is deployable** (`qual-b6759850-2026-09-26.md`, amended by qual-harness-c18). Its 154 module runs had 122 OK, and every red is class (c), (d) or (e). It has one named limit, M1: under saturating mixed load about half of control requests time out uncertain. The deploy is ember's go (PKT-360).
- **`dfa810fc` is not deployable.** A served ARTICLE of 2 MiB or more killed the owner (`Control stack exhausted`), from public-exposure onward. The fix is on dev at 189e5903 and in 69046a76 (`exposure-reply-size-2026-09-26.md`). Its record is not committed; the working record is `build/lanes/qual-dfa810fc-lane/LANEDUMP.md`.
- **The next cut is `69046a76`.** Its closure is green. Its four images are being built on hbox, and its qualification follows `build/coordinator/queue/qual-NEXT.txt`, with a 3 MiB ARTICLE and a large OVER as standing cases.
- Rolling back to `bbf52159` past the accounts, binding and pull-journal records exits 4 on those stores (qual-dfa810fc's rollback item). That consequence belongs in the deploy note.

## 3. The assurance chain as it stands

The chain runs: native entry → ACL2 subject → equating theorem → maintained relation →
keystone → observed result. `planning/current.md` names the host line and the equating
theorem for each capability. For example, `fn-ccar-own-finish` is equated to
`fn-own-finish` by `fn-ccar-own-finish-is-own-finish`.

**Maintained relations**, each established at the host-called open and preserved by the
admitted transitions:
- `fn-ocl-relation` (owner under live configuration).
- `fn-own-relation`.
- `fn-snt-relation` (store-node traces).
- `fn-ceis-indexedp`: the Store's derived Message-ID and count index. It is established
  with no hypothesis at every host open (`fn-osi-open-installs-indexed-store`, merge
  24481dcc), and hot-path-scans-2 reads the committed count from it.
- The byte-store K0 relation at every cut: `fn-bs-recover-program-keeps-relation-at-every-cut`.
- The capacity vector (`fn-cvec-admitted-history-keeps-the-vector`) and the maintenance
  reserve (`fn-smr-admission-keeps-the-reserve`).

**Named assumptions.** `books/assumptions.lisp` has 11 encapsulates constraining 12
`fn-assume-*` functions: durability-image, write-isolation-observe, host-report,
host-events, peer-retainsp, identity-freshp, policy-authorizedp, fairness-contact-index,
physical-crash, crash-tearp, host-exclusive-read, bp-contact-asks.

Cryptography stays outside them. The SHA-256 collision figure (about 2^128 work) is
assumed, not proved (`visibility-join-2026-09-25.md`). The disk as observed by statvfs is
an environmental assumption with no encapsulate yet (`capacity-vector-2026-09-26.md`).

**Model-only theorems.** `planning/reach-baseline.json` holds 43, and every one carries a
reason. 38 are SPEC, a model kept on purpose. Examples: the receiver-journal replay
awaits a bpaj/bprr bridge (PKT-413); the M4 exchange model has no wire format; the
counting-copy cost bounds. 5 are HOST: the payload arena's theorems, which have no
caller. `reach_check --strict` refuses a placeholder reason. The count is a floor,
because the checker also counts hint symbols (PKT-412).

**Teeth.** AGENTS.md's rule is enforced by `teeth_check --strict --changed-since` at
every merge. `tools/ledger.py` at 6addf294 counts:
- 13,932 theorems, 1,758 `must-fail`, 14,929 `assert-event`.
- 2 must-fails labelled prover-refusal.
- 148 teeth-form warnings and 790 functions never guard-verified. Both lints are
  warn-only.

`rep-wave-d-3-2026-09-26.md` records an impractical u64 hypothesis-removal as a failed
proof attempt, not as a counter-witness.

**Merge certification.** A batch of merges gets one farm run over `--affected-by` at the
merged bytes, then `make check`, then a cite commit. A lane's own run never certifies
merged bytes. `planning/how-we-work.md` step 5.

**Throughput gate.** `tools/throughput_gate.py` runs one hbox unit on tmpfs at N = 100
and 1,000, covering probe, POST, ARTICLE, reopen, checkpoint and signed POST.
- Under load it compares only `probe_bytes_consed_per_commit`, which is deterministic.
  CPU and wall are recorded, not compared (PKT-477 (1),
  `throughput-gate-2026-09-26.md`).
- Latest: batch AC at f314a5a3, 1,406,515 bytes a commit against a baseline of
  1,651,892.
- No quiet run of any image exists yet. The gate sees neither ZFS nor N past 1,000.

**Limits of all of the above.** No human session. No power loss (the kill campaigns keep
the page cache). No hostile network. hbox loopback only, except the one persvati tarball
peering. dtn7-rs is the only foreign BPA (no ION). Production-image cuts are process
kills; coordinate-precise cuts run on the developer twin only.

## 4. Measured performance

Scope keys: images as named; **tmpfs** = /dev/shm; **ZFS** = hbox `tank`, 90 to 91% full,
47% fragmented, no SLOG; hbox load average 4 to 14 in every row (no quiet run exists).

`rep_measure` greets before the store loads, so its greeting rows say nothing about N
(`service-envelope-2026-09-26.md` §2). `planning/performance-2026-09-26.md` does not
exist.

**Greeting on a loaded store**
| N | figure | scope, record |
| --- | --- | --- |
| 1,000 | not measured loaded | — |
| 10,000 | p95 14,035 → 1,294 ms (tmpfs); 12,144 → 1,544 ms (ZFS) | a80534ed → 1770d687, service-envelope |
| 20,000 | 116,539 ms (one sample) → 369 ms on reopen (1,039 ms while the automatic publication runs) | 273cd980 → 5e15ad4c, fixture copy, served-path-scale |

- **Cause:** three whole-state recognizers run per connection under the owner mutex (`fn-statep` twice, `fn-node-statep` once).
- **Fixed:** the quadratic part (PRF-173).
- **Open:** the carried O(1) open (PKT-455 (1)); served-path-scale-2 is running.

**OVER**
| N | figure | scope, record |
| --- | --- | --- |
| 1,000 | 0.88 ms (one article) | 56f94181 tmpfs, hot-path-checker |
| 10,000 | 3.43 ms (one article); 40-row window p95 317 ms tmpfs / 321 ms ZFS | 56f94181; 1770d687, service-envelope |
| 20,000 | 70 ms median (one article, during publication) | 5e15ad4c, served-path-scale |

- **Cause:** about 8 ms per row, the same on both file systems, so CPU. No profile names the walk.
- **Suspects:** hot_path_check lists 9 OVER-candidate walks (PKT-448 (c)).
- **Owner:** none (PKT-476 (3)).

**ARTICLE**
| N | figure | scope, record |
| --- | --- | --- |
| 1,000 | 2 KiB 2.29 ms, 0.43 MB; 32 KiB 38.5 ms, 5.81 MB | 483987b1 ZFS, rep-wave-d |
| 10,000 | 2 KiB 2.30 ms; 32 KiB 85.3 ms; 29.4 ms with a concurrent writer | 483987b1 ZFS, rep-wave-d |
| 20,000 | 7.4 ms median (first run) | 5e15ad4c, served-path-scale |

- **Shape:** flat in N.
- **Cause:** the reply is an octet list, 177 bytes consed per octet. Readers and the writer serialize on the owner mutex.

**Unsigned POST**
| N | figure | scope, record |
| --- | --- | --- |
| 1,000 | 2.13 ms, 2.46 MB allocated; ZFS 217.8 ms | 56f94181 tmpfs, hot-path-checker; 8ca933b1, hot-path-scans |
| 10,000 | 5.34 ms, 7.93 MB; p95 6.5 ms tmpfs / **607 ms ZFS**; 73 /s tmpfs vs **1.4 /s ZFS** (1 connection, 3 readers) | 56f94181; 1770d687, service-envelope |
| 20,000 | not measured (PKT-455 (4)) | — |

- **Profile** (tmpfs, 17ff24aa, N = 10,000, `publish-program-2026-09-26.md` §1.4): FN-INDEX-BUILD 31.9%, FN-AG-CAR/CDR 24.6%, FN-INDEX-MEMBERSHIP-ENTRIES 18.0%, FN-SCAR-FEED-COUNTED 16.4%.
- **Causes:**
  - The group index is rebuilt per refresh. PKT-517 says it still grows with N, although it was recorded closed.
  - The wire is fed a byte at a time (ingress-span's target).
  - On ZFS the durable publication is 94% of wall time.
- **Allocation:** hot-path-scans-2 took FN-SBUD-RECORD-OCTETS from 20,752 samples to 0 at N = 10,000, but per-POST allocation did not fall (−0.13%).

**Signed POST**
| N | figure | scope, record |
| --- | --- | --- |
| 1,000 | 0.355 → 0.101 s median | tmpfs, 8d4ea42c → a888b104, signed-history-index |
| 10,000 | 18.92 → 0.241 s; p95 282 ms tmpfs / 786 ms ZFS | same; 1770d687, service-envelope |
| 20,000 | not measured | — |

- **Fixed:** the identity prepare replayed the history; it no longer does (PRF-144).
- **Remains:** linear walks that decode nothing (PKT-330 (2)).

**Reopen**
| N | figure | scope, record |
| --- | --- | --- |
| 1,000 | 1.18 s, 1.57 GB consed | 56f94181 tmpfs (before the linear-open fix), hot-path-checker |
| 10,000 | full replay 12.7 s tmpfs / 72.4 s ZFS; fresh checkpoint 11.9 / 10.6 s; 32 KiB checkpoint 132.3 s at 19.3 GB peak (it died before) | 1770d687, service-envelope; rep-wave-d-3 |
| 20,000 | to LISTENING 280.7 → 119.3 s; checkpoint reopen 251 → 43 to 51 s | 273cd980 → 5e15ad4c, served-path-scale |

- **Profile after the fix, at 20,000:** `fn-record-string-octets-aux` 24.2%, `fn-cbor-octet-listp` 20.5%, `fn-record-payloadp` 20.3%, collector 11.3%. That is octet-list replay (D27).
- **Remains:** one linear lookup per replayed step (PKT-455 (2)).

**Checkpoint publication**
| N | figure | scope, record |
| --- | --- | --- |
| 1,000 × 32 KiB | 18.9 s, 7.33 GB → 27.8 s, 3.11 GB | rep-wave-d-2 |
| 10,000 × 2 KiB | 30.1 s, 5.37 GB → 31.1 s, 2.74 GB; automatic capture 24.2 s | rep-wave-d-2; 1770d687 tmpfs |
| 10,000 × 32 KiB | failed at 32.8 GB → 154 s, 22.5 GB; a 670 MB file holding every payload twice (PKT-307) | rep-wave-d-2 |
| 20,000 | automatic capture 54.2 s at 21,050 | 1770d687 tmpfs, service-envelope |

**The capture ceiling.** An owner posting 2 KiB articles died at N = 32,729 with
`Heap exhausted` in `FN-SCC-FRAMES` (tmpfs, the 32,000 MiB dynamic space). It died again
at 36,208. N = 100,000 could not run. This is a process death, not a named refusal
(PKT-492, PKT-191).

**Commit on storage.** Every image makes 7 fsyncs per commit on both file systems
(commit-regression, publish-program). A commit costs 0.6 to 1.8 ms on tmpfs. On ZFS it
costs 100 to 418 ms, and that figure tracks box load, not N: 417.6 ms at N = 1,000 under
load 11, and 169.4 ms at N = 10,000 under load 6. The "20× regression" compared tmpfs
with ZFS.

**BP fragment session.** 3,679 / 6,807 / 15,880 ms fell to 57 / 58 / 72 ms at
64 / 128 / 256 held rows (`bp-lifecycle-5-2026-09-26.md`, DTN developer image). Opening
1,311 held rows still takes 51.9 s.

## 5. Decisions taken under mandate §2, restated at today's bytes

These restate `decisions-2026-09-26-coordinator-statement.md` at 6addf294.
1. **The signed retry answers DUPLICATE, exit 0** (source-corpus). A changed source now
   prints `CONFLICT`, exit 1 (outcome-algebra). An old `b6759850` client reads CONFLICT
   as uncertain, exit 3, so the client upgrades with the node (PKT-372).
2. **Each article is charged its own worst case** (packet 1, bounds-p6, width-producers-2),
   and this is in b6759850. The live store's copy opens below H: 10,960 of
   805,306,368 octets. A store an older image filled past H still has no repair path
   (PKT-338).
3. **Maintenance reservation** (PKT-169). It was generalized by capacity-vector to one
   release record per open obligation plus one for maintenance. Every profile admits one
   transaction fewer than its budget (127 of 128 on the development profile).
4. **Custody from a refused channel is refused** (PRF-128).
5. **Declined key statements at reopen: reversed in form.** The `:current` switch is gone
   (key-replay-fixture). Re-evaluation is now the explicit operator verb `keys redecide`
   (keys-and-accounts), which is what §12.7 asked for.
6. **The pull cursor stays as FNPL files.** It gained the `:pull-unavailable` kind. An
   image older than that faults on such a journal (PKT-432, decided "accept").
7. **Refused signed evidence is classified, not held.** Transit now logs the seven-class
   verdict.
8. **E2 positions pin nothing.**
9. **signed-history-index was held, then merged (24481dcc)** once `fn-ceis-indexedp` was
   proved at every host open. No keystone gained a premise.

**The coordinator decided later** (`build/coordinator/WAVE-STATE.md` "DECIDED";
`planning/backlog-2026-09-25.md`):
- one outcome table, with NO-STORE 6 → 1 and CONFLICT appended (PKT-295 and PKT-246, as
  gpt-6 recommended);
- R bounded by the poll reply in profile validation, with a named refusal at open and
  `upgrade-profile` as the repair (PKT-467, PKT-471);
- `starting` is a reason under fenced, exit 20 (PKT-454);
- a pre-C1 signed cancel is refused by name at open (PKT-444 (1));
- peer rows change by deltas (PKT-436);
- the stale carrier test is fixed, not the signer (PKT-485);
- the signer names no target bound by default (PKT-487);
- the gate counts only the deterministic counter under load (PKT-477 (1)).

**Open for ember.** Each gives the trace, the default, and the rejected alternative with
its cost. Nothing in wave 4 waits on these.
- **Deploy** b6759850 now, or wait for 69046a76 (PKT-360). The default is to wait for 69046a76's qualification. Deploying b6759850 now ships without the chains, the index, accounts and the linear open. 69046a76 adds record kinds that `bbf52159` refuses, so a rollback needs the snapshot.
- **Storage tier** (PKT-442, PKT-477 (2)). Seven barriers at 40 to 60 ms of ZIL each give about 2 POST/s on `tank`. The default in force publishes that weaker tier (docs/operator.md "What one node sustains"). The options are an SLOG or a pool for the node, group commit, or PKT-441's six-barrier program (−45 ms). Every cheaper marker program is refused by theorem, because it breaks A ≤ M ≤ D.
- **News-only restore** (PKT-228, with PKT-336 folded in). The default is a witness-driven `store rebase` with per-group floors covering every prior allocation. The rejected alternative is a numbering epoch: under RFC 3977 §6 it reissues numbers readers saw.
- **Repairing a pre-C1 store with a signed cancel** (PKT-444 (2)). In force, every open refuses it by name. The recommendation is replay as filed, as a logged migration on a snapshot.
- **`:fn-enrollment` HDR** (PKT-175). It is built as (a), which is yes; confirm or overrule.
- **Policy members in a signed statement** (PKT-229, PKT-337). The default is 64 as a grammar limit, field 13 out of validity, and any raise versioned.
- **Smaller packets:** 440 before "already stored" (PKT-164); no content-holding consumer (PKT-165); the three capacity defaults (PKT-323).
- **Chores:** the live marker `required` (PKT-235); the internet-facing certificate (PKT-404); gpt-6's AGENTS.md rule (PKT-342); who the friend is, and on which machine (PKT-343).

**Question for the reviewer:** do items 2, 3 and 5 exceed §2's "routine reversible"
line? Item 5's reversal removed the switch the statement offered.

## 6. The forks, restated with today's evidence

Your earlier answers are in `review-2026-09-26-gpt6-answers.md`. Each fork below says
what has moved since.

1. **Representation.** The checkpoint reader over the buffer landed: 132.3 s at 19.3 GB
   for 10,000 × 32 KiB, where the owner died before. The writer landed too. The capture
   still materializes lists, and the owner dies near N = 32,729 × 2 KiB. The arena has
   no caller. ingress-span built the span wire machine (`fn-wire-feed-span-is-feed-proper`);
   it is unmerged and awaits its native gate.
   *Question:* does the records freeze below still take the checkpoint boundary first,
   now that the capture is the ceiling?
2. **Hidden whole-state work.** `tools/hot_path_check.py` is in `make check` and reports
   182 traversals from 147 host entries: 174 unexpected, 7 cold, 1 uncalled; 0 new and
   0 stale. By dimension: N 118, F 43, J 21. `tools/scale_probe.py` confirms growth on
   52. The checker is path-insensitive.
   *Question:* which classes earn a work-bound theorem first? The candidates are the
   per-request whole-node recognizers (22) and the per-arrival BP walks (52).
3. **v1 throughput.** The envelope at N = 10,000 is in docs/operator.md: greeting p95
   1.3 s, OVER-40 p95 317 ms, unsigned POST p95 6.5 ms tmpfs / 607 ms ZFS, 73 vs
   1.4 POST/s. Every row misses your targets on ZFS; on tmpfs the POST latency and rate
   rows meet them and the greeting and OVER do not.
   *Question:* does v1 publish the ZFS tier as its promise, or require an SLOG before
   stating one? And does mutex fairness (M1, PKT-321) come before the greeting?
4. **Candidate scope.** b6759850 is qualified. dfa810fc was refused on the reply-size
   defect. 69046a76 carries your ranks 1 to 4: decoder, signed index, chains, multi-peer
   relay. Rank 5 (10 MiB) is unexercised: the open of 1,311 held rows takes 51.9 s, and
   the sender job image is 131,072.
   *Question:* is 69046a76 the deploy target, and is anything missing from its checklist?
5. **Exit table.** Done as you recommended. `health` keeps its own 0/19 to 27 scale, and
   the Python tools keep theirs (PKT-329).
   *Question:* should health's scale join the one table?
6. **v2 spines.** The consumer transaction now spans two peered nodes. Its BP carriage
   (phase 2) has not run. The signed mission runs without listener turns. ION is
   untouched. The first external observation still needs a person (PKT-343).
   *Question:* is the persvati tarball peering enough to begin the consumer phase over
   BP, or does the friend session come first?
7. **Assurance debt.** Model-only theorems are down to 43, each with a reason. One book
   stays over 10 s on a quiet box (owner-invariants, 11.19 s). The rollback-checker
   misstep you found is repaired (PRF-141). The fragment/job relation is still proved at
   cold start only. Your AGENTS.md rule is not adopted.
   *Question:* is 14 certified at dev's digest, against a green closure at each
   candidate, the right cadence?

**The records freeze (PKT-293, PKT-167).** The lane's closed design is in
`rep-wave-d-2-2026-09-26.md` §1 and §2.
- **Trace.** `fn-sn-finish` reads every finished payload for the statement verdict.
  Reclaim digests the held payload. 40 books read `fn-article-payload`, and the
  acceptance state carries a second payload field. Threading `fn-arena` costs about 100
  books of statement moves.
- **Design.** Two views of one `fn-record-shapep` tuple:
  - the **wire record**, with an octet-list payload: the codec's domain, and every seam
    theorem unchanged;
  - the **held record**, with a payload handle plus parsed fields decided once at
    intern: verdict, tombstone flag, body line count, control target.
- **Materialize.** `fn-arn-wire-record` is the abstraction. The transition is parametric
  in the payload, so replay is proved once over both views.
- **Order.** Intern with the parsed fields, then the shape freeze on the record and the
  acceptance state (438 and 407 including books), then the codec and recovery over the
  arena, then the served reference effect.
- **Rejected.** The arena as a stobj formal on every transition theorem; a union
  payload type; a list copy "for now".

**The coordinator recommends** adopting the design with your refinements:
- keep context-dependent facts (the verdict under the keyring) with their snapshot and
  the phase-gate theorem;
- persist file-local references;
- **checkpoint boundary first**: PKT-492's decision before the encode, and PKT-307's
  single-payload checkpoint. That work is in the running checkpoint-capture-stream lane.

The record freeze follows as rep-wave-d-4, which is held on ember's word.

## 7. What is red, held or unmeasured now

- **marker-sharing (PKT-441), held.** marker-sharing-2 stopped at its budget with 481 of 513 affected roots green, so it was not merged. marker-sharing-3 (Fable) is running on the B2 shape. It is off the cut path until green.
- **ingress-span, held.** It is built and REPL-proved, but not mergeable until its native modules and the 32 KiB POST before/after pass the gate. ingress-span-2 is running.
- **The capture ceiling.** The owner dies near N = 33,000 × 2 KiB with no named refusal (PKT-492). checkpoint-capture-stream is running. Until it lands, the scale profile admits more than the heap can capture.
- **The pool.** `tank` is 90 to 91% full with no SLOG, so every POST figure on it is the weaker tier (PKT-442). Separately, persvati's 16 ACL2 slots were jammed by idle REPL sessions until tooling-velocity reaped them.
- **M1.** In the mixed hour on b6759850, control requests starved behind saturating reads, and POST p99 was 84 s (PKT-321). No bbf52159 baseline was run.
- **Unmeasured:**
  - N = 20,000 POST, and anything at 100,000;
  - a quiet gate run;
  - live heap after a full collection (PKT-317);
  - SCN-077 (10 MiB);
  - production-image consumer cuts;
  - OVER's cause.
- **Sidecar gap.** `planning/current-view.json` lacks the b6759850 image, so `current.md` understates what is qualified.

## 8. The next wave (from `backlog-triage-2026-09-26.md`, pile (a), in its order)

1. **friend-session:** a friend installs on their own machine, and every stumble is fixed in the verb and doc together (needs ember's person, PKT-343).
2. **peer-feeds remainder:** a durable MODE STREAM refusal with IHAVE fallback, a pull-only credential, and the Message-ID-to-txid index after withdrawal (PKT-431).
3. **upgrade-restore:** rebase/restore without reissued numbers, an over-H repair, and a marker copy-back guard. The success branch waits on PKT-228.
4. **served-path-scale-2 and hot-path remainders:** the carried greeting, linear replay, POST at 20,000, and PKT-517's index rebuild.
5. **operator-daily-4:** a log sink that cannot wedge the owner, `bp-node health`, alerts, heap from the profile.
6. **keys-and-accounts remainder (PKT-497), and community-bounds/caps-to-profile-2:** O(N²) offline config replay (8,336 s for 1,100 requests), and group-name width.
7. **control-across-peers remainder**, and consumer-exchange phase 2 over BP (PKT-333, PKT-466).
8. **The representation wave** (rep-wave-d-4, then ingress-span), once PKT-293 is answered, with checkpoint-capture-stream first.
9. **tooling:** the 322 stale spec citations, per-test budgets, the prover-refusal teeth audit (PKT-445, PKT-496).
10. **qual-69046a76, then qual-next:** TLS pull with auth, a revoking rehearsal, wire marker cuts, an old client against the new node (PKT-226, PKT-372).
