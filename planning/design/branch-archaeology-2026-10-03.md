# Branch archaeology, 2026-10-03 (READ-ONLY; nothing merged, deleted or rewritten)

Base: `origin/dev` = 31d645af9. Scope: every remote branch with commits not reachable from origin/dev: 105, not the
25 the brief guessed (the 25 were only those the runner named in batch-bm.md; the rest are the 2026-09-27..30 codex/*
and lane/* heads of the same era). Method: `git rev-list --count origin/dev..B`, per-branch subjects, the earlier
triage (unlanded-triage-2026-10-02.md, whose shas are PRE-rewrite: translated with planning/commit-map-20261002.txt),
and then a re-check against today's dev (symbol greps with `git grep -F ... origin/dev`; `git merge-tree
--write-tree` for whole-branch conflicts; `git apply --check` of translated commits in a scratch detached worktree
build/lanes/branch-archaeology). Where I did not re-verify a triage claim, the row says "triage".

Reading the numbers: "commits not on dev" counts merge commits too and the lineages are stacked (3188 branch/commit
pairs, 1895 unique commits, 1269 unique in codex/*), so never add the column up. Verdict suffixes: MINE-A = worth a
lane now, MINE-B = real residual but it belongs to a larger unscheduled body of work (revive with its owner),
MINE-H = held on purpose by the plan.

Origin of the swarm: all commits carry ember's git identity; the codex/* subjects ("Freeze actual BEGIN captured-order
law and stopped source closeout", "Record exact ...", "Prove ...") are the Codex gpt-6 Astra/Sol style, and several
lane/* tips (online-reclaim, paged-history-2, join-f2-midx, bp-remainder) end in the same style. Claude Opus lanes
("served-wiring:", "stranded-lanes:", "raw-dispatch-3:") are the others.

## Counts

| verdict | branches |
|---|---:|
| MINE (A 13, B 34, H 1) | 48 |
| ALREADY-ON-DEV | 27 |
| DEAD | 24 |
| SUPERSEDED | 6 |
| total | 105 |

## Table (sorted by verdict)

| branch | commits not on dev | dates | verdict | one-line reason |
|---|---:|---|---|---|
| `lane/depth-debt-3` | 80 | 2026-09-29..2026-09-30 | MINE-A | fa656d387 fn-store-charge-is-positive-and-representable (resource-accounting goal); bootstrap/receiver rest is parked (D43/D47) |
| `lane/join-f2-midx` | 94 | 2026-09-29..2026-10-01 | MINE-A | 7116c024c: NOV metadata full decimals instead of dev's ten-digit clamp (a D27 cap); rest of branch parked (stage-0 s8) |
| `lane/operability-review` | 7 | 2026-09-28 | MINE-A | web posting domain defaults to node identity (fn-web-plan-domain absent on dev) + 371-line review; 1 conflict (packaging/install.sh) |
| `lane/post-guard-off` | 4 | 2026-10-02 | MINE-A | ember's 'just not have that guard': 7 owner entries raw-dispatched under fn-owner-served-carried + def-carried :incomplete escape; 1 conflict (generated interfaces.json) |
| `lane/raw-dispatch-3` | 11 | 2026-10-01..2026-10-02 | MINE-A | stage-5 tier A WIP + the D40 trap; superset of rd3-trap; 4 host conflicts |
| `lane/rd3-trap` | 8 | 2026-10-01..2026-10-02 | MINE-A | THE TRAP (0347f1fdd): fnn-install-raw-dispatch captures raw-dispatched objects, fnn-raw-dispatch-traps-intact; 1 conflict (host/native/io.lisp) |
| `lane/retire-fence` | 3 | 2026-10-01 | MINE-A | fn-ort-retire-step / clean SIGTERM exit native test; dev lacks both; 2 conflicts (host/interfaces.lisp, interfaces.json) |
| `lane/runtime-floor` | 1 | 2026-09-27 | MINE-A | tools/runtime_floor (22 files, +1418) and the heap-by-object measurement behind 'SBCL core is the product'; 0 conflicts |
| `lane/served-incremental-1` | 11 | 2026-10-01..2026-10-02 | MINE-A | NEWNEWS on the served -cat dispatcher (e79d0c0ad) + 760-line blake3-string-tests; r67 NEWNEWS blockers F1-F5 open; 6 conflicts |
| `lane/stranded-1` | 7 | 2026-09-29..2026-10-01 | MINE-A | PKT-894 atomic init (node secret in the staged plan, PRF-1040); merges with 0 conflicts |
| `lane/stranded-2` | 19 | 2026-09-29..2026-10-01 | MINE-A | PKT-893 bounded journal reads (D27), PKT-825a shared feed barrier, PKT-700 profile-owned control capacity; 5 conflicts |
| `lane/stranded-3` | 39 | 2026-09-29..2026-10-01 | MINE-A | PKT-855 reclaim-note live checks (fn-rcn-*), carries correctness-remainder/crem9-devfix; whole branch merges with 1 conflict (host/owner-host.lisp) |
| `lane/transit-subject` | 71 | 2026-09-29..2026-09-30 | MINE-A | 83b03d2a3 drops the fn-arena-p premise from fn-ssr-extent/lz-step-refines-resident + statement-physical-tests; applies sans registries; binding migration part is D43-parked |
| `lane/stage-5b-carrier` | 1 | 2026-10-02 | MINE-H | carrier move WIP, does not build; plan-2026-10-03 holds it off dev on purpose, re-run at landing |
| `codex/allocation-epoch` | 72 | 2026-09-29..2026-09-30 | MINE-B | connection prepare/start/finish ticket book + tests (17 files +1594); STO-10001 still cites them; parked activation |
| `codex/allocation-turns` | 75 | 2026-09-29..2026-09-30 | MINE-B | fn-icac-abort / fn-icsc-settle / fn-copc-evaluate observers (30 files +3396); revive with RESOURCE-LEDGER-2 |
| `codex/assurance-hygiene` | 29 | 2026-09-29 | MINE-B | fn-oert-dispatcher-witness and literal PRF-021/025/050/094/168/177 positive/removal teeth; 7 commits, restricted patch applies |
| `codex/byteframe-projection` | 16 | 2026-09-29 | MINE-B | 6af659e36 fn-csa-post-admission, twice-K suffix theorem, :checkpoint-deferred refusal; 28-line conflict |
| `codex/canonical-size` | 134 | 2026-09-29..2026-10-01 | MINE-B | held-record-size / decode-size / sized store-recover-stream carries; 115 commits, 54 files +8038; S7 cohort |
| `codex/collector-core-join` | 67 | 2026-09-29..2026-09-30 | MINE-B | fnn-runtime-collection-step and prepaid-turn tests (12 files +1044); parked activation |
| `codex/connection-native-join` | 72 | 2026-09-29..2026-09-30 | MINE-B | 48c6506d0 fnn-fs-observe-into (preallocated, u32-split statvfs, uncertain/lost-ack fixtures); APPLIES CLEAN on dev; dev still uses a 256-byte alien buffer |
| `codex/consumer-remainder` | 67 | 2026-09-29..2026-10-01 | MINE-B | SIGKILL cuts, repeated NEWNEWS, signed-BP exchange tests (12 files +889); account code itself D46-parked |
| `codex/extracted-product` | 54 | 2026-09-29..2026-10-01 | MINE-B | fn-srnc-connection-owned-request + constructor census (2 commits +235); needs stage-6 refresh |
| `codex/gpt61-coordinator` | 64 | 2026-09-29..2026-09-30 | MINE-B | 35c9234d1: one literal issuer test (+48); broader packet 5 files +581 |
| `codex/history-columns-renamed` | 85 | 2026-09-29..2026-09-30 | MINE-B | bounded canonical image writer and resumable preparation (78 files +13493); S7/OPERABILITY-14 |
| `codex/history-cursor` | 49 | 2026-09-29 | MINE-B | Message-ID hash cursor, emitter packed-row residual, census teeth (6 files +963) |
| `codex/history-record-cursor` | 61 | 2026-09-29..2026-09-30 | MINE-B | cold canonical-stream/termination and decoder lineage (18 files +3352) |
| `codex/history-scalar-cursor` | 42 | 2026-09-29..2026-09-30 | MINE-B | authenticated pagestore reader fn-hsr-* and two native drivers (13 files +3042); specs/history-auth-reader.md still says PLANNED |
| `codex/legacy-parser` | 108 | 2026-09-29..2026-10-01 | MINE-B | ABI-width and logical source-execution traces fn-lpw-* / fn-lpt-* (10 files +1097) |
| `codex/number-source` | 33 | 2026-09-30 | MINE-B | f5cf77ebc fn-wire-scan-preserves-statep (2 files +69, clean on dev) |
| `codex/operability-held16` | 61 | 2026-09-29..2026-09-30 | MINE-B | HPI producer/writer absent on dev while snapshot-producer already calls fnn-hpi-offer (9 files +1279) |
| `codex/operability-producer` | 78 | 2026-09-29..2026-09-30 | MINE-B | private online snapshot/recovery assembly, 100 files +9851; S7 |
| `codex/page-digest-cursor` | 30 | 2026-09-29 | MINE-B | one doc, planning/page-digest-cursor-allocation-inventory.md; APPLIES CLEAN |
| `codex/peering-remainder` | 20 | 2026-09-29..2026-09-30 | MINE-B | 7395f2523 peer pull-login + selected-peer credential proof, a2cb50fe2 varying-budget carriage; both apply sans registries |
| `codex/reclaim-equivalence` | 78 | 2026-09-29..2026-10-01 | MINE-B | fn-idrt-protected-refusals-keep-full-store-frame, fn-rr-durable-revocation-refuses-new-release (7 files +935); the one ttag in the set sits in a test harness |
| `codex/replay-produced-evidence` | 76 | 2026-09-29..2026-09-30 | MINE-B | fn-ris-produced-step size carries (7 files +1026) |
| `codex/snapshot-proof` | 93 | 2026-09-29..2026-10-01 | MINE-B | snapshot-canonical/config/node-alpha books (33 files +3858) |
| `codex/sol-ninep-completion` | 9 | 2026-09-30..2026-10-01 | MINE-B | 36-line core refusal teeth test + nine historical manifests (evidence dropped by the rewrite) |
| `codex/sol-substrate-entry` | 2 | 2026-10-01 | MINE-B | six certify manifests listed in planning/evidence/manifests/LOST.txt; evidence only |
| `codex/source-preparer` | 15 | 2026-09-29..2026-09-30 | MINE-B | proof-speed hint (569,328 -> 64,129 prover steps) and a 36-line removal-witness test; 2 files +62/-6 of source |
| `codex/streaming-extent` | 54 | 2026-09-29..2026-10-01 | MINE-B | decoded-worker-controller-canonical, durable-lz-octet and tests (no fn-dwcc-* on dev); b1f5fda83 clean sans registries |
| `deputy2/proofs` | 1 | 2026-10-01 | MINE-B | 1 commit, 5 lines: scope the global fn-cbor-octet-listp disable in books/pagestore-words.lisp; HELD 'until stage 0', stage 0 is done; merges clean |
| `lane/bp-remainder` | 95 | 2026-09-29..2026-10-01 | MINE-B | fn-bpnj-forward-publication-refusal-preserves-waits-and-class + controller continuation; 86 commits, 17 conflicts |
| `lane/online-reclaim` | 102 | 2026-09-29..2026-10-01 | MINE-B | fn-pwrt-current-step and W8 funded reclaim pool; 102 commits, 35 conflicts, funded-pool integration is stage-0 s2 parked |
| `lane/operability-3` | 26 | 2026-09-29..2026-09-30 | MINE-B | report reader/reset/stream books (111 absent paths); feed-count books already on dev |
| `lane/paged-history-2` | 68 | 2026-09-29..2026-10-01 | MINE-B | 6af659e36 fn-csa-post-admission (POST refused beyond twice checkpoint suffix K); 66 commits, 26 conflicts; same payload as codex/byteframe-projection |
| `lane/productive-read-transfer` | 13 | 2026-09-29..2026-09-30 | MINE-B | 87d18782c + d3145ba6c apply sans registries: inbound nine-step durable acceptance, ACL2-owned catch-up loss diagnostics |
| `lane/served-costs` | 15 | 2026-09-29 | MINE-B | a456bfc18 refusal without the whole-node recognizer (fn-irc-pout-*); same O(store) as ledger PGO-REFUSE-ABORT; 18 conflicts |
| `codex/account-config-posting-relation` | 71 | 2026-09-29..2026-10-01 | ALREADY-ON-DEV | its own posting-policy packet landed (bbf414f8f); the rest is D46-parked |
| `codex/entry-preflight` | 6 | 2026-09-30 | ALREADY-ON-DEV | tool, test and architecture equal dev; residual is D43-parked |
| `codex/history-decode-cursor` | 5 | 2026-09-29 | ALREADY-ON-DEV | decoder, normalizer, refinement books/tests equal dev |
| `codex/history-directory` | 6 | 2026-09-30 | ALREADY-ON-DEV | books, tests, design equal dev |
| `codex/history-prefix-source` | 6 | 2026-09-30 | ALREADY-ON-DEV | 49/57 paths equal dev; only generic LANEDUMP residue |
| `codex/ledger-expansion` | 2 | 2026-09-30 | ALREADY-ON-DEV | lazy observer normalization remains in tools/ledger.py |
| `codex/nov-projection` | 16 | 2026-09-29 | ALREADY-ON-DEV | NOV/cursor books and tests equal dev |
| `codex/obligation-continuation` | 1 | 2026-09-30 | ALREADY-ON-DEV | four cursor books and teeth byte-identical on dev |
| `codex/operator-port-reservation` | 2 | 2026-09-30 | ALREADY-ON-DEV | tests and evidence directory identical on dev |
| `codex/owner-dense-completion` | 37 | 2026-09-30..2026-10-01 | ALREADY-ON-DEV | 46 changed source files byte-identical on dev |
| `codex/profile-seal` | 19 | 2026-09-29 | ALREADY-ON-DEV | its independent fix 377db3837 was cherry-picked as 5b907104b; rest is shared with byteframe-projection |
| `codex/read-foundation-packet` | 1 | 2026-09-30 | ALREADY-ON-DEV | sole patch equivalent on dev; five books identical |
| `codex/reclaim-guard` | 3 | 2026-09-29 | ALREADY-ON-DEV | owner-reclaim.lisp identical on dev |
| `codex/report-emitter` | 1 | 2026-09-30 | ALREADY-ON-DEV | sole patch equivalent on dev |
| `codex/resilience-packet` | 2 | 2026-09-30 | ALREADY-ON-DEV | observer/model identical; later work extends it |
| `codex/snapshot-gate` | 1 | 2026-09-29 | ALREADY-ON-DEV | sole patch equivalent on dev (7f8c9fe96) |
| `codex/sol-peering-completion` | 5 | 2026-09-30 | ALREADY-ON-DEV | 512094bc8 landed as 7fe9474f7 |
| `codex/store-projection` | 2 | 2026-09-29 | ALREADY-ON-DEV | both patches landed |
| `lane/arena-store-8` | 4 | 2026-09-28 | ALREADY-ON-DEV | codec split landed as bdb2734c4 |
| `lane/ccf-dmap` | 1 | 2026-10-01 | ALREADY-ON-DEV | r44 F1/F2 correction landed rewritten (PRF-1227 Theta(pages)) |
| `lane/codex-defloop-2` | 1 | 2026-10-01 | ALREADY-ON-DEV | only a merge commit; the eight loop twins landed as 146686a0b |
| `lane/compress-3` | 2 | 2026-09-29 | ALREADY-ON-DEV | two merge commits, no non-merge commit |
| `lane/decision-keystones-4` | 2 | 2026-09-29 | ALREADY-ON-DEV | both keystone books and tests byte-identical on dev |
| `lane/def-holder-core` | 1 | 2026-10-02 | ALREADY-ON-DEV | only commit is a manifest-index line (409f1ae54); b81e6300c was merged in the batch |
| `lane/operations-i4` | 13 | 2026-09-28 | ALREADY-ON-DEV | functional work landed via 4e15a0079/c0dd6dd0e; only two historical manifests absent |
| `lane/resilience-framework` | 34 | 2026-09-29..2026-09-30 | ALREADY-ON-DEV | 133/137 changed blobs equal dev; residual is design prose |
| `lane/small-rows-d3-on-dev` | 4 | 2026-09-28 | ALREADY-ON-DEV | both patches landed (c9205d5c3, 2062273d6) |
| `codex/operability-ready` | 1 | 2026-09-29 | SUPERSEDED | one regenerated planning/interfaces.json; regenerate against dev instead |
| `codex/resilience-admitted-page` | 7 | 2026-09-30 | SUPERSEDED | implementation landed; the two commits are a handoff note superseded by 13f459d6c |
| `lane/correctness-i4` | 17 | 2026-09-29 | SUPERSEDED | tip is an ancestor of stranded-2 |
| `lane/correctness-remainder` | 38 | 2026-09-29 | SUPERSEDED | tip is an ancestor of stranded-3 |
| `lane/crem10-init` | 6 | 2026-09-29 | SUPERSEDED | strict ancestor of stranded-1 (same four patches) |
| `lane/crem9-devfix` | 32 | 2026-09-29 | SUPERSEDED | its unique work rides in stranded-3; the fix/revert pair cancels |
| `codex/account-adoption-lifecycle` | 9 | 2026-09-30..2026-10-01 | DEAD | D46/stage-0 item 5 unloaded adoption; 48/64 paths already equal |
| `codex/account-config-marker` | 51 | 2026-09-29..2026-09-30 | DEAD | D46: FNCE/account-adoption producer unhooked; its four codec books are already on dev |
| `codex/bpsec-asb` | 28 | 2026-09-30..2026-10-01 | DEAD | D44/F08: BPSec activation parked; dev removed 19 BPSec test roots |
| `codex/captured-wire-dispatch` | 2 | 2026-09-30 | DEAD | stage-0 breaks 3/4 removed these gates |
| `codex/connection-owner-exclusion` | 50 | 2026-09-29..2026-09-30 | DEAD | parked receiver-turn; only 7d2928ac0 (recursive lock nesting repair) is worth remembering |
| `codex/frame-fixture` | 7 | 2026-09-29 | DEAD | implementation landed; residue is 820 lines of stale gate fingerprints (README: gate NOT RUN) |
| `codex/history-consumer-plan-stage` | 38 | 2026-09-29..2026-09-30 | DEAD | fn-caps-* planners belong to the D46-parked account adoption |
| `codex/incoming-authority` | 43 | 2026-09-29..2026-09-30 | DEAD | body on dev; its caller (incoming-freshness-host) is parked, no runtime caller |
| `codex/index-incoming-request` | 34 | 2026-09-29..2026-09-30 | DEAD | books identical on dev; receiver/index producer parked (stage-0 s8/14) |
| `codex/native-custody` | 60 | 2026-09-29..2026-09-30 | DEAD | indexed-connection custody parked (stage-0 s8) |
| `codex/publication-mapping` | 54 | 2026-09-29..2026-09-30 | DEAD | D43: row-carry family UNHOOKED in stage 0 |
| `codex/publication-row-carry` | 52 | 2026-09-29..2026-09-30 | DEAD | D43: UNHOOKED header already on dev |
| `codex/publication-share` | 56 | 2026-09-29..2026-09-30 | DEAD | D43: UNHOOKED row-carry inside |
| `codex/recovery-header-profile` | 6 | 2026-09-30 | DEAD | stage-0 item 1 disabled the bootstrap host family; 27 files equal dev |
| `codex/remote-endpoint` | 64 | 2026-09-29..2026-10-01 | DEAD | D46: FNCE4 grammar reverted until its producer exists |
| `codex/row-carry` | 47 | 2026-09-29..2026-09-30 | DEAD | D43: depends on the reverted held16 binding |
| `codex/rx-connection-factory` | 88 | 2026-09-29..2026-09-30 | DEAD | RX parked (stage-0 s8); the FS primitive in it duplicates connection-native-join |
| `codex/served-publication-producer` | 57 | 2026-09-29..2026-09-30 | DEAD | D43/D46: needs typed subject binding |
| `lane/closure-theorems` | 2 | 2026-09-29 | DEAD | two commits change only planning/evidence/closure-theorems-2026-09-29.md, which the history rewrite dropped; tip diff vs dev is empty |
| `lane/incremental-views` | 42 | 2026-09-29 | DEAD | fn-rov maintenance parked by D47 until reader and resource term land together |
| `lane/owner-offlock-before` | 1 | 2026-10-02 | DEAD | measurement baseline, 'never merge' (handoff owner-offlock.md) |
| `lane/raw-dispatch-owner` | 6 | 2026-10-01 | DEAD | every commit is 'probe: ...' (never landed by its own words) |
| `lane/tls-handshake-budget-2` | 43 | 2026-09-29..2026-09-30 | DEAD | TLS fixes already landed; residual snapshot-initial-reader has no owner-install caller (parked recovery integration) |
| `spike/mega` | 49 | 2026-09-25 | DEAD | 2026-09-25 spike (mission lab); skip-proofs under an explicit FN_SPIKE waiver; replaced by the real server |

## MINE-A, branch by branch

Applicability notes: every "applies" below is `git diff c^ c | git apply --check --exclude=planning/* --exclude=Makefile
--exclude=*.json --exclude=specs/* --exclude=docs/*` on a detached origin/dev worktree. A real landing still has to
regenerate planning/interfaces.json, the ledger, proofs.json and the Makefile roots, and certify.

### lane/post-guard-off (4 commits, 2026-10-02 23:30..23:49; the last live lane at the stop)
- What: ember's ruling "we can just not have that guard" (written into planning/decisions.md by the branch as the D40
  implementation status). Seven owner entries (`fn-owner-io`, `-take`, `-control-submit`, `-prepare-retention`,
  `-prepare-identity`, `-prepare-consumer`, `-prepare-topic`) become raw-dispatched transitions of a new row
  `fn-owner-served-carried` (host/owner-served-carried.lisp, 246 lines, absent on dev); books/def-carried.lisp gains the
  NAMED ESCAPE `:incomplete (A-OWNER-INVARIANT-CARRIED (...))`; definterface accepts `:raw-with (:carried NAME :assuming
  A-ID)`; tools/interface_emit.py mirrors it; `FN_NATIVE_DISPATCH_COUNTERPART=1` keeps the whole-guard path.
- Value: removes the per-call whole-guard cost on the POST path (the cubic POST guard in plan-2026-10-03.md). Dev has
  `:raw-with` (26 hits in books/definterface.lisp) but not the `:incomplete` escape or the row.
- Land: `git merge-tree` gives ONE conflict, generated planning/interfaces.json (regenerate with interface_emit --write
  on hbox). Everything else merges clean.
- Risk: medium. Its own commit says "UNVERIFIED in the image world"; the escape waives completeness for named writers,
  so it relies on the owed list (332 writers) being enforced (the image build refuses unlisted/stale entries). Two untracked
  ledger items in build/lanes/post-guard-off/planning/repair/items/ (PGO-HOST-READING-HOLE: harness_check misses 108 undeclared
  dispatched names reached through fnn-owner-result, six are owner state writers; PGO-REFUSE-ABORT, exposure live:
  `fn-owner-refuse-reservation`, `-known-abort`, `-finish` still evaluate `fn-sn-statep` per call, O(store) per refused POST)
  must be filed before landing; they are the honest list of what the escape does not earn. Pair with
  lane/served-costs a456bfc18 (reservation refusal without the whole-node recognizer, same O(store) site).
  STAGE-5B's carrier move is meant to retire the escape.

### lane/rd3-trap and lane/raw-dispatch-3 (rd3-trap 8 commits, raw-dispatch-3 11; 2026-10-01..02)
- What: THE TRAP (0347f1fdd, "D40 in the image, Codex r34"): `fnn-install-raw-dispatch` captures each raw-dispatched
  function object and replaces the symbol binding with a trap that faults outside the dispatcher's extent
  (`*fnn-in-core*`), plus `fnn-raw-dispatch-traps-intact` at build; r60 item 2 (abstract-stobj :exec case), r63 F1-F6;
  raw-dispatch-3 adds "WIP stage 5 tier A (NOT READY: image-world REPL pending)" with host/native/raw-trap.lisp (261 lines)
  and host/owner-retain-host.lisp (229), neither on dev.
- Value: closes the "raw dispatch can be bypassed" hole the Codex r34 review found (six bypasses in raw_dispatch_rule); the
  plan keeps "raw dispatch continues" and the whole-system-correctness design cites the trap's `call-in-core`.
- Land: rd3-trap alone: 1 conflict (host/native/io.lisp). raw-dispatch-3 whole: 4 (io.lisp, owner-host.lisp, add/add
  owner-retain-host.lisp, tools/extract/world-host.lisp). Take rd3-trap first, raw-dispatch-3's stage-5 WIP only with STAGE-5B.
- Risk: medium-high; trust-critical (needs the fresh review the codex-liaison handoff already asks for).

### lane/stranded-1, stranded-2, stranded-3 (7, 19, 39 commits; 2026-09-29..10-01) -- the "STRANDED-FINISH" packets
- stranded-1 (= crem10-init): PKT-894 atomic init. `71dc5cb2c` "init retry discards an unheld unpublished stage; stage held by
  flock; node secret in the plan" (PRF-1040, tests/acl2/store-init-log-publication-tests.lisp, tools/power_loss.py). Dev lacks
  `fn-bs-init-log-crash-retry-is-old-or-new`, `fn-bs-init-log-complete-store-carries-the-node-secret`, `fnn-init-admit`.
  Whole branch merges with 0 conflicts. Lowest-risk, highest-clarity item here: node secret survives a crash during init.
- stranded-2 (= correctness-i4): `PKT-893: store ROOT journal reads the decision journal a bounded chunk at a time (D27)`
  (`fn-otjs-feed-reports-the-prefix-read`), `PKT-825a: the START quantum's feed frames share one barrier per peer journal`,
  `PKT-700: the control worker ceiling is the store profile's field 16 everywhere`. Dev has none of `fn-otjs`,
  `fn-feed-journal-batch-writes`, `fn-bs-profile-max-control-clients`. 5 conflicts (heap-reservation.lisp, operator-internals.md,
  native/owner.lisp, specs/host.md).
- stranded-3 (= correctness-remainder, crem9-devfix): PKT-855 reclaim note (`books/reclaim-note.lisp`, `fn-rcn-live-note-checks`,
  config delta :reclaim-note code 28, host `--recorded` check refuses `reclaim-note-mismatch`); PKT-854 already reached dev.
  Whole branch: 1 conflict (host/owner-host.lisp). Contains a "revert-of-the-reverts" (BC had reverted six of this lane's
  commits on dev earlier; see off-the-rails) and a Revert/redo pair that cancels.
- Risk: low (1) / medium (2, 3). These touch owner.lisp/owner-host.lisp, which batch BM just churned (fence-boundary,
  sweep-ops): re-certify the owner books and run the native owner/power-loss tests, not the suite.

### lane/retire-fence (3 commits, 2026-10-01)
- `fn-ort-retire-step`, `fn-ort-producers-settled`, `fn-ort-clean-stop-keeps-its-exit` (books/owner-retire-counted.lisp,
  owner-retire-settlement.lisp, tests/acl2/native-retire-tests.lisp, native `test_plain_sigterm_after_feeding_a_peer_exits_ok`):
  the owner queue becomes the producer fence and a final checkpoint is requested before SIGTERM stop. 2 conflicts
  (host/interfaces.lisp, interfaces.json). Check against host-lifecycle (4e409a9d6, merged in BM) which now owns shutdown;
  may be partly superseded. Risk: medium.

### lane/served-incremental-1 (11 commits, 2026-10-01..02)
- `e79d0c0ad` NEWNEWS on the served -cat dispatcher (PRF-1232: `fn-nntp-newnews-ovw` emits a plan-cursor effect, cursor lives in
  the response plan so the reader hold keeps payloads across quanta; keystones `fn-nnw-step-reads-at-most-q`,
  `-consumes-q`), plus `tests/acl2/blake3-string-tests.lisp` (760 lines: 35 official vectors x2 modes, keys, tag pins, 12
  mutations; absent on dev), and the `fn-scj-ocfg-read-span-is-reference-under-invp` conclusion corrected to `fn-scr-tls-agrees`.
- Why now: plan phase 2 names cg-newnews-hang first (NEWNEWS with a wildmat pins the owner). Dev has the NEWNEWS cursor
  BOOK (`fn-nnw` x189 in books/newnews-cursor.lisp) but no `fn-nnw` in host/; the commit's own OPEN note says "carry passed
  as NIL, so the early stop past the date is not live". The tip commit hands off "r67 NEWNEWS blockers F1-F5 as NEXT 0":
  not READY. 6 conflicts (served-catalog.lisp, served-plan-cursor.lisp, ledger files). Risk: medium; start from the book work,
  re-do the host wiring on current owner-host.lisp (it is -283 lines different from dev).

### Small, clean slices (each: one commit, lands as its own tiny lane)
| item | branch / commit (translated) | what | apply check |
|---|---|---|---|
| NOV full decimals | lane/join-f2-midx 7116c024c (-> 50cb50075) | "Render full NOV metadata decimals and refine resumable cached rows": replaces dev's ten-digit clamp (an arbitrary ceiling, D27) | clean sans registries |
| store charge fits codec domain | lane/depth-debt-3 fa656d387 (-> a2ab7c2de) | `fn-store-charge-is-positive-and-representable` + teeth (resource accounting founding goal) | clean sans registries |
| physical statement replay | lane/transit-subject 83b03d2a3 (-> facbc8af2) | drops `fn-arena-p` premise from `fn-ssr-extent-step-refines-resident` / `fn-ssr-lz-step-refines-resident`, adds tests/acl2/statement-physical-tests.lisp | clean sans registries (13 files in the commit; the 2-file theorem slice is cleaner) |
| filesystem observation | codex/connection-native-join 48c6506d0 (-> 5d545c821) | `fnn-fs-observe-into` (preallocated, u32-split statvfs fields, uncertain/lost-ack fixtures; native/fn-fs-observation.c) vs dev's 256-byte alien buffer in `fnn-statvfs-free-octets`; ledger S018/S033 show statvfs under the owner lock | applies fully, 5 files +325 |
| peer pull-login | codex/peering-remainder 7395f2523, a2cb50fe2 | `peer pull-login`, selected-peer credential proof, varying-budget carriage theorem (dev: 0 hits for pull-login outside a handoff note) | both clean sans registries |
| web posting domain | lane/operability-review | `fn-web-plan-domain`: posting domain defaults to node identity; books/web-session.lisp +108, tests, docs/web.md | 1 conflict (packaging/install.sh) |
| runtime floor | lane/runtime-floor 8ac70017a | tools/runtime_floor/*: heap by object (production image RSS 90 MiB: core pages 70.5, anon 17, 9.1 of it the 65,536-word TLS), SBCL floor, fn without ACL2 in the process; "exploratory: no book, host file, build script or release image changed" | 0 conflicts; its evidence md was dropped by the rewrite, the commit message keeps the numbers |

## MINE-H

### lane/stage-5b-carrier (fa32ac06f, 1 commit)
"WIP carrier move (NOT READY, does not build): owner globals 'fn-owner/'fn-owner-retain-carry moved into stobj fn-owner-st
(books/owner-carrier.lisp); 277 touchers", 36 files +18498/-1691, 1 conflict (host/owner-host.lisp, 300 dev commits ahead of its
base). Held off dev by plan-2026-10-03.md and handoff-2026-10-03/stage-5b.md; repair items X05/X16 depend on it. Not an
archaeology question: it is the plan.

## MINE-B (real, not scheduled: take when the owning lane starts, do not mine ahead)

Cohorts, from the earlier triage and my symbol greps (all named symbols still absent on dev today):
- OPERABILITY-14 / S7 / snapshot-open cohort (largest, ~600 absent files): codex/canonical-size (115 commits), operability-producer
  (+9851), history-columns-renamed (+13493), history-record-cursor, history-scalar-cursor (fn-hsr-* auth reader; spec still
  PLANNED), history-cursor, snapshot-proof (+3858), operability-held16, replay-produced-evidence, lane/operability-3,
  lane/tls-handshake-budget-2 (parked). Cross-branch duplicates, so count once. Dev already carries the lower layers
  (cursors, columns, NOV), but `fnn-hpi-offer`/`fnn-hpi-action` are called from snapshot-producer with no producer.
- RESOURCE-LEDGER-2 / stage-6 cohort: allocation-epoch, allocation-turns, collector-core-join, extracted-product,
  gpt61-coordinator (35c9234d1 one test +48), page-digest-cursor (a one-file doc, applies). STO-10001 still cites ticket
  files that exist only on these branches: a dangling cite on dev to chase.
- Recovery/checkpoint: lane/paged-history-2 6af659e36 = codex/byteframe-projection `fn-csa-post-admission` ("Refuse POST before
  preparation beyond twice checkpoint suffix K": a POST refusal bound; count once); lane/online-reclaim (`fn-pwrt-current-step`,
  35 conflicts), codex/reclaim-equivalence (`fn-rr-durable-revocation-refuses-new-release`).
- Teeth/proof: codex/assurance-hygiene (`fn-oert-dispatcher-witness`, literal PRF teeth), codex/source-preparer (proof
  speed 569,328 -> 64,129 prover steps), codex/number-source (`fn-wire-scan-preserves-statep`, 2 files +69),
  codex/streaming-extent (`fn-dwcc-*`), codex/legacy-parser (`fn-lpw-*` ABI widths), codex/consumer-remainder (SIGKILL/NEWNEWS/
  signed-BP tests, no MissionConsumerExchange on dev), codex/sol-ninep-completion (core refusal test), lane/served-costs
  a456bfc18, lane/productive-read-transfer (87d18782c, d3145ba6c apply), lane/bp-remainder (86 commits, 17 conflicts),
  deputy2/proofs (5 lines, unhold now that stage 0 landed).
- Evidence-only: codex/sol-substrate-entry (six manifests in LOST.txt).

## DEAD and SUPERSEDED, why

- 18 branches are the PARKED families: Codex built producer-less machinery that stage 0 (D43, D44, D46, D47) un-hooked:
  account adoption / FNCE (account-adoption-lifecycle, account-config-marker, remote-endpoint, history-consumer-plan-stage),
  the row-carry/publication family (row-carry, publication-row-carry, publication-mapping, publication-share,
  served-publication-producer), receiver/index/connection activation (incoming-authority, index-incoming-request,
  native-custody, connection-owner-exclusion, captured-wire-dispatch, rx-connection-factory, recovery-header-profile) and
  BPSec (bpsec-asb). Their pure books are mostly byte-identical on dev with an UNHOOKED header; nothing to mine until a producer
  exists. One nugget: connection-owner-exclusion 7d2928ac0 (recursive lock nesting in custody helpers, now in
  host/native/receiver-turn-parked.lisp).
- Others: raw-dispatch-owner (all "probe:"), owner-offlock-before ("never merge"), spike/mega (Sept 25 spike), lane/incremental-views
  (D47), closure-theorems (evidence file dropped by the rewrite, tip diff empty), frame-fixture residue.
- SUPERSEDED: crem9-devfix / crem10-init / correctness-remainder / correctness-i4 (strict ancestors of stranded-1/2/3),
  operability-ready (a regenerated JSON), resilience-admitted-page (13f459d6c).

## What went off the rails (evidence, not impression)

1. Not unsound proofs. I scanned every non-merge commit of every unmerged branch for added `skip-proofs`, `defaxiom`, `ttag`,
   `set-ignore-ok`: none in any codex/* book. The only hits are `(defttag :identity-reserve-adapter-test)` in a Python test
   harness (codex/reclaim-equivalence 3f8f5d4bf, commented "restricted to evaluating the actual CL adapter forms in a test
   process; no production proof uses it"), `(defttag :raw)` in a harness (codex/source-preparer c68a17f9c), and spike/mega's
   17 `(skip-proofs` under an explicit `FN_SPIKE` waiver. Hypothesis removals I read are the AGENTS.md pattern: 53e1676a0 "Weaken
   row domain preservation and add actual parse transition teeth" drops `(member-eq (nth 2 s) '(:parse :emit))` and adds
   positive + corrupted-state removal witnesses; aac0efc3e "Remove redundant suffix carry alignment hypotheses" ships a
   `Width lemma's sole retained seed hypothesis is necessary` assert-event.
2. Width, not depth: ~20 branches (above) built machinery with no producer in the served path; stage 0 then unhooked it. This is
   the "diagnosis = width not kind" of the 2026-09-21 orientation, visible in branch form.
3. Stacking and duplication: 3188 branch/commit pairs for 1895 unique commits; `514c7e45e` "WIP incremental-views (W9 bounded
   pilot)" sits under six branches; `36de56741` "WIP: preserve admitted decoder inverse for Sol handoff" under four. Same payload
   counted on several branches (fn-csa-post-admission on byteframe-projection, profile-seal, paged-history-2; the FS primitive on
   connection-native-join and rx-connection-factory).
4. Documentation-as-output: of 1269 unique codex/* commits, 237 have subjects starting Freeze/Record/Preserve/Archive/Name/State/
   Package/Keep/Narrow/Match and 85 name archive/manifest/receipt/evidence/closeout/handoff (e.g. "Preserve raw ACL2 count logs in
   exact byte archives", "Freeze unfinished early recovery caller and exact dependency handoff"); 258 mention a proof/theorem/
   teeth/witness. The raw logs are why a full branch diff reads +299,799 lines (replay-produced-evidence) and why the history
   rewrite dropped planning/evidence.
5. Churn that is real but not Codex: the stranded-3 chain ("revert-of-the-reverts: re-apply BC's six reverts of this lane", plus
   `Revert "correctness-remainder-9 (dev fix): ..."`) is the runner reverting a lane to relieve a red and the lane re-applying:
   the pattern ember has since ruled out (fix forward, never revert for green). The re-applied PKT-854 reached dev
   (2282bffb7); PKT-855/893/894/700 did not.
6. Honesty of the lanes is good: the tips are labelled ("NOT READY", "WIP", "UNVERIFIED in the image world", "a probe, never
   landed"). The failure was integration, not candour: nothing here claims a green it does not have.

## Caveats
- Triage shas are pre-rewrite; I translated those I checked. Class verdicts for codex/* MINE-B rows are the triage's (Codex,
  2026-10-02) re-checked only by symbol grep on today's dev, not by apply.
- merge-tree/apply checks write nothing to any branch; the scratch worktree build/lanes/branch-archaeology was removed afterwards.
