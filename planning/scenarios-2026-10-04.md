# Scenarios: what the end-to-end layer tells us (coverage map, 2026-10-04)

Lane scenarios (Opus). ember, 2026-10-04 morning: "make sure we're visiting
ourselves upon the simulation & end-to-end testing scenarios to make sure
those are gucci and robust and that they give us what we want to know about
our software." Then, the same day: fn has its first external collaborator,
who will peer with the next redeploy, so peering and interop is the top tier.

Source: `lane/scenarios` on `origin/integrate/20261004` = `d5b0b9100`, the
published image set `hbox:/tank/fn/images/d5b0b9100...`. Every number below
says where it comes from. "Today" means a run on that image set:

- `core`: the integrator's twelve, run `native-set-coldstart1`;
- `run2`: the integrator's 53 selectors, run `native-run2-d5b0b9100`;
- `smoke`: this lane's tier, run `native-smoke-d5b0b9100`.

The per-module inventory has one row per module: question codes, quality,
the decisive assertion or the defect at file:line, the last hbox run, and
today's result. It is `planning/scenarios-2026-10-04-modules.tsv`. The
runnable form of this map is `tests/scenarios/tiers.tsv`, run with
`tools/scenario_suite.py` (docs/testing.md, "Scenario tiers").

## 1. The layer in numbers

**Native modules.** There are 223 `tests/test_native_*.py` and
`tests/test_bp_*` modules. Each one's assertions were read (5 audit agents),
with this result:

| quality | modules | meaning |
|---|---|---|
| REAL | 132 | drives an image and asserts behaviour a wrong implementation would fail |
| MOCK | 50 | stubs a seam (`fnn-core`, syscalls, recorded owner answers) or the function under test; the Python side checks only a PASS line. Nine have no `-mock` in their name (section 5) |
| OPTIN | 21 | the whole module is skipped unless an env flag or dependency is set; most are REAL when on |
| SRC | 15 | reads or greps source only |
| WEAK | 3 | drives an image, but the assertions pass a broken implementation (`accept_maintenance`, `admin`, `post_seal_gate`) |
| PINNED | 2 | expectations encode what the code did, or contradict the test's own claim (`implicit_tls`:90 vs :98, `operator_verbs`:384/:738/:750) |

**Freshness.** Most of the layer has not run on current source:
- 73 modules have no recorded hbox run at all. Of the REAL ones, 19 have never run.
- Before today, the newest run of most REAL modules was 09-27 to 10-01, on pre-rewrite sources thousands of commits back.
- Today 68 modules ran on `d5b0b9100`: 35 OK and 33 red.

**Kits** (`tools/`):
- `power_loss.py` has the strongest oracle in the tree: block-level cuts, with planted control cuts that must be caught (32/32 caught). It last ran 09-26, on the per-file format.
- `tests/campaign/native_production_kill.py` (SIGKILL under concurrent POSTs) last produced evidence on 09-24. It crashed on log stores until 10-02 and has not run since.
- `hostile_campaign.py` last ran 09-27, four families only.
- `throughput_gate.py check` has been vacuous since the 10-02 history rewrite: no run is an ancestor of HEAD, so it prints NOT MEASURED and exits 0. Its baseline is a min-ratchet of observed runs.
- `scale_curve.py` records only; its fit flags never fail.
- `fundamentals.py` has real bars. F4 cannot be MET until Q_max and H are given.
- `native_mixed_workload.py` ran 10-03. Its restart is graceful (SIGTERM), not a crash.

None of these kits is GPT-6's integrated crash campaign (release row 8, `planning/release-v6.6.0.md:162`, "to build").

**Catalog.** `tests/scenarios/catalog.json` has 315 rows. It is a specification and is checked structurally only (`witness_check` covers `tests/*.sh`). Problems found:
- SCN-003 (the crash matrix) is `specified`, with `implementation: null`.
- SCN-096/100/113/193/216 name test cases that no longer exist.
- SCN-1031 names a missing `.lisp`.

## 2. Questions x scenarios

The table below lists, for each question:
- the REAL witnesses: the ones whose assertions discriminate, best first;
- what ran on the current image today;
- the gap.

Codes are those of `tests/scenarios/tiers.tsv`.

| question | strongest REAL witnesses | today on d5b0b9100 | gap |
|---|---|---|---|
| **DUR** durability across crash cuts | `crash_model` (store CLI at every POST_LOG/recovery cut), `log`, `init_publication`, `state_checkpoint`, `commit_log` (served POST at every POST_LOG cut; segment growth), `resilience_cuts` (whole-history checker), `served_crash_model`, `owner_scheduler` (every 240 body exact after SIGKILL), `log_compaction`, `store_export`, `import_publication`, `checkpoint_auto` | OK: crash_model, log, recovery, init_publication, state_checkpoint, log_compaction, store_export, visibility_join. RED: commit_log (`extent incarnation refused: READ-RESOURCES-UNAVAILABLE`, owner EOF), checkpoint_auto, log_damage and compression (setUpClass: base store does not serve), page_io | (G1) process death only. Nothing block-level has run on the record-log format (power_loss last ran 09-26). (G2) no integrated crash campaign (row 8). (G3) `resilience_cuts`' served cuts all lie *before* the reply, so they test lost-reply fate, not "acked, then crashed". `commit_log` and `owner_scheduler` are the acked-then-killed witnesses |
| **ARU** accepted/refused/uncertain distinct | `outcome_algebra` (one exit table across families), `conformance` (V0-OUT-*: 0/1/3, recover resolves), `visibility_join`, `fence_boundary` (exit 3 vs 4, fence before reply), `known_abort`, `slow_disk` (uncertain at H) | OK: outcome_algebra, conformance, visibility_join, crash_model, recovery. RED: slow_disk 2f/3e | (G4) `bp_fragment_node_native`:471,:514 asserts named profile **refusals** as `EXIT.UNCERTAIN`. That is either a pinned bug or a wrong expectation; ledger, not a test edit. (G5) `store_export`:265 and `outcome_algebra`:145 accept any non-0 for a fault cut |
| **IDEM** idempotent resend | `source_corpus` (POST retry, changed byte, operator post, signed routes, transit: exact ALREADY/DIFFERENT and DUPLICATE/CONFLICT), `conformance` (operator and NNTP duplicate vs conflict, IHAVE/CHECK/TAKETHIS 435/438/439), `visibility_join` (lost reply, then the resend is already-stored with nothing added), `operator_verbs`:511 (no transaction), `hybrid_author` (opt-in), `own_cancel` | OK: conformance, visibility_join, outcome_algebra; source_corpus 1/3 tests only (run2 filter). consumer_exchange: only its two resend cases passed, and they asserted exit 0 alone (fixed, section 5) | (G6) after a crash cut, only NNTP POST is resent (`commit_log`, `resilience_cuts`, `production_kill`). `hybrid-author`, operator post and IHAVE/TAKETHIS are resent only without a crash. (G7) a cross-route resend (POST then operator post of the same article) is refused as a conflict (`resilience_cuts` `test_a_retry_across_routes...`): not idempotent across routes. (G8) over NNTP, duplicate, conflict, refused and uncertain all answer 441 and differ only in text |
| **BND** bounded work / no owner pinning | `mux`, `public_exposure`, `public_limits`, `tls_handshake_budget`, `cold_off_loop`, `cold_line_quanta`/`_deadline` (HDR/XPAT/NEWNEWS past the cache), `newnews_wildmat`, `owner_offlock`, `host_lifecycle`, `slow_disk` | OK: mux. RED: cold_line_quanta and cold_line_deadline (node closed the connection), feed_idle (2,466 wakeups vs 150: busy-poll), owner_offlock, host_lifecycle (3 classes), over_pins | (G9) `cold_line_deadline` accepts 403 as a pass (the bridge, not the fix). (G10) `host_lifecycle` IdleTimerTests reports a known OVER defect as a **skip** (:339-345). (G11) `over_pins`' cold-quantum case passes vacuously when no PAGE-IO hold is reached (:310-314) |
| **MEM** F1/F8 | `mux` (RSS per connection), `image_floor`, `heap_from_profile` (VmHWM; effectively opt-in: needs a cgroup of 2 GiB or less), `credits`, `article_slots` | OK: mux | (G12) the F8 bar (<=256 MiB anon, <=128 MiB working set after 1,000 posts) is judged only by `fundamentals.py` (last 09-28, OPEN). `reclaim_walk`'s RSS case asserts nothing |
| **LAT** F4 | `slow_disk`, `owner_scheduler`, `cold_off_loop`, `decoded_custody`, `status_live_posts` | RED: slow_disk | (G13) F4 needs Q_max and H as `fundamentals.py` parameters; nobody has given them, so it cannot be MET |
| **FSYNC** F3 | `commit_log` (batching through the record log), `owner_offlock` (fsync outside the owner quantum) | both RED | (G14) no module measures fsyncs per POST at a rate. Only `fundamentals.py` F3 (09-28, OPEN) |
| **OPEN** F6 | `open_depth` (OPTIN, 100k fixture) | not run (fixtures predate the format: `replay_determinism` test_d today, `open refused reason=schema-digest`) | (G15) every registered fixture under `/tank/fn/scratch/fixtures` predates the current schema. Release row 1 (`tools/fixtures.py rebuild`) gates OPEN, scale and status_scale |
| **PEER** | see section 3 | | |
| **BP** | `bp_node_native`, `bp_app_native`, `bp_fragment_node_native`, `bp_service_native`, `bp_obligation_native`, `bp_receive_integrity_native` | RED: the whole family (bp2's socket-read-quantum fix is in the next set) | 15 of 28 BP-tagged modules are MOCK sbcl fixtures |
| **WEB** | `web`, `outside_in`, `host_lifecycle` (web POST on a stalled disk) | RED: web 8e (node closed the connection) | - |
| **AUTH** | `starttls`, `sasl`, `tls_reload`, `group_access`, `auth`, `tls_handshake_budget`, `injection_info` | OK: starttls, reader_clients. RED: auth 1/7 (rebind case needs an unguarded ML-DSA openssl) | - |
| **RDR** | `served_differential`, `conformance`, `header_lines`, `group_access`, `reader_clients` (slrn/pan), `fuzz_nntp`, `nov_metadata` | OK: served_differential, conformance, reader_clients, nov_metadata | `conformance` test_reader_profile checks codes, not bodies |
| **CKPT** | `state_checkpoint`, `log_compaction`, `expiry`, `checkpoint`, `maintenance_live`, `store_lineage`, `reclaim_walk` | OK: state_checkpoint, log_compaction, checkpoint, maintenance_live, expiry (1 case). RED: checkpoint_auto, reclaim_in_flight, reclaim_walk (S152) | - |
| **CUR** consumer cursor | `agent_wait`, `consumer_identity`, `consumer_e2` (OPTIN), `consumer_inspect` (OPTIN), `consumer_exchange[_two_nodes]` (OPTIN) | RED: agent_wait (bootstrap exit 1); consumer_exchange 8/11 and two_nodes 3/3, all `consumer refused identity` | (G16) **the cursor has no executed green evidence on any current image.** consumer_e2 has never executed (every run skipped 5/5); consumer_inspect has never run; consumer_identity last ran 09-27 (FAILED) |
| **RCON** remote consumer (FNCR) | none on dev | - | (G17) the listener exists only on unmerged `lane/apps@23d02fe96` (batch R), with `test_remote_consumer_reads_a_store_it_is_not_local_to`. Dev's `host/native/consumer-remote.lisp` says "not activated from bootstrap" |
| **IDN** store identity | `replay_determinism` (genesis teeth: a damaged or swapped genesis is refused); `consumer_inspect` prints history/incarnation from a `.fncu` | RED: replay_determinism test_d (env, G15) | (G18) **no identity command exists** (Mini M4): nothing prints the genesis node identity, format word, or schema/profile digests |
| **OPS** | `operator_cli`, `operator_refusals`, `install`, `maintenance_live`, `limits_live`, `store_mount_identity` | OK: admin (WEAK), checkpoint, journal_stream, maintenance_live, raw_dispatch_image | `install` "upgrades" between two identical image bytes (:108-109) |

## 3. The peer tier: can a stranger's server peer with us safely and usefully?

| ask | witness (tier `peer`) | state before today | gap |
|---|---|---|---|
| push both ways, IHAVE/CHECK/TAKETHIS | `peering` (two production nodes: 235/435/437, CHECK 238x16 431x4 438, kill mid-IHAVE, requeue, queue bound 436), `protected_peering` (reciprocal over STARTTLS+AUTHINFO), `header_limits`/`header_lines` (exact 437/439 at the boundary), `conformance` IHAVE rows, `article_subject` | run2: peering 3/24 red; protected_peering last 10-01 FAILED | (P1) `peering` has no changed-bytes case on transit: 435/438 are by Message-ID presence alone (by design, M3) |
| pull, catch-up after a gap | `peer_pull` (NEWNEWS pull, cursor cuts, TLS principal), `peer_catchup` (1000 articles, digest chain, kill mid-round) | run2: peer_pull 1/14 (catch-up stalls beside a slow pull: catchup2's); peer_catchup 3/4 (startup refusals: cold-start's) | - |
| NEWNEWS wildmat, HDR/XPAT past the cache (the old node's hang) | `cold_line_quanta`, `cold_line_deadline`, `newnews_wildmat`, `cold_off_loop` | run2: both cold_line modules red (node closed the connection); newnews_wildmat and cold_off_loop have never run | (P2) `cold_line_deadline` accepts 403 (G9); `cold_line_quanta` counts rows and never checks their content |
| a misbehaving peer never pins the owner (new: `peer_misbehaving`, below) | `public_exposure` (flood, slowloris, lockout), `tls_handshake_budget`, `host_lifecycle`, `feed_idle`, `feed_temporary` (400 then backoff), `feed_tls_read` (drops, backoff) | run2: feed_idle red (busy-poll; catchup2's); feed_tls_read red today **from a harness bug** (fixed, section 5) | (P3) no module put a misbehaving *transit* peer against the owner; only `hostile_campaign.py`'s transit family (two reader-port cases, a kit, last run 09-27) did, and `peer_round_driver` (trickling pull) is MOCK. **Filled by `tests/test_native_peer_misbehaving.py`** (this lane): a configured peer trickling inside IHAVE, resetting half-way through TAKETHIS, sending garbage and an endless line, flooding CHECK without reading; during each a reader's DATE is answered within 5 s and a good transfer completes and is served exact; after each the owner runs, the half-sent id is 430 and transfers cleanly (no stuck reservation). Not yet run on an image. hostile_campaign now counts a family whose harness raised as a defect (it passed as "no defect") |
| replies a stranger's server gives our feed; offers that must not poison us (lane read-peer's cases) | `peer_hostile_feed` (new): 431 four times then taken (rp-feed-defer-drop: dropped after the third today); a stray second 239 (rp-feed-reply-msgid); a swallowed CHECK and a never-greeting peer dropped at the 600 s round deadline and redialled; a forged TAKETHIS from X must not make Y's CHECK 438 (rp-refused-memory-poison, design); changed bytes after acceptance 438/439; TAKETHIS with an ungrammatical id smuggling a second TAKETHIS (rp-takethis-bad-msgid-desync, high). `operator_walk`: a stopped streaming peer fed by IHAVE once `peer set --streaming false` (read-peer) | not yet run on an image | (P5) four of these are expected red until lane read-peer's fixes and the poison design decision land |
| peer login and credentials | `protected_peering`, `peer_invite`, `peer_by_name`, `friends_feed`, `injection_info` | peer_invite last 09-27 FAILED | `peer_invite`'s refused() checks exit 1 only, never the reason word (:97-102) |
| real external software | `peer_pull` INN cases (`FN_INN_SRC=/tank/fn/inn/2.7.4`, installed on hbox; the tier sets it), `reader_clients` (slrn and pan in docker), `tools/inn_lab.py` (fn feeds innd, innfeed feeds fn, duplicates, loop, kill) | INN pull cases: 2 skipped in run2 (no FN_INN_SRC); inn_lab last ran in the per-file era | (P4) inn_lab is a kit, run from the laptop with `--host hbox`, so it is not in one hbox_native run |

## 4. The Mini contract (`redregg/work/FN-660-RESPONSE-20261004.md`)

| ask | what the layer can say today | gap |
|---|---|---|
| M1 durable-after-ack on the served commit | `commit_log` (kill at every POST_LOG cut; every 240 served again, body now exact), `owner_scheduler` (every 240 body exact after SIGKILL), `served_crash_model`, `resilience_cuts`. Block level: `power_loss.py` (09-26, old format) | `commit_log` is red today (READ-RESOURCES-UNAVAILABLE). There is no power-cut evidence on the record-log format (G1), and no rotation case beyond segment growth (M1-e) |
| M3 idempotent resend on every post path | NNTP POST: conformance, visibility_join, source_corpus, outside_in b16 (now exact). Control `hybrid-author`: hybrid_author (opt-in), consumer_exchange (now asserts DUPLICATE). Operator post: conformance, operator_verbs, consumer_exchange. IHAVE/TAKETHIS: conformance, peering | G6 (no resend after a crash except NNTP POST), G7 (cross-route conflict), G8 (441 text only) |
| M4 identity command | none | G18 |
| consumer cursor | agent_wait, consumer_e2, consumer_inspect, consumer_exchange | G16: red or never run |
| M7 remote consumer | none on dev | G17 |

## 5. Assertions that did not test the claim

**Fixed on `lane/scenarios`.** These are harness defects; no expectation was relaxed:

| module | defect | fix |
|---|---|---|
| feed_tls_read | `TicketingTlsPeer.accepted` collided with `ScriptedTransitPeer.accepted = set()`. Every session thread died on `set.append`, so 3 of 4 cases failed (smoke-d5b0b9100) | renamed `connected_at` |
| friends_accounts | the crash cut ran only when FN_NATIVE_HOST was a developer image, which it never is under hbox_native. Its last line read an undefined `refused` (NameError) | the cut runs on FN_NATIVE_DEVELOPER_HOST, or skips by name |
| key_statements | the `statement-committed:kill` cut set a developer selector on the production image | the cut cases start the developer image |
| consumer_exchange | "identical resend answers duplicate" asserted exit 0, which a fresh accept also gives | requires `DUPLICATE`, and none on the first post |
| outside_in b16 | any 4xx passed for "the node answers that it already has it" | exact duplicate and conflict lines |
| owner_offlock | the changed-bytes resend accepted any 441 | the conflict line |
| operator_walk | the peered pair passed on log lines with nothing delivered; the SIGKILL case never read the post back | STAT 223 at B, and after recovery |
| commit_log | acked posts after a death were checked by a body substring | served body == posted body |
| replay_determinism | determinism of a store whose every write was refused passed | the 17 article writes must be accepted |
| agent_wait | the bootstrap refusal kept no reason | carries the native output |
| article_subject | its relayed fixture had no Date, so transit hygiene (PRF-236) refused it 437 before the subject under test was reached | a Date within the skew |
| peering (productive reader) | posted with `operator post` before starting the owner; refused `no-owner` since 99de13e07 | posts to a running owner, stops, starts |
| peering (retire) | expected the refusal keyword in lower case; the operator prints the book's keyword `(RETIRE DRAIN-SECONDS-OVER-BOUND)` | the keyword, case-insensitively |
| hostile_campaign (kit) | a family whose harness raised was recorded and then judged by the liveness oracle alone, so "never ran" read as "no defect" | the raise is a `harness` defect |

**Open.** These go to the ledger or to their owners; they are not harness edits:
- `bp_fragment_node_native`:471,:514: named refusals asserted as uncertain (G4).
- `host_lifecycle` IdleTimerTests: a known red reported as a skip (G10).
- `resilience_cuts`: harness `*-unavailable` causes become "pending by name" skips (:92-97).
- `implicit_tls`:90 vs :98: the comment says STARTTLS upgrades on the plaintext listener, but the assertion is 502.
- `install`: an upgrade between identical image bytes.
- `parser_turn_boundary`: its mutations edit frozen 09-30 snapshots, not live source.
- The MOCK fixtures named `_raw` without `-mock`: seven renamed `-mock` on this branch (`bp_app_clock`, `publication_lock`, `bpapp_acquisition`, `admin_cleanup`, `tcpcl_acquisition`, `bp_resume`, `auth_lock`; each stubs `fnn-core`, `fnn-owner-action`, syscalls or `fnn-store-close`). Two are left to their owners: `bp_transit_identity_raw.lisp` is cited as evidence by planning/proofs.json and requirements.json (renaming it `-mock` withdraws those citations: a claim decision), and `pull_journal_registry_raw.lisp` is named by ledger items S054/S067/S106/S112.
- `test_native_raw_scripts`:105 passes on "PASS" anywhere in the last line.

## 6. The gaps, ranked by what they hide

0. **Peering a friend's server today stops our owner**: `peer confirm` faults the owner on a host-entry guard (SCEN-PINV-CONFIRM-ARITY, high, since bbfc3b915 on 09-30), so the invite/accept/confirm flow cannot complete. Found by the peer tier's first run; nothing ran peer_invite between 09-27 and today.
1. **G16 cursor**: the consumer cursor (Mini's read path) has no green run on any current image. agent_wait and consumer_exchange fail at bootstrap with `consumer refused identity`, and consumer_e2 and consumer_inspect never ran (the e2e tier now sets their opt-ins).
2. **G1/G2 durability below process death**: no power-cut run on the record-log format, and no integrated crash campaign.
3. **G18 identity command** (M4): nothing to test.
4. **G17 remote consumer** (M7): not on dev.
5. **P3 misbehaving transit peer as a module**: today only the hostile kit covers it.
6. **G6/G7 resend after a crash on non-POST paths; cross-route conflict.**
7. **G15 fixtures predate the schema**: OPEN, scale and status checks cannot run until release row 1 rebuilds them.
8. **G13/G14 F4 parameters and an F3 rate.**
9. **throughput_gate check vacuous** since the rewrite.
10. **Catalog rows naming absent tests** (SCN-096/100/113/193/216, 1031), and SCN-003 without an implementation.

## 7. Tiers (`tests/scenarios/tiers.tsv`)

| tier | modules | wall (hbox, --jobs 4) | answers |
|---|---|---|---|
| peer | 31 + inn_lab + hostile transit families | 13 min (peer-d5b0b9100: 14:57->15:10Z, 28 modules); now about 15-20 min (the ten-minute pull soak and silent-peer case run in parallel) | section 3 |
| smoke | 14 | 2.5 min (smoke-d5b0b9100) | one REAL module per question |
| core | 12 | ~10 min (coldstart1: 14:05->14:14Z) | the release image bar |
| e2e | 39 + opt-ins | ~30-45 min (estimate) | one module per user-visible surface; consumer and hybrid opt-ins on |
| resilience | 38 + hostile, production_kill, power_loss | about an hour, plus the kits | crash cuts, faults, hostile input |
| scale | 11 + fundamentals, scale_curve, throughput_gate, mixed workload | hours, quiet box; fixtures must be current (G15) | F1-F8, curves |

## 8. Runs

| run | image set | tests at | result |
|---|---|---|---|
| peer-d5b0b9100 | d5b0b9100 | 4edb8509a | 13/28 OK: peer_by_name, feed_tls_ready, feed_temporary, header_lines, injection_info, reader_freshness, own_cancel, control_filing, source_corpus (3/3), newnews_wildmat, conformance, cold_off_loop, tls_handshake_budget. Red, already owned: peer_catchup 3/4 and peering's startup refusal (cold-start; catchup2@8d5210ee3), feed_idle 2,474 transit holds vs 150 and peer_pull's catch-up beside a slow pull (catchup2@8d5210ee3), cold_line_quanta and cold_line_deadline (node closed the connection; cold-line items S-reopened by run2), host_lifecycle 3 (run2's). Red, new and filed: **SCEN-PINV-CONFIRM-ARITY** (high: every `peer confirm` stops the owner on a host-entry guard, 10 arguments for 8; peer_invite 7/7, friends_feed), SCEN-EXPOSURE-LOCKOUT (address lockout not held for the next connection), SCEN-FEED-RESUME (a resumed feed does not deliver within 30 s), SCEN-HEADER-LIMITS-RAISED (node closes on a 900-field article), SCEN-GROUP-CREATE-UNCERTAIN (reader_clients' developer case: `group create` exit 3). Red, harness, fixed after the run: article_subject (its fixture had no Date; transit hygiene PRF-236 refuses 437 before the subject is reached), peering's retire case (expected the refusal keyword in lower case), peering's productive-reader case (`operator post` to a stopped node is refused `no-owner` since 99de13e07; it now posts to a running owner and restarts). Environment: protected_peering 1/6 (EADDRINUSE: a port race between concurrent modules) |
| installed-red-d5b0b9100 | d5b0b9100 | e14259ca3 | tests.test_native_installed_start red on both images, as the ruling predicted: through the installed launcher the heap probe decides, then `refused operator run cold startup refused: invalid runtime capture` (every installed node on this dev; lane/cold-start@ae4e1cc95). The 32000 MB natives never met it. Green-after waits on an image set carrying ae4e1cc95 |
| smoke-d5b0b9100 | d5b0b9100 | d5b0b9100 | 8/14 OK (log, visibility_join, crash_model, outcome_algebra, served_differential, starttls, mux, conformance). Red: web, bp_receive_integrity (BP family), commit_log (READ-RESOURCES-UNAVAILABLE), agent_wait (consumer bootstrap), replay_determinism (G15 fixture), feed_tls_read (harness, fixed) |
| smoke-6107ceb56 (scenarios-2) | 6107ceb56 | abd783618 (decided launch, e14259ca3+) | 5/15 OK (log, served_differential, visibility_join, bp_receive_integrity, crash_model). The other 10 (installed_start, conformance 10F1E, outcome_algebra, starttls, mux, feed_tls_read, replay_determinism, web, agent_wait, commit_log): all 23 failing starts are ONE refusal, `cold startup refused: the process heap does not hold the store's protected runtime`, filed **SCEN-INSTALLED-HEAP-NOT-HELD** (high, redeploy blocker: every installed node). The launcher's heap figure and the owner's protected allowance each count the calling process's own dynamic usage, so they disagree with no slack between them. Probes on hbox: the same fresh store's figure was 2433 MB once and 2416 MB the next time; 6 of 6 launcher starts were refused; the image started directly at 2433 to 16000 MB listens. The peer tier is held: under decided launch every owner start hits the same refusal |

### Batch 6 (set-6107ceb56, lat1, tests at 6107ceb56): the 23 red modules, by cause and owner

The run is lat1:/tank/fn/scratch/integrate-20261004/native-set-6107ceb56, which reported 20 OK and 23 FAILED. Below, "heap" means SCEN-INSTALLED-HEAP-NOT-HELD: a test that starts at the heap probe's figure meets the installed refusal. That covers peer-flight stores (7d27f56ca) and the installed bin/fn walk.

| module | b6 | cause | owner |
|---|---|---|---|
| peer_catchup | 1F 2E | 1F heap. The 2E (EOF: "the node closed the connection") get re-checked after the heap fix | cold-start (heap), then peer-default |
| peer_pull | 2F | test_unreadable_credential: heap. test_trickling_body: the owner exited 4 after "DECODED-WINDOW storage-ready" | cold-start (heap); peer-default (trickling, catch-up beside a slow pull) |
| operator_walk | 9F | 7 heap. 1 config text (expects `tls_port = N`, the writer now emits `tls_port=N`). 1 expected USAGE (5), got FAULT (4) | cold-start (heap); peer-feed (the two others) |
| peer_invite | 1F | test_current_inviter_accept_resumes_after_configuration_cut: "composed native image source unavailable: build/MANIFEST.json" (the run tree has no MANIFEST.json) | environment (box layer: cloud) |
| consumer_exchange_two_nodes | 1F | the same missing build/MANIFEST.json | environment (cloud) |
| peering | 1E | test_transit_hygiene_refused_offer_memory_and_relay_checks: socket timed out (17 s) | w-peer |
| host_lifecycle | 1F | PendingAcceptBound: 29 sockets accepted while the loops were held, the bound is 4 (r71-F13) | host-lifecycle (r71-F13) |
| feed_fair_round | 1F | the silent fixture lacked +fnn-socket-read-attempt-max+; fixed by w-peer dbb2ced00 (batch 7) | w-peer (fixed, batch 7) |
| auth | 1F | test_the_address_limit_closes_a_read_that_also_posts: [381 481 400], expected [381 481 381 281 340 240 400]. It closes on the second AUTHINFO, not at the post | design question for the root (read-serve 8a5ebe2ee) |
| bp_node_native | 16F 2E | the BP family. In batch 7 (66076ce8d) it is 14F 2E; test_deletion_report_intent costs 124 s | w-bp |
| bp_service_native | 1F | S024: status=forwarded is the contract word. Green in batch 7 | w-bp (fixed) |
| recovery | 1F | record-exceeds-log-frame (571b3cdbc) | m1-durable-2 |
| log_compaction | 2F | record-exceeds-log-frame (571b3cdbc) | m1-durable-2 |
| log_damage | 13F | stale test contract: plain `status` reads the checkpoint header alone (row S3), so it exits 0 on a damaged log; the open's refusal is `status --replay`'s (SCEN-STATUS-ACCEPTS-DAMAGE, f751aac87) | scenarios-2 |
| initializer_fidelity | 1F | the same, on a misaligned segment (`recover` already refused it by name) | scenarios-2 |
| image_differential | 1F | the same, on a checkpoint deleted after compaction (the image needs the reference image; checked at the next batch) | scenarios-2 |
| page_io | 3F | test_cancel_retire_and_reuse: it waits for a PAGE-IO line, but the window path emits DECODED-WINDOW. The test vocabulary predates the window executor (cold-start red 5). It costs its whole 382 s deadline | window-read lane (test contract) |
| slow_disk | 1F 1E | 1F is a source assertion: `(fnn-owner-peer-read-class service)` is no longer in mux.lisp, so the test reads stale source. 1E: a graceful stop past the deadline (98 s) | window-read lane; w-serve (mux text) |
| over_pins | 1E | test_a_large_article_drained_slowly: the socket read timed out at 300 s (fixture limits: cold-start red 3) | served-catalog-live (SCL2) |
| owner_offlock | 1E | test_a_stalled_feed_journal_holds_no_owner_quantum: the socket read timed out | w-owner |
| reclaim_walk | 1F | a pass longer than two chunks is refused (S152, deferred-credit) | s152 |
| web | 2F | 403 "a page it needs was not read within 5000 ms" on a compressed article (plain and TLS) | codex-sol-web (S032) / window-read |
| reader_clients | 30F | lat1 has no docker, so every reply is None. OK on hbox at b4 | environment (lat1) |
