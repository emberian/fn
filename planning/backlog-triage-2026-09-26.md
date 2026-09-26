# Backlog triage, 2026-09-26: every open packet in one of three piles

Lane burndown-triage, from dev `0d211647` (after the rollback-history merge; sweep 9 was the last, at `88ec3ef0`). Source: `planning/backlog-2026-09-25.md`, whose open lines are the universe: 235 packets (225 ids on unticked checkbox lines, PKT-127 and PKT-173 counted once each though each has two lines, plus the ten unticked alias rows PKT-129 to PKT-138 of the data-constants list; PKT-162 is done by test-latency and not counted). Closed in this pass: PKT-281 (the registry merge driver is registered); partial closures noted on their lines: PKT-145, PKT-245, PKT-253, PKT-312. No other open packet was done by a merge since `88ec3ef0` (ten-second-4 2e9dc981, bp-lifecycle-5 6e6acb1f, rollback-history 575f3e06; PKT-287 and PKT-294 were already ticked).

Aim (ember, 2026-09-26): friends bring up their own instances and peer, some peering public; performance, scalability and peering built out now that v0 is surpassed. The order of pile (a) is leverage toward that.

## Counts

| Pile | Packets |
| --- | ---: |
| (a) WAVE 4 | 117 |
| &nbsp;&nbsp;already owned by a lane running or queued now | 20 |
| &nbsp;&nbsp;in the 17 wave-4 lane candidates | 86 |
| &nbsp;&nbsp;coordinator chores (not lanes) | 11 |
| (b) AFTER v1 | 119 |
| (c) WON'T DO / SUPERSEDED | 22 |
| **Total** | **258** |

Sweep 10 (deputy 3, dev `88ec3ef0..804896a1`): 235 at the triage, 6 retired by merges in the window (PKT-002, 242, 249, 271, 319, 348; struck below with the hash), 38 added: sweep 10's 16 new packets (PKT-353 to 368), 13 reserved ids given their first backlog line (PKT-321, 323, 326, 330, 331, 401, 403 to 406, 409 to 411) and 9 open packets this pass had missed (PKT-168, 324, 332, 408, 412 to 416). Moved between piles: PKT-197 to (c); PKT-164 and PKT-263 to (b); PKT-252 to friend-session; PKT-300 to operator-daily; PKT-301 to served-path-scale. Running now (WAVE-STATE): outcome-algebra, pack-chain-open, signed-history-index-2, and the candidates peer-feeds, keys-and-accounts, community-bounds, reader-2 (their packets stay under their candidate headings).

Sweep 11 (deputy 3, dev `804896a1..afdcae06`): 267 after sweep 10, less PKT-355 and PKT-365 (retired at 17ff24aa and 114af152 and struck then, the table not updated), less 22 retired by the merges in the window (keys-and-accounts 67bae805: PKT-325, 240, 212; community-bounds 07922169: PKT-003, 007, 135, 136; outcome-algebra e0459479: PKT-295, 246, 275; tooling-velocity e94d7cad: PKT-306, 346, 345, 305, 258, 341, 312, 117; control-across-peers 76e7ad91: PKT-210, 147, 154, 208; struck below with the hash), plus 15 added: the lanes' own PKT-329, 433, 435, 436, 443, 444, 445, 446 and sweep 11's PKT-369 to 375. Moved: PKT-211 and PKT-221 to keys-and-accounts-2 (queued, PKT-433), PKT-401 to friends-accounts (running). New (a0) blocks: caps-to-profile and keys-and-accounts-2 (queued), friends-accounts and control-across-peers-2 (running). Counted by script against the backlog's open lines: every open packet once.

Every open packet appears exactly once below (struck lines are retired and not counted) (checked by script against the backlog's open lines).

Ids for wave 4: wave 3's briefs took PRF-160 to 162, NNT-030 to 032, SCN-090 to 092 and PKT-400 to 416, above `WAVE-STATE.md`'s next-free list (PRF-146, NNT-024, SCN-084, PKT-353; sweep 10 appends from PKT-353). The ranges proposed per lane below continue above wave 3's (PRF-163, NNT-033, SCN-093, PKT-417 and up; STO-021, HST-010, SEC-005, CNS-004, REP-012, WEB-002 from `tools/next_id.py`); they are proposals: the coordinator confirms each with `tools/next_id.py` and the board when it writes the brief.

## (a) WAVE 4

### (a0) Already owned by a lane running or queued now (not wave-4 candidates; a continuation takes what each leaves)

**commit-regression (merged 1f9d8ef8)**

- ~~PKT-348 the ~20x per-commit regression after 483987b1~~ retired at 1f9d8ef8 (no regression; the offline term repaired at 735614d6)

**qual-b6759850 (merged 8e27c115)**

- ~~PKT-249 show the live store copy sits below H before any deploy proposal~~ retired at 8e27c115
- ~~PKT-271 format-3 frontier frames: the pre-upgrade snapshot is the only rollback; first native run of format 3~~ retired at 8e27c115
- moved: PKT-300 (b) closed at 8e27c115; the remainder (the operator page's one-fewer sentence) moved to operator-daily
- ~~PKT-319 mission-signed-2's dev-head image never built: name it in the qualification~~ retired at 8e27c115

**pack-chain-join (merged 735614d6 with lane/bounds-p5)**

- ~~PKT-002 chained packs: `store compact` past 4,096 transactions~~ retired at 735614d6
- moved: PKT-197 narrowed at 735614d6 and moved to (c) (superseded by PKT-168 (1) to (3))

**pack-chain-open (running)**

- PKT-347 one preserved 20,000-article chain fixture
- PKT-331 the 20,000-article served-identical claim over a compacted chain (sweep 10)
- PKT-168 chained packs' remainder: (4) the chain open over the buffer is this lane's; (1) generation names below 4096, (2) the link codec round trip unproved, (3) no crash composition or K0 over chain cuts stay after it (sweep 10)

**capacity-vector (merged 9851d6a7)**

- moved: PKT-263 not reached by the lane; moved to (b) History reclamation

**hot-path-scans (merged b1e164ab, part 2)**

- moved: PKT-301 moved to served-path-scale with PKT-324 (the terms it named)

**signed-history-index-2 (running; signed-history-index held by statement item 11, f370581b)**

- PKT-330 the signed-entry index held until `fn-bpaj-store-indexedp` is established at the open and preserved (sweep 10)
- PKT-223 the signed POST's identity prepare replays the history
- PKT-190 the 1.4 s greeting under the owner mutex (if the budget reaches; else served-path-scale takes it)

**outcome-algebra (merged e0459479)**

- ~~PKT-246 the FNCT conflict word (source-corpus's remainder)~~ retired at e0459479 (sweep 11)
- ~~PKT-275 the FNCT conflict word: append `:conflict`, a refusal, exit 1~~ retired at e0459479 (sweep 11)
- ~~PKT-295 exit 6 means two things: one fn-wide exit table~~ retired at e0459479 (sweep 11)

**caps-to-profile (queued; community-bounds merged 07922169)**

- PKT-436 FOR EMBER: config rows per peer through `:set-peer` (default: incremental row deltas, config schema 1) (sweep 11)
- PKT-435 community-bounds' remainder: (1) field 7 governs group names up to the wire's 460, (2) the checkpoint generation names (PKT-168 (1)); (3) PKT-183's contiguity and credential-file bound and (4) the FNFD fit stay after the brief (sweep 11)
- PKT-370 the consumer bound across a reopen composed only in prose (replay does not re-apply field 9) (sweep 11)

**keys-and-accounts-2 (queued; keys-and-accounts merged 67bae805)**

- PKT-433 what keys-and-accounts left, NARROWED by keys-and-accounts-2 ((a), the live login binding, is PKT-221's, done there): (b) succession-era invitations and `peer list`'s budget, (c) the served POST reply naming a refused key change, (d) the seven verdict names in the transit log; these are PKT-463 (sweep 11)
- PKT-463 keys-and-accounts-2's remainder: PKT-433 (b) to (d) and PKT-211 unchanged, fn_verify `revoked` exercised natively, and a must-fail per hypothesis for fn-lb-a-connection-opened-after-a-publication-is-bound-anew (keys-and-accounts-2)
- PKT-211 succession-era invitations refused `genesis`; `peer list` without the budget; no native unsupported-profile/signature-failed row (moved from keys-and-accounts: PKT-433 (b), sweep 11)
- PKT-221 a login-to-principal binding change needs a restart (moved from keys-and-accounts: PKT-433 (a), sweep 11); DONE on lane/keys-and-accounts-2 (PRF-175), to strike at its merge

**friends-accounts (running; friends-accounts-2 queued for PKT-439)**

- PKT-401 invitation-code accounts (designed by friends-peer-2; not in the running brief: the friends-accounts lane, WAVE-STATE next launch 3, PRF-164/NNT-034/SCN-094) (sweep 10) (moved from keys-and-accounts, sweep 11)

**control-across-peers-2 (running, launched by the deputy at 76e7ad91)**

- PKT-444 a pre-C1 store holding a signed cancel fails to open with a generic fault: (1) refuse it by name at exit 1 with its theorem (this lane); (2) the repair verb's semantics is ember's (sweep 11)

**rep-wave-d-4 (queued, Fable; waits on ember's PKT-293/PKT-167)**

- PKT-293 the shape of the records freeze (two views, shared transition)
- PKT-167 adopt the representation program with the payload in the arena
- PKT-307 what the checkpoint reader left
- PKT-314 the checkpoint file holds every payload twice
- PKT-317 live heap after a full collection is measured nowhere
- PKT-303 the arena's five model-only events wait for a host caller

**friends-peer (merged e36706fa; friends-peer-2 merged f5fcea88)**

- ~~PKT-242 the invitation carries the inviter's address so `peer accept` configures the peer (PKT-236 (a))~~ retired at e36706fa

**sanding (merged 15c25aef)**

- moved: PKT-164 the default built at 15c25aef; moved to (b) decisions with a default in force
- moved: PKT-252 tin over TLS and the pill closed at 15c25aef; the remainder moved to friend-session

### Wave-4 lane candidates, by leverage toward friends peering and public reading

#### 1. friend-session

- **Packets:** PKT-343
- **User-visible result:** one of ember's friends, on their own machine, installs the release tarball from docs/peering-with-a-friend.md (friends-peer's runbook), peers with ember's node, posts and reads both ways, and every step they stumble on is fixed in the verb and the doc together; the confusion log is the evidence.
- **Ids to reserve:** SCN-093, PKT-417..418 (a PRF only if a fix moves a served decision).
- **Mandate:** §11, §15 "Protected ordinary use"; answers §6 (the first external observation).
- **Starts after:** friends-peer's runbook and tarball fixes landed; a person and a machine (ember).

- PKT-343 the first external observation: a second operator on a second machine
- PKT-252 the web reader on a non-loopback deployment and a human session (from sanding, sweep 10)
- PKT-354 the repeatable friend session rerun with the friend on persvati; then the scratch goes (sweep 10)
- PKT-411 tin on hbox needs a domain name for its From line; tin's TLS wire unlogged (sweep 10)

#### 2. peer-feeds (RUNNING since 09:45; PKT-431..432)

- **Packets:** PKT-236, PKT-213, PKT-207, PKT-115, PKT-074
- **User-visible result:** a peering between two friends' nodes stays up for days without an operator: a peer that keeps listing an article it cannot produce no longer stalls the pull, a MODE STREAM refusal survives a restart and falls back to IHAVE, TLS pulls have their replay bound observed, and a withdrawal no longer drops IHAVE/CHECK to a history scan.
- **Ids to reserve:** PRF-163, NNT-033, SCN-094, PKT-419..420.
- **Mandate:** §5.7, §12 packet 8, §13 (source/control/key/peering composition).
- **Starts after:** friends-peer merged (it changes the invitation and the peer record); takes PKT-264 item 3 (listed under operator-daily).

- PKT-236 peering-tls-pull's remainder: (b) the TLS replay bound native, (c) the lab exception native, (d) a pull-only credential slot ((a) is PKT-242)
- PKT-213 pull liveness: a peer listing a Message-ID it cannot produce holds the cursor
- PKT-207 after any withdrawal the IHAVE/CHECK history test falls to a scan; a Message-ID-to-txid index
- PKT-115 the IHAVE/CHECK per-event config check (half of what remains)
- PKT-074 the three-node D23 chain has never run natively (relay with `carried`, unlisted author 439)
- PKT-353 a pulling friend misses a cancel: NEWNEWS serves by filed group (not in the running brief; its seam) (sweep 10)

#### 3. upgrade-restore

- **Packets:** PKT-228, PKT-336, PKT-100, PKT-243, PKT-214, PKT-338, PKT-327
- **User-visible result:** a friend can back up, restore and upgrade their node without reissuing article numbers their readers saw, without silently dropping the marker requirement, and while peering with nodes one release behind; an over-H store from an older image has a repair path instead of exit 4.
- **Ids to reserve:** PRF-164, STO-021, HST-010, SCN-095, PKT-421..422 (D33 if the restore rule becomes a decision).
- **Mandate:** §5.6, §12.2, §15 "Pack/reclaim/restore".
- **Starts after:** ember's answer to PKT-228 (with gpt-6's PKT-336 correction folded into the packet first); the qualification's upgrade rehearsal (PKT-271).

- PKT-228 news-only restore and numbering (the decision; witness-driven `store rebase` recommended)
- PKT-336 the restore-witness correction: coverage of every prior allocation, not a sampled high-water
- PKT-100 a restore verb: `checkpoint clone` refuses every news-only store
- PKT-243 docs/operator.md "Back up" teaches copy-back with no number-reuse warning
- PKT-214 a hand-copied format-7 config.json over a required store drops the requirement
- PKT-338 a repair path for a store an older image committed past H
- PKT-327 `rollback-check --snapshot` does not compare the configuration history

#### 4. served-path-scale

- **Packets:** PKT-189, PKT-041
- **User-visible result:** a public node with many concurrent readers answers the greeting, GROUP, OVER and ARTICLE without waiting on whole-state work under the owner mutex, and a restart opens in record-linear time: reader-side critical sections pin an immutable view and render outside the lock; the two quadratic node checks at open go.
- **Ids to reserve:** PRF-165, SCN-096, PKT-423..424.
- **Mandate:** §7 (last three paragraphs), answers §3 order of attack (second and third), §15 "Long-lived mixed workload".
- **Starts after:** hot-path-scans and signed-history-index report (they own the POST and greeting terms); takes PKT-190 if signed-history-index did not reach it.

- PKT-189 two quadratic node checks at open (reopen about N^1.6)
- PKT-041 in checkpoint mode pack, compact and the owner still rebuild all N records' octets
- PKT-301 the O(N) POST allocation and OVER terms (from hot-path-scans, sweep 10)
- PKT-324 hot-path-scans' served-path prefix traversals: `fn-own-refresh`'s index rebuild, the byte-count cache, the kernel appends, the BP cursor (sweep 10)
- PKT-321 M1: control requests starve behind saturating reads in the mixed hour; mutex hold per request kind (sweep 10)

#### 5. operator-daily (RUNNING)

- **Packets:** PKT-283, PKT-344, PKT-264, PKT-098, PKT-209, PKT-220, PKT-269, PKT-016, PKT-286
- **User-visible result:** a friend operating their own node reads `health`, `status` and the logs and knows what is wrong without asking: a restarting owner says starting, a stale control socket after a crash does not lock them out, every refusal names its reason, the BP node reports its own health, the heap size comes from the operator's machine, and the 45-step walk runs on every image.
- **Ids to reserve:** PRF-166, HST-011, SCN-097, PKT-425..426.
- **Mandate:** §11 (health that distinguishes the states; one coherent installed `fn`).
- **Starts after:** outcome-algebra's exit table (it owns the codes these verbs print).

- PKT-283 after a crash `health` says fenced store-held until the owner listens
- PKT-344 a stale control socket after SIGKILL refuses offline `control` verbs
- PKT-264 operator-walk's remainder: (1) `bp-node health`, (2) a refused control post names no reason, (3) the MODE STREAM stop (to peer-feeds)
- PKT-098 doctor, thresholds and alert rules backed by the health verdict; no refusal-rate signal
- PKT-209 `control evidence MSGID` and `control log` missing; reconfiguration refusal reason omitted; the carrier-render theorem
- PKT-220 `bp-obligation status` and `store retention` only offline
- PKT-269 the health verdict runs under the owner mutex with `:verify-guards nil`
- PKT-016 `--dynamic-space-size` 32000 MB is a data bound; take it from the profile or the operator
- PKT-286 SCN-076 (the operator walk) as tests/ modules within the budget
- PKT-300 the operator page does not say a profile admits one transaction fewer than its budget ((b) closed at 8e27c115; sweep 10)
- PKT-361 `store checkpoint` prints an ACL2 invariant-risk warning on stdout (sweep 10)
- PKT-403 the mission makes no TLS pair (X.509 through the image's OpenSSL) (sweep 10)
- PKT-409 the mission writes no `tls_port` (sweep 10)
- PKT-410 a live `store inspect` through the control socket (sweep 10)
- PKT-329 outcome-algebra's remainder: (1) health's 0/19/20..27 scale, proved disjoint from 1..7 (in this brief), (2) the Python host's exit tables, (3) hybrid-author CONFLICT natively, (4) include hygiene (sweep 11)
- PKT-369 a consumer refused past the operator's bound gets exit 1 with no reason on the wire (sweep 11)

#### 6. keys-and-accounts (merged 67bae805; the remainder is keys-and-accounts-2 in (a0))

- **Packets:** PKT-325, PKT-211, PKT-221, PKT-212, PKT-240
- **User-visible result:** friends rotate and revoke keys, and the operator re-decides a declined key statement, without restarts or refused invitations: succession-era invitations work, a login's principal binding changes live, `peer list` shows the carriage budget, the transit log prints the seven-class verdict, and fn_verify renders revoked.
- **Ids to reserve:** PRF-167, SEC-005, SCN-098, PKT-427..428.
- **Mandate:** §5.4, §12.7 (policy at commit, at reopen, today); §11.
- **Starts after:** friends-peer (its invitation-code accounts touch the same books).

- ~~PKT-325 `operator CONFIG keys redecide MSGID`, specified not built~~ retired at 67bae805 (sweep 11)
- ~~PKT-212 a refused kind-3 commit surfaces as the transit's refusal; fn_verify does not render `revoked`~~ retired at 67bae805 (sweep 11)
- ~~PKT-240 `fn-pcb-admission-verdict` (seven classes) has no host caller~~ retired at 67bae805 (sweep 11)

#### 7. community-bounds (merged 07922169; PKT-001, 013, 157, 183 narrowed and stay here; the remainder is caps-to-profile in (a0))

- **Packets:** PKT-003, PKT-007, PKT-136, PKT-013, PKT-001, PKT-157, PKT-183, PKT-135
- **User-visible result:** a public node with hundreds of accounts, peers, groups and consumers never meets a hidden constant: the keyring snapshot, the configuration record, group-name width, config rows and deltas, and the namespace counts come from the profile or are proved work bounds.
- **Ids to reserve:** PRF-168, STO-022, SCN-099, PKT-429..430.
- **Mandate:** §5.5, D27, §7 (no development cap masquerading as a limit).
- **Starts after:** pack-chain-join (PKT-001's `*fn-cpp-max-generations*` row).

- ~~PKT-003 the keyring snapshot caps the principal count (131,072 / 65,536 octets)~~ retired at 07922169 (sweep 11)
- ~~PKT-007 generic CBOR 65,535/65,538 caps config and stxe~~ retired at 07922169 (sweep 11)
- ~~PKT-136 `*fn-stxe-max-octets*` and `-max-detail*` (evidence records)~~ retired at 07922169 (sweep 11)
- PKT-013 group names 256 not 460; config rows 1,024, deltas 64, octets 65,538
- PKT-001 the P5 namespace counts no book reads (consumers 256, config observations, credentials, policy members, generations)
- PKT-157 bounds-profile remainder: consumers field 9 (replay refuses past 256), the BP ADU rows
- PKT-183 namespace contiguity and the credential file's bound composed only in prose
- ~~PKT-135 classify feed, scheduler, anchor, consumer-token and topic payload caps~~ retired at 07922169 (sweep 11)

#### 8. reader-2 (RUNNING since 09:50; PKT-437..438)

- **Packets:** PKT-253, PKT-175, PKT-245, PKT-109, PKT-111, PKT-158, PKT-238
- **User-visible result:** a friend reading on the web or in tin sees whether a signed post was verified here, by whom, and whether that key is still enrolled; the tin rows and the INN supplied-Path case run in the matrix; the login-rebinding lost reply is exercised.
- **Ids to reserve:** PRF-169, NNT-034, WEB-002, SCN-100, PKT-431..432.
- **Mandate:** §11, §5.1.
- **Starts after:** sanding merged; ember's word on PKT-175.

- PKT-253 the web reader's fifth fact is still "not performed" (the consumer half done at 45ab031c)
- PKT-175 a served `:fn-enrollment` HDR item (the coordinator recommends adoption)
- PKT-245 the web client freezes the signed bytes of its signed drafts (docs half landed)
- PKT-109 the `withdrawn` verdict token's grammar; the reader reading `HDR :fn-control`
- PKT-111 the tin phase and four V0-CLIENT-TIN rows (KeyError at the bbf52159 run)
- PKT-158 the INN lab's supplied-Path scenario; the verdict record does not carry the login
- PKT-238 the login-rebinding lost reply not run natively

#### 9. publish-program

- **Packets:** PKT-079, PKT-186
- **User-visible result:** a POST's durable reply stops paying two of seven fsyncs for the marker and a file-system query per file in the transaction directory, toward answers §3's 250 ms p95 and 10 POST/s on ZFS, with the success-boundary guarantee unchanged.
- **Ids to reserve:** PRF-170, STO-023, SCN-101, PKT-433..434.
- **Mandate:** §5.6 (A <= M <= D frozen), answers §3 (fourth: the durable publication program).
- **Starts after:** commit-regression's cause named (it may be the same term).

- PKT-079 a cheaper publication program against A <= M <= D (326 to 388 ms per commit on ZFS)
- PKT-186 79 % of a stalled N=10,000 POST in `QUERY-FILE-SYSTEM` on the publish path

#### 10. service-envelope

- **Packets:** PKT-335, PKT-191
- **User-visible result:** docs/operator.md states a measured envelope for one named profile (greeting, OVER, unsigned and signed POST p95, sustained POST rate, reopen) at N=10,000 and 100,000, with the weaker tier published where storage cannot meet the targets.
- **Ids to reserve:** SCN-102, PKT-435..436 (no PRF).
- **Mandate:** §15 sustained scale, answers §3 (the envelope table), D26.
- **Starts after:** throughput-gate's harness; after served-path-scale and publish-program for the after rows.

- PKT-335 the measured v1 service envelope
- PKT-191 N=100k: 86 ms per POST, 3,870 s full replay, checkpoint capture exhausts 32 GB

#### 11. control-across-peers (merged 76e7ad91; PKT-444 (1) is control-across-peers-2 in (a0))

- **Packets:** PKT-210, PKT-154, PKT-147, PKT-208
- **User-visible result:** a cancel or withdrawal filed on one friend's node has the selected behaviour on the other in both arrival orders, with grants on each side and a kill between arrivals; a signed article for a group the node does not serve gets a named answer.
- **Ids to reserve:** PRF-171, NNT-035, SCN-103, PKT-437..438.
- **Mandate:** §5.4, §15 "Cancel order and policy change".
- **Starts after:** friends-peer (the two-machine harness with enrolment and grants).

- ~~PKT-210 two-node control cases (authority, no grant, kill between arrivals, pinned reader on the other node)~~ retired at 76e7ad91 (sweep 11)
- ~~PKT-154 the BP author path files a signed control by Newsgroups; pre-C1 signed controls may not replay~~ retired at 76e7ad91 (sweep 11)
- ~~PKT-147 a signed article naming an unserved group refused by hybrid-author, cause unfound (the rmgroup half is C4)~~ retired at 76e7ad91 (sweep 11)
- ~~PKT-208 a view with a nil group index answers plain 423/430; `:control-signed` unreachable in the served reasons~~ retired at 76e7ad91 (sweep 11)
- PKT-443 control-across-peers' remainder: the empty-view withdrawn answer, the BP refusal reason, the pull side (PKT-353), a signed control over BP (sweep 11)

#### 12. consumer-exchange

- **Packets:** PKT-333, PKT-351, PKT-254, PKT-256, PKT-262
- **User-visible result:** two agents on two nodes exchange a signed report and reply across interruption, each verifying independently, with no second application transition under lost replies, consumer deaths or repeated transfers.
- **Ids to reserve:** PRF-172, CNS-004, SCN-104, PKT-439..440.
- **Mandate:** §10, §9; gpt-6 wave-2 §7 (the convergence's first outcome).
- **Starts after:** commit-regression closed; best after multi-peer-relay (else the driver still turns listeners).

- PKT-333 the signed two-store application exchange
- PKT-351 one consumer process per database: enforce by a lock; the anchor tests on hbox
- PKT-254 an article above the poll reply ceiling never progresses
- PKT-256 the six consumer cuts ran on the developer image only; a frontier premise without a must-fail
- PKT-262 a consumer registered after a post still polls it: intended or defect under CNS-002

#### 13. multi-peer-relay

- **Packets:** PKT-291, PKT-261, PKT-202
- **User-visible result:** an fn relay serves every admitted BP neighbour at once and routes held transit per destination, so the mission runs without the driver turning listeners or restarting nodes, and one transit decision serves NNTP and BP.
- **Ids to reserve:** PRF-173, SCN-105, PKT-441..442.
- **Mandate:** §9; answers §4 rank 4.
- **Starts after:** signed-history-index (it takes PKT-291 (2)).

- PKT-291 (1) a multi-listener `bp-node serve` ((2) is signed-history-index's; (3) a watch item)
- PKT-261 a relay forwards held transit toward one PEER-ID only
- PKT-202 one transit decision for NNTP and BP (K6): two writer locks bridge two stores

#### 14. tooling-velocity (merged e94d7cad; what stays is its continuation's)

- **Packets:** PKT-306, PKT-312, PKT-345, PKT-346, PKT-305, PKT-218, PKT-248, PKT-117, PKT-285, PKT-288, PKT-258, PKT-341, PKT-120
- **User-visible result:** lanes stop losing runs to the tools: DTN images through hbox_native.sh, spec theorem citations checked, a readable unbalanced-paren error, finished lanes' REPL sessions reaped, stale native tests repaired to the selected contract, and a certification key that covers the host files a test book loads.
- **Ids to reserve:** PKT-443..444 (no PRF).
- **Mandate:** §14.
- **Starts after:** nothing.

- ~~PKT-306 hbox_native.sh cannot build the DTN images~~ retired at e94d7cad (sweep 11)
- ~~PKT-312 the spec-citation check (the citation half landed at 6e6acb1f)~~ retired at e94d7cad (sweep 11)
- ~~PKT-345 native_program_check reports an unbalanced paren as StopIteration~~ retired at e94d7cad (sweep 11)
- ~~PKT-346 orphan proof_repl sessions hold persvati's slots: lane tags, reap, a refusing pool~~ retired at e94d7cad (sweep 11)
- ~~PKT-305 `make tooling-test` times out before its new modules; no test for the ACL2-error refusal~~ retired at e94d7cad (sweep 11)
- PKT-218 native tests older than the behaviour (live_reconfiguration C3, control C4, ...)
- PKT-248 seven native modules over the 20 s test budget; the reverse sweep on a matching image; C10 selectors
- ~~PKT-117 the certification key does not cover host files a test book loads~~ retired at e94d7cad (sweep 11)
- PKT-285 in-place hbox certification has no farm path; cited manifests not checked committed
- PKT-288 twonode and scale gates keep the reader fallback: no fake owner with feeds
- ~~PKT-258 the launcher AST rule misses an ACL2 program in a variable~~ retired at e94d7cad (sweep 11)
- ~~PKT-341 must-fails that are prover refusals counted as teeth: label them~~ retired at e94d7cad (sweep 11)
- PKT-120 stale prose in proofs.json and the rep-heap record
- PKT-359 stale expectations at the candidate (C15 to C18, W1); C18: the served crash model gives no evidence as shipped (sweep 10)
- PKT-412 reach_check reads subjects from hints and hypotheses and seeds from an unloaded host file (sweep 10)
- PKT-364 the teeth-form lint misreads a constant inside a macro as a bare claim (sweep 10)
- PKT-366 the farm installs `defrecord` without its compiled file (sweep 10)
- PKT-368 teeth_check: `fn-record-group-namep` never anchored true (sweep 10)
- PKT-445 what tooling-velocity left: (a) merge_lane.sh's two lines, (b) the over-budget native modules, (c) the prover-refusal teeth audit, (d) PKT-288's fake owner, (e) `farm.py certify-in-place` (sweep 11)
- PKT-446 349 stale spec/doc citations of 254 names (sweep 11)
- PKT-374 hbox_native.sh skips the hybrid-author refusal-class case without FN_RUN_HYBRID_E2E (sweep 11)
- PKT-375 fn_verify's verdict tests run only on hbox (sweep 11)

#### 15. hot-path-checker

- **Packets:** PKT-334
- **User-visible result:** a static checker with size provenance lists every path from a host entry to a traversal of retained history, held fragments or queued jobs, so the next hidden whole-state scan is found before a native run exposes it.
- **Ids to reserve:** PKT-445..446 (no PRF).
- **Mandate:** §6, §7, §14; answers §2.
- **Starts after:** hot-path-scans' findings (its list seeds the checker's first report).

- PKT-334 the hot-path dependency checker with size provenance, paired with one-dimension scaling tests

#### 16. ingress-span

- **Packets:** PKT-302, PKT-315, PKT-316
- **User-visible result:** a 32 KiB POST stops allocating 20.8 MB and spending 59 % of its CPU feeding the body one byte at a time: the wire machine consumes a buffer range by span, and an article larger than a quantum is ingested without a copy per quantum.
- **Ids to reserve:** PRF-174, REP-012, SCN-106, PKT-447..448.
- **Mandate:** §7; rep-wave-d §3 step (iv).
- **Starts after:** rep-wave-d-4's freeze.

- PKT-302 rep-wave-d's (iv) ingress span machine and (v) projections reading the arena by handle
- PKT-315 the checkpoint writer's per-octet export call (0.12 us per octet)
- PKT-316 the 64 MiB collection trigger's placement slows the checkpoint reopen

#### 17. qual-next

- **Packets:** PKT-226, PKT-081, PKT-126
- **User-visible result:** the qualification of the candidate cut after wave 3 covers what bbf52159's and b6759850's did not: TLS pull with auth, a revoking key-statement rehearsal, the NNTP probe's marker cuts on the wire, production-image process-kill variants.
- **Ids to reserve:** PKT-449.
- **Mandate:** §15.
- **Starts after:** the wave-3 cut.

- PKT-226 what the bbf52159 qualification did not cover (plaintext pull, no revoke, developer-twin-only cuts, loopback)
- PKT-081 the NNTP probe's five marker cuts have no wire run; the staging-cleanup swallow S1
- PKT-126 "TLS reset preserves the selected library identity" failed on hbox, not investigated
- PKT-358 the exposure post rate not exercised natively (sweep 10)
- PKT-367 SCN-027, 047, 055, 056 back to specified; SCN-047's native run contradicted its expectation (sweep 10)
- PKT-372 the next cut changes the client contract (CONFLICT, the author-refusal words, moved exit codes): client with node, an old-client run (sweep 11)

### Coordinator chores (in wave 4's window, not lanes)

- PKT-227 stop the spike/mission lab's four nodes on hbox
- PKT-320 remove /tank/fn/scratch/rep-wave-d-2 once rep-wave-d-4 says it does not reuse it
- PKT-352 a superseding note in mission-four-node's record naming PRF-128
- PKT-342 gpt-6's proposed AGENTS.md rule, for ember
- PKT-235 the live node's `upgrade-profile --history-marker required`: ember's go
- PKT-360 deploy the qualified candidate b6759850 (or a later cut): ember's go (sweep 10)
- PKT-404 how a node faces the internet and with which certificate: ember's packet (sweep 10)
- ~~PKT-355~~ friends-peer-2's merge certification `--affected-by books/owner.lisp` at the merged bytes (sweep 10) — retired at 17ff24aa
- ~~PKT-365~~ lower the throughput baseline after 735614d6 with a named improvement (sweep 10) — retired at 114af152
- PKT-408 the gate once per host/books batch; a quiet run to arm the wall-clock figures (sweep 10)
- PKT-326 owner-invariants and owner-control-read: a quiet re-measure, never a lane (sweep 10)
- PKT-371 one quiet re-measure of the five books over 10 s under load today, native-operator's growth watched (sweep 11)
- PKT-373 reap the merged lanes' persvati REPL sessions; identify opv-mirror2 (sweep 11)

## (b) AFTER v1: matters, but not for friends peering

### BP: large transfers, fragments and the job table

- PKT-308 what PRF-136 left: the linear open (1,311 rows in 51.9 s), offset-order arrivals, held-octet walk (the bp-lifecycle-6 brief)
- PKT-309 a node cannot originate the 10 MiB article it can receive (job image 131,072)
- PKT-310 the BP decode is not resumable per quantum
- PKT-311 BP profile edges: ADU not re-checked at replay, cannot raise past a full journal, 2^24 ceiling, a Python size check
- PKT-339 the coverage precheck must be interval-union, not an extent sum
- PKT-266 no theorem bounds one reassembly's work
- PKT-265 the fragment/job-table relation proved at cold start only (assurance-triage files the warm-start PKT)
- PKT-267 the kill and EIO at every cut of a large family
- PKT-185 the receiver's 65,538 x 64 fragment recognizers; the sender's 1 MiB bundle bounds
- PKT-198 held-transit fragmentation; no per-fragment custody
- PKT-199 N16 retire remainder (a killed rotation's directory; the removal model; guards)
- PKT-058 the rest of N16 (kind-19 chunks, manifest, `:quiesce`, obligations 3 to 6)
- PKT-060 the journal fill past 8,192 finals with a rotation, natively
- PKT-139 `*fn-bpn-machine-max-records*` 4,096 on the base journal
- PKT-014 the remaining BP constants: evidence records 4,096, routes 64 (jobs and octets closed by PKT-171)
- PKT-015 the TCPCL MRU literal 1,048,576
- PKT-299 the BP namespace's maintenance reservation (rotation reserve 0, unproved)
- PKT-298 two older FNBS replay folds answer the old bound
- PKT-414 `fn-bpb-encode` at ~6 us an octet; one `:session` step encodes every candidate three times (1.3 s) (sweep 10)

### BP: mission, routing, exits and assurance

- PKT-203 a BP store cannot enrol an author
- PKT-204 the mixed NNTP/BP return receipt; contacts as a modelled plan
- PKT-297 BP run classes for expiry, no-route, busy, clock domain (on outcome-algebra's table)
- PKT-200 bp exit-code remainder: no-route exit after a durable attempt; store-less verbs keep the queued address
- PKT-318 carrier signature verification at B over BP not evidenced
- PKT-304 the fast transit functions on the served BP path are not guard-verified
- PKT-259 BP attempt tokens monotone across events and restart, unproved
- PKT-260 `fn-bpnp-contact-next` and its keystones unreachable since `fn-bpnj-contact-next`
- PKT-054 "offered once per contact" as a theorem over the host driver loop
- PKT-148 spike/bp deferrals (routed-jobs theorem, durable contact-time route, ION via a UDP hop, ...)
- PKT-062 production DTN labs (setup uses the developer `store post`)
- PKT-063 `bp-boundary show` omits receipt-signer rows
- PKT-064 the with-issued waits slot (narrower than filed)
- PKT-363 test_bp_obligation_native's kill between attempt and outcome fails on the candidate's image: C10 or a defect (sweep 10)
- PKT-413 the bprv replay bridge: `fn-bpaj-replay` against `fn-bprr-replay` (sweep 10)
- PKT-415 the fragment/job relation's warm-start theorem (PKT-265's statement) (sweep 10)

### Representation (D27)

- PKT-024 boundary 7: the record codec over the buffer
- PKT-025 boundary 8: the frame codec over the buffer
- PKT-026 boundary 9: the article parser over the buffer
- PKT-027 SHA-256 read from the buffer for trailers and subject ids
- PKT-028 boundary 10: the owner state as a stobj
- PKT-029 the payload arena freeze (records-shape)
- PKT-030 the intent identity as an ACL2-held field
- PKT-031 the checkpoint kernel carries the record list, not a count
- PKT-032 group names walked as character lists
- PKT-033 recovery decodes every record from a fresh list
- PKT-034 `fn-pa-filing-plan` parses an octet list
- PKT-035 the N16 rotation codec on octet lists
- PKT-036 the BP, TCPCL and feed codecs on lists
- PKT-037 fold `records-attach` and `-concrete`; the leaf mbe freeze batch
- PKT-038 the prepare's guard names the list dispatchers (guard only)
- PKT-119 the RFC 5536 grammar out of records-shape (rides a freeze)
- PKT-145 the live-status codec on octet lists (the per-page re-render closed at ea66da80)
- PKT-187 the carrier parse over a payload list on every served POST
- PKT-188 the control request built and decoded as an octet list
- PKT-224 replay dispatch through `fn-stxa-p` on prepare, gate and finish
- PKT-340 the arena grows by doubling: amortized, not a per-step bound
- PKT-349 the checkpoint seal over a buffer range

### Bounds and widths (D27)

- PKT-244 the remaining u64 width migration (checkpoint codec, file machine, observed open, consumer, compaction)
- PKT-181 charge above 2^32-1 refused; retention ledger codecs unaudited
- PKT-270 health `exhausted` never produced natively (the 2^32-2 twin)
- PKT-006 segmented articles (one article is one bounded u32 read)
- PKT-012 header caps as work bounds; a linear header-parse work theorem
- PKT-152 receipt-journal blobs, app-journal count and aggregates
- PKT-182 an overbound control frame reads as uncertain to a client still writing
- PKT-184 the control-signed path gets the codec ceiling, not the served bound

### History reclamation and maintenance (D13)

- PKT-193 spike/storage's reclaim keystones (stub identity, stub codec, D25 under a constrained digest)
- PKT-194 the reclaimed record's replay step; authorship-verdict articles refused
- PKT-237 SCN-060's reclaimed-tombstone arm natively (after the release verb)
- PKT-251 source-routes' tombstone theorems unreachable until a program writes tombstones
- PKT-257 the consumer's unavailable gap unexercised natively
- PKT-196 history compaction as a semantic summary
- PKT-050 covered files checked at open, not ruled out by proof
- PKT-153 reader pins have no durable form
- PKT-263 reclaim-lifecycle-2 steps 3 to 7: holders, per-article release verb, replay proof, guards, N=5,000 (capacity-vector did not reach them; sweep 10)
- PKT-332 `store reclaim` past one quantum refused `spans-links`; the capture's digest length; the mid-chain disk refusal unexercised (sweep 10)
- PKT-416 the reclaim bridge: reopening the rewritten pack equals `fn-rcl-reclaim-state` (sweep 10)
- PKT-362 the capacity vector's debt over replay, a must-fail for the natp debt hypothesis, two unexercised compaction cuts (sweep 10)

### Owner, checkpoint, marker and K0 assurance

- PKT-042 the checkpoint trusted for records below S
- PKT-043 the whole-file statement over the host's range loop
- PKT-044 checkpoint codec round-trip hypotheses without must-fails
- PKT-045 the owner's append-only octet cache, stated not proved
- PKT-046 `fn-ocl-relation` across staging, `:close` and publish
- PKT-192 untoothed hypotheses in the checkpoint-open keystones
- PKT-215 stated marker limits (shared-lock reader above the marker; K0 at the catch-up cuts)
- PKT-086 K0 remainder: frontier publication to end of init, barrier errors with an entry pending
- PKT-216 K0: root barrier errors over a pending rename; the admin publication byte program
- PKT-217 PKT-087 follow-ups (reconfigured stores, a sharper hypothesis, the deployed journal)
- PKT-239 a Message-ID uniqueness invariant for the `:duplicate` keystone
- PKT-250 PRF-123's composition over two host calls, outside the image closure
- PKT-350 the owner's key-statement recovery related by construction, not a theorem
- PKT-206 the C3 owner relation (journal equality, txid order) and owner-level teeth

### Peering and public exposure (sweep 10)

- PKT-356 no future-Date policy (RFC 5537 §3.4 local policy)
- PKT-357 no theorem ties `fn-exp-conns` to `fn-own-conns`

### Consumers beyond the local profile

- PKT-255 remote and multi-group consumer scope with an authenticated version contract

### Python host retirement

- PKT-089 the last twin: the BP drivers' provenance label
- PKT-155 `*fn-store-format-id*` unreferenced; Python read-bound pre-checks
- PKT-272 the Python owner client's article-verdict path never ran
- PKT-017 Python data caps (workflow aggregate, format-7 profiles, 32,768 post read)

### Audit and cleanup

- PKT-075 three dead `fn-pix-` copies
- PKT-122 the uncalled `fn-bpiw-attempt-record`
- PKT-123 `fn-sn-existing-action` uncalled; the v3/v4/v5 constructors
- PKT-124 1,070 unreached definitions; heavy `-by-definition` lemmas
- PKT-118 the pcert Convert wave never ran (77 unresolved pairs)

### Control C4 (deferred by D29)

- PKT-071 C4, group control by article, feed suppression of withdrawn targets

### Decisions with a default in force (decisions-for-ember-2026-09-26.md; nothing in wave 4 waits)

- PKT-127 RFC 5536 special-purpose group names (standing default implemented)
- PKT-173 peering-compose's packets a/b/c (implemented as recommended)
- PKT-230 hold refused signed evidence or keep refusing (refusing, in force)
- PKT-231 the pull cursor as FNPL files (in force)
- PKT-322 a revoked author's retry refused before identity (gate order in force)
- PKT-165 a charged content-holding consumer mode (no implicit pin, in force)
- PKT-229 the policy-member count inside a signed codec (64, the v1 grammar limit)
- PKT-337 field 13 reserved, no >= 64 check (gpt-6's correction to packet 3)
- PKT-296 the unread Store profile field 10 `max-bp-rows`: retire or bind
- PKT-018 T and H from the offline profile to a configuration record
- PKT-076 store identity (a decision candidate from LIST COUNTS)
- PKT-164 the lost-reply 440 case: `store inspect` with the node stopped is built (15c25aef); the privileged query stays ember's (sweep 10)
- PKT-323 capacity-vector's three defaults: the release ceiling, the kept configuration generation, the disk as an assumption (sweep 10)
- PKT-405 what an anonymous reader may do (`none` off loopback in force) (sweep 10)
- PKT-406 the public defaults in force; PROXY v2 the alternative (sweep 10)

## (c) WON'T DO / SUPERSEDED

- PKT-197: superseded by PKT-168 (1) to (3) at 735614d6 (the reconstruction keystone generalized; sweep 10)
- PKT-004: superseded: the ADU, bundle and held-image widths closed at 9ebf5f0e (PKT-276); the fragment recognizers and sender bounds are PKT-185
- PKT-005: superseded: record schema 2 and frontier format 3 landed (4fce0568); the txid, stamp and checkpoint widths are PKT-244, the charge PKT-181
- PKT-047: spike-only artefact: three scratch patches for bounds-p3's image; P3 merged long ago and checkpoint-cost and rep-wave-d-3 replaced its figures
- PKT-049: superseded umbrella: the reclaim lifecycle is PKT-263 (capacity-vector) with PKT-193, 194, 196
- PKT-065: superseded: deploy and qualification go through the coordinator on ember's go (mandate reconciliation); what the labs owe a qualification is PKT-226
- PKT-073: superseded umbrella: friends-peer (PKT-400..403; friends-peer-2 retired PKT-400 and PKT-402, narrowed PKT-403 to the mission TLS pair, left PKT-401 open with its design) with PKT-236, 211, 213
- PKT-114: superseded by ember's ten-second ruling (07:00 UTC: over 10 s only under load is not a problem) and the baseline 04372f7e; owner-invariants is at 10.3 s under load (2e9dc981); a book over 10 s on a quiet box gets a fresh packet
- PKT-225: superseded, as PKT-114: the names were measured under load; five were retired as improved at 04372f7e; assurance-triage (running) takes the four books for-gpt6 §7 names
- PKT-205: superseded, as PKT-114: bp-node-progress-guards and bp-node-retire at 10.9 s were load figures
- PKT-121: operational, not a lane: recertification refills the persvati fasl cache as books are certified (the fasl-cache record); nothing waits on a rewarm
- PKT-149: spike-only: the D28 spike allowance; spikes are over and AGENTS.md forbids skip-proofs toward a claim
- PKT-137: not a cap: an operator-settable default (the line says so)
- PKT-138: not a D27 cap: RFC 3977 §6 limits article numbers to 2^31-1 for every server; it stays a wire limit
- PKT-140: duplicate of PKT-054 (once per contact as a theorem)
- PKT-143: duplicate of PKT-079 (the cheaper marker publication program)
- PKT-129: alias of PKT-008, closed at b0517f04
- PKT-130: alias of PKT-009, closed at b0517f04
- PKT-131: alias of PKT-010 (closed) whose remainder is PKT-152
- PKT-132: alias of PKT-012
- PKT-133: alias of PKT-013
- PKT-134: alias of PKT-014

## Questions for ember

1. **friend-session (PKT-343) needs a person and a machine.** Which friend, on what hardware, and when? The lane is support and a confusion log; it cannot start without them. Until then friends-peer's persvati run is the agent stand-in, not the external observation.
2. **PKT-228 gates upgrade-restore.** Adopt the witness-driven `store rebase` with a durable per-group numbering floor (the coordinator folds gpt-6's PKT-336 correction into the packet first), or pick (b) a new numbering epoch or (c) same-identity restore only from a known-latest backup? The lane's backup, restore and docs work proceeds either way; the success branch waits.
3. **PKT-175 gates part of reader-2.** Adopt a served `:fn-enrollment` HDR item so a reader can show whether a signed post's key is still enrolled (the coordinator recommends yes), authenticated readers only, or leave it "not available"?
4. **PKT-293 and PKT-167 hold rep-wave-d-4 (queued) and, behind it, ingress-span.** Confirm the two-views, shared-transition freeze gpt-6 answered, or overrule.
5. **Pile check: BP large transfers are in AFTER v1** (PKT-308's bp-lifecycle-6, the 10 MiB send PKT-309, the resumable decode PKT-310). gpt-6 ranks the 10 MiB delivery 5th and "in parallel"; friends peering over NNTP does not need it. Keep it out of wave 4, or run bp-lifecycle-6 beside it?
6. **Pile check: consumer-exchange (PKT-333) and multi-peer-relay (PKT-291) are ranked 12th and 13th,** below the peering, restore, operator and scale lanes. gpt-6 made durable consumers and disconnected networking v2's two spines; your aim tonight puts friends' NNTP peering first. Keep that order?
7. **PKT-235 (a chore, your go):** mark the live node's store history-marker `required` now, with a fresh snapshot, after which bbf52159 cannot open it?
8. **PKT-342 (a chore):** adopt gpt-6's AGENTS.md rule ("a producer's admitted domain is a lifecycle contract")? AGENTS.md is yours and the coordinator's to edit.
