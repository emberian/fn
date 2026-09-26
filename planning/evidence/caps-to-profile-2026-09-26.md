# caps-to-profile: the three data caps become profile capacities or work bounds (2026-09-26)

Lane `caps-to-profile` (wave 4), branch `lane/caps-to-profile` from dev
`deb68237` (friends-accounts merged: the tenth configuration slot). PRF-171,
STO-023, SCN-101, PKT-451 (PKT-452 unused: no format bump). D27: bound work,
never data.

## 1. The decision table

| Cap | Today | Class after | Governed by | Format bump? | Rollback consequence |
| --- | --- | --- | --- | --- | --- |
| (A) `*fn-cpp-max-generations*` 4096, checkpoint-publish.lisp:323; packs checkpoint-pack-retire.lisp:8-32 | a LIFETIME cap on generation numbers: nothing reclaims a number, so a store gets 4,096 checkpoint (or pack/compaction) publications | the number is the u32 codec width (iii), as the frontier's; the RETAINED names are a capacity of the profile's T | field 2 `max-transactions` (existing): the next generation exists while fewer than T+1 names are retained and the number is below 2^32-1; the host's listing bound is T+2 (names plus the selection marker) | **no**: generation names are already decimal u32 (`fn-cpp-generation-name-chars` takes any `fn-record-uint32p`), the selection marker is already one CBOR uint32 | an older image reads every directory this lane writes while it holds at most 4,096 names below 4096; a store that has published generation 4096 or above refuses to open under an older image (its namespace plan refuses the name `:bound`/exhausted): the same class as PKT-440 |
| (B) `*fn-cfg-max-rows*` 1024 through `:set-peer`, config.lisp:51/:724 | DATA: `:set-peer` replaces the whole row group, carriage grows it, so one peer holds at most 1,024 rows / 65,538 octets | WORK: 1,024 rows per delta, 64 deltas and 65,538 octets per record, a per-publication bound; the peer's total grows by records | the record count by field 11 (`fn-cvec-config-generations`, `fn-cvec-config-publication-keeps-the-release-generation`), octets by H | **no** (config delta codes 17 and 18, as friends-accounts added 15 and 16; schema-0 records decode unchanged: they are their own translation) | an older image refuses a store whose configuration log holds code 17 or 18 (PKT-440's class); a store that never extended a peer past its first request is unaffected |
| (C) the group-name width: field 7 has no reader; `*fn-record-max-group-name*` / `*fn-cfg-max-label*` 256 | a hidden constant: a profile with field 7 = 100 admits a 256-octet name | DATA governed by field 7; the codec widths rise to the wire's 460 (RFC 3977 section 3.1, a protocol bound, iii) | field 7 `max-group-name-octets` (existing), read by `group create` (`:max-group-name-octets`) | **no**: community-bounds' design (section 3): the ceiling takes field 7, validity only weakens, the format-7 translation keeps 256 | none for a store whose names are at most 256; a name above 256 is refused by an older image's record codec |

Rejected for (A): reclaiming retired numbers. `fn-cprt-next-after-retirement-is-above-selected`
(checkpoint-pack-retire.lisp:184) makes the selected generation a durable
high-water mark, the crash model (`fn-cprt-crash-survivors`) lets an issued
unlink of an older name survive a crash before the directory barrier, so a
reused number could meet a surviving file of the same name; and the ordinary
checkpoint allocator's gap-free contract (`fn-cpp-next-generation-from`) has
no gaps to reuse. Monotone numbering is load-bearing; widening it to the u32
width is not.

Rejected for (B): a profile field for rows per peer (PKT-436's rejected
alternative: a format change that still keeps one peer inside one record).

Rejected for all: a store format 9. Every quantity this lane needs is either
an existing field (T for A, field 7 for C) or a work bound (B). PKT-452 is
therefore not written; the deploy step gains nothing and ember hears nothing.

## 2. (B) A peer's rows: the work bound per delta (PRF-171)

Commit `9755f664`. books/config.lisp: `:add-peer-rows` (code 18) and
`:remove-peer-rows` (code 19; the lane wrote 17 and 18, but keys-and-accounts-2 had merged `:login-binding` as 17 at 02021d18: renumbered at the merge, both sides kept), constructors `fn-cfg-add-peer-rows` /
`fn-cfg-remove-peer-rows`, the row arithmetic `fn-cfg-rows-without-members`
and `fn-cfg-rows-within`. `fn-cfg-delta-reason` names every refusal:
`:peer-rows-empty`, `:peer-rows-unkeyed`, `:no-such-peer`, `:peer-row-absent`
(a removal of a row the group does not hold), `:peer-rows-emptied` (a removal
may not empty a peer; that is `:remove-peer`). `fn-cfg-apply-delta`: an add
leaves the group less the repeated rows followed by the new ones; a removal
drops exactly the listed rows. books/peer-carriage-rows.lisp:
`fn-pcb-extend-deltas NAME NEW PEERS` = the add of NEW, then the removal of
the rows a single-valued slot of NEW supersedes (`fn-pcb-slot-superseded-rows`),
only when there are any. books/native-admin.lisp
`fn-native-admin-plan-deltas-over` emits it.

Theorems (books/peer-carriage-rows.lisp):

- `fn-pcb-extend-deltas-apply-as-the-extend-delta`: `(implies (and
  (true-listp new) (fn-cfg-rows-keyed-p new name)) (equal (fn-cfg-apply v gen
  stamp (fn-pcb-extend-deltas name new (fn-cfg-peers v))) (fn-cfg-apply-delta
  v gen stamp (fn-pcb-extend-delta name new (fn-cfg-peers v)))))`. The
  published record applies as the old whole-group `:set-peer`, so PRF-099's
  `fn-pcb-peer-budget-after-extend-delta` holds of it. (A third hypothesis,
  that the peer exists, was removed after the weakened theorem was proved:
  both sides are the value unchanged when it does not.)
- `fn-cfg-add-peer-rows-refuses-exactly-past-the-work-bound`: for a label
  NAME, a row list ROWS that is non-empty and keyed on NAME, and a peer that
  exists, `(fn-cfg-delta-reason v gen stamp reserved ceiling
  (fn-cfg-add-peer-rows name rows))` is `(if (< *fn-cfg-max-rows* (len rows))
  :malformed-delta nil)`.
- `fn-cfg-add-peer-rows-extends-the-group`: with ROWS a true list keyed on
  NAME, the group after the delta is `(append (fn-cfg-rows-without-members
  existing rows) rows)`: no bound but the records that built it.
- `fn-cfg-apply-delta-adds-at-most-the-work-bound` (linear): every
  `fn-cfg-deltap` delta grows the peers slot by at most 1,024 rows;
  `fn-cfg-apply-adds-at-most-the-work-bound`: a delta list by at most 1,024
  times its length (a record holds at most `*fn-cfg-max-deltas*`; the record
  count is `max-config-generations`, `fn-cvec-config-publication-keeps-the-
  release-generation`, cited).

Host lines: `fn-native-admin-plan-deltas-over` is called by
host/native-admin-host.lisp `fn-native-admin-host-apply` (offline, the
replayed table) and `fn-native-admin-host-owner-reconfigure` (the live
owner's table); the record is admitted by `fn-store-cfg-peer-delta-record`
(host/store-node-host.lisp) through `fn-cnode-record-acceptablep`, and
replayed at open by `fn-cfg-record-acceptablep` / `fn-cfg-apply-record`, the
same `fn-cfg-delta-reason` and `fn-cfg-apply-delta`.

Teeth (tests/acl2/peer-carriage-tests.lisp, PRF-171 section): a peer of 1,025
rows takes one more (1,026, every earlier row kept); a 1,024-row delta is
admitted and a 1,025-row one is `:malformed-delta`; one refusal per
hypothesis of the exact-bound keystone (a 257-octet name, a non-uint32 row, no
rows, unkeyed rows, no such peer); must-fails for the keyed and true-list
hypotheses of the extension keystone and of the refinement keystone (rows
keyed on another peer apply in another order; an improper row list); the
work bound reached by exactly 1,024 rows and passed by a malformed 1,025;
the budget request's two deltas (add, then remove the two old budget rows),
admitted, equal to the whole-group extension, budget (5 3); the two new
refusals; codes 18 and 19 round-trip and a record holding both encodes and
decodes to itself. tests/acl2/native-admin-tests.lisp: the `peer budget` and
`peer carries` plans publish the incremental deltas, and applied give the
answers the whole-group delta gave.

Replay and translation: codes 1 to 16 decode exactly as before (the decoder
is unchanged on them; friends-accounts' 279-octet literal test keeps checking
the old kinds byte-identically), so a schema-0 `:set-peer` record is its own
translation; nothing at open rewrites anything.

Assurance chain: native entry `operator CONFIG peer carries|budget` ->
`fn-native-admin-plan` -> `fn-native-admin-plan-deltas-over` ->
`fn-pcb-extend-deltas` -> refinement `fn-pcb-extend-deltas-apply-as-the-
extend-delta` -> the admitted record (`fn-cfg-delta-reason`, exact bound) ->
`fn-cfg-add-peer-rows-extends-the-group` -> observed: `peer list` after a
fresh open (SCN-101). The maintained relation is `fn-cfg-valuep` (the peers
slot a row list): `fn-cfg-apply-delta-preserves-valuep`
(books/config-invariants.lisp) covers both new arms.

## 3. (A) Checkpoint generations: uint32 numbering, profile capacity (PRF-171)

Commit `e10e4530`. books/checkpoint-publish.lisp: `*fn-cpp-max-generations*`
and the constant observation limit are gone; `fn-cpp-generation-capacity T` =
T + 1; `fn-cpp-namespace-observation-limit CAPACITY` = CAPACITY + 1 (the
selection marker); `fn-cpp-next-generation(-from)`, `fn-cpp-namespace-plan`
and `fn-cpp-publication-initial` take CAPACITY.
books/checkpoint-pack-retire.lisp: `fn-cprt-generationsp` is the strictly
increasing uint32 shape (no length cap); `fn-cprt-next-generation GENERATIONS
CAPACITY` refuses `:exhausted` at CAPACITY retained names; `fn-cprt-next-from`
numbers to the uint32 maximum. Host: host/checkpoint-host.lisp
`fn-store-checkpoint-generation-capacity VALUES` (the opened profile's T + 1)
and every namespace wrapper take the profile; host/native/checkpoint.lisp
passes `(fnn-store-config store)` and refuses by name ("checkpoint
generations at the profile's capacity (max-transactions + 1)", and for packs
"retire older generations or raise it"); tools/checkpoint.py passes
`store.config["profile"]`.

Theorems:

- `fn-cpp-next-generation-refuses-exactly-at-the-profile-capacity`:
  `(implies (and (not (equal (fn-cpp-next-generation names capacity) :bad))
  (<= (nfix capacity) (+ 1 *fn-cbor-max-uint*))) (equal
  (fn-cpp-next-generation names capacity) (if (<= (nfix capacity) (len
  names)) :exhausted (len names))))`. Host: `fnn-checkpoint-publish` ->
  `fn-store-checkpoint-next-generation` and
  `fn-store-checkpoint-publication-initial`.
- `fn-cprt-next-generation-refuses-exactly-at-the-profile-capacity`: on
  `fn-cprt-generationsp`, `:exhausted` exactly at CAPACITY retained names or
  a highest name at the uint32 maximum, else the highest plus one. Host:
  `fnn-pack-publish-generation` -> `fn-store-checkpoint-pack-next-generation`
  and `-pack-publication-initial`.
- Carried unchanged in statement: `fn-cprt-next-after-retirement-is-above-
  selected` (now with the CAPACITY argument), the durable high-water mark.
  PRF-085's chain keystones (books/checkpoint-pack-chain.lisp) are untouched.

Teeth: 4,097 retained names under T 8191 give 4097; the old figure is the
instance T 4095 (capacity 4096: 4,096 names exhausted, 4,095 names give
4095); a gapped namespace is `:bad` (must-fail for that hypothesis); the
uint32 width (must-fail past it); packs: `(70000)` under capacity 2 gives
70001, two names exhausted, `(4294967294)` gives 4294967295, the maximum is
exhausted, an unordered list is `:invalid` (must-fail).

Rollback: an older image refuses a checkpoint or pack directory holding a
name at or above 4096 (its generations-after-p / next-from) or more than
4,097 entries (its observation limit). Nothing is written at open.

## 4. (C) The group-name width: NOT touched

This lane did not edit books/records-shape.lisp or books/byte-store-frame.lisp.
The design stands as community-bounds section 3 wrote it and is PKT-451, a
freeze batch the deputy schedules.

## 5. Certification

Every changed book and its test book ran first in the REPL on persvati
(/home/ember/fn-gates/caps-to-profile-repl: books/config 247 forms,
config-invariants, peer-carriage-rows and the PRF-171 teeth in session
`ctp-cfg`; checkpoint-publish 102 forms, checkpoint-pack-retire and both test
books in `ctp-cpp`). One REPL-invisible failure reached the farm: the
checkpoint-publish test book did not include must-fail (the session had it
loaded by hand), r2.

| Run | Box, toolchain | Rev | Scope | Result | Manifest |
| --- | --- | --- | --- | --- | --- |
| run-20260926T112246Z-06cd | persvati, w25, 2 jobs, 300 s | 9755f664 | `--affected-by` config, peer-carriage-rows, native-admin, config-invariants (config's closure) | 399 passed, 0 failed | `certify-20260926T112332Z-985333.json` |
| run-20260926T113419Z-7e19 | persvati, w25 | e10e4530 | `--affected-by` checkpoint-publish, checkpoint-pack-retire | 7 passed, 1 failed (the test book's missing include) | `certify-20260926T113443Z-1122513.json` |
| run-20260926T113603Z-8408 | persvati, w25 | a8e9914f | the same | 1 passed (the repaired test book), 176 from the cache | `certify-20260926T113632Z-1144441.json` |

Books over 10 s in r1, none of them changed here except native-admin (one
arm of `fn-native-admin-plan-deltas-over` now calls `fn-pcb-extend-deltas`):
native-admin 11.2 s; today's manifests measure it between 8.9 s and 15.0 s
(095234Z 13.1, 102123Z 15.0, 105643Z 9.3), so this is its variance under
contention, not a change of this lane; it is still a D26 debt (PKT-451 names
it). The others over 10 s (owner-invariants 16.3, config-owner-live 11.9,
native-operator 11.3, public-exposure 10.8, source-routes-tests 10.0) were
recertified as config's dependents at unchanged bytes.

## 6. Native (SCN-101), hbox, tools/hbox_native.sh

- (A) `tests.test_native_checkpoint_generations` on a8e9914f (native-a1,
  /tank/fn/scratch/caps-to-profile/native-a1): both cases OK in 2.0 s:
  4,097 retained generations under `--max-transactions 8191` and the next
  publication prints `generation=4097`; under 4095 the 4,097th is refused
  exit 1 naming the profile's capacity with the directory unchanged.
  `tests.test_native_checkpoint` OK (4 skipped, as on dev: production-image
  and Python-host cases). Log
  planning/evidence/caps-to-profile/native-checkpoint-generations.log
  (sha256 90d8f09a...), sums native-a1-SHA256SUMS (developer image
  33ac181a...).
- (B) `tests.test_native_peer_rows_growth` on 9755f664 (native-b1,
  /tank/fn/scratch/caps-to-profile/native-b1): OK. 1,100 separate
  `peer carries far HEX` requests, each exit 0, in 8,335.9 s (the O(N^2)
  offline replay of section 7 item 2); `peer list` after a fresh open lists
  all 1,100 principals in request order (past the old 1,024); two
  `peer budget` requests over the grown group keep every principal; a
  repeated principal adds no row. Log
  planning/evidence/caps-to-profile/native-peer-rows-growth.log (sha256
  ed83cdb4...), sums native-b1-SHA256SUMS (developer image 038accbb...).
  `NativeOperatorPeerListTests` ran with all 4 cases SKIPPED (they need the
  production image, which this run did not build): no evidence from it.

## 7. Not done (PKT-451)

1. (C) the group-name width: field 7 read by `group create`
   (`:max-group-name-octets`), the ceiling `(+ 5 n)` per group, widths to
   460, the format-7 translation keeping 256, the preset reopen witnesses.
   records-shape and byte-store-frame were never edited here: a freeze the
   deputy schedules.
2. Found by SCN-101 (measured, not profiled): every offline `operator` request
   replays the whole configuration log at open, so one `peer carries` costs
   about 2.4 s at 100 records and about 9 to 10 s at 700 to 800 on hbox, and
   N requests cost O(N^2). This is not a cap and not new (the whole-group
   `:set-peer` path replayed the same log, with larger records), but it is
   work that grows with data per request on the offline path; a configuration
   checkpoint or the live owner's arm is the remedy.
3. The pack path past 4,096 natively (`store compact` with retirement over
   more than 4,096 publications) is covered by the ACL2 teeth only; the
   native case exercised the ordinary checkpoint allocator.
4. The live owner's `peer carries` arm
   (`fn-native-admin-host-owner-reconfigure`) runs the same
   `fn-native-admin-plan-deltas-over`, but only the offline arm ran natively.
5. The rollback consequence (an older image refusing codes 18 and 19, or a
   generation name at or above 4096) is stated, not rehearsed on a copy.
6. native-admin at 11.2 s in r1 (its variance today is 8.9 to 15.0 s): a D26
   debt this lane did not create.
7. `make check-lane` is RED on the D26 timing ratchet only, from r1's
   measurements of books this lane did not edit but recertified as config's
   dependents: owner-invariants 16.3 s (baseline 10.3 s; 12.7 s after
   friends-accounts), config-owner-live 11.9 s, native-operator 11.3 s. The
   two new `fn-cfg-apply-delta` arms may add case splits where those books
   open it; not yet examined (accumulated-persistence in the REPL on
   owner-invariants is the next action). No baseline was edited.

## Continuation (caps-to-profile-2, 2026-09-26)

Lane `caps-to-profile-2`, branch `lane/caps-to-profile-2` from dev `a931ed8d`.
IDs: PRF-186 (new), PRF-171 (extended for field 7), STO-025, SCN-115,
PKT-510 (what remains). PKT-511 unused (no decision for ember). No
configuration delta code, wire kind or store format was taken (the codes on
dev stay 17 `:login-binding`, 18 `:add-peer-rows`, 19 `:remove-peer-rows`;
no other file names 17/18 for the peer rows).

### C1. PKT-501: the offline request's cost, measured, then fixed (PRF-186)

Where the time went, measured before choosing a design (persvati REPL, the
SCN-101 shape built in ACL2: one `:set-peer` then 1,099 `:add-peer-rows`
records of one 64-octet principal each):

| At dev a931ed8d | 550 records | 1,100 records |
| --- | --- | --- |
| `fn-cnode-config-replay` | 0.43 s | 1.61 s, 6.6 GB consed |
| `fn-cpr-replay` (the open's fold) | | 2.43 s, 9.9 GB consed |
| decoding the 1,100 records (`fn-cfg-decode-exact`) | | under 0.05 s, 23 MB |
| `fn-cfgp` of the final configuration, once | | 5.9 MB |

The cost was not the image start, not the reads and not the decode: every
replay fold ran the whole-configuration recognizer `fn-cfgp` (every row of
every slot) inside `fn-cnode-record-acceptablep` two or three times per
configuration record, plus `fn-cnode-statep` of the advanced node (which
includes `fn-cfgp` and the node recognizer), so one replay was O(records x
configuration size). An offline request runs about five replays of the whole
log: `fnn-recover` at open (`fn-store-sn-recover`: `fn-sco-extend` ->
`fn-sco-store-open` -> `fn-cpr-loop`), `fnn-admin-authorize`
(`fn-store-cfg-native-admin-authorize` -> `fn-native-admin-publication-authorize`:
`fn-cnode-config-replay`, then `fn-native-admin-candidate-open-result`:
`fn-cnode-config-replay`, `fn-cpr-replay`, `fn-cpo-open-observed`) and
`fnn-admin-verify-under-lock` (`fnn-recover` again). This is AGENTS.md's
"no whole-state revalidation on a served path", in the config arm that
bounds-p3 finding 2 had left because "there are few" configuration records.

The cheaper true fix (commit `c5233ed4`): the folds carry the invariant.
books/node-config.lisp defines `fn-cnode-carried-acceptablep` (every
conjunct of `fn-cnode-record-acceptablep` but `fn-cfgp`) and proves

- KEYSTONE `fn-cnode-record-acceptablep-is-the-carried-check`:
  `(implies (fn-cfgp (fn-cnode-config cn)) (equal (fn-cnode-record-acceptablep
  cn record ceiling) (fn-cnode-carried-acceptablep cn record ceiling)))`;
- `fn-cnode-advanced-node-is-configured`: `(implies (fn-cnode-statep cn)
  (fn-cnode-statep (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn)
  txid) (fn-cnode-config cn))))`.

`fn-cnode-apply-config`, `fn-cnode-replay-loop`, `fn-cpr-loop`
(books/config-physical-replay.lisp) and `fn-sco-cpr-prefix`
(books/store-checkpoint-open.lisp) run the carried check, and the last two
skip the advanced node's recognizer, under `:exec`; each `:logic` body is
unchanged, so no theorem statement moved, and each `verify-guards` proves
the `:exec` equal to the `:logic` with the two theorems above. The host
subjects: host/native/io.lisp `fnn-bridge-recover` (every open) and
host/native/admin.lisp `fnn-admin-authorize` (every publication, offline and
live). After, same REPL measurement: `fn-cpr-replay` of 1,100 records 0.12 s
and 139 MB (from 2.43 s and 9.9 GB), `fn-cnode-config-replay` 0.13 s,
`fn-sco-store-open` 0.13 s.

Not chosen: the configuration checkpoint of the brief. The measurement put
the cost in revalidation, not in the log's length, and the brief's rule was
to take the cheaper true fix. What the checkpoint would still buy is below.

Native, hbox, `tests.test_native_peer_rows_growth` (developer image):

| Run | Image | Requests | Seconds | Per request |
| --- | --- | --- | --- | --- |
| predecessor native-b1 | 9755f664 | 1,100 | 8,335.9 | 7.58 s |
| native-base | a931ed8d (dev) | 300 | 251.7 | 0.84 s |
| native-base | a931ed8d (dev) | 1,100 | 8,156.8 | 7.42 s |
| native-after2 | bf00ae29 | 300 | 58.5 | 0.20 s |
| native-after1 | c5233ed4 | 1,100 | 1,058.3 | 0.96 s |

1,100 requests on the same day: 8,156.8 s at dev a931ed8d -> 1,058.3 s
(7.7x; the predecessor's 8,336 s at 9755f664 agrees); 300 requests: 251.7 s -> 58.5 s
(4.3x). native-after1 ran while native-base's 1,100-request run (below) was
using the box. NOT linear: 300 requests average 0.20 s and 1,100 average
0.96 s, so a request still costs O(configuration records), now about 1 ms
per record per request: every request still reads, decodes and folds the
whole log about five times, and an `:add-peer-rows` apply copies the peer's
group (138 MB consed per 1,100-record replay). A configuration checkpoint
that the open resumes from, with its refinement to the full replay (the
split theorem `fn-cnode-replay-loop-splits-at-any-prefix` is the start), and
one replay per request instead of five, are PKT-510.

Logs: planning/evidence/caps-to-profile/native-peer-rows-growth-after.log
(sha256 431bcc40...; native-after1-SHA256SUMS, developer image core
91f321b2...), native-peer-rows-growth-base-300.log (20d01251...),
native-peer-rows-growth-base-1100.log (9c453776...),
native-peer-rows-live-and-rollback.log (028e3cfd..., the 300-request line
and C3), native-after2-SHA256SUMS (developer launcher 233d4add..., production
69ef2eea...).

Crash points: no host code changed in C1 (no `fnn-at` site, no program
step); `tools/native_program_check.py` is part of `make check-lane`, green.

Assurance chain: native entry `operator CONFIG peer carries` ->
`fnn-admin-execute` -> `fnn-open-live-store`/`fnn-bridge-recover`
(`fn-store-sn-recover`) and `fnn-admin-authorize`
(`fn-store-cfg-native-admin-authorize`) -> the four folds, whose `:exec` is
the carried check -> refinement `fn-cnode-record-acceptablep-is-the-carried-check`
(and `fn-cnode-advanced-node-is-configured`) -> maintained relation
`fn-cnode-statep`, established by `fn-cpr-initial-cnode-statep` at the
initial node and preserved by `fn-cnode-apply-config-preserves-state` and
`fn-cpr-apply-event-preserves-cnode-statep` -> the unchanged replay theorems
-> observed: 1,100 requests all exit 0 and `peer list` names the 1,100
principals in order (SCN-101, SCN-115).

Teeth (tests/acl2/config-physical-replay-tests.lisp, PRF-186 section): a
reachable node (the file's replayed history) and the next record: antecedent
true, both checks T; a late record: both NIL; the host's `fn-cpr-replay` of
the history plus that record gives the one-step `fn-cnode-apply-config`
node; the hypothesis: a node whose quota slot is not a row list fails
`fn-cfgp`, the carried check admits the record and the node's check refuses
it (asserted, and the ground `must-fail`); the advanced-node lemma: the
reachable node advanced to txid 8 is configured, from the malformed node it
is not (asserted, ground `must-fail`).

### C2. PKT-451 (C): field 7 read at both intakes (PRF-171 extended)

Commit `bf00ae29`. Field 7 `max-group-name-octets` had no reader. Now:

- books/store-capacity-config.lisp `fn-cvec-native-admin-authorize`: a
  record creating a group whose name is longer than field 7 is refused
  `:max-group-name-octets`, else it is the publication authorization it
  replaced. Host: host/store-node-host.lisp
  `fn-store-cfg-native-admin-authorize`, called by host/native/admin.lisp
  `fnn-admin-authorize` (offline `fnn-admin-execute` and the live owner's
  `fnn-owner-live-reconfigure-locked`). KEYSTONES
  `fn-cvec-native-admin-authorize-refuses-exactly-past-the-group-name-bound`
  (the refusal iff a created name exceeds field 7; within it, equal to
  `fn-native-admin-publication-authorize` under `fn-cvec-config-generations`,
  so PRF-102's and PRF-138's keystones carry) and
  `fn-cvec-accepted-group-names-are-within-the-profile`.
- books/native-operator.lisp `fn-nop-parse-init-plain`: `init` refuses
  `:max-group-name-octets` by name; KEYSTONE
  `fn-nop-init-plain-groups-are-within-the-profile` (an accepted plan's
  groups are within the field 7 of the profile it resolves).

No format bump, and D27's three agree: field 7 was already validated at most
the codec width (byte-store-frame `fn-bs-profile-invalid-reason`,
`:max-group-name-octets-outside-codec`), the representation (the 256-octet
record and label widths) is unchanged, and no format evolves; a saved
profile's field 7 now governs what it always named. The widths rising to the
wire's 460 (RFC 3977 section 3.1) with the ceiling taking field 7 remain:
the records-shape and byte-store-frame freeze, PKT-510.

Teeth: tests/acl2/store-capacity-config-tests.lisp (a 100-octet name under
field 7 = 100 is accepted at generation 2 and equals the publication; 101 is
refused by name and the publication alone would have accepted it; the
default field 7 = 256 accepts 101; a record creating no group is untouched
at field 7 = 1; the acceptance hypothesis, ground); tests/acl2/native-operator-tests.lisp
(init at the bound accepted with its groups within; 101 refused by name;
default accepts; the acceptance hypothesis: a non-accepted result whose
arguments hold a 101-octet name is not within, asserted and ground).

Native (native-after2, bf00ae29, developer image):
`tests.test_native_group_name_bound` OK, 3 ran: under
`--max-group-name-octets 100` a 100-octet `group create` exits 0, a
101-octet one exits 1 naming MAX-GROUP-NAME-OCTETS with the configuration
directory unchanged; `init` of the 101-octet name exits 1 by name and
writes no store; the default profile creates it. Log
native-group-name-bound.log (sha256 c9fcce59...).

### C3. Sweep 19's additions (PKT-451 (4), (5), (6))

- (4) The live owner's arm, natively: `NativePeerRowsLiveTests` (native-after2):
  with a node running, `peer add`, three `peer carries` and two `peer budget`
  go through the control socket to `fnn-owner-live-admin-serialized` ->
  `fn-native-admin-host-owner-reconfigure`, all exit 0; after SIGTERM (exit
  0) `peer list` names the three principals and the second budget only
  (`:remove-peer-rows` applied live).
- (5) The rollback, rehearsed on copies: the bbf52159 production image (the
  qualification gate's copy, /tank/fn/gates/qual-bbf52159-20260925, never
  /tank/fn/node) opens a fresh store `status` exit 0 and refuses the store
  holding codes 18 and 19, exit 4 "ACL2 refused configuration namespace
  observation". docs/operator.md's rollback section says so (PKT-440's rule).
  Log native-peer-rows-live-and-rollback.log (028e3cfd...).
- (6) `tests.test_native_operator_verbs` with `--images developer,production`:
  22 ran, 0 skipped; `NativeOperatorPeerListTests` all 4 OK on the production
  image. One failure, not this lane's and not behaviour:
  `NativeOperatorVerbCompositionTests.test_peer_list_is_a_query_and_the_host_asks_acl2_which`
  greps books/native-admin.lisp for `(fn-native-admin-peer-report ...)`,
  which a50312ef1 (PKT-391) renamed to `fn-native-admin-peer-budget-report`
  (a stale source-shape test, harness class; PKT-510). Log
  native-operator-verbs-after2.log (95faffac...).
- `tests.test_native_checkpoint_generations` OK (2), `tests.test_native_capacity_vector`
  OK (1); `tests.test_native_admin` SKIPPED 9 of 9 (it needs explicit
  source and launcher SHA values hbox_native.sh does not set): no evidence
  from it.

### C4. D26

PKT-502 closed the owner-invariants examination at batch Z (10.8 s at two
jobs, within its baseline). This lane's r1 installed owner-invariants from
the cache (it does not include the changed books), so nothing here moves it.
The one book over 10 s in r1 was this lane's own
tests/acl2/store-capacity-config-tests (25.4 s: a general must-fail the
prover searched for 24 s), fixed by a ground instance, r2 (no book over 10 s).

### C5. Certification

REPL/incremental on persvati first (~/fn-gates/caps-to-profile-2-repl, every
changed book and test book). Farm, persvati, w25, 2 jobs, 300 s:

| Run | Rev | Scope | Result | Manifest |
| --- | --- | --- | --- | --- |
| run-20260926T153104Z-77b9 | bf00ae29 | `--affected-by` node-config, config-physical-replay, store-checkpoint-open, store-capacity-config, native-operator | 151 certified, 0 failed, 291 from the cache; store-capacity-config-tests 25.4 s | certify-20260926T153141Z-3460348 |
| run-20260926T154025Z-581e | e77f5af8 | store-capacity-config-tests | 1 passed, none over 10 s | certify-20260926T154049Z-3549609 |
| run-20260926T154352Z-aee1 | ee5dd011 | config-physical-replay-tests | 1 passed, none over 10 s | certify-20260926T154415Z-3583008 |

### C6. Not done (PKT-510)

1. A configuration checkpoint the open resumes from (its refinement to the
   full replay), and one replay per offline request instead of about five:
   the remaining O(records) per request (0.96 s average at 1,100).
2. The group-name width to 460: `fn-record-encoded-octets-ceiling` taking
   field 7, validity weakened, the format-7 translation keeping 256,
   `fn-bs-profile-admits-every-article-record` with the name hypothesis, the
   preset reopen witnesses (records-shape and byte-store-frame freeze).
3. The pack path past 4,096 natively (PKT-451 (3)).
4. The stale source test in test_native_operator_verbs (a50312ef1).
5. PKT-451 items 1 to 5 of the packet body beyond (C) were not reached.
