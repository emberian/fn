# community-bounds: the community counts come from the profile (2026-09-26)

Lane `community-bounds` (wave 4 lane 7), branch `lane/community-bounds` from
dev `eb79070b`. PRF-167, STO-021, SCN-097, PKT-435, PKT-436. Commits: see
"Commits" at the end.

## 1. The table

Every constant the brief named, classified as one of three classes:

- **(i) DATA**: governed by an existing profile field.
- **(ii) WORK**: a work bound on one record of fixed shape. It cannot grow
  with the node's data, and its producer or decoder does a bounded amount of
  work per step.
- **(iii) CODEC**: a generic width that must never cap below any valid
  profile.

Rows marked **DATA, no field** are defects. Each one caps the node's data and
no profile field governs it. They are carried in PKT-435 or PKT-436. No new
profile field was added.

| Constant | Value | Where | Class | Why (one sentence) | Evidence |
| --- | --- | --- | --- | --- | --- |
| `*fn-cp-max-consumers*` | 256 | consumer-position.lisp:9 | **(i) field 9, done** | The consumer table is the node's data; the served registration now refuses past the profile's `max-consumers`, and the constant is gone. | `fn-cp-register-within-refuses-exactly-past-the-operator-bound`, section 2 |
| `*fn-record-max-group-name*` | 256 | records-shape.lisp:50 | (iii), capping field 7 | It is the group-name width of the record codec; `fn-bs-profile-validp` bounds field 7 by it (`fn-bs-profile-validp-codecs-accept`), so today no valid profile passes it. | byte-store-frame.lisp:208, :398 |
| `*fn-cfg-max-label*` | 256 | config.lisp:50 | (iii) | It is the width of every configuration label: group names, policy ids, quota scopes, listener addresses, peer names and EIDs, principals in hex, and patterns. | `fn-cfg-labelp-of-record-group-name` (config.lisp:87) ties it to the group-name width |
| `*fn-cpp-max-generations*` | 4096 | checkpoint-publish.lisp:323 | **DATA, no field** | It caps checkpoint generation NUMBERS: `fn-cpp-next-generation-from` returns `:exhausted` at 4096 and retirement frees no number, so a store gets 4096 checkpoint publications in its lifetime. | section 4 |
| `*fn-cfg-max-deltas*` | 64 | config.lisp:52 | (ii) | Deltas in one record, one publication; 2000 groups take 32 or more records of `:create-group` deltas, each carrying no rows. | config.lisp:1179, :1474 |
| `*fn-cfg-max-rows*` | 1024 | config.lisp:51 | **DATA, no field** (through `:set-peer`) | `:set-peer` replaces a peer's whole row set, and carriage (peer-carriage-rows.lisp:113-117 `fn-pcb-extend-rows`) grows it, so a peer's carried principals, budgets and patterns stop at 1024. | PKT-436 |
| `*fn-cfg-max-items*` / `*fn-cfg-max-octets*` | 65535 / 65538 | config.lisp:53-54 | (ii) for a delta batch; **DATA** through `:set-peer` | These are per-record figures; they are work bounds only while no single delta carries growing data. | config.lisp:1333 decodes through the generic `fn-cbor-decode`; PKT-436 |
| `*fn-cbor-max-bytes*` | 65535 | cbor.lisp:25 | (iii) | Only the legacy generic entry defaults to it; the record codec uses the bounded API at `*fn-record-max-octets*` = 2^32-1. | records.lisp:59-89 |
| `*fn-cbor-max-input*` | 65538 | cbor.lisp:28 | (iii) | The generic one-item entry. It is used by the statement codec, the checkpoint selection frame (one uint32), bp-adu, and config (`fn-cfg-decode-exact`, host/store-node-host.lisp). Each caller's record is (ii), except config through `:set-peer`. | cbor.lisp:375 |
| `*fn-stxe-max-octets*` | 65538 | stx-evidence-records.lisp:15 | (ii) | A statement-verdict event is node-generated, with a fixed 11-item shape. | stx-evidence-records.lisp:201 `fn-stxe-decode-exact` |
| `*fn-stxe-max-detail*` | 8192 | stx-evidence-records.lisp:17 | (ii) | The detail is a principal, two keys and two signatures (about 5.4 KB, hybrid-store.lisp:144-168), a 32-octet principal, or a reason token. | hybrid-store.lisp:144 |
| `*fn-stxk-max-snapshot*` | 65536 | stx-keyring-records.lisp:17 | (ii) | A snapshot is one principal and its two public keys (`fn-hsig-keyring-snapshot`, a fixed five-item list, about 2 KB), and each principal is its own event. So it does not cap the principal count; H does. | hybrid-store.lisp:67-89; `fn-hsig-keyring-event-snapshot-bound` (:762) |
| `*fn-stxk-max-octets*` | 131072 | stx-keyring-records.lisp:15 | (ii) | It caps one kind-3 envelope: fixed uints, a profile tag and one snapshot. | stx-keyring-records.lisp:87 |
| `*fn-stxk-max-profile*` | 64 | stx-keyring-records.lisp:16 | (ii) | A profile tag is a short constant (`fn-hybrid-v1`). | stx-accept-records.lisp:48 |
| `*fn-pol-max-members*` | 64 | policy.lisp:59 | protocol grammar limit (PKT-229, PKT-337) | It sits inside a signed statement's codec. A per-node figure would split authority, so it is statement schema v1's grammar limit and not a work limit. Field 13 has no reader and is to be marked reserved. | section 6 |
| `*fn-feed-max-payload*` | 1024 | peer-feed.lisp:850 | (ii), fit unproved | It bounds one FNFD tuple. `:feed-intent` has four frame texts of at most 512 each, so the grammar's worst case (about 2070) is above 1024; the encoder refuses (`:bad`), it never truncates. | PKT-435 |
| `*fn-sched-max-payload*` | 4096 | scheduler.lisp:420 | (ii) | It bounds one FNSC decision: three texts of at most 512 and naturals, so it fits. | scheduler.lisp:437 |
| `*fn-anchor-max-payload*` | 1024 | anchor-record.lisp:52 | (ii) | It bounds one FNAN record of fixed-length keys, signature, nonce and root. | anchor.lisp:247-263; host/anchor-host.lisp:72 |
| `*fn-cp-max-token*` | 512 | consumer-position.lisp:8 | (ii) | A cursor is a fixed tuple of ids of at most 64 octets and u32s; the encoder's figure is 346 (`fn-cp-cursor-encode-length-bound`). | host/native/signature-command.lisp via `fn-cp-cursor-decode` |
| `*fn-th-topic-max-octets*` | 1024 | topic-history-store-events.lisp:9 | (ii) | It bounds one install, anchor or admit tuple of at most 24 items. | topic-history-store-events.lisp:187, :199 |

**Counts:**

- (i) DATA governed by a field: 1, consumers, done in this lane.
- (ii) WORK: 12. Two of them are also DATA through `:set-peer`: config
  items and octets.
- (iii) CODEC: 4. These are the group-name width, the label width and the
  two generic CBOR figures.
- Protocol grammar limit: 1, policy members.
- DATA with no field (defects): 2. They are `*fn-cpp-max-generations*` and
  `*fn-cfg-max-rows*`, the latter carrying items and octets with it.

The PKT-135 five have a comment at each constant naming the class (commit
54104a12).

**Finding on PKT-003.** The packet's premise is wrong: a keyring snapshot
holds one principal and does not cap the principal count, so no format change
is needed. The principal count is bounded by H. Field 12 counts AUTHINFO
logins, which is a different namespace. The packet is retired.

## 2. Field 9 governs the consumer count (PKT-157, PKT-001 row)

**The subject and how it changed** (books/consumer-position.lisp):

- `fn-cp-register-within (s max caller consumer query qver view)` is
  `fn-cp-register` under the operator's count. A register write that would
  hold more than MAX entries is refused `:max-consumers`, and every other
  answer is `fn-cp-register`'s.
- `*fn-cp-max-consumers*` is removed from the decision, from the applier
  `fn-cp-apply` and from the state recognizer `fn-cp-statep`.
- Replay (`fn-cpe-projection-step`, books/consumer-store-projection.lisp)
  re-runs the validity decision `fn-cp-register` and not the admission
  bound. The reasons:
  - The profile only rises (`fn-profile-upgrade-keeps-namespace-counts`).
  - A register the node committed under an older bound is therefore within
    the current one.
  - A replay that refused it would be whole-state revalidation of a
    decision the served path already made (AGENTS.md "No whole-state
    revalidation").
  - Threading MAX through replay would change the statements of the
    projection replay and step. More than 15 books state theorems over those
    (store-node-traces*, consumer-store-invariants, store-open-bridge and
    others).
- **Departure from the brief: replay does not refuse past the profile's
  figure.** The brief asked that "the replay that refuses past 256 refuse
  past the profile's figure". Replay no longer refuses at any figure. Past
  the bound, the admission is refused by name. The table's bound is carried
  by `fn-cp-apply-preserves-consumer-capacity` together with the upgrade
  keystone.
- The reason is `:max-consumers` (the field's name, as the configuration
  writer's `:max-config-generations`), not `:budget`. `:budget` in the
  bounds-profile pattern is the listing reader's word.

**Host chain:**

1. host/native/owner.lisp `fnn-owner-consumer-local-serialized` (`:register`)
2. host/owner-host.lisp `fn-owner-consumer-local-register`, which passes
   `(fn-store-profile-max-consumers (fn-owner-store-profile state))`. That is
   the profile installed at open, read by ACL2 through
   host/store-host.lisp `fn-store-profile-max-consumers` =
   `fn-bs-profile-max-consumers`. A format-7 store reads its translation's
   2^20.
3. books/consumer-owner-local.lisp `fn-col-register (o max consumer group)`
4. `fn-cp-register-within`

The `:write` it returns is published by the owner and re-decided at replay
by `fn-cp-register`. Replay accepts the same event, because the write of
`fn-cp-register-within` equals that of `fn-cp-register` (conjunct 2 of the
first keystone below).

**Theorems (PRF-167)**, in books/consumer-position.lisp:

- `fn-cp-register-within-refuses-exactly-past-the-operator-bound` (KEYSTONE):
  - The result is `(:refused :max-consumers)` iff `fn-cp-register` answers
    `:write` and `(<= (nfix max) (len entries))`.
  - Otherwise the result is `fn-cp-register`'s.
  - It has no hypothesis.
- `fn-cp-apply-preserves-consumer-capacity` (KEYSTONE, restated):
  - It assumes `len <= (nfix max)`, and that the event is not a register or
    is the served decision's write at `s` under `max`.
  - It concludes `len (fn-cp-apply s event) <= (nfix max)`.
  - With `fn-profile-upgrade-keeps-namespace-counts`, the table stays within
    the profile across reopen.
- `fn-cp-apply-grows-only-by-a-register` (lemma): only a register grows the
  table, and by one entry.
- `fn-cp-apply-preserves-statep` and `fn-cp-apply-trace-preserves-statep`:
  unchanged statements. The recognizer lost its length conjunct.

**Teeth:**

- tests/acl2/consumer-position-tests.lisp. Every pre-D27 witness runs at
  `*cpt-old*` = 256.
  - Positive witnesses:
    - The 256th register is a write under 256.
    - The 257th is refused `:max-consumers` under 256.
    - The 257th is a write under 300, equal to `fn-cp-register`'s.
    - After the 257th is applied the table holds 257 and satisfies
      `fn-cp-statep`.
    - A 300 table is refused its 301st.
    - The no-op and `:input` refusals are unchanged at the bound.
  - A must-fail per hypothesis:
    - `fn-cpt-within-refuses-without-the-bound`
    - `fn-cpt-capacity-needs-bounded-initial-table`
    - `fn-cpt-capacity-needs-the-served-decision`, with its concrete
      witness: the committed 257th applied to a 256 table exceeds 256.
- tests/acl2/consumer-owner-local-tests.lisp, on the served subject
  `fn-col-register`:
  - With one consumer, a second is a write under 2 and refused
    `:max-consumers` under 1.
  - The existing consumer is a no-op under 1.
  - The pre-existing witnesses run at 256.

**The assurance chain for the slice:**

- The native entry is `consumer register`, then the owner's local control.
- The executed ACL2 subject is `fn-col-register`, then
  `fn-cp-register-within`, with MAX from ACL2's reading of the carried
  profile.
- The behavioural theorems are the two keystones.
- The maintained relation is `len entries <= field 9`. Bootstrap
  establishes it (the empty table). Every applied event preserves it
  (`fn-cp-apply-preserves-consumer-capacity`), and so does every upgrade
  (`fn-profile-upgrade-keeps-namespace-counts`).
- The observed result is section 7.

## 3. Field 7, the group-name width (PKT-013): classified, not raised

Two findings. Each makes the brief's step 3 a continuation with a design, and
not an edit.

- **Field 7 has no reader.** Nothing on the served path reads
  `fn-bs-profile-max-group-name-octets`. The only uses are the validity
  relation and the codec keystone. A profile with
  `max-group-name-octets 100` still admits a 256-octet name, because
  `group create` checks `fn-record-group-namep` (the codec width 256,
  native-admin.lisp:189). The operator's field has no effect.
- **Raising the width to 460 by the constant breaks reopen.** The validity
  relation requires `R >= fn-record-encoded-octets-ceiling(A, G)`, which
  counts `(+ 5 *fn-record-max-group-name*)` octets per group
  (records-shape.lisp:149).
  - At 460 the per-group figure goes from 261 to 465.
  - The format-7 translation derives R as `ceiling(A, 65535)`. That rises
    from 17 138 486 to about 30.5 M, above the development preset's
    H (24 MiB). So the translated development profile, and every format-8
    store whose persisted R sits at the old ceiling, would fail
    `fn-bs-profile-validp` at open.
  - "Every codec width admits every valid profile" would hold, but the
    promise that a valid profile stays valid would not.

**The design for the continuation** (PKT-435 item 1):

- Make the ceiling take the profile's name bound:
  `fn-record-encoded-octets-ceiling a g n` with `(+ 5 n)` per group, and the
  validity check `r >= ceiling(a, g, field 7)`.
  - Every profile valid today has field 7 at most 256, so its figure is
    unchanged or lower. Validity only weakens.
- The format-7 translation keeps field 7 at 256 (the old figure) and does
  not use the codec width.
- The record and label widths then rise to the NNTP wire's 460 (RFC 3977
  §3.1, nntp-syntax.lisp). That is a protocol bound: a longer name cannot
  appear in GROUP.
- `fn-bs-profile-admits-every-article-record` gains the hypothesis that
  every group name of the record is at most field 7, carried from the
  configured-group table.
- The served refusal: `group create` refuses `:max-group-name-octets` past
  field 7, at `fn-store-cfg-native-admin-authorize`, which already holds the
  profile.
- Cost: records-shape (about 622 dependents) and byte-store-frame (about
  300). It is a freeze batch, and it is the deputy's to schedule.

## 4. Field 11 and the checkpoint generations; the config caps

**`*fn-cpp-max-generations*` 4096 is not governed by field 11.**

- Checkpoint generations are pack publications, not configuration
  generations.
- It conflates two quantities:
  - **The generation number**, a counter. It is (iii) and wants the u32
    width, as the frontier does.
  - **The listing**: how many retained names one open observes, which is
    work.
- After chained packs (735614d6), the chain's link count is bounded by
  BOUNDARY ≤ T: books/checkpoint-pack-chain.lisp:273
  `fn-ccc-links-count-within-boundary`, and the walk bound is
  max-transactions (:280). The count is also bounded by the 4096 names,
  because the retire plan keeps every link's pack generation (:1008, :1029).
  No disk check is involved.
- So the bound that holds and is already proved is T
  (`fn-ccc-links-count-within-boundary`).
- The 4096 is a lifetime publication cap with no field. At
  `max-open-suffix` 65 536 (published at K/2) it binds after about 134 M
  transactions, and far sooner under a small K.
- The fix, for the continuation: the generation numbering takes the u32
  width, and the listing is bounded by T+1. It is in
  checkpoint-publish/-pack-retire/-pack-chain, just merged, and was not
  touched here to avoid a conflict with the chain's owners. It is already
  PKT-168 item (1); PKT-435 item 2 points there.

**The config caps:**

- `*fn-cfg-max-deltas*` is a per-publication batch (work).
- `*fn-cfg-max-items*` and `*fn-cfg-max-octets*` are per-record (work), and
  H and R govern the record's octets in the Store.
- The exception is `:set-peer`. It replaces a peer's whole row set, so the
  set's size is data capped at 1024 rows and 65 538 octets. That is a
  format question: PKT-436.

## 5. PKT-007 and PKT-136

- The generic CBOR entry's figures (65535/65538) are (iii) and bind only
  callers that use the generic entry. The record codec does not (it moved
  to the bounded API, records.lisp:59-89). The statement codec, the
  selection frame and bp-adu carry fixed-shape items.
- Config decodes through the generic entry (config.lisp:1333), so config's
  per-record 65 538 is inherited. That is a work bound once PKT-436 lands,
  and data through `:set-peer` until then.
- The stxe evidence caps are (ii): the record is node-generated and has a
  fixed shape.
- No width change was needed for either, so the width-producers-2 u64
  pattern does not apply.

## 6. Field 13 and field 10 (PKT-229, PKT-337, PKT-296)

- **Field 13.** `*fn-pol-max-members*` 64 is statement schema v1's grammar
  limit. Per PKT-337, field 13 is to be marked reserved and every valid
  profile stays readable. No `>= 64` check is added, because format-8
  profiles with 1 to 63 exist. The operator table now says field 13 is not
  read.
- **Field 10.** It is read by nothing (PKT-296, waiting on ember). The
  operator table says so.

## 7. Native (SCN-097)

- hbox run `tools/hbox_native.sh --name community-bounds --images developer
  54104a12 tests.test_native_consumer_profile`.
  - Tree: `/tank/fn/scratch/community-bounds/native-54104a129342`.
  - Certify, acquire and validate: exit 0. The default image closure was
    recertified on hbox, including consumer-position and its dependents
    (`build/acl2/certify-20260926T095234Z-1208620` in that tree).
  - Developer image built.
  - The module: **OK**, 1 test, 25.0 s.
- `tests/test_native_consumer_profile.py`:
  1. `init --max-consumers 256`. `status` prints 256.
  2. The owner runs. `consumer bootstrap`, then c1..c256 registered, and c257
     refused (exit 1).
  3. `store upgrade-profile --max-consumers 300`. `status` prints 300.
  4. Reopen, which replays the 256 with no migration. c257..c300 are
     accepted, c301 refused, and `position c1` is accepted.
  5. Reopen again, replaying 300 (above the old constant). c301 refused,
     `position c300` accepted.
  6. `--max-consumers 299` refused, naming max-consumers.
- The native refusal is exit 1 and "refused". The control socket's consumer
  reply carries no reason (`(:consumer-reply :refused nil)`,
  host/native/control.lisp:355), so the reason `:max-consumers` is witnessed
  in ACL2 (section 2), not on the wire.
- SHA-256:
  - log `planning/evidence/community-bounds/native-consumer-profile.log`
    `1ed511ff31bdaaee12bf436eabbd71b46ada202bed31371550137611cba96bec`
  - image `fn-host-developer.core`
    `89971b853125d5d178eac2865e70d1610afbe17079bcab8041f1ab2042df070d`
  - launcher
    `5f1c478dd50fa7ded311b72dba3b6706c0a3ef9410f97a57b9d2997efcded831`
  - Full list: `planning/evidence/community-bounds/SHA256SUMS`.
- Not run: the group-name case of brief step 9 (a 300-octet name under
  field 7 = 460). It needs section 3's design first.

## 8. Certification

persvati, w25 `acl2-literal`, 2 jobs, 300 s:

- run-20260926T094930Z-38b9 at 818c589a (`--affected-by` consumer-position,
  consumer-owner-local, store-profile-namespace): 557 passed, 0 failed.
  Manifest `planning/evidence/manifests/certify-20260926T095002Z-4098660.json`.
- run-20260926T100215Z-724c at e671ce6b (the same roots plus peer-feed,
  scheduler, anchor-record, topic-history-store-events and the docs grammar
  test book): 586 passed, 0 failed. Manifest
  `planning/evidence/manifests/certify-20260926T100254Z-46471.json`.
- Books over 10 s at two jobs: owner-invariants (10.4 s, then 12.4 s),
  store-node-invariants (11.3 s) and native-admin (10.0 s). This lane edited
  none of the three; they were recertified as dependents under load. They
  are dev's D26 debt, and their times varied between the two runs.
- `make check-lane` is red on one item, the proof-cost ratchet:
  store-node-invariants at 11.29 s (run 2) is not in the baseline. Run 1
  measured the same book at 8.43 s. The book's own bytes are unchanged
  between the runs, and its closure differs only by a comment, so this is
  load variance on persvati and not this lane's regression. It is left red
  and not re-run for a lower figure. The deputy decides: a matched quiet
  remeasurement, or the ten-second work on that book (8df249ea was its
  last). Every other check-lane step passes.
- hbox recertified the default image closure at 54104a12 (section 7).

## 9. PKT-183 (not done here)

- **The contiguity composition.** The writer
  `fn-native-admin-publication-within-the-operator-bound` and the listing
  `fn-nco-observe-refuses-exactly-past-the-operator-bound` compose only
  through an unstated lemma: that the configuration replay of k records has
  `fn-cfg-generation` k, so the listing after an accepted publication holds
  GENERATION entries.
  - The writer is also bounded by
    `fn-cvec-config-generations profile record`
    (store-capacity-config.lisp:38), not by field 11 itself. Field 11 is at
    least that figure, and one more for a non-retention record.
  - Host line: host/native/admin.lisp `fnn-admin-authorize` (:58), then
    host/store-node-host.lisp `fn-store-cfg-native-admin-authorize`.
- **The credential file.** `(:fault :serialized-profile)` stays at
  native-auth-admin.lisp:383 (set-password) and :405 (bind). The reason is
  that no theorem bounds `fn-native-auth-admin-serialize`'s length by
  `fn-native-auth-max-octets n` for n credentials. The per-credential 512 is
  a comment (native-auth-profile.lisp:20-27), not a lemma.
- Both are PKT-435 item 3.

## Commits

- 818c589a: field 9 (books, tests, host).
- 54104a12: PKT-135 comments, and the SCN-097 test.
- The record and registry commit follows.
