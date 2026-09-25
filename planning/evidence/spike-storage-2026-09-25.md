# Spike: storage at scale (spike/storage, D28), 2026-09-25

Lane `spike/storage` from `spike/mega` 0e2173ab. A SPIKE lane (D28): the
code here is `:program` host code and host decisions marked `;; SPIKE`, not
certified books, except where named. Everything below ran on hbox, stores on
tmpfs (`/dev/shm`), images built from this tree with the certified closure
(323 books, all from the certificate cache; `tests/spike/setup.sh`,
`build.sh`). No farm run was needed: no book changed in the final tree.

P3 had not landed on `dev` or `spike/mega`. Its branch
`lane/bounds-p3-checkpoint` (a9f527eb, certified, with its own evidence) is
merged here (481fc710) instead of a second, simpler checkpoint: building a
rival would have been a copy of finished work. Say so to the coordinator:
this lane carries P3 into `spike/mega`.

## What works

| Piece | Where | Shown by |
| --- | --- | --- |
| Replay without per-event whole-state checks | `host/spike-storage-fast-host.lisp` (fold), wrappers in `host/store-node-host.lisp`, `host/owner-host.lisp` | sb-sprof before/after (below) |
| Owner installs the open's own state | `fn-spk-owner-recover-opened`, `host/native/owner.lisp` | owner restart at N=3000: 7.1 s, one replay instead of four |
| (1) Release + reclaim (capability C under D13) | `host/spike-storage-host.lisp` C2, `host/native/spike-storage.lisp` | `tests/spike/test-small.sh`, log `logs/test-small-t4.log` |
| Stub-aware D25 | `fn-spk-existing-action` (fast file C1) | resend of a reclaimed article: `441 ... already stored here`; changed body: `441 ... a different article` |
| (2) Chained packs | link codec D (ACL2 `:program`), walk and verbs native | history digest identical before and after compaction and at every cut |
| (3) BP rotation cleanup | `host/spike-storage-bp-host.lisp`, `fnn-spk-bp-cleanup` from `fnn-bps-open` | `tests/test_spike_bp_rotation_cleanup.py` (OK, 36 s, hbox) |
| (4) 64-bit widths | not built | inventory below |
| (5) Measurement | `tests/spike/ramp.py`, `scale.sh` | tables below |

The verbs are a registered verb of every spike image:
`fn-host --fn spike-store STORE-ROOT COMMAND`, with `release MSGID...`,
`release --oldest K`, `reclaim [--older-than SECONDS] [--verify]
[--dry-run]`, `compact-chain [--link-events N]`, `chain-retire` and
`history-digest`. The operator grammar (`books/native-operator`) is not
extended.

### Replay cost: the Θ(N³) was whole-state revalidation per event

sb-sprof (`FN_SPIKE_SPROF=PATH`, the spike's diagnostic) of `store status`
at N=300 on the P3 code: 76% of the open is `fn-node-statep`. `fn-cpr-loop`
and `fn-cpr-apply-event` (`books/config-physical-replay.lisp`) run
`fn-cnode-statep` or `fn-node-statep` four times per replayed event, and
`fn-node-statep` is quadratic by itself (binding and article subset checks
by `member`). So open was Θ(N³). The spike fold checks the recognizer once
per open, and not per event.

| Open, full replay (no checkpoint) | P3 image (a9f527eb) | spike fold |
| --- | --- | --- |
| N=300 | 10.6 s | 0.85 s |
| N=1000 | 240 s (P3 record) | |
| N=3000 | about 3165 s at 2048 (P3 record) | 5.9 s |
| N≈35,900 | not run (about 10^5 s by the N³ fit) | 809 s, 4.2 GB RSS (owner open, measured) |

What remains is Θ(N²): per event, the retention ledger's
`fn-retain-known-idp` (`member-equal` over `fn-retain-obligation-ids`, which
conses the id list each time) and acceptance's `fn-acceptedp` (N=3000
profile: 19% in `fn-retain-obligation-ids`, 9% `string=`). Pessimistic
sentence: a full-replay open is Θ(N²) in these scans. It measured 809 s at
N≈35,900. Scaled by N² to N=100,000, that is about 6,300 s. It is not
bounded by any profile field. A checkpoint open with suffix k costs a linear
decode plus k events at O(N) each.

The served POST path has its own O(N) per POST: `fn-index-build` and
`fn-gidx-build-entries` (group index rebuild) and the same retention scan
(owner profile N=3000 to 5000). Per POST: 2.4 ms at N=1,000 and 45 ms at
N=35,000 (P3 image). With the spike image it was 66 ms at N=36,000. This is
the served path's whole-state work, which AGENTS.md forbids. It is reported
here, not fixed.

### (1) Release and reclaim

- **Release.** The model cannot release an article's archive undertaking.
  - `fn-node-statep` (`books/node.lisp`) keeps every binding id among the
    live pins and every article with a live archive pin.
    `fn-replay-apply-retention-event` refuses a bound id.
  - Admitting the release in replay broke
    `fn-replay-apply-record-non-nil-is-node-state` on the first
    certification (hbox certify-20260925T081250Z-2847123). That change was
    reverted.
  - The spike keeps a sealed operator **release record** per undertaking
    (id, subject, evidence, msgid, DTN seconds) in `releases/`. The
    retention ledger still charges a released article: reclaim frees bytes,
    not charge.
- **Reclaim rule.** An article is reclaimed when:
  - a release record names its binding's obligation id;
  - no other pin holds the same subject;
  - it is older than `--older-than` (stamp seconds since 2000; a `:legacy`
    stamp is kept when an age is set);
  - `fn-stx-delta` and `fn-stx-verdict-of-octets` are the same on the stub
    (signed and identity-bearing articles are kept);
  - no consumer is registered (conservative: any consumer entry refuses the
    whole reclaim).
- **The stub.** The payload becomes its header block plus
  `FN-Reclaimed: v1 octets=N sha256=H source=S` and an empty body. H is
  SHA-256 of the payload. S is the digest of the poster's source under the
  article's own Path agent (D25).
- **What stays.** The record keeps sequence, txid, Message-ID, groups,
  obligation id, content subject, evidence, charge and stamp. The article
  keeps groups, memberships (article numbers), pin and stamp.
- **Rewrite order.** The history is written first (suffix transaction files,
  or chain links in place), then the checkpoint. The checkpoint is P3's
  capture with records, node articles and the event index stubbed, extended
  over the stubbed suffix.
- **`--verify` (executable form of keystone 1):**
  - the full open of the stubbed history equals the pre-reclaim open on every
    decision slot (groups, nexts, next txid, per-article
    msgid/groups/memberships/pin/stamp, retention, bindings, keyring, index,
    keyring generation, verdicts, snapshots, identity-next, consumer, topic);
  - the stubbed checkpoint's open equals the full open;
  - the event index equals the stub transform of the old one (it maps each
    sequence to its whole record);
  - every run printed `decisions-equal=t checkpoint-equals-full=t
    payloads-stubbed=t event-index-is-stubbed=t`, at N=300 with 100, 50 and
    60 articles, and with and without a checkpoint and a chain.
- **Served:**
  - `ARTICLE` of a reclaimed article answers the 9-line stub.
  - `GROUP fn.test` is unchanged: `211 300 1 300`.
  - A resend of the same article is `441 ... already stored here`
    (duplicate). A changed body is `441 ... a different article` (conflict),
    before and after reclaim.
- **Cuts.** Exit 137 at `reclaim-record-staged`, `-replaced` and
  `reclaim-history-done`:
  - each reopens;
  - a rerun of `reclaim` converges to the same history digest (2b5f2864...);
  - a rerun at `reclaim-history-done` finds nothing left.
  - Window: when a checkpoint existed before the reclaim and the process
    dies after the history but before the checkpoint, the open serves the
    old checkpoint's bytes until a rerun rewrites it.

### (2) Chained packs

- **Link format.** `packs-chain/link-G.fnpl` holds `FNPL` 1, then lower,
  boundary, the predecessor generation (u64) and the predecessor's header
  digest, then the count, one SHA-256 per original record, then the
  length-prefixed bodies, sealed with the ACL2 trailer.
- **Selection.** `selection.fnps` names the newest link's generation and
  header digest.
- **Open.** The open walks newest to oldest. It checks each header digest,
  contiguity (`lower` = the predecessor's `boundary`) and that the first
  link names no predecessor. It concatenates the links, then the suffix
  files. A surviving covered file must equal its link record or be its stub.
- **Reclaim.** A body is admitted if its digest is listed, or if it decodes
  as a record with a stub payload. Reclaim therefore rewrites a link in
  place, and the chain header does not change.
- **Compaction and retire.** `compact-chain` packs only the uncovered suffix
  into new links of at most `--link-events` (default 4096) events and the
  pack's 4 MiB. `chain-retire` removes generations outside the selected
  chain.
- **Evidence** (N=300, 64 events per link, 5 links):
  - history digest `07101be8...` before and after compaction;
  - `62ac6528...` over a reclaimed history, unchanged by compaction;
  - reclaim through the chain rewrote 2 links each time, and the digest
    followed the stubs;
  - at each cut (`link-staged`, `link-linked`, `chain-selection-staged`,
    `chain-selection-replaced`, `chain-selected`, `chain-reclaim-unlink`)
    the reopen gives `07101be8...`, a rerun completes, and `chain-retire`
    removes a killed run's unselected links (5 after
    `chain-selection-staged`, 1 after `link-linked`).
- The P3 checkpoint open reads no link when S ≥ the chain boundary.

### (3) BP journal rotation cleanup

`fnn-bps-open` (after it holds the journal locks and has read the durable
selection) removes three things, each unlink a cut:

- every generation directory below the selected one (recursively, bounded
  depth);
- every killed rotation's `.bp-generation-*` staged file;
- every directory above the selected one, when it is empty.

A non-empty later directory is kept and counted (`kept-nonempty`). The plan
is ACL2 `:program` (`fn-spk-bp-cleanup-plan`) over `fn-bpnr-generation-of-name`.

The test (hbox, `tests/test_spike_bp_rotation_cleanup.py`, OK, 36 s)
covers each killed cut (`directory`, `stage`, `replace`) and a clean
rotation. After each, the reopen recovers the held rows (1, then 2) and
only the selected generation remains. On the spike this replaces N16's
assertion that the old generation stays untouched
(`tests/test_bp_node_native.py`; it is expected to fail on a spike image,
not run here).

### (4) 64-bit widths: not built

- **Width sites.** `*fn-cbor-max-uint*` = 2^32 - 1 (`books/cbor.lisp:24`)
  and `fn-record-uint32p` (`books/records-shape.lisp:364`, 264 uses in 87
  books) bound the transaction id, sequence, charge and stamp. The frontier
  is `fn-bs-frontier-encode-impl` (`books/byte-store-frame.lisp:448`).
- **Why not.** P6 is the whole-tree freeze (721 dependents). With skip-proofs
  it is still several full recertifications. This lane spent its
  certification on finding that the archive release is outside the node
  invariant.
- **What the spike does carry at u64.** The chain link fields (lower,
  boundary, predecessor, count) and P3's checkpoint header (S, index,
  count, length).
- **The translation dev owes.** Schema-2 records with CBOR head 27 uints.
  Old schema 0 and 1 bytes decode to the same logical record, so the
  translation at open is the identity on logical records. Keystone:
  `fn-record-decode-v2-of-old-bytes` equals the old decode.
- **Headroom at this scale.** 100,000 articles use about 10^5 of 4.29 × 10^9
  transaction ids.

## Deferrals (the keystones dev owes)

1. `fn-replay-apply-record-preserves-node-statep` and
   `fn-spk-cpr-fold-equals-cpr-loop` (and `= fn-sco-cpr-prefix` when
   pausing). The spike's fold checks `fn-cnode-statep` once, drops the
   per-event checks, and drops the closing `fn-sn-statep` of the open.
2. The stashed open state equals `fn-owner-recover`'s. Both are
   `fn-cpo-open-observed` of the same inputs, or P3's keystone.
3. The archive release as a Store event. `fn-node-statep` must be relaxed
   to binding ids within pins or releases, and articles within a live or
   released archive pin. A bound `:archive` release must be admitted in
   `fn-replay-apply-retention-event`, and the node invariants re-proved.
   The release then frees its charge. D13's authority policy for an
   operator release is open.
4. `fn-spk-reclaim-preserves-decisions`: the open of the stubbed history
   equals the stub transform of the open, on every slot but payloads (the
   `--verify` projection). This includes the event index's stub transform
   and the checkpoint commute (stubbing the checkpoint then opening equals
   opening the stubbed history).
5. `fn-spk-stub-identity-invariant`: an eligible record's identity replay
   does not read its body. The spike checks it against the current keyring
   only.
6. The stub codec as a book with its round trip, and the D25 keystone
   `fn-spk-same-articlep-equals-original`, under a constrained
   `A-DIGEST-COLLISION-FREE`. It also needs the fact that the injection
   inverse gives a source only under the article's own agent. The POST
   refusal of a submission carrying `FN-Reclaimed:` is checked at the
   owner's prepare only (the developer `store post` path does not check it).
7. The consumer-pin bound on reclaim. The spike refuses when any consumer is
   registered.
8. The chain: `fn-spk-link-decode-of-encode`, PRF-073 over a chain, the
   crash keystone for each link and selection cut, and a chain-length
   bound in the profile. The spike walks up to 10^6 links. The walk,
   selection frame and names are host code.
9. BP cleanup: an ACL2 plan book with the preservation theorem (no open
   reads a generation other than the selected one), and the removal program's
   cuts in the crash model.
10. Release records, chain files and stubs are compared and parsed by
    host code in places (`fnn-spk-unseal` recomputes the trailer and
    compares it; `fnn-spk-released-ids` parses lengths). ACL2 owns this
    parsing on `dev`.
11. `tests/test_native_served_crash_model.py` lds `host/store-node-host.lisp`
    without the fast file and fails on this tree.
    `tools/run_store.py` and `tools/labs.py` load it.

## Measured at N≈100,000 (2 KiB articles, hbox tmpfs)

**Setup.**

- Logs: `/tank/fn/scratch/spike-storage/logs/{ramp1,ramp2,scale,scale2}.jsonl`.
- Images:
  - P3 image: 0 to 35k.
  - img1: 36k to 101k (launcher 73db26fb, core 1f796549).
  - img2: the operations (launcher 217efde5, core 34cc67a4).
- The store holds 100,912 committed articles. POSTs 35,912 to 35,999 were
  skipped when the first ramp was stopped and resumed.

| Quantity | Measured | Pessimistic sentence, with its scope |
| --- | --- | --- |
| Disk | 394 MiB, 100,917 files (403,664 KiB, 4 KiB per record file) | One file of about 4 KiB per record until `compact-chain`. The history grows without bound under D03 until reclaim or a chain. |
| POST wall at size | 86 ms per POST at 100k (81 to 93 ms from 90k to 101k); 2.4 ms at 1k, 45 ms at 35k | Θ(N) per POST from the served path's group-index rebuild and retention scan. 100k POSTs from empty took about 1.1 h plus two owner opens. |
| Owner RSS while serving | 4.2 GB at 101k (2.0 GB at 35k) | Octet-list articles held by the node: about 40 KB of heap per 2 KiB article. |
| Open without a checkpoint (`status`, full replay) | 3,870 s and 3,888 s, 16.9 GB max RSS | Θ(N²) in the ledger and acceptance scans, after the spike fold. On the P3 image the N³ fit gives about 10^6 s. |
| Owner open (full replay, installs the open's state) | 3,698 s, 8.9 GB | The same fold. The P3 owner replayed a second time. |
| Checkpoint capture from a full open | **failed**: heap exhausted during GC after 6,471 s at `--dynamic-space-size 32000` (32.6 GB RSS) | The P3 checkpoint holds the record list, the node and the fold accumulators as cons trees, and encodes them to one octet list. At 100k that exceeds 32 GB. **So at N=100k there is no checkpoint and no open with one.** Every open is the 3,870 s replay. |
| Open with a checkpoint | measured at N=300 (below 1 s) and by P3 at 1k (1.7 s) and 2k (4.6 s); not at 100k | The capture must first fit (representation ranks 4 and 6: payload as byte arrays, bodies by reference). |
| `store compact` (single pack) | not run | One pack is capped at 4096 events and 4 MiB. At 2.4 KB per record it covers about 1,700 records, so a single pack cannot compact this store. |
| release, reclaim, compact-chain, history-digest at 100k | in the second run, below | Each opens by full replay (about 3,900 s) before it writes. |

**Reading of the numbers.**

- **The Θ(N³) is gone.** The fast fold keeps the open to hours, not days.
  Open time is still Θ(N²), and memory is Θ(N) with a constant of about
  160 bytes of heap per payload octet at open.
- **The wall at 100k is the representation, not the algorithm.** The
  checkpoint that would make the open Θ(K) cannot be built in 32 GB.
- **Order of work for dev:**
  1. Payloads as byte arrays and archive bodies by reference (the
     representation design, ranks 4 and 6).
  2. Carry the ledger and acceptance membership sets as indices, not lists
     scanned per event. This removes the Θ(N²).
  3. Only then the checkpoint at scale.
- **The owner's served path must stop rebuilding the group index per
  POST.** 86 ms per POST at 100k is Θ(N).
- **Harness fault.** The scale run's owner survived its unit: the POST
  client timed out after a 3,698 s open. The spike owner PID was stopped
  by hand.

