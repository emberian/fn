# Recovery refinement: one theorem for every crash point of the composed store

Status (lane recovery-refinement, 2026-10-01; design
`planning/design-store-representation-2026-10-01.md` §2 "Crash story" and
§4 stage 7): the statement below is one ACL2 theorem,
`fn-rr-recovery-refines-a-prefix-with-every-acknowledged-record`
(`books/recovery-refinement.lisp`, PRF-1212), composed from the log's and
the image medium's cut models by citing their keystones; the checkpoint
reserve is `books/checkpoint-reserve.lisp` (PRF-1213); the checkpoint
program's own crash points are `fn-rr-checkpoint-crash-point-recovers-
committed-under-old-or-new` (PRF-1216). Both books were REPL-admitted on
hbox from the cached chain (0 refused) and certified (the manifests are in
the registry rows); their store instance `books/recovery-refinement-store.lisp`
is written and NOT admitted (its chain reaches the node tower, red at dev
896c48c16). **The claim is MODEL-LEVEL** (the Codex review of 2d1b10ed7,
F1): no host file calls `fn-rr-open` or `fn-rrs-open`; it becomes a claim
about the served path when the store instance is admitted and a named
theorem equates its open to the one `fnn-recover-log` calls
(`fn-rii-sco-extend-open`, `fn-sfi-extend-open`). What the composition
cannot yet cite is an open obligation by id (§5), never a paper premise.
Counts live in the generated ledger; this page carries the property, its
premises and its scope.

## 1. The statement

The composed store is two layers over one byte model
(`books/byte-store.lisp`, [crash model v2](crash-model-v2.md) §1):

- **The log** is the authority: the record segments of `fn-store-9`
  (STO-033, STO-034). Its kernel state (`fn-lgk-*`,
  `books/store-log-kernel.lisp`) holds COMMITTED (the records the durable
  segment scans to), INFLIGHT (the batch written at the frontier and not
  yet fenced) and ACKED (the acknowledged prefix length of COMMITTED, the
  owner batch layer's `fn-owb-acked` members).
- **The image medium** is a prefix cache the open may use: today the state
  checkpoint file `store-checkpoint.fnsc` ([storage](storage.md) STO-011,
  STO-026, `books/byte-store-state-checkpoint-program.lisp`); the design's
  target is the page store's root (STO-035, `books/pagestore-keystones.lisp`).
  An image is the capture of a prefix of S committed records
  (`fn-sco-capture`), and the open serves it only when S is within the
  recovered records and the suffix within K (`fn-sco-select`). In the
  ACL2 statement the medium is an interface, the constrained
  `fn-rr-medium-capture`, `-open`, `-full-open`, `-select`, `-open-okp` and
  `-holds`, whose three constraints are PRF-083's keystone shape (the open
  of the capture of P over Q is the full open of P ++ Q), the selection's
  bound (a served S is within the count) and holding (a full open that
  SUCCEEDED holds every record it was opened from; without it the opened
  state was unconstrained beyond its equation to the full open, the Codex
  review's F2; the store's: `fn-sn-open-okp`, membership in
  `fn-sf-records` of the opened Store's files); the store's functions are
  to discharge it by functional instantiation in
  `books/recovery-refinement-store.lisp` (WRITTEN, NOT ADMITTED: nothing
  there is a claim yet), the log's records decoded by `fn-srs-decode` (the
  host's `fn-store-decode-records`).

**The tree sequence** (DFSCQ's metadata-prefix form, Chen et al. SOSP 2017)
at a crash point is the list of abstract states the recovery may land on:
the full open (`fn-cpo-open-observed`) of COMMITTED ++ P, one element per
prefix P of INFLIGHT. In ACL2, `fn-rr-tree-sequence-memberp recovered
committed inflight` says RECOVERED is COMMITTED followed by a prefix of
INFLIGHT.

**The theorem** (Argosy's shape, Chajed et al. PLDI 2019: the log's recovery
and the medium's recovery compose into one recovery refinement). For every
crash point of the composed store, that is every cut state (BS, KS) of the
log's served programs, which is a state satisfying the log relation R
(`fn-lgk-relp`) with the owner batch layer aligned on it
(`fn-owb-alignedp`), and for every admissible crash image
(`fn-bs-crash-imagep`) of it:

1. **Old-or-new per operation, as a prefix.** The records the log's
   recovery holds from the image's segment
   (`fn-rr-recovered-records`: `fn-lgk-committed` of `fn-lgk-recover` over
   the image's durable content) are one element of the tree sequence:
   COMMITTED followed by a prefix of INFLIGHT. An operation in flight is
   present or absent, the present ones form a prefix, and no committed
   record is lost.
2. **The composed open is the full open of that prefix.** Whatever image
   the medium holds, bound to the capture of its first S records (S at most
   the committed count), the open the composition MODELS (`fn-rr-open`:
   the selection under K, then the medium's open of the image over the
   suffix it leaves, or the full open; the store instance's `fn-rrs-open`
   over `fn-sco-open` is not what the host calls, §1's MODEL-LEVEL note)
   equals the medium's full open of the recovered records (the store's
   `fn-cpo-open-observed`; `fn-sn-recover-from-checkpoint-equals-full-recover`,
   PRF-083).
   An image the selection refuses (absent, corrupt, past the reader's bound,
   ahead of the history, past K) is the full replay by definition.
3. **Acknowledged implies present, in the opened state.** Every record
   among the first ACKED of COMMITTED (the kernel's acknowledged prefix;
   ACKED <= len COMMITTED is a conjunct of R) is among the recovered
   records, and a composed open that succeeded holds it. The owner batch
   layer's acknowledged members are exactly those records
   (`fn-owb-alignedp`, `fn-lgu-acknowledged-record-is-committed`,
   `books/store-log-durable.lisp`), the owner-layer corollary. A refused
   open stays refused: conjunct 2 carries the full open's refusal through
   the composed open unchanged, and the holding constraint is conditional
   on the open's success, so an always-refusing open satisfies the
   interface. LIVENESS OF THE OPEN IS NOT CLAIMED here: that the full open
   of a well-formed history succeeds is the open's own theorem
   (`fn-cpo-open-observed` over `fn-sn-observed-historyp`), not this one's.

Stated as one event, `:rule-classes nil`:

```lisp
(defthm fn-rr-recovery-refines-a-prefix-with-every-acknowledged-record
  (let ((recovered (fn-rr-recovered-records image ino genesis (fn-bs-unit bs) max next-txid)))
    (implies (and (fn-lgk-relp bs ks ino genesis max)
                  (fn-bs-crash-imagep bs image)
                  (fn-lg-platform-tears-p
                   (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino))
                   (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))
                  (natp s)
                  (<= s (len (fn-lgk-committed ks)))
                  (equal ckpt (fn-rr-medium-capture configs (take s (fn-lgk-committed ks)))))
             (and (fn-rr-tree-sequence-memberp recovered (fn-lgk-committed ks) (fn-lgk-inflight ks))
                  (equal (fn-rr-open status s ckpt configs frontier recovered k)
                         (fn-rr-medium-full-open configs frontier recovered))
                  (implies (member-equal r (take (fn-lgk-acked ks) (fn-lgk-committed ks)))
                           (and (member-equal r recovered)
                                (implies (fn-rr-medium-open-okp
                                          (fn-rr-open status s ckpt configs frontier recovered k))
                                         (fn-rr-medium-holds
                                          (fn-rr-open status s ckpt configs frontier recovered k)
                                          r))))))))
```

The host functions whose composition the theorem models:
`host/native/io.lisp` `fnn-recover-log` (P-LOG-RECOVER, the kernel
`fn-lg-open-kernel`, proved the recovered kernel by
`fn-lg-open-kernel-is-the-recovered-kernel`; `fnn-log-recover`), then the
checkpoint's selection and the open through `fn-rii-sco-extend-open`
(`books/replay-identity-index.lisp`) or `fn-sfi-extend-open`
(`books/store-finalize-incremental.lisp`), or the full replay. `fn-rr-open`
names that composition in ACL2 over `fn-sco-open`; no host file calls it or
`fn-rrs-open`, and no host-called ACL2 function composes the two layers, so
the open square is host code, the same gap PRF-344 records for the page
store. The registry row says MODEL-LEVEL (F1) until the store instance and
the equation of `fn-rrs-open` to the host-called opens land.

## 2. The premises, each named

| premise | form in the theorem | kind | discharged by |
| --- | --- | --- | --- |
| R, the log relation at the crash point | `fn-lgk-relp bs ks ino genesis max` | fn obligation, proved per program | `fn-lg-append-program-keeps-the-relation`, `fn-lg-fence-program-keeps-the-relation` (`books/store-log-programs.lisp`); `fn-lg-reserve-program-keeps-the-relation`, `fn-lg-order-program-keeps-the-relation`, `fn-lg-open-suffix-keeps-the-relation` (`books/store-log-route-programs.lisp`); `fn-lg-extend-program-keeps-the-relation` (`books/store-log-extend.lisp`); `fn-lg-recover-program-establishes-the-relation`; the failed fence's landed selection `fn-lgu-committed-record-survives-every-cut-of-a-failed-fence` |
| the batch layer aligned | not in the generic theorem: ACKED is the kernel's own field | fn obligation of the owner layer | `fn-owb-alignedp` (`books/owner-batch.lisp`): established by `fn-owb-recover`, kept by prepare, append, fence, finish; `fn-lgu-acknowledged-record-is-committed` |
| external synchrony (STO-003) | ACKED <= len COMMITTED inside R; a member joins `fn-owb-acked` only after the batch's fence | fn obligation | `fn-owb-fence`, `fn-owb-finish-member` (`books/owner-batch.lisp`); the native ack path `host/native/io.lisp` fnn-finish after fnn-log-publish's barrier (`tests/campaign/native_cuts.py` POST_CUTS) |
| the platform's crash | `fn-bs-crash-imagep bs image` | model (A-CRASH-IMAGE, crash model v2 §1.5) | per-unit tears, zero-fill, garble, dropped entry operations; the model is the premise, the platform rows below are what makes it true of a box |
| A-DURABILITY, A-WRITE-ISOLATION | `fn-bs-crash-keeps-fenced-content` (a fenced inode's durable content survives every image) | named assumptions, `books/assumptions.lisp` | used in the quiet case (nothing in flight) and in the medium's half |
| A-CRYPTO-TRAILER | `fn-lg-platform-tears-p (nthcdr F content) INFLIGHT LAST UNIT` | named assumption, `books/assumptions.lisp` | removes the forgery disjunct of `fn-lgk-crash-of-related-state-is-a-prefix` (`fn-lg-no-forgery-under-a-crypto-trailer`); without it the theorem holds with "or the first damaged entry forges", the pessimistic figure the collision one, about 2^-128 per chosen pair |
| image binding | `ckpt = (fn-rr-medium-capture configs (take s committed))`, `s <= len committed` (the store instance: `fn-sco-capture` of the decoded prefix) | fn obligation of the publication | `fn-sct-decode-file-of-file-is-the-capture` (PRF-199), `fn-sct-load-is-decode-file` (PRF-135), `fn-ock-finish-binds-the-captured-prefix`, `fn-ock-next-checkpoint-is-the-capture` (PRF-083): what the owner writes is the capture of the committed records it was handed, and S is their count |
| fsync ordering | implicit in the binding: the captured records are COMMITTED (fenced) records, so S never exceeds the durable count | fn obligation (the owner captures under its mutex from the committed rows) and a selection arm | `fn-sco-select`'s `:ahead-of-history` arm refuses S past the recovered count; a bound S with different records (a log repaired or rolled back under a kept image) is the freshness gap C2-12, outside the crash-only claim |
| the medium's own ordering | stage, write, fsync file, rename, fsync dir (`fn-bs-scp-program`); pages, table, root slot, one fdatasync (`pgs-plan-commit`) | proved per medium | `fn-bs-scp-program-crash-is-old-or-new`; `pgs-open-after-crash` (PRF-344) |
| A-HOST-EXCLUSIVE-READ | the image's range reads concatenate | named assumption | `fn-bs-read-ranges-concatenate` |
| A-DURABLE-EXTENT, A-DURABLE-LZ | a recovered record's payload read from its segment extent is the durable octets | named assumptions, `books/assumptions-durable.lisp` | the arena's consumers after the open; the records themselves are what the scan reads |
| the platform rows | not in the theorem | MEASURED, per deployment | Linux ext4/xfs: fdatasync drains the inode's writes, fsync(dir) the entries, a failed fsync has marked the pages clean (fsyncgate; crash model v2 §1.6); Darwin: `fsync` does not reach the drive, `F_FULLFSYNC` does, so laptop runs are not durability evidence for the node; OpenBSD (the friend node): its own row. Each is a measured premise of the qualified image, never a theorem |

What the theorem does not say: nothing about freshness (a valid older
image with a truncated log needs an external anchor, C2-12); nothing about
the host's open loop being the model's (the open square). A crash INSIDE a
publication while a batch is in flight is the lifted statement of
`books/recovery-refinement-concurrent.lisp` (PRF-1214, §5): the same three
conclusions over `fn-rrc-relp`, R with the segment's own pending
operations in place of the store's whole pending list.

## 3. What composes today, and the crash points covered

`books/recovery-refinement.lisp`:

- `fn-rr-open-is-the-full-open-of-the-recovered-records` (the medium's
  half): one hypothesis, the binding; by `fn-sco-select-bounds-the-suffix`
  and PRF-083.
- `fn-rr-log-crash-image-in-flight-recovers-a-tree-sequence-member` (a
  batch in flight) and `fn-rr-log-crash-image-quiet-recovers-committed`
  (nothing in flight; the segment is fenced, `fn-bs-crash-keeps-fenced-
  content`, and its scan is exactly COMMITTED by
  `fn-lg-scan-of-complete-append` and `fn-lg-scan-of-zeros`), joined in
  `fn-rr-log-crash-image-recovers-a-tree-sequence-member`.
- `fn-rr-acknowledged-record-is-in-every-tree-sequence-member`.
- the keystone, §1; and §8's `fn-rr-checkpoint-crash-point-recovers-committed-
  under-old-or-new` (PRF-1216).

`books/recovery-refinement-store.lisp` (written, not admitted, §5):
`fn-rrs-open-is-the-full-open-of-the-recovered-records` and
`fn-rrs-recovery-refines-a-prefix-with-every-acknowledged-record` by
functional instantiation over `fn-sco-*`, `fn-cpo-open-observed` and
`fn-srs-decode`; `fn-rrs-reserve-is-two-capture-budgets` and
`fn-rrs-funded-reserve-never-defers-for-space` (§4).

The native cut table (`tests/campaign/native_cuts.py`, what
`tools/native_program_check.py` ties to `host/native/io.lisp`), each cut a
related state by the theorem named in §2's first row:

| cuts | program | the crash point's R |
| --- | --- | --- |
| frontier-reserved, record-completing | `fn-lg-reserve-program`, `fn-lg-order-program` | `fn-lg-reserve-program-keeps-the-relation`, `fn-lg-order-program-keeps-the-relation` |
| log-written, log-fenced | `fn-lg-append-program`, `fn-lg-fence-program` | `fn-lg-append-program-keeps-the-relation`, `fn-lg-fence-program-keeps-the-relation` |
| log-extended, log-extent-fenced | `fn-lg-extend-program` | `fn-lg-extend-program-keeps-the-relation` |
| log-truncated, log-recovered, recover-replayed, recover-barrier-1..3 | `fn-lg-recover-program`, `fn-lg-open-program` | `fn-lg-recover-program-establishes-the-relation`, `fn-lg-open-suffix-keeps-the-relation` |
| finish-consumed, finish-durable, recovery-stage-unlinked | `fn-bs-finish-program`, `fn-bs-recover-stage-cleanup-program` | OWED (PRF-1221): the route is PRF-1214's `fn-rrc-keeping-the-segment-keeps-the-lifted-relation` (a state that keeps the segment's presence, content, unit and own pending operations of a lifted-related state is lifted-related, and the keystone covers its images); what is owed per program is the keep-the-segment theorem over its run. K0's `fn-bs-k0-finish-program-preserves-relation` is the octet half for the finish program; the pending half (entry operations only) is not yet a theorem |
| state-checkpoint-created, -written, -staged-durable, -replaced, -durable | `fn-bs-scp-program` | PROVED, PRF-1216 (quiet) and PRF-1214 (concurrent). Quiet: `fn-rr-checkpoint-crash-point-recovers-committed-under-old-or-new`: from the quiet store (`fn-bs-scp-inputp`) the program never writes the segment, every crash image of every state recovers exactly COMMITTED and holds the old or the new image (`fn-bs-scp-program-crash-is-old-or-new`). Concurrent (a batch in flight at log-written): `fn-rrc-checkpoint-crash-point-refines-with-a-batch-in-flight` (`books/recovery-refinement-concurrent.lisp`): the run keeps the segment's presence, content, unit and own pending operations (`fn-rrc-scp-run-keeps-the-segment`), so every state is lifted-related and the keystone's three conclusions hold on every image of every cut. The inner cuts of the host's write loops are PRF-1223 |
| rotate-created, rotate-fenced, rotate-renamed, rotate-headed, rotate-durable, drop-unlinked, drop-durable; import-*, export-*, init-*; statement-committed | `fn-lgs-spare-program`, `fn-lgs-rotate-program`, `fn-lgs-rotate-durable-program`, `fn-lgs-drop-program`, the import, export and init publication programs, `fn-ks-cut` | NOT COVERED by this theorem family; OWED (PRF-1221). The rotation changes which inode is the active segment, so the relation's INO moves with it (`books/store-log-segments.lisp`, `books/store-log-lineage.lisp` hold the rotation's own theorems); the publications and the statement touch other inodes and directories and need only a keep-the-segment proof each |

## 4. The checkpoint reserve (KeyKOS's rule over the existing policy)

`books/checkpoint-reserve.lisp`, PRF-1213. KeyKOS reserves two alternating
checkpoint areas at format time and forces a checkpoint by a dirty-set
bound, so free space is never observed to decide whether the system may
checkpoint (Landau 1992; Hardy 1985; `build/coordinator/scholar-
literature-2026-10-01.md` A2, E.1.1).

- **Two generations within the reserve.** The publish program holds at
  most two images at any cut: the durable old file and the staged new one.
  Each is within the capture budget B = `fn-ock-capture-budget` =
  `fn-sccr-file-read-bound` (three times `max-history-octets` plus one
  segment's framing): the old one because the open refuses a file past the
  reader's bound, the new one because `fn-ockp-decide` plans only an
  estimate within B and the estimate is the file's length
  (`fn-ockp-estimate-is-len-file-octets`). KEYSTONE
  `fn-ckr-two-generations-fit-the-reserve-at-every-cut` (PROVED): at every
  state of `fn-bs-run` over `fn-bs-scp-program` from a quiet store
  (`fn-ckr-all-fit`: the pairs after every step, the five cuts included),
  with the new image within BOUND and the old within BOUND, the octets the
  two images take through the view (pending writes included,
  `fn-ckr-generations-octets`) are at most 2 * BOUND. The format-time
  reserve is `fn-ckr-reserve-octets` = 2 * `fn-sccr-file-read-bound`
  (`fn-rrs-reserve-is-two-capture-budgets` ties it to
  `fn-ock-capture-budget`, in the store instance).
- **The checkpoint never needs unreserved space.**
  `fn-rrs-funded-reserve-never-defers-for-space` (the store instance,
  written, not admitted): when the observed free
  octets cover the maintenance reserve (`fn-smr-reserve-octets`, STO-019)
  plus one budget, an estimate within the budget is `(:plan estimate)`,
  never `:exceeds-space`. Under the format-time reserve that observation is
  one the host no longer needs to make; retiring the statvfs read from the
  decision is a served host change outside this lane (MODE §2).
- **The forcing bound.** The owner publishes when the suffix reaches K/2
  (`fn-ock-publication-duep`); `fn-ock-not-due-keeps-the-checkpoint-open`
  is the theorem that until then a restart is served from the checkpoint.
  K is the fast path's threshold, not a maximum suffix (ember, 2026-09-26).
- **Sized by K, in the target medium: PROVED for the model's commit**
  (`books/recovery-refinement-pages.lisp`, PRF-1215). On the page store a
  checkpoint is a root commit (`pgs-plan-commit`): the dirty pages
  copy-on-write to fresh addresses, the table pages they touch, the
  directory run, the record to the other slot. A generation is what one
  commit writes, and `fn-rrp-commit-writes-within-the-generation` bounds it
  by `fn-rrp-generation-pages` = 2|DIRTY| + 1 (one page per dirty page, at
  most one table page per dirty page since `pgs-touched` emits each touched
  table once, the directory). `fn-rrp-two-generations-fit-the-reserve`: two
  planned commits over dirty sets of at most K * D pages (K records, D pages
  a record) write at most `fn-rrp-reserve-pages` K D = 2(2KD + 1) in all:
  KeyKOS's reserve in pages (EROS's snapshot-at-an-instant lets the next
  suffix accumulate beside the staged generation). What binds |DIRTY| to
  K * D on the host (the due rule at K/2, a per-record dirty bound from the
  profile), the root record's log position S, and the page store as an
  instance of §1's medium are PRF-1220 (§5): no host path opens the owner's
  state from a root yet (design stage 5), so the page store's crash story
  today is its own keystone, `pgs-open-after-crash` (PRF-344), the
  "medium's own ordering" row of §2, with the snapshot program's cuts
  mapped onto it:

  | cut (`*pgs-snapshot-cuts*`, `pgs-cut-crash-point`) | KEEP | slot | `pgs-open-after-crash` says |
  | --- | --- | --- | --- |
  | :begin | none of the writes | old | the OLD view |
  | :page-written k, :table-written k | the first k data (table) writes | old | the OLD view |
  | :dir-written | every write | old | the OLD view |
  | :record-torn | every write | a record that does not validate | the OLD view (the slot's `pgs-rec-valid` fails) |
  | :record-written, :record-synced | every write | new | the NEW view (`pgs-open-after-commit`) |

  The host's commit is `pgs-x-commit` (`books/pagestore-refine.lisp`,
  `pgs-x-commit-refines-plan` equates its plan to `pgs-plan-commit`), so the
  bound is about what `fnps-commit` writes through that square; MODEL-LEVEL
  as §1.

## 5. Open obligations (registry rows, not premises)

- **The store instance is not admitted.** `books/recovery-refinement-store.lisp`
  includes `store-checkpoint-open`, `store-recover-stream` and
  `owner-checkpoint-writer`, whose chains reach `books/store-events-carried.lisp`
  (`fn-evc-consumer-shape`) and `books/store-node-traces.lisp`
  (`fn-snt-record-directory-preserves-relation`), red at dev 896c48c16 (the
  record-shape revert of stage 0). Nothing in it is a claim until that
  tower is green and the book certifies; the rows PRF-1212 and PRF-1213
  say so.

- **PRF-1214, R lifted to per-inode pending: PROVED**
  (`books/recovery-refinement-concurrent.lisp`). `fn-rrc-relp` is R with
  `fn-bs-ops-for-ino` of the pending list in place of the whole list; the
  kernel's R implies it. The byte model orders nothing across inodes, and
  that is a theorem: THE PROJECTION
  `fn-rrc-crash-content-is-the-projected-crash-content` (a crash image's
  content at an inode is the content of the projected store's image under
  the projected choices), so every theorem of the generic book transfers
  through the projection and the keystone is restated over `fn-rrc-relp`
  (`fn-rrc-recovery-refines-a-prefix-with-every-acknowledged-record`). The
  concurrent checkpoint cuts are
  `fn-rrc-checkpoint-crash-point-refines-with-a-batch-in-flight` (§3). The
  kernel's own R and the programs' keeps-the-relation theorems are
  unchanged: the lift is a weakening the composition is stated over, not a
  change to the served invariant.
- **PRF-1221, the cut table's remaining rows.** Each remaining program
  owes one keep-the-segment theorem over its run (§3); with it the lifted
  keystone covers its cuts by `fn-rrc-keeping-the-segment-keeps-the-lifted-
  relation`. The rotation programs move the relation's INO and need their
  own theorems cited instead.
- **PRF-1215, the page store's generation: PROVED** (§4,
  `books/recovery-refinement-pages.lisp`): the commit's write bound and the
  two-generation reserve in pages.
- **PRF-1220, the page store as the medium.** Open until design stage 5
  (fn-hist on pages): (a) a root's pages decode to the capture of the first
  S committed records, S carried on the root record (PRF-199's shape);
  (b) the open from a root over the log's suffix as `fn-rr-medium-open`,
  equal to the full open of prefix ++ suffix, with `-open-okp` and `-holds`
  over the opened pages; (c) `pgs-open-after-crash` as the binding of the
  image read to S_old or S_new; (d) the host's open from a root named as
  the subject (PRF-344's open square); (e) |DIRTY| <= K * D on the host
  (the due rule at K/2 and a per-record dirty bound from the profile),
  discharging `fn-rrp-two-generations-fit-the-reserve`'s hypotheses.
- **PRF-1222, the host's checkpoint write joined to the reserve** (the
  Codex review of 2d1b10ed7, F5; restated after r10). PRF-1213 bounds the
  model's OCTETS, one `:write-all`. The staged file the host writes is
  `fn-his-file-octets` (`host/store-node-host.lisp`: the history image
  region, `fn-his-region-octets` of the image's page count, plus the
  stream the checkpoint steps write), produced by `fnn-history-image-write`
  then `fnn-checkpoint-write-steps`, and it is not the table estimate
  `fn-ockp-decide` plans against. Two obligations, neither a byte
  equality: (a) the octets the two loops write have length
  `fn-his-file-octets` of the image's page count and the steps' stream,
  and that length is within `fn-ock-capture-budget` (the reader's bound the
  old image is held to), so the two generations are what PRF-1213 bounds;
  (b) a RESERVATION invariant: the reserve's space is set aside at format
  time and the publication draws on it, so that `fn-ockp-decide`'s free-
  space observation (statvfs) can be retired (MODE §2: a served host
  change). Byte equality alone discharges neither; until both land the
  funded-space premise is an assumption of the join.
- **PRF-1223, the write loops' inner cuts: REGISTERED, NOT RESOLVED**
  (F6). `fn-bs-scp-program` (`books/byte-store-state-checkpoint-program.lisp`)
  is still one `:write-all`, `tests/campaign/native_cuts.py` is unchanged,
  and the intra-batch SIGKILL points of `host/native/io.lisp`
  (`fnn-checkpoint-write-steps`' per-step kill under
  `fnn-checkpoint-batch-fault`; `fnn-history-image-write`'s header, pad and
  page writes) have NO model crash point today. Expected shape: the
  `:write-all` split into the batch's writes, each a cut, every state's
  images recovering COMMITTED under the OLD image (the root entry is
  untouched until the rename); the cut rows added to the table. PRF-1216
  covers the five outer cuts only.
- **A-CRYPTO-TRAILER's witness** (F4, against `books/assumptions.lisp`, not
  this lane's books). The keystone's premise `fn-lg-platform-tears-p` is a
  constrained consequent; its local witness admits only the exact tear, so
  the theorem's applicability to a torn write is witnessed by nothing
  executable. The natural witness ("no tears": observed = written) needs
  `fn-bs-view-is-an-admissible-image`, open there.

## 6. Teeth

`tests/acl2/recovery-refinement-tests.lisp`: the keystone on the two-record
ground log (the fixture of `tests/acl2/store-log-durable-tests.lisp` under
its own prefix: a related state, a third record in flight, every per-unit
tear at log-written, nothing pending at log-fenced); the ground medium (the
interface's witness, executable) instantiated into `fn-rr-open`, the
composed open at S = 0, 1, 2, past K and absent, and the keystone itself
instantiated over it (`rrt-keystone`, the literal theorem with the medium's
six functions replaced) with a reachable positive witness asserting its
complete antecedent and conclusion at log-written with the batch landed
whole (the exact tear, where the trailer premise evaluates without reaching
the constrained function) and at log-fenced; at a non-exact tear the
premise is the assumption's consequent and only the conclusion is
evaluated (§5, A-CRYPTO-TRAILER's witness); the MUTATION: a recovery that
drops the acknowledged r2 (the segment zeroed from its entry) is no
admissible image of the fenced segment and the conclusion fails on it;
hypothesis removal, one hypothesis each: the binding (a non-prefix capture
opens elsewhere), the relation (a pending write of TWO records r3 r4 under
INFLIGHT = (r3): the trailer premise still evaluates true on the landed
image, the choice is admissible, and the recovered r1 r2 r3 r4 is no
tree-sequence member); and §8's theorem at all ten states of the publish
run under two choices. `tests/acl2/checkpoint-reserve-tests.lisp`: the ten
states at bound 3, the first publication without an old image, and the
violating values refused one hypothesis at a time (a new image past the
bound 2 with the old within it; an old image past the bound 3 with the new
within it), each witness asserting the retained hypotheses, the removed one's
failure and the conclusion's failure.
