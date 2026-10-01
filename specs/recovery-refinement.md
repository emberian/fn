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
  `fn-sf-records` of the opened Store's files); the store's functions discharge it by functional
  instantiation in `books/recovery-refinement-store.lisp`, the log's
  records decoded by `fn-srs-decode` (the host's `fn-store-decode-records`).

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
   the committed count), the open the host composes (`fn-rr-open`: the
   selection under K, then `fn-sco-open` of the image over the suffix it
   leaves, or the full open) equals `fn-cpo-open-observed` of the recovered
   records (`fn-sn-recover-from-checkpoint-equals-full-recover`, PRF-083).
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
   the composed open unchanged.

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
| external synchrony (STO-003) | ACKED <= len COMMITTED inside R; a member joins `fn-owb-acked` only after the batch's fence | fn obligation | `fn-owb-fence`, `fn-owb-finish-one` (`books/owner-batch.lisp`); the native ack path `host/native/io.lisp` fnn-finish after fnn-log-publish's barrier (`tests/campaign/native_cuts.py` POST_CUTS) |
| the platform's crash | `fn-bs-crash-imagep bs image` | model (A-CRASH-IMAGE, crash model v2 §1.5) | per-unit tears, zero-fill, garble, dropped entry operations; the model is the premise, the platform rows below are what makes it true of a box |
| A-DURABILITY, A-WRITE-ISOLATION | `fn-bs-crash-keeps-fenced-content` (a fenced inode's durable content survives every image) | named assumptions, `books/assumptions.lisp` | used in the quiet case (nothing in flight) and in the medium's half |
| A-CRYPTO-TRAILER | `fn-lg-platform-tears-p (nthcdr F content) INFLIGHT LAST UNIT` | named assumption, `books/assumptions.lisp` | removes the forgery disjunct of `fn-lgk-crash-of-related-state-is-a-prefix` (`fn-lg-no-forgery-under-a-crypto-trailer`); without it the theorem holds with "or the first damaged entry forges", the pessimistic figure the collision one, about 2^-128 per chosen pair |
| image binding | `ckpt = (fn-rr-medium-capture configs (take s committed))`, `s <= len committed` (the store instance: `fn-sco-capture` of the decoded prefix) | fn obligation of the publication | `fn-sct-decode-file-of-file-is-the-capture` (PRF-199), `fn-sct-load-is-decode-file` (PRF-135), `fn-ock-finish-binds-the-captured-prefix`, `fn-ock-next-checkpoint-is-the-capture` (PRF-083): what the owner writes is the capture of the committed records it was handed, and S is their count |
| fsync ordering | implicit in the binding: the captured records are COMMITTED (fenced) records, so S never exceeds the durable count | fn obligation (the owner captures under its mutex from the committed rows) and a selection arm | `fn-sco-select`'s `:ahead-of-history` arm refuses S past the recovered count; a bound S with different records (a log repaired or rolled back under a kept image) is the freshness gap C2-12, outside the crash-only claim |
| the medium's own ordering | stage, write, fsync file, rename, fsync dir (`fn-bs-scp-program`); pages, table, root slot, one fdatasync (`pgs-plan-commit`) | proved per medium | `fn-bs-scp-program-crash-is-old-or-new`; `pgs-open-after-crash` (PRF-344) |
| A-HOST-EXCLUSIVE-READ | the image's range reads concatenate | named assumption | `fn-bs-read-ranges-concatenate` |
| A-DURABLE-EXTENT, A-DURABLE-LZ | a recovered record's payload read from its segment extent is the durable octets | named assumptions, `books/assumptions-durable.lisp` | the arena's consumers after the open; the records themselves are what the scan reads |
| the platform rows | not in the theorem | MEASURED, per deployment | Linux ext4/xfs: fdatasync drains the inode's writes, fsync(dir) the entries, a failed fsync has marked the pages clean (fsyncgate; crash model v2 §1.6); Darwin: `fsync` does not reach the drive, `F_FULLFSYNC` does, so laptop runs are not durability evidence for the node; OpenBSD (the friend node): its own row. Each is a measured premise of the qualified image, never a theorem |

What the theorem does not say: nothing about a crash INSIDE a publication
while a batch is in flight (§5, PRF-1214); nothing about freshness (a valid
older image with a truncated log needs an external anchor, C2-12); nothing
about the host's open loop being the model's (the open square).

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
| finish-consumed, finish-durable, recovery-stage-unlinked | `fn-bs-finish-program`, `fn-bs-recover-stage-cleanup-program` | K0: these programs touch no segment octet (`fn-bs-k0-finish-program-preserves-relation`); R's segment conjuncts are untouched and the pending set is the finish's own entry operations, outside the segment inode. The lift of R's fourth conjunct to per-inode pending that makes this a citation rather than an argument is PRF-1214 |
| state-checkpoint-created, -written, -staged-durable, -replaced, -durable | `fn-bs-scp-program` | PROVED, PRF-1216: `fn-rr-checkpoint-crash-point-recovers-committed-under-old-or-new`: from the quiet store (`fn-bs-scp-inputp`, nothing pending, so nothing in flight) the program never writes the segment (`fn-rr-all-keep-segment` over the run), every crash image of every state recovers exactly COMMITTED and holds the old or the new image (`fn-bs-scp-program-crash-is-old-or-new`). The concurrent case (a batch in flight meanwhile) is PRF-1214 |

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
- **Sized by K, in the target medium.** On the page store a generation is
  the dirty pages of at most K commits since the last root (the due rule
  forces the checkpoint by that bound, EROS's snapshot-at-an-instant lets
  the next suffix accumulate beside it); that bound and the page-store
  instance of §1 are PRF-1215.

## 5. Open obligations (registry rows, not premises)

- **The store instance is not admitted.** `books/recovery-refinement-store.lisp`
  includes `store-checkpoint-open`, `store-recover-stream` and
  `owner-checkpoint-writer`, whose chains reach `books/store-events-carried.lisp`
  (`fn-evc-consumer-shape`) and `books/store-node-traces.lisp`
  (`fn-snt-record-directory-preserves-relation`), red at dev 896c48c16 (the
  record-shape revert of stage 0). Nothing in it is a claim until that
  tower is green and the book certifies; the rows PRF-1212 and PRF-1213
  say so.

- **PRF-1214, R lifted to per-inode pending.** R's fourth conjunct names
  the segment's write as the ONLY pending operation of the store. A crash
  point inside the owner's publication thread while a batch is in flight
  has two pending sets (the segment's write, the staged file's), outside R.
  The byte model already orders nothing across files, so the lift is to
  `fn-bs-ops-for-ino` in R and in the tear lemma's hypotheses
  (`fn-lg-batch-crash-is-a-prefix`); with it the finish and stage-cleanup
  rows of §3 and the checkpoint-program row cite R directly.
- **PRF-1215, the page store as the medium.** `pgs-open-after-crash` is the
  old-or-new premise over the model disk; the binding of a root's image to
  a captured prefix, the open from a root (the host's open loop; PRF-344's
  open square) and the dirty set of K commits as the generation bound are
  the stage-5 and stage-7 work.
- **PRF-1222, the host's checkpoint write refined to OCTETS** (the Codex
  review of 2d1b10ed7, F5). PRF-1213 bounds the model's OCTETS; the host
  writes the staged file through `fnn-state-checkpoint-write` ->
  `fnn-history-image-write` and `fnn-checkpoint-write-steps` with no
  theorem that their concatenated writes are `fn-sct-encode` of the
  captured prefix with the planned estimate's length; until it lands,
  funded space is an assumption of the join, not a consequence of the
  reserve.
- **PRF-1223, the write loops' inner cuts** (F6). The model's `:write-all`
  is one operation; the host dies between write(2) calls
  (`fnn-checkpoint-write-steps`' per-step kill under
  `fnn-checkpoint-batch-fault`, `fnn-history-image-write`'s header, pad
  and page writes). Each is the model state with k pending writes to the
  staged inode and the root entry old, so its images recover COMMITTED
  and hold the OLD image; the chunked program and the cut rows that make
  that a theorem are the row's work. PRF-1216 covers the five outer cuts.
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
