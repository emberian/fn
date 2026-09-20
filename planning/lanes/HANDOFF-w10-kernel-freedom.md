# Handoff: lane `w10/kernel-freedom` (D14-b, the recovery freedom)

Branch `w10/kernel-freedom` in `build/lanes/w10-kernel-freedom`, from `dev` at
`f730c24`, merged `dev` at `6fba627`. All ACL2 on persvati
(`/home/ember/fn-lanes/w10-kernel-freedom`, ACL2 8.7 at
`$HOME/fn-tools/acl2-8.7/saved_acl2`, via `tools/farm.py`) except three `ld`
probes of `books/store-files` + `books/store-files-invariants` on the laptop,
one process at a time through `tools/acl2 --timeout 600`.

## 1. What the packet asked, and what the evidence said instead

The packet: widen `fn-sf-crash-imagep` (`books/store-files.lisp:593`) so a
`:replaying`/`:recovering`/`:fenced-recovery` state also admits its record list
with the last element dropped, then re-prove the closure.

That was done first, exactly as proposed, gated on `(null (fn-sf-successes
s))`. The wide run is persvati `run-20260920T211812Z-1f0a`, `--affected-by
books/store-files.lisp --closure`, 122 roots, **23 failed in 272 s**. Twenty-two
were cascades of one include; the single genuine proof failure was
`fn-snt-admissible-crash-image-is-recoverable`
(`books/store-node-traces.lisp:678`), which needs a prefix-recoverability lemma
the tree does not have.

Reading the two `-extends-` theorems behind that cascade then produced a
**counterexample that refutes the proposal**, and it is now mechanized.

## 2. The counterexample

`*own-reopened*` (`tests/acl2/owner-tests.lisp`, already in the book before
this lane) is an ordinary reachable owner, reached by the trace
open / post / open / advance / post / close / reopen:

* its store is a recovery-window state (`fn-sf-record-rollback-visiblep` is T);
* its own success history is **empty** -- `fn-sn-open-observed` keeps no ghost
  (`fn-sn-open-observed-success-exact-history`);
* its **ledger** names both of its records, and the second is one an earlier
  process completed and acknowledged, hence fenced.

The emptiness gate the proposal rests on is a fact about *this state's* success
list, not about what earlier processes promised, so it does not protect that
record. A widened `fn-sf-crash-imagep` -- which is the gate of `fn-own-reopen`
(`books/owner.lisp:911`) -- therefore lets the reopen take the rolled-back
image, and `fn-own-ledger-durablep` is then false, so
`fn-own-reopen-preserves-relation` is FALSE.
`fn-bprv-crash-image-extends-history` and `fn-bprv-observed-reopen-facts` fail
the same way.

**No narrower kernel gate exists.** Which of a state's records are fenced is a
fact about the byte store's pending list (`fn-bs-store-relation`), not about
the kernel state: a `:replaying` state reached by `fn-sn-open-observed` and one
reached by `fn-sf-crash ... :absent` are the same tuple, and only the first may
lose its tail. A marker field does not help either, because the reopening
process is the one that cannot know.

## 3. What shipped

Two recognizers instead of one.

| name | what it is | who takes it |
| --- | --- | --- |
| `fn-sf-crash-imagep` | the RELIANCE predicate, **unchanged byte for byte** | the gate of `fn-own-reopen`; the premise of all eleven theorems in §4 |
| `fn-sf-recovery-crash-imagep` | the PLATFORM predicate: the stable list, that list plus the data-durable candidate, or -- only in the recovery window, only with `(null (fn-sf-successes s))`, only with `(consp (fn-sf-records s))` -- that list without its last element | the CONCLUSION of `specs/crash-model-v2.md` K2; a premise of nothing |

Supporting, all certified: `fn-sf-recovery-visiblep`,
`fn-sf-record-rollback-visiblep`, `fn-sf-but-last`, `fn-sf-stable-records`,
`fn-sf-crash-rollback` (the second constructor), `fn-sf-image-crash` (selects
between the two constructors).

`fn-sf-crash-choicep` gains **no** third choice and `fn-sn-crash` is untouched.
Giving the trace language's crash event a rollback choice would let a trace
drop a record an earlier process acknowledged -- the reopened state carries no
success of its own while its record list still holds those records -- and
`fn-snrt-acknowledged-record-retained-across-observed-reopen` would be false.

New keystones:

* `fn-sf-recovery-admissible-image-facts` -- **this is K2r, proved**: an
  acknowledged pair of the pre-crash state names a record of EVERY image the
  platform may leave, the rolled-back one included, because the arm that drops
  a record and a non-empty success history cannot both hold.
* `fn-sf-recovery-crash-realizes-every-admissible-image` -- K3 over all three
  arms. The old `fn-sf-crash-realizes-every-admissible-image` stands unchanged
  beside it.
* `fn-sf-recovery-crash-image-extends-stable-records` -- the exact retention
  guarantee. Outside the window `fn-sf-stable-records` IS `fn-sf-records`
  (`fn-sf-stable-records-outside-the-window`), so this is the old "an
  admissible image extends the record list" verbatim there.
* `fn-sf-crash-imagep-implies-recovery-crash-imagep`,
  `fn-sf-crash-rollback-preserves-state`,
  `fn-sf-crash-rollback-image-is-recovery-admissible`,
  `fn-sf-image-crash-preserves-state`.

## 4. The enumerated premise-taking closure, with verdicts

Every theorem in the `store-files`, `store-observed`, `store-node`, `owner` and
`bp-receiver` closure that takes `fn-sf-crash-imagep` as a premise. There are
**eleven**, plus one definition that gates on it and one that mentions it.
Because the predicate is unchanged, every statement and every proof is
unchanged; the column that matters is what the WIDE predicate would have done
to each, which is the evidence for §2.

| # | theorem | book:line | verdict | under a widened `fn-sf-crash-imagep` |
| --- | --- | --- | --- | --- |
| 1 | `fn-sf-crash-realizes-every-admissible-image` | `store-files-invariants:440` | unchanged, certified | would need `fn-sf-image-crash`; that version shipped as the `-recovery-` twin |
| 2 | `fn-sf-crash-imagep-implies-state` | `store-files-invariants:468` | unchanged, certified | true; twin added |
| 3 | `fn-sf-admissible-image-facts` | `store-files-invariants:491` | unchanged, certified | true; twin added (`-recovery-`), and it is K2r |
| 4 | `fn-own-crash-image-extends-records` | `owner-invariants:336` | unchanged, certified | **FALSE** -- the image no longer extends the record list |
| 5 | `fn-snt-admissible-crash-image-is-recoverable` | `store-node-traces:678` | unchanged, certified | **UNPROVED** -- needs prefix recoverability; measured failure in `run-20260920T211812Z-1f0a` |
| 6 | `fn-sn-acknowledged-record-survives-observed-reopen` | `store-observed:625` | unchanged, certified | true (its `member-equal` hypothesis and the arm's gate are contradictory) |
| 7 | `fn-snrt-acknowledged-record-retained-across-observed-reopen` | `store-observed:706` | unchanged, certified | true for the predicate; **FALSE** if `fn-sf-crash` gains the choice |
| 8 | `fn-bprv-crash-image-extends-history` | `bp-receiver-evolving-store-invariants:388` | unchanged, certified | **FALSE** -- same shape as row 4 |
| 9 | `fn-bprv-observed-reopen-facts` | `bp-receiver-evolving-store-invariants:398` | unchanged, certified | **FALSE** via row 8 (`fn-bprv-extendsp`) |
| 10 | `fn-bprv-evolving-invariant-survives-observed-reopen` | `bp-receiver-evolving-store-invariants:428` | unchanged, certified | **FALSE** via row 9 |
| 11 | `fn-bpr-live-receipt-regenerated-after-restart` | `bp-receiver-evolving-store-invariants:627` | unchanged, certified | **FALSE** via rows 8 and 9 |
| d1 | `fn-own-reopen` (definition, the host's reopen gate) | `owner.lisp:911` | unchanged | the gate would admit the rolled-back image: this is the counterexample |
| d2 | `fn-bs-store-relation` (definition) | `byte-store-scan.lisp:510` | unchanged | unaffected; its recovery arm already carries the emptiness |
| c1 | `fn-sf-crash-image-is-admissible` (conclusion, not premise) | `store-files-invariants:342` | unchanged, certified | wider conclusion, still true |

**Separation witnesses.** Rows 1 to 11 keep the witnesses they had, and those
still separate because the premise is unchanged: `tests/acl2/store-files-tests`
(the six crash-point states), `tests/acl2/store-files-teeth-tests`,
`tests/acl2/store-node-teeth-tests:224/240/262`,
`tests/acl2/store-observed-traces-tests:140-147/179-180/232`,
`tests/acl2/bp-receiver-evolving-tests:142/355`. The new predicate's witnesses
are new, and there is one per conjunct of its gate:

* reachable and non-degenerate: `*fn-so-gap-opened*`, a process opened on a
  TWO-record image, admits the one-record image and not the empty one, not the
  list with the first record dropped, and not a rolled-back frontier;
* the PHASE conjunct: `*fn-so-gap-ready*` -- the same two records, the same
  empty success history, the same frontier, five barriers later -- refuses it;
* the SUCCESS conjunct: `*fn-so-acked-replaying*` -- a `:replaying` state
  reached by `fn-sf-crash`, which carries the ghost history -- refuses it, and
  the record the dropped image would have lost is asserted to be the
  acknowledged one;
* the `consp` conjunct: `*fn-so-empty*`, where the third arm would be the first
  disjunct restated, so `fn-sf-record-rollback-visiblep` is false there;
* the two predicates are asserted to DIFFER on `*fn-so-gap-opened*`, which is
  the whole of D14-b;
* the constructor's inhabitation and its image, and that the rolled-back image
  still opens (`fn-sn-open-okp`), so the freedom is an image the host cannot
  tell from the durable one rather than one it would refuse.

## 5. Per-root certification

All on persvati, `--jobs 4`, `--remote-root /home/ember/fn-lanes/w10-kernel-freedom`,
`--affected-by books/store-files.lisp --closure`, ACL2 8.7 / SBCL.

| run | tree | roots | result |
| --- | --- | --- | --- |
| `run-20260920T211812Z-1f0a` | the FIRST shape: `fn-sf-crash-imagep` itself widened | 122 | **23 failed**, 272.2 s. One genuine proof failure, `fn-snt-admissible-crash-image-is-recoverable`; 22 includes of it. Kept: this is the measurement behind §2. |
| `run-20260920T213023Z-4804` | the shipped shape, before merging `dev` `e5e6218` | 122 | **7 failed**, 306.8 s, none in the `fn-sf-crash-imagep` closure. Every store root passed: `books/store-files{,-invariants}`, `books/store-node-traces`, `books/store-observed`, `books/byte-store-scan`, `books/bp-receiver-evolving-store-invariants`, `tests/acl2/store-files-tests`, `tests/acl2/store-observed-traces-tests`, `tests/acl2/store-node-teeth-tests`, `tests/acl2/bp-receiver-evolving-tests`. |
| `run-20260920T213846Z-bd4f` | the shipped shape, after merging `dev` `e5e6218` | 129 | **125 passed, 4 failed**, 286.9 s. Evidence `build/acl2/certify-20260920T213853Z-3576178`. |
| `run-20260920T214551Z-90a4` | the final tree, `--affected-by books/store-files.lisp --affected-by books/byte-store-scan.lisp --closure` | - | the confirming run over the `:rule-classes nil` and byte-store-scan comment commits; see the board. |

**The four failures of the third run, and why none is this lane's.**

* `books/owner-invariants` is open at `fn-own-advanced-session-is-bounded`, a
  theorem in the auth/peer session vocabulary, and **this lane does not touch
  that book**: `git diff dev...HEAD -- books/owner-invariants.lisp
  books/owner.lisp books/owner-config.lisp` is empty. It is a defect in dev's
  current merge state (`w10/auth-served` against `w6/peering-feed-4`); the
  peering lane recorded the same three roots failing on dev `ca1ce5d`, at a
  later form (`planning/deputies/BOARD.md`, `w6/peering-feed-4`'s verdict).
* `books/owner-config` and `tests/acl2/owner-tests` are includes of it.
* `tests/acl2/checkpoint-codec-tests` fails an `assert-event` about
  `fn-cpc-validp` on a bad-generation record; its include closure is
  `books/checkpoint-codec` alone, with no path to `books/store-files`. It
  failed identically in the first run, under a different kernel.

**Consequence for the counterexample.** The owner-specific spelling of it
(`tests/acl2/owner-tests.lisp`, using `fn-own-ledger-durablep`) is **written
and not run** -- not admitted, not certified -- because that book cannot be
certified in this tree at all and its dependency has no certificate to `ld`
against either. Its substance is certified: `tests/acl2/store-observed-traces-tests`
passed, and it asserts that the pair `(1 . 2)` of `*fn-so-second*` is in the
two-record list, is **not** in the one-record list, and that
`fn-sf-recovery-crash-imagep` admits that one-record image of
`*fn-so-gap-opened*` while `fn-sf-crash-imagep` does not. That is the ledger
clause's content without the owner's name for it. Say this, and do not call
the owner half certified, until the owner cluster reopens.

## 6. Open, with its checkpoint

* **K2f, new and the next global step.** The recovery window can be entered
  with a pending `:root` entry operation, not only a pending transaction link:
  die at `frontier-replaced` (`tools/run_store.py:1305`), reopen, and the
  rename is drained only by `fsync_dir(self.root)` at `:1216`, the FOURTH
  recovery barrier. A crash at `recover-replayed` (`:1207`) or the first three
  `recover-barrier` cuts (`:1228`) rolls the frontier back to the durable
  value, which the kernel does not hold (`fn-sf-frontier-candidate` is `nil`
  there). `specs/crash-model-v2.md` §3.3 K2 is false in that sub-case. It needs
  a clause in `fn-bs-replay-matches-scan` (the durable frontier is the scanned
  one minus one, true because `advance_frontier` writes `old+1`) and then a
  frontier arm in `fn-sf-recovery-crash-imagep` gated by
  `(fn-sf-record-listp (fn-sf-records ks) 0 0 (1- (fn-sf-frontier ks)))`, which
  is what keeps `fn-sf-recovery-admissible-image-facts` true of it.
* **Prefix recoverability, a packet in the replay cluster.** No lemma says a
  recoverable history stays recoverable when its last record is dropped.
  `fn-sn-replay-loop-append` (`books/store-node-invariants.lisp:309`) gives
  ok(whole) implies ok(prefix); what is missing is that the prefix node is idle
  with `next-txid` at most the frontier. This is exactly what blocked the first
  widening at `fn-snt-admissible-crash-image-is-recoverable`, and K4's route
  through the recovery arm needs it.
* **K1's other three clauses** (config and frontier entry and content, and no
  `:fault`), unchanged from `w9/storage-3`'s handoff. K2 rests on them.
* **The stable-prefix restatement of rows 4 and 8**, if a future lane ever does
  want the reopen path to cover the recovery arm: the honest form is
  `(fn-sf-prefixp (fn-sf-stable-records ...) records)`, which
  `fn-sf-recovery-crash-image-extends-stable-records` already proves at the
  kernel. Carrying it through the owner and the receiver means strengthening
  `fn-own-relation` and `fn-bprv-system-invariantp`, and that strengthening is
  NOT preserved by reopen for the same reason the counterexample bites, so it
  is not a small change. Say so before starting it.
