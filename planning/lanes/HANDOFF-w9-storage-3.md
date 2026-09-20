# Handoff: lane `w9/storage-3` (the §3.2 decision, the K seam, the cuts)

Branch `w9/storage-3` in `build/lanes/w9-storage-3`, from `dev` at `ca8a2ef`.
All ACL2 on hbox (`/tank/fn/lanes/w9-storage-3`, ACL2 8.7 at
`/tank/fn/acl2-8.7/saved_acl2`, every run wrapped in `swarm-build` by
`tools/farm.py`); the fault campaign on persvati
(`/home/ember/fn-lanes/w9-storage-3`). Nothing ran on the laptop.

## 1. D14-a: the §3.2 pending-name clause, decided from the host

Recorded in [`planning/decisions.md`](../decisions.md) with its full evidence;
`specs/crash-model-v2.md` §3.2, §3.3 and §7's K2 row are rewritten to match,
and `FLR-001` carries the gap the decision exposed.

**Selected:** keep `books/byte-store-scan.lisp`'s
`(fn-bs-txn-name (len (fn-bs-durable-names bs :transactions)))`. §3.2's
`(fn-bs-txn-name (len (fn-sf-records ks)))` is withdrawn, and so is the other
candidate, the blanket equality of counts.

The link is removed from the pending list in TWO places, so there are two
windows and six cut states (`tools/run_store.py` at `ca8a2ef`):

| window | cuts | durable names | `(fn-sf-records ks)` | the two forms |
| --- | --- | --- | --- | --- |
| publish (`publish:1334`-`1348`) | `record-linked` 1338, `record-attempted` 1346, the `record-link :error` branch 1336 | `R` | `R` | agree |
| recovery (`recover:1164`-`1187`) | `recover-replayed` 1179, two `recover-barrier` 1200 | `R` | `R+1` | **disagree** |

The publish window holds because the only transition that appends to
`fn-sf-records` is `fn-sf-record-dir-result :ok`
(`books/store-files.lisp:507`), which the host issues at `publish:1353`
strictly after the `fsync_dir(self.transactions)` at 1348 that empties the
directory's pending list (`fn-bs-fsync-dir`, `books/byte-store.lisp:549`).
The recovery window exists because **process death is not power loss**: the
entry operation stays in the kernel's cache, the next process's
`durable_records` (1100) scans the VIEW, and `acl2.recover` (1164) replays
`R+1` records into a `:replaying` image (`host/store-node-host.lisp:39`).
This is the campaign's ordinary path, not a corner.

Consequences in the book: `fn-bs-pending-matches-phase` splits into
`fn-bs-pending-shape-okp` (at most one entry operation per authority
directory, at the durable namespace's next name, pointing at a fenced inode),
the publish window (which carries
`(equal (fn-bs-durable-records bs) (fn-sf-records ks))` -- an equality of
LISTS, and that, not a count, is what excludes the image holding the
candidate twice) and `fn-bs-replay-matches-scan`, the recovery window.

**The finding to carry forward is a gap in the KERNEL.**
`fn-sf-crash-imagep` (`books/store-files.lisp:593`) has no freedom for a
record that recovery replayed and has not yet re-fenced, so a crash in the
recovery window yields an image it does not admit. Nothing acknowledged is at
risk -- such a state carries no success, because `fn-sn-initial nil 0` starts
with none and `Store.recover` runs exactly once per process, at open
(`run_store.py:1674`, `run_owner.py:660`, `fn9p.py:428`, `run_reader.py:313`,
`run_bp_ingress.py:132`). K2 therefore takes `(not (fn-bs-replay-visiblep
ks))` and the window is the new open row **K2r**. Widening the kernel
predicate is the cross-cluster proposal and was NOT taken here: it changes the
premise `books/store-observed.lisp` and the whole store-node closure take.

## 2. `books/byte-store-scan` certifies

The ld/certify gap was four concrete defects, and none of the three hints the
previous lane left in the book was the cause. What an `ld` driver inherits
from the books it includes, and a `certify-book` world does not, is enabled
RULES.

| # | defect | fix |
| --- | --- | --- |
| 1 | `fn-bs-crash-select-names-are-an-outcome` recursed to the induction-depth-limit at 33,381,159 steps (`certify-20260920T193919Z-1122107`, log:16128) | `fn-bs-member-of-append` is byte-store-invariants' OWN rule, withdrawn with `fn-bs-invariants-vocabulary`; enabled here, not restated |
| 2 | `fn-bs-txn-names-length` failed at `Subgoal *1/4'` | `len` of `append` is `local` in that book; restated locally |
| 3 | `fn-bs-assoc-of-name-in-entries` was **false as stated** -- `(strip-cars '(nil))` is `(nil)`, and `(assoc-equal nil '(nil))` is `nil` | hypothesise `(alistp alist)` |
| 4 | `fn-bs-txn-name-not-in-txn-names` carried `:in-theory (disable fn-bs-txn-name)` on a CONSTRAINED function -- a HARD ERROR under `certify-book`, silent under the probe | removed; the injectivity constraint does the work |

Two general traps for other lanes: **a theory expression naming a constrained
function is a certify-only hard error**, and **an `ld` probe that includes
several books sees their withdrawn vocabularies**.

Two things also changed shape, for the proof and not around it:
`fn-bs-names-outcomes` loses its unused third formal (it now mirrors
`fn-bs-entry-outcomes` formal for formal) instead of carrying
`(ignorable dir)`; and `fn-bs-record-of` splits into
`fn-bs-record-of-octets` (the decoder, a function of the OCTETS) and
`fn-bs-record-of` (that of the content), which is what
`fn-bs-read-records-under-agreement` needed -- with the decoder written only
over states its conclusion is two closed terms over different states and
nothing connects them.

## 3. K1's bridge, and the profile that found it

`fn-bs-apply-entries-names-is-names-after` is **proved**. Three hints had been
tried and none was the cause. `tools/proof_profile.py` named it in one run:
THIRTEEN runes with no useful application at all, headed by the recognizers
being OPENED -- `FN-BS-ENTRIESP` 47,712 frames, `FN-BS-DIR-TABLEP` 42,664,
`ASSOC-EQUAL` 26,504, `ALISTP` 16,224, all re-deriving `(alistp dirs)` in
every branch. Closing them at the form and enabling
`fn-bs-dir-tablep-implies-alistp` so the fact arrives as a rewrite takes the
form from an induction-depth-limit blowout at **2,016,278** prover steps to
**33,789** steps and 0.05 s. The brief's rule, working exactly as written.

On it, and CLOSED: `fn-bs-crash-names-is-names-after`,
`fn-bs-crash-image-names-are-an-outcome` and
`fn-bs-crash-image-transaction-names` -- K1's namespace clause, "exactly the
durable transaction namespace, or that namespace with the one pending link's
name appended". The last of them needed two things beyond the bridge:
`fn-bs-names` and `fn-bs-durable-names` both CLOSED, since the only thing
that connects them is the image's quietness; and the relation's "exactly one
pending entry operation" stated by SPINE (`(and (consp ops) (not (consp (cdr
ops))))`) rather than as `(equal (len ops) 1)`, because `fn-bs-names-outcomes`
walks the spine and a bound on the length leaves it closed. `specs/crash-model-v2.md`
§3.2 carries the spine form now.

**`tools/proof_profile.py` was broken and is fixed in this lane.** The driver
is the book's own source, so its `include-book` forms are relative to the
BOOK's directory; it ran at the tree root, every include failed with "the
file does not exist", the prefix never built, and the report said
"the form closed" with "no useless runes" over an EMPTY world. Every profile
taken with this tool before 2026-09-20 was reporting an empty world. It now
runs in the book's directory and says loudly when a prefix did not build.

## 4. The fourteen missing host cuts

`tools/transcribe_check.py` now reports `missing-host-cuts=0`
(`transcriptions=10 fidelity-defects=0 syscall-drift=5 unmodelled=4`).
Fourteen `faults.at` markers added where the model program puts its `:cut`,
and ten rows in `tests/campaign/cuts.py` (the five `init-barrier` sites share
one cut name, as `recover-barrier` does), each naming its model crash point.

The five cross-post cuts RUN, on persvati:

    python3 -m tests.campaign.campaign --cut store:frontier-created \
      --cut store:frontier-written --cut store:record-created \
      --cut store:record-written --cut store:record-stage-unlinked

`pairs=5 failures=0 seconds=94.0`. Each case was killed at its point,
reopened through the real recovery path and checked against its record
expectation. `tests/campaign/campaign.py` gains `--cut`, which is what made a
five-cut run possible without paying for the whole table.

The four `initialize` cuts and `checkpoint:candidate-stage-unlinked` carry
`uncovered` with the reason: no campaign scenario initializes a store or
publishes a checkpoint (`tests/campaign/child.py`'s scenarios run against a
template the harness built before the injector exists). **That is the next
campaign packet**: an `initialize` scenario would make four of them live.

## 5. Per-root certification table

| root | state | evidence (hbox, `/tank/fn/lanes/w9-storage-3`) |
| --- | --- | --- |
| `books/byte-store-scan` | **certified** | `build/acl2/certify-20260920T204940Z-1181403` (with K1's namespace clause). Earlier: `certify-20260920T200057Z-1137489` the first certificate at all, `certify-20260920T201600Z-1149433` with the D14-a relation and the bridge, `certify-20260920T202027Z-1153389` with the first two namespace lemmas |
| `books/checkpoint-codec` | **certified** | `build/acl2/certify-20260920T203302Z-1165393` |
| `books/checkpoint-publish` | **certified** | `build/acl2/certify-20260920T203302Z-1165393` |
| `tests/acl2/checkpoint-tests` | **certified** | `build/acl2/certify-20260920T203603Z-1168997` |
| `tests/acl2/checkpoint-publish-tests` | **certified** | `build/acl2/certify-20260920T203603Z-1168997` |
| `books/checkpoint`, `books/replay`, `books/store-node*`, `books/store-files*`, `books/records*`, `books/frame*`, `books/acceptance*`, `books/node*`, `books/retention`, `books/cbor*`, `books/defrecord`, `books/wildmat` | certified in the closure | `build/acl2/certify-20260920T203302Z-1165393` (26 roots) |
| `tests/test_checkpoint` (python) | **passes** | hbox, `python3 -m unittest tests.test_checkpoint`: 6 tests, 136.6 s, including `test_process_death_at_every_cut_recovers_old_authority_or_complete_generation` with the new `checkpoint:candidate-stage-unlinked` marker |
| `tests/campaign` (five new cuts) | **passes** | persvati, `pairs=5 failures=0 seconds=94.0` |

`books/replay` certifying closes the w4-byte-store ASK on the board
(`planning/deputies/BOARD.md:110`) as an observation, not as a fix: nothing
in this lane touched it.

## 6. Open, with its checkpoint

* **K1** `fn-bs-store-crash-image-scans`: its NAMESPACE clause is closed
  (`fn-bs-crash-image-transaction-names`). What is left is the other three:
  the config entry and content and the frontier entry and content (by
  `fn-bs-crash-keeps-untouched-entry`, since the phase clause leaves no
  pending operation at either name, with their contents by
  `fn-bs-crash-keeps-fenced-content` through the relation's authority
  clause), and no `:fault` (by `fn-bs-read-records-under-agreement` against
  `(fn-bs-durable bs)`). Every lemma each one needs is proved in the book.
* **K2** `fn-bs-store-crash-image-is-kernel-admissible`, now with
  `(not (fn-bs-replay-visiblep ks))`.
* **K2r** `fn-bs-replay-window-carries-no-success`: new, and the interesting
  one. It is one unfolding of `fn-bs-replay-matches-scan` away once K0 says
  the relation is preserved; the real content is K0.
* **K3** from K2 and `fn-sf-crash-realizes-every-admissible-image`.
* **The kernel freedom**, the cross-cluster proposal: widen
  `fn-sf-crash-imagep` so a `:replaying`/`:recovering`/`:fenced-recovery`
  state admits its record list with the last element dropped. It is sound --
  such a state carries no success -- and it would let K2 drop its hypothesis
  and K2r disappear. It changes the premise `books/store-observed.lisp` and
  the store-node closure take from the kernel, so it belongs to whoever owns
  `books/store-files.lisp`, with a witness per affected theorem.
* **An `initialize` campaign scenario**, which would make four of the ten new
  cut rows live instead of `uncovered`.
