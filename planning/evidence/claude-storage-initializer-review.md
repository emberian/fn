# Independent review: fresh byte-store initializer (w13)

Reviewer: Claude Opus 5, isolated worktree `build/lanes/w13-claude-review`.
Date: 2026-09-21. Bounded to the fresh-initializer packet; no whole-tree
certification was run and no unrelated subsystem was opened.

## Reviewed revision

* Commit **`8820acc9423495ecd82c4a19374b1a74937170ba`** (`storage: archive
  initializer farm evidence`), baseline `1501492`, lane commits `2ee5166`,
  `20e4353`, `943ec1b`, `8820acc`.
* Subjects: `books/byte-store-initializer.lisp`,
  `tests/acl2/byte-store-initializer-tests.lisp`,
  `specs/crash-model-v2.md:1891-1917`,
  `planning/lanes/HANDOFF-w13-storage-initializer.md`,
  `planning/evidence/manifests/certify-20260921T071623Z-1742111.json`.
* Host anchor read in full: `tools/run_store.py:937-1024`
  (`_open_lock`, `_safe_directory`, `_publish_initial_file`,
  `Store.initialize`).

### Evidence checked, not taken on trust

* Source digests in the archived manifest match the reviewed tree exactly:
  `books/byte-store-initializer.lisp` = `931a4a61e4d3a2a5c9cd23e097fc5a523fa7173439c87d6330cd853548121e87`,
  `tests/acl2/byte-store-initializer-tests.lisp` = `22661d0c53a93366caf709a4cc8c91e9783f8a89f02f798f515d2fd50dae24b4`.
  The manifest records ACL2 8.7, 34 books, both new books `passed`.
  The claimed certification is real and is about these bytes.
* The step-by-step transcription of `Store.initialize` was checked call by
  call against `tools/run_store.py`. **Order, helper inlining and the five
  final barriers are faithful**, including the two places that are easy to
  get wrong: `_publish_initial_file` fences `:root` even when the link
  targets `config/` (`books/byte-store-initializer.lisp:52-54` vs
  `tools/run_store.py:968`), and the separate post-publication
  `(:fsync-dir :config)` therefore is not redundant
  (`books/byte-store-initializer.lisp:87-90` vs `tools/run_store.py:1008`).
  I found no ordering or missing-syscall defect on the fresh path.
* Program indices were recomputed by hand and agree with the test book's
  positional cuts: index 4 = `(:create :root "writer.lock")` (len 5 run),
  index 42 = `(:fsync-dir :config)` (len 43 run), program length 68.

## Findings (5, most severe first)

### F1 — `...-establishes-relation` is blind to every byte this lane added. Severity: high.

`fn-bs-store-relation` (`books/byte-store-scan.lisp:570-589`) reads only:
`:root`'s `config.json` and `allocation-frontier.json` entries, the
`:transactions` namespace, and pending ops on `:root`/`:transactions`.
Every sub-predicate confirms this — `fn-bs-pending-shape-okp:432-433` and
`fn-bs-pending-matches-phase:459-460` bind only `root-ops` and `txn-ops`;
`fn-bs-pending-entry-targets:532-533` collects targets only for
`'(:root :transactions)`; `fn-bs-authority-inode-list:537-542` is those two
plus the two root metadata inodes.

**Counterexample (logical, by definition chain).** Delete step 42,
`(list :fsync-dir :config)` at `books/byte-store-initializer.lisp:89`. The
final store then carries a pending `(:set-entry :config "00000001.cfg" 2)`,
so the generation-1 configuration record is **not durable**. But that op is
on `:config`, so: `fn-bs-ops-for-dir ... :root` and `... :transactions` are
unchanged, `fn-bs-pending-entry-targets` skips it, inode 2 never enters
`fn-bs-authority-inode-list`, and `fn-bs-opp` accepts it — so
`fn-bs-statep`, `fn-bs-authority-fencedp`, `fn-bs-authority-knownp` and
every other conjunct still hold. `fn-bsi-current-init-program-establishes-relation`
(`:204`) remains true. The same argument shows
`(:fsync-file :config *fn-bsi-config-record-name*)` at `:95` is likewise
unconstrained by the relation, and that `writer.lock`/inode 0 is invisible
to it.

Consequence: of the two theorems, **only**
`fn-bsi-current-init-program-establishes-current-image` (`:175`) carries the
lane's new content — it pins the whole store value, so it does fix the
`:config` entry and the six-element `:staging`-only pending list. The
relation theorem is a corollary about the pre-existing root/transactions
surface. `specs/crash-model-v2.md:1917` reads "proves ... final image and
relation ... with concrete failure cuts ... at the config-history directory
fence", which invites the reading that the relation certifies that fence.

*Minimal correction:* (a) restate the K0 row and the handoff so the
config-history/lock claims cite the **image** lemma by name, and say in one
sentence that `fn-bs-store-relation` does not observe `:config`; (b) add the
separating test below. Optionally register `:config` in
`*fn-bs-authority-dirs*` / the relation — that is a larger change and should
be a decision, not a lane edit.

*Evidence needed:* one `assert-event` pair in the test book on the
barrier-free variant program — `fn-bs-store-relation` still `t`, and the
image equation `nil` — plus recertification of the test book.

### F2 — Cut names do not identify crash points, and the new program is not registered with the cut checker. Severity: medium-high.

`fn-bsi-publish-steps` (`:42-57`) is instantiated three times, so the
program's 34 cuts include `"init-file-created"`, `"init-file-written"`,
`"init-file-fenced"`, `"init-file-linked"`, `"init-root-fenced-after-link"`
and `"init-stage-unlinked"` **three times each** — 18 of 34 cuts are
non-unique.

**Concrete failure.** A campaign that names `init-file-linked` cannot
distinguish (i) `config.json` linked, config record and frontier absent,
(ii) config record linked, frontier absent, (iii) frontier linked. Those are
three different recovery inputs. The lane's own tests could not use the
names and addressed cuts positionally instead
(`tests/acl2/byte-store-initializer-tests.lisp:66,76-77`). The comment at
`books/byte-store-programs.lisp:19-22` says new cut names "are faults.at
sites P2's host half must add"; a duplicated name is not an addable site.

I ran the checker that enforces this in both directions:

    $ python3 tools/transcribe_check.py
    syscall-drift: store:initialize() issues [':fsync-dir', ':fsync-file', ':fsync-file',
      ':fsync-file', ':fsync-dir', ':fsync-dir', ':fsync-dir'] and fn-bs-init-program has
      [':mkdir', ':mkdir', ':mkdir', ':fsync-file', ':fsync-file', ':fsync-dir',
       ':fsync-dir', ':fsync-dir']
    transcriptions=10 fidelity-defects=0 missing-host-cuts=0 syscall-drift=5 unmodelled=4

`store:initialize()` is still bound to the **obsolete** `fn-bs-init-program`.
`fn-bsi-current-init-program` is not among the 10 transcriptions, so
`fidelity-defects=0` and `missing-host-cuts=0` say nothing about it, and the
reported drift on `store:initialize()` is still measured against the program
the lane says is no longer the host subject.

*Minimal correction:* give `fn-bsi-publish-steps` a label-prefix argument
(`"init-config-"`, `"init-record-"`, `"init-frontier-"`); step indices are
unchanged, so the existing tests keep their positions. Then point
`tools/transcribe_check.py`'s `store:initialize()` entry at the new program.

*Evidence needed:* recertify both books (unchanged step count), one
`assert-event` that the program's cut names are duplicate-free, and a
`transcribe_check` run showing `store:initialize()` bound to
`fn-bsi-current-init-program`.

### F3 — Three hypotheses of `fn-bsi-fresh-inputp` are inert; no witness separates them. Severity: medium.

`books/byte-store-initializer.lisp:38-40` requires the three stage names
pairwise distinct, and `:21-24` explains them as "the condition the model can
state for the host's O_EXCL allocations".

**Logical counterexample.** Take `config-stage = record-stage =
frontier-stage = ".init"`. `fn-bs-create` refuses only when
`fn-bs-lookup` finds the name, and `fn-bs-lookup` reads the **view**
(`books/byte-store.lisp:498-500`, `fn-bs-apply-op` `:del-entry` at
`:280-285`). The first publication leaves pending
`(:set-entry :staging ".init" 1) (:del-entry :staging ".init")`, whose view
has no `".init"`, so the second `:create` succeeds with inode 2, the link
resolves to 2, and so on. The final pending list is
`((:set-entry :staging ".init" 1) (:del-entry :staging ".init")
  (:set-entry :staging ".init" 2) (:del-entry :staging ".init")
  (:set-entry :staging ".init" 3) (:del-entry :staging ".init"))`
— *exactly* `fn-bsi-current-initial-image`'s pending list under the same
substitution (`:129-134`). Both theorems remain true with the three
distinctness conjuncts deleted. They cannot be given a `must-fail`, which the
assurance rule ("Teeth ship with the theorem") requires of every hypothesis.

The real host risk — a stage name colliding with an entry that already
exists, so `O_EXCL` returns `EEXIST` — is a *different* branch, and it is
already listed as open. The distinctness conjuncts read as if they covered
it; they do not.

*Minimal correction:* delete the three conjuncts and replace the comment at
`:21-24` with one sentence saying the fresh-store precondition makes stage
collision unreachable in this model and that `EEXIST` on a staging create
belongs to the open existing-entry branch.

*Evidence needed:* recertify; the two theorem statements shrink, nothing else
changes.

### F4 — The `must-fail` pair does not separate the two contracts it claims to separate. Severity: medium.

`tests/acl2/byte-store-initializer-tests.lisp:84-85` says the physical input
boundary and the metadata-to-kernel binding "are separate theorem hypotheses,
each with a reachable counterexample". The second `must-fail` (`:97-108`,
frontier encoding 1) does isolate `fn-bs-initial-inputp`. The first
(`:86-96`, `config = nil`) falsifies **both**: `(consp config)`
(`books/byte-store-initializer.lisp:32`) *and* `fn-bs-config-okp nil`
inside `fn-bs-initial-inputp` (`books/byte-store-relation.lisp:12`). It is
the second hypothesis that actually makes the relation fail there, because
`fn-bs-store-relation:574-575` reads `fn-bs-config-okp` of the durable
config content. So there is currently **no** witness that
`fn-bsi-fresh-inputp` contributes anything at all; with F3 removing the
distinctness conjuncts, its only load-bearing content is `fn-bs-namep` on
the three stage names — which is genuinely necessary (`fn-bs-opp:178-182`
requires `fn-bs-namep` on the `:set-entry`/`:del-entry` names that survive in
pending, so a non-string stage breaks `fn-bs-statep` and hence the relation)
and is untested. Note also that `(consp config-record)` (`:33`) cannot
affect the relation at all, since the relation never reads inode 2 (F1).

*Minimal correction:* add one `must-fail` whose inputs satisfy
`fn-bs-initial-inputp` and violate only `fn-bsi-fresh-inputp` — a non-string
stage name, e.g. `7` for `config-stage` — and fix the comment at `:84-85` to
say which hypothesis each witness kills.

*Evidence needed:* recertify the test book with the added `must-fail`.

### F5 — Test-book comment misdescribes the config-fence fault. Severity: low.

`tests/acl2/byte-store-initializer-tests.lisp:73-74`: "The runner stops
there; the explicit config-directory barrier never runs." Step index 42 —
the step the outcome `(fn-bsi-test-outcome-at 42 '(:eio :drop))` targets —
**is** `(:fsync-dir :config)` (`books/byte-store-initializer.lisp:89`), and
`(equal (len drop) 43)` on line 79 confirms the run stopped *at* it, not
before it. The barrier runs, returns `:eio`, and lands the torn selection
`(:drop)` or `(:apply)` per `fn-bs-fsync-dir`'s error arm
(`books/byte-store.lisp:549-564`) — which is precisely *why* both images are
legal (fsyncgate). As written the comment says the opposite and would lead a
reader to classify this as a pre-fence crash. The test itself is correct and
non-degenerate.

*Minimal correction:* one-line comment rewrite. *Evidence needed:* none
beyond recertification.

## Material unresolved assumptions — verified already acknowledged

Each of these is a real limitation of the packet, and each is stated in the
tree. I list them so they are not mistaken for findings.

1. **`O_CREAT` modelled as the fresh-create primitive.** The host's
   `_open_lock` uses `O_CREAT` without `O_EXCL`
   (`tools/run_store.py:911-915`); the model uses `fn-bs-create`.
   Acknowledged at `books/byte-store-initializer.lisp:68-69` and
   `planning/lanes/HANDOFF-w13-storage-initializer.md` ¶6, with the reason
   (fresh-store hypothesis).
2. **Existing store, existing lock, `EEXIST` link, and the read-and-validate
   branches of `_safe_directory` / `_publish_initial_file` are unproved and
   are not treated as retries.** Acknowledged at
   `books/byte-store-initializer.lisp:10-13`, the handoff ¶6, and
   `specs/crash-model-v2.md:1904-1907, 1917`.
3. **Staging cleanup is unfenced; `:staging` is never quiet.** True of the
   host (`_publish_initial_file`'s `finally: os.unlink` has no following
   `fsync_dir(staging)`), stated at `books/byte-store-initializer.lisp:106-109`
   and asserted as `(not (fn-bs-dir-quietp bs :staging))` in the test at `:47`.
4. **This is a source-correspondence claim to the Python calls, not a theorem
   about Python.** Stated in the handoff ¶3.
5. **General K0 remains open**: arbitrary syscall preservation, recovery
   establishment, retained-history composition, existing/retry
   initialization. Handoff ¶6 and `specs/crash-model-v2.md:1917`.
6. **Makefile / registry / ledger registration is not in this lane.**
   Assigned to integration by root. I confirmed it is pre-existing rather
   than lane-introduced: `planning/ledger.json` and `planning/ledger.md` are
   already reported stale at baseline `1501492` (checked against a clean
   `git archive` of that commit in a scratch directory), and
   `books/byte-store-relation`, `books/byte-store-frame`,
   `books/byte-store-program-invariants`, `books/byte-store-initializer` and
   the new test book are all absent from `ACL2_BOOKS` (`Makefile:8-292`).
   Not counted as a finding.

## Housekeeping note (not one of the five)

`fn-bsi-` is a new function prefix and is not registered in
`docs/prefixes.md`; the `fn-bs-` row there (`docs/prefixes.md:18`) also
predates `byte-store-relation`, `byte-store-frame`,
`byte-store-program-invariants` and `byte-store-keystones`. One row edit.

## What I did not do

No certification run was started, locally or on hbox: the archived manifest
already covers the reviewed digests, and every finding above is decided by
reading definitions, not by re-proving. F1–F4 each name the single
`assert-event` / `must-fail` that would settle them; all four fit in the
existing test book and cost one recertification of two books.
