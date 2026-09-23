# Certificate cache: composing a closure from several origins, 2026-09-23

Status: measured on persvati with real ACL2, implemented in `tools/certs.py`
and `tools/farm.py`, and used for one real plain-roots farm run. Nothing here
certifies a book. What changed is which cached pairs a run may install.

## The problem

`certs.py install-set` installed a closure only when one origin/toolchain
group held a complete set for the requested roots. `farm.py`'s preflight also
passed `--require-origin <remote root>` for every plain-roots run. A fresh
remote root has no entries of its own, so every lane's plain-roots submit was
refused. Each lane then ran `--closure` and recertified 60 to 310 books from
`sha256` up. The rule rested on one reading: an ACL2 certificate's
post-alist names each sub-book by absolute path, so a parent from origin X
over a child from origin Y "conflict[s] even when both source closures are
byte-identical".

## What ACL2 8.7 does (source and documentation)

The ACL2 was `/home/ember/fn-gates/toolchains/w25/acl2-literal` (ACL2 8.7
built 2026-09-19, SBCL 2.6.8), toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`, with the
fn environment `ACL2_BOOK_HASH_ALISTP=NIL ACL2_CUSTOMIZATION=NONE`.

- `other-events.lisp`, `include-book-alist-subsetp`: "We check that the first
  is a subset of the second, in the sense that the (familiar-name
  cert-annotations . book-hash) parts of the first are all among those of the
  second. We ignore the full names and the user names because they may change
  as the book or connected book directory moves around." This one check runs
  at include time (`include-book-certified-p`, on the certificate's
  post-alist), on the portcullis pre-alist, and between certify-book's Step 2
  and Step 3.
- With `ACL2_BOOK_HASH_ALISTP=NIL` the book-hash is a checksum of the forms
  read, not a write date. (`:doc book-hash`) Comments do not change it.
  fn's closure key hashes bytes, so it is stricter.
- `include-book-certification-tuple` records the certificate's own
  full-book-name (`cert-full-book-name`) in the world's `include-book-alist`,
  so the world names the origin's paths. It never opens them.
- The one path-sensitive check, `unexpected-from-book-name` in
  `chk-raise-portcullis`, applies only when the certificate names the book
  by a sysfile (`(:K . "relpath")`), which happens only under a
  `project-dir-alist` entry (below).
- `tilde-*-book-hash-phrase1` builds the error text after the subset check
  has already failed. For each required entry whose full-book-name has no
  exact match it prints "its certificate requires the book X, but that book
  has not been included although the book Y -- which has the same familiar
  name ... -- has been included", whether or not that entry's hash matched.

That last point explains the 2026-09-21 failures in
[cert-origin-coherence-2026-09-21.md](cert-origin-coherence-2026-09-21.md).
Their `served` logs list 41 such entries under one error. That error is
printed only when some `(familiar-name annotations . book-hash)` differed.
The mismatch was in content or annotations, and the absolute paths were
only how ACL2 worded it. The logs do not say which entry differed. The
likely source is the legacy per-book `install`, which then mixed pairs from
the laptop and three boxes with no toolchain identity. That repair's
toolchain identity and closure-key checks already rule this out.

## The experiment

The experiment ran in trees under `/home/ember/fn-gates/tool-cache-*` on
persvati, each an rsync of this worktree at `dev` `1554e2cd`. The chain is
`books/wildmat-work` → `books/wildmat` → `books/cbor`. The driver was
`(include-book "books/wildmat-work")` under `strace -f -e trace=openat`. It
printed the world's `include-book-alist` and `include-book-alist-all`.

**Real cache, two snapshot origins.** `wildmat-work`'s pair came from the
`/home/ember/fn-gates/w31-treewide` entry, and `wildmat`'s and `cbor`'s from
`/home/ember/fn-gates/dev-head`, all at dev's closure keys. The include
succeeded. The only warning was `[Compiled file]`, because the cache does not
carry `.fasl` files. The files opened were all in the target tree:
`tool-cache-exp/books/{wildmat-work,wildmat,cbor}.{lisp,cert}`. The world
names `w31-treewide/books/wildmat-work.lisp`,
`dev-head/books/wildmat.lisp` and `dev-head/books/cbor.lisp`.

For the controlled cases, `tool-cache-oA` certified all three books and
`tool-cache-oB` certified `cbor` and `wildmat`. The target `tool-cache-t2`
took `wildmat-work` from oA and the two children from oB.

1. **Both origins on disk, unmodified.** Accepted with no warning other than
   `[Compiled file]`. Only t2's files were opened. The world names
   `oA/.../wildmat-work.lisp`, `oB/.../wildmat.lisp` and `oB/.../cbor.lisp`.
2. **Child's origin removed** (`mv tool-cache-oB tool-cache-oB.gone`). The
   transcript matched case 1 exactly: accepted, and the same files opened.
3. **Origins modified.** oB's `wildmat.lisp` gained
   `(defthm fn-cache-probe-bogus (equal 1 2))`, its `cbor.lisp` gained a
   line, its `wildmat.cert` was overwritten with `garbage`, and oA's
   `wildmat.lisp` was edited. The transcript again matched case 1.
4. **Control: the target's own child is changed.** An event
   `(defun fn-cache-probe (x) x)` was appended to t2's `cbor.lisp`. ACL2
   refused: `Warning [Uncertified] ... The certificate for ".../tool-cache-t2/
   books/cbor.lisp" lists the book-hash of that book as 2138256274. But its
   book-hash is now computed to be 106748854`, followed by the "same familiar
   name" messages for both parents. The `include-book-alist` entries carry no
   hash. Appending only a comment was *not* refused, because the checksum is
   over the forms read.
5. **Extending a mixed closure** (the reason the preflight required the
   remote origin). A third origin `tool-cache-oC` certified
   `wildmat-utf8-invariants`. t2 took `wildmat-work` from oA,
   `wildmat-utf8-invariants` from oC, and `wildmat` and `cbor` from oB. A new
   book `books/fn-cache-probe.lisp` (includes both, plus `wildmat`, plus one
   `defthm`) was then certified at t2. It certified with no warning other
   than `[Subsume]` on the probe theorem. The second include of `wildmat` was
   redundant. Next oA, oB and oC were all removed, and in a fresh session
   `(include-book "books/fn-cache-probe")` was accepted. Only t2's files were
   opened.

## Relocatable certificates (`project-dir-alist`), measured too

`:doc project-dir-alist` says: "Let S be a set of books certified with a
given project-dir-alist ... assume that the absolute pathname of every book
in S has a prefix among the directories in that project-dir-alist. Then all
books in S, along with their certificate files, can be moved." The `:dir`
keyword in `include-book` is **not** required. `:doc sysfile` says such a
full-book-name is written to the certificate as `(:K . "relpath")`. The
projects file is named by `ACL2_PROJECTS`, and a relative directory in it is
read relative to the file itself.

Test: an `acl2-projects` file containing `:FN "./"` at each tree's root.
`tool-cache-oP` certified the chain with `ACL2_PROJECTS=<oP>/acl2-projects`,
the pairs were copied to `tool-cache-t3`, and oP was removed.

- With `ACL2_PROJECTS=<t3>/acl2-projects` the include was accepted, and the
  world names `(:FN . "books/wildmat-work.lisp")` and so on. No foreign path
  appears anywhere.
- Without `ACL2_PROJECTS`: `HARD ACL2 ERROR [Missing project] ... The
  project-dir-alist needs an entry for the keyword :FN`. The include failed.
- With a certificate at the wrong path (`wildmat.cert` copied onto `cbor`):
  `Warning [Uncertified] ... The book being included, .../cbor.lisp, is not
  in the location expected ... .../wildmat.lisp`. This is the one check
  plain absolute names do not get.

**Could fn use it?** No book changes. There are 746 `(include-book "x")`
forms with a relative path and 128 `:dir :system` forms under `books/` and
`tests/acl2/`, and all of them stay as they are. `host/native/build.lisp`'s
`ld` forms and `include-book "books/..."` forms are relative to the cbd, and
`tools/proof_repl.py`'s `set-cbd` is unaffected. The edit list:

1. Add a committed `acl2-projects` file at the repository root containing
   `:FN "./"`.
2. Set `ACL2_PROJECTS=<root>/acl2-projects` everywhere fn sets
   `ACL2_BOOK_HASH_ALISTP=NIL` today: `tools/acl2`, `tools/certify_books.py`,
   `tools/proof_artifacts.py`, `tools/run_reader.py`, `tools/stx.py`,
   `tools/run_simulator.py`, `tools/host_check.py`, `tools/auth_secret.py`,
   `tools/run_store.py`, `tools/proof_profile.py`, the four sites in
   `tools/live_service.py` (including its systemd `Environment=` line), and
   `tools/build_native_host.sh`.
3. Add it to `tools/acl2_toolchain.py`'s proof environment, so certificates
   written with it get a different compatibility identity.
4. Record it in `certify_books.py`'s manifest environment.

Cost: two to three hours of mechanical edits and tests. After that, one
treewide `--closure` run of `dev` on each box, because step 3 turns every
existing entry into a miss. What it buys: a certificate names no machine
path at all, and ACL2's wrong-location check becomes active. It would also
let the origin bookkeeping in `certs.py` (`origin_root`, `origin_kind`,
`foreign-local`, the live-worktree rule) be deleted instead of maintained.
It does *not* buy reuse this change lacks: case 5 already shows that a mixed
closure installs and extends. Any launch site that misses the variable fails
loudly (`Missing project`), not silently. The saved native image carries the
alist into `save-exec`. That is not measured here.

This change does not take that route. The brief made it conditional on ACL2
refusing mixed origins, and ACL2 does not refuse them.

## What was implemented

`tools/certs.py`:
- `artifact_sets` still builds one candidate per origin and toolchain. For
  each toolchain it also builds one **composed** candidate
  (`origin_root == "composed"`), taking the newest usable entry for each
  book by `published_at`. A usable entry is this tree's own, one whose
  origin is not on this machine, or one from a `gate` or `run` snapshot. It
  is never from a live worktree still on disk. The order is: complete
  first, then the widest coverage, then a single origin before a
  composition of equal coverage. So a closure that one origin covers
  installs exactly as before.
- `install_artifact_set` reports `origins` (origin → books). The identity
  line ends in `; origins /a=n,/b=m`, and the origin field reads `composed`
  for a composition. `require_origin` keeps the single-origin rule.
- `choose_entry` (legacy `install` and `status`) takes the newest usable
  entry after this tree's own. `status` also prints the origins its usable
  pairs come from.
- The module docstring states the new rule and cites this record.

`tools/farm.py`:
- A plain-roots or `--affected-by` preflight no longer passes
  `--require-origin`. `--closure` still passes it with `--purge-on-miss`,
  because that is root's explicit recertification plan.
- `parse_installed` reads the `origins` field into the run record's
  `cache_install`. `status` adds a `from-cache` column
  (`installed+kept/origins`) from the local run record.
- The refusal message now says what is missing, and no longer tells a lane
  to run `--closure`.

Tests (`python3 -m unittest tests.test_certs tests.test_farm`: 72 tests, OK):
- one complete origin: `test_one_complete_origin_is_installed_as_a_unit`
  (unchanged) and `test_a_single_complete_origin_is_preferred_to_a_composition`
- two snapshot origins composing: `test_two_snapshot_origins_compose_one_set`
  and `test_each_pair_keeps_the_bytes_its_own_origin_wrote` (rewritten from
  the 2026-09-21 regression that asserted refusal)
- newest per book: `test_the_newest_pair_is_taken_for_each_book`
- a live origin on disk refused: `test_a_live_worktree_still_on_disk_is_not_composed`
- a snapshot origin whose directory is gone:
  `test_a_snapshot_origin_whose_directory_is_gone_still_installs`. It
  installs, per experiment case 2.
- `test_require_origin_keeps_the_single_origin_rule` and
  `test_a_composition_never_mixes_toolchains`
- farm: the preflight has no `--require-origin` for plain roots and keeps it
  for `--closure`; a composed identity line is parsed and recorded; the
  older line still parses.

`python3 -m unittest tests.test_proof_artifacts tests.test_certify_runner`
(35 tests) also passed, because `proof_artifacts.acquire` iterates the same
candidates.

## Measured effect

`python3 tools/farm.py submit persvati books/peer-inbound
books/peer-inbound-invariants tests/acl2/peer-inbound-tests --jobs 4
--timeout-seconds 1800 --remote-root /home/ember/fn-gates/tool-cache --acl2
/home/ember/fn-gates/toolchains/w25/acl2-literal --cache
/home/ember/fn-certcache`, with no `--closure`, from this worktree at `dev`
`1554e2cd` plus this change.

- Run `run-20260923T012303Z-f54b`, certification run
  `certify-20260923T012310Z-2197907` (manifest committed under
  `planning/evidence/manifests/`).
- Preflight: `installed 74, kept 0, missing 0, removed 0; origins
  /home/ember/fn-gates/dev-head=74`. This was a single origin. The 74
  dependencies of these roots are all current in the stopped treewide run's
  tree, so the old code's only obstacle here was `--require-origin`, not
  the one-group rule.
- ACL2 started and certified the 3 requested books and nothing else, in
  8.7 s of certification wall time (3.4 s, 2.6 s and 2.4 s per book). Status
  `passed`. All three pairs were published to the box cache as `run`
  entries.

Composition across the whole tree, as measured by `artifact_sets` with each
book as a plain root (`--dependencies-only`) against the box cache at the
same moment and the same toolchain:

- 338 of 409 books with dependencies have a complete single-origin set.
- 1 has a complete set only by composition.
- 70 have neither. The books missing for them are ones no run has certified
  at `dev`'s current digests: `store-node-traces`, `store-node-resolution`,
  `store-observed`, `peer-inbound` (before this run), `nntp-auth`, `served`,
  `owner`, and so on.

Composition cannot supply a book nobody certified. Right now the old rule's
real cost was `--require-origin`. Composition matters when the digests a lane
branched at are split across runs, which is the situation described tonight.

## What is not shown

- The experiment covers one three-book chain and one diamond (case 5) on one
  host and toolchain. It does not include `.pcert` handling (`--pcert` mode),
  and it does not include a native image built from a composed closure.
- The live-worktree exclusion is kept as policy. The experiment found no
  mechanism that needs it.
- The cache ships no `.fasl`, so every installed book loads its source
  (`[Compiled file]` warning). That is unchanged by this work.
- `planning/how-we-work.md`'s root recipe calls `proof_artifacts.py roots
  --profile all`, but that option does not exist (the choices are
  `default` and `dtn`).
- The 2026-09-21 mismatch is explained by ACL2's message logic. Which entry
  actually differed was not recovered.
