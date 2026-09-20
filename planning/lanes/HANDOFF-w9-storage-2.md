# Handoff: lane `w9/storage-2` (the K seam, the codec, and the A-* move)

Branch `w9/storage-2` in `build/lanes/w9-storage-2`, from `dev` at `3237e73`.
All ACL2 on hbox (`/tank/fn/lanes/w9-storage-2`, ACL2 8.7 at
`/tank/fn/acl2-8.7/saved_acl2`, every run wrapped in `swarm-build`); nothing
ran on the laptop.

## 1. `books/checkpoint-codec` certifies

Evidence `build/acl2/certify-20260920T190729Z-1095941` on hbox. The book had
not certified end to end since the codecs realignment. Four forms, each fixed
by stating the fact over its own domain with the definition left closed --
the shape every row of the w3 table has:

| # | Form | Fix |
| --- | --- | --- |
| 12b | `fn-cpc-accepted-input-is-canonical`, the FNCP magic | `fn-cpc-read-bytes-reencode` cited by `:use` at `octets` |
| 12c | the same form's 4 MiB payload bound | `fn-cpc-read-{uints,strings}-reencode-len`, `:rule-classes nil`, cited at the two instances; the three encoded segments and the final remainder partition `octets` |
| 13 | `fn-cpc-uint-encoding-len`, the selection guards | `(len (fn-cbor-u16-bytes n)) = 2`, `= 4` for u32, and a five-octet bound on every `fn-cbor-encode-argument` head |
| 14 | `fn-cpc-frame-accepted-is-canonical` | row 12a's vacuity again, on `fn-frame-result-okp`; plus the empty payload, closed by evaluation with `fn-cpc-decode` open in one local fact |

`books/checkpoint-publish`: **`fn-cpp-find-of-append` was false as stated**
and now hypothesises `(fn-cpp-entryp e)`. `fn-cpp-find` returns the matching
element, so a `NIL` element of `GENS` that matches `NAME` is a hit the
recursion reports as a miss; the realignment withdrew the accessor unfold and
made that branch visible. No keystone statement moved.

## 2. `books/byte-store-scan.lisp`, the per-name route

The book exists and carries, as executable definitions, everything §3.1 and
§3.2 of `specs/crash-model-v2.md` proposed: the scan (`fn-bs-scan-store`,
`fn-bs-read-records`, `fn-bs-record-of`, `fn-bs-contiguous-namesp`), the
relation (`fn-bs-store-relation` with the durable-contiguity clause the
previous handoff named), and three seams as `encapsulate`s with local
witnesses -- the frontier codec, `fn-bs-txn-name` (`fn-bs-namep` plus
injectivity; the decimal format stays the host's) and `fn-bs-config-okp`.

The per-name machinery is the lane's new proof content: `fn-bs-names-after`
is to `strip-cars` what `fn-bs-entry-after` is to one entry's value -- a
projection onto ONE directory that ignores every other directory's operations
by construction, so the commutation lemma the per-directory route needed never
arises. `fn-bs-names-outcomes` mirrors `fn-bs-entry-outcomes`.

**Open, with the exact obligation.** The bridge from `fn-bs-apply-entries` to
`fn-bs-names-after` did not close:

```lisp
(defthm fn-bs-apply-entries-names-is-names-after      ; OPEN
  (implies (and dir (fn-bs-dir-tablep dirs) (fn-bs-op-listp ops))
           (equal (strip-cars (cdr (assoc-equal dir (fn-bs-apply-entries dirs ops))))
                  (fn-bs-names-after ops (strip-cars (cdr (assoc-equal dir dirs))) dir))))
```

The induction scheme is right (`fn-bs-apply-entries dirs ops`, which
generalises `dirs`, exactly as `fn-bs-apply-entries-entry-is-entry-after`
does). It exhausts a 2,000,000 and then a 40,000,000 step limit in the
`:set-entry` branch, whose checkpoint is `Subgoal *1/1.4'`: the induction
hypothesis is stated over
`(fn-bs-put-assoc (nth 1 (car ops)) (fn-bs-put-assoc (nth 2 (car ops)) ...) dirs)`
and the conclusion's accumulator must be rewritten into that shape. Three
things were tried and are left in place so the successor need not retry them:
the book-wide `fn-bs-invariants-vocabulary` enable was narrowed to the eight
alist rules the section inducts through (it was the first suspect and was not
the cause); `fn-bs-strip-cars-of-assoc-of-put-assoc` states the projection as
one IF-producing rewrite instead of the two conditional
`fn-bs-assoc-of-put-assoc-{same,other}`, which are disabled at the form; and
`:do-not '(generalize fertilize)`. **Next step: profile it** --
`python3 tools/proof_profile.py books/byte-store-scan
fn-bs-apply-entries-names-is-names-after --host hbox` -- which is what the
brief says to do before a fourth hint, and which this lane did not have the
budget for. The companion suspicion, worth one probe first: state the lemma
with `dirs` replaced by a single directory's entry alist (`fn-bs-apply-entries`
projected once, by hand) so the accumulator is a `strip-cars` of an alist
rather than of an `assoc` of a `put-assoc`.

**K1, K2, K3 remain open**, and their obligation is now much smaller than the
previous handoff left it. What is proved and what is left:

* proved: `fn-bs-crash-select-names-are-an-outcome` (a crash's name list for
  one directory is one of the `fn-bs-names-outcomes` of that directory's
  pending operations), `fn-bs-crash-image-is-quiet`, the three quiet-reader
  facts, `fn-bs-ops-for-name-through-ops-for-dir` (`:rule-classes nil`, it
  loops as a rewrite), `fn-bs-crash-keeps-untouched-entry`,
  `fn-bs-read-records-under-agreement` (two images that agree on the entry
  and the content at every index of a range read the same records there --
  the composition over the name list, with `fn-record-p` and the frame
  decoder closed), `fn-bs-read-records-len`, `-of-one-more`,
  `fn-bs-txn-name-not-in-txn-names`, and the `fn-bs-all-fencedp` vocabulary.
* left for K1: the bridge above, then the four scan clauses -- config entry
  and content, frontier entry and content (both by
  `fn-bs-crash-keeps-untouched-entry` and `fn-bs-crash-keeps-fenced-content`
  through the relation's authority clause), contiguity (by the bridge and
  `fn-bs-txn-names-of-1+`), and no `:fault` (by
  `fn-bs-read-records-under-agreement` against `(fn-bs-durable bs)`).

**A defect in §3.2 the relation found.** §3.2 writes the pending transaction
entry's name as `(fn-bs-txn-name (len (fn-sf-records ks)))`; this book writes
`(fn-bs-txn-name (len (fn-bs-durable-names bs :transactions)))`, because the
namespace clause has to be decidable from the byte store alone. The two forms
are NOT interchangeable for K2: with the book's form, a state whose durable
records are already `(append (fn-sf-records ks) (list rc))` and which also has
a pending link admits an image with `rc` twice, which `fn-sf-crash-imagep`
does not admit. Either the relation carries
`(equal (len (fn-bs-durable-records bs)) (len (fn-sf-records ks)))` whenever
the transaction directory is not quiet, or §3.2's form is restored and the
namespace theorem takes the kernel's record count as an input. **Decide this
before proving K2**; it is the one place where the two models' bookkeeping can
disagree, and it is not a proof convenience.

## 2b. `books/byte-store-scan` does NOT certify -- start here

Under `ld` on hbox with a 40,000,000 step limit every form in the book is
admitted and proved (`build/probe-scan-9.out`). Under `certify-book` two
things differ:

1. `fn-bs-names-outcomes` is rejected for an unused third formal, which `ld`
   accepted. Patched with `(ignorable dir)` in `05baa85`; the better fix is
   to drop `dir` from that function entirely.
2. With that patch, **`fn-bs-crash-select-names-are-an-outcome` fails under
   `certify-book`** although it proves under `ld`. Evidence
   `build/acl2/certify-20260920T192132Z-1110237`,
   `books--byte-store-scan.certify.log:16128`. Check the `(ignorable dir)`
   change first -- it can change the induction ACL2 suggests -- then whether
   the probe's world carried a rule the book's include-closure does not.

**Everything section 2 above calls proved is an `ld` result until this
closes.** An `ld` probe is not a certification.

## 3. The A-* move

`fn-bs-torn-variantp`, `fn-assume-physical-crash` (A-CRASH-IMAGE) and
`fn-assume-crash-tearp` (A-CRYPTO-TRAILER) now live in
`books/assumptions.lisp`, which gains one `include-book "byte-store-invariants"`.
They are the first assumptions in that book whose subjects are the tree's own
predicates rather than abstract values. `books/assumptions` and
`tests/acl2/assumptions-tests` moved after `books/byte-store-invariants` in
the Makefile; `books/relay`, `books/bp-release` and
`books/scheduler-invariants` now carry the byte-store closure.

## 4. `tools/transcribe_check.py` in `make check`

It is §2.3's check, mechanical and needing no ACL2, so it runs in `check`. It
fails on a fidelity defect and reports the rest. On this tree:
`transcriptions=10 fidelity-defects=0 missing-host-cuts=14 syscall-drift=5
unmodelled=4`.

**The 14 missing host cuts are the next packet, not this lane's.** They are
`faults.at` sites in the host, and each new site needs a matching row in
`tests/campaign/cuts.py` and a recovery expectation in `tests/test_store.py`
and `tests/test_checkpoint.py`; adding the markers without them turns a green
campaign into an untested one. Owners:

| Host function | Cuts | Owner |
| --- | --- | --- |
| `tools/run_store.py` `advance_frontier()` | `frontier-created`, `frontier-written` | store host |
| `tools/run_store.py` `publish()` | `record-created`, `record-written`, `record-stage-unlinked` | store host |
| `tools/run_store.py` `initialize()` | `init-root-created`, `init-transactions-created`, `init-staging-created`, five `init-barrier` | store host |
| `tools/checkpoint.py` `publish()` | `checkpoint:candidate-stage-unlinked` | checkpoint host |
