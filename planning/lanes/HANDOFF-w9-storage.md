# Handoff: lane `w9/storage` (crash model v2, the K seam and the campaign)

Branch `w9/storage` in `build/lanes/w9-storage`, from `dev` at `52eb0db`.
Proof work on **hbox** (`/tank/fn/lanes/w9-storage`, ACL2 8.7 at
`/tank/fn/acl2-8.7/saved_acl2`), moved there mid-lane on the coordinator's
instruction: persvati was at load 9 with five queued runners and zero ACL2
processes, hbox at load 0.3.

## Certified

`FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 python3 tools/certify_books.py --jobs 3
books/byte-store books/byte-store-invariants books/byte-store-programs`:
**all three pass**, evidence `build/acl2/certify-20260920T182231Z-1039695`
on hbox. Everything else below that says "probe" is an `ld` of the book's
source against certified dependencies, which is not a certification.

## What landed

### 1. `fn-bs-splice-composition`, and the model defect it found

The obligation recorded against the open `fn-bs-view-is-an-admissible-image`
was the splice-composition lemma. It is proved:

```lisp
(defthm fn-bs-splice-composition
  (implies (and (natp offset) (true-listp a))
           (equal (fn-bs-splice (fn-bs-splice old offset a) (+ offset (len a)) b)
                  (fn-bs-splice old offset (append a b)))))
```

with the nothing-lost choice list `fn-bs-view-choices` and its admissibility
(`fn-bs-view-choices-are-choices`), which is the witness the view theorem's
`fn-bs-crash-imagep-suff` needs.

**The view theorem was false as stated.** A pending `(:write ino offset NIL)`
has `fn-bs-unit-count` 0, so a crash tears it into no pieces at all, while
`fn-bs-apply-op` splices it and zero-extends the inode when the offset is
past the end. The view of `(:byte-store 4 ((0)) NIL ((:write 0 5 NIL)) 1)`
is five zero octets and no crash image of that state has them. `write(2)`
of zero octets changes nothing on POSIX and `fn-bs-write` issues no
operation for it, so `fn-bs-statep` now carries `fn-bs-writes-nonemptyp`,
with the eight preservation facts beside the `fn-bs-writes-knownp` ones.

`fn-bs-view-is-an-admissible-image` is **still open**, not weakened, with a
smaller obligation stated at its place in `byte-store-invariants` and in
`specs/crash-model-v2.md` §7: two index facts (A1, A2) relating the i-th
unit piece to the octets pieces 0..i-1 covered. The induction on `i` is
right and its step is the composition lemma; it exhausts a 2,000,000 step
limit re-deriving A1 and A2 inside every branch of `fn-bs-tear-write`. State
them as `:linear` rules over a named `fn-bs-piece-start` and open the tear
by `:expand`.

### 2. The journals, the inbox and the checkpoint machine as programs

`books/byte-store-programs.lisp` now transcribes P-JOURNAL (both halves),
P-INBOX with its reconciliation branch, and both P-CHECKPOINT programs, with
the host's own cut names and the same ground assertions the store programs
carry (step-list well-formedness, D1 to D3, the run completes, D5 and K0 at
every step, the final name carries the exact frame in a quiet directory).

`tools/transcribe_check.py` is §2.3's check, mechanical and in both
directions. On this tree: **`fidelity-defects=0`**, `missing-host-cuts=15`
(exactly P2's host half: `frontier-created`, `frontier-written`,
`record-created`, `record-written`, `record-stage-unlinked` and the eight
`init-*` names), `syscall-drift=5` (advisory; each answered in the book) and
`unmodelled=4` (the composite receiver and three transport-delete
boundaries, each named with its reason). The advisory found one real
omission and the ground assertion refused the wrong fix: the host's
`os.unlink` after `checkpoint:select`'s replace is the `except` arm, and a
model program that took it stops at `:enoent`.

### 3. The campaign against the byte model

`tests/campaign/model_images.py` imports a case directory as a byte-store
image, asks ACL2 for the model state `bs_k` at a cut through `fn-bs-run`
over the program constant, enumerates the whole-or-lost choices of its
pending list, and returns the record counts the model admits there.
`campaign.py --model-images` fails a case whose recovered record count is
outside that set, reporting `bs_k`'s pending list. See
`planning/evidence/campaign-model-images-2026-09-20.md` for the run.

This is the *namespace envelope*, not §5.1's exact check: it does not
compare the recovered record octets, because that needs `fn-bs-scan-store`,
and it enumerates choices instead of deciding membership, because
`fn-bs-image-admissiblep` and its `-iff-crash-imagep` are still open.
Both limits are written into the module's docstring.

### 4. The checkpoint codec's recorded open theorem

`fn-cpc-decode-tree-of-encoding` (row 8 of `HANDOFF-w3-checkpoint.md`) is
**proved**, and three forms behind it with it: `fn-cpc-decode-tree-accepted`,
`(verify-guards fn-cpc-decode)` and `fn-cpc-checkpointp-reassembles`. The
handoff's table carries rows 8 to 12 with the cause, the fix and where the
failure moved. Row 12a closes the two spurious subgoal families of
`fn-cpc-accepted-input-is-canonical` -- each reader's remainder by
forward chaining, and a vacuous pair of hypotheses (`(not (parse-okp X))`
beside `(equal (car X) :ok)`) that the closed recognizer hid. Row 12b is
the new frontier: that form's real obligation, the FNCP magic prefix
rebuilt in front of the remainder, where `fn-cpc-read-bytes-reencode`
should be cited by `:use` at the instance.
**The book is not certified**; these are `ld` probes.

The lesson, beside the one that handoff already records: the scoped
`(enable fn-cbor-octetp)` could not have worked, because the head's
octet-ness is not something the proof has to decide. Under the branch
hypothesis it is refuted. Every one of the four fixes has that shape -- the
fact stated over the value's own domain lemma, with the definition left
closed.

## Not done, with what the successor needs

* **K1, K2, K3** (`books/byte-store-scan.lisp`) were not written. The lane
  spent its probe budget on the two seams above. The decomposition it
  worked out is in `specs/crash-model-v2.md` §7's K1 row: the crux is one
  lemma, "with at most one pending entry operation on a directory, the
  image's entries for it are the durable ones or their `put-assoc`",
  from (S1) `assoc-equal` of `fn-bs-apply-entries` restricted to
  `fn-bs-ops-for-dir`, and (S2) the crash selection of a directory's
  operations is a subsequence of them. `fn-bs-txn-name` should be a
  constrained function (`fn-bs-namep` plus injectivity): the decimal format
  is the host's and ACL2 owning it is its own packet.
* **The A-CRASH-IMAGE and A-CRYPTO-TRAILER move into
  `books/assumptions.lisp`** was not made. It is not free: that book's own
  header says it "deliberately includes nothing. It is the bottom of the
  tree", and these two constraints are about `fn-bs-crash-imagep` and
  `fn-bs-torn-variantp`, so the move puts `byte-store-invariants` into the
  closure of `books/relay`, `books/bp-release` and
  `books/scheduler-invariants`, which include `assumptions` today. There is
  no cycle (nothing in the byte-store closure includes `assumptions`), so
  the move is available; it should be made deliberately, with those three
  books recertified, not as a side effect.
* **Articles by reference** (the reader's real ceiling) was not started. The
  pinned snapshot still carries article octets by value.
* **Proposal 5** (the bound-candidate test for `fn-sf-history-recoverablep`)
  was not started.

## What ran

* hbox, `ld` probes: `build/probe/d1.out` (byte-store + invariants),
  `d2.out` (checkpoint-codec), `d3.out` (byte-store + invariants +
  programs).
* hbox, certification: the three byte-store roots, evidence above.
* hbox, `python3 tests/campaign/campaign.py --quick --scenario cross-post
  --model-images`: see the evidence file.
* laptop: `python3 tools/transcribe_check.py`, `python3 tools/ledger.py
  --write`, `make check` (green: 188 Markdown files, 56 requirements, 26
  proof targets, 19 scenario specifications; 234 ledger lint warnings).
