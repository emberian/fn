# w3/identity-v1 — the v1 content identity profile, adopted

HEAD: the merge of `dev` (ca66782) into `w3/identity-v1` (1c7a3e6).

## What changed

`books/identity.lisp` no longer derives `"sha256:"+hex` and
`"archive:"+hex`. That derivation is deleted, not kept beside the new one.
The two derivations are now the v1 profile of `specs/encoding.md` exactly as
that spec wrote it:

    subject-v1    = SHA-256("fn/subject/v1" || 0x00 || uint32-be(len(payload))
                            || payload)
    obligation-v1 = SHA-256("fn/obligation/v1" || 0x00 || uint32-be(len(msgid))
                            || msgid || uint32-be(len(subject)) || subject)

The length prefixes are `fn-cbor-u32-bytes`, the same four big-endian octets
the frame grammar already uses.

## The new rendering

An identity is the triple (label octets, algorithm id, digest octets),
rendered canonically by `fn-id-render`:

    identity = label || 0x00 || version-octet || algorithm-octet || digest

version 1, algorithm 1 (SHA-256). A subject identity is 48 octets
(13 + 3 + 32), an obligation identity 51 (16 + 3 + 32). The kind is carried
inside the encoded identity; there is no hex label prefix any more, and the
algorithm identifier is in the container, so D09 agility changes the algorithm
octet without changing the meaning of an identity already written.

The canonical identity is **octets**. `fn-id-text` (`fn-id-hex-octets` of the
whole identity, label included) is the only rendering into a string, and the
host uses it at exactly three places, which is where a string is unavoidable:

* the store record's metadata fields (`subject`, `archive-obligation-id`),
* the workflow journal's JSON records,
* the NNTP header value.

`fn-id-from-text` is its inverse. `fn-id-text` is 96 hex octets for a subject
and 102 for an obligation; the record metadata cap is 256.

The digest stays the host-supplied constrained `fn-frame-digest`. For a
subject the bridge is handed only `fn-id-subject-prefix` (label, separator,
uint32-be length) and appends the payload itself, so a 32 KiB article never
crosses the bridge — the same idiom as `fn-frame-inbound-prefix`.

## The separation theorem, verbatim

```lisp
(defthm fn-id-subject-and-obligation-preimages-differ
  (not (equal (fn-id-subject-preimage payload)
              (fn-id-obligation-preimage msgid subject)))
  :hints (("Goal" :in-theory (enable fn-id-subject-preimage
                                     fn-id-subject-prefix
                                     fn-id-obligation-preimage))))
```

No hypotheses: for every payload and every (msgid, subject) pair the two
preimages are different octet strings, because the domain labels differ at
their fourth octet (115 `s` against 111 `o`). Two kinds of identity cannot
share a preimage by construction.

Length prefixing is proved by reading the lengths back out of the preimages:
`fn-id-subject-preimage-length-is-recoverable`,
`fn-id-obligation-preimage-msgid-length-is-recoverable` and
`fn-id-obligation-preimage-subject-length-is-recoverable`. A field boundary is
a decoded number, not a separator octet a field might itself contain.

The hex-projection invertibility theorems are kept and extended to the new
rendering: `fn-id-unhex-of-hex-octets`, `fn-id-hex-octets-of-unhex`,
`fn-id-hex-octets-injective`, plus `fn-id-from-text-of-text`,
`fn-id-text-of-from-text` and `fn-id-text-injective`.

## Store format

`books/store-config.lisp` now owns `*fn-store-format-id*` =
`fn-store-experiment-5` (it previously lived only in
`tools/run_store.py`'s `DEFAULT_CONFIG`). `host/store-host.lisp` exposes
`(fn-store-format-id)`, `frame_bridge.FrameSession.format_id()` reads it, and
`run_store.group_codes` refuses a store whose configuration names another
format — the same shape as the existing `group_table` check. A store holding
pre-v1 identities is format 4 and is now refused at open by its configuration
rather than misread.

`specs/encoding.md`'s section is retitled "Content identity: the v1 profile,
adopted" and rewritten; `specs/store-experiment.md` records the format bump
and that the id is ACL2-owned.

## Fixtures changed

* `tests/test_workflow_live.py` — the two re-derived strings are gone; it
  calls `run_store.metadata(b"<a@example.invalid>", b"article")`. The now
  unused `hashlib` import is dropped.
* `tests/test_bp_receive.py` — `test_bad_subject_stays_staged` no longer
  corrupts a `b'sha256:'` prefix (there is none). It asks the bridge for the
  subject the receiver will derive and breaks one hex digit of it.
* `tests/bp-dtn7/fn_sender_lab.py` — already went through
  `run_store.metadata`; no change was needed.

Deliberately **not** changed: the `"sha256:…"` / `"archive:…"` strings in
`tests/test_store.py`, `tests/test_store_corruption.py`,
`tests/test_store_node_host.py`, `tests/test_store_fault_matrix.py`,
`tests/test_workflow_journal.py` and the ACL2 exchange/bp tests. Those are
opaque record labels, never derived and never compared against a derivation;
rewriting them through the bridge would invent a dependency that does not
exist, and several are pinned by frozen evidence JSON. They now read as a
stale echo of the old profile and are worth a rename pass in a later lane.

## Brought onto the realigned tree (2026-09-19)

`git merge dev` over the deputies’ realignment. Four conflicts:

* `books/identity.lisp` — the deputy’s export theory, with the lane’s names
  in it. `fn-id-subject-prefix`, `fn-id-subject-preimage`, `fn-id-render`,
  `fn-id-text` and `fn-id-from-text` join `fn-id-definitions` and the
  `(:d …)` withdrawal; nothing but the executable functions leaves enabled.
* `books/identity-invariants.lisp` — the lane’s `(include-book
  "cbor-invariants")` together with the deputy’s local enable of the frame
  and CBOR vocabularies, including `(:d fn-frame-split)` and
  `(:d fn-frame-u64-bytes)`, which the codecs board entry requires of every
  book above the frame split.
* `tests/acl2/identity-tests.lisp` — the deputy’s concrete `assert-event`
  tooth for the odd-length hex projection replaces the lane’s general negated
  `must-fail`; `std/testing/must-fail` is no longer included.
* `planning/ledger.{json,md}` — generated; regenerated by `tools/ledger.py`.

Every keystone statement on both sides is unchanged, including
`fn-id-subject-and-obligation-preimages-differ` and the three length-recovery
theorems.

Two proofs needed work against the realigned base, recorded in the books:

* `fn-id-labelledp`’s guard obligations are propositional
  (`(not (cddr tail))` from `(not (consp (cddr tail)))`), and
  `fn-frame-split-suffix-true-listp` is a rewrite rule, so it never reaches
  the context. A **local** forward-chaining corollary of it, triggered on the
  split term, closes them; type-set carries the fact down the `cdr`s. No
  `true-listp` backchaining rule leaves the book.
* `fn-id-obligation-preimage-subject-length-is-recoverable` reached its cut by
  `:use` and left the arithmetic library to find the rest by induction, which
  looped (`GENERALIZE-CLAUSE` three times on one subgoal, under the `mod`
  rules). The two steps it needs — skipping the four octets of a closed
  length prefix, and skipping a field whose own length was just read back —
  are now local rewrite rules and the `:use` is gone.

## Results

Certified in this worktree, one root at a time, ACL2 8.7 (SBCL,
`/opt/homebrew/Cellar/acl2/8.7_6`), `ACL2_BOOK_HASH_ALISTP=NIL`, after
`make certs-install`:

| root | s | evidence |
| --- | --- | --- |
| `books/store-config` | 0 | `build/acl2/certify-20260919T201203Z-46624` |
| `books/identity` | 8 | `build/acl2/certify-20260919T201452Z-61017` |
| `books/identity-invariants` | 16 | `build/acl2/certify-20260919T215417Z-495` |
| `tests/acl2/identity-tests` | 1 | `build/acl2/certify-20260919T215433Z-1391` |

Nothing else is in the closure: `books/identity` is included only by
`books/identity-invariants` (and by `host/store-host.lisp`, which is not a
certified root), and `books/store-config` only by `host/store-host.lisp`.
`python3 tools/certify_books.py --affected-by books/identity --dry-run`
returns nothing beyond those, so there is no convergence-gate remainder from
this lane.

`python3 tools/ledger.py --write` and `make check`: green (142 Markdown
files, 50 requirements, 18 proof targets, 18 scenario specifications;
2812 theorems, 945 guards verified, 26 SUSPECT, 62 lint warnings, none of
them in the identity books).

`python3 -m unittest tests.test_store tests.test_workflow_journal
tests.test_workflow_live tests.test_receipt_journal tests.test_bp_receive -v`:
**56 tests, OK, 160.0 s**, against the merged tree with 89 certificates
installed from the cache. `test_bad_subject_stays_staged`
(`tests/test_bp_receive.py:41`) is the one that had to agree: it asks the
bridge for the subject the receiver will derive and breaks one hex digit of
it, so it passes only if the v1 identity the sender writes and the one the
receiver recomputes are the same octets. No bp book was certified by this
lane and none had to be.

## Note for the next lane

The merge base is `dev` at **ca66782**; `dev` has since moved to 4ab9472
(`dep/bp`), so the convergence gate merges again. Nothing in this lane touches
a book outside the identity closure, so that merge should be textual.

Two certificate-cache traps cost this lane real time and are worth knowing.
`make certs-install` will *keep* a stale local `.cert` ("kept identical local
N") rather than replace it, so a worktree that was certified before the
realignment keeps certificates whose book-hash no longer matches the source
and every include fails with a `book-hash` mismatch naming a length that is
not your file's. Delete the stale `.cert` files for the closure and re-install.
And the deputies' certificates were in their own worktrees, not the cache:
`python3 tools/certs.py publish --root build/lanes/dep-<cluster>` for each
deputy filled it (codecs 22, core 14, nntp 10, substrate 5, store 21, bp 17),
after which `make certs-install` put 89 into this worktree.
