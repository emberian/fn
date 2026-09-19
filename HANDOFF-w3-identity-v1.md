# w3/identity-v1 — the v1 content identity profile, adopted

HEAD: 4bc47c5 (branch `w3/identity-v1`, from `9321344`)

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

## Results

* Certified, one book at a time (`books/store-config`, `books/identity`,
  `books/identity-invariants`, `tests/acl2/identity-tests`): **PENDING** —
  the root coordinator killed the local baseline at load and the remote
  baseline certificates had not landed in this worktree when the lane's tool
  budget ran out. The run is armed and waiting: it blocks until
  `books/*.cert` is populated, then certifies those four roots one at a time
  and runs the Python suites, appending to `build/lane.log` and finishing
  with the line `LANE-DONE`. Harvest that file.
* `python3 -m unittest tests.test_store tests.test_workflow_journal
  tests.test_workflow_live tests.test_receipt_journal tests.test_bp_receive`:
  **PENDING**, in the same armed run (they need the bridge, so they need
  ACL2).
* `python3 tools/ledger.py --write`, `make check`: green (104 Markdown files,
  50 requirements, 18 proof targets, 18 scenario specifications).

## Note for the next lane

The local baseline `make certify` was killed by the root coordinator at load;
the baseline certificates were installed from a remote box at the same
absolute path, and only this lane's four roots were certified locally.
