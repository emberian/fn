# LANEDUMP — lane `twins-into-acl2` (packet C1-13, "bytes into ACL2")

Worktree `/Users/ember/dev/fn/build/lanes/twins-into-acl2`, branch
`lane/twins-into-acl2`, branched from `0bd0b5c`. Written at the session's
usage cut-off; the packet is **not complete**. `HANDOFF.md` in this worktree
holds the finished prose (sections 1 to 7) and should be read together with
this file; where the two disagree, this file is the later word, because
`HANDOFF.md` was written assuming certification would finish.

---

## 1. The packet as I understood it

Kill the twins table in §4 of `planning/review-2026-09-18-independent.md`:
every decision that Python and ACL2 both compute moves to ACL2, and Python
becomes a byte pump.

1. **Framing.** FNST (`run_store.py:134-155`), FNWF/FNBI
   (`workflow_journal.py:112-175, 459-476`), FNRJ (`receipt_journal.py:25-70`)
   are Python-only grammars. Define one frame grammar in `books/frame.lisp`
   (magic, version, kind, bounded length, payload, trailer), prove round trip
   both directions, accepted-input canonicality, and bounds before allocation.
   Measure SHA-256 in ACL2; under two seconds for 32 KiB means ACL2 owns the
   trailer, otherwise a constrained `fn-frame-digest` recorded as A-CRYPTO.
   Python's encoders become bridge calls.
2. **Content identity.** `run_store.py:771-775` derives subject and archive
   obligation; ACL2 only compares. Move the derivation to
   `books/identity.lisp`, byte-exactly, and record the missing domain
   separation plus a v1 profile in `specs/encoding.md`.
3. **One Message-ID bound.** Three exist; `books/article-fields.lisp`'s
   `fn-af-message-idp` becomes the single owner.
4. **Group table.** One shared source; Python obtains it by bridge.
5. **Charge policy.** `fn-charge-for-payload`, positive and monotone.
6. Makefile roots, `docs/prefixes.md`, `specs/encoding.md`,
   `specs/store-experiment.md`.

Gate: `make check`; full `make certify` green including the new roots;
`python3 -m unittest tests.test_store tests.test_store_lifecycle
tests.test_workflow_journal tests.test_receipt_journal
tests.test_workflow_boundary -v`.

Standard: both codec directions proved, non-minimal/malformed forms rejected
before allocation, teeth via `must-fail` or negated `assert-event`s, no
`skip-proofs`/`defaxiom`/`defttag`, no Python implementation left beside the
ACL2 one.

---

## 2. DONE

### 2.1 `books/store-config.lisp` — CERTIFIES

The group table and both directions of the name/code mapping, with `fn-store-`
names so `host/store-node-host.lisp` and `host/store-host.lisp` keep working
unchanged. Certified green (last clean run
`build/acl2/certify-20260919T054704Z-7185`).

Verbatim keystones:

```lisp
(defthm fn-store-group-code-of-name
  (implies (fn-store-group-of-name name)
           (equal (fn-store-group-code (fn-store-group-of-name name)) name)))

(defthm fn-store-group-name-of-code
  (implies (fn-store-group-code code)
           (equal (fn-store-group-of-name (fn-store-group-code code)) code)))

(defthm fn-store-codes-from-groups-inverts
  (implies (and (true-listp names)
                (not (equal (fn-store-codes-from-groups names) :bad)))
           (equal (fn-store-groups-from-codes
                   (fn-store-codes-from-groups names))
                  names)))
```

The third is the one the boundary composes: `group_codes` sends names,
`host/store-node-host.lisp:47,142` turns the codes back into names.

### 2.2 `books/frame.lisp` — CERTIFIES

One grammar for all four frames:

```
FRAME := MAGIC(4) VERSION(1) KIND(1) LENGTH(4, big-endian)
         PAYLOAD(LENGTH) TRAILER(32)
```

plus a field grammar for journal payloads (`:text` = u16 length 1..512 then
UTF-8 octets validated by the wildmat RFC 3629 decoder; `:blob` = u32 length
1..131072; `:nat` = eight octets big-endian; `(:enum . keys)` = one octet,
the 1-based position in a duplicate-free keyword list), the A-CRYPTO
`encapsulate`, and guard-verified entry points. Certified green
(`build/acl2/certify-20260919T055812Z-12693`); every `verify-guards` in it
passes.

The A-CRYPTO seam, verbatim:

```lisp
(encapsulate
  (((fn-frame-digest *) => *))
  (local (defun fn-frame-digest (octets)
           (declare (ignore octets))
           '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)))
  (defthm fn-frame-digest-octet-listp
    (fn-cbor-octet-listp (fn-frame-digest octets)))
  (defthm fn-frame-digest-length
    (equal (len (fn-frame-digest octets)) *fn-frame-trailer-octets*)))
```

Host entry points defined and guard verified in this book:
`fn-frame-encode`, `fn-frame-decode`, `fn-frame-store-encode/-decode/
-protected`, `fn-frame-workflow-encode/-decode/-protected`,
`fn-frame-receipt-encode/-decode/-protected`, `fn-frame-inbound-prefix`,
`fn-frame-inbound-open`, plus `fn-frame-seal` and `fn-frame-open` as the
specification pair over the constrained digest.

### 2.3 `host/store-host.lisp` — rewritten, NOT yet loaded against ACL2

- includes `../books/replay`, `../books/store-config`, `../books/identity`,
  `../books/article-fields` (so it no longer depends on the caller having
  included `replay` first);
- `fn-store-msgid-octetsp` is now exactly `(fn-af-message-idp xs)` — the
  single Message-ID owner (packet item 3, DONE in source);
- the group table and its two mappings are gone from here (packet item 4);
- new marshalling wrappers, all thin: `fn-store-frame-constants`,
  `fn-store-frame-{store,workflow,receipt}-{protected,encode,decode}`,
  `fn-store-frame-{workflow,receipt}-{schema,kinds}`,
  `fn-store-frame-inbound-{prefix,open}`, `fn-store-subject-id`,
  `fn-store-obligation-preimage`, `fn-store-obligation-id`,
  `fn-store-charge`, `fn-store-msgid-validp`, `fn-store-post-boundary`,
  `fn-store-group-names`, `fn-store-group-table-id`, `fn-store-group-codes`,
  `fn-store-octet-lists->strings`.

**Never executed.** `(ld "host/store-host.lisp")` has not been run in this
session, so nothing has type-checked these wrappers. First thing to do.

### 2.4 Python — written, never executed against ACL2

- `tools/frame_bridge.py` (new): the one place that talks to ACL2 about
  frames, identity, bounds, groups and charge. Its S-expression reader was
  unit-tested standalone (see §5); the ACL2 side was not.
- `tools/run_store.py`: `MAGIC` is now `b"FNST\x01\x01"` (magic + version +
  kind) so `len(MAGIC) + 4` still equals the header size at the two sites this
  lane does not own (`durable_records`, `tests/test_store_corruption.py:155`,
  `tests/test_store_process_crash.py:130`); `DEFAULT_CONFIG` format is
  `fn-store-experiment-3` and carries `group_table` instead of `groups`;
  `frame`, `unframe`, `metadata`, `group_codes`, `conservative_charge`,
  `validate_post_boundary` are bridge calls; unused `hmac` import removed.
- `tools/workflow_journal.py`: `KINDS`, `KIND_NAMES`, `FIELDS`, `STATUSES`,
  `PHASES`, `RESULTS`, `_text`, `_nat` deleted; `encode_record`,
  `decode_record`, `encode_inbound`, `decode_inbound` are bridge calls; unused
  `struct` import removed.
- `tools/receipt_journal.py`: `KINDS`, `NAMES`, `FIELDS`, `OUTCOMES`, `_s`,
  `_b` deleted; `encode_receiver_record`, `decode_receiver_record` are bridge
  calls; unused `struct`/`hashlib` imports removed.

### 2.5 Specifications and registry — DONE

- `specs/encoding.md`: the frame grammar is a chosen layout with its proved
  properties named; A-CRYPTO recorded; the non-domain-separated identity
  preimage stated as a defect with a concrete v1 profile.
- `specs/store-experiment.md`: new "Framing: what is proved and what is
  assumed" section; group/Message-ID/charge ownership recorded.
- `docs/prefixes.md`: rows for `fn-frame-`, `fn-id-`/`fn-charge-`, and
  `fn-store-` as used by `books/store-config`.
- `Makefile`: seven new roots added after `tests/acl2/article-fields-tests`,
  in dependency order: `books/store-config`, `books/frame`,
  `books/frame-invariants`, `tests/acl2/frame-tests`, `books/identity`,
  `books/identity-invariants`, `tests/acl2/identity-tests`.

---

## 3. IN PROGRESS — exact state

### 3.1 `books/frame-invariants.lisp` — 22 of ~35 events admitted, then stalls

This is the blocker. A `certify-book` run and then an interactive
`(ld "books/frame-invariants.lisp")` both reach the same place.

**Live log:** `build/ld-frame-invariants.log` in this worktree (an
interactive `ld`, killed at the handoff; it is the readable one — the
`certify_books.py` runs buffer their output and only write it at the end).

**Admitted, in order, all green:** `fn-frame-u16-bytes-true-listp`,
`fn-frame-u32-bytes-true-listp`, `fn-frame-u16-bytes-of-u16-from`,
`fn-frame-u32-bytes-of-u32-from`, `fn-frame-u16-from-bounded`,
`fn-frame-u32-from-is-integerp`, `fn-frame-u32-from-is-natural`,
`fn-frame-u32-from-bounded`, `fn-frame-u64-from-of-u64-bytes`,
`fn-frame-mod-halves` (local), `fn-frame-floor-halves` (local),
`fn-frame-u64-halves-natural` (local),
`fn-frame-u64-bytes-of-u64-from-halves` (local),
`fn-frame-u64-from-is-natural`, `fn-frame-u64-bytes-of-u64-from`,
`fn-frame-item-of-enum-index`, `fn-frame-enum-index-zero-when-not-member`,
`fn-frame-item-is-member`, `fn-frame-enum-index-of-item`.

**Stalls on the next form, `fn-frame-field-parse-of-octets`**
(`books/frame-invariants.lisp:181`). It does not error; it diverges into a
deep nested induction. Tail of `build/ld-frame-invariants.log` at kill time:

```
Subgoal *1/3.7.2.3.3.1.39.9.9.9.9.9.9.9.9.9.14'4'
*1.69 (Subgoal *1/3.7.2.3.3.1.39.9.9.9.9.9.9.9.9.9.14'4') is pushed
for proof by induction.
Subgoal *1/3.7.2.3.3.1.39.9.9.9.9.9.9.9.9.9.13
```

The statement:

```lisp
(defthm fn-frame-field-parse-of-octets
  (implies (and (fn-frame-specp spec)
                (fn-frame-field-okp spec value)
                (fn-cbor-octet-listp rest))
           (equal (fn-frame-field-parse
                   spec (append (fn-frame-field-octets spec value) rest))
                  (fn-frame-parse-ok value rest)))
  :hints (("Goal" :in-theory (enable fn-frame-field-parse fn-frame-field-octets
                                     fn-frame-field-okp fn-frame-parse-counted
                                     fn-frame-textp fn-frame-blobp
                                     fn-frame-natp fn-frame-specp))))
```

**Diagnosis I am confident of, not yet applied.** The `:in-theory (enable ...)`
list is the problem: enabling `fn-frame-textp` and `fn-frame-blobp` drags in
`fn-cbor-at-mostp` and `fn-wildmat-decode-aux`, and enabling
`fn-frame-field-octets` lets `fn-cbor-u16-bytes`/`fn-cbor-u32-bytes` reopen
into floor/mod, so ACL2 inducts on the payload octets. Every other proof in
`books/frame.lisp` was fixed by the opposite move. The fix to try first, in
order:

1. Split the theorem into four, one per `spec` shape (`:text`, `:blob`,
   `:nat`, enum), each with `:do-not-induct t` and
   `:in-theory (disable fn-cbor-u16-bytes fn-cbor-u32-bytes fn-frame-u64-bytes
   fn-frame-split floor mod)`, using `fn-frame-split-of-append`,
   `fn-frame-u16-bytes-len`, `fn-frame-u32-bytes-len`,
   `fn-frame-u64-bytes-len`, `fn-frame-u16-from-u16-bytes`,
   `fn-frame-u32-from-u32-bytes` and `fn-frame-u64-from-of-u64-bytes` as
   rewrite rules rather than opening anything.
2. Keep `fn-frame-textp`/`fn-frame-blobp` **disabled** and add two small
   lemmas instead: `(implies (fn-frame-textp v) (and (consp v) (<= (len v)
   512) (fn-cbor-octet-listp v)))` and the `fn-frame-blobp` analogue,
   `:rule-classes (:rewrite :linear)` as appropriate. `fn-frame-textp` must
   stay closed because it calls the wildmat decoder.
3. Re-assemble `fn-frame-field-parse-of-octets` from the four cases with
   `:in-theory (enable fn-frame-specp)` and nothing else.

The same treatment is very likely needed for the forms after it, which have
never been attempted: `fn-frame-field-octets-of-parse`,
`fn-frame-field-parse-value-okp`, `fn-frame-fields-parse-aux-of-octets`,
`fn-frame-fields-parse-of-octets`, `fn-frame-fields-parse-aux-round-trip`,
`fn-frame-fields-octets-of-parse`, `fn-frame-header-octets`,
`fn-frame-head-fields-of-header`, `fn-frame-decode-of-encode`,
`fn-frame-encode-of-decode`, `fn-frame-decode-refuses-oversize-before-
validation`, `fn-frame-decode-bounds-its-payload`,
`fn-frame-decode-trailer-is-the-supplied-digest`,
`fn-frame-digestp-of-fn-frame-digest`, `fn-frame-protected-prefix-of-encode`,
`fn-frame-encode-is-seal`, `fn-frame-decode-is-open`,
`fn-frame-open-of-seal`, `fn-frame-store-decode-of-encode`,
`fn-frame-workflow-decode-of-encode`, `fn-frame-receipt-decode-of-encode`,
`fn-frame-store-encode-is-protected-plus-digest`,
`fn-frame-workflow-encode-is-protected-plus-digest`,
`fn-frame-receipt-encode-is-protected-plus-digest`,
`fn-frame-inbound-open-of-prefix`.

**These are proposed statements, not theorems.** Nothing in
`books/frame-invariants.lisp` beyond the 22 listed above has been admitted by
ACL2. `HANDOFF.md` §3 quotes several of them as keystones; that section is
premature and must not be cited until they certify.

### 3.1a What the repair session (2026-09-19, post-merge) actually found

`books/frame-invariants.lisp` now carries the §3.1 fix in source: shape
lemmas `fn-frame-textp-is-octets/-is-consp/-len-bound` and the `fn-frame-blobp`
analogues, a local `fn-frame-append-assoc`, a local
`fn-frame-len-positive-when-consp`, four rewrite rules that close the parse
result (`fn-frame-parse-okp-of-parse-ok`, `-of-parse-error`,
`fn-frame-parse-value-of-parse-ok`, `fn-frame-parse-rest-of-parse-ok`), a
`(local (in-theory (disable fn-cbor-u16-bytes fn-cbor-u32-bytes
fn-frame-u64-bytes fn-frame-textp fn-frame-blobp)))` and a second disable of
the parse-result constructor, accessors and `fn-frame-item`, then
`fn-frame-field-parse-of-octets` split into `-text`, `-blob`, `-nat`, `-enum`
and re-assembled. Everything up to and including `fn-frame-blobp-len-bound`
is admitted (logs `build/ld-frame-invariants-{2,3,4,5}.log`).

Three things were learned, each paid for by a run:

1. **`associativity-of-append` is not a rule name in this installation.** A
   hint naming it fails with `ACL2 Error [Translate] ... A theory expression
   could not be evaluated` (log 3). The local `fn-frame-append-assoc` above
   replaces it; without right-association `fn-frame-split-of-append` cannot
   fire, because the outer append's first argument is the whole field, not
   the two-octet length prefix. Log 2's `Subgoal 3''` shows exactly that:
   `(FN-FRAME-SPLIT 2 (APPEND (APPEND (FN-CBOR-U16-BYTES (LEN VALUE)) VALUE)
   REST))` left unreduced.
2. **`:do-not-induct t` does not bound the cost.** Runs 4 and 5 sat at 98%
   CPU for more than ten minutes inside the simplifier on
   `fn-frame-field-parse-of-octets-text` with no induction message, and
   `certify_books.py`-style buffering means the log ends mid-form, so the
   failing subgoal is never written. Closing the parse-result accessors
   (the if-explosion hypothesis) did not change it.
3. **The remaining suspect is the text case specifically.** `-blob`, `-nat`
   and `-enum` have never been reached. Next thing to try is to prove the
   counted tail once over a variable length --
   `(implies (and (true-listp value) (consp value) (natp maximum)
   (<= (len value) maximum)) (equal (fn-frame-parse-counted (append value rest)
   (len value) maximum) (fn-frame-parse-ok value rest)))` -- disable
   `fn-frame-parse-counted` afterwards, and let the `-text` case do only the
   split-2 step. Run it as an `ld` of a *scratch* file holding just that one
   lemma, not as an `ld` of the whole book: each full-book run costs four
   minutes of admitted preamble before it reaches the form under test.

### 3.1b Resolved (2026-09-19, later session): the stall was never in `-text`

`books/frame-invariants.lisp`, `books/identity.lisp`,
`books/identity-invariants.lisp`, `tests/acl2/frame-tests.lisp` and
`tests/acl2/identity-tests.lisp` all certify (evidence under
`build/acl2/certify-20260919T0829*` and `-T0830*`; `frame-invariants` in
13 s). No definition in `books/frame.lisp` changed. What was actually wrong:

1. The cost was a rewrite cascade on every `(consp x)` and
   `(fn-cbor-octet-listp x)` term, not any one theorem. `books/frame` exports
   `fn-frame-len-{2,4,8}-conses` and `fn-frame-not-consp-when-len-zero`
   (rewrite rules on `(consp x)` that backchain into `len`), and the §3.1a
   shape lemmas `fn-frame-textp-is-consp`/`-is-octets`/`-len-bound` were
   `:rewrite`/`:linear` rules whose hypothesis opens `fn-frame-textp`, which
   unrolls `fn-cbor-at-mostp x 512` to its literal bound. With those live,
   plain `(equal (append (append a b) c) (append a (append b c)))` took
   108 s and `fn-id-hex-octets-are-octets` in `identity-invariants` took
   619 s (163M prover steps). Measured with `accumulated-persistence`; the
   `certify_books.py` buffering had hidden which form was grinding.
2. Fix: the four frame rules and the two value predicates are disabled
   locally right after the u64 lemmas; the shape lemmas are
   `:forward-chaining` only and the two proofs that need them `:use` them;
   every list/splitter helper is proved under `minimal-theory` plus named
   runes; `fn-frame-parse-counted-of-append` is proved once over a variable
   length; the field cases are straight-line rewrites. `fn-frame-encode-is-seal`
   and `fn-frame-decode-is-open` are exported *disabled* (each loops against
   the definition it inverts; the `must-fail` in `frame-tests` hit the
   rewriter call-depth limit with them enabled).
3. `fn-frame-decode-trailer-is-the-supplied-digest` is proved through a
   local lemma stated on a separate variable `xs` with the encoding as an
   equation, because ACL2 cannot substitute a term for `octets` when `octets`
   occurs inside that term.
4. `fn-id-hex-octets-of-unhex` had its own `Waterfall-loop` with `floor`,
   `mod` and the digit functions all open; it now uses nibble bounds and
   `floor`/`mod` of `16a+b` as rewrite lemmas, statement unchanged.

### 3.2 Never attempted

- `books/identity.lisp`, `books/identity-invariants.lisp` — written, never
  submitted to ACL2. Guard risks already anticipated and pre-fixed:
  `(local (include-book "arithmetic/top" :dir :system))` added for the
  `floor`/`mod` in `fn-id-hex-octets`; `fn-id-labelledp` reordered so the
  octet check precedes the split.
- `tests/acl2/frame-tests.lisp`, `tests/acl2/identity-tests.lisp` — written,
  never submitted. They include `std/testing/must-fail` (`:dir :system`,
  certified in this installation) and `assert-event`s that require the
  functions to execute.
- `host/store-host.lisp` has never been `ld`-ed.
- No Python test has been run against the new bridge.

---

## 4. NOT STARTED

- Anything in the gate beyond `make check` (see §6).
- A guard-audit test book for `fn-frame-*` / `fn-id-*` in the style of
  `tests/acl2/*-guards-tests.lisp`.
- `tools/certify_books.py`'s `DEFAULT_BOOKS` list still lacks the seven new
  roots (only the Makefile was updated; `make certify` passes roots
  explicitly, so this is cosmetic until someone runs the script bare).

---

## 5. Design decisions, and why

**Direct octet layout, not CBOR items.** Two structural reasons, both in the
book header: the frame's job is to bound the payload before anything
allocates, so building it on the CBOR decoder would make that bound depend on
the parser the frame exists to protect, and the store payload is itself a CBOR
record; and a fixed-width big-endian field has exactly one encoding of each
value, so canonicality is structural rather than a rejected alternative form.

**One layout for all four frames, with FNWF and FNRJ byte-identical.** The
Python FNWF/FNRJ frames were already `MAGIC(4) SCHEMA(1) KIND(1) LEN(4)
PAYLOAD TRAILER(32)`; the grammar was chosen to match them exactly, verified
by generating golden vectors from the pre-migration Python encoders
(`tests/acl2/frame-tests.lisp`, eight full records, trailer included). FNST
gains the kind octet it lacked — one octet longer, so `DEFAULT_CONFIG`
format moves to `fn-store-experiment-3` and an old store is refused loudly by
`_load_config` rather than misread. FNBI moves its BID length into a payload
text field — two octets longer; inbound frames are transient.

**The SHA-256 decision. Do not redo this measurement.** Measured once:

```
$ ACL2_CUSTOMIZATION=NONE acl2 <<EOF
(ld "/opt/homebrew/Cellar/acl2/8.7_6/libexec/books/kestrel/crypto/sha-2/package.lsp")
(ld "/opt/homebrew/Cellar/acl2/8.7_6/libexec/books/kestrel/crypto/padding/package.lsp")
(include-book "kestrel/crypto/sha-2/sha-256" :dir :system)
(defconst *probe* (make-list 32768 :initial-element 0))
(time$ (len (sha2::sha-256-bytes *probe*)))
EOF
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 0.06 seconds realtime, 0.06 seconds runtime
; (37,273,680 bytes allocated).
32
```

0.06 s for 32 KiB — under the packet's two-second threshold. **I still took
the constrained-function branch**, for two reasons the threshold could not
see:

1. The book is uncertified and so is its entire dependency chain. A plain
   `(include-book "kestrel/crypto/sha-2/sha-256" :dir :system)` fails with
   `There is no certificate on file for .../sha-256.lisp`; the measurement
   above only runs because the two portcullis `package.lsp` files are `ld`-ed
   first and the book is then included *uncertified*, which `certify-book`
   refuses. `kestrel/{bv,bv-lists,arithmetic-light,lists-light,
   typed-lists-light,crypto/padding,crypto/sha-2}` hold 465 `.lisp` files and
   16 `.cert` files in this installation, so making it available means
   certifying that chain into a Homebrew-managed directory shared by ten
   lanes.
2. The cost does not stay at 32 KiB: 0.06 s / 37 MB there extrapolates to
   about 7.7 s / 4.7 GB at the 4 MiB inbound bundle bound, and every octet
   would also cross the decimal-octet bridge twice.

The upgrade path costs no theorem change: a certified guard-verified SHA-256
can be attached to `fn-frame-digest` with `defattach` (no trust tag needed),
and every theorem keeps its statement while A-CRYPTO becomes discharged
rather than assumed. That is the right shape for a later packet.

**Python keeps no grammar, only slice arithmetic, and that is checked.**
`run_store.MAGIC`, `TRAILER_BYTES` and the journal record caps survive because
code this lane does not own (`durable_records`, two corruption tests,
`WorkflowJournal.open`, `ReceiptJournal.open`, `receipt_bridge`) uses them for
sizing. `frame_bridge.FrameSession._check_host_constants` compares each
against `fn-store-frame-constants` at session open, so a divergence is a
startup failure rather than a second grammar.

**A second ACL2 process, deliberately, with a one-line exit.** None of the
Python functions this lane owns (`frame`, `unframe`, `metadata`,
`group_codes`, `conservative_charge`, `validate_post_boundary`,
`encode_record`, `decode_record`, `encode_inbound`, `decode_inbound`,
`encode_receiver_record`, `decode_receiver_record`) is called with a live
`Acl2Store` in scope, and editing their call sites is outside the lane's
ownership (the packet reserves those functions for `host-repair`). I rejected
monkey-patching `Acl2Store.__init__` as a debt hole. `frame_bridge.session()`
therefore opens its own `Acl2Store` lazily, and `frame_bridge.adopt(store)`
exists so that one line in `Acl2Store.__init__` collapses it back to one
process. That line is the first proposal in §8.

**`books/store-config.lisp`, not `host/store-config.lisp`.** The packet named
the host path. `tools/certify_books.py`'s `BOOK_NAME` regex only accepts roots
under `books/` or `tests/acl2/`, so a file under `host/` can never be
certified, and therefore nothing in `books/` could include it. Putting the
table in a certified book is also what makes the two directions of the mapping
provable instead of merely shared.

**Enumerations are 1-based positions in a duplicate-free keyword list**, not a
second code table — so code injectivity follows from `no-duplicatesp-equal`
rather than from a hand-maintained inverse. Python's `STATUSES`, `PHASES`,
`RESULTS`, `OUTCOMES` and `KINDS` were all already 1-based enumerations, so
the bytes match.

**Field names are published by ACL2, not kept by Python.**
`fn-store-frame-{workflow,receipt}-schema` returns the field-name octets and
the field specification together, so `frame_bridge` labels a decoded record
without holding an ordered field list. The boundary convention for the
single-member enum (`(:enum :authorized)`) is that it spells Python's `True`.

**UTF-8 has one owner.** `fn-frame-textp` calls
`fn-wildmat-decode-aux` from `books/wildmat.lisp` (RFC 3629, table-exact,
guard verified) rather than defining a second table. `books/frame.lisp`
supplies only the 512-octet bound in front of it.

**`fn-frame-item`, a total positional accessor.** Every result record is read
through it, so no guard obligation anywhere depends on the shape of a value
that failed to parse. This removed a whole class of guard failures.

**Decoded lengths are `nfix`-ed at the point of use.** `fn-frame-decode`,
`fn-frame-inbound-open` and `fn-frame-field-parse` wrap `fn-cbor-u16-from` /
`fn-cbor-u32-from` in `nfix`, which makes every downstream `<`, `+` and split
guard trivial without a chain of type lemmas.

**`(local (in-theory (disable fn-frame-split fn-cbor-u16-bytes
fn-cbor-u32-bytes fn-frame-u64-bytes)))` after the shape lemmas.** Opening
these on a literal length unrolls them and defeats the lemmas; this single
line is what made `books/frame.lisp`'s guard proofs go through, and the
same discipline is what `fn-frame-field-parse-of-octets` still needs.

---

## 6. Gate commands and last results

| Command | Last result |
| --- | --- |
| `make check` | **not run this session** |
| baseline `make certify` (before any edit) | **failed**, 112 of 113 roots green; `books/article-properties` hit the runner's 600 s per-book timeout under ten-lane load and five dependents then failed for a missing certificate. Log: `build/certify-baseline.log`, evidence `build/acl2/certify-20260919T033149Z-68355`. Re-run with `FN_ACL2_TIMEOUT_SECONDS=1800`; the repair run I started was killed twice by session events and never completed, so `books/article-properties.cert` is still absent. |
| `FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py books/store-config` | **passed** (`build/acl2/certify-20260919T054704Z-7185`) |
| `FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py books/frame` | **passed** (`build/acl2/certify-20260919T055812Z-12693`) |
| `... books/frame-invariants` | **fails**: stalls on `fn-frame-field-parse-of-octets`, see §3.1. Readable log: `build/ld-frame-invariants.log` |
| `... books/identity books/identity-invariants` | **not run** |
| `... tests/acl2/frame-tests tests/acl2/identity-tests` | **not run** |
| full `make certify` with the new roots | **not run** |
| `python3 -m unittest tests.test_store tests.test_store_lifecycle tests.test_workflow_journal tests.test_receipt_journal tests.test_workflow_boundary -v` | **not run** |

One thing was verified standalone: `tools/frame_bridge.py`'s S-expression
reader, against the shapes ACL2 prints:

```
(1 2 3) -> [1, 2, 3]
NIL -> []
T -> True
(:OK :TRANSPORT ((119 111) (97) 2 :DELIVERED)) -> ['ok', 'transport', [[119, 111], [97], 2, 'delivered']]
(:ERROR :INTEGRITY) -> ['error', 'integrity']
(:OK ((108 111) (112 48)) (:TEXT :NAT (:ENUM :ORDINARY :RECOVERY))) -> ['ok', [[108, 111], [112, 48]], ['text', 'nat', ['enum', 'ordinary', 'recovery']]]
```

and the three edited modules import cleanly with
`MAGIC = b'FNST\x01\x01'`, `format = fn-store-experiment-3`,
`group_table = fn-store-groups-1`.

### Operational notes for whoever continues

- Set `FN_ACL2_TIMEOUT_SECONDS=1800` on every certification: ten lanes share
  this box and `books/article-properties` alone exceeds the 600 s default.
- `setsid` does not exist on this macOS install. Start long runs with the
  harness's background option, or `nohup … &` followed by `disown`; a bare
  `&` inside a tool shell is killed when the turn ends, and a *background
  wait loop* will kill the job it is waiting on (that is how the repair run
  died — twice).
- `certify_books.py` buffers ACL2's output and writes the `.certify.log` only
  at the end, so it tells you nothing while a book is grinding. For iteration,
  run `acl2 < <(echo '(ld "books/X.lisp" :ld-error-action :return
  :ld-error-triples t)')` and tail the redirect instead.

---

## 7. Known defects

- **`books/frame-invariants.lisp` does not certify**, so `books/identity`,
  `books/identity-invariants` and both test books are untested, the Makefile
  root list names books that do not build, and `make certify` is red. This is
  the whole remaining risk.
- **`HANDOFF.md` §3 overstates.** It presents the frame and identity keystones
  as proved. Only the 22 events listed in §3.1 plus everything in
  `books/frame.lisp` and `books/store-config.lisp` are proved. Fix that
  section or delete it before anyone cites it.
- **`fn-frame-inbound-prefix` is two octets stricter than Python was.**
  `MAX_INBOUND_BUNDLE` allows exactly 4 MiB; the ACL2 payload cap of 4 MiB
  must also cover the two-octet BID length, so a full 4 MiB bundle is now
  refused. Nothing in the tree produces one.
- **Two ACL2 processes per store command** until the `adopt` line lands.
- **The evidence label is still a host constant** (`b"unsigned-legacy-v0"` in
  `metadata`); ACL2 only compares it. That is D9 and belongs to C1-11.
- **The identity preimage is not domain separated.** Deliberate: existing lab
  stores, `tests/test_workflow_live.py:23-24` and
  `tests/bp-dtn7/fn_sender_lab.py:67` depend on the exact bytes. The v1
  profile to adopt is written out in `specs/encoding.md`.
- **No fixture or test loses its Message-ID.** Every Message-ID in `tests/`,
  `tools/`, `host/` and `docs/` was checked against `fn-af-message-idp`'s
  grammar by inspection. The only strings that fail it — `<a..b@example>`,
  `<a@ex..ample>`, `<a@[x\y]>`, `<a@[]>x` — appear solely as negative vectors
  in `tests/acl2/article-fields-tests.lisp`, where rejection is the assertion.
  The bound tightens from the host's 512 octets to RFC 5536's 250; the longest
  Message-ID in the tree is 25 octets. **This was not machine-checked**; a
  cheap confirmation is to run each through `fn-store-msgid-validp` once
  `host/store-host.lisp` loads.
- **`books/article-properties.cert` is missing** in this worktree from the
  interrupted baseline; five dependent books will fail until it is rebuilt.

---

## 8. Proposals for files this lane does not own

| File and line | Now | Replacement |
| --- | --- | --- |
| `tools/run_store.py` `Acl2Store.__init__`, after the three `ld` calls | nothing | `frame_bridge.adopt(self)` — one line; removes the second ACL2 process from every store, ingress and receive command |
| `host/bp-ingress-host.lisp:8-10` | `*fn-bpi-host-group-map*` restates `fn.letters`/`fn.test` as octet/name pairs | `(include-book "../books/store-config")` and build the map from `*fn-store-groups*` |
| `host/reader-host.lisp:5` | `(defconst *fn-reader-groups* '("fn.letters"))` | `(include-book "../books/store-config")` and `(defconst *fn-reader-groups* (list (fn-store-group-code 0)))` |
| `tools/workflow_bridge.py:8-18` | `_FIXED` and `_ORDER` restate the record kinds and field order | `frame_bridge.session().schema("workflow", kind)` returns both |
| `tools/receipt_bridge.py:5-9` | `ORDER` restates the receiver field order | `frame_bridge.session().schema("receipt", kind)` |
| `tools/certify_books.py` `DEFAULT_BOOKS` | lacks the seven new roots | add them in Makefile order, or generate the list from the Makefile |
| `tools/run_store.py:158-173` `read_prompt` default `timeout=20` | fixed 20 s per call | `host/store-host.lisp` now `include-book`s four books in one `ld`; if that call ever exceeds 20 s the bridge will fail at startup. Unmeasured — measure it first. |

---

## 9. Dirty and untracked files at handoff

Modified (tracked):

```
Makefile
docs/prefixes.md
host/store-host.lisp
specs/encoding.md
specs/store-experiment.md
tools/receipt_journal.py
tools/run_store.py
tools/workflow_journal.py
```

Untracked (new):

```
HANDOFF.md
LANEDUMP-twins-into-acl2.md
books/frame-invariants.lisp
books/frame.lisp
books/identity-invariants.lisp
books/identity.lisp
books/store-config.lisp
tests/acl2/frame-tests.lisp
tests/acl2/identity-tests.lisp
tools/frame_bridge.py
```

Not committed, and not part of the lane's deliverable: `build/` (certification
evidence, `build/certify-baseline.log`, `build/certify-repair.log`,
`build/ld-frame-invariants.log`) and the regenerated `.cert`/`.port` files
under `books/` and `tests/acl2/`.
