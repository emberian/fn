# HANDOFF - w3/index-cache (packet C1-09)

HEAD at hand-off: 980099e
Branched from dev at 9321344.

## What this lane did

Adopted the certified PRF-010 index (`books/index.lisp`) as a generation-bound
cache for the NNTP number projection, without changing the served path in
`books/nntp.lisp`.

New files:

- `books/nntp-index.lisp` - index-backed twins of the six `books/nntp.lisp`
  number enumerations, each proved equal to the fold it replaces, plus the
  generation-bound cache (`fn-nntp-index-cache-open`, `-freshp`, `-query`).
- `tests/acl2/nntp-index-tests.lisp` - witness, per-hypothesis separating
  witnesses, bounded `must-fail`s, and the stale/forged-generation cases.
- `host/index-host.lisp` - `:program` adapter: `fn-index-host-observe`
  (configuration read once per selection), `fn-index-host-open` (build at an
  observed generation), `fn-index-host-query` (the served call; it calls
  `fn-nntp-index-cache-query` and nothing else), `fn-index-host-fold` (oracle
  and measurement baseline only, not a served path).
- `tests/test_index_cache.py` - four tests over a real recovered store.
- `tests/index_measure.py` - the 128-article maximum-profile measurement.

Changed: `Makefile` (two roots after `tests/acl2/nntp-teeth-tests`),
`docs/prefixes.md` (two rows), `specs/index.md` (host-adoption section and the
measurement table), `planning/ledger.json` / `planning/ledger.md` (generated).

## The equality theorems, verbatim

```lisp
(defthm fn-nntp-index-numbers-of-query-range
  (implies (and (fn-article-listp configured articles)
                (stringp group)
                (natp low)
                (natp high))
           (equal (fn-nntp-index-numbers
                   (fn-index-query-range (fn-index-build articles) group low high))
                  (fn-nntp-available-numbers group low high articles))))

(defthm fn-nntp-index-group-count-equals-fold
  (implies (and (fn-article-listp configured articles)
                (stringp group))
           (equal (fn-nntp-index-group-count (fn-index-build articles) group)
                  (fn-nntp-group-count group articles))))

(defthm fn-nntp-index-group-low-equals-fold
  (implies (and (fn-article-listp configured articles)
                (stringp group))
           (equal (fn-nntp-index-group-low (fn-index-build articles) group)
                  (fn-nntp-group-low group articles))))

(defthm fn-nntp-index-group-high-equals-fold
  (implies (and (fn-article-listp configured articles)
                (stringp group))
           (equal (fn-nntp-index-group-high (fn-index-build articles) group)
                  (fn-nntp-group-high group articles))))

(defthm fn-nntp-index-group-next-number-equals-fold
  (implies (and (fn-article-listp configured articles)
                (stringp group))
           (equal (fn-nntp-index-group-next-number
                   (fn-index-build articles) group current)
                  (fn-nntp-group-next-number group current articles))))

(defthm fn-nntp-index-group-last-number-equals-fold
  (implies (and (fn-article-listp configured articles)
                (stringp group))
           (equal (fn-nntp-index-group-last-number
                   (fn-index-build articles) group current)
                  (fn-nntp-group-last-number group current articles))))

(defthm fn-nntp-index-group-range-numbers-equals-fold
  (implies (and (fn-article-listp configured articles)
                (stringp group)
                (natp low)
                (natp high))
           (equal (fn-nntp-index-group-range-numbers
                   (fn-index-build articles) group low high)
                  (fn-nntp-group-range-numbers group low high articles))))

(defthm fn-nntp-index-cache-query-refuses-other-generation
  (implies (not (equal (fn-nntp-index-cache-generation cache) generation))
           (equal (fn-nntp-index-cache-query
                   cache generation digest kind group low high current)
                  (list :stale))))

(defthm fn-nntp-index-cache-query-refuses-other-configuration
  (implies (not (equal (fn-nntp-index-cache-digest cache) digest))
           (equal (fn-nntp-index-cache-query
                   cache generation digest kind group low high current)
                  (list :stale))))

(defthm fn-nntp-index-cache-open-answers-group
  (implies (and (fn-statep archive)
                (natp generation)
                (stringp group))
           (and (equal (fn-nntp-index-cache-query
                        (fn-nntp-index-cache-open generation archive)
                        generation (fn-nntp-index-config-digest archive)
                        :count group low high current)
                       (cons :ok (fn-nntp-group-count
                                  group (fn-state-articles archive))))
                (equal (fn-nntp-index-cache-query
                        (fn-nntp-index-cache-open generation archive)
                        generation (fn-nntp-index-config-digest archive)
                        :low group low high current)
                       (cons :ok (fn-nntp-group-low
                                  group (fn-state-articles archive))))
                (equal (fn-nntp-index-cache-query
                        (fn-nntp-index-cache-open generation archive)
                        generation (fn-nntp-index-config-digest archive)
                        :high group low high current)
                       (cons :ok (fn-nntp-group-high
                                  group (fn-state-articles archive)))))))

(defthm fn-nntp-index-cache-open-answers-cursor
  (implies (and (fn-statep archive)
                (natp generation)
                (stringp group))
           (and (equal (fn-nntp-index-cache-query
                        (fn-nntp-index-cache-open generation archive)
                        generation (fn-nntp-index-config-digest archive)
                        :next group low high current)
                       (cons :ok (fn-nntp-group-next-number
                                  group current (fn-state-articles archive))))
                (equal (fn-nntp-index-cache-query
                        (fn-nntp-index-cache-open generation archive)
                        generation (fn-nntp-index-config-digest archive)
                        :last group low high current)
                       (cons :ok (fn-nntp-group-last-number
                                  group current (fn-state-articles archive)))))))

(defthm fn-nntp-index-cache-open-answers-range
  (implies (and (fn-statep archive)
                (natp generation)
                (stringp group)
                (natp low)
                (natp high))
           (equal (fn-nntp-index-cache-query
                   (fn-nntp-index-cache-open generation archive)
                   generation (fn-nntp-index-config-digest archive)
                   :range group low high current)
                  (cons :ok (fn-nntp-group-range-numbers
                             group low high (fn-state-articles archive))))))
```

## Why the served path is not switched

`fn-nntp-group-result` and `fn-nntp-listgroup-result` reach the archive only
through their arguments. A cache cannot be handed to them without widening
`fn-nntp-make-session` / `fn-nntp-step`, which is a shared-struct change owned
by this wave's `books/nntp.lisp` lane. Changing `nntp.lisp` to rebuild the
index per command would be slower, not faster, so there is no honest
"minimal call-site swap" available from inside a pure function. The six
`-equals-fold` theorems are exactly what makes that swap a substitution once
the session carries the index; see the proposals below.

## Certification

GREEN, both lane roots, on the coordinator-installed baseline certs:

    FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py \
        books/nntp-index tests/acl2/nntp-index-tests
    ACL2 certification passed: books/nntp-index, tests/acl2/nntp-index-tests
    Certification evidence: build/acl2/certify-20260919T170804Z-29266

The scratch admit (`build/scratch/ld-both.lsp`, `(set-prover-step-limit
2000000)`) reports 0 ACL2 errors, 50 passing `assert-event`s and 4 passing
`must-fail`s. Guards are verified for all 25 new functions.

The local baseline `make certify` did NOT complete in this lane: it was killed
at the wire/wildmat books when the coordinator moved baselines off the laptop
(load 98, nineteen ACL2 processes). `build/certify-baseline.log` ends in
`Terminated: 15`. The certs this lane built on were installed by the
coordinator from the remote box; this lane certified only its own two roots.

Two defects the prover found, both worth carrying forward as lessons:

1. `fn-nntp-index-numbers-of-reference-range` failed because
   `fn-article-msgid` and `fn-article-memberships` had unfolded to
   `CAR`/`CADDDR`, so the accessor-vocabulary rewrite rule beside it could not
   match. The fix is the `:in-theory (disable ...)` on that hint, with a
   comment. This is a general tax in this tree: functions are stated in
   accessor/`fn-ag-` vocabulary and proved in `car`/`cdr`/`<` vocabulary,
   and `books/index.lisp` already carries a comment about the same trap.
2. `(with-prover-step-limit N (must-fail (thm ...)))` does not work:
   exceeding the limit is a hard error that `must-fail` will not absorb, even
   with `:expected :any`. The must-fails now carry
   `:hints (("Goal" :do-not-induct t))` so the failure is soft and immediate.
   The separating `assert-event`s beside each one are the stronger teeth
   anyway: they compute both answers and exhibit the difference.

## Measurements

NOT RUN. `tests/index_measure.py` is written and compiles, and
`specs/index.md` has no numbers in it: no performance claim is made anywhere in
this lane, because none was measured.

The script builds the `tests/store_capacity_probe.py` maximum profile (128
transactions of 32768 payload octets, every article in both configured
groups), recovers it read-only, asserts that the index answer equals the fold
answer for `:count`, `:low`, `:high` and `:range` before timing anything, and
then takes five samples of each of nine arms: fold and index for each of
GROUP's three enumerations and LISTGROUP's range, plus `refusal_round_trip`,
which is `fn-index-host-query` at a generation the cache was not built for -
the same bridge round trip with no enumeration at all. It reports min and
median per arm into `build/index-measure/measure.json`, with the source
digests of the four files that produced them.

    python3 tests/index_measure.py

When that has run, put its table into `specs/index.md` under the host-adoption
section with that exact command, and say in the same sentence that every
number is one ACL2 bridge call in a persistent process - not a socket, not a
served connection, not CLI startup.

## Python results

NOT RUN. `tests/test_index_cache.py` needs `books/nntp-index.cert` to exist,
because `host/index-host.lisp` includes that book.

    python3 -m unittest tests.test_index_cache tests.test_reader \
        tests.test_reader_partitions -v

The four tests are: every kind's index answer equals `fn-index-host-fold` on
the same recovered store; a forged generation (four values, both directions)
is refused and the cache still answers afterwards; a post between two reader
sessions makes the pre-post generation refuse and the re-opened index carry
the post-generation truth (count 2 to 3, high 2 to 3, range (1 2) to (1 2 3));
and a changed configuration digest, or a cache never opened, refuses rather
than answering. `tests.test_reader` and `tests.test_reader_partitions` are the
control: this lane changed nothing they exercise, so they must be unchanged,
not merely green.

## Open items and proposals

1. **Session-carried index (for the `nntp.lisp` owner).** Widen
   `fn-nntp-make-session` with an index field set by `fn-nntp-open-session`
   (which already runs the one whole-archive pass), then replace
   `(fn-nntp-group-low group (fn-state-articles archive))` in
   `fn-nntp-group-result` with `(fn-nntp-index-group-low index group)` and the
   equivalent four substitutions in `fn-nntp-listgroup-result`,
   `fn-nntp-next-command` and `fn-nntp-last-command`. Each is licensed by one
   named theorem above; no new proof obligation is created, but
   `fn-nntp-step-preserves-consistent-session` and the effects book must be
   rebuilt, since the session shape changes.
2. **`fn-nntp-index-config-digest` is a digest in name only.** It is the
   group list, the watermark list and the article count, compared with
   `equal`. That is sound (no collision risk, because nothing is hashed) but
   it is O(configuration) to build. It is built once per selection, never per
   command. If the configuration ever grows, replace it with a content
   identity from `books/identity`, not with a Python-side hash.
3. **The generation is an observation, not a computed value.** Python passes
   the durable record count it recovered, the same way it already passes the
   allocator frontier. ACL2 owns every derived value in the answer. If a
   future store exposes a durable generation counter, pass that instead.
4. **`stringp group` does not separate.** It is carried because
   `fn-index-query-range` is total; under `fn-article-listp` both sides answer
   the empty projection for a non-string group. This is recorded in the test
   book rather than dressed up as a tooth.
5. **Not measured here:** the socket path. Every number below is one ACL2
   bridge call in a persistent process; none of it is a served-connection
   latency and none of it is a claim about a reader under load.
