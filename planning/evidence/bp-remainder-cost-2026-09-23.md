# The rest of the BP cost list, and `fn-defrecord`'s forward fact (lane COST-bp2, 2026-09-23)

Branch `cost/bp2` from `dev` 5c549e6c. It works through the "not changed"
list of [the first BP cost lane](bp-books-cost-2026-09-23.md) and row 8 of
[the profiler's list](certification-cost-2026-09-23.md).

The diagnosis comes from certify logs that already existed. The "before"
numbers are from the `dev` head run on persvati,
`/home/ember/fn-gates/dev-head/build/acl2/certify-20260923T003741Z-1790068/`.
None of the six books changed between that run's sources and 5c549e6c. The
seam run, `certify-20260923T000250Z-1473169`, gives the same shape for the
five books it contains.

Only one slow form was rerun on purpose: `fn-bpa-encoding-bound`, whose log
names no rule. It ran once under `accumulated-persistence`.

Each repair was tried in one `tools/proof_repl.py` session per book on the
Mac (ACL2 8.7, SBCL, `tools/acl2`, `FN_ACL2_SLOTS=8`). The closure came from
`~/.cache/fn-certs`. `bp-workflow-invariants` changed under
`bp-workflow-binding-core`, so it was certified locally once
(`build/acl2/a local certification in the lane's worktree (manifest not retained; recertified by the incremental run of dev's head)) before the second book's
session. In the "after" columns, each whole book was loaded form by form in a
fresh session at the committed bytes, and every form was admitted. The session
times are Mac times. Prover steps do not depend on the machine.

"Time" is the sum of the events' `Time:` lines, without wrapper events and
without `include-book`.

## Diagnosis, per book

### bp-release-invariants: 386.1 s over 51 events, 40.2 M steps

| event | time | steps | subgoals | definitions opened | cause |
|---|---|---|---|---|---|
| `fn-bprl-release-record-replays-decision-by-definition` | 318.3 s | 28.6 M | 29 283; `Goal` splits 29 280 ways | 86 | the three `-formula` rewrite rules expand a decision the goal only projects |
| `fn-bprl-release-removes-the-forward-pin` | 65.1 s | 10.8 M | 1 307; 580 at `Goal''`, then 234 per case | 64 | the state recognizers, opened book-wide, expand the `:use` hypotheses |

**The replay theorem.** Its hint opens `fn-bprl-apply-journal-record`. The
goal assumes `fn-bprl-release-recordp r`, so the first arm is taken, and the
theorem then only says that projections of
`(list t (fn-bprl-decision-state d) ...)` are those projections. The book
disabled `fn-bprl-release-decision` and the three projections after proving
`fn-bprl-decision-state-formula`, `-okp-formula` and `-evidence-formula`. The
formulas are enabled rewrite rules, though, and each one rewrote
`(fn-bprl-decision-X (fn-bprl-release-decision s id))` into the
`fn-bprl-release-okp` spelling. `fn-bprl-release-okp` opens into
`fn-bp-statep`. The top of the book enables `fn-node-statep`, `fn-statep`,
`fn-node-stagep` and `fn-retain-statep`, and those opened in turn. The
splitter note for `Goal` names all three formula rules and 20 definitions:

- the workflow recognizers: `fn-bp-statep`, `-workp`, `-attemptp`,
  `-pendingp`, `-receiptp`, `-configp`, `-authorized-receiptp`;
- the node and retention recognizers: `fn-node-statep`, `-stagep`,
  `fn-statep`, `fn-retain-statep`, `-admissiblep`, `-known-idp`,
  `-matching-releasep`, `fn-fencedp`;
- `member-equal`, `natp` and `posp`.

The statement needed none of that. This is the D6 shape: a whole-state
recognizer opened to prove a projection.

**The forward-pin theorem.** Its `:use` list instantiates
`fn-bp-statep-components`. The instance puts `fn-node-statep`,
`fn-bp-configp`, `fn-bp-work-listp`, `fn-bp-receipt-listp`, `fn-bp-pendingp`
and `fn-bp-tx-key-listp` terms into the hypotheses. The hint closes
`fn-bp-statep` but none of these, and `fn-node-statep` is enabled book-wide.
The splitter names `fn-bp-attemptp`, `-configp`, `-pendingp`, `-receiptp`,
`-workp` and `fn-fencedp`, and the definitions `fn-node-stagep`,
`fn-node-statep`, `fn-retain-admissiblep` and `fn-retain-known-idp` in the
subcases. The facts used are the conclusions of the five `:use` instances,
with the recognizers as opaque literals.

### bp-primary-cbor: 72.6 s over 126 events, 22.8 M steps

| event | time | steps | subgoals | cause |
|---|---|---|---|---|
| `fn-bpc-u64-bytes-have-eight-octets` | 32.9 s | 9.0 M | 0 | the hint re-enables `fn-bpc-u32-octets` |
| `fn-bpc-u64-bytes-fields` | 31.8 s | 10.3 M | 0 | the same |

No subgoal is printed: the whole cost is in simplifying `Goal`, with type
reasoning over the nested `floor`/`mod` terms of two opened
`fn-bpc-u32-octets` calls. `Rules:` shows `FLOOR-BOUNDED-BY-/`,
`MOD-BOUNDED-BY-MODULUS` and the `floor`/`mod` type prescriptions. The book
disables `fn-bpc-u32-octets` at line 226 so that "every later proof uses the
inverse, length and octet lemmas". It then proves `-u32-octets-fields` and
`-prefix-fields` for exactly this purpose. Both u64 hints put the function
back in their `enable` list.

### bp-bundle-invariants: 24.1 s over 36 events, 4.5 M steps

| event | time | steps | subgoals | cause |
|---|---|---|---|---|
| `fn-bpb-encode-block-head` | 15.5 s | 2.7 M | 260; 128 at `Subgoal 4` | the CRC field and the argument encoder opened to read the first octet |
| `fn-bpb-bundle-tail-are-octets` | 4.5 s | 0.74 M | 0 | the bundle recognizer's field recognizers opened (24 definitions) |

The head is the `car` of `fn-bpb-encode-block-with-crc`'s `cons`, and it
depends on neither argument. The splitter names `fn-bpp-zero-crc`, then
`fn-bpp-crc-octets`, `fn-bpp-crc16-scan`, `fn-bpc-argument` and `natp`.

### bp-workflow-binding-core: 33.1 s over 30 events, 10.4 M steps

| event | time | steps | subgoals | cause |
|---|---|---|---|---|
| `fn-bp-binding-state-implies-statep` | 14.9 s | 4.5 M | 161; 149 at `Goal'` | extracts a conjunct, but `fn-bp-statep` opens on both sides |
| `fn-bp-prepare-receipt-preserves-binding-state` | 9.2 s | 3.5 M | 1 304; 360 at `Goal''` | the step's refusal tests open |
| `fn-bp-binding-state-implies-pending-boundp` | 8.6 s | 2.1 M | 292 | as the first |

Each opens 63 definitions. The first and third state a conjunct of
`fn-bp-binding-statep`. The splitter names `fn-bp-workp`, `-attemptp`,
`-receiptp`, `-pendingp`, `member-equal`, `natp` and `posp`: the state
recognizer, opened under the only enable in the hint. The second opens
`fn-bp-authorized-receiptp`, `fn-bp-configp`, `-workp` and `-receiptp` from
the refusal tests of `fn-bp-prepare-receipt`. Those tests are hypotheses of
the arms the proof works on, and are never needed opened.

### bp-workflow-invariants: 31.1 s over 60 events, 29.1 M steps

| event | time | steps | subgoals | cause |
|---|---|---|---|---|
| `fn-bp-work-with-status-preserves-workp` | 12.1 s | 12.8 M | 370; 110 at `Goal'`, 13 per case | the receipt and the 13-way status enumeration opened |
| `fn-bp-work-with-attempt-preserves-workp` | 9.4 s | 8.8 M | 398 | the attempt, receipt and status recognizers opened |

`fn-bp-work` is a hand-written record whose accessors are enabled `fn-bp-nth`
calls. The rebuilt work carries the old receipt, and for `-with-attempt` the
new attempt, as the same terms the hypotheses test. The splitter names
`fn-bp-attemptp`, `fn-bp-receiptp` and `member-equal`: the member test is
`fn-bp-transport-statusp`, a 13-constant enumeration.

### bp-adu: 25.3 s over 76 events, 3.6 M steps

| event | time | steps | subgoals |
|---|---|---|---|
| `fn-bpa-encoding-bound` | 20.7 s | 45 k (2 k steps/s) | 2 |

The log names only the rules that were used. The one instrumented run
(`accumulated-persistence`) took 19.05 s and 45 462 steps, and showed:

- `(:definition len)`: 15.9 M frames and 166 tries, 17 of them useful;
- `(:type-prescription true-listp-append)`: 5.3 M tries, none useful;
- `(:type-prescription binary-append)`: 5.3 M tries, none useful;
- `(:type-prescription true-listp)`: 5.3 M tries;
- `(:rewrite default-cdr)`: 8.0 M frames, none useful.

`fn-bpa-encode` is thirteen constant header octets consed onto an append of
the nine field encodings. `len` opened once per header octet. Each opening
re-derived the type of the whole append nest through the append type
prescriptions, so the time went to type-set and not to rewriting.

## `fn-defrecord`: `<recognizer>-forward-shape`

The macro proved `(implies (<rec> x) (and (<shape> x) (consp x) (true-listp
x)))` with `:in-theory (enable <shape>)` over the current theory. The fact
needs the recognizer's first conjunct and `<shape>-forward-shape`, which the
macro generates just above it. With the old hint, every enabled field
predicate opened in the hypothesis and split. In the seam run, the two
`bp-node-machine` records paid 128.6 s and 120.1 s (about 1 460 subgoals
each), and the other 128 forward-shape events in the tree took about 7 s
between them. The first BP lane wrapped the two `bp-node-machine` records in
encapsulates. The macro change keeps any record from paying this again.

## The repairs (hints, one local lemma; no statement changed)

- **bp-release-invariants.**
  - The replay theorem's hint also disables
    `fn-bprl-decision-state-formula`, `-okp-formula` and `-evidence-formula`.
    The goal then stays in the projection vocabulary, and it closes from the
    arm alone.
  - The forward-pin theorem's hint also closes `fn-node-statep`, `fn-statep`,
    `fn-node-stagep`, `fn-retain-admissiblep`, `fn-retain-admit`, and the
    workflow recognizers `fn-bp-configp`, `-work-listp`, `-receipt-listp`,
    `-pendingp`, `-tx-key-listp`, `-workp`, `-receiptp`, `-attemptp` and
    `fn-fencedp`. The five `:use` instances carry the facts as opaque
    literals.
- **bp-primary-cbor.** The two u64 hints no longer enable `fn-bpc-u32-octets`.
  The halves are closed, and `fn-bpc-u32-octets-fields` and `-prefix-fields`
  plus `fn-bpc-append-associativity` do the work.
- **bp-bundle-invariants.**
  - `fn-bpb-encode-block-head` gets a hint that closes `fn-bpb-block-crc` and
    `fn-bpc-argument`.
  - `fn-bpb-bundle-tail-are-octets` also closes `fn-bpb-block-listp`,
    `fn-bpb-payload-blockp`, `fn-bpb-splitp` and `fn-bpp-blockp`. The octet
    facts of the encoders are stated over those recognizers, and tau
    discharges the goal from them (41 steps).
- **bp-workflow-binding-core.**
  - The three conjunct extractions close `fn-bp-statep`,
    `fn-bp-works-boundp` and `fn-bp-pending-boundp`.
  - `fn-bp-prepare-receipt-preserves-binding-state` also closes
    `fn-bp-authorized-receiptp`, `fn-bp-configp`, `-workp`, `-receiptp` and
    `-attemptp`. `fn-bp-work-outstandingp` stays open, because its `consp`
    conjunct is what licenses `fn-bp-find-work-boundp`. The first attempt,
    which closed it, failed on exactly that.
- **bp-workflow-invariants.**
  - `-with-attempt-` closes `fn-bp-attemptp`, `fn-bp-receiptp` and
    `fn-bp-transport-statusp`. It no longer enables `fn-bp-attemptp`: the
    attempt is the hypothesis's term.
  - `-with-status-` closes `fn-bp-receiptp` and `fn-bp-transport-statusp`. It
    still opens `fn-bp-attemptp`, because the new attempt is built from the
    old one's fields.
- **bp-adu.** A local lemma `fn-bpa-len-of-cons`,
  `(len (cons a x)) = (+ 1 (len x))`, is disabled right after it is proved.
  `fn-bpa-encoding-bound`'s hint enables it and closes `len`. The header then
  counts thirteen octets by rewriting, and `fn-record-length-append` takes the
  appends.
- **`fn-defrecord`** (`books/defrecord.lisp`).
  - `<recognizer>-forward-shape` is proved in `minimal-theory`, with
    `:expand` of the recognizer call and `:use` of `<shape>-forward-shape`.
    No field predicate and no `:extra` function is opened. The rule classes
    and the statement are unchanged.
  - Section 5 of `tests/acl2/defrecord-tests.lisp` is the proof on a small
    record. `fn-drt-code` has six fields, each an **enabled** ten-way
    disjunction. The whole `fn-defrecord` form admits under
    `(with-prover-step-limit 5000 ...)`: 2 824 steps, of which the forward
    fact is 106. The same statement under the old hint is a `must-fail`
    under 100 000 steps. Unlimited, it closed in 27.7 M steps and 49.9 s on a
    158-way split in the session.
  - The macro, with its test book, certified locally in
    `build/acl2/a local certification in the lane's worktree (its manifest was not retained; the incremental run of dev's head recertifies the test book).

## Before and after

| book | before: time (persvati, dev head) | before: steps | after: time (Mac session) | after: steps |
|---|---|---|---|---|
| `bp-release-invariants` | 386.1 s | 40.2 M | 2.0 s | 0.78 M |
| `bp-primary-cbor` | 72.6 s | 22.8 M | 6.1 s | 3.45 M |
| `bp-workflow-binding-core` | 33.1 s | 10.4 M | 0.28 s | 0.27 M |
| `bp-workflow-invariants` | 31.1 s | 29.1 M | 7.2 s | 7.75 M |
| `bp-bundle-invariants` | 24.1 s | 4.5 M | 4.3 s | 1.07 M |
| `bp-adu` | 25.3 s | 3.6 M | 3.2 s | 3.63 M |
| total | 572.4 s | 110.7 M | 23.0 s | 17.0 M |

| event | before | after |
|---|---|---|
| `fn-bprl-release-record-replays-decision-by-definition` | 318.34 s, 28.6 M, 29 283 sg | 0.05 s, 42 538 steps, 2 sg |
| `fn-bprl-release-removes-the-forward-pin` | 65.07 s, 10.8 M, 1 307 sg | 0.02 s, 14 305 |
| `fn-bpc-u64-bytes-have-eight-octets` | 32.90 s, 9.0 M | 0.01 s, 1 822 |
| `fn-bpc-u64-bytes-fields` | 31.84 s, 10.3 M | 0.01 s, 2 691 |
| `fn-bpa-encoding-bound` | 20.74 s, 45 k | 0.06 s, 39 k |
| `fn-bpb-encode-block-head` | 15.46 s, 2.7 M, 260 sg | 0.01 s, 2 476 |
| `fn-bp-binding-state-implies-statep` | 14.88 s, 4.5 M | 0.00 s, 37 |
| `fn-bp-work-with-status-preserves-workp` | 12.07 s, 12.8 M | 0.05 s, 76 216 |
| `fn-bp-work-with-attempt-preserves-workp` | 9.38 s, 8.8 M | 0.06 s, 94 206 |
| `fn-bp-prepare-receipt-preserves-binding-state` | 9.24 s, 3.5 M, 1 304 sg | 0.01 s, 20 658 |
| `fn-bp-binding-state-implies-pending-boundp` | 8.62 s, 2.1 M | 0.00 s, 46 |
| `fn-bpb-bundle-tail-are-octets` | 4.54 s, 0.74 M | 0.01 s, 41 |

What remains over 1 s:

- `fn-bpc-u32-octets-prefix-fields` (2.5 s) and `-fields` (1.1 s): the
  arithmetic, proved once;
- `fn-bpb-decode-block-of-encode-block` (2.4 s for 89 k steps, a low rate
  that has not been profiled);
- `fn-bp-recovery-pending-preserves-pendingp` (1.7 s);
- `fn-bp-prepare-enqueue-preserves-state` (1.1 s);
- `fn-bpa-round-trip` (1.1 s).

## Unverified

- The six BP books are session admissions, not certificates, apart from
  `bp-workflow-invariants`, which was certified locally.
- The `defrecord` change invalidates every certificate in the tree. Only
  `books/defrecord` and `tests/acl2/defrecord-tests` have certified against
  it. The claim that the new proof holds for all 40-odd records in the tree
  rests on its shape: the goal is propositional after one expansion and one
  `:use`, whatever the fields or `:extra` are. Root's next treewide run is
  where it is checked.
- The `bp-node-machine` encapsulates from the first lane are now redundant.
  They are left as they are, because that book is not on this lane's list.
