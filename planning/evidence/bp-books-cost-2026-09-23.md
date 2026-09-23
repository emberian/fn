# Why the BP books took 657 s, 251 s and 132 s, and the repair (lane COST-bp, 2026-09-23)

Branch `cost/bp` from `dev` 549c750a. The diagnosis was read from certify
logs that already existed. No slow form was rerun on purpose. One exception
was an accident: a `proof_repl` load of `bp-node-machine` ran the original
`fn-bpn-machine-recordp-forward-shape` again, because `--upto` does not name
an `fn-defrecord` form. That run was killed partway. The repair was tried
in one `tools/proof_repl.py` session per book on the Mac (ACL2 8.7, SBCL
2.6.8, `tools/acl2`), with the closure installed from `~/.cache/fn-certs`
and every dependency cached. Session times are Mac times. The old times
are persvati times. Prover steps do not depend on the machine, so both
columns carry them.

## The logs

| log (persvati) | what it is |
|---|---|
| `/home/ember/fn-gates/t1-seam/build/acl2/certify-20260923T000250Z-1473169/books--bp-*.certify.log` | the 310-book run of `planning/evidence/manifests/certify-20260923T000250Z-1473169.json`. It is the source of every "before" number below. |
| `/home/ember/fn-gates/dev-head/build/acl2/certify-20260923T003741Z-1790068/books--bp-*.certify.log` | the `dev` head. It gives the same shape: `bp-primary-invariants` 689.4 s, `bp-sequence-fidelity` 131.9 s. |

"Time" is the sum of the events' `Time:` lines. The `PROGN` that
`fn-defrecord` expands to reports its inner `defthm` a second time, so
`bp-node-machine`'s 500 s event sum is 251 s of work.

## bp-primary-invariants: 656 s over 47 events, 410 M prover steps

| event | time | steps | subgoals | cause |
|---|---|---|---|---|
| `fn-bpp-block-crc-width` | 458.3 s | 134.0 M | 726, first split 108 ways at `Goal'` | a CRC codec and the block recognizer opened by a goal that only needs a width |
| `fn-bpp-bundle-age-round-trip` | 42.4 s | 2.7 M | 5 | the decoder opened, so the `:use` instance cannot match |
| `fn-bpp-accepted-block-has-valid-crc` | 39.0 s | 17.9 M | 4 915, 217-way split | dispatch goal opens the block value through a local unfolding rule |
| `fn-bpp-crc-octets-are-octets` | 36.1 s | 17.6 M | 46 | the CRC bit loop and the u16/u32 conversions opened |
| `fn-bpp-accepted-input-is-canonical-by-construction` | 30.4 s | 12.8 M | 3 673, 217-way split | same as `-has-valid-crc` |
| `fn-bpp-decode-yields-block` | 26.4 s | 10.4 M | 3 673, 217-way split | same |
| `fn-bpp-block-value-cost` | 5.2 s | 1.8 M | 500 | a genuine field-by-field proof over `fn-bpp-blockp` |
| `fn-bpp-crc-octets-length` | 4.5 s | 2.3 M | 8 | the conversions opened |
| `fn-bpp-block-crc-is-octets` | 3.9 s | 1.0 M | 496 | `fn-bpp-blockp` opened for one field |
| the other 38 | 9.8 s | | | |

**`fn-bpp-block-crc-width`.** The statement is `(len (fn-bpp-block-crc b)) =
(fn-bpp-crc-width (fn-bpp-crc-type b))` under `(fn-bpp-blockp b)`. The
splitter note for `Goal'` names these if-intro rules: `FLOOR`,
`FN-BPP-CRC-OCTETS`, `FN-BPP-CRC-TYPEP`, `FN-BPP-DTN-SSPP`, `FN-BPP-EIDP`,
`FN-BPP-TIMEP` and `NTH`. The `Rules:` list opens 33 definitions:

- the whole recognizer: `fn-bpp-blockp`, `-eidp`, `-dtn-sspp`, `-timep`,
  `-vchar-listp`, `-flag-setp`, `-fragmentp` and every projection;
- the CRC: `fn-bpp-crc16`, `fn-bpp-crc32c`, `fn-bpp-zeroed-encoding`;
- the conversions: `fn-cbor-u16-bytes` and `fn-cbor-u32-bytes`, plus `FLOOR`
  and `MOD` with `arithmetic/top`.

The conversions were open because line 22 enabled `fn-cbor-codec-vocabulary`
for the whole book (review F3). Each of the 108 cases coming from the
recognizer carried the floor/mod spelling of a CRC over the zero-filled
encoding, and each cost about 0.6 s of arithmetic. The proof needs two
facts: a valid block's CRC type is 0, 1 or 2, and a u16/u32 conversion has
2 or 4 elements whatever its argument. `fn-bpc-u16-bytes-have-length-two`
and `-u32-bytes-have-length-four` already exist in `bp-primary-cbor`.

**The three decode theorems.** Each one only dispatches on the outcome of
`fn-bpp-decode` and reads off its last arm. Their hints disable
`fn-bpp-encode`, but the local rule `fn-bpp-encode-unfolds` (defined above
them) rewrites the decoder's `(fn-bpp-encode b)` into
`(fn-bpc-encode (fn-bpp-block-value b ...))`. `fn-bpp-block-value` and
`fn-bpp-eid-value` are enabled, so the goal opened the whole block value
(`Rules:` lists `FN-BPP-BLOCK-VALUE`, `FN-BPP-EID-VALUE` and
`FN-BPC-ENCODE`) and split 217 ways.

**`fn-bpp-bundle-age-round-trip`.** Five subgoals and 2.7 M steps still took
42 s. The goal opened `fn-bpc-decode` and `fn-bpc-decode-exact` (the
splitter names `FN-BPC-DECODE`), so the `fn-bpc-value-round-trip` instance,
stated about `fn-bpc-decode-exact`, no longer matched the goal syntactically.
The prover then worked on the decoder applied to the encoding.

## bp-node-machine: 251 s of work (500 s event sum), 59 M steps

| event | time | steps | subgoals | cause |
|---|---|---|---|---|
| `fn-bpn-answerp-forward-shape` | 128.6 s | 20.3 M | 1 462 at `Goal'` | the whole-state recognizer opened by a shape fact |
| `fn-bpn-machine-recordp-forward-shape` | 120.1 s | 18.9 M | 1 460 at `Goal'` | the same |
| everything else | about 2 s | | | |

Both theorems are generated by `fn-defrecord` (`books/defrecord.lisp`
line 290). The statement is "the recognizer implies its shape predicate",
and the macro's hint is `:in-theory (enable <shapep>)` on top of the
current theory. In this book the field predicates are ordinary enabled
`defun`s: `fn-bpn-jobp`, `-maybe-pendingp`, `-pendingp`, `-routep`,
`-effectp`, `-lifecycle-recordp`, `-machine-u64p`, `-boolp`, `-limitp`,
`fn-bpp-eidp` and `fn-frame-textp`. The splitter lists them, and each one
opened with the recognizer. The answer record's field is
`fn-bpn-machine-statep`, which is the machine record's recognizer again. So
both proofs split about 1 460 ways, although the fact needs only the
recognizer's first conjunct. This is the D6 shape, the whole-state
recognizer, but here the cost is paid when the record is defined, not per
event. It is local to this book: in the same run, all 113 other
`<recognizer>-forward-shape` events in the tree took 0.49 s together.

## bp-sequence-fidelity: 132 s over 60 events, 98 M steps

| event | time | steps | subgoals | cause |
|---|---|---|---|---|
| `fn-bpn-sf-step-preserves-nonreuse` | 72.9 s | 26.5 M | 11 538, deepest `5.134.104.102.57` | twelve-field recognizer open under a kind dispatch |
| `fn-bpn-sf-recover-step-preserves-nonreuse` | 37.6 s | 14.1 M | 6 625, 124 at `Goal'` | the same, per arm |
| `fn-bpn-sf-stage-step-preserves-nonreuse` | 9.5 s | 3.2 M | 1 581 | the same |
| `fn-bpn-sf-parent-steps-preserve-nonreuse` | 3.9 s | 1.9 M | 980 | the same |
| `fn-bpn-sf-directory-step-preserves-nonreuse` | 3.5 s | 1.6 M | 786 | the same |

Every definition in this book is enabled. The arm lemmas' hints also name
`fn-bpn-sf-statep` explicitly. The comment on `fn-bpn-sf-nonreusep` says
that state shape "is proved separately so the transition proof does not
repeatedly expand the twelve-field recognizer". The proofs expanded it
anyway: `Rules:` lists `FN-BPN-SF-STATEP` and `FN-BPN-SF-OBSERVATIONP` in
every row above. The observation disjunction and the eleven field tests
multiplied the step's case tree. Nonreuse needs three facts from the state
recognizer: the state is a true list, and its frontier, its confirmed
frontier and (when present) its pending sequence are sequence frontiers.

None of the three books has a forcing round or an induction (no `*1/`
subgoal) in any slow event, and no subgoal name repeats, so there is no
rewrite loop.

## The repair (hints, disables and local shape lemmas; no statement changed)

**bp-primary-invariants.**

- The top-of-book `(local (in-theory (enable ...)))` is gone. The CBOR codec
  vocabulary is opened nowhere, because no theorem here decodes a CBOR head.
  `fn-cbor-record-vocabulary` is opened in the hints of the five theorems
  that read a CBOR result (`fn-bpp-decode-of-encode`, the three decode
  theorems and `fn-bpp-bundle-age-round-trip`). The two octet lemmas of
  `fn-cbor-invariants-vocabulary` are opened in the one hint that uses them.
  The log's `Rules:` lines say which theorems used which runes.
  `tools/theory_check.py` no longer lists the book as a codec opener
  (46 books before, 45 after).
- `fn-bpp-crc-octets-are-octets` and `-length` close `fn-bpp-crc16`,
  `fn-bpp-crc32c` and the conversions, and use the conversions' octet and
  length lemmas with the checksums' existing bound lemmas.
- Two new local shape lemmas:
  - `fn-bpp-crc-octets-width`: for a CRC type, the field has
    `fn-bpp-crc-width` octets.
  - `fn-bpp-blockp-crc-type` (forward chaining): a valid block's CRC type is
    a CRC type.

  `fn-bpp-block-crc-is-octets`, `-length` and `-width` then keep
  `fn-bpp-blockp`, `fn-bpp-crc-type`, `-crc-typep` and `-crc-octets` closed.
- The three decode theorems also close `fn-bpp-encode-unfolds`.
- `fn-bpp-bundle-age-round-trip` also closes `fn-bpc-decode-exact` and
  `fn-bpc-decode`, so the round-trip instance matches the goal as it stands.

**bp-node-machine.** Each of the two `fn-defrecord` forms is wrapped in an
`encapsulate` whose only other event is a `local` disable of that record's
field predicates:

- machine state: `fn-bpn-job-listp`, `-contact-listp`, `-maybe-pendingp`,
  `-machine-boolp`, `-machine-u64p`, `-machine-limitp`;
- answer: `fn-bpn-machine-statep`, `fn-bpn-effect-listp`.

The rest of the book sees exactly the theory it saw before. The macro is not
changed. Only this book pays the cost, and editing `books/defrecord.lisp`
would invalidate every certificate in the tree.

**bp-sequence-fidelity.** Right after `fn-bpn-sf-step-preserves-statep`:

- two local forward-chaining lemmas, `fn-bpn-sf-statep-numeric-fields` and
  `fn-bpn-sf-statep-pending-field`, state the three facts listed above in
  the `nth` form the goals have;
- a local `in-theory` closes `fn-bpn-sf-statep` and
  `fn-bpn-sf-observationp`;
- `fn-bpn-sf-statep` is removed from the seven arm lemmas' `enable` lists.

The keystone's hint is unchanged. After this change the comment on
`fn-bpn-sf-nonreusep` describes what the proofs actually do.

## Before and after

In the "after" column, each whole book was loaded form by form in a fresh
session at the committed bytes, and every form was admitted.

| book | before: event time (persvati) | before: steps | after: event time (Mac session) | after: steps |
|---|---|---|---|---|
| `bp-primary-invariants` | 656.4 s | 410.1 M | 10.7 s | 5.8 M |
| `bp-node-machine` | 251 s (500.4 s summed) | 59 M (118.7 M summed) | 1.5 s (3.0 s summed) | 0.37 M (0.74 M summed) |
| `bp-sequence-fidelity` | 132.2 s | 98.3 M | 3.9 s | 2.0 M |

Each slow event, before and after:

| event | before | after |
|---|---|---|
| `fn-bpp-block-crc-width` | 458.27 s, 134.0 M steps | 0.01 s, 123 steps |
| `fn-bpp-bundle-age-round-trip` | 42.44 s, 2.7 M | 0.20 s, 0.12 M |
| `fn-bpp-accepted-block-has-valid-crc` | 38.96 s, 17.9 M | 0.01 s, 870 |
| `fn-bpp-crc-octets-are-octets` | 36.09 s, 17.6 M | 0.01 s, 458 |
| `fn-bpp-accepted-input-is-canonical-by-construction` | 30.45 s, 12.8 M | 0.01 s, 561 |
| `fn-bpp-decode-yields-block` | 26.36 s, 10.4 M | 0.00 s, 549 |
| `fn-bpn-answerp-forward-shape` | 128.55 s, 20.3 M | 0.01 s, 479 |
| `fn-bpn-machine-recordp-forward-shape` | 120.13 s, 18.9 M | 0.01 s, 507 |
| `fn-bpn-sf-step-preserves-nonreuse` | 72.94 s, 26.5 M | 0.62 s, 0.54 M |
| `fn-bpn-sf-recover-step-preserves-nonreuse` | 37.63 s, 14.1 M | 0.43 s, 0.38 M |
| `fn-bpn-sf-stage-step-preserves-nonreuse` | 9.47 s, 3.2 M | 0.07 s, 53 k |

What remains in `bp-primary-invariants` is about 9 s of genuine
field-by-field proofs over `fn-bpp-blockp`: `fn-bpp-block-value-cost`,
`-value-block-of-block-value`, `-block-value-is-shape` and
`-primary-identity-value-is-shape`. The steps of these rows did not change.

## The other BP books on the list (diagnosed, not changed here)

Changing these books is outside this lane's certification set.
`bp-primary-cbor` in particular sits under `bp-primary`, so changing it
recertifies every BP book above it.

- **`bp-primary-cbor`, 78.9 s.** `fn-bpc-u64-bytes-fields` (37.2 s, 10.3 M
  steps) and `fn-bpc-u64-bytes-have-eight-octets` (31.8 s, 9.0 M) open
  `fn-bpc-u32-octets` twice. The work goes to type reasoning over the nested
  `floor`/`mod` terms: `Rules:` shows `FLOOR-BOUNDED-BY-/`,
  `MOD-BOUNDED-BY-MODULUS` and the `FLOOR`/`MOD` type prescriptions, and no
  subgoals. Proposed repair: keep `fn-bpc-u32-octets` closed and use
  `fn-bpc-u32-octets-fields` and `-prefix-fields`, which are proved just
  above them.
- **`bp-bundle-invariants`, 27.1 s.** `fn-bpb-encode-block-head` (17.2 s)
  asks only for the head octet of an encoded block. It opens
  `fn-bpp-crc16-scan`, `fn-bpp-crc32c-scan` and `fn-bpp-crc-octets`: the
  same CRC opening as above. Proposed repair: close the CRC.
- **`bp-workflow-binding-core`, 30.7 s, and `bp-workflow-invariants`,
  30.1 s.** `fn-bp-binding-state-implies-statep` (14.3 s, 63 definitions,
  149-way split) and `fn-bp-work-with-{status,attempt}-preserves-workp`
  (11.6 s and 9.0 s, 110- and 112-way splits) open the receipt, attempt and
  config recognizers field by field. This is the recognizer-opening class
  again; per-field shape lemmas are the repair.
- **`bp-adu`, 20.4 s.** `fn-bpa-encoding-bound` spends 16.8 s on 2 subgoals
  and 45 k steps. That is time outside rewriting (linear arithmetic or
  ground evaluation over the encoders), and the log does not name the rule.
  It needs the one allowed instrumented run.

## Unverified

These are session admissions, not certificates. The farm run submitted with
this change certifies the three books and their test books. `bp-bundle`,
`bp-node-machine-codec` and `bp-node-machine-invariants` include the changed
books, and their dependents recertify at root's next treewide run. Every
change here is local or a hint, so the worlds those books see are the same
theorems as before.
