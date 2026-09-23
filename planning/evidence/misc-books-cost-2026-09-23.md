# Nine books over ten seconds, read from their logs, and the repairs (lane COST-misc, 2026-09-23)

Branch `cost/misc` from `dev` 5c549e6c. The diagnosis below was read from
certify logs already on disk; no slow form was rerun to find its cause. The
repairs were tried in `tools/proof_repl.py` sessions on the Mac (ACL2 8.7,
SBCL, `tools/acl2`), one per book, with the dependencies included from
`~/.cache/fn-certs` where a pair was cached and from source otherwise.
Session times are Mac times and the old times are persvati times; prover
steps do not depend on the machine, so both columns carry them where known.

## The logs

| log | books read from it |
|---|---|
| `persvati:/home/ember/fn-gates/dev-head/build/acl2/certify-20260923T003741Z-1790068/` (dev head treewide, stopped; see `certification-cost-2026-09-23.md`) | `identity-invariants`, `byte-store-scan`, `bp-fragment-invariants`, `tests/acl2/bp-fragment-tests`, `principal-invariants`, `node-config`, `bp-bundle`, `checkpoint-compaction` |
| `persvati:/home/ember/fn-gates/t1-seam/build/acl2/certify-20260923T000250Z-1473169/` (seam tree) | the same books where present, as a cross-check: identical step counts |
| `persvati:/home/ember/fn-gates/w31-treewide/build/acl2/certify-20260922T204423Z-3881000/` | `bp-node-machine-invariants`, which neither run above reached. Its source is unchanged since 76924870 (2026-09-21); the `121645Z` run's log is byte-identical |

Method: every `Summary` block's `Form`, `Rules` (the `:DEFINITION` runes),
`Time`, `Prover steps counted`, the splitter notes and the subgoal names
between one summary and the next; wrapper events (`encapsulate`, `progn`,
`make-event`) left out of the sums. `theory_check.py --table` for the
top-of-book enables.

## Per book

"Book" is ACL2's own `certify-book` time; "events" is the sum of the event
times. "split" is the largest splitter note, "sg" the subgoals printed.

### bp-node-machine-invariants: 47.5 s, 11.5 M steps, 93 events

| event | time | steps | sg | split | cause |
|---|---|---|---|---|---|
| `fn-bpb-encode-is-an-octet-list` | 16.9 s | 3.03 M | 1 180 | 108 at `Goal''`, then 101 | the hint opens `fn-bpb-bundlep` for three field facts and leaves `fn-bpp-blockp` (the primary block's recognizer) open under it; the splitter names `FLOOR`, `FN-BPP-CRC-TYPEP`, `-DTN-SSPP`, `-EIDP`, `-TIMEP`, `NTH`, 25 definitions opened |
| `fn-bpn-find-job-is-a-job` | 14.2 s | 2.75 M | 70 | 64 at `*1/2'` | induction on `fn-bpn-find-job`; `fn-bpn-job-listp` gives `(fn-bpn-jobp (car jobs))` and `fn-bpn-jobp` (a `fn-defrecord` recognizer, enabled) opens into its eleven field predicates, which are all enabled `defun`s (`fn-bpp-eidp`, `fn-bpn-routep`, `fn-frame-textp`, ...) |
| `fn-bpn-next-token-of-applicable-record` | 6.3 s | 1.87 M | 468 | 242 at `Goal` | a token equation; the splitter names `FN-BPN-JOBP`, `-LIFECYCLE-RECORDP`, `-MEMBER`, `-RECORD-KEY`, `-ROUTEP`, `FN-BPP-EIDP` ...: 42 definitions for a fact about one field |
| `fn-bpn-job-with-status-is-a-job` | 3.0 s | 0.61 M | 0 | | the same field predicates opened on both sides |
| the other 89 | 6.7 s | | | | none over 1.3 s |

Class (a) of `certification-cost-2026-09-23.md` throughout: a recognizer
left open where the goal needs one conjunct of it. No forcing round, no
repeated subgoal name.

### identity-invariants: 19.9 s, 18.6 M steps, 46 events

| event | time | steps | sg | cause |
|---|---|---|---|---|
| `fn-id-obligation-shape` | 7.3 s | 9.31 M | **0** | the whole cost is simplifying `Goal` (1.27 M steps/s: rewriting, not arithmetic). The hint opens `fn-id-render` and `fn-id-labelledp` on the quoted 16-octet label, so the identity is spelled out as a 51-element cons nest and `fn-frame-split` (enabled book-wide by `(:d fn-frame-split)`) runs down it octet by octet, with `fn-cbor-octet-listp` and `len` over every prefix |
| `fn-id-subject-is-not-an-obligation` | 5.0 s | 5.21 M | 0 | the same, splitting a 48-octet identity at 16 |
| `fn-id-obligation-is-not-a-subject` | 2.1 s | 1.88 M | 0 | the same at 13 |
| `fn-id-obligation-preimage-octets` | 1.8 s | 0.46 M | 104 | `fn-cbor-u32-bytes` opened to `floor`/`mod` (splitter: `FLOOR`) |
| `fn-id-u32-from-append` | 1.2 s | 0.32 M | 50 | the u32 codec opened on purpose (2 forced) |
| `fn-id-subject-shape` | 1.1 s | 1.16 M | 0 | as `-obligation-shape` |

The separation theorems need only lengths: `fn-id-labelledp label x`
forces `(len x) = (len label) + 35`, a 13-octet label makes a 48-octet
identity and a 16-octet label a 51-octet one. The book also opens six codec
vocabularies at the top (`theory_check.py`: `fn-cbor-codec-vocabulary`,
`fn-frame-codec-vocabulary`, ...), which is where the open `fn-frame-split`
and CBOR list rules come from.

### bp-fragment-invariants: 19.9 s, 5.53 M steps, 47 events

| event | time | steps | sg | cause |
|---|---|---|---|---|
| `fn-bpf-anonymous-conformant-bundle-is-not-fragmentable` | 12.8 s | 3.24 M | 788, 146-way at `Goal'`, 32 under 17 of those | propositional in three flag tests, but `fn-bpp-no-fragmentp`, `-any-status-requestp` and `-administrativep` open to `(mod (floor flags mask) 2)` bit tests with `arithmetic/top` loaded (`EQUAL-CONSTANT-+`, `EQUAL-DENOMINATOR-1` split); 39 hypotheses forced, one forcing round |
| `fn-bpf-fragment-block-is-a-block` | 2.6 s | 0.92 M | 337, 104-way | `fn-bpp-blockp` open on the fragment block |
| `fn-bpf-fragment-block-sets-the-fragment-flag` | 2.2 s | 0.64 M | 337, 104-way | the same |

### tests/acl2/bp-fragment-tests: 16.6 s, 6.50 M steps

Two `must-fail` forms are 16.3 s of it (4.8 s and 11.5 s, 2.08 M and 4.41 M
steps, inductions reaching `*1.39.3.2.4.1.1` and `*1.36.2.2.5.2.2.6.6`): the
prover searching for a proof of a general claim until it gives up. The
ledger's teeth-form lint (`tools/ledger.py`, "Teeth are concrete: a specific
violating value") flags exactly this shape, and the book already bites two
of the keystone's four hypotheses with concrete instances for the same
reason.

### principal-invariants: 15.9 s, 2.64 M steps, 25 events

| event | time | steps | sg | cause |
|---|---|---|---|---|
| `fn-prin-apply-succession-preserves-statep` | 12.2 s | 1.91 M | 23, 21-way at `Goal'` | 156 k steps/s. The hint withdraws three statement functions but leaves `fn-prin-succession-key` open; its decode test (`FN-STMT-OKP`, `-VALUE`, `-BYTES-ITEM-P`, `FN-SIG-PUBLIC-KEY-P`) splits the goal against the acceptability test's accessor chain (31 definitions, `fn-stmt-header-*` included). The only fact the goal takes from the payload is that a key it yields is a public key |

The book opens six codec vocabularies at the top; the other 24 events are
3.6 s together.

### node-config: 13.2 s, 2.09 M steps, 95 events

| event | time | steps | sg | cause |
|---|---|---|---|---|
| `fn-cnode-replay-apply-record-keeps-groups-and-capacity` | 6.8 s | 0.80 M | 1 536 at `Goal` | the replay dispatch opened with the event recognizers (`FN-STXA-P`, `-STXE-P`, `-STXK-P`), the composite decoder and the retention arm's release test all open |
| `(verify-guards fn-cnode-apply-record)` | 3.3 s | 0.86 M | 918, 743-way | the hint opens `fn-store-event-p` to reach the used lemma's hypothesis and `fn-record-p` comes open under it (the book enables `fn-record-record-vocabulary` and `-shape-vocabulary` at the top); the splitter names ten record field recognizers |

### byte-store-scan: 15.0 s, 4.40 M steps, 185 events

| event | time | steps | sg | cause |
|---|---|---|---|---|
| `fn-bs-names-after-of-tear-write` | 6.8 s | 2.06 M | 746, 105-way per induction case | no hints; induction on `fn-bs-tear-write` with `min`, `max`, `floor`, `nfix` and the slice helpers open, so every case splits over the slice bounds. The fact is that every operation a torn write emits is a `:write`, which the name walk passes over |
| `fn-bs-crash-select-names-are-an-outcome` | 1.7 s | 0.38 M | 18 | an induction that opens `fn-bs-tear-write` again under `fn-bs-crash-select` |

The book is 185 events; 5.4 s of it are events under 1 s.

### bp-bundle: 7.5 s, 1.27 M steps

`fn-bpb-bundlep-forward-shape` 4.2 s (5.4 s in the seam log), 0.45 M steps:
generated by `fn-defrecord`, which proves it with the current theory, and
`fn-bpp-blockp` and the block-list recognizer are open here. The repair is
the macro's (lane cost/bp2, which owns `books/defrecord.lisp`); nothing in
this book is changed for it. The guard of `fn-bpb-encode-blocks` is 1.8 s
(128-way splits over the CRC scans: `fn-bpb-encode-block` and
`fn-bpb-blockp` open where the guard needs only that a block's encoding is
a true list, which `fn-bpb-encode-block-is-true-list` states).

### checkpoint-compaction: 1.5 s

Its 31 s wall is from `certify-20260922T022942Z` and `T031240Z` (2026-09-22
02:29 and 03:12 UTC); every manifest since has it between 1.1 and 1.8 s, and
the dev head log sums its 32 events to 0.8 s. Nothing to do.

## Repairs

No theorem statement changed. Every repair is a hint, a local lemma, or
(in the test book) a general `must-fail` replaced by a concrete
counterexample. "Before" is the persvati log; "after" is the session on the
Mac, the sum of the event `Time:` lines with the book's whole event list
loaded from the edited source.

| book | before: book (events) | after: session event sum | worst event after |
|---|---|---|---|
| `bp-node-machine-invariants` | 47.5 s, 11.5 M steps | 4.13 s | 1.27 s (`fn-bpn-restart-step-preserves-machine-invariant`, unchanged) |
| `principal-invariants` | 15.9 s (15.4 s prove), 2.64 M steps | 2.35 s | 0.51 s |
| `identity-invariants` | 19.9 s, 18.6 M steps | 1.29 s | 0.78 s (`fn-id-u32-from-append`, unchanged) |
| `bp-fragment-invariants` | 19.9 s, 5.53 M steps | 1.46 s | 0.66 s |
| `tests/acl2/bp-fragment-tests` | 16.6 s, 6.50 M steps | 0.54 s | 0.53 s |
| `node-config` | 13.2 s, 2.09 M steps | 1.39 s | 0.22 s |
| `byte-store-scan` | 15.0 s, 4.40 M steps | 6.58 s | 1.43 s (`fn-bs-crash-select-names-are-an-outcome`, unchanged) |
| `bp-bundle` | 7.5 s, 1.27 M steps | 5.87 s, of which 4.12 s is `fn-bpb-bundlep-forward-shape` | 4.12 s (the `fn-defrecord` forward-shape event, which lane cost/bp2 owns) |
| `checkpoint-compaction` | 1.5 s | not touched | |

**bp-node-machine-invariants.** Six hints now close what their goals never
needed open. The changes to hints only, and no lemma was added, so the book
composes with cost/bp2's macro change. In `fn-bpb-encode-is-an-octet-list`,
`fn-bpp-blockp` is closed (1 665 steps, against 3.03 M). In
`fn-bpn-find-job-is-a-job`, `fn-bpn-jobp` and `fn-bpn-job-key-memberp` are
closed (806 steps, against 2.75 M). In
`fn-bpn-next-token-of-applicable-record`, the job, record and list
functions are closed (8 213 steps, against 1.87 M). In
`fn-bpn-job-with-status-is-a-job`, the eleven field predicates are closed
(449 steps, against 612 k). In `fn-bpn-apply-inapplicable-record-is-noop`,
the applicability test is closed (39 steps, against 359 k). In
`fn-bpn-send-bundle-anchor-is-typed`, the sent bundle and its age decoder
are closed, because the anchor type holds for any age that tests as a time
(551 steps, against 470 k). The session loaded all 94 forms. The book's
dependencies `bp-bundle`, `bp-bundle-invariants`, `bp-node`,
`bp-node-machine` and `bp-primary-invariants` had no cached pair at these
digests and were included from source.

**bp-bundle.** The guard of `fn-bpb-encode-blocks` gets `:guard-hints`
closing `fn-bpb-encode-block` and `fn-bpb-blockp`: 1 463 steps, against
271 k. The forward-shape event is left to the macro lane.

**principal-invariants.** The hint on `fn-prin-apply-succession-preserves-statep`
withdrew three statement functions and left the rest of the book's theory
in place. With `fn-prin-succession-key` also closed the proof still took
7.7 s and 2.0 M steps with only nine subgoals, so its time was not in the
split. One `accumulated-persistence` run named it: `true-listp` and
`fn-cbor-octet-listp` terms backchaining through
`fn-record-cbor-octet-list-true-listp`,
`fn-cbor-octet-listp-implies-true-listp`,
`fn-stmt-id-listp-implies-true-listp`, `fn-stmt-decode-ok-implies-octets`
and `fn-digest-octetsp-implies-octet-listp` into `fn-cbor-decode` (803 k
frames on the first rune alone, none useful). These rules are open because
the book enables the codec and record vocabularies at the top. The goal
needs the state record's accessors, the acceptability test and one fact
about the payload. That fact is now a local lemma,
`fn-prin-succession-key-is-a-key`: a key the succession yields is a public
key. The theorem is proved in `minimal-theory` plus the eleven runes it
uses: 5 100 steps, 0.01 s.

**identity-invariants.** Four local lemmas about `fn-id-render` over any
label: its octets, its length, `fn-id-labelledp label (fn-id-render label d)`
(through `fn-frame-split-of-append`, with `fn-frame-split` closed), and
`fn-id-labelledp label x` implies `(len x) = (len label) + 35`. The two
shape theorems use the first three with `fn-id-render` and
`fn-id-labelledp` closed: 266 steps each, against 9.31 M and 1.16 M. The two
separation theorems are the length lemma instantiated at the other label,
a 48-against-51 contradiction: 151 steps each, against 5.21 M and 1.88 M.
The two preimage-length theorems close `fn-cbor-u32-bytes`, whose octets and
length the CBOR invariants already give: 12 k steps against 456 k. The
top-of-book vocabulary enables are left as they are. Withdrawing them is a
larger change to this book, and nothing in it is slow once these five
events stopped taking constant labels apart.

**bp-fragment-invariants.** In `fn-bpf-anonymous-conformant-bundle-is-not-fragmentable`,
`fn-bpp-no-fragmentp`, `-any-status-requestp` and `-administrativep` are
closed. The fact is propositional in them: 107 steps, no forcing, against
3.24 M steps and 39 forced hypotheses. The two fragment-block theorems close
the EID, time, CRC-type and DTN-SSP recognizers. The fragment block copies
those fields, and the two new fields are hypotheses: 7 k and 11 k steps,
against 0.64 M and 0.92 M.

**tests/acl2/bp-fragment-tests.** The two general `must-fail` teeth
(without `fn-bpf-all-agreep` and without `fn-bpf-inputsp`) are now concrete
instances, the form the book already uses for the other two hypotheses.
The first uses the same three cuts of eight zero octets, which reassemble
to `(:ok (0 0 0 0 0 0 0 0))`. The second is one fragment that carries the
whole payload but declares a total of 9, and is refused as
`(:invalid :bounds)`. Each instance satisfies every other hypothesis and
falsifies the conclusion. The book's `must-fail` count goes from 2 to 0 and
its `assert-event` count rises by 7. The ledger's teeth-form lint had
flagged both general forms as bare general claims.

**node-config.** The replay theorem closes the event recognizers
(`fn-stxa-p`, `-stxe-p`, `-stxk-p`, `fn-store-retention-event-p`) and
`fn-replay-composite-record`: 3 777 steps against 800 k. The guard of
`fn-cnode-apply-record` closes `fn-record-p` and
`fn-store-retention-event-p`, because the hypothesis `(fn-record-p record)`
is the disjunct of `fn-store-event-p` that the used lemma needs: 2 893 steps
against 862 k.

**byte-store-scan.** `fn-bs-names-after-of-tear-write` gets an explicit
induction on `fn-bs-tear-write` with `min`, `max`, `floor`,
`fn-bs-unit-count`, `fn-bs-take` and `fn-bs-zeros` closed: 31 795 steps
against 2.06 M. The book's remaining 6.6 s is spread over 159 events. The
largest is `fn-bs-crash-select-names-are-an-outcome` at 1.4 s, which was
left alone.

## What is not verified here

- A session admission is not a certificate. The farm run below is the
  certification; until its manifest is harvested, the rows above are
  session evidence only.
- The session times are Mac times with other lanes' ACL2 processes running;
  the step counts are the machine-independent comparison.
- `bp-node-machine-invariants`, `bp-fragment-tests` and `byte-store-scan`
  were loaded over dependencies included uncertified from source (no cached
  pair at these digests). `bp-bundle`'s change moves the digest of every
  BP book above it, so the farm run recertifies that closure.
- `bp-bundle`'s forward-shape event (4.1 s) and the book-wide codec enables
  in `identity-invariants`, `principal-invariants`, `bp-fragment-invariants`
  and `node-config` are left as they are.
