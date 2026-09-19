# Lane dump: `bp-primary-time`

Written on instruction to hand the lane to a Codex root. Branch
`lane/bp-primary-time`, worktree
`/Users/ember/dev/fn/build/lanes/bp-primary-time`, branched from `0bd0b5c`.

## 0. A certification is running right now

- Log: `/Users/ember/dev/fn/build/lanes/bp-primary-time/build/cbor15.log`
- Command: `ACL2_CUSTOMIZATION=NONE acl2 < <scratchpad>/drv.lsp > build/cbor15.log 2>&1`
  where `drv.lsp` is
  `(ld '((certify-book "books/bp-primary-cbor" 0 t)) :ld-error-action :return :ld-error-triples t) (quit)`
- It is an **unchanged re-run** of round 14, to test whether round 14's failure
  was flaky (see §3).
- At the time of writing it had processed 33 forms and was at
  `FN-BPC-U32-FROM-IS-A-NUMBER`.
- Progress can be read with `grep -c '^Form:  (' build/cbor15.log` and
  `grep -nE 'ACL2 Error|is now certified' build/cbor15.log`.
- Earlier attempts are `build/cbor5.log` through `build/cbor14.log`;
  `build/certify-baseline.log` and `build/acl2/certify-*/` hold the runner's
  evidence directories. The furthest any run got is **form 101 of ~110**
  (`build/cbor12.log`).

**Box safety note that must be passed on:** early in the lane I ran
`pkill -f "acl2"` to stop a diverging proof of my own. That pattern matches
every process whose command line contains `acl2`, which on this machine is
**every other lane's** `saved_acl2.core` SBCL process. I killed other lanes'
in-progress certifications at roughly 02:20 local on 2026-09-19. Nothing in any
other worktree was modified; only processes were signalled. Kill by explicit
PID (`lsof -t <logfile>` identifies the writer) — never `pkill -f` on a shared
toolchain path.

## 1. The packet as I understood it

Ten parallel lanes; mine is `bp-primary-time`. Deliver, in this worktree only:

1. **CBOR extension** (`books/bp-primary-cbor.lisp`): extend the existing
   `fn-cbor` primitives — without editing `books/cbor.lisp` — with exactly the
   vocabulary RFC 9171 §4.3.1 needs: definite arrays of bounded arity, definite
   text strings, unsigned integers to 2^64-1 (CBOR additional information 27,
   which `fn-cbor-decode-unsigned` answers `:unsupported` for), and nothing
   else. Prove round trip, accepted-input canonicality (RFC 8949 §4.2.1), and
   bounds before allocation.
2. **Primary block model** (`books/bp-primary.lisp`, `bp-primary-invariants.lisp`):
   version 7; bundle processing control flags as a bounded bit set; CRC type
   and CRC-16 / CRC-32C computed in ACL2 and tested against RFC or pinned
   implementation vectors; `dtn` (including `dtn:none`) and `ipn` endpoint IDs;
   creation timestamp; lifetime; fragment offset and total ADU length. Define
   bundle identity and prove it is determined by the canonical encoding. Model
   the Previous Node, Bundle Age and Hop Count extension blocks. Explain in the
   spec how fn's current BID maps onto bundle identity and what a relay needs.
3. **Fragmentation** (`books/bp-fragment.lisp`, `bp-fragment-invariants.lisp`):
   fragment and reassemble; accept any complete cover **including
   byte-identical overlaps** (explicitly not repeating the transfer kernel's
   hard stall); conflict only on differing bytes; theorems for complete cover,
   identity preservation, missing range, conflict; teeth for each.
4. **Time** (`books/clock.lisp`, `clock-invariants.lisp`): host observation
   {monotonic, wall, wall-error-bound, has-wall}; `fn-clock-expiry-decision`
   returning `:expired` / `:live` / `:uncertain`; never `:expired` while the
   error bound admits liveness; monotone in monotonic time; safety never
   depends on two nodes agreeing on wall time; teeth.
5. **Specs** `specs/bp-primary.md` and `specs/time.md`; prefix rows in
   `docs/prefixes.md`; RFC rows in `docs/references.md`; Makefile roots.

Standard: both codec directions, reject malformed and non-minimal input before
allocation, every keystone with a reachable witness and `must-fail` teeth per
hypothesis, no `skip-proofs`/`defaxiom`/`defttag`, no editing `books/cbor.lisp`,
no counts in prose, no interoperability claim without a vector.

Gate: `make check`; full `make certify` green including the new roots.

## 2. DONE

### 2.1 Reference texts (committed, `141d0da`)

`rfc9171.txt` (2990 lines), `rfc9172.txt` (1989), `rfc9173.txt` (2690), fetched
from rfc-editor.org — the only network action this lane took. `docs/references.md`
updated with local-copy links and the sections each document is used for.

### 2.2 Source, specs and registry rows (committed, `40d52e9`)

All seven books, three test books, two specs, prefix rows and Makefile roots are
written and committed. **They are not all certified**; see §3.

Makefile roots added after the `bp-adu` group, in dependency order:

```
books/bp-primary-cbor  books/bp-primary  books/bp-primary-invariants
tests/acl2/bp-primary-tests
books/bp-fragment  books/bp-fragment-invariants  tests/acl2/bp-fragment-tests
books/clock  books/clock-invariants  tests/acl2/clock-tests
```

`docs/prefixes.md` gained four rows: `fn-bpc-`, `fn-bpp-`, `fn-bpf-`,
`fn-clock-`.

### 2.3 What each book contains

**`books/bp-primary-cbor.lisp`** (`fn-bpc-`, ~1000 lines). Value domain
`(:uint . n) | (:text . octets) | (:bytes . octets) | (:array . values)` via a
flag function `fn-bpc-shapep`, so one induction scheme serves items and lists.
`fn-bpc-enc` / `fn-bpc-dec` with an **item budget** that is simultaneously the
termination measure and the work bound. `fn-bpc-cost` over-counts (sums where
the decoder needs a maximum), so `(<= (fn-bpc-cost flg x) budget)` is
sufficient. Bounds: `*fn-bpc-max-uint*` 2^64-1, `*fn-bpc-max-text*` 1024,
`*fn-bpc-max-arity*` 16, `*fn-bpc-max-bytes*` 64, `*fn-bpc-max-items*` 128,
`*fn-bpc-max-input*` 65536.

**`books/bp-primary.lisp`** (`fn-bpp-`). Block record
`(:fn-bp-primary flags crc-type destination source report-to creation-time
sequence lifetime fragment-offset total-adu-length)`; version is not a field
because a stored version could only disagree with the codec. Bounded
exclusive-or `fn-bpp-xor` by bit recursion (no logops library), then
`fn-bpp-crc16` (X-25: reflected 0x8408, init 0xFFFF, final xor 0xFFFF) and
`fn-bpp-crc32c` (iSCSI: reflected 0x82F63B78, init/final 0xFFFFFFFF).
`fn-bpp-encode` builds the zero-filled encoding, computes the CRC over it, and
re-encodes with the real CRC, so `fn-bpp-encode` is literally
`(fn-bpc-enc :item (fn-bpp-block-value b (fn-bpp-block-crc b)))`.
`fn-bpp-decode` has four distinct refusals: the CBOR reason, `:malformed`,
`:crc-mismatch`, `:noncanonical`.

**`books/bp-primary-invariants.lisp`** — the codec theorems and the identity
theorems.

**`books/bp-fragment.lisp`** (`fn-bpf-`). Reassembly is specified **index-wise**
(`fn-bpf-cell-at` folds the whole fragment list at one index) rather than as a
fold over fragments, so the result cannot depend on fragment order. Four
outcomes: `(:invalid reason)`, `(:conflict i)`, `(:missing lo hi)`, `(:ok bytes)`.
Bounds `*fn-bpf-max-length*` 65536, `*fn-bpf-max-fragments*` 64.

**`books/clock.lisp`** (`fn-clock-`). Observation
`(:fn-clock-observation monotonic wall wall-error has-wall)`; age anchor
`(age . monotonic-at-anchor)` or nil; decision prefers the age path whenever an
anchor exists, else decides over the whole admissible interval
`[wall-err, wall+err]`.

### 2.4 Verbatim keystone statements

These are the statements as committed. **None of them is currently certified**
— see §3. They are reproduced so Codex does not have to re-derive them.

```lisp
(defthm fn-bpc-decode-of-encode
  (implies (and (fn-bpc-shapep flg x)
                (fn-cbor-octet-listp rest)
                (natp budget)
                (<= (fn-bpc-cost flg x) budget))
           (equal (fn-bpc-dec flg
                              (if (eq flg :list) (len x) 0)
                              (append (fn-bpc-enc flg x) rest)
                              budget)
                  (fn-cbor-ok x rest))))

(defthm fn-bpc-value-round-trip
  (implies (and (fn-bpc-valuep x)
                (<= (fn-bpc-cost :item x) *fn-bpc-max-items*)
                (fn-cbor-at-mostp (fn-bpc-enc :item x) *fn-bpc-max-input*))
           (equal (fn-bpc-decode-exact (fn-bpc-encode x))
                  (fn-cbor-ok x nil))))

(defthm fn-bpc-accepted-input-is-canonical
  (implies (fn-cbor-result-okp (fn-bpc-decode-exact octets))
           (equal (fn-bpc-encode (fn-cbor-result-value
                                  (fn-bpc-decode-exact octets)))
                  octets)))

(defthm fn-bpc-dec-yields-shape
  (implies (and (fn-cbor-octet-listp octets)
                (natp count)
                (fn-cbor-result-okp (fn-bpc-dec flg count octets budget)))
           (fn-bpc-shapep flg (fn-cbor-result-value
                               (fn-bpc-dec flg count octets budget)))))

(defthm fn-bpc-enc-length-bound
  (implies (fn-bpc-shapep flg x)
           (<= (len (fn-bpc-enc flg x)) (* 1033 (fn-bpc-cost flg x))))
  :rule-classes :linear)

(defthm fn-bpp-value-block-of-block-value
  (implies (and (fn-bpp-blockp b)
                (fn-cbor-octet-listp crc-octets)
                (equal (len crc-octets)
                       (fn-bpp-crc-width (fn-bpp-crc-type b))))
           (equal (fn-bpp-value-block (fn-bpp-block-value b crc-octets)) b)))

(defthm fn-bpp-decode-of-encode
  (implies (fn-bpp-blockp b)
           (equal (fn-bpp-decode (fn-bpp-encode b)) (fn-bpp-ok b))))

(defthm fn-bpp-accepted-input-is-canonical-by-construction
  (implies (fn-bpp-result-okp (fn-bpp-decode octets))
           (equal (fn-bpp-encode (fn-bpp-result-block (fn-bpp-decode octets)))
                  octets)))

(defthm fn-bpp-accepted-block-has-valid-crc
  (implies (and (fn-bpp-result-okp (fn-bpp-decode octets))
                (not (equal (fn-bpp-crc-type
                             (fn-bpp-result-block (fn-bpp-decode octets)))
                            0)))
           (equal (fn-bpp-value-crc-field
                   (fn-cbor-result-value (fn-bpc-decode-exact octets)))
                  (fn-bpp-block-crc
                   (fn-bpp-result-block (fn-bpp-decode octets))))))

(defthm fn-bpp-encode-is-injective
  (implies (and (fn-bpp-blockp p) (fn-bpp-blockp q)
                (equal (fn-bpp-encode p) (fn-bpp-encode q)))
           (equal p q))
  :rule-classes nil)

(defthm fn-bpf-complete-agreeing-cover-reassembles-to-payload
  (implies (and (fn-cbor-octet-listp payload)
                (fn-bpf-inputsp fs (len payload))
                (fn-bpf-all-agreep fs payload)
                (fn-bpf-covers-all fs (len payload)))
           (equal (fn-bpf-reassemble fs (len payload))
                  (list :ok payload))))

(defthm fn-bpf-reassemble-ok-agrees-with-every-fragment
  (implies (and (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :ok)
                (member-equal f fs)
                (natp k)
                (< k (len (fn-bpf-bytes f))))
           (equal (nth k (fn-bpf-bytes f))
                  (nth (+ (fn-bpf-offset f) k)
                       (fn-bpf-result-bytes (fn-bpf-reassemble fs total))))))

(defthm fn-bpf-uncovered-index-blocks-success
  (implies (and (fn-bpf-fragment-listp fs)
                (natp i) (< i total) (natp total)
                (not (fn-bpf-coveredp fs i)))
           (not (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :ok))))

(defthm fn-bpf-missing-low-index-is-uncovered
  (implies (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :missing)
           (not (fn-bpf-coveredp
                 fs (fn-bpf-result-bytes (fn-bpf-reassemble fs total))))))

(defthm fn-bpf-disagreeing-fragments-yield-conflict
  (implies (and (fn-bpf-inputsp fs total)
                (member-equal f fs)
                (member-equal g fs)
                (natp i) (< i total)
                (not (equal (fn-bpf-cell-of f i) :gap))
                (not (equal (fn-bpf-cell-of g i) :gap))
                (not (equal (fn-bpf-cell-of f i) (fn-bpf-cell-of g i))))
           (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :conflict)))

(defthm fn-bpf-fragment-block-preserves-adu-key
  (implies (and (fn-bpp-blockp b) (natp offset) (natp total))
           (equal (fn-bpp-adu-key (fn-bpf-fragment-block b offset total))
                  (fn-bpp-adu-key b))))

(defthm fn-clock-expired-requires-every-admissible-clock-to-agree
  (implies (and (fn-clock-observationp obs)
                (fn-clock-timep creation-time)
                (fn-clock-timep lifetime)
                (null bundle-age)
                (fn-clock-admissible-truep obs now)
                (equal (fn-clock-expiry-decision creation-time lifetime
                                                 bundle-age obs)
                       :expired))
           (< lifetime (- now creation-time))))

(defthm fn-clock-expired-and-live-cannot-both-be-sound
  (implies (and (fn-clock-observationp a)
                (fn-clock-observationp b)
                (fn-clock-timep creation-time)
                (fn-clock-timep lifetime)
                (fn-clock-admissible-truep a now)
                (fn-clock-admissible-truep b now)
                (equal (fn-clock-expiry-decision creation-time lifetime nil a)
                       :expired))
           (not (equal (fn-clock-expiry-decision creation-time lifetime nil b)
                       :live))))

(defthm fn-clock-expired-by-age-requires-true-age-over-lifetime
  (implies (and (fn-clock-observationp obs)
                (fn-clock-age-anchorp bundle-age)
                (consp bundle-age)
                (fn-clock-timep lifetime)
                (<= (fn-clock-age-estimate bundle-age obs) true-age)
                (equal (fn-clock-expiry-decision creation-time lifetime
                                                 bundle-age obs)
                       :expired))
           (< lifetime true-age)))

(defthm fn-clock-expiry-is-monotone-in-local-time
  (implies (and (fn-clock-observationp a)
                (fn-clock-observationp b)
                (fn-clock-age-anchorp bundle-age)
                (fn-clock-timep creation-time)
                (fn-clock-timep lifetime)
                (fn-clock-later-observationp a b)
                (equal (fn-clock-expiry-decision creation-time lifetime
                                                 bundle-age a)
                       :expired))
           (equal (fn-clock-expiry-decision creation-time lifetime
                                            bundle-age b)
                  :expired)))
```

The hypothesis predicates one level down:

- `fn-bpc-shapep flg x` — the flag-function value recogniser (see §2.3).
- `fn-bpc-cost flg x` — `1` for a scalar, `1 + cost(:list elements)` for an
  array, `1 + cost(item) + cost(rest)` for a list step, `1` for nil.
- `fn-bpp-blockp b` — 11-element tagged list, `fn-bpp-flag-setp` flags,
  `fn-bpp-crc-typep` in {0,1,2}, three `fn-bpp-eidp` endpoints, three
  `fn-bpp-timep` times, and the fragment fields present exactly when the
  fragment flag is set.
- `fn-bpp-eidp` — `(:dtn-none)`, or `(:dtn . ssp)` with `fn-bpp-dtn-sspp` (all
  VCHAR, ≤1024, begins `//`, non-empty node-name, name delimiter present), or
  `(:ipn n s)` with both ≤ 2^64-1.
- `fn-bpf-inputsp fs total` — every element `fn-bpf-fragmentp`, `total` in
  `(0, 65536]`, at least one and at most 64 fragments, all declaring the same
  total.
- `fn-bpf-fragmentp f` — 4-element tagged list, natural offset, octet-list
  bytes, non-empty, `offset + len(bytes) <= total <= 65536`.
- `fn-bpf-all-agreep fs payload` — each fragment's bytes equal the payload's
  extent at its offset, pointwise.
- `fn-bpf-covers-all fs n` — `fn-bpf-covered-range fs 0 n`; every index below
  `n` is inside some fragment's extent.
- `fn-clock-observationp` — 5-element tagged list, three `fn-clock-timep`
  fields, boolean `has-wall`.
- `fn-clock-admissible-truep obs now` — `now` is a time, `obs` claims a wall
  reading, and `wall - err <= now <= wall + err`.
- `fn-clock-later-observationp a b` — monotonic counter has not gone backwards,
  `has-wall` is the same, and `wall - err` has not gone backwards.
- `fn-clock-age-anchorp` — nil, or a cons of two times.

### 2.5 Teeth

`std/testing/must-fail` cases, each wrapped in `local` per that macro's own
documented caveat about non-local `(must-fail (thm ...))`:

| Test book | `assert-event` | `must-fail` |
| --- | --- | --- |
| `tests/acl2/clock-tests.lisp` | 26 | 9 |
| `tests/acl2/bp-primary-tests.lisp` | 89 | 11 |
| `tests/acl2/bp-fragment-tests.lisp` | 52 | 10 |

**UNVERIFIED RISK Codex must check first:** `tools/certify_books.py` fails a run
if the string `ACL2 Error` appears anywhere in the log (`FAILURE_MARKERS`, line
30). `must-fail` wraps its inner form in `(with-output :off :all ...)`, which
should suppress that, but **no test book has been certified yet, so this was
never confirmed**. If it does leak, the fallback is to replace each `must-fail`
with a concrete counterexample `assert-event` — arguably stronger evidence
anyway (an exhibited counterexample rather than "ACL2 could not prove it") — and
say so in the handoff. A one-form probe already exists at
`<scratchpad>/probe-must-fail.lisp`.

## 3. IN PROGRESS — exact current state

**Nothing in this lane has been certified.** `books/bp-primary-cbor.lisp` is the
only book that has been run through ACL2 at all; the other six books and the
three test books have **never been submitted to ACL2**, because each depends on
the CBOR book certifying first and the lane allows one ACL2 process at a time.

### 3.1 `books/bp-primary-cbor.lisp`

Fifteen `certify-book` attempts. The furthest (`build/cbor12.log`) reached
**form 101 of about 110**: everything up to and including all four
`fn-bpc-*-head-range` and all four `fn-bpc-*-head-decodes` corollaries
certified, and the failure was the main round trip:

```
7725:ACL2 Error [Failure] in ( DEFTHM FN-BPC-DECODE-OF-ENCODE ...)
```

with key checkpoints of the form

```
Subgoal *1/4.3
(IMPLIES (AND (NOT (EQUAL FLG :LIST)) (CONSP X) (EQUAL (CAR X) :UINT)
              (NATP (CDR X)) (<= (CDR X) 18446744073709551615)
              (FN-CBOR-OCTET-LISTP REST) (NATP BUDGET) (<= 1 BUDGET))
         (EQUAL (FN-BPC-DEC FLG 0 (APPEND (FN-BPC-ARGUMENT 0 (CDR X)) REST)
                            BUDGET)
                (FN-CBOR-OK X REST)))
```

annotated "before the induction-depth-limit stopped the proof attempt".
**Diagnosis:** `fn-bpc-dec` is not being opened, because its measure is the
variable `budget` and ACL2 sees no decrease, so it declines to expand and then
tries its own inductions until the depth limit. The fix applied in round 13 was
an `:expand ((:free (a b c d) (fn-bpc-dec a b c d)))` hint on that theorem and
on `fn-bpc-dec-reencodes-consumed-prefix`; **that fix has not yet been tested**,
because round 13 failed earlier on a speculative lemma and round 14 failed
earlier still (next paragraph).

Round 14 (`build/cbor14.log`) failed at form 35 on
`FN-BPC-U64-BYTES-FIELDS` — a lemma that had **passed in round 12** with
identical text — with

```
Time:  15.80 seconds (prove: 0.00, print: 0.00, other: 15.80)
Prover steps counted:  213
*** Note: No checkpoints to print. ***
ACL2 Error [Failure] in ( DEFTHM FN-BPC-U64-BYTES-FIELDS ...)
```

Zero prover time, 213 steps, no checkpoints, 15.8 s of "other". That is not a
proof failure shape. The box was at load average 27 with eight concurrent ACL2
processes each getting ~37% of a core. **My working hypothesis is a resource
flake, and round 15 (now running) is the unchanged re-run that tests it.** If
round 15 gets past form 35, the real remaining question is whether the round-13
`:expand` fix closes `fn-bpc-decode-of-encode`.

### 3.2 Recommended next steps for whoever picks this up

1. Read `build/cbor15.log`. If `FN-BPC-U64-BYTES-FIELDS` passed, the round-14
   failure was a flake and the next real checkpoint is
   `FN-BPC-DECODE-OF-ENCODE`.
2. If `fn-bpc-decode-of-encode` still does not close with the `:free` `:expand`
   hint, **the structured fallback is to stop relying on one big induction** and
   prove four opening lemmas whose `:expand` patterns match exactly, then let
   the main induction be bookkeeping:
   - `(fn-bpc-dec flg count (append (fn-bpc-argument 0 n) rest) budget)`
     = `(fn-cbor-ok (cons :uint n) rest)`
   - the same for major 2 with `(append (fn-bpc-argument 2 (len bs)) bs rest)`
   - the same for major 3
   - an array lemma conditioned on the inner `:list` decode, and a `:list` step
     lemma conditioned on the item and tail decodes.
   Each gets `:hints (("Goal" :expand ((fn-bpc-dec flg count <that exact
   term> budget))))`, which matches syntactically where the `:free` form may not.
3. The whole-book iteration cost under contention is 15-25 minutes. Splitting
   the file so the 200-line arithmetic prefix certifies once would pay for
   itself after two iterations.

### 3.3 Hard-won theory-control facts (do not re-derive)

These cost several rounds each:

- **`arithmetic/top`'s `MOD-X-Y-=-X+Y-FOR-RATIONALS` is a `:generalize` rule**
  that *introduces* `mod` terms into case trees that had none, and loops the
  waterfall. `(disable mod)` does not stop it. The book now carries
  `(local (in-theory (disable floor mod mod-x-y-=-x+y-for-rationals
  mod-x-y-=-x-for-rationals mod-minus mod-bounded-by-modulus integerp-mod
  rationalp-mod mod-type floor-mod-elim cancel-mod-+-basic cancel-floor-+-basic
  rewrite-mod-mod rewrite-floor-mod floor-floor-integer floor-=-x/y mod-=-0)))`
  immediately before the streaming decoder, and the same one-rule disable was
  added defensively to `bp-primary.lisp`, `bp-fragment.lisp`,
  `bp-fragment-invariants.lisp` and `clock-invariants.lisp`.
- **The decoder must not use `floor`/`mod` to split the head octet.** It was
  originally `(floor head 32)` / `(mod head 32)`; it is now range comparisons
  (`(< head 32)`, `(and (< 63 head) (< head 96))`, …) exactly as
  `books/cbor.lisp` dispatches, and the per-major-type head lemmas are stated
  with the literal subtraction (`(+ -64 (car (fn-bpc-argument 2 n)))`) so that
  they match the goal. A single general lemma whose left-hand side contains
  `(* 32 major)` does **not** match when `major` is a literal in the goal.
- **`append` associativity is not a named rule in this ACL2 image.** The book
  defines `fn-bpc-append-associativity`, plus `fn-bpc-car-of-append`,
  `fn-bpc-cdr-of-append`, `fn-bpc-consp-of-append`, `fn-bpc-append-nil`,
  `fn-bpc-len-of-append`, `fn-bpc-take-of-append`, `fn-bpc-nthcdr-of-append`.
- **Do not enable `fn-cbor-result-okp/value/rest` in the decoder's induction
  hints.** Unfolding them to `car`/`cadr`/`caddr` silently defeats every
  `fn-bpc-*-rest-are-octets` and `*-value-is-natural` rule. The book instead
  proves `fn-bpc-fields-of-ok`, `fn-bpc-fields-of-error` and
  `fn-bpc-results-are-true-lists` and keeps the accessors closed
  (`local (in-theory (disable ...))`).
- **Guard proofs ask for `rationalp` and `acl2-numberp`, not just `natp`.**
  The `*-is-natural` lemmas each carry `natp`, `integerp`, `rationalp`,
  `acl2-numberp` and `(<= 0 ...)` conjuncts for this reason.
- **`fn-bpc-enc` and `fn-bpc-dec` need `:verify-guards nil`** plus a later
  `verify-guards`, because their guard obligations need properties of
  themselves.
- The book exports the base-256 conversions **disabled**
  (`fn-bpc-u32-octets`, `fn-cbor-u16-bytes`, `fn-cbor-u32-bytes`,
  `fn-bpc-u64-bytes`, `fn-cbor-u16-from`, `fn-cbor-u32-from`, `fn-bpc-u64-from`,
  and the `fn-bpc-u32-octets-agree-with-fn-cbor-u32-bytes` rewrite) with their
  inverse, length and octet lemmas exported enabled. `bp-primary.lisp`
  re-enables them in the two hints that need them
  (`fn-bpp-block-crc-width`, `fn-bpp-crc-octets-length`). If that export turns
  out to hurt, make the `in-theory` local.

## 4. NOT STARTED

Nothing in the packet is unwritten. Everything is written and committed; what
is missing is **certification of every book**, and consequently:

- no `make certify` gate has been run with the new roots;
- the tails the packet asks for in `HANDOFF.md` do not exist;
- `specs/bp-primary.md` and `specs/time.md` describe the theorems in the
  present tense. **If any named theorem does not certify, those sentences must
  be corrected before the lane lands** — they are currently claims about
  statements, not about certified results, and the specs do not say so.
  `HANDOFF.md` does say so.

## 5. Design decisions, and why

1. **Prefix `fn-bpf-`, not the packet's `fn-bp-fragment` / `fn-bp-reassemble`.**
   `fn-bp-` is already registered in `docs/prefixes.md` for the sender workflow
   books; reusing it would make the registry ambiguous. `fn-bpf-` matches
   `fn-bpa-`, `fn-bpi-`, `fn-bpo-`, `fn-bpr-`. `fn-clock-` was free and is used
   as the packet named it.
2. **Bundle identity takes the payload length as an argument.** RFC 9171 §4.3.1
   (under Creation Timestamp) says identity is source node ID + creation
   timestamp + "(if the bundle is a fragment) the fragment offset and **payload
   length**". The packet said "total ADU length". Payload length lives in the
   payload block, not the primary block, so **the primary block alone does not
   determine a fragment's bundle identity**. The model keeps `fn-bpp-adu-key`
   (the §5.9 reassembly key, fully determined by the primary block) apart from
   `fn-bpp-bundle-id` (which takes the payload length).
3. **The packet's section numbers for lifetime (§4.2.8) and the fragment fields
   (§4.2.9) do not exist.** RFC 9171 §4.2.8 is Block-Type-Specific Data; both
   fields are specified in §4.3.1. The books and specs cite the RFC's own
   numbering.
4. **`fn-bpp-blockp` accepts what the wire allows; `fn-bpp-flags-conformantp`
   carries the two §4.2.3 MUSTs separately.** A peer that violates a MUST then
   produces a decodable block plus a policy decision, rather than a parse
   failure indistinguishable from corruption.
5. **Reassembly is specified index-wise, not as a fold.** Order-independence is
   then structural rather than a permutation theorem. The cost is
   `total x fragments` cell computations (at most 65536 x 64); a production
   reassembler needs an interval structure refined against this specification,
   not this function executed directly. Stated in the book and in
   `specs/bp-primary.md`.
6. **A conflict is reported in preference to a gap.** A peer that contradicts
   itself is a different event from a peer that has not finished sending.
7. **The clock decision prefers the Bundle Age path whenever an anchor exists**,
   which is stronger than RFC 9171 §5.5's MUST (it only requires the age block
   when the clock is inaccurate), because the age path needs no clock agreement
   at all.
8. **"Later observation of the same clock" is defined as: the monotonic counter
   has not gone backwards *and* the earliest admissible true time has not gone
   backwards.** A resynchronisation that widens the error bound enough to move
   the earliest admissible time backwards is deliberately *not* a later
   observation — a node that discovers its clock was wrong is allowed to stop
   being sure.
9. **`*fn-bpc-max-bytes*` is 64, not 65535.** The only byte string RFC 9171
   §4.3.1 puts in a primary block is the CRC. Keeping the item bound small is
   what makes the whole-block length bound (1033 x 59 = 60947) fit inside the
   65536-octet input preflight.
10. **Assumptions are not named `A-*`.** The honesty of the host's
    `wall-error-bound` and the Bundle Age block's lower-bound property are
    carried as explicit theorem hypotheses. `books/assumptions.lisp` does not
    exist, and the assurance rules forbid prose that pretends to be an
    assumption artifact; these belong to the C1-15 packet.
11. **Definitional lemmas are named `-by-definition` / `-by-construction`** so
    the registry cannot cite them as proof events:
    `fn-bpp-adu-key-ignores-destination-lifetime-and-crc-type-by-definition`,
    `fn-bpp-adu-key-separates-source-and-timestamp-by-definition`,
    `fn-bpp-bundle-id-of-fragment-uses-payload-length-by-definition`,
    `fn-bpp-bundle-id-of-non-fragment-ignores-payload-length-by-definition`,
    `fn-bpp-anonymous-source-is-not-identifiable-by-definition`,
    `fn-bpp-accepted-input-is-canonical-by-construction`,
    `fn-clock-drop-permission-is-exactly-expired-by-definition`.
    The identity keystone is `fn-bpp-encode-is-injective`.

## 6. CRC vectors used, and their sources

RFC 9171 §4.2.1 names two algorithms and gives no vectors; it points at [CRC16]
for X-25 and at RFC 4960 for CRC32C. Two independent sources are used, both in
`tests/acl2/bp-primary-tests.lisp`:

**(a) Catalogue check values** for the exact parameter sets §4.2.1 names, over
the ASCII string `123456789` (octets 49 50 51 52 53 54 55 56 57):

- CRC-16/IBM-SDLC (X-25): `0x906E` = 36974
- CRC-32/ISCSI (CRC32C): `0xE3069283` = 3808858755

**(b) Pinned-implementation vectors.** `tests/bp-dtn7/pin.json` pins dtn7-rs at
revision `4daf02d7ea927e9293753b2a5c4497457f6e5a40`, release 0.21.0. That
revision's `Cargo.lock` pins crate `bp7` **0.10.7**, checksum
`d0dd4a4f935d4040f93aa8b0ccda0ce210911631673ee62a35efba619954b937`. The crate
source is at
`~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/bp7-0.10.7/`. Its
`doc/encoding_samples.md` publishes one primary block with CRC 16 ending
`42 e7ca` and the same block with CRC 32 ending `44 ca4fc368`. The test book
computes both over those exact octets with the CRC field zero-filled, which is
the input §4.3.1 prescribes:

```
CRC-16 input (decimal):
137 7 0 1 130 1 104 110 50 47 105 110 98 111 120 130 1 98 110 49
130 1 98 110 49 130 25 9 38 2 26 3 147 135 0 66 0 0      -> 59338 = 0xE7CA

CRC32C input (decimal):
137 7 0 2 130 1 104 110 50 47 105 110 98 111 120 130 1 98 110 49
130 1 98 110 49 130 25 9 38 2 26 3 147 135 0 68 0 0 0 0  -> 3394225000 = 0xCA4FC368
```

Both were reproduced independently with a Python reference implementation
before being written into the book.

**Important caveat, recorded in the test book and in `specs/bp-primary.md`:**
that sample block's `dtn` endpoint IDs carry the SSP **without** its leading
`//`. The same crate's `src/eid.rs` encodes the complete SSP — its own decoding
test reads `82 01 6c "//node1/test"` back as `dtn://node1/test`, and its parser
normalises the bare name `node1` to the SSP `//node1/`. The shipped
documentation is stale relative to the code it ships with. RFC 9171 §4.2.5.1.1
requires the complete SSP; fn implements the RFC form and **refuses that sample
block as a block** while still checking its CRC exactly. No byte-level block
interoperability with dtn7-rs is claimed from a stale document.

**(c) fn's own block vectors**, hand-derived from §4.3.1 and §4.2.5.1 (array
head, field order, argument widths) and asserted against the encoder in both
directions:

```
A  CRC-16, dtn EIDs, not a fragment, arity 9
   flags 0, crc 1, dest dtn "//n2/inbox", src/report-to dtn "//n1/",
   creation 2342 seq 2, lifetime 60000000
   137 7 0 1 130 1 106 47 47 110 50 47 105 110 98 111 120
   130 1 101 47 47 110 49 47 130 1 101 47 47 110 49 47
   130 25 9 38 2 26 3 147 135 0 66 3 151

B  CRC32C, ipn EIDs, creation timestamp needing CBOR additional info 27, arity 9
   flags 0, crc 2, dest ipn 23.42, src/report-to ipn 23.0,
   creation 1577836800000 seq 7, lifetime 86400000
   137 7 0 2 130 2 130 23 24 42 130 2 130 23 0 130 2 130 23 0
   130 27 0 0 1 111 94 102 232 0 7 26 5 38 92 0 68 87 208 145 118

C  fragment, CRC-16, arity 11, offset 1024, total ADU length 4096
   139 7 1 1 130 1 106 47 47 110 50 47 105 110 98 111 120
   130 1 101 47 47 110 49 47 130 1 101 47 47 110 49 47
   130 25 9 38 2 26 3 147 135 0 25 4 0 25 16 0 66 28 184

D  CRC type 0, dtn:none everywhere, flags 4 (must not be fragmented), arity 8
   136 7 4 0 130 1 0 130 1 0 130 1 0 130 0 1 26 0 54 238 128
```

Negative vectors in the same book: a single flipped CRC octet (`:crc-mismatch`),
a non-minimal spelling of the version field (`:noncanonical`), version 8
(`:malformed`), an arity that disagrees with the fragment flag, trailing octets
(`:trailing`), and a dtn SSP that is not a conforming dtn-hier-part.

**No ION vector was used.** No ION source or documentation is on this machine
and no fetch beyond the three RFCs was permitted, so the lane makes no statement
about ION beyond quoting RFC 9171 §4.2.5.1.1's own warning that the dtn-scheme
rules "impose constraints ... that were not imposed by [RFC 5050]".

## 7. RFC sections modeled

| Section | What |
| --- | --- |
| §4.2.1 | CRC type 0/1/2 and no others |
| §4.2.2 | CRC over the block with the CRC field zero-filled; 2 or 4 octets, network byte order |
| §4.2.3 | Bundle processing control flags as a 64-bit bit set; the two MUSTs as `fn-bpp-flags-conformantp` |
| §4.2.5.1, §4.2.5.1.1, §4.2.5.1.2 | Endpoint IDs, `dtn` including `dtn:none`, `ipn` |
| §4.2.5.2 | Node IDs (`fn-bpp-eid-node-idp`) |
| §4.2.6 | DTN time, milliseconds since 2000-01-01, zero means unknown |
| §4.2.7 | Creation timestamp and its role in identity |
| §4.3.1 | The primary block: field order, arity 8/9/10/11, lifetime, fragment offset, total ADU length, the CRC rule |
| §4.4.1, §4.4.2, §4.4.3 | Previous Node, Bundle Age, Hop Count — block-type-specific data only |
| §5.5 | Bundle expiration; age from the timestamp only with a non-zero timestamp and an accurate clock |
| §5.8 | Fragmentation constraints, including that fragments keep the source node ID and creation timestamp |
| §5.9 | Reassembly by material extents; overlapping subsets are normal |
| RFC 8949 §4.2.1 | Deterministic encoding: definite lengths, shortest argument |

Explicitly **not** modeled: §4.2.4 block processing control flags, §4.3.2 the
canonical block format, the payload block, §6.1 status reports, custody
(absent from BPv7 — RFC 9171 Appendix A is the reference), RFC 9172 BPSec and
RFC 9173 default security contexts, and lifetime overrides.

## 8. Gate commands and last results

| Command | Last result |
| --- | --- |
| `python3 tools/check_scaffold.py` (`make check`) | **passed**: `Scaffold OK: 78 Markdown files, 49 requirements, 18 proof targets, 18 scenario specifications.` Run after all files were in place |
| `make certify` at base `0bd0b5c`, no new roots | **did not complete**: the runner's default 600 s per-book timeout was exceeded on `books/article-properties` under ten-lane contention; 106 of 113 roots certified, the seven `article-*` roots unfinished. Evidence `build/acl2/certify-20260919T033521Z-71924/`. Not a proof failure. The coordinator's later notice prescribes `FN_ACL2_TIMEOUT_SECONDS=1800` |
| `FN_ACL2_TIMEOUT_SECONDS=1800 make certify` with the new roots | **never run** |
| `certify-book "books/bp-primary-cbor"` | **failing**; best run reached form 101/~110, failing at `FN-BPC-DECODE-OF-ENCODE`; see §3.1 |
| every other new book and test book | **never submitted to ACL2** |

Tool versions: ACL2 8.7 on SBCL, `/opt/homebrew/bin/acl2` ->
`/opt/homebrew/Cellar/acl2/8.7_6/bin/acl2`, system books at
`/opt/homebrew/Cellar/acl2/8.7_6/libexec/books`, macOS arm64.

## 9. Known defects

1. **The `pkill -f acl2` incident** (§0). Other lanes lost in-progress runs.
2. **Nothing is certified.** Every theorem statement in this lane is a proposed
   theorem, not a theorem proved by ACL2.
3. **No host calls any of these functions.** Under the assurance rule that the
   theorem subject must be the function the host calls, every theorem here is
   about a function with no caller. No BPv7 conformance or interoperability
   claim may cite a host line.
4. `fn-bpf-reassemble` is quadratic by construction (§5.5 above).
5. The primary block alone does not determine a fragment's bundle identity
   (§5.2 above).
6. CRC type zero is representable but its RFC precondition (a BPSec Block
   Integrity Block targeting the primary block) is not checkable here; a
   zero-CRC primary block must be treated as unprotected by a policy above.
7. No resource-cost bound is proved for CRC computation; it is linear in the
   encoded block length, which the input preflight bounds, but that is prose.
8. The `must-fail` / `FAILURE_MARKERS` interaction is unverified (§2.5).
9. `specs/bp-primary.md` and `specs/time.md` describe the theorems in the
   present tense and must be corrected for anything that does not certify.

## 10. Proposals for the adapter

`tools/bpa_dtn7.py` carries a **BID**: bounded visible ASCII of at most 512
octets, read from the pinned agent's `/status/bundles` inventory and used as the
raw query argument of `/download?` and `/delete?`. Nothing in fn parses it. It
is an index into one agent instance's table. It cannot supply a source node ID,
a creation timestamp, a sequence number, a fragment offset or a payload length,
and it is meaningless to any other agent.

No host or tool file was touched by this lane. The proposals:

1. **Leave `bpa_dtn7.py` alone.** It is correctly transport-only. The change
   belongs one level up, in `tools/run_bp_receive.py`.
2. **Decode the primary block in ACL2, never in Python.** `run_bp_receive.py`
   already holds the bounded bundle bytes from `download_bundle`; send the
   leading octets across the existing decimal-octet bridge to a new
   `:program`-mode wrapper in `host/bp-receive-host.lisp` calling
   `fn-bpp-decode`. The assurance rule "one owner per decision, and it is ACL2"
   forbids a Python twin for the ADU key, the CRC or the canonical form.
   `tools/bpa_payload_extract.rs` may keep using the pinned upstream `bp7`
   decoder for the payload extent: it is already a declared trusted component
   and it computes no identity.
3. **Persist bundle identity, not the BID, in the receive context** — the ADU
   key and, when the fragment flag is set, the fragment offset and the payload
   block's length — in the FNRJ record, so it survives restart. The
   `max_transactions` check that review defect D1 found missing must cover the
   new path.
4. **Key duplicate recognition on bundle identity as well as the work-id.**
   That addresses review defect D10 (work-id squatting as a denial of service)
   with a key the peer cannot choose freely: §4.2.7's sequence counter belongs
   to the source BPA. `fn-bpp-identifiablep` says when that key exists at all.
5. **Reconcile a lost delete reply by identity**, which is review defect D14:
   with decoded primary blocks in the inventory, absence of a bundle with the
   recorded ADU key is evidence the delete landed, and presence under a
   different BID is evidence it did not.
6. **Carry the clock observation**: persist creation time, lifetime and a Bundle
   Age anchor with each staged bundle, call `fn-clock-expiry-decision` before
   forwarding, keep `:uncertain` from deleting anything, and keep the three
   outcomes distinct at the CLI exit status (the discipline review defect D13
   asks for on the store paths).
7. **Fragment carriage**: the receive context must carry the offset and payload
   length and the reassembly buffer must be keyed by `fn-bpp-adu-key`;
   `books/bp-fragment.lisp` has no input until that exists.

## 11. Dirty and untracked files at the time of this dump

Before the WIP commit that carries this file:

```
 M HANDOFF.md
 M books/bp-primary-cbor.lisp
?? LANEDUMP-bp-primary-time.md
```

`books/bp-primary-cbor.lisp` is modified relative to `40d52e9` by the round-13
`:expand` hints on `fn-bpc-decode-of-encode` and
`fn-bpc-dec-reencodes-consumed-prefix`. `HANDOFF.md` is modified by the
"Commands run and results" section, whose "Certification status" subsection
still reads `RESULTS-PLACEHOLDER` — **that placeholder is deliberate and must be
replaced with the real outcome, not deleted.**

Everything else is committed: `141d0da` (RFC texts and `docs/references.md`) and
`40d52e9` (all seven books, three test books, two specs, `docs/prefixes.md`,
`Makefile`, `HANDOFF.md`).

Untracked build artifacts left in place for diagnosis and not committed:
`build/cbor5.log` .. `build/cbor15.log`, `build/certify-baseline.log`,
`build/acl2/certify-*/`.
