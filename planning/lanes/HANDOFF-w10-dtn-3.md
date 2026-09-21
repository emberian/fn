# Handoff: w10/dtn-3 — the record eliminator every codec needed, and the fold it unblocked

Branch `w10/dtn-3`, worktree `build/lanes/w10-dtn-3`, from `dev` at `34288c4`
and merged forward. Boxes, measured before every run: hbox
(`/tank/fn/lanes/w10-dtn-3`, ACL2 `/tank/fn/acl2-8.7/saved_acl2`, cache
`/tank/fn/certcache`, always under `swarm-build`) and persvati
(`/home/ember/fn-lanes/w10-dtn-3`, ACL2 `$HOME/fn-tools/acl2-8.7/saved_acl2`,
cache `/home/ember/fn-certcache`). Two ACL2 runs on the laptop, both under a
second.

## 1. Packet 0 — `fn-defrecord` generates constructor-of-accessors (LANDED ALONE)

`books/defrecord.lisp` generated accessor-of-constructor and not its dual,
so every decode-of-encode round trip in this tree had a hand-written
eliminator under it: `fn-record-reconstruct`, `fn-snt-node-reconstruct`,
`fn-snt-acceptance-reconstruct`, `fn-bpa-request-fields-reconstruct`,
`fn-bpb-block-is-its-own-accessors`, each with its own name, its own
`:expand` list and its own rule class. The macro now generates it:

```lisp
(defthm <ctor>-of-accessors
  (implies (<shape> x)
           (equal (<ctor> (acc1 x) ... (accn x)) x)))
```

**Under the shape predicate, not the recognizer**, for two reasons a
recognizer-hypothesis form could not meet: a record declared `:recognizer
nil` (`fn-sched-result`) has no recognizer and still needs the lemma, and a
recognizer with `:recognizer-formals` (`fn-articlep`, `fn-pendingp`,
`fn-node-stagep`) would put a free variable in the rule's hypothesis. **It
still fires with the recognizer CLOSED** --- the only way a transition proof
may use it --- because `<recognizer>-forward-shape` now forward-chains
`(<shape> x)` beside `consp` and `true-listp`; the shape predicate stays
withdrawn, and the forward-chained literal relieves the hypothesis without
opening anything.

**There is no field shape it cannot do.** Tagged and untagged, every width:
the constructor writes the tag itself and the shape predicate pins
`(equal (car x) tag)`, so a tagged record rebuilds from its fields alone.
The `:expand` list of `(len (cdr^k x))` the proof needs is generated from
the record's width.

Teeth (`tests/acl2/defrecord-tests.lisp`): three rebuilds proved with the
recognizer disabled AT THE FORM (untagged, tagged, and the context-formal
record), and four concrete values on which the rebuild is not the original
--- wrong length, right length but not a true list, not a cons, a foreign
tag --- with the admitted witness beside them so none is vacuous.
`tools/ledger.py` mirrors both changes; `tests/test_ledger.py` pins the
statement and the new forward-chaining conjunct.

**The hazard it introduces, and the cure, because it cost this lane a
run.** The hand-written eliminators were `:rule-classes nil` and cited by
`:use`. The generated one is an ENABLED rewrite, so a `:use` of it adds a
hypothesis whose left-hand side is the rule's own left-hand side: the
rewriter collapses it to `(equal b b)` and the `:use` is gone before the
goal can use it. `fn-bpb-decode-block-of-encode-block` failed exactly this
way at `Subgoal 17.3'` (`build/acl2/certify-*`, the first profile run).
**Every `:use` of a `<ctor>-of-accessors` needs that rule in the `e/d`
disable list of the same hint.**

Certified, ACL2 8.7 / SBCL 2.6.8, all `passed`:

| where | run | evidence | books | note |
| --- | --- | --- | --- | --- |
| laptop | --- | `build/acl2/certify-20260920T213002Z-19121` | `books/defrecord` 0.13 s, `tests/acl2/defrecord-tests` 0.22 s | the macro and its teeth |
| persvati | `run-20260920T213144Z-7728` | `build/acl2/certify-20260920T213153Z-3503617` | 16 books, 63.92 s wall at `--jobs 4` | the named heavy users: `books/records` 8.04 s, `books/records-invariants` 51.01 s, `books/anchor` 1.91 s, `books/peer-config` 2.90 s |
| hbox | `run-20260920T213132Z-f558` | `build/acl2/certify-20260920T213139Z-1210785` | 7 books | `books/bp-primary-invariants` 632.25 s, `books/bp-primary-cbor` 54.03 s, `books/bp-bundle` 10.32 s |
| persvati | `run-20260920T214122Z-02f2` | `build/acl2/certify-20260920T214126Z-3601692` | **54 books**, 203.94 s wall at `--jobs 6` | the whole DTN image substrate: `books/tcpcl-octets` 133.92 s, `books/store-node-invariants` 71.35 s, `books/frame` 69.25 s, `books/tcpcl-session` 66.81 s |

That is 77 distinct books re-certified against the changed macro with no
statement edited anywhere and no regression. Ledger lint total unchanged at
236; `defthm` count +38 (one per record), `assert-event` +5, SUSPECT 45 to
44.

Landed alone on `dev` as `ab8816e` (+ board `6dd10da`), merged `fed697f`,
before any of the work below.

## 2. Packet 1 — the fold's round trip

`fn-bpb-decode-blocks-of-encode-blocks` was the one open form in
`books/bp-bundle-invariants` and the previous lane was killed on it at the
1200 s cap. **It closes in 0.05 seconds, 21,275 prover steps.**

The cause was never a missing fact, and no hint would have found it. The
form carried

```lisp
:induct (fn-bpb-decode-blocks
          (append (fn-bpb-encode-blocks xs) (cons *fn-bpb-array-break* rest))
          budget)
```

--- an induction on the DECODER applied to the encoded octets. The scheme
that generates has, in its induction hypothesis, the term
`(fn-cbor-result-rest (fn-bpb-decode-block (append ...)))`, which becomes
the subject of the hypothesis only AFTER the one-block keystone has fired on
it; so the hypothesis never matches the goal it is supposed to discharge and
the search does not terminate. Replacing it with a scheme over the block
list --- one block and one unit of budget per step, which is exactly the
recursion the goal has --- makes each step an application of the keystone:

```lisp
(local (defun fn-bpbi-blocks-induction (xs budget)
         (declare (xargs :measure (len xs)))
         (if (consp xs) (fn-bpbi-blocks-induction (cdr xs) (- budget 1))
           (list xs budget))))
```

with two local `append` facts (`consp` and `car` of an `append` whose first
argument is a cons) so that the break octet is distinguished from an encoded
block's head without opening `binary-append`.

**`tools/proof_profile.py` paid for itself twice on this form.** Its first
run did not profile the fold at all: it stopped at
`fn-bpb-decode-block-of-encode-block`, on `Subgoal 17.3'`, and that
checkpoint is the hazard packet 0 introduced --- see section 1. Its second
run named the fan: `fn-bpp-vchar-listp` and `fn-bpp-vcharp`, 1,527,614 and
1,369,220 frames with no useful application, the two largest runes in the
run, on a form about a canonical block that is not an endpoint ID.
Disabling those two at the keystone took the whole book's run to that point
from what had been a 1200 s cap to 129 s.

**Then the tail behind it ran for the first time, and the next keystone was
open too.** `certify-book` stops at the first failure, so "everything before
the fold proves" had never been a statement about `fn-bpb-decode-of-encode`:
that form had never been attempted. It fails on the branch where
`(fn-bpc-dec :item 0 (append (fn-bpp-encode primary) ...) 128)` is not `ok`,
which its `:use` of `fn-bpc-decode-of-encode` is meant to refute and cannot,
because the `:use` names `(fn-bpc-enc :item (fn-bpp-block-value b
(fn-bpp-block-crc b)))` while the goal contains `(fn-bpp-encode b)`. That
equality is `fn-bpp-encode`'s definition and
`books/bp-primary-invariants` keeps its copy of it (`fn-bpp-encode-unfolds`)
`local`, so this book has to restate it.

**Stated `:rule-classes nil` and cited by `:use`, it changed nothing** --- the
checkpoint came back byte-identical. An equality carried as a hypothesis is
not a normal form: the two terms never become the same term. It has to be a
REWRITE that is active at the form, so `fn-bpbi-bpp-encode-unfolds` is a
`local` rewrite, withdrawn on the line after it is proved and enabled in
exactly one hint.

**The measurement that nearly became a false claim, and the tool fix it
bought.** In between, `tools/proof_profile.py` reported this form with no
checkpoint and a 100.93 s Summary, which its own last line renders as "the
form closed, or it was cut by the step limit or the timeout". It had been
cut: the form needs about 10M prover steps (`certify-book` counted
10,058,074 for the book) and the tool's default is `DEFAULT_STEPS =
4_000_000`, so ACL2 aborted it with `ACL2 Error [Step-limit]` and printed no
key checkpoint --- indistinguishable, in that report, from success. The tool
now detects the marker and prints **CUT BY THE STEP LIMIT: the form did not
close and ACL2 printed no checkpoint because it was aborted, not refuted**,
naming `--steps`; `tests/test_proof_profile.py` pins it. A profile is not a
verdict, and until today it could read like one.

**What was actually wrong, in three measured layers.** The form is a
composition and each layer hid the next.

1. `(fn-bpp-encode primary)` and `(fn-bpc-enc :item (fn-bpp-block-value
   primary (fn-bpp-block-crc primary)))` are the same by definition and were
   not the same term. Fixed by the local rewrite above.
2. With the terms matched, the `:use`d lemmas still went unrelieved, because
   **`fn-bpp-blockp` had been opened**. `fn-bpb-bundlep` opens to a conjunct
   `(fn-bpp-blockp (fn-bpb-bundle-primary bundle))`, and with that recognizer
   enabled the conjunct becomes eleven `nth` hypotheses; the literal the
   three `:use`d lemmas hypothesise is then not in the goal at all and
   cannot be relieved. Closing `fn-bpp-blockp` at the form --- with
   `fn-bpp-eidp`, `fn-bpp-vchar-listp` and `fn-bpp-vcharp`, which are only
   reachable through it --- relieved all three AND removed the fan: the form
   went from 100.93 s and about 10M steps to **0.13 s and 45,658 steps**.
   This is `docs/proof-style.md`'s "never open a recognizer", costing a
   whole afternoon on the goal's HYPOTHESES rather than on its conclusion.
3. One element. The payload block is a field of the bundle, not the last
   element of its block list, so the fold is instantiated at
   `(append blocks (list payload))`; `fn-bpb-encode-blocks-of-append` splits
   that into `(append (fn-bpb-encode-blocks blocks) (fn-bpb-encode-blocks
   (list payload)))` while `fn-bpb-encode` wrote `(fn-bpb-encode-block
   payload)`. `fn-bpbi-encode-blocks-of-one`, local and enabled only at the
   form, is that one-element difference.

4. And then the composition itself. `fn-bpb-decode` is a scan, a fold and
   an assemble; with the fold proved and the primary's facts available, the
   remaining gap was the scan's `take`: `(take (- (len octets) (len after))
   octets)`, whose count is the head's length only after
   `fn-bpc-len-of-append` and a cancellation base ACL2 will not do inside a
   subterm. The cure is a decomposition, not arithmetic:
   **`fn-bpb-scan-primary-of-encode`** --- the primary block scans back out
   of a bundle image and what follows it is returned untouched, the same
   shape `fn-bpb-decode-block-of-encode-block` has one block down. It closes
   in 0.01 s and 2,459 steps, and `fn-bpb-decode-of-encode` is then two
   `:use`s and nothing else.

Two smaller measured facts worth keeping. `fn-bpbi-len-of-append-minus-tail`
is stated in BOTH argument orders because ACL2 sorts a sum by term order and
matches the rule against the sorted form; written one way round it does not
fire. And `fn-bpc-len-of-append` is deliberately DISABLED at the scan
keystone, so the count keeps the `(- (len (append a b)) (len b))` shape the
rule matches; enabled, it becomes a five-term sum nothing cancels.

**And the round trip found a defect in the codec, not in the proof.** At
`(len (fn-bpb-bundle-blocks bundle))` = `*fn-bpb-max-blocks*` = 32 the
theorem is FALSE as `books/bp-bundle` stood: `fn-bpb-splitp` admits 32
canonical blocks, the payload block is a thirty-third element of the array
on the wire (section 4.1 requires it last), and `fn-bpb-decode` budgeted
`fn-bpb-decode-blocks` at 32 --- so **fn's decoder refused fn's own
encoder's output with `:too-many-blocks`** for every bundle at the bound.
`fn-bpb-decode` now budgets `(+ 1 *fn-bpb-max-blocks*)`, which is the count
of blocks in the array rather than the count of canonical blocks; the bound
on canonical blocks is not loosened, because one more of them makes the
array two longer than the budget. `tests/acl2/bp-bundle-tests.lisp` gains
the witness at the boundary (a 32-block bundle that round-trips) and the
refusal one past it. No theorem was weakened to reach this: the statement
of `fn-bpb-decode-of-encode` is the one the previous lane wrote.

## 3. Packet 2 — what the round trip unblocked

**The image, the lab scenario and the dtn7 interop did NOT run, and nothing
is claimed for the `bp` verb or for dtn7 interoperability.** They are behind
`books/bp-node`, which is open at one guard conjecture. The substrate is
ready: 54 of the DTN image's closure certified on persvati
(`run-20260920T214122Z-02f2`) and `books/bp-bundle-invariants` certified on
hbox, so `books/bp-node` is the only root between here and
`tools/build_native_host.sh`.

**`books/bp-node` had never been attempted** --- the lane that wrote it was
blocked below it --- and with `books/bp-bundle-invariants` certified, every
event in it runs for the first time. All of them close except
`fn-bpn-receive`'s guard. Three things landed getting there, and the next
lane should not redo them:

- **`fn-bpn-expiry`'s guard** wanted `fn-bpb-bundlep` and `fn-bpp-blockp`
  opened at the form and the fragment BIT TEST (`fn-bpp-fragmentp`,
  `fn-bpp-flag-onp`) CLOSED: opened, the bit test puts `numerator` and
  `denominator` parity goals in front of a guard about times, and the
  branch it leaves is arithmetically false.
- **`fn-bpn-send`'s guard** is keystone K5 (`fn-bpn-send-bundle-is-a-bundle`)
  and nothing else, because `fn-bpb-encode` is guarded by `fn-bpb-bundlep`.
  It is now deferred at the definition and discharged at K5, which is the
  caller-discharges-the-callee pattern of `docs/proof-style.md` section 4;
  K5 itself needed the bundle and block recognizers opened and the
  endpoint-ID vocabulary closed.
- **Three local bridges** carry `fn-bpb-decode-yields-bundle` to the
  primary's fields, `:rewrite` and `:forward-chaining` both, because the
  guard goals are in field vocabulary where `(fn-bpb-bundlep ...)` never
  appears.

**The one obligation left**, verbatim:

```lisp
(implies (and <fn-bpn-configp config, opened>
              (fn-cbor-result-okp (fn-bpb-decode octets limit))
              (fn-bpp-flags-conformantp
               (fn-bpb-bundle-primary
                (fn-cbor-result-value (fn-bpb-decode octets limit)))))
         (integerp
          (nth 1 (fn-bpb-bundle-primary
                  (fn-cbor-result-value (fn-bpb-decode octets limit))))))
```

`fn-bpp-fragmentp`'s guard on the primary's flags. Every fact available is
about `fn-bpp-blockp` or `(fn-bpp-flags p)`, and the goal is about
`(nth 1 p)`: **`books/bp-primary` ships its accessors with their
`:definition` runes ENABLED** --- six of the 26 the new `enabled_projection`
lint counts are in that book --- so the accessor is gone from the goal
before any rule can match it. Forward-chaining triggered on the projection
does not help, because the projection is opened too. Repairing that lint in
`books/bp-primary` (one name in its closing `deftheory`) is probably the
whole fix, and it belongs to that book's owner; it is not a change this lane
should make inside someone else's export policy at the end of a shift.

## 4. Packet 3 — the §1.5 machine, named and not started

`books/bp-node.lisp` is two ends of the machine of `specs/bp-design.md`
section 1.5, not the machine, and section 1.5.1 of that spec already lists
what is absent. Not started, and this is what starting it would mean.

**What the machine adds that the two ends do not have.** `fn-bpn-send` and
`fn-bpn-receive` are pure functions of a configuration and some octets;
neither has a STATE. The machine is `(fn-bpn-step st event) -> (st'
effects)` over `fn-bpn-make-state (config bundles reassembly next-seq
reports)`, and everything the two ends cannot express lives in that state:

- the bundle store, so a received bundle can be held, retried, expired and
  deleted rather than decided once and dropped;
- the reassembly alist, so `fn-bpn-receive` can stop refusing a fragment
  with `:fragment-not-reassembled` and call `books/bp-fragment`, which is
  certified and has no caller;
- `next-seq`, the durable creation-timestamp frontier of section 1.3 with
  its FNBS `(:bpn-sequence n)` record, which is the one thing that makes
  `bp send` restart-safe: today `host/native/bp.lisp` takes the sequence as
  an argument and says in its own header that a restarted operator must not
  reuse one;
- the status-report intents of section 6.1.1, so a received administrative
  record becomes a transport observation instead of an ADU;
- dispatch, so local delivery is decided against forwarding.

**What it would need that does not exist.** Three things, in order. (a)
The FNBS record family in `books/frame` and its journal, because every
`(:persist record)` effect must be barriered before the next step --- this
is the same shape as FNWF and `books/frame-journal`, and until it exists
`fn-bpn-step` can be written but not run by the host. (b) A join to
`books/scheduler` for `(:contact peer open-p)` and to `books/bp-receipt`
for `(:deliver ...)`: both are certified and neither is in the DTN image's
build list. (c) A trace function and its preservation keystone
(`fn-bpn-trace`, `fn-bpn-step-preserves-statep`) before any of T1 to T6 has
a subject; T1 to T6 are stated in section 1.6 against `fn-bpn-step` and are
**not proved, and nothing in this tree claims them**.

The honest first packet is (a) alone, because it is the one that changes a
claim: with the durable frontier, `bp send` stops carrying a
restart-unsafety note in its own header.

## 5. Per-root table

| root | verdict | run / evidence | note |
| --- | --- | --- | --- |
| `books/defrecord` | CERTIFIED | laptop `certify-20260920T213002Z-19121` | 0.13 s |
| `tests/acl2/defrecord-tests` | CERTIFIED | laptop `certify-20260920T213002Z-19121` | 0.22 s, the new teeth |
| `books/records`, `books/records-invariants`, `books/anchor`, `books/peer-config` and their closure (16 roots) | CERTIFIED | persvati `run-20260920T213144Z-7728` / `certify-20260920T213153Z-3503617` | packet 0 regression |
| the DTN image substrate (54 roots, `books/replay` to `books/tcpcl-session`) | CERTIFIED | persvati `run-20260920T214122Z-02f2` / `certify-20260920T214126Z-3601692` | 203.94 s at `--jobs 6` |
| `books/bp-primary-cbor`, `books/bp-primary`, `books/bp-primary-invariants`, `books/cbor`, `books/cbor-invariants` | CERTIFIED | hbox `run-20260920T213132Z-f558` / `certify-20260920T213139Z-1210785` | `bp-primary-invariants` 632.25 s |
| `books/bp-bundle` | CERTIFIED | hbox `run-20260921T003648Z-4dae` / `certify-20260921T003651Z-1346980` | 7.65 s; the block-budget fix |
| `books/bp-bundle-invariants` | CERTIFIED, two forms removed open | same run | 22.26 s; `fn-bpb-decode-of-encode` 1.27 s / 719,428 steps, the fold 0.05 s / 21,275 steps, `fn-bpb-scan-primary-of-encode` 0.01 s / 2,459 steps |
| `tests/acl2/bp-bundle-tests` | CERTIFIED | same run | 0.71 s, 50 assertions; two of them had never run and were WRONG (below) |
| `books/bp-node` | OPEN at one guard conjecture | hbox `run-20260921T002350Z-2a95`, then local `ld` iteration | the obligation is quoted in section 3 |
| `tests/acl2/bp-node-tests` | NOT ATTEMPTED | --- | fails at `(include-book "../../books/bp-node")` |
| `build/fn-host-dtn` | NOT BUILT | --- | needs `books/bp-node`; its other 59 closure books are certified |
| `tools/tcpcl_lab.py --scenario adu` | NOT RUN | --- | needs the image |
| `tests/bp-dtn7/run_fn_bp_interop.py` | NOT RUN | --- | needs the image; **no claim about dtn7 interoperability follows from this lane** |

## 6. What the next lane should take

1. **The fan in `fn-bpb-decode-of-encode`.** 67 runes with no useful
   application and `(:TYPE-PRESCRIPTION LEN)` at 3,533,005 frames, in a form
   whose own reasoning is 24 steps of `:use`. The endpoint-ID vocabulary
   (`fn-bpp-eidp`, `fn-bpp-vchar-listp`, `fn-bpp-vcharp`) is in the goal only
   because `fn-bpb-bundlep` reaches `fn-bpp-blockp`; the same `e/d` cure that
   took the one-block keystone from a 1200 s cap to seconds applies, and it
   is the cheapest minute anyone will spend on this cluster.
2. **A `PRF-` row for the bundle codec.** `planning/proofs.json` has no
   `fn-bpb-*` target at all: the three keystones of
   `books/bp-bundle-invariants` are proved and unregistered. Claim the id on
   the board first (`dev` is at `PRF-031` as of this lane).
3. **The FNBS record family and the `(:bpn-sequence n)` frontier**
   (`specs/bp-design.md` section 1.3), which is packet 3's item (a) and the
   one open item that changes a claim rather than adding a feature.
4. **The outbound-suffix obligation of `specs/tcpcl.md` section 6**, still
   untouched by any lane.

## 7. Two test assertions that had never run, and were wrong

`tests/acl2/bp-bundle-tests.lisp` was written by the previous lane against a
book that did not certify, so every assertion in it ran for the first time
tonight. Two were false, and both are repaired to what the codec actually
does rather than the codec changed to match them:

- the "declared length above the per-block bound" witness spelled its
  byte-string head `26`, which is major type 0. It measured
  `:not-a-byte-string`, not `:limit`. The head is now `90` (= 64 + 26,
  major type 2 with a four-octet argument, RFC 8949 §3), and the original
  octets are kept beside it as the `:not-a-byte-string` witness, so the two
  refusals stay distinct.
- `(fn-bpb-decode (list 159 255) ...)` was asserted `:primary-block-refused`
  and is `:malformed`: the break octet is not the start of a CBOR item, so
  `fn-bpc-dec` refuses before `fn-bpp-decode` is reached. `(159 0 255)` is
  the witness for `:primary-block-refused`, because `(0)` IS a CBOR item and
  the scan hands it on.

Both values were measured by evaluation before the assertion was changed
(local ACL2 8.7, `tools/acl2`), not inferred.
