# w9/proof-infra: the proof discipline, made mechanical

Branch `w9/proof-infra` from `dev` `52eb0db`, worktree
`build/lanes/w9-proof-infra`. Nothing here is a new proof obligation or a new
claim: every deliverable moves a convention out of prose and into something a
lane cannot forget.

## What exists now

| | | replaces |
| --- | --- | --- |
| `fn-defrecord`, `fn-defrecord-export` | `books/defrecord.lisp` | eleven to forty-one hand-written events per record |
| `fn-deftransition-closed`, `fn-deftransition` | `books/deftransition.lisp` | a floating `(local (in-theory (disable ...)))` and hand-wired branch lemmas |
| `tools/proof_profile.py` | one command | rediscovering `accumulated-persistence` on every slow form |
| hand-written-record lint | `tools/ledger.py` | nothing: the migration was invisible |
| `docs/proof-style.md` | rewritten | prose that a lane had to re-derive |

Both books have **no `include-book` and export no rule**: their plumbing is
`:program` mode, which has no definitional axiom, and they define only
macros. `fn-defrecord`'s output names `fn-ag-car`/`fn-ag-cdr` in the `:exec`
branch only, and `:car-fn`/`:cdr-fn` override them.

## `fn-defrecord`

```lisp
(fn-defrecord fn-sched-config
  :tag :fn-sched-config
  :constructor (fn-sched-config queue-bound aging-limit retry-bound)
  :fields ((fn-sched-queue-bound posp)
           (fn-sched-aging-limit posp)
           (fn-sched-retry-bound posp)))
```

Generates, in order: `<name>-shapep`; the constructor; one `mbe` accessor per
field with `:guard t :verify-guards nil` plus its `verify-guards`;
`<shape>-of-<ctor>`; one `<accessor>-of-<ctor>` per field;
`<ctor>-injective`; `<shape>-forward-shape`,
`<name>-accessors-forward-consp` (one `:forward-chaining` class per field,
triggered on the field term) and `<recognizer>-forward-shape`; the
recognizer over shape and accessors; `deftheory <name>-internals` of the
`:d` runes of shape, constructor and accessors, and its `in-theory (disable
...)`.

Decisions a later lane may want to revisit, each deliberate:

- **Injectivity is `:rule-classes nil`.** An enabled rewrite on every
  constructor equality is exactly the class of rule proof-style section 7
  forbids, and it would have changed the theory scheduler's keystones were
  proved in. `:injective :rewrite` asks for the rule and is a decision to
  defend in the asking book.
- **Accessor names are given in full.** The tree does not derive them
  (`fn-sched-config` has `fn-sched-queue-bound`), so deriving them would have
  forced renames across the host.
- **The `:logic` body is `(car (cdr^i x))`, not `(fn-bp-nth i x)`.** Both are
  the same function; the chain needs no import and matches the acceptance
  cluster. Scheduler's five records changed `:logic` bodies this way with no
  downstream effect, because their `:d` runes are withdrawn on the spot and
  nothing in the tree enables them.
- **A field type may be a term over `x`**, so
  `(or (null (fn-sched-open-contact x)) (fn-sched-contactp ...))` needs no
  escape hatch; `:extra` carries whole-record conjuncts; `:recognizer nil`
  suppresses the recognizer for a record that has none.
- **No layout but `:positional`.** Anything else is a hard error at
  expansion. The tagged form puts a keyword at index 0 and shifts the fields
  by one, which is what `books/records.lisp` and the host CBOR codec already
  encode, so **no host encoding moved** --- `fn-drt-mark-unfolds-to-a-tagged-list`
  and `fn-drt-point-unfolds-to-a-list` prove both layouts equal to the `list`
  call they replace.

**Acceptance test.** `books/scheduler.lisp`'s five records (contact, config,
item, state, result) are now five `fn-defrecord` forms and two
`fn-defrecord-export` forms: 1265 lines to 972. `books/scheduler-invariants`
and `tests/acl2/scheduler-tests` recertified with **no hint added**. Checked
mechanically (reader diff against `dev:books/scheduler.lisp`): no theorem and
no function was lost; five `<ctor>-injective` names are added; the only
statements that differ are the thirty `<accessor>-of-<ctor>` record lemmas,
which are alpha-variants --- the constructor's formals are now
`(work-id class size seq passes agedp expiredp)` where the hand-written
lemmas wrote `w c s q p a e`. No keystone statement changed. The only
reordering: `fn-sched-classp` moved above the item record, because the macro
emits the recognizer inside the record's block.

## `fn-deftransition`

```lisp
(fn-deftransition-closed fn-tcl-session-closed
  (fn-tcl-sessionp fn-tcl-next fn-tcl-with-outbound))

(fn-deftransition fn-tcl-refuse-preserves-sessionp
  :statement (implies (and (fn-tcl-sessionp s) (fn-clock-timep now))
                      (fn-tcl-sessionp
                       (fn-tcl-result-session (fn-tcl-refuse s xfer-id reason now))))
  :closed (fn-tcl-session-closed)
  :opens (fn-tcl-refuse))
```

`:statement` is passed through unedited. What the macro adds is the theory,
`(e/d <opens> <closed>)` pinned at the form instead of inherited from
wherever the last `in-theory` happened to sit, and, for each `:branches`
entry `(<lemma-name> <branch-test> <claim>)`, a local `:rule-classes nil`
lemma proved in the same theory whose name is appended to the lift's `:use`
--- so a generated branch lemma cannot be left as decoration.

**Honest note on the applied example.** `fn-tcl-refuse` has no non-affecting
branches, so the tcpcl application exercises the closed theory and the lift
but not `:branches`. The branch generator is exercised end to end on a
three-branch transition (`fn-drt-recolor`) in
`tests/acl2/defrecord-tests.lisp`, together with the content lemma proved at
the constructor with the recognizer open --- the one part the macro does not
and should not write.

## `tools/proof_profile.py`

    python3 tools/proof_profile.py books/scheduler \
        fn-sched-step-preserves-statep --host hbox

Builds a driver from the book's own source up to the named form (so the form
runs in exactly the theory the book builds for it, with dependencies coming
from the box's certificate cache), runs it under `(accumulated-persistence
t)` with a step limit, and prints: the top rules by frames with **no useful
application** (the fan), the top by frames overall, the top by tries, the
form's Summary line and prover steps, and the first key checkpoint if it did
not close. With no `--host` it picks the less loaded of persvati and hbox
from one `ssh host uptime` each; hbox runs under `swarm-build`. `--log
<file>` re-renders a saved log and `--dry-run` prints the driver.

**What it does not invent.** ACL2 attributes frames and tries per rune and
time only per form. There is no per-rule time figure, so the tool reports the
form's own Summary and says so in its output. This is a deviation from the
lane brief's "top ten by time", recorded rather than faked; frames are the
per-rule cost proxy.

`tests/test_proof_profile.py` (21 tests) pins the parser against two **real**
ACL2 8.7 logs in `tests/vectors/` --- `proof-profile-closed.log` and
`proof-profile-checkpoint.log` --- produced by the driver this tool writes.
ACL2's listing header does not name its sort key, so the driver prints its
own `FN-PROFILE-SECTION` markers; a log without them falls back to the order
the driver issues the listings in, and that fallback is tested.

## The fifth lint

A book with a shape predicate and three or more one-argument selector
accessors over the same variable is WARN. Both flavours in the tree count:
the `mbe` `car`/`cdr` chain (`books/acceptance.lisp`) and the
`(fn-bp-nth 1 x)` call (the bp books). One finding per book, so the accessor
count is unambiguous.

**24 books**, largest first: `books/tcpcl-records.lisp` (15 shape predicates,
62 accessors), `books/bp-receipt.lisp` (4, 19), `books/bp-ingress.lisp` (2,
14), `books/checkpoint-publish.lisp` (3, 13), `books/acceptance.lisp` (2 at
12 plus 1 at 6), `books/anchor.lisp` (4, 10), `books/node.lisp`,
`books/peer-inbound.lisp`, `books/records.lisp`, `books/owner.lisp` (5 shape
predicates, 6 accessors) and the rest. That is the migration queue, in cost
order.

The ledger reader also had to learn `fn-defrecord`. Without the expansion a
migrated book loses forty names from `definitions` (host-names then calls
every accessor the bridges use undefined), its recognizers never reach
`disabled_rules` (include-hygiene then warns about every includer), and its
guard and theorem counts fall. `tests/test_ledger.py` gained 17 tests
pinning that expansion and the lint; the Lisp side is proved by
`tests/acl2/defrecord-tests.lisp`.

One principled exemption came with it: a book with no theorems, no includes
and only `:program`-mode functions has **no rule to export**, so a non-local
include of it cannot cost an includer one. That is what makes `defrecord` and
`deftransition` includable without a WARN, and it is deliberately tight --- an
include-only shim does not qualify.

## Numbers

| | dev `52eb0db` | this branch |
| --- | --- | --- |
| Lint warnings | 234 | 259 |
| export hygiene / include hygiene / host names | 67 / 86 / 81 | 67 / 87 / 81 |
| hand-written record | n/a | 24 |
| Functions with verified guards | 1294 | 1325 |
| SUSPECT by shape | 32 | 34 |
| `books/scheduler.lisp` | 1265 lines | 972 |

The two new SUSPECTs are `fn-drt-mark-unfolds-to-a-tagged-list` and
`fn-drt-point-unfolds-to-a-list`, the layout audits in the new test book.
They are definitional restatements, named `-unfolds` and kept
`:rule-classes nil` for exactly that reason (proof-style section 7); SUSPECT
is the correct reading of them. The +1 include hygiene is
`tests/acl2/defrecord-tests` including `acceptance-alloc`, which exports
everything by design.

## Evidence

- persvati, ACL2 8.7, `ACL2_BOOK_HASH_ALISTP=NIL`, farm
  `run-20260920T180049Z-cffc`, evidence
  `build/acl2/certify-20260920T180054Z-1462292`, exit 0: `books/defrecord`,
  `tests/acl2/defrecord-tests`, `books/scheduler`,
  `books/scheduler-invariants`, `tests/acl2/scheduler-tests` and their
  closure (cache install: 164 installed, 0 kept, 59 uncached).
- hbox, ACL2 8.7, farm `run-20260920T180725Z-ca18` (cache install: 177
  installed, 3 kept, 60 uncached): `books/deftransition`,
  `books/tcpcl-session`, `books/tcpcl-invariants`, `tests/acl2/tcpcl-tests`
  and the re-run of `tests/acl2/defrecord-tests`. **See the final board note
  for its verdict.**
- `make check` green. `python3 -m unittest tests.test_ledger
  tests.test_proof_profile`: 91 tests, all pass.
- `python3 tools/ledger.py --write` run; `planning/ledger.md` and
  `planning/ledger.json` are current.

Root's mid-lane direction was to move all certification to hbox. The persvati
run above was already in flight when that arrived and was left to finish
rather than redone; everything after it went to hbox.

## For the next lane

1. **Migrate a cluster, in the lint's cost order.** `books/tcpcl-records.lisp`
   is the single largest win (15 records, 62 accessors) and is a pure
   records book, so its blast radius is its own cluster. The recipe is this
   lane's scheduler commit: replace the block, hoist any predicate the
   recognizer needs above the form, recertify the cluster, check the
   keystones' statements are byte-identical.
2. **`fn-deftransition` wants a real dispatcher.** `fn-sched-step` (seven
   event branches) and `fn-tcl-drive` are where `:branches` earns its keep;
   this lane only proved the machinery works.
3. **Run `tools/proof_profile.py` on `books/nntp-effects.lisp:971`**
   (`fn-nntp-hdr-labelled-line-is-block-text`, 2598 s and 1.47e9 prover steps,
   board note w5/owner-followups). That is precisely the form the tool was
   written for and nobody has profiled it.
4. **Do not weaken a keystone to fit a macro.** `fn-deftransition` takes the
   statement unedited on purpose. If a record does not fit `fn-defrecord`,
   widen the macro or leave the record hand-written and let the lint count
   it; do not reshape the record.
