# fn2 layer C continuation (present state, rewritten whole after every commit)

Seat: Opus, layer C (the ordered-run metadata engine). Fifth seat since 2026-10-30. Method of
2026-10-29 (`briefs/FN2-SEAT-COMMON.md`): dev is the branch; Opus writes the code; Codex only for
bounded pieces with real signatures pasted; READY to main per commit (SendMessage to "main"). Brief:
`briefs/FN2-LAYER-C-ORDERED-RUNS.md`. Layer doc on dev: `fn2/docs/c-ordered-runs.md`. Box safety
verbatim in COMMON.

## Landed (all READY sent)
- Earlier seats: C1a 181df0df0, C1b 8dfba6db2, C1b' 1e823b06f, run assembly 1c603fcdd, C2a
  8db53928a, C2b c06369c9d, C2c 37a48f7d0, C2d 76b82807c, words d2f2ea9e8, C3a ab5662b34, C3b 439586224,
  C-S1 d21ffb2b3, C-S2 c0b4e158f (+945f625ad OWED).
- 91cf52deb (dev efec6d5c6) **machines-c red fixed**: C-SHAPE-READS (shape macros
  `fn2-idc-op-shape`/`fn2-idc-fn-shape` take a list of reads to fold; rehome 14.4 s -> 0.3 s) and
  C-SUCCESSOR-BOOK (`fn2/books/machines-c-successor.lisp` holds C-S2, includes machines-c; assembly-index
  includes it; assembly-callbacks-c calls `fn2-identity-core-events` and
  `fn2-identity-successor-core-events`). Whole-tree gate on forge: closure rc=0, export PASS, OWED unchanged.

- 34e106dca + 736247f3d (dev eff0ab945) **C4a**: fold declarations on the :schema row
  (`defrunschema :fold`, compiler `fn2-rf-*` in runs-schema.lisp, :program mode; generated
  NAME-FOLD-EVENTP and NAME-FOLD-APPLY in the declaration, the logic family beside it:
  -KEY -STEP -KEYP -KEYSP -ROWSP -STATEP -EVENTSP -VALUE -APPLY-SPEC -RUN -SPEC -OBSERVE -OBSERVE-ALL);
  `folds.lisp` (group counts 5, consumer cursor 6, principal charges 7; runs-served includes it);
  dispatcher `fn2-run-layout-merge`, `fn2-fold-apply`; overlay replace (`fn2-ov-reput`, ov-write REPL
  arg); `folds-served.lisp` (`fn2-fold-image`, `-bug` :plus1/:skip; keystones NAME-SUMMARY-ADEQUATE-KIND x6,
  NAME-SUMMARY-CUT x3); `tests/folds-unit.lisp` (teeth, in owed-export.lsp). Gate green at 34e106dca;
  OWED 411. The merged eff0ab945 (with dev's ba644c1de, A for D7) re-gated green on forge:
  closure rc=0, export PASS, OWED.md identical.

## Next
1. Shave machines-c-successor (32.4-35.0 s forge at load 7; fn2-idc-copy
   preserves ~4 s, publish-stamps preserves ~2.5 s, record-insert shape 2 s; try reads lists).
2. C4b, statement first: `fn2-select-materialize-equivalent` (INBOX §4.6). Sketch: list spec of
   streams (stream -> ascending (position . event)), registration edges (stream, start), the
   select-only reference (merge entries after max(cursor, start) by position, dedup per event with
   reasons, cut at a limit, next cursor); the materialized reader (inbox rows keyed (consumer, epoch,
   position) up to cov on materialized intervals, the source above cov and elsewhere); statement: for
   every policy assignment and materializer schedule the reader equals the reference. Teeth: a
   materializer that skips an entry; a reader trusting the fold above cov (two edges, one switch,
   tiny). CONSUMER checker `fn2/sim/check-consumer.lisp`. Folds: registration, read-state, edge-policy
   (interval lists may need a value kind beyond integers: decide), inbox as a :unique derived stream.
   C-S3 seam to D: fold write in D's transaction through the private successor (range read of the
   key, `fn2-fold-apply`, bind into the batch's private overlay; publish/drop as C-S2).
3. C1c when B lands GC2; C5; C6. `sim-layer-c-sweep.lsp` (10,000 seeds) not yet run on forge.

## Seam state
- B: GC2 inside B5 pending; B owes calls of `fn2-identity-publish`/`-drop` from its commit kind.
- D: D5 uses C-S1/C-S2. D6 will need range/seek core wrappers (not yet requested).
- A: A-S8 `fn2-pool-copy-across` replaces `fn2-idc-copy` (now in machines-c-successor).

## Pitfalls
- Time a lemma in a world that INCLUDES certified books; an ld-built world keeps local theory events.
- Shape lemmas: fold reads that only feed checks/callee args; keep reads used as write indices.
- Generated defuns: no CL symbols as variables (`count`, `replace`, `state`).
- A teeth helper that recurses over a counter with big image calls in its body sent the measure
  proof into a 20-minute search: enumerate the cases at macro time instead (fn2-ft-cuts).
- REPL smoke of a changed library chain: ld include-stripped copies in order (drv6.lsp in scratch),
  then certify on forge; ld keeps local theory events, so times there are not cert times.
- Everything from earlier seats: child inits as functions; -preserves disables after first use
  (`:disable nil`); pool ops enabled globally; never edit a book inside a running cert chain;
  swarm-build scopes survive killing the wrapper.

## Commands that work
- REPL against certified books: from /Users/ember/dev/fn, `tools/acl2 --timeout N < drv.lsp`
  detached via python setsid with the PID in a file (scratch drivers in the session scratchpad).
- Forge: push HEAD to `fn@forge:/build/fn.git` as `fn2/c-found`; in /build/lanes/c: `git checkout -q
  -- . && git fetch -q /build/fn.git fn2/c-found && git reset -q --hard FETCH_HEAD`; start `sh
  build/c1.sh` under python setsid; PID in build/c1.pid (the setsid child = group leader). Results:
  build/c1-closure.out ("closure rc=0"), build/c1-export.out ("FN2-OWED-EXPORT PASS"); per-book
  times in fn2/books/*.cert.time.
- Landing: commit in c-found (`git commit --no-gpg-sign -F msg -- paths`), merge origin/dev, then in
  /Users/ember/dev/fn `git merge --ff-only fn2/c-found`, `python3 tools/secrets_check.py`, push.

## Certify times (forge, load ~7.5, 2026-10-30)
| book | s |
|---|---|
| machines-c | 10.7 |
| machines-c-successor | 28.7 (32.4 after C4a's ov-insert branch) |
| runs-schema | 1.9 |
| folds / folds-served / folds-unit | 14.5 / 3.9 / 4.0 |
| assembly-index | 8.3 |
| assembly-core (A's) | 51.9 |
| assembly-init | 36.1 |
| runs-served / range-served | 35.3 / 26.8 |

## C4 design (statement first): folds, their declarations, the summary cut

Sources: STORAGE-DESIGN §4 decision 1 (each fold names interpretation, initialization, coverage;
internal folds latest-only; the summary equation), scholar ch. 1 (fold initialization and coverage;
the summary-cut scenario: tiny exhaustive continuations), TRANSPORT §9 experiment A (the relational
two-representation contract; its two teeth), UC §2.1-2.4, INBOX §4.3-4.6.

### deffold

`(deffold NAME :id N :key ((field kind) ...) :value ((field kind) ...) :events ((KIND STEP) ...)
 :init INIT :coverage COV :observe OBS)` registers `(:fold NAME)` through `fn2-declare` and generates:
- the fold-row run schema `NAME-row` (`defrunschema`, `:merge :latest`, key = the fold's key), so a
  fold's materialized state is rows in overlays and runs like every other keyed structure;
- the interpretation in the logic: `NAME-step (value event) -> value` per event kind (the STEP
  functions are pure list functions on the row's value list), `NAME-spec (events) -> alist`, the full
  fold from INIT;
- INIT: `:empty` (history start: no row) or `(:from FN)` (a bootstrap from an existing summary,
  `F_new(H) = g(Summary(H))`, scholar ch. 1 item 12);
- COV: `:history-start`, or `(:from POSITION)` with the earlier range declared unavailable (never
  implied);
- OBS: the fold's observation, `(NAME-observe state query)`, the answers a summary must keep giving;
- the owed rows of the homomorphism certificate per event kind (`NAME-summary-adequate-KIND`):
  `obs(sigma s) = obs s` and `sigma(delta(s, e)) = delta_Sigma(sigma s, e)`, where sigma is the
  materialization (rows read back by the real scan) and delta_Sigma the real row update (overlay
  replace through the real insert), with TRANSPORT §9's two teeth per fold: (1) the observation as
  the relation is not step-closed (an observation-equal pair separated by one event, evaluated);
  (2) an off-by-one step (a mutated STEP) breaks the per-kind equation (evaluated witness).

### The overlay's replace for :latest (C-RANGE-NEWEST)

`fn2-ov-insert` refuses an equal key `:duplicate`. For a `:latest` schema an equal key replaces: the
new entry is encoded at the arena's fill and the index row at the key's position points at it (the
old bytes stay in the arena until the overlay is sealed; the arena's capacity is the bound).

### The folds

| fold | key | value | events | observation |
|---|---|---|---|---|
| group counts | group | count, low, high | article accepted into (group, number); withdrawal | GROUP's COUNT LOW HIGH |
| consumer cursor | (consumer, epoch) | position, registration version | ack (position), rebase | cursor position |
| principal accounts (durable half) | principal | charges by dimension | charge (dimension, amount) | charged total per dimension |
| registration, read-state, edge-policy | INBOX §4.3, §4.5 | | | |

### Keystones

- `fn2-fold-summary-adequate` per fold and event kind (above).
- `fn2-summary-cut`: for every cut k of a tiny event list (exhaustive in the tiny profile), the
  observations of `Fold(Summary_k, E_{k+1..n})` through the real engine (rows materialized at k,
  sealed or in an overlay, then the suffix applied by real row updates) equal the full fold's.
  Teeth: a summary that drops one row; a step applied twice at the cut.
- `fn2-select-materialize-equivalent` (INBOX §4.6), with the CONSUMER checker.
