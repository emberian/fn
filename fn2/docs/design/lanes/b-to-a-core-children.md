# From layer B to layer A: two seams B3's commit machine needs (2026-10-28, B seat)

B3 found that a layer-B `defmachine` kind can be declared (B-MACHINE-SEAM: `machines-b.lisp` included by
machines-a.lisp before `(fn2-machine-index-events)`, continuations in `commit.lisp` included by
machines-a-run.lisp), but its continuations cannot do their work. Evidence: B3's report
`build/coordinator/fn2/lanes/b-quests/B3.REPORT.md` ("Required layer-A seam"); docs §10 of
`fn2/docs/b-durability.md` on fn2/b-durability 1f359447d.

## 1. Persistent core children registered by other layers (blocking)

The commit, checkpoint, cleaner and recovery machines call B's existing APIs, which take B's own
defcolumns stobjs: `fn2-extents` (allocator, alloc.lisp), `fn2-fc` (format-check.lisp), `fn2-b3`
(blake3.lisp), `fn2-fields` (layout.lisp), later `fn2-mk` (merkle.lisp). A continuation's signature is
`(id [budget] fn2-core)`, and `*fn2-core-children*` (core.lisp:13-26) is six fixed tables plus the
machine kinds. `with-local-stobj` per call loses state across yields and allocates; copying those
tables into commit columns would be an executable twin. So these tables must be children of `fn2-core`.

Request, in A's DSL (A's names and shape win; this is the contract B needs):
- A declaration, e.g. `(defcorechild fn2-core-extents fn2-extents :init (fn2-extents-init-for profile fn2-extents) :why "...")`,
  recorded in a table; core.lisp appends registered children to `*fn2-core-children*` after the machine
  kinds; `fn2-core-init` calls each child's `:init` (a function of `profile` and the child stobj, with a
  guard derivable from `fn2-core-profilep`); `fn2-core-wfp` and the child-shape facts include each
  child's `-wfp`; `reference-state.lisp` generates copy/difference for registered children too (it now
  lists `(fn2-pool fn2-ops fn2-machines fn2-control)` + machine names, line ~99).
- Registration must be possible from a book included before core.lisp (B would register in
  `machines-b.lisp` or a `core-children-b.lisp` that machines-a/core includes, as with the kinds).
- Capacities come from the profile (B adds profile keys for its table sizes; B's scenarios use a
  B-owned profile constant).

## 2. The observation router (fold into R5a's `:observes`, if still open)

B's observer must ACCUMULATE several completions harvested before the row runs again (several writes
in flight), so its observe continuation returns `(mv wake fn2-core)`, receives `reason`, and runs after
the router's kind/generation/not-free validation but BEFORE the generic `pending` decrement and the
scribe-style single event cell (machines-a-run.lisp:14-75 ignores `reason` and returns one stobj from
its cond). Exact op identity is not needed (event class + issued length + per-phase counts suffice).

## 3. Service 0 (not blocking)

The calendar's protected service 0 ("commit") runs nothing in `fn2-exec-service`; B will schedule commit
rows on principal 0 like the scribe unless A prefers to wire service 0 (with matching semantics in
reference.lisp's service runner).

Until item 1 lands, B3's machine, scenarios 13/14 and B5-B7 (all machines over these tables) wait.
B's HISTORY checker is committed (1f359447d) and does not wait.
