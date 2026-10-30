# fn2 layer D continuation (present state, rewritten whole; 2026-10-30 ~04:40 forge time, third Opus seat writing directly)

Seat: Opus, layer D (machines, scheduler over principals, accounting, NNTP over them). The seat WRITES
the code; Codex (second account) only for bounded pieces with real signatures pasted, every line read.
Brief: `build/coordinator/briefs/FN2-LAYER-D-MACHINES-NNTP.md`. Layer doc: `fn2/docs/d-machines-nntp.md`
on dev (section 4 is D3's design: 4.2 the machine, 4.3 the decision table, 4.5 the seam).

## Tree
- Shared tree `/Users/ember/dev/fn` on `dev`; commit by `git commit -F <msg> -- <paths>` (new files
  `git add -N`), never stage. D3 works in the worktree `build/lanes/fn2/d3-conn` (branch `fn2/d3-conn`)
  because conn.lisp joins the assembly (foundation edit): it lands on dev as one commit with the export
  green; non-assembly commits fast-forward dev from the lane branch.
- Forge clone `/build/lanes/d3` (`ssh forge`): push the lane branch to `fn@forge:/build/fn.git`, then
  `git pull --ff-only /build/fn.git fn2/d3-conn` there; rsync uncommitted files into `fn2/`. Whole closure
  certified there at 430a77b9a (R6a1 pulled since; assembly recertifies on the next run).
- Scratch: `build/d-seat/` (commit messages, parens.py).

## Done
| quest | commit | one line |
|---|---|---|
| D3 oracle | 67d678389 | fuzz oracle compares D3's 501 both ways (no DEFERRED list); 0 disagreements on 13,501 lines |
| D3 2/n | 20ecfc4fc (+ merge 90fd04369, OWED 9412139a1) | fn2-conn in the served core (conn.lisp, assembly-callbacks-d), owed-conn (T1, T8 fragmentation/privacy, reader-only interim), WIRE checker sim/check-wire.lisp, conn-unit (7 transcripts, every split, pairs, 24 random, WIRE controls), Q1 pin 67, OWED 331 |
| D2c | 56bcb0125 | fn2-gram-frame onto fn2-pool-scan (one scan per run); octet loop only as grammar-unit's reference, equal at every probe state |
| D3 prefix fix | 431982c49 | conn-answer library prefix fn2-answer- (defmachine's fn2-conn-* names collided) |
| D3 1/n | af591acec | conn-answer.lisp: decision table over the pool (CAPABILITIES HELP QUIT MODE DATE AUTHINFO XREDEEM STARTTLS LIST fixed bodies; interim replies per quest; greeting/400; overflow), deferred sub-form checks; conn-answer-unit 67 spec-written fixtures, grammar-responder teeth |
| D3 design | 430a77b9a | layer doc section 4 rewritten against R7 as landed; section 8 ABI; seam request (4.5) |
| D docs §11 | 27fa4a089 | the deferred-assertion table E must restore |
| D2b-2 | 7ead1d598 | H's model as second oracle over 4,416 fuzz cases; 0 disagreements |
| D2b-1 | b121e210e | generator, mutator, fuzzer 17,664 cases, mutation controls |
| D1a | 1ddce858f | T10 resident measure |
| D2a | 615dfde78 | defgrammar, NNTP table, parser, renderer |
| D0 | 90d9405c4 | acquisition tables, bundles, ranked-no-cycle proved |

## In flight
Nothing uncommitted. Lane worktree build/lanes/fn2/d3-conn (branch fn2/d3-conn) equals dev at 67d678389.
Forge clone /build/lanes/d3b (branch lane) is that tree, closure certified, drivers run there.

## Certify times (laptop, two jobs, loaded)
| book | s |
|---|---:|
| books/resources.lisp | 0.8 |
| books/resources-owed.lisp | 2.7 |
| tests/resources-unit.lisp | 0.6 |
| tests/sim-acquisition.lisp | 2.3 |
| books/grammar.lisp | 2.2 |
| books/nntp-grammar.lisp | 3.0 |
| tests/grammar-unit.lisp | 3.8 |
| tests/grammar-gen.lisp | 4.3 |
| tests/grammar-fuzz.lisp | 12.7 |
| books/resident.lisp | 0.7 |
| books/owed-d.lisp | 2.6 |
| books/conn-answer.lisp (forge) | 21.7 |
| books/nntp-grammar.lisp (forge) | 17.9 |
| books/conn.lisp registration (forge) | 4.7 |
| books/assembly-callbacks-d (forge) | 29.5 |
| books/assembly-callbacks (forge, merged) | 54.8 (A/B book; near the limit) |
| books/assembly-core (forge, merged) | 51.9 (A book) |
| tests/conn-unit.lisp (forge) | 5.8 |
| tests/grammar-unit.lisp with the D2c equivalence (forge) | 4.2 |
| tests/conn-answer-unit.lisp (forge) | 0.5 |
| tests/owed-d-unit.lisp | 2.4 |
| tests/owed-d-coverage.lisp | 2.3 |
(certify.sh waits on the tree-wide lock build/fn2-certify.lock; wall time of a run is mostly that wait.
Under load average ~250 (other seats) grammar.lisp took 169-277 s with 1.55 s of event time: host load,
not the book; re-measure when quiet before calling a one-minute red.)

## Next
1. sim-layer-d: scenario 1 plaintext anonymous half under the simulator's network (fn2-sim-advance
   with :listener-targets fn2-conn) with WIRE over the client drain record; fuzz-nntp served half.
3. D4 (upload + :article-input), noting the 32-value row limit (seam note to A: snapshot only the
   fields an arm reads, or split the row).
4. assembly-callbacks is at 56.8 s, assembly-core 53.0 s on forge: one more kind will cross 60 s;
   tell A (their books) before D4 registers a kind.

## Open seam notes (sent to main)
- OWED.md is current at 1ddce858f (D0, D2a, T10 rows in). owed-d-coverage cannot join owed-export (it is a
  second core instance; it certifies on its own).
- A's a4 driver not run for D2a (no A file changed by D2a; the declare clause is the DSL seat's 5d809cb94).
- Shared-tree commit rule: never stage; `git commit -F <msg> -- <paths>` (new files need `git add -N`).
- When R6b makes a bundle atomic, sim-acquisition fails ("owed bundle passes"): remove that bundle's
  :owed-by in resources.lisp. The Accept RX-exhaustion check currently expects wait reason :pool; R6b may
  choose another name, then update the check.

## Commands that work
- Certify: `sh fn2/tools/certify.sh --jobs 2 <paths relative to fn2/>` (background with PID file when it
  may wait: build/d-seat/cert-d0.sh pattern; poll with `until grep -q "CERT EXIT" log; do sleep 3; done`).
- REPL-first: `FN_ACL2_SLOT_DIR=/tmp/fn2-d0-acl2-slots FN_ACL2_SLOTS=4 timeout 600 tools/acl2 < script.lsp`
  where the script does `(ld "fn2/tests/X.lisp" :ld-error-action :continue)` and `cw`s results
  (build/d-seat/try.lsp).
- D0 driver: `FN_ACL2_SLOT_DIR=/tmp/fn2-d0-acl2-slots FN_ACL2_SLOTS=4 timeout 1800 tools/acl2 <
  fn2/tests/sim-acquisition-driver.lsp` (prints BUNDLE lines, the §3 tables between TABLES BEGIN/END;
  strip the `ACL2 !>` prefix, do not drop those lines: they carry each table's first row).
- OWED export: `sh fn2/tools/certify.sh --export-owed`. It needs every book owed-export.lsp includes
  certified; after other seats merge, certify them first (zsh: `${=L}` to split the list; 398 s).
- Fuzz: `sh fn2/tools/certify.sh tests/grammar-fuzz.lisp` (tallies in its .cert.out, `FUZZ real` and
  `FUZZ controls`). Model oracle: `tools/acl2 < fn2/tests/grammar-fuzz-export.lsp >
  build/nntp-fuzz-cases.txt; python3 fn2/tests/grammar-fuzz-oracle.py`. Table oracle:
  `tools/acl2 < fn2/tests/grammar-export.lsp > build/nntp-grammar-table.txt; python3 fn2/tests/grammar-oracle.py`.
- Commit: `git add -N <new files>`, `python3 tools/secrets_check.py <files>`, `git commit --no-gpg-sign -F
  build/d-seat/commit-<q>.txt -- <paths>`, `git fetch`, merge origin/dev, push dev.

## Pitfalls hit
- Never REPL-`ld` a file with unbalanced parens: the ld loops on SET-CBD errors (34M log lines).
  Check balance with build/d-seat/parens.py first; prefer certify (fails fast).
- A defun with no :measure over several decreasing formals can stall ACL2's measure guessing; give
  `:measure (nfix k)`.
- One huge backquote body: split the emission into helpers (fn2-gram-parse-events).
- Guard t predicates over arbitrary data: member-equal/remove-equal/append need true lists; use the book's
  own guard-t helpers (fn2-resource-memberp, -remove).
- zsh: `=====` at a word start is an expansion; quote separators.
- macOS sed `\n` in a replacement duplicated a line; edit with python for multi-line changes.
- Scribe's fill phase takes ~4,096 runs in the scenario profile; bound loops generously.
- `foreground sleep` is blocked; wait with `until ...; do sleep 3; done` in one call.
- ACL2: a defthm about `(mv-nth i (f ...))` over a let*-heavy arithmetic body case-splits forever;
  return one natural (YYYYMMDD packed) instead of an mv.
- Disable each pool function after its `fn2-pool-preserves` line, or the next function's preservation
  lemma re-opens it (fn2-conn-answer took minutes until then).
- `view` is a reserved defcolumns field name (rows wfp init row-view view view-aux); `fill` is a CL
  special and cannot be let-bound. defmachine's "Invalid machine declaration" is generic: evaluate
  its conjuncts (fn2-columns-declarationsp etc.) in a REPL to find which.
- A recursive test helper whose ruler holds an enabled recursive helper applied to a quoted list makes
  the termination proof expand it without bound: disable every helper after its defun.
- Stopping a swarm-build wrapper by its PID file leaves certify.sh children running and holding the
  tree's lock: put the PID of the inner command in the file, or use a fresh clone.
