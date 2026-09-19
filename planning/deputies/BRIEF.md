# Deputy-scholar brief (read before any tool call)

You own one cluster of books. Fix everything you can inside it; keep its
include-closure certifying; return one report and one proposal for the
cross-cluster steps you could not take alone.

## Box rules (each one cost a lane hours in the last cycle)

- Certificates are installed in your worktree before you start (content
  hashed: `ACL2_BOOK_HASH_ALISTP=NIL` is set by every tool). Never run a full
  `make certify`. Certify only books in your cluster's closure, one root at a
  time, with `FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py <book>`.
- Iterate with `ld` on a scratch driver that starts with
  `(set-prover-step-limit 2000000)` and includes only your dependencies; the
  runner is for the end, not for search. Kill your own runaway ACL2 by PID
  after three minutes.
- At most ONE ACL2 process of yours at a time. Any run over two minutes uses
  the Bash tool's `run_in_background: true` and you wait for its notification.
  Never a polling loop; never `pgrep -f` on other lanes' processes; never
  `pkill`, `killall` or any pattern kill.
- Never `git stash`; never `git add -A`; commit named files with
  `git commit -F <msgfile>`; never search under `build/` or `/`.
- Hard budget: the tool-call number in your prompt. When it is spent, commit
  what certifies, write the report, stop.

## Micro discipline (apply everywhere in your cluster)

1. **Opaque records.** Prove each record's shape and accessor-of-constructor
   lemmas once; then `(in-theory (disable <accessors> <constructor>))`.
   Nothing downstream opens a record. Rules are stated in accessor vocabulary
   and goals stay in it.
2. **Export policy.** A book ends with an explicit theory event. It exports
   keystones and record lemmas. Every accessor or unfold equality used only
   for guard proofs is `:rule-classes nil` (used via `:use`) or `local`.
   No `len`-backchaining or accessor-equality rule leaves a book enabled.
3. **Recognizers are carried invariants.** A whole-state recognizer guards the
   executable path under `mbe`; it is proved preserved by every transition
   and never re-run per operation.
4. **Teeth as concrete witnesses.** One `assert-event` per hypothesis on a
   specific violating value (under `with-guard-checking :none` when outside a
   guard). Never a general negated `must-fail`; never a trivially true
   assertion; if a hypothesis proves unnecessary, delete it from the theorem
   and say so.
5. **Layering.** Split books over 800 lines at their seams; fold ad-hoc
   `-invariants`/`-traces`/`-teeth` sprawl into definitions, properties and
   one test book per cluster, when that does not cross cluster boundaries.
6. **Honesty.** A theorem you cannot close within budget is removed and
   recorded open, never weakened; a claim in a spec that a theorem no longer
   supports is walked back in the same commit.

## Report (`planning/deputies/<cluster>.md`, at most 60 lines)

HEAD; per book: certified (evidence dir) or open (failing form); before/after
ledger numbers for your cluster (global rewrite rules exported, SUSPECT
count, closure certify wall time); what you changed and why; the proposal:
the cross-cluster steps, each with the exact interface change and who owns it.
