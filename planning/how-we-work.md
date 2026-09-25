# How we work now

A lane is briefed from this page, [now](now.md) (dev, the goal, the lanes)
and [the current view](current.md). Release scope is
[the trajectory plan](plan-2026-09-22-trajectory.md) §0 to §2. The rules of
[AGENTS.md](../AGENTS.md) apply in full; this page is the loop.

## The loop

1. **Start from ground truth, in your own worktree.** The brief names the
   step, the functions and books, the host function that calls the subject,
   the theorem statements, the teeth owed, the box and the evidence file,
   with absolute paths and pasted signatures. A brief that describes a
   signature instead of pasting it means: read the named source at the
   pinned revision first, and ask only when that does not resolve the
   contract.
2. **Iterate in a live session.** `tools/proof_repl.py start NAME BOOK
   --upto EVENT`, then `send`; 300 s bounds a discovery attempt, and a
   timeout is a finding with the theorem named. An admitted form is not a
   certificate.
3. **Certify incrementally.** `farm.py submit <box> --affected-by <book>` (or
   the changed books and tests as plain roots): cached books install, the
   rest certify. Never `--closure` for lane work. Wait with one background
   command and do other work.
4. **Report what the tools say**: theorem statements, host function, teeth
   book, the `green_check` line, run id and committed manifest, evidence
   file, and what you did not do.
5. **The coordinator merges as lanes land**, regenerates the ledger and
   `current.md` in the merge (never hand-resolving a generated file),
   assigns new registry IDs, runs `make check` and
   `teeth_check --strict --changed-since`, removes the lane's worktree, and
   coalesces the certification of merged bytes against the current frontier
   (one run per batch of merges, reusing matching results; never one run
   per merge).
   A lane merges `dev` mid-flight only for a landed change it needs, then
   recertifies what that moved.
6. **Waves converge once.** At convergence, one immutable candidate: a
   fresh closure and one qualification lane over the whole set while the
   next wave runs. Never re-qualify interim cuts. A regression the cut finds
   does not freeze unrelated development, but it blocks the affected
   deployment or claim until the repaired candidate has matching evidence;
   unchanged evidence is reused, a green verdict is never transferred to
   changed bytes. Deploy when the candidate is green.

## Width and who proves

Start around ten lanes; add one only for substantive work. Claims announce
intent and do not reserve files; lanes that overlap agree on the interface
and on who assembles the combined change, then certify its bytes. A lane
whose brief says implement-only hands a failed proof (source, event, log)
to the proof owner rather than searching for it.

## Proof cost

- A book over ten seconds at two jobs is a defect (D26). `proof_cost` fails
  on a book not in the baseline above 11 s, or on a baseline book 25 % over
  its figure; 10 to 11 s prints `NEAR`. The baseline only shrinks, by proof
  work: read the certify log's per-event times and `Rules:`, one
  instrumented session at most, never raise a timeout or weaken a statement.
- The band and the threshold are operating rules, not proof that an
  excursion is noise: keep matched host, toolchain and job conditions when
  adjudicating one. Splitting a book must reduce total or critical-path
  work, never only the per-book figure.
- Aim for under three minutes from edit to certified verdict; record queue,
  install, proof and total time when you claim a speedup.

## Boxes

`swarm-build` around every hbox build; on the laptop, `tools/acl2` or
`tools/proof_repl.py` for every ACL2 (the pool, `tools/acl2_slots.py`, caps
each process at 8,000 MB and admits six: the machine-memory budget; a bare
`acl2 <` bypasses it and is how the laptop hard-crashed on 2026-09-25); no bare `&` in a lane shell; `free` lies on hbox; a farm run's
`--remote-root` is absolute; certificates install from the box's cache,
never from a live worktree. The box-specific environment for a remote REPL
and the full trap list are in the `proof_repl.py` header and the runbooks.

## What a step is

DONE or NOT. DONE means the theorems over the host-called subject exist with
teeth, the affected closure is green at the current bytes, the behaviour is
observed on an image, and the evidence file exists. A step that would need a
`partial` row is two steps. A branch someone else left is an input to a
brief, never a thing to resume. Intermediate reds stay visible and never
excuse a weaker statement or a host twin.
