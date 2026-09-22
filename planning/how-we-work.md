# How we work now

One page. A lane is briefed from this and from its step in
[the trajectory plan](plan-2026-09-22-trajectory.md). The rules below are the
five findings of [the proof-engineering review](review-2026-09-22-proof-engineering.md)
turned into practice, plus the assurance rules of [AGENTS.md](../AGENTS.md),
which still apply in full.

## The loop

1. **Start from ground truth, in your own worktree.** The brief names the
   step, the books you own (and nothing else), the host lines that call the
   subject, the theorem statements you are to prove, the teeth you owe, and
   the evidence file you will write. If the brief says "put it under a
   directory" instead of an absolute path, or describes a signature instead
   of pasting it, ask before writing a line.
2. **Iterate in a live session, not on the farm.** `python3 tools/proof_repl.py
   start NAME BOOK --upto EVENT`, then `send NAME FORM`: seconds per attempt
   against cached certificates, a minute at most for a search that stops
   returning. A form the session admits is not a certificate; it goes into
   the book and the book certifies.
3. **Open a codec in a hint, never at the top of a book.** `theory_check`
   names the habit; `--strict` will refuse it. A goal that only dispatches on
   a record kind must not carry the codec (F3).
4. **Certify your own closure before you report.** `python3 tools/farm.py
   submit <box> --remote-root <abs path> --affected-by <book> --closure`,
   then `python3 tools/green_check.py --changed-since <base> --strict` in your
   worktree. Discovery runs use a 300 s per-book budget; a book that needs
   more is a finding you report, not a budget you raise (F2). Only the final
   closure run uses 1800 s.
5. **Report what the tools say.** Your report names: the theorems (their
   statements, not their names), the host lines, the teeth book, the
   `green_check` line, the farm run id and manifest, the evidence file, and
   what you did not do. "Green" is a tool's word; do not use it for a book
   you did not certify at its current bytes.
6. **Root triages, gates, merges, images.** One provisional wave
   (`tools/triage.py`) over the image closure with your branch merged
   locally; every independent red in one report (F1); the merge gate
   (`green_check --changed-since ORIG_HEAD --strict`) decides; a red means
   `git reset --hard ORIG_HEAD` and the fix is yours. The image is rebuilt
   from a frozen tree with `tools/runbooks/hbox-image-build.sh` after a batch
   that touched the closure, at most once a day, and the deployed node moves
   only to a frozen image with its manifest.

## Width, and why

**Three lanes editing `books/` at once, on disjoint include-closures declared
at launch; host and tool lanes as needed.** On 2026-09-21 twelve capability
lanes ran at once and five commits in three hours widened `fn-sn-state`, gave
`fn-sn-finish` two arms, bound the AUTHINFO peer role and gave `fn-sn-recover`
a fault arm under invariant books nobody recertified; the exported statements
were false in the shape the machine had and `git log` read as green for a
day (F4, [the second freeze record](evidence/native-freeze-01fbdad4-2026-09-22.md)).
A provisional wave attributes a red to a lane only if no two lanes touched the
same closure; three is the number one root can triage and merge in a day with
an image at the end of it. A step whose lanes overlap (the codec seam) lands
its lanes one at a time, one wave each.

## Boxes

`swarm-build` around every build on hbox; `tools/acl2` for every ACL2 you
start by hand (it takes a slot); never a bare `&` in a lane shell; `free` lies
on hbox (read `arcstats` and summed RSS); a farm run's `--remote-root` is
absolute; certificates are not relocatable across worktrees on one machine
(`tools/certs.py` refuses `foreign-local` for you). The full trap list is
[the freeze recipe](evidence/native-freeze-c28ffc30-2026-09-22.md) and the
runbooks' headers.

## The five findings as rules

| | Finding | Rule |
| --- | --- | --- |
| F1 | a failed book hides every book above it | discovery is a provisional wave, never a chain of ordinary runs; one report per batch names every red |
| F2 | a proof that stops returning burns the round | 300 s for discovery; a timeout is a finding with the theorem named; `with-prover-time-limit` in the session |
| F3 | codec vocabularies opened book-wide | a codec is opened in a hint or not at all; the seam books (plan §4.1) make it impossible above them |
| F4 | behaviour landed under uncertified invariants | the merge gate; behaviour and the invariants over it land together or the merge waits; three book lanes at once |
| F5 | each lane re-derived the loop | this page and the runbooks; a lane that spends its first hour on the recipe reports that as a defect in the brief |

## What a step is, and is not

A step is DONE or NOT (plan §3). DONE means the theorems over the host-called
subject exist with teeth, the closure is green at the current bytes, the
behaviour is measured on an image, and the evidence file exists. A step that
would need a `partial` row is two steps or a wrong step. A theorem with a
hypothesis that names the arm it is true on is a claim about one arm; state
the other arms or say why they are unreachable. Uncertain, refused and
accepted stay three words all the way out. The pessimistic number is quoted
with its scope in the same sentence. Counts come from the tools.
