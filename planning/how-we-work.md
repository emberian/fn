# How we work now

One page. A lane is briefed from this and from its step in
[the trajectory plan](plan-2026-09-22-trajectory.md) (§3 the steps, §3.3 the
phase schedule). The rules below are the five findings of
[the proof-engineering review](review-2026-09-22-proof-engineering.md) turned
into practice, plus the assurance rules of [AGENTS.md](../AGENTS.md), which
still apply in full. ember's decisions of 2026-09-22 (plan §0) set the width
and the convergence rhythm.

## The loop

1. **Start from ground truth, in your own worktree.** The brief names the
   step, the books you own (and nothing else), the host lines that call the
   subject, the theorem statements you are to prove, the teeth you owe, the
   box you certify on, and the evidence file you will write. If the brief
   says "put it under a directory" instead of an absolute path, or describes
   a signature instead of pasting it, ask before writing a line.
2. **Iterate in a live session, not on the farm.** `python3 tools/proof_repl.py
   start NAME BOOK --upto EVENT`, then `send NAME FORM`: seconds per attempt
   against cached certificates, a minute at most for a search that stops
   returning. A form the session admits is not a certificate; it goes into
   the book and the book certifies.
3. **Open a codec in a hint, never at the top of a book.** `theory_check`
   names the habit; `--strict` will refuse it once T1 lands. A goal that only
   dispatches on a record kind must not carry the codec (F3).
4. **Certify your own closure before you report.** `python3 tools/farm.py
   submit <your box> --remote-root <abs path> --affected-by <book> --closure`,
   then `python3 tools/green_check.py --changed-since <base> --strict` in your
   worktree. Discovery runs use a 300 s per-book budget; a book that needs
   more is a finding you report, not a budget you raise (F2). Only the final
   closure run uses 1800 s. This is the step that F4 was missing and it is
   not optional: behaviour and the invariants over it land together.
5. **Report what the tools say.** Your report names: the theorems (their
   statements, not their names), the host lines, the teeth book, the
   `green_check` line, the farm run id and manifest, the evidence file, and
   what you did not do. "Green" is a tool's word; do not use it for a book
   you did not certify at its current bytes.
6. **Root merges as batches land; converges every two to three.** A batch
   with its own certification and a clean static gate is merged (`--no-ff`)
   when it lands. After every two to three merged batches, or at the end of
   a phase, whichever is sooner, root runs one provisional wave
   (`tools/triage.py`) over the image closure and reads every independent red
   in one report (F1); a red goes back to the lane whose books it names, and
   the image is rebuilt from a frozen tree (`tools/runbooks/hbox-image-build.sh`)
   only after a clean wave. The deployed node moves only to a frozen image
   with its manifest, and its page says which properties hold on it.

## Width, and why

**Five lanes: two certifying on hbox, two on persvati, one local**, each on
books it alone edits within the phase (include-closures may overlap; edited
books may not), declared at launch and listed in the schedule. On 2026-09-21
twelve capability lanes ran at once and five commits in three hours widened
`fn-sn-state`, gave `fn-sn-finish` two arms, bound the AUTHINFO peer role and
gave `fn-sn-recover` a fault arm under invariant books nobody recertified;
the exported statements were false in the shape the machine had and `git log`
read as green for a day (F4, [the second freeze record](evidence/native-freeze-01fbdad4-2026-09-22.md)).
What prevents that is step 4 of the loop, not the number of lanes; what the
number buys is that one wave can attribute every red to one lane, and one
root can merge and image in a day. A step whose lanes must edit the same
book (the codec seam's clusters, T2 then T3 then T4 on `store-node`) runs
those lanes one after another in one slot of the schedule.

## Boxes

`swarm-build` around every build on hbox; `tools/acl2` for every ACL2 you
start by hand (it takes a slot); never a bare `&` in a lane shell; `free` lies
on hbox (read `arcstats` and summed RSS); a farm run's `--remote-root` is
absolute; a farm run installs its dependencies from the box's cache, composed
from several snapshot origins when no one origin holds them all, and never
from a live worktree on the same machine (`tools/certs.py` refuses
`foreign-local` for you; `planning/evidence/certificate-cache-2026-09-23.md`). The local lane's pool is
four slots; a local lane whose closure outgrows it submits to its step's box.
The full trap list is [the freeze recipe](evidence/native-freeze-c28ffc30-2026-09-22.md)
and the runbooks' headers.

## The five findings as rules

| | Finding | Rule |
| --- | --- | --- |
| F1 | a failed book hides every book above it | discovery is a provisional wave, never a chain of ordinary runs; one report per convergence names every red |
| F2 | a proof that stops returning burns the round | 300 s for discovery; a timeout is a finding with the theorem named; `with-prover-time-limit` in the session |
| F3 | codec vocabularies opened book-wide | a codec is opened in a hint or not at all; the seam books (plan §4.1) make it impossible above them |
| F4 | behaviour landed under uncertified invariants | a lane certifies its own closure before it reports, every time; root converges every two to three batches; five lanes on disjoint edited books |
| F5 | each lane re-derived the loop | this page and the runbooks; a lane that spends its first hour on the recipe reports that as a defect in the brief |

## What a step is, and is not

A step is DONE or NOT (plan §3). DONE means the theorems over the host-called
subject exist with teeth, the closure is green at the current bytes, the
behaviour is measured on an image, and the evidence file exists. A step that
would need a `partial` row is two steps or a wrong step. A theorem with a
hypothesis that names the arm it is true on is a claim about one arm; state
the other arms or say why they are unreachable. Uncertain, refused and
accepted stay three words all the way out. The pessimistic number is quoted
with its scope in the same sentence. Counts come from the tools. A branch
someone else left is an input to a brief, never a thing to "resume".

## Certification cost, learned 2026-09-23

Four lanes each spent over an hour recertifying 60 to 150 books from
`sha256` upward, one chain of large books at a time, while the agents sat
in `farm.py wait`. The cache had no usable entry at their digests because
every merge that day touched a book low in the graph and nobody had
published a certification of `dev`'s head since. The rules that follow:

- **Root keeps `dev` certified.** After each merge batch root submits one
  treewide run of `dev`'s head on persvati (`farm.py submit persvati
  $(python3 tools/proof_artifacts.py roots --profile default; python3 tools/proof_artifacts.py roots --profile dtn; ls tests/acl2/*.lisp | sed 's/\.lisp$//') --jobs 16
  --cache /home/ember/fn-certcache ...`) so the cache carries every
  unchanged book at its current digest, and a lane's run certifies only
  what the lane changed and what includes it. Since 2026-09-23 that run is
  a plain-roots run, not `--closure`: whatever is cached at the current
  digests installs from any snapshot origin, and only the rest certifies.
  That is the default for every submit without `--closure` or
  `--require-origin` (`certs.py install-partial`, `certify_books.py
  --incremental`): a book whose pair is cached at its closure key and
  toolchain installs, roots included, and the uncached books certify in
  dependency order, so a change low in the graph costs that book and what
  includes it, never a refusal. `submit` prints "installed N of M books ...
  certifying K" at once; the manifest says `installed` or `certified` per
  book and names the origins drawn from. `--require-origin` is the explicit
  way to demand one origin.
- **A lane does not merge `dev` mid-flight.** It branches from `dev`, works,
  certifies its own change against the digests it branched at, and root
  merges on landing; if root needs the lane on a newer base, root says so
  and the lane recertifies only what the merge changed.
- **A lane reports when its run is submitted**, with the run id and the
  gate, and root harvests the manifest with `farm.py wait` and files it.
  An agent waiting an hour on a farm run is the most expensive idle there
  is. If a lane must wait on something (a proof session loading, a short
  run), it issues ONE command in the background and does other work until
  the notification arrives; a foreground wait that hits the ten-minute
  shell cap and is reissued six times is the pattern that cost a night.
- **A provisional wave runs only when the closure failed behind a
  cascade**, to name the reds behind it; never beside a closure run, and
  never to "show the books proved" when the closure passed.
- **Never submit a lane run with `--closure`.** In this tree `--closure`
  is the explicit recertification plan: the farm installs from the cache
  with purge-on-miss and certifies every book of the closure again (the
  seam lane's final submit: "missing 171, removed 278"). A lane submits
  `farm.py submit <box> --affected-by <changed book> ...` (or the changed
  books and test books as plain roots): everything cached at its current
  digest installs, and only the changed books, their dependents and
  anything else the cache lacks certify. Root
  uses `--closure` for the freeze and the treewide run, nothing else.
- **A book over ten seconds is a defect.** On 2026-09-23 every book over
  a minute turned out to be a recognizer, codec or table left enabled
  where one proof needed a shape fact, and each was repaired with hints,
  disables and local lemmas, no statement touched: 805 s to 3.7,
  656 to 10.7, 307 to 2.3 (the cost records under `planning/evidence/`).
  Read the certify log's per-event times and `Rules:` first; one
  instrumented session run (`accumulated-persistence`) at most; never
  rerun the slow form to "see". A lane that lands a book over ten seconds
  says why in its report.
- **Iteration time is a number.** The target from 2026-09-23 is under
  three minutes from a book edit to a certified verdict, measured by the
  three rows of `tools/iteration_bench.py` (leaf edit, deep edit, freeze)
  and recorded with each change that claims to help.
