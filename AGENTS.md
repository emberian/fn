# Working on fn

fn is an ACL2-verified NNTP node: ACL2 books own every decision; the SBCL host does I/O and
calls them. Read docs/README.md, docs/architecture.md and planning/decisions.md before
substantial changes, then the spec you touch. Proposals and open questions are not requirements.

## The engineering laws
- ACL2 decides identity, bounds, framing, charges and reply lines. Host code and Python never
  compute or compare a value ACL2 computes. A missing decision is an open item, not a host function.
- No arbitrary ceilings on stored data (D27); admission limits belong to the supported profile.
  Bound work and allocation per step and yield or resume; never silently truncate.
- The served path uses concrete representations (D27); octet lists are the logical model. Each
  boundary has a named refinement theorem (outputs and effects) to its model; guard-verified.
- Parsing external data never invokes the Lisp reader; bound the work before consuming input.
- Octets, fields, content identities, Message-IDs and article numbers are distinct types.
- Durable acceptance only from persisted state; an ambiguous persistence failure is a recovery
  event, never a silent rollback. No last-writer-wins on wall-clock time. Uncertain, refused and accepted stay distinct at every boundary.
- No whole-state revalidation on a served path: carry the invariant and prove it preserved.
- Every process-death cut is a model crash point (`native_program_check`).
- Generators (def-loop, def-representation, def-buffer) are the design of record; grow the
  generator, never hand-write a twin. D68: no migration or compatibility duty; delete old layouts.

## What makes a claim
- The subject is the function the host calls, or a named theorem equates them. A theorem about
  a branch the composed machine cannot reach is marked `unreachable-in-composition` or the
  branch goes (`reach_check --strict`). Lemmas that only unfold are named `-unfolds` or
  `-by-definition` and not cited as events (`ledger.py --check`).
- Keystones ship with teeth: a positive witness asserting the whole antecedent and conclusion,
  and a hypothesis-removal witness. keystone_emit's toothless list is becoming the ledger of keystones
  without teeth (shrink-only, lane x-teeth-ratchet); until then TEETH-OWED items exempt. A failed proof search is not a counterexample.
- No skip-proofs, defaxiom, trust tags or :program; never weaken a theorem, lock rule or
  ratchet to go green; never re-baseline; no vacuous statements.
- A named assumption is an `encapsulate` with a local witness in `books/assumptions*.lisp`,
  and the theorems that use it mention it. An abstract crypto model proves nothing about real
  signatures, hashes, disks or a peer's honesty.
- Open a codec in a hint, never at the top of a book (`theory_check`).
- Certified means a record-toolchain cert-cache entry at the book's current closure key
  (`green_check`). A commit message, a proposed theorem or passing tests are not certification.
- Quote the pessimistic number with its scope in the same sentence (collision, not preimage).

## Your lane
- Work only in your worktree, `build/lanes/<name>`. Never stash; never reset or check out
  ~/dev/fn; commit named files with `git commit -F`; run `tools/secrets_check.py <files>`;
  push `HEAD:lane/<name>` only. The integrator alone writes origin/dev.
- Claim new ids first: `tools/next_id.py claim KIND --lane NAME`.
- Iterate in `tools/proof_repl.py` (seconds per attempt, steps not seconds); certify is for
  READY, not iteration. Certify with
  `farm.py submit <box> --lane --affected-by <book>`, never `--closure`. Laptop certs are
  the author's check only (arm64). A book over ten seconds at two jobs is a defect (D26).
- Read failures with `tools/certify_triage.py RUN_DIR`; never grep for FAILED.
- Run the narrowest test that could refute you; state your control. Never an unfiltered suite.
- Merge on narrow gates (`--affected-by` certify, filtered tests; for host/ `host_check --load`
  and `interface_emit --check` at 0 findings, a new definterface taking `:kinds` from its book
  guard); images, natives and full `green_check` run at convergence. Say which closure a green covers.
- More than ~5 identical edits is a program transformation (`tools/lisp_rewrite.py`) with
  fixtures; never hand-edit the class. Bounded mechanical work may go to `claude-grok -p`; review its diff. Find bugs by tracing the current tree, never bisecting.
- Take the next known step in the lane in hand; fix the root, drain the class. Owed items only
  for work that needs another lane or a decision.
- Commit within 30 minutes; proof work per lemma. READY = `lane/<name>@sha`, the gates run, any red.

## Boxes and safety
- hbox: every build under `swarm-build`; `free` lies (read arcstats and summed RSS).
- Laptop ACL2 only through `tools/acl2` or `proof_repl` (the slot pool, 6 slots, 8,000 MB each).
- Never kill, pkill, killall or systemctl stop anything you did not start, and never by name,
  pattern or user match (`pkill -x sbcl -u hbox` killed production): stop your own job only by
  the PID you recorded (`$!`). Every long command carries a `timeout`.
- Long box jobs run detached (`setsid nohup ... > /tmp/<lane>-<x>.log`), PID beside the log; poll the log, don't hold ssh open.
- No deploys, publication or messaging. Don't touch fn-node.service or /tank/fn/node.
- Disk low: stop writing, tell your deputy, wait. Delete nothing.

## Context
- `wc -l` before reading; over 800 lines, grep and read +-60. Never read a LANEDUMP.md.
  Long output to `/tmp/<lane>-<x>.log`; read its tail.
- Before context runs out, write `build/coordinator/lanedumps/<lane>-continue.md` (<= 80 lines).

## Writing
Lead with the point, then the mechanism with real names, then detail. Claim and scope in one
sentence. No process narration; history is git and the decision register. Commands exact.
kimi, grok and ZAI may review batched changes: advisory, minimal pasted context, no secrets.
