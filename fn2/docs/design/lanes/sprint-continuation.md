# fn2 sprint C/D continuation (present state; the sprint is finished)

Brief: `build/coordinator/briefs/FN2-SPRINT-CD.md` over `FN2-SEAT-COMMON.md`. Status: DONE, pushed.
Nothing from the sprint merges into fn2/main except through a layer's own reviewed quest.

## Where things are
- Worktree `/Users/ember/dev/fn/build/lanes/fn2/sprint-cd`, branch `fn2/sprint-cd` (pushed), head
  8e3488fcb = origin/fn2/b-durability 0ec44b22a (which already contains fn2/main 4e31a2def; the
  merge was a fast-forward) + one commit of 32 named files, all under `fn2/sprint/`.
- Products: `fn2/sprint/FOUNDATION-GAPS.md` (10 entries: G1, G2, GC1-GC4, GD1-GD4),
  `fn2/sprint/REPORT.md` (verbatim driver outputs, certify times, sub-agents),
  `fn2/sprint/ASTRA-VERDICT.md` (Astra verbatim + a monitor's note at the end),
  `INTERFACE.md`, `REPORT-C.md`, `REPORT-D.md`, `gaps-C.md`, `gaps-D.md`, `evidence/` (Sol's
  capture) and `evidence/seat-rerun/` (the monitor's rerun).
- Code: `fn2/sprint/c/{runs,seal,page-lookup}.lisp` (447 lines), `fn2/sprint/d/{machine,parser,
  connection,owed}.lisp` (628), `fn2/sprint/tests/` (c-examples, d-exchange, integration + drivers +
  run-examples.py), `fn2/sprint/acl2-readonly-slot.py` (sandbox launcher: same global slot files
  opened read-only with the same exclusive flocks; labelled sandbox tool, A5r reviews it).
- Quest files: `build/coordinator/fn2/lanes/sprint-quests/{SOL,ASTRA}.{prompt,log,pid,last.md}`
  (SOL.head is the prose half of SOL.prompt; the rest was spliced from the real files).
  Sol session 01a1842c-3d21-7e43-9d32-b1f1b39555e0 (gpt-6.1-sol, ~55 min, 2 sub-agents);
  Astra session 01a18460-efd2-72c3-9414-c96c7f08aa39 (gpt-6-astra, read-only, ~20 min).
  SOL.log contains a cat of ~/loore-profile.txt (Codex's AGENTS.md asks for it); build/ is git-ignored.

## Examples that ran (Sol's capture; the monitor reran all three, exit 0, identical lines)
- C (c-examples-driver, 0.73 s): one 64 KiB page sealed (`:sealed-volatile`, 45 calls) through B's
  page header + layout codec + BLAKE3, checked by B's `fn2-format-check-page` (`:ok`); output lease
  makes it immutable (`:state`), corruption gives `:bad-hash`; exact Message-ID lookup present /
  absent / yield+resume, on the resident table and on the sealed page after the source handles were
  released; equal-tag different-octets control; sparse cursor over group numbers 2, 900, 1000000
  (`(:yield 0 2 900 54)` then `(:done 2 1 1000000 27)`; byte-budget yield); malformed varint bounded.
- D (d-exchange-driver, 3.5 s): greeting/GROUP/ARTICLE by number and by Message-ID/POST/GROUP/
  ARTICLE/430/QUIT under the simulator, every reply byte against independent fixtures (441 bytes),
  client fragments 1, 7, 4096; failed-fence control (uncertain, no 240, no C row, not durable);
  full-window retained-tail compaction control.
- Integration (3.6 s): full-C POST issues no Write; scoped T1 shape positive + premise removal.

## Verdicts (Astra; the monitor read the code whole and agrees)
INTEGRATE 0; HARVEST 6: P1 gaps (with Astra's corrected table), P2 page sealing/lookup experiment,
P3 sparse seek with shared fuel and seek continuation, P6 CR/LF scanner + retained-tail compaction
+ wire fixtures, P7 POST completion-order experiment, P8 tests/drivers/runner conventions; DISCARD 3:
P4 C remainder (scalar-sum fold, no overlay/filters), P5 the combined connection+upload+txn+query
sidecar machine (row 0, owner 250, driver ignores runnable), P9 the T1/T6/T8/T9/T10 packet.
Gap audit: G1, GC2, GD1, GD2, GD3 P0 (all map to R5a/R5c, B3/B5/B6, or an A-owned arm-contract
extension with D1); GC1, GC4, GD4 P1 (R6 + consumed-prefix/fill semantics; a B codec-width
follow-up); GC3 not a gap; G2 tooling (A5r). Unrecorded: non-machine core children (R5c), admission
bundles/resource waits (R6 + D0), OWN read hook (R5b), column-expansion cost 402 s / 85 GB for a
41-column declaration (R5a), codec width.

## Monitor's own reading (read every source file whole; additions to Astra)
- `fn2-sd-post-check` at full C returns runnable with no phase change: a livelock the integration
  test asserts as success (Astra P5 bullet 2 agrees).
- The uncertain POST outcome is rendered as `441 posting outcome uncertain; recovery required`: a
  refusal code for an uncertain outcome, against T6's three distinct outcomes. D5 must not copy it.
- Every pool access and issued action in C and D uses the fixture owner (250 0 1), never the row's
  (kind slot gen); `fn2-sd-*` continuations ignore `id`.
- Charges are self-declared constants (Astra: write submission charges 0 bytes; scan charge lost on
  `:need-input`).

## For the C and D monitors
Read `fn2/sprint/ASTRA-VERDICT.md` §"What the C/D monitor should read first" (ordered lists), then
FOUNDATION-GAPS.md against Astra's table. The brief amendments Astra proposes are quoted per piece.

## Commands that worked
- Launch: `nohup codex exec -m gpt-6.1-sol -C <wt> --skip-git-repo-check --sandbox workspace-write
  -c sandbox_workspace_write.network_access=false -c features.multi_agent=true
  --output-last-message $PWD/SOL.last.md "$(cat SOL.prompt)" < /dev/null > SOL.log 2>&1 &
  echo $! > SOL.pid`; Astra the same with `-m gpt-6-astra --sandbox read-only` and no multi-agent.
- Wait: `timeout 590 sh -c 'while kill -0 <pid>; do sleep 30; done'` repeated (or a background loop).
- Rerun: `python3 fn2/sprint/tests/run-examples.py fn2/sprint/tests/{c-examples,d-exchange,
  integration}-driver.lsp` from the worktree root (~10 s with warm certs). It rewrites
  `fn2/sprint/evidence/`: do not run it while a reviewer is reading the evidence.
- Commit: zsh array of `git status --short --untracked-files=all fn2/sprint`; secrets_check on it;
  `git commit --no-gpg-sign -F build/commit-sprint-cd.txt`; `git push origin HEAD:fn2/sprint-cd`.

## Pitfalls hit
- In-tree `fn2/docs/design/` copies are an older snapshot (four differ from the coordinator's):
  point Codex at the coordinator originals.
- Codex's sandbox cannot open `~/.cache/fn-acl2-slots` read-write: Sol's read-only flock launcher.
- Cold certify of the A/simulator closure on a fresh worktree: ~31 min; `d/machine.lisp` (41
  generated columns) 402 s.
- The monitor's rerun overwrote Sol's evidence while Astra read it (Astra flagged the mismatch);
  Sol's capture restored, rerun moved to evidence/seat-rerun/.
