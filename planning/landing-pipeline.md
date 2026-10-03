# The landing pipeline: each check runs once (2026-10-03, after ember's review ask)

## What was happening (the triple testing)
A host change ran the same tests three times as it moved through the pipeline:
1. LANE: REPL admission, certify its closure on hbox, build three images, run natives.
2. REVIEWER (liaison): re-ran natives / certify / acceptance on a box "to confirm".
3. RUNNER: re-ran fast checks at the merge head, certified the pushed head's closure, built images again and
   re-ran the core natives for the image set.
Image builds (~1 h each on hbox, three images) were the dominant cost, and three lanes often built images of
nearly the same tree at the same time.

## The rule: one owner per check, evidence passed by content
| Check | Who runs it | Keyed by | Who reuses it |
|---|---|---|---|
| REPL admission | lane | - | nobody re-runs |
| certify of the changed books' closure | lane (farm; cache by content) | book bytes | runner: farm installs from cache; only books whose closure the MERGE changed certify again |
| red-before / green-after native for the defect | lane, on images at its sha | image source sha | reviewer reads the run ids; runner does not re-run that module |
| review | reviewer reads diff + evidence; runs a check ONLY if the lane did not, or the claim depends on something unmeasured | - | - |
| fast checks (interface, host_check, ledger, reach, build_lists, secrets) | runner, once per batch at the merge head | tree | - |
| core native modules + image set | runner, once per batch, on the images that become the published set | merge-head source sha | lanes base on the published set; no lane rebuilds images it does not change |
| whole-tree certify | runner, background, per pushed head | content cache | - |

Consequences:
- The liaison no longer re-runs natives or certifies; it reads evidence and attacks the claim.
- A lane whose change touches no host bytes runs NO natives (books and tools are covered by certify + tests).
- A lane that changes host bytes runs only the modules its change affects, plus the defect's red/green test.
- The runner batches host-changing READYs so one image build serves several lanes.
- Evidence must be trustworthy for reuse: SWEEP-GATES' S055 (check_steps cached a PASS taken after a
  timeout) and S009 (green_check passing uncertified books) are prerequisites, so they are priority there.

## Closing out
A lane finishes its current item to LANDED before starting the next; READYs go out per item, not in big batches
at the end; a lane with more than two unlanded READY-able items stops starting new ones.

## MERGE TRAIN (2026-10-03, ember: "do we have a branch with everything that is ready?")
- origin/next is the integration branch. The runner merges each review-cleared READY into next as it arrives.
- Ledger states: `ready` = merged into origin/next; `landed` = on origin/dev. A lane's own branch being done is
  `in-progress` until the runner merges it.
- Fast checks run continuously on next's tip; a red pass reverts the breaking merge on next and returns it to its lane.
- next fast-forwards to dev when its tip passes fast checks AND the batch native/image run; the image set is published then.
- Lanes base new work on origin/next (it has everyone's merged fixes hours before dev).
