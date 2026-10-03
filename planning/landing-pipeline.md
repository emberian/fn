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
| assurance catch-up | runner, once at convergence under X13 | content cache and named candidate | later matching claims |

Consequences:
- The liaison no longer re-runs natives or certifies; it reads evidence and attacks the claim.
- Native needs follow the executable image and called tools, not only host text: a changed image book closure can require native checks too.
- A lane that changes host bytes runs only the modules its change affects, plus the defect's red/green test.
- The runner batches host-changing READYs so one image build serves several lanes.
- Evidence must be trustworthy for reuse: SWEEP-GATES' S055 (check_steps cached a PASS taken after a
  timeout) and S009 (green_check passing uncertified books) are prerequisites, so they are priority there.

## Closing out
Lanes own continuing workstreams and send complete slices as they become ready. Start with at most two
unlanded slices per lane; work on independent preparation while a check runs rather than waiting idle
for a qualification image. Finish integration and consumer wiring before calling a workstream done.

## Integration during stabilization

Ember's late October 3 instruction in [the prior plan](plan-2026-10-03.md#update-at-the-end-of-the-session-2026-10-03-late)
supersedes the earlier next-to-dev qualification gate. One integrator merges
reviewed source directly onto dev. New lanes branch from current dev; next, if
maintained, is an integration mirror rather than a required staging gate.
`landed` records source on dev; historical `ready` entries recorded next.

Fast checks run once per integration batch. Fix forward; a failure blocks its
affected candidate/claim without freezing unrelated lanes. Qualify one immutable
candidate at convergence while the next wave runs. An image verdict never
transfers to changed source.

## Current operating contract

[The development workstreams](overnight-2026-10-03.md) supplies the current roster,
shared contracts and source snapshot. Behavior-first work may land with exact
`category=proof-owed` entries; whole-tree certification does not gate source merges.
Image/native claims still require matching evidence, including when image book
closures change without host Lisp edits. Do not call a suite with known failures
green. A source-landed ledger item is not proof/native completion.
