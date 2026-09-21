# Handoff: `w11/gate-verdicts`

Lane worktree `build/lanes/w11-gate-verdicts` on `w11/gate-verdicts`, branched
from `dev` at `cfcd600` and merged with `dev` at `8db4836`. No ACL2 process
was started by this lane, no book was touched and no certificate is
invalidated by anything here: the whole change is in the harness family
(`tools/deploy_gate.py`, `twonode_gate.py`, `inn_lab.py`, `scale_gate.py`,
`v0_matrix.py`, `verdict.py`, `labs.py`) and its tests.

It closes F1 of
[the follow-up review](../review-2026-09-20-astra-followup.md).

## The defect, confirmed in the source before anything was changed

`Step.failed` is `self.rc is not None and self.expect is not None and
self.rc != self.expect`, so a probe declared `expect=None` can never fail. The
gates' exit was `bad = [s for s in gate.steps if s.failed]` then `return 1 if
bad else 0`, and `self.gaps` -- where every scenario assertion wrote its
verdict -- reached the printed evidence and nothing else. A scenario could
observe its promised behaviour failing and exit 0.

## The three-way distinction, as implemented

`tools/deploy_gate.py` now carries a `Finding` beside the `Step`. A step is a
command and its exit code; a finding is what a scenario CONCLUDED. The shape
is `tools/v0_matrix.py`'s, which already keeps five verdicts apart over 190
rows: a fixed vocabulary never collapsed into pass/fail, a declared
`ASSERTIONS` inventory so an assertion the run never reached is emitted rather
than lost, one emitter (`record`) that refuses what it cannot check, and a
sha256 over the rows so a verdict cannot be typed in afterwards.

| verdict | what it says | exit |
| --- | --- | --- |
| `held` | decided, and true | 0 |
| `violated` | decided, and false | **1** |
| `inconclusive` | the run meant to decide it and could not | **3** |
| `not-exercised` | the run did not reach it; `blocker` says why | 0 |
| `not-built` | the feature it is about is not on this tree | 0 |
| `limitation` | a boundary no run of this harness crosses | 0 |

Exit 2 is still a gate that stopped early. 3 is D13's uncertain, and
`tools/verdict.py` and `tools/labs.py` carry it out as a fourth state rather
than folding it into pass or fail.

**Where this diverges from `v0_matrix` and why.** A v0_matrix row is an
OBSERVATION of a feature, and `accepted`/`refused`/`uncertain` are D13's three
outcomes, all three of which can be the feature working. A gate finding is a
CONCLUSION about an assertion, so the two deciding words are `held` and
`violated` and D13's outcomes stay where they already were, in the steps'
expected exit codes. Second divergence: v0_matrix requires every row to be
declared; here only `held` is, because refusing to RECORD a failure nobody
declared in advance would be the inventory rule pointed the wrong way, and
`broke()` reports exactly such a failure.

**`limitation` versus `inconclusive` is the line that keeps this from being
the indiscriminate fix the review rules out.** A postpublish fault is
indeterminate by construction (D13) and no run of any harness can decide it,
so it reports and never fails. A tap that never took its cut, a GROUP reply
with no count, a series that printed no JSON, an offer command no recorder saw
-- those are defects in THAT run, they establish nothing, and a release claim
must not rest on them.

## Triage, per harness

Every `gaps.append` site on `dev` at `8db4836`, by the verdict it now carries.
Several `violated` rows have a runtime-detected absence branch that records
`not-built` instead; those are counted once, under `violated`, and the branch
is named in the next section.

| harness | sites | violated | inconclusive | not-built | not-exercised | limitation |
| --- | --- | --- | --- | --- | --- | --- |
| `twonode_gate.py` | 40 | 30 | 6 | 1 | 0 | 3 |
| `inn_lab.py` | 23 | 11 | 3 | 0 | 0 | 9 |
| `scale_gate.py` | 13 | 3 | 5 | 1 | 0 | 4 |
| `deploy_gate.py` | 10 | 4 | 1 | 0 | 1 | 4 |
| `v0_matrix.py` | 17 | 0 | 0 | 0 | 0 | 17 |

`v0_matrix.py`'s rows already carry its verdicts and its exit already reads
them, so F1 never applied to it: its `gaps` are narrative scope notes and all
seventeen are limitations. It keeps its own `planning/v0-matrix.json` and
turns the findings sidecar off rather than publishing two machine-readable
files a reader must reconcile.

## Two probes the honest classification needed

A gate that calls everything it cannot do a failure is as useless as one that
calls everything a pass, so two absences are now observed rather than guessed.

- `twonode_gate.cli_absent(output)` reads argparse's own `invalid choice` and
  `unrecognized arguments`. A store CLI with no `policy set path-identity` is
  a verb this tree has not built (`not-built`); a CLI that HAS the verb and
  refuses the value is a node refusing (`violated`).
- `TwoNodeGate.probe_feed(node)` greps the node's own server log for
  `FEED <peer> replayed`, which `Owner.feed_configure` prints once per
  configured peer at startup. An entry point with no outbound feed cannot fail
  a feed assertion -- `run_reader.py` has none -- and one the tree DOES give a
  feed (`owner`, `fn`) that prints no line has failed instead. It asks the
  running server, never a file name, which is how this harness already decides
  everything else.

## The injection tests

`tests/test_gate_verdicts.py`, 24 tests, is the review's own
`planning/evidence/astra-followup-2026-09-20/probe.py` turned into a committed
regression with its assertions inverted. It drives the real
`scenario_feed_peer_cut` and `scenario_feed_restart` with simulated boundary
responses and requires, for each injected outcome, the named assertion to fail
AND the gate's exit to be nonzero:

| injected | assertion | verdict | exit |
| --- | --- | --- | --- |
| the article never arrives after the cut | `cut-arrival` | violated | 1 |
| two accepted transfers across one lost reply | `cut-at-most-one` | violated | 1 |
| the final group count is wrong | `cut-copies` | violated | 1 |
| POST refused, so nothing was queued | `cut-post` | violated | 1 |
| the tap never took the cut | `cut-taken` | inconclusive | 3 |
| no tap in front of node B | all four cut rows | inconclusive | 3 |
| POST not offered at all | all six cut rows | not-built | 0 |
| no arrival after the `kill -9` | `k5-arrival` | violated | 1 |
| two accepted transfers across the kill | `k5-exactly-one` | violated | 1 |
| node A does not restart | `k5-restart` | violated | 1 |
| no offer recorded after the restart | `k5-offer-recorded` | inconclusive | 3 |

plus: a clean run of each scenario holds every row and exits 0; a violation
outranks an inconclusive; `held` with an undeclared key, an undeclared
instance, an undecided verdict with no blocker and an unknown verdict each
raise; an assertion the run never reached is emitted `not-exercised` with a
blocker; and editing one row's verdict breaks the digest.

## What this invalidates

See the report. The committed gate evidence already carried the sentences; the
runs carried exit 0.

## Open, and who owns it

1. **`tests/deploy_gate_fake` has no owner.** All four dry-run fixtures now
   exit 1 for one true reason: the deployed tree carries the real
   `tools/run_owner.py`, the fixture's ACL2 is a shell script, so the owner
   cannot reach LISTENING and the gate falls back to the reader. The tests
   pin the violated KEY SET rather than the exit code, so this is loud and
   exact, but a `tests/deploy_gate_fake/tools/run_owner.py` would make the
   fixtures green honestly and would let the feed rows be exercised in a dry
   run for the first time. It needs a fake with an outbound feed, which is
   real work and is not this lane's.
2. **`v0_matrix.py` has no `inconclusive`.** A row whose observation was
   insufficient becomes `not-exercised` there and exits 0, which is the same
   shape F1 had one level up. Its owner should decide whether a matrix row can
   be undecided.
3. **`entry-point-listening` on a `--server-command` tree.** When the operator
   names an entry point, the gate takes the name at its word and does not
   fall back; if that program does not start, `start_node` returns False and
   the gate raises. That is right, but the finding is not recorded on that
   path.
