# Four-node carried-media lab, 2026-09-20

A complete run. `tests/evidence/2026-09-20-four-node-lab.json` is the machine
record the lab wrote; this file says what it means. It replaces the incomplete
run w3/media-lab recorded on the same date, whose stop is described and closed
in `planning/lanes/HANDOFF-w6-workflow-restart.md`.

- Command: `python3 tests/bp-dtn7/run_four_node_lab.py`, mock BPA transport,
  Python 3.14.7, ACL2 through `tools/run_store.py` against the certificates
  installed in this worktree. Revision is in the JSON. 40.5 s.
- Status: **passed**. All twenty-two named assertions were checked and every
  one held, including the eleven the earlier run never reached: the carried
  media hop with no contact window, the lost-and-regenerated receipt, the
  expired attempt and its retry under the next window, the reordered pair with
  a duplicate, and each node's local-number frontier.
- Two defects were fixed to get here, neither in the workflow model. The lab
  submitted an attempt whose `bp-lifetime` was not the configured one, which
  `fn-bp-record-contextp` refuses; and `tests/bp-dtn7/mock_bpa.py` spooled its
  queue under a digest of the BID, so the queue was not first in, first out and
  the reordered-pair assertion read the wrong order. Nothing in the ACL2
  acceptance path was relaxed.
- `relay_a_onward_obligation_recoverable_after_kill` is back and holds: after
  the mid-forward SIGKILL of relay-a and its recovery, `work:a1:relay-a` reads
  `outstanding`, and `absent` now means only that the image holds no such work.
