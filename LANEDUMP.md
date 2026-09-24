# LANEDUMP: two-store-join

## Files added or changed
- `tools/runbooks/two_store_join.py` (new, SHA-256 c88160cf459d3959928f6ae913f455ed9ff49971b89619518ab7b49c884c99e6)
- `tools/runbooks/README.md` (one entry)
- `planning/evidence/two-store-join-harness-2026-09-24.md` (new)

No books/, specs/, host/ or Mini changes. `make check` exit 0.

## Command for a new image (run on the Mac, ssh alias hbox)
    python3 tools/runbooks/two_store_join.py run \
      --image-dir /tank/fn/gates/<gate>/build \
      --mini-bin /Users/ember/dev/minidregg-wt/fn-evidence/.lake/build/bin/minidregg-host \
      --mini-sha256 0cce4fbd02c5b5156fb061e2d96f2e25e12588c35b59d2fd2efe20acb202f286 \
      --scratch /tank/fn/scratch/two-store-<date>/<run> \
      --local-out <fresh local dir> --cut none   # then a-accepted | b-verdict | ack-response | reply-at-b
The image dir needs fn-host(+.core) and a manifest (image.sha256 or freeze/image-pair.sha256);
fn-host-developer(+.core) is needed only for the a-accepted and reply-at-b cuts. The path must be under /tank/fn/gates/ (Mini bridge rule).

## Dry run on 863c2141 (Mini 0cce4fbd...)
- none: 22 steps ACCEPTED; step 23 b-verdict-gen1 REFUSED. B has HDR :fn-verified "0 absent no-record", its poll is a 30,338-byte event, and consumer-project refused codec.
  A-side control: same R, "0 verified ... keyring 1". This is the expected negative, not a harness bug.
- a-accepted: the cut ran fully and its invariant held. A stopped after durable :feed-sent, R was absent at B, A was SIGKILLed and restarted, R was durable at A, R reached B, GROUP counted 1/1. It then stopped at the same b-verdict-gen1 REFUSED.
- b-verdict: stopped at the same REFUSED step. The cut boundary (after Mini's transaction, before ACK) was not reached.
- Cut families passed on 863: a-accepted only. Not reachable: b-verdict, ack-response, reply-at-b.

## Left on hbox
- Scratch (kept): /tank/fn/scratch/two-store-20260924/dry-863-{none,a-accepted,b-verdict}/ (stores, logs, steps.json, summary.json, pids.log, console.txt, mini-side/)
- PIDs: none running. All harness-started owners were stopped (see each pids.log). Ports 11201/11202 are free again.

## Next concrete experiment
Once a source-matched image containing peer-authored ingress (c12f4f28, 9963dbbe, e7aeac8f and later) is frozen, run `--cut none` against it.
Step b-verdict-gen1 must become ACCEPTED (keyring 1, projected source = R). The first unexercised seam is then steps 6-9 (Mini at B, reply, Mini reply-consumer at A).
After that, run the four cuts one at a time. Known risks are listed in the evidence record under "Expected on the repaired image".
