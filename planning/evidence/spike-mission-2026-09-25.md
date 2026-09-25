# The mission lab on hbox, 2026-09-25 (spike/mission, D28)

The integration harness the spike lanes plug into: four native fn nodes on
hbox, NNTP peering A-B and C-D, a BP link B-C through two dtn7-rs relays
with a switchable partition, one demo and one status screen, from one
command. What works, every deferral, and the gaps the demo exposed, each
as a finding with its log line. Nothing here is a proof; `dev` owns the
proved re-implementation of what this record specifies.

## Environment

| | |
| --- | --- |
| tree | `/tank/fn/gates/spike-mission-0e2173ab` = `spike/mega` at `0e2173ab` plus the lab tools (`tools/mission_*.py`, `docs/mission-lab.md`) |
| images | `build/images/0e2173ab7b4f68e66081955472b69291988ceed8/` (`fn-host`, `fn-host-developer`, `fn-host-dtn`, `fn-host-dtn-developer`), built by `tools/runbooks/hbox-image-build.sh` at 04:18 EDT; log `build/freeze/image-build.log` |
| certificates | the cache held no usable pair for 55 of the 320 closure books (67 were `foreign-local`: made in another live worktree on hbox); one incremental run on hbox certified them, all pass: `planning/evidence/manifests/certify-20260925T080909Z-2837376.json` (`certify_books.py --jobs 4 --incremental` over the 133 default+dtn roots, `FN_CERT_ORIGIN_KIND=run`, ACL2 `/tank/fn/toolchains/w28/acl2-literal-4g`). `farm.py submit` refused the same plan with an unparsed preflight; the runner was started by hand under `swarm-build` |
| dtn7-rs | `/tank/fn/dtn7/repo` at `4daf02d` (the pin), `dtnd -D sled -r static --disable_nd -j 5s` |
| OpenSSL | `/tank/fn/toolchains/openssl-3.5.8` (ML-DSA-65); its binary needs `LD_LIBRARY_PATH` to its own libraries ahead of the system 3.3.1 |
| lab root | `/tank/fn/scratch/spike-mission/lab` (prototype runs on the `c3420013` images under `proto-old-*`) |
| commands | `docs/mission-lab.md`; every run under `swarm-build` |

## What works

(filled from the runs below)

## Runs

(filled from `demo/<tag>/demo.json`)

## Latencies

(filled)

## Deferrals

Every one is marked `;; SPIKE` in `tools/mission_lab.py` or
`tools/mission_demo.py`.

1. K6 (one transit decision for NNTP and BP): `operator CONFIG run` and
   `bp-node serve` each take a store's writer lock (`fnn-owner-install` ->
   `fnn-open-live-store root t`, `host/native/owner.lisp:460`,
   `host/native/bp-node.lisp:703`), so B and C carry two stores and the demo
   bridges them host-side: `store post` into the BP store, `store inspect`
   out of it, `operator post` into the NNTP owner.
2. The receipt's return past B: NNTP has no application receipt; C's receipt
   releases B's BP obligation and A's obligation to B is B's streaming
   reply (the feed journal `A/store/feed/B.fnfd`).
3. Status over the control socket: `bp-obligation status`, `store
   retention`, `operator status` are offline verbs; the status screen and
   the demo stop the serving node when they must read them.
4. Author enrolment in a BP store: `hybrid-enroll` needs an owner's control
   socket and the DTN image has none, so a developer owner serves the BP
   store for the enrolment and stops.
5. The link is a Python TCP proxy pair, not a modelled contact plan; the
   relays route by dtn7 static routes, not `books/scheduler`.
6. The cancel is C1 filing only (`control.cancel` created on every node,
   `Control: cancel` posted unsigned by `ember`); no authority, no
   withdrawal.

## Findings

(each with the log line)

## Box safety

Every process the lab started is in `lab.json` (`pids`, then `stopped`
with the signal that ended it); `down` signals only those. Kernel ports
12101 to 12191 were free (`ss -ltn`) before `up`. The live node
`/tank/fn/node` was not touched. ACL2 ran on hbox only (the certification
runner); no `find` over `build/` or `/`.
