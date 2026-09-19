# HANDOFF — w3/ltp-ion (C1-12 LTP feasibility with a real second BPA)

HEAD before this lane: `9321344` (dev). Worktree:
`/Users/ember/dev/fn/build/lanes/w3-ltp-ion`, branch `w3/ltp-ion`.
All heavy work ran on hbox under `/tank/fn/ltp/`; only logs and small evidence
came back.

## What ran

- ION-DTN pinned at tag `ion-open-source-4.2.1-a.1`, commit
  `4912bf82de7d03a9a11bf5d68614cc002f9ac911`, built clean with
  `autoreconf -fi && ./configure --prefix=/tank/fn/ltp/install && make -j8 &&
  make install` (hbox needed `libtool` installed first; without it `configure`
  fails with `LT_INIT: command not found` and then `"OS  is not supported"`).
- Two ION nodes `ipn:1`/`ipn:2` over an LTP/UDP loopback link with
  `ltpclock`/`ltpmeter`/`ltpdeliv`/`ltpcli`/`ltpclo`. `bpsource`→`bpsink`
  confirmed BP-over-LTP. Every config file is committed in `tests/ltp/`.
- `tests/ltp/fn_ltp_stage.c`: an ION receiver that durably stages one ADU
  (temp write, fsync, rename under the RFC 9171 bundle id, dir fsync) before
  releasing delivery. Built against the installed ION headers/libs.
- `tests/ltp/run_fn_ltp_lab.py`: ACL2 fn sender work → 449-octet request ADU →
  LTP → durable staging → `tools/run_bp_receive.py` acceptance. **Passed**:
  byte-identical ADU, outcome `accepted`, one record/article/pin, exact article,
  staged copy deleted only after the receipt decision committed. Run from the
  certified tree `/tank/fn/gates/dev-9321344` with
  `FN_ACL2=/tank/fn/acl2-8.7/saved_acl2`.
- `tests/ltp/interrupt_expiry.sh`: 20 s UDP outage mid-transfer of a 60,000-octet
  ADU — nothing staged while cut, LTP resumed and repaired, arrived
  byte-identical. Expiry case — 20 s lifetime into a 60 s outage, nothing ever
  staged. Link cut with one named `iptables` rule, deleted by spec; the ruleset
  was never flushed and ION's `killm` was never used.

## Blockers (detail in `planning/ltp-feasibility.md`)

- **LTP-B1** ION has no non-destructive receive. `bp_receive()` deletes the
  delivery element, zeroes the payload, destroys the bundle and commits before
  returning; `bprecvfile` writes `testfile<N>` with no fsync, no rename and a
  per-process counter. An app-level staging copy is mandatory, its `delete`
  is of fn's own file, and the commit-to-fsync window is irreducible through
  ION's public API — covered at the fn layer by retry and receipt idempotence.
- **LTP-B2** ION returns no bundle identifier to the sender (`bpsendfile` prints
  none, `bp_send()` returns an in-process `SdrObject`). No transport handle for
  a durable attempt to bind, so **no receipt return leg was attempted**.
- **LTP-B3** EID mapping: fn's application `peer-eid` (`dtn://fn.lab/inbox`)
  is not ION's BP destination (`ipn:2.1`); the unmapped first run failed.

## Not done

Receipt return over BP; relay topology; backpressure and staging-quota
campaign; outages past LTP's repair budget (`maxTimeouts 5`,
`maxRepairRounds 8`); real one-way light time via `owltsim`; BPSec or any
authenticated peer. This is feasibility, not C3-04, and it closes no
`REP-006`/`SCN-010/017` obligation.

## Host state

ION nodes were stopped gracefully and their shared-memory segments removed.
The pinned checkout, install prefix, run state and logs remain under
`/tank/fn/ltp/` on hbox. `tests/ltp/` was also copied into
`/tank/fn/gates/dev-9321344/tests/ltp/` so the driver could run against the
certified books; that copy is disposable.
