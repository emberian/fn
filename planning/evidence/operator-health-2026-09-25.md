# operator-health: the health verdict (PRF-112, HST-007, SCN-070, PKT-174)

Lane `lane/operator-health` from dev 483987b1, 2026-09-25/26. Brief:
`build/coordinator/queue/w2-operator-health.txt` (with node-health's PKT-098).

## What now works

`fn-native operator CONFIG health` prints one line per state, in a fixed
order, and exits with the code of the first held one:

| exit | state | decided from |
|---|---|---|
| 20 | fenced | the host's observation: clone fence file, writer lock held with the configured socket absent, or a socket that accepted and did not answer (`fn-nh-fence-of`) |
| 21 | exhausted | headroom at the codec ceiling: transactions used >= 2^32 - 1, or reserved charge >= 2^32 - 1 |
| 22 | unqualified-profile | persisted profile not format 8, or the development profile |
| 23 | space-pressure | free headroom below `[alerts] headroom_min_percent` on transactions, history octets or charge, when not exhausted |
| 24 | no-route | held `:forward` obligations and an empty `fn-bprt-table` |
| 25 | stranded-transfer | an owner feed entry dropped at its retry bound (`(:dropped :retry-bound)`) |
| 26 | unavailable-peer | an owner feed with pending work and no connection |
| 27 | receipt-debt | held `:forward` obligations |
| 19 | none held, some unobserved | offline the feed table does not exist; a fenced store is not opened |
| 0 | every state clear | |

Each line is `held` (with its figures), `clear` or `unobserved` (with why);
unobserved is never clear.

## Assurance chain

native entry `fnn-operator-execute-health` (host/native/operator.lisp) ->
route by `fn-nls-route`; live: FNLS kind 6 to the owner, which renders
`fn-nh-answer-report` -> `fn-nh-live-report` under its mutex
(host/native/control.lisp `fnn-control-live-status-answer` ->
host/native-live-status-host.lisp `fn-native-live-status-host-answer`);
offline: `fn-native-health-host-fenced` (`fn-nh-fence-of` over the lock and
clone-fence observations) or `fn-native-health-host-offline`
(`fn-nh-offline-report` over the replayed Store) -> the verdict
`fn-nh-verdict` -> rendered octets `fn-nh-render` -> the host prints them and
returns `fn-native-health-host-exit` = `fn-nh-report-exit` of the same octets.

- Representation: octet lists, like the status report (the FNLS renderer's
  twin is open there too). The offline report re-encodes every committed
  record once (`fn-sbud-bytes-used`); the live one extends the carried sum.
- Maintained relation: the carried octet sum (`fn-sbud-octets-cache-validp`),
  established by the owner at open and extended per commit
  (books/store-budget.lisp); the keystone below is conditional on it.
- Not a whole-state revalidation per command: health is an operator query,
  one render per request.

## Theorems (books/native-health.lisp)

- `fn-nh-verdict-states`: eight outcomes, each held/clear/unobserved exactly
  as the report's sources decide (table above).
- `fn-nh-exit-code-decodes`: the exit code names the first held state
  (`fn-nh-code-state`) and is 0 exactly when nothing is held or unobserved.
- `fn-nh-report-exit-of-render`: for every verdict of at most eight outcomes
  the code read back from the rendered octets is the verdict's code.
- `fn-nh-first-held-monotone`: a verdict holding every state another holds
  has a first held state no later (more faults never a milder code).
- `fn-nh-pressedp-monotone`: more use or a higher threshold never clears
  pressure.
- `fn-nh-live-report-is-the-store-report`: with the carried sum valid the
  owner's report is the verdict over its Store's own octets, configuration
  and feed table.
- `fn-nh-fence-of-route`: an uncertain route is always fenced; otherwise the
  clone fence and the lock decide.

Teeth (tests/acl2/native-health-tests.lisp): reachable instances over the
host-shaped owner state of native-live-status-tests (development profile:
exit 22 and its first line), a synthetic feed table (stranded + unavailable,
exit 25), forwarding pins (count 2, charge 7), the codec-ceiling boundary for
exhausted vs pressure, the fenced report (exit 20), exit 0 and 19. Must-fails:
report-exit without the length bound (81 outcomes: code 100 prints "00"),
monotone without covers and without a held state, pressure without each of
its three premises, the live keystone with a stale sum (min 100: the held
pressure line prints the stale history-octets), fence-of without the route
hypothesis. `fn-nh-exit-code-decodes` holds for every verdict length, so it
carries no length hypothesis.

## Certification

| run | box | what | result | manifest |
|---|---|---|---|---|
| run-20260925T234708Z-0716 | persvati | affected-by native-live-status, native-operator (22 books) | passed; native-live-status 3.6 s, native-operator 3.6 s, native-mission 1.5 s | `manifests/certify-20260925T234730Z-2706900.json` |
| run-20260926T002909Z-b8b1 | hbox | 156 default image roots + native-health-tests, incremental | passed; native-health 4.7 s, tests 6.1 s, native-live-status 9.8 s | `manifests/certify-20260926T002921Z-4138097.json` |
| run-20260926T010419Z-6268 | hbox | the same at 30d87fbe | passed; native-health 5.2 s, tests 6.8 s | `manifests/certify-20260926T010443Z-10040.json` |

owner-invariants 12.5 s on persvati is the known pre-existing cost debt
(not changed here).

## Native (hbox, developer image)

Image: `build/fn-host-developer` from `git archive` of 30d87fbe in
/tank/fn/scratch/operator-health/tree, built under `swarm-build` (artifact
set acquired from /tank/fn/certcache, 156 roots loaded). Launcher SHA-256
af59712b3ab462ff704040c7bf9728a50889f453905db403e9a3d68586e9fcc9, core
4500e041b2201b78dcd14e854be91eb60b223f53371cf21c3eff17dfde6ff8d0.

Run: `native.sh` (this directory), scratch nodes under
/tank/fn/scratch/operator-health/run on loopback ports 31501-31599, owners as
`systemd-run --user -p MemoryMax=24G` units. Every output and its SHA-256 is
in `operator-health-2026-09-25/native-out/` (SHA256SUMS itself:
627c9ba5772b30314e7730aed3234d3dabef8656a30c9655bfb2b189ac24db04).

| case | how | exit | line held |
|---|---|---|---|
| unqualified-offline | `init --profile development` (mission line removed) | 22 | unqualified-profile `format=8 development` |
| clear-offline | the small-community mission profile, fresh store | 19 | none; the two feed states unobserved |
| pressure-offline | one offline post, `headroom_min_percent=100` | 23 | space-pressure `transactions=1/4294967295 history-octets=440/... charge=2/1048576` |
| clear-live | owner running, peer `hub` on a closed port, nothing queued | 0 | none (all eight clear) |
| unavailable-live | one post into `local.test` | 26 | unavailable-peer `peers: hub` |
| fenced-store-held | the owner's control socket moved away | 20 | fenced `reason=store-held`; the other seven unobserved |
| fenced-unanswering | the owner SIGSTOPped with its socket present | 20 | fenced `reason=owner-unanswering` |
| stranded-live | a loopback peer (`defer_peer.py`) answering 431 to every CHECK | 25 | stranded-transfer after three CHECKs (the retry bound) |
| no-route-offline | `bp-obligation undertake` with no `bp-route` | 24 | no-route and receipt-debt |
| receipt-debt-offline | `bp-boundary add` + `bp-route add` | 27 | receipt-debt only |

Findings from the harness passes (kept as the first confusing actions of the
operator walk):
- `init --profile P` under a mission `fn.toml` is a usage error
  (`MISSION-FIXES-PROFILE`); choosing a profile means removing `[ops] mission`.
  The usage line says so; docs/operator.md does not yet.
- `health` (and `status`, `run`) on a configuration whose store was never
  initialized is `fault ... missing store directory` (exit 4), not a usage
  or refused answer. Classification: implementation (a missing store is an
  operator error, not a host fault); left for the walk.
- A peer that answers `501` to `MODE STREAM` is re-dialled with `MODE STREAM`
  indefinitely (no IHAVE fallback; defer-peer log of the first pass,
  unavailable held the whole time). Classification: implementation, in the
  outbound feed; not changed here.
- A run with `kill -STOP $PID` where the unit had no main PID stopped the
  harness's own process group (harness defect, fixed in native.sh).


## Not done, and why

- **Exhausted (21) natively:** unexercised capability. It needs 2^32 - 1
  committed transactions (or that much reserved charge); the ACL2 witness
  covers the boundary. A development profile's budget reached is space
  pressure (raisable by `store upgrade-profile`), not exhaustion.
- **BP node sources:** stranded and unavailable are read from the NNTP
  owner's outbound feed table. The DTN image's stranded forwarding rows
  (`bp-node resume`), its contacts and route liveness are not a source yet:
  that image carries no NNTP owner and `health` runs in the store image.
- **Task 3 (the full operator walk from nothing to a recovered node) and task
  4 (the packaging wrapper on the proved path):** not reached within the
  budget. docs/operator.md still carries a duplicated block (the
  "Install the native production entry" to "Stranded forwarding rows"
  sections appear twice); the walk should fix it with the verbs.
- **Task 2 (operator-config continuation):** already merged on dev
  (34e020a5; native-mission 1.6 s by proof work); `git log dev..lane/operator-config`
  is empty, nothing to salvage. The verb set is unchanged here apart from
  `health`.
- **Guards:** the verdict and reports are `:verify-guards nil`, as the status
  report they share inputs with (`fn-nls-report`); the leaf predicates,
  exit code, renderer and reader are guard-verified.

## PKT-174 (decision packet: where BP-node health comes from)

- Trace: `health` runs in the store image; the BP node machine state (jobs,
  contacts, pending, fenced) lives in the DTN image's journal.
- Constraint: one ACL2 verdict; the host must not compute a state.
- Default: a `bp-node health JOURNAL` verb in the DTN image that feeds the
  same `fn-nh-verdict` with a BP feed-source (stranded rows at
  `*fn-bpnp-max-forward-retries*`, contacts not holding = no route,
  unavailable neighbour), rendering the store states unobserved.
- Rejected: opening the DTN journal from the store image's `health` (two
  images' lock disciplines in one verb; cost: a second owner of the journal).
- Affected: books/native-health.lisp (a BP source), host/native/bp-node.lisp.
- Continues without it: the store image's eight lines, with the NNTP feed as
  the transfer source.

Named by assurance-triage (2026-09-26) as the scenario catalog's evidence log for SCN-070: [`summary.txt`](operator-health-2026-09-25/native-out/summary.txt), the output of `native.sh`, sha256 `7088a1905b3d47a8293a4821d5e1c368ef53cfd8a7575f1525fcd91dca67f010`.
