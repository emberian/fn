# D23 release authority: carriage is not release authority

Lane `d23-issuer-authority`, 2026-09-24, on hbox. Source: branch
`lane/d23-issuer-authority` from dev `19709182` (commits `08135a90`,
`2fdb83b3`, `95069712`, and the record commit). The DTN developer image was
built from `git archive 95069712` by
[`lab.sh`](d23-issuer-authority-2026-09-24/lab.sh); everything ran under
`/tank/fn/scratch/d23-issuer/`. Reports and logs are in
[`d23-issuer-authority-2026-09-24/`](d23-issuer-authority-2026-09-24/) with
a `SHA256SUMS`. dtn7-rs is the pinned 0.21.0 checkout `/tank/fn/dtn7/repo`.

## Result in one paragraph

Through one dtn7-rs relay, with A's return boundary carrying B's EID but not
releasing for it, B accepts the request under the author's enrollment
(`carried carrier=ingress-boundary author=sender-author`,
`request-accepted`), B's receipt reaches A, ACL2 prints `BP node release
carried-not-released carrier=return-boundary issuer=dtn://receiver/`, A
answers `receipt-refused`, the obligation stays `outstanding pinned=yes`,
and A's kind-7 FNBS row keeps `release=carried-not-released`. With a
`releases-for dtn://receiver/` row on the same boundary the receipt is
`listed-issuer`, `receipt-accepted`, `receipted pinned=no`, with one and with
two relays. The direct control is `self-issued`, `pinned=no`. Before this
change (lane d23-bp-carrier) the carried list alone released the pin.

## What changed

Four predicates, each with its own configuration input (spec
[bp-node-machine §6.1](../../specs/bp-node-machine.md)):

| question | function | input |
| --- | --- | --- |
| neighbour admitted | `fn-bpaj-neighbor-admittedp` (`books/bp-session-admission.lisp`) | boundary listener/trust/transport rows |
| origin carriage | `fn-bpaj-origin-carriage-permittedp` (same) | `bp-boundary-carries` rows; takes `(:bp-source-eid E)` |
| author publication | `fn-bpah-author-publication-authorizedp` (`books/bp-app-handoff.lisp`) | the author's own boundary; takes `(:principal P)` |
| receipt release | `fn-bpah-receipt-authorizes-releasep` (new `books/bp-release-authority.lisp`) | `bp-boundary-releases-for` rows and the held obligation; takes `(:release-issuer-eid E)` |

- `fn-bpah-receipt-trustedp` reads `fn-bpah-release-issuer-authorizedp`
  (the neighbour's own EID, or the release list), not the source decision.
- `bp-boundary add ... [carries EID ...] [releases-for EID ...]`
  (`fn-native-admin-bp-boundary-plan`) writes the separate row kind;
  default empty; the configuration record and replay carry it.
- Host: `fnn-bpnode-receipt-result` prints `BP node release ...`, refuses on
  the gate before opening FNWF, then publishes only
  `fn-bpah-receipt-release-record` (through
  `fn-owner-bp-receipt-release-record`); the kind-7 detail is ACL2's
  `fn-bpah-release-detail` of `fn-bpah-receipt-release-verdict`.
- Provenance accessors over a held row: `fn-bpah-held-received-from`,
  `fn-bpah-held-claimed-source`, `fn-bpah-held-verdict`,
  `fn-bpah-held-policy-row`; for requests, `fn-bpah-held-source-decision`.

## Theorems (PRF-075)

| theorem | statement | host line |
| --- | --- | --- |
| `fn-bpah-unauthorized-issuer-releases-nothing` | issuer not authorized for release at the delivering neighbour: receipt gate false and release record nil | `host/native/bp-node.lisp` 104/110 (gate), 120 (record) |
| `fn-bpah-carrier-without-release-row-releases-nothing` | neighbour's boundary has no `transport-bp` and no `releases-for` row for the issuer (carried rows unconstrained): same conclusion | same |
| `fn-bpah-released-receipt-names-exactly-its-obligation` | a non-nil record: issuer authorized, the work the receipt's id finds is outstanding and passes `fn-bp-authorized-receiptp`, the record names that work's id, and the workflow image admits it | 120 |
| `fn-bpah-receipt-naming-other-terms-releases-nothing` | no outstanding work for the id, or a different subject, policy or terms: record nil | 120 |
| `fn-bpah-request-trust-ignores-release-rows` | configurations equal after dropping release rows (same generation and well-formedness) trust the same requests | 36/60 |
| `fn-bpaj-source-decision-ignores-release-rows` | the same for the source decision (keystone of the one above and of `fn-bpaj-ingress-peer-ignores-release-rows`) | via the above |

Teeth, one `must-fail` per hypothesis, and reachable witnesses (a real
FNWF image with an outstanding pinned work) in
`tests/acl2/bp-release-authority-tests.lisp`; typed-list and carriage teeth
in `bp-session-admission-tests.lisp`; gate, line and provenance witnesses in
`bp-app-handoff-tests.lisp`; grammar and replay in `native-admin-tests.lisp`.
The theorems of PRF-075 that said the receipt gate answers like a direct
one (`...-judged-as-the-authors-direct-request`, `...-unlisted-...`,
`...-unenrolled-...`) no longer claim anything about receipts; that claim
was the collapse this lane removes.

## Certification (hbox, ACL2 8.7, w28 `acl2-literal-4g`, 2 jobs, 300 s)

| run | roots | result | manifest |
| --- | --- | --- | --- |
| `run-20260924T231033Z-cfaf` (`08135a90`) | `--affected-by` bp-session-admission (74) and native-admin: 90 roots, 94 certified | passed; `bp-release-authority` 15.9 s and `native-admin` 13.1 s over the rule | `manifests/certify-20260924T231054Z-2148356.json` |
| `run-20260924T232022Z-575d` (`95069712`) | `--affected-by` native-admin and bp-release-authority: 18 roots, 20 certified | **passed**; `native-admin` 9.6 s, `bp-release-authority` 4.5 s, its tests 4.8 s | `manifests/certify-20260924T232040Z-2181356.json` |

The second run's two changed books are the only ones whose bytes moved
after the first; `bp-app-handoff` 5.3 s, `bp-session-admission` 5.8 s,
`bp-transit-join` 5.0 s, their tests under 6 s (first run).

## Image and labs

`fn-host-dtn-developer` from `95069712`: `proof_artifacts validate` loaded
109 dtn roots, 0 `undefined` build lines; launcher `add3be754e122b69`, core
`9dbadcd5a23d3474` (full in `lab.log`). Scratch, not frozen.

| run | A's boundary | B decision / application | A release line | A result | A obligation after | report |
| --- | --- | --- | --- | --- | --- | --- |
| control, direct | `transport-bp` B | `direct` / request-accepted | `self-issued` | receipt-accepted | `receipted pinned=no` | `44d2437372cb72f3` |
| 1 relay, **none** | carries B, no release | `carried ... author=sender-author` / request-accepted | `carried-not-released` | **receipt-refused** | **`outstanding pinned=yes`** | `81fd81fa17175a3e` (A log `4e712956b3501922`) |
| 1 relay, listed | carries B, `releases-for` B | same / request-accepted | `listed-issuer` | receipt-accepted | `receipted pinned=no` | `e2ff69594b28a359` (A log `bd63c534736db030`) |
| 2 relays, listed | same | same / request-accepted | `listed-issuer` | receipt-accepted | `receipted pinned=no` | `0ac5e5bfc9880ebc` |

Each run: step 1 uncertain (first hop SIGKILLed mid-transfer), step 2
accepted on resume. A's FNBS lifecycle file holds exactly one
`release=<verdict>` detail per run, matching the release line
(`carried-not-released`, `listed-issuer`, `self-issued`).

## Findings

1. **Transitive trust.** The release row is a finite delegation: A trusts the
   listed relay to hand on B's receipts faithfully; nothing authenticates B's
   receipt. A listed relay can forge a receipt naming the exact obligation.
   Release through an untrusted intermediary needs a signed receipt bound to
   the authorized issuer; open.
2. **A direct neighbour is its own release issuer** without a row (the
   `trusted-local-observation-v0` profile the control relies on). Requiring a
   row for the direct case too would be a one-clause change in
   `fn-bpah-release-issuer-authorizedp`.
3. **A request's policy row and verdict are not stored bytes**: its kind-7
   detail is the receipt id the owed handoff binds. They are re-derived from
   the kind-5 row and the configuration record of the stamped generation.
4. **Kind-7 receipt detail changed** from the receipt id to
   `release=<verdict>`. No reader used the old value (grep over host, tests,
   tools).
5. **`books/bp-node-fragment-step` measured 10.09 s** in the first run (not
   changed here; its history on hbox at 2 jobs is 7.6 to 12.9 s). The
   `proof_cost` ratchet reports it.
6. The four-node lab was not rerun; its carried mode uses
   `run_fn_dtn7_app_receipt.py`, whose default is now `--a-releases listed`.

## Stopped and released

Processes were started and stopped by the lab by PID (each `report.json`
`processes`/`dtnd_processes`); REPL sessions `isa`, `iah`, `ina`, `ina2`,
`inad`, `ira` and the install sessions stopped; `/tank/fn/node` untouched.
