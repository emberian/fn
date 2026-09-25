# Signed receipts: release through an untrusted intermediary

Lane `signed-receipts`, 2026-09-25, on hbox. Branch `lane/signed-receipts`
from dev `e8f4faa5`; books at `d50823bc`. The review of 2026-09-24 (D23,
"The receipt condition") asks that release through an untrusted
intermediary bind and verify the receipt itself against the authorized
issuer and exact work, content subject, requester and terms; the D23
issuer lane left it open (its finding 1: a listed relay can forge a
receipt naming the exact obligation). Logs and reports are in
[`signed-receipts-2026-09-25/`](signed-receipts-2026-09-25/) with a
`SHA256SUMS`; the recipe is its `lab.sh`.

## Result in one paragraph

Through one dtn7-rs relay, with A's return boundary carrying B's EID, with
NO release row, and flagged `require-signed-receipts`, and A's own boundary
for B naming B's hybrid principal as `receipt-signer`: B signs its receipt
(`BP node receipt signed principal=4242424242424242 octets=3655`), A
prints `BP node release signed-issuer carrier=return-boundary
issuer=dtn://receiver/`, answers `receipt-accepted`, the obligation is
`receipted pinned=no`, and A's kind-7 row keeps `release=signed-issuer`.
With a proxy between B and the relay that flips the last octet of the
receipt's ML-DSA-65 signature and recomputes the payload block's CRC32C
(the bundle stays well-formed): `signature-refused`, `receipt-refused`,
`outstanding pinned=yes`, kind-7 `release=signature-refused`.

## What changed

- `books/bp-signed-receipt.lisp` (new): the frame `FN-BP-SRCPT` (bytes
  magic, uint 0, bytes ADU, bytes principal, bytes Ed25519 signature, bytes
  ML-DSA-65 signature), decoder with an exact re-encode check, and
  `fn-bpsr-adu-octets`, through which every reader reads a receipt ADU.
- Classification reads through it: `fn-bpah-held-adu-result`
  (`bp-node-foundation`), `fn-bpnp-local-class` (`bp-node-progress`, one
  line, so `fn-bpnp-local-class-refines-a3` still holds),
  `fn-bpah-view-receipt` and `fn-bpah-outbox-job-matchp` (`bp-app-handoff`;
  the return job carries FNRJ's exact ADU bare or signed, since ML-DSA-65
  signing is hedged), and the `bp-handoff-status` theorems restated so.
- `books/bp-release-authority.lisp`: preimage `fn-bpsr-signed-preimage`
  (table: [spec §6.1](../../specs/bp-node-machine.md), "The signed receipt
  bytes"), `fn-bpah-receipt-signature-verifiedp` (the third way),
  `fn-bpah-receipt-authorizes-releasep` with it, the host gate
  `fn-bpah-receipt-gatep`, plan/line/verdict (`signed-issuer`,
  `signature-refused`, `signature-required`).
- `bp-boundary add ... [receipt-signer HEX] [require-signed-receipts]`
  (`books/native-admin.lisp`, a wrapper over the unchanged base plan).
- Host: B signs in `fnn-bpnode-signed-receipt` when `bp-node serve` has a
  signer directory (20th argument); A observes both primitives with
  `fnn-hsig-observe-raw` over ACL2's plan and ACL2 decides
  (`host/native/bp-node.lisp`, `host/bp-native-app-host.lisp`).

## Theorems (PRF-075, `books/bp-release-authority.lisp`)

Host subject: `fn-bpah-receipt-release-record view cfg wf snapshots obs`,
called through `fn-owner-bp-receipt-release-record` by
`fnn-bpnode-receipt-result`; the gate `fn-bpah-receipt-gatep` through
`fn-owner-bp-receipt-gatep`.

| theorem | statement |
| --- | --- |
| `fn-bpah-signed-receipt-releases-through-any-carrier` | signed, delivered shape, signature verified under the issuer's own enrollment: record = workflow's answer for the carried ADU with authorization = the obligation check; no hypothesis on the carrier's rows or flag |
| `fn-bpah-unverified-signed-receipt-releases-nothing` | signed and not verified: gate false, record nil, whoever delivered it |
| `fn-bpah-receipt-signature-needs-both-observations` | verified implies both observations `:verified` and the issuer's own signer row |
| `fn-bpah-trusted-bare-receipt-releases` | bare, unflagged carrier, gate trusts: record = workflow's answer (the delegation profile: a listed relay's forgery releases) |
| `fn-bpah-required-signature-refuses-bare-receipts` | bare under `require-signed-receipts`: gate false, record nil |
| keystones 1, 1', 2, 3 | restated with the keyring and observations; 1 and 1' now about bare receipts; 2's authorization conclusion names the signed or the bare way |

Teeth and witnesses: `tests/acl2/bp-release-authority-tests.lisp` (a real
FNWF image; keyring snapshot built with `fn-hsig-keyring-event`; frame
round trip; preimage binds the requester; signed release through the
flagged unlisted relay; failing observations; other terms; signer row on
the carrier instead of the issuer; unenrolled principal; bare receipt under
the flag; one must-fail per hypothesis of each keystone above).
Observations there are abstract (A-CRYPTO): they test the decision, not
Ed25519 or ML-DSA-65. Grammar witnesses in `native-admin-tests.lisp`.

## Certification (hbox, ACL2 8.7, w28 `acl2-literal-4g`, 2 jobs, 300 s)

| run | roots | result | manifest |
| --- | --- | --- | --- |
| `run-20260925T010122Z-7b8e` | bp-app-handoff, bp-handoff-status (4 certified) | passed | `manifests/certify-20260925T010134Z-2304740.json` |
| `run-20260925T011352Z-6ac1` (`4dc6aef6`) | `--affected-by` bp-signed-receipt, native-admin, bp-release-authority, bp-handoff-status: 124 roots, 125 certified | 124 passed, `native-admin-tests` failed (a test constant), `native-admin` 62 s | `manifests/certify-20260925T011416Z-2317683.json` |
| `run-20260925T012218Z-e558` (`d50823bc`) | `--affected-by` native-admin: 16 roots, 18 certified | **passed**; `native-admin` 10.9 s | `manifests/certify-20260925T012235Z-2325138.json` |

The second run's books other than native-admin and its tests are at the
same bytes in `d50823bc`. `bp-release-authority` 4.5 s, its tests 4.9 s.

## Lab

DTN developer image from `d50823bc`: 0 `undefined` build lines, launcher
`676622601de93c01`, core `069b0dd77478195f`. A's enrollment of B's keys
used the qualified default image of `c3420013`
(`/tank/fn/scratch/qual-c3420013/tree/build/fn-host-developer`, sha256
`e12edb0196111a1e`) for `operator run` and `hybrid-enroll` only (the DTN
image has no NNTP owner); the keyring format is unchanged on this branch.

| run | A's return boundary | B | A release line | A result | obligation after | report | A log |
| --- | --- | --- | --- | --- | --- | --- | --- |
| relay1-signed | carries B, no release row, `require-signed-receipts` | signs (3655 octets) | `signed-issuer` | receipt-accepted | `receipted pinned=no` | `106e177064ba1206` | `43e4a997a2c83f28` |
| relay1-flipped | same; proxy flips the ML-DSA-65 signature's last octet | signs | `signature-refused` | **receipt-refused** | **`outstanding pinned=yes`** | `db0ecf23c4496c15` | `224f2fa6014cc65a` |

Each: step 1 uncertain (first hop SIGKILLed mid-transfer), step 2 accepted
on resume, B `request-accepted` under the author's enrollment.

## Findings

1. The flip proxy recomputes CRC32C; without that the bundle fails its
   CRC at the relay and the case would test BP integrity, not the
   signature.
2. `fn-bpah-held-policy-row` returns nil for `signed-issuer`: the row
   that verdict rests on is the issuer's own `receipt-signer` row plus a
   keyring snapshot, not a row of the carrier's boundary. Not added.
3. The obligation check is not a separable hypothesis of the positive
   keystones: the workflow's own admission refuses what
   `fn-bpah-receipt-names-obligationp` refuses on the probed cases, so the
   keystones state the record with the obligation check as its
   authorization instead of assuming it.
4. `tests/native_bp_node_admission_lock_raw.lisp` was already red on dev
   (`fnn-bpnode-test-busy-p` undefined since BP-R17); stubbed, now PASS.
5. `bp-boundary show` does not render the two new rows.
6. `native-admin` certified at 10.9 s (history 9.6 to 13.1 s).
7. The receipt signer directory is a positional argument; the signer's
   own keyring is not consulted at B (A's enrollment is what binds).

## Stopped and released

Lab processes were started and stopped by the lab by PID; REPL sessions
`sr`, `ra`, `na` stopped; `/tank/fn/node` untouched.
