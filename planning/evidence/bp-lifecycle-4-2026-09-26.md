# bp-lifecycle-4 (wave 2, 2026-09-26): the BP codec widths under the node profile

Lane `lane/bp-lifecycle-4` from dev `081eb72e` (continuation of bp-lifecycle-3).
Brief: `build/coordinator/queue/w2-bp-lifecycle-4.txt`. Ids: PRF-134, PKT-294;
SCN-077 stays `specified` (below). Model: Opus 5.5.

Commits: `33b132c7` (books, host, tests), `eb7e469e` (r1 manifest, registry,
specs, native module), `99cae727` (restart names `:held-beyond-profile`),
`ca8f7bf9` (the family selector skips a family without offset zero),
`aa7dabf1` (SCN-077 harness drains the receiver's pipes), and the record commit.

## What now works

- A BP node's profile is `(ROWS OCTETS ADU BUNDLE)`: `bp-node profile JOURNAL
  NODE ROWS OCTETS [ADU BUNDLE]`, raise only, each field 1..2^24, defaults 64,
  16 MiB, 65,538, 1 MiB. A format-1 profile file (bp-lifecycle-3's) still opens,
  with the default ADU and bundle octets.
- The receive boundary applies it: a wire past `max-bundle-octets` is refused
  `bundle-beyond-profile` before it is decoded; a bundle whose ADU (a fragment's
  total ADU length) is past `max-adu-octets` is refused `adu-beyond-profile`
  before custody (`BP refused xfer=N reason=adu-beyond-profile`, observed
  natively). The held image's bound is `max-held-octets`.
- The three former data caps are codec widths at 2^24, every profile field's
  ceiling: `*fn-bpa-max-octets*` (was 65,538) with `*fn-bpa-max-article*` =
  2^24 - 2106 (was 32,768), `*fn-bpb-max-data*` and `*fn-bpb-max-input*` (were
  1 MiB), `*fn-bpnf-max-held-image*` (was 131,072); kind 5 and kind 18 carry the
  image in `(:blob . 2^24)`; `*fn-bpn-lifecycle-max-payload*` = 2^24 + 3,072.
  Existing bytes are unchanged: the ADU fields are record items
  (`fn-record-item-encode`, the generic CBOR bytes at or below 65,535 octets;
  bp-adu-tests checks a 32,768-octet article's exact old bytes), and a
  `(:blob . W)` value within 131,072 is the `:blob` octets.
- A journal whose rows or held octets exceed the profile it opens under fences
  with `restart fenced: held-beyond-profile` (natively; before this lane the
  verdict reached the operator as `fnbs-or-base`).
- A fragment family whose offset-zero row is not held is no longer planned on
  every arrival (the plan builds a canvas as long as the whole ADU).

## Theorems (PRF-134) and their host lines

- books/bp-node-profile.lisp: `fn-bpnpf-profile-read-of-octets` (keystone: a
  saved profile 2 opens as itself), `fn-bpnpf-profile-read-of-format-1`,
  `fn-bpnpf-profile-read-is-valid`, `fn-bpnpf-profile-write-never-lowers`
  (keystone). Host: `fnn-bps-read-profile` (host/native/bp-service.lisp) calls
  `fn-bpnpf-profile-read`; `fnn-command-bp-node-profile` (host/native/bp-node.lisp)
  calls `fn-bpnpf-profile-write-octets`.
- books/bp-node-profile-admission.lisp: `fn-bpnpf-admission-within-profile-is-the-channel-answer`
  (refinement to PRF-128's `fn-bpaj-admitted-receive-event`),
  `fn-bpnpf-admission-ready-is-within-profile` (keystone),
  `fn-bpnpf-admission-refuses-beyond-the-profile` (keystone),
  `fn-bpnpf-profile-within-codec-widths`. Host: `fnn-bps-receive` calls
  `fn-bpnpf-admitted-receive-event` with the profile in force.
- books/bp-node-profile-replay.lisp: `fn-bpnpf-row-past-the-octets-is-named`,
  `fn-bpnpf-replay-past-the-octets-is-refused` (keystone; extends
  `fn-bpnpf-replay-past-the-profile-is-refused` to the held image),
  `fn-bpnpf-restart-names-held-beyond-profile` (over
  `fn-bpnf-recover-fnbs-step`, the restart step the recovery event drives,
  host `fnn-bps-open`).
- books/bp-node-fragment-step.lisp: `fn-bpnf-family-without-offset-zero-is-not-ready`,
  and `fn-bpnf-family-next-memo-is-aux` re-proved over the changed memo (host:
  `fnn-bps-fragment-progress` calls `fn-bpnf-family-next`, whose :exec is the memo).
- Codec: `fn-bpa-round-trip` and `fn-bpa-encoding-bound` hold at the new width
  (statements unchanged); new `fn-bpa-read-encoded-fields-wide` and the wide
  prefix lemmas. `fn-bpfw-reassemble-is-spec` (PRF-121) untouched.
- **One statement moved**: `fn-bpn-limits-compose` (books/bp-limits.lisp, cited
  by no registry entry) stated the old finite machine, "an ADU of 65,538 octets
  plus 65,534 octets of header fits one sender job image of 131,072"; that is
  the composition P5 removes and it is false at the ADU width. It is replaced by
  `fn-bpn-limits-compose-at-the-codec-widths`. No other existing statement moved.

## Teeth

- tests/acl2/bp-node-profile-admission-tests: over PRF-128's reachable admitted
  answer, the exact profile (ADU 4, bundle = the wire) answers the channel
  answer; per hypothesis a counterexample (no bundle field; bundle one short:
  `bundle-beyond-profile`; ADU one short: `adu-beyond-profile`) and a must-fail;
  the ready keystone against an invalid profile's `:profile`; the refusal
  keystone without an admitted channel (a refused channel keeps
  `:ambiguous-peer` past both bounds) and without a profile; a fragment of a
  70,000-octet ADU carrying 4 octets has ADU length 70,000; the widths at the
  largest profile.
- tests/acl2/bp-node-profile-tests: SCN-077's profile round trip, an ADU of
  2^24 + 1 refused, a trailing octet and the format-1 text in a five-field frame
  refused, format 1 opening with defaults, each field's lowering refused;
  replay of the two kind-5 rows with held octets one short of both images
  answers `(:fault :held-beyond-profile)`, exactly enough `:ready` with both,
  a must-fail without the bound; the restart names the verdict, and another
  replay fault keeps `:fnbs-or-base`.
- tests/acl2/bp-node-fragment-step-tests: p3 without p0 has no offset-zero
  source, its plan is not ready and the selector answers nil; with p0 it is ready.
- tests/acl2/bp-adu-tests: a 70,000-octet article (refused before) encodes past
  65,538 octets and round-trips. tests/acl2/bp-limits-tests: the widths.

## Certification (hbox, w28 acl2-literal-4g, 2 jobs, 300 s)

| run | rev | manifest | result |
| --- | --- | --- | --- |
| r1 `run-20260926T033703Z-12b7` | 33b132c7 books | `certify-20260926T033748Z-255233.json` | 204 certified, 0 failed; max 9.79 s (tests/acl2/bp-node-forwarding-teeth-tests; bp-adu 2.77, bp-fnbs-codec-invariants 6.33, bp-node-profile-admission 5.53, bp-node-profile-replay 5.77) |
| r2 `run-20260926T034918Z-eb59` | 99cae727 | `certify-20260926T035040Z-277769.json` | 137 certified, 0 failed; max 9.18 s |
| r3 `run-20260926T040537Z-3ae8` | ca8f7bf9 | `certify-20260926T040600Z-305166.json` | 56 certified, 0 failed; books/bp-node-progress 11.15 s |
| r4 `run-20260926T043913Z-b7c5` | ca8f7bf9 | `certify-20260926T043930Z-327759.json` | books/bp-node-progress recertified alone: 4.83 s |

`books/bp-node-progress` is not changed by this lane (it includes
fragment-step transitively); it was 4.87 s in r1 and 5.63 s in r2 at the same
bytes, and r3 ran with hbox's load average at 5 to 7 from other lanes; r4
recertified it alone at the same bytes in 4.83 s (load 3.2). Load, not a regression.
Every book this lane changed is certified at its final bytes.

## Native (hbox, /tank/fn/scratch/bp-lifecycle-4, `native.sh`)

Image at ca8f7bf9 (DTN developer `4630ae10…`, core `d046dc78…`; developer
`10600e6c…`, core `58f2d877…`; build logs 0 undefined, 0 ACL2 errors).
The SCN-077 harness change (aa7dabf1) is Python only.

| case | result | log SHA-256 |
| --- | --- | --- |
| journal past its profile refused at open (named) | OK | 89e7545b… |
| ADU past the profile refused before custody | OK | a9e8fc11… |
| nonzero fragment then offset zero | OK | 3c1c36dc… |
| 64 fragments across a kill | OK | 20b534c8… |
| SCN-067, 70 fragments across a kill | OK | aafe6b05… |
| rotation with a family in flight | OK | 5cf6b779… |
| test_bp_service_native | OK 17 | 96e19784… |
| test_bp_contact_native | OK 2 | 25fca7a9… |
| test_bp_contact_relay_native | OK 1 | a0c650ab… |
| test_bp_app_native | OK 5 | d7afb2b2… |
| test_bp_node_native | OK 27 | 29acc298… |
| test_bp_receive_integrity_native | OK 4 | 4d491f1d… |
| SCN-077 | not completed (below) | 3fe11fd1… |

At eb7e469e the journal case failed with `restart fenced: fnbs-or-base`
(implementation: the named verdict was dropped at the restart step), repaired
in 99cae727. Logs: `bp-lifecycle-4-2026-09-26/native-logs.tgz`
(b453872f…).

## SCN-077: what the 10 MiB case measured, and why it is not done

The caps are gone: ACL2 authored the 10,486,094-octet ADU in 24 to 28 s and cut
it into 2,622 fragments whose bundles are at most 4 KiB; the receiver accepted
every fragment it was sent under the raised profile. The obstruction is per
arrival work:

- first attempt (eb7e469e): each arrival built a reassembly canvas as long as
  the ADU (~3.5 s). Repaired in ca8f7bf9 (no offset zero, no plan).
- second attempt (ca8f7bf9): arrivals take about 45 ms per held row: seconds
  per ten arrivals 7 at 20 held, 25 at 60, 44 at 100, 63 at 140. The family of
  2,622 projects to about 43 hours; the run was stopped after 172 arrivals.
  The growth is linear in held rows per arrival; the likely cause (inferred, not
  profiled) is `fn-bpnf-heldp`, which re-encodes each held bundle and is called
  per row by `fn-bpnf-active-fragmentp` in the selector and the active set, and
  the `*1*` guard check at each host call. That is whole-state revalidation on
  a served path (AGENTS.md).
- the first harness also blocked the receiver on a full stdout pipe after 87
  sessions (harness defect, repaired in aa7dabf1).

Work per quantum: a received transfer is decoded under min(profile bundle
octets, the transfer MRU); a held family image is encoded, framed and decoded
in one step linear in its octets (not measured at 10 MiB: the family never
completed). Bytes copied for 10 MiB: not measured.

## Assurance chain (the profile slice)

Native entry `fnn-bps-open` → `fn-bpnpf-profile-read` → the machine state's
max-jobs/max-octets (`fn-bpnpf-valid-profile-opens`); `fnn-bps-receive` →
`fn-bpnpf-admitted-receive-event` (refinement: PRF-128's answer within the
profile) → the step's held-octet check → replay's named verdict
(`fn-bpnpf-replay-past-the-octets-is-refused`) → the restart's
(`fn-bpnpf-restart-names-held-beyond-profile`) → observed: the native cases
above. The relation "every held fragment's ADU is within the profile's ADU" is
established at admission and preserved because the profile only rises; replay
does not re-check the ADU (PKT-294 item 4).

## PKT-276, retired by name

`*fn-bpa-max-octets*`, `*fn-bpb-max-input*` and `*fn-bpnf-max-held-image*` are no
longer data caps: each is a codec width at the profile ceiling, and the bounds
are the profile's ADU octets, bundle octets and held octets.

## PKT-294: found and not finished

1. **Per-arrival revalidation** (above) blocks SCN-077. Carry "every held row is
   `fn-bpnf-heldp`" as a state invariant established at receive and replay, and
   give the selector and active set an exec path that does not re-encode; the
   host's `*1*` guard check at each call must not walk the held list.
2. A general coverage precheck for families (sum of extents < total ⇒ not ready)
   so an early offset zero does not rebuild the whole canvas per arrival.
3. The sender machine's job image (`*fn-bpn-machine-max-job-octets*`, plain
   `:blob`, 131,072) caps what a node can send as one job (about 64 KiB of ADU);
   `fn-bpfs-plan` can cut a larger bundle but the job cannot hold it.
4. Replay does not re-check the ADU octets (only rows and held octets).
5. Decoding a held family image is one step linear in its octets, not a
   resumable quantum (brief item 2's resumable decoder is not done).
6. `bp-node profile` opens the journal, so it cannot raise a profile the journal
   is already past; the remedy is restoring the file (docs/operator.md says so).
7. The profile fields are capped at 2^24 by `fn-bpn-machine-limitp` (PRF-131's
   representation ceiling); widening needs the machine state's limit widened.
8. tools/run_bp_receive.py still checks a staged request ADU against 65,538.
9. The Store profile's `max-bp-rows` is still not read (PKT-276 item 2's decision).

## Not done

SCN-077 (PKT-294 item 1); the resumable bundle decoder; native bytes-copied figures.
