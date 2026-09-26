# bp-lifecycle-3 (wave 2, 2026-09-26): distinct BP exit codes, and the node's held rows in the operator's profile

Lane `lane/bp-lifecycle-3` from dev `f2d40879` (both bp-lifecycle and
harness-repair-2 merged). Brief: `build/coordinator/queue/w2-bp-lifecycle-3.txt`.
Ids: PRF-131, SCN-077, PKT-276. Model: Opus 5.5.

## What now works

- `bp send` and every BP verb answer one code per class, computed by ACL2
  from the evidence the host records (specs/host.md "BP run classes"):
  0 accepted, 1 refused, **3 fenced** (a publication's outcome is unknown:
  stop and recover, the meaning 3 has for every fn command), **6
  interrupted** (a connection lost after it existed: the job stays durable
  and the next contact re-offers it under its own identity), **7 not
  connected** (no socket: nothing left the node). Before, a lost
  connection and an uncertain Store publication both exited 3, and a
  refused port exited 0 (`bp-service`) or 3 (`bp send`).
- A BP node's held rows and held octets are the operator's profile
  (`bp-node profile JOURNAL NODE ROWS OCTETS`, raise only; default 64 rows
  and 16 MiB). SCN-067 (70 fragments across a SIGKILL) runs under a
  128-row profile instead of being skipped.
- A journal opened under a profile smaller than its rows is refused at
  replay with the named verdict `:held-beyond-profile`, never truncated.

## A decision taken against the brief's parenthetical (for the deputy)

The brief says "harness-repair-2's C1 tests keep exit 3 for the
lost-after-connect case". Keeping that makes the four cases distinct only
if the Store-uncertain fence leaves exit 3, and exit 3 is, for every fn
command, "the outcome of a publication is unknown and recovery is required
before further mutation" (specs/host.md "CLI exit codes"; docs/operator.md
"What uncertain means": stop the service and run recovery). A lost TCPCL
connection requires no recovery: the sender's durable state is certain and
RETRY or the next contact re-offers the same identity (mandate section 4,
"Uncertainty": a connection-local fault costs a connection; uncertain
shared authority fences). So the fence keeps 3 and the lost connection
moves to 6. The first cut (daf01b70) followed the brief (lost 3, fence 6);
3b40c74a swapped them. Every changed expectation names the class through a
module constant (`LOST = 6`, `NOT_CONNECTED = 7`) whose comment cites
specs/host.md "BP run classes"; no fence expectation changed.
Rejected alternative and its cost: fence 6, lost 3 would redefine 3 for six
verbs only, and an operator script that recovers on 3 would recover on
every dropped contact and miss a real BP fence at 6.

## The assurance chain

**Item 4 (run class).**
- Native entry: `fnn-bps-exit-code` (host/native/bp-service.lisp) for
  `bp-service run/resume`, `bp-contact tick`, `bp-node resume/checkpoint`,
  `bp-obligation`; `fnn-bp-exit-code` (host/native/bp.lisp) for `bp send`,
  `bp receive`, `bp-app`; the `bp-node serve` result; `fnn-bp-verb` for any
  `fnn-store-indeterminate`.
- Executed ACL2 subject: `fn-bprc-run-exit-code` over the evidence record
  `(refused failed uncertain fenced)`, built by `fn-bprc-note` from
  `fn-bprc-effect-evidence` (the `:forward-refused` arm of
  `fnn-bps-drive-effects`, :process scope), `fn-bprc-session-evidence`
  (TCPCL outcome and the new `fnn-tclc-fenced` flag, set where a Store or
  FNBS publication in the delivery callback was uncertain),
  `fn-bprc-publication-evidence` (every persist arm), and
  `fn-bprc-with-articles` (the tally's article counts).
- Refinement: `fn-bpnrc-job-result-class-is-the-transport-class`: over
  PRF-120's `fn-bpnj-named-result-is-the-transport-outcome`, the class of
  the durable answer's effects is the class of the outcome the `:requeued`
  record names (`:failed` -> not-connected, `:uncertain` -> interrupted).
- Maintained relation: the record is a `fn-bprc-countsp`; `fn-bprc-note`
  preserves it; a fence, once recorded, stays (`fn-bprc-note-keeps-a-fence`).
- Behavioural theorems: `fn-bprc-exit-code-separates-the-classes`,
  `fn-bprc-fence-is-never-masked`, `fn-bprc-connection-local-never-fences`,
  `fn-bprc-uncertain-article-fences`.
- Observed: the native modules below.

**P5 (profile).**
- Native entry: `fnn-bps-open` -> `fnn-bps-read-profile` ->
  `fn-bpnpf-read`; `fn-bpnf-initial-state config rows octets`;
  `fnn-command-bp-node-profile` -> `fn-bpnpf-write-octets`.
- Theorems: `fn-bpnpf-read-of-octets` (a saved profile opens: the frame
  carries every value the relation admits), `fn-bpnpf-read-is-valid`,
  `fn-bpnpf-valid-profile-opens` (every valid profile opens a machine with
  exactly its limits), `fn-bpnpf-write-never-lowers`,
  `fn-bpnpf-row-past-the-profile-is-named` and the keystone
  `fn-bpnpf-replay-past-the-profile-is-refused` (after any prefix that
  filled the profile, the next well-formed received row makes the whole
  `fn-bpnf-family-replay-rows-aux` answer `(:fault :held-beyond-profile)`).
  The served recovery event is `fn-bpnf-family-recover-auto-event`, built
  at `fnn-bps-open` through `fn-bpnr-recover-auto-event`.
- Work bounds that stay constants, and say so: the lifecycle-record count
  between rotations (`*fn-bpn-machine-max-records*`, 4096), the profile
  file's read bound (256 octets), the TCPCL MRUs. Every host loop that
  walks held rows in one step is bounded by the profile's rows.

## Teeth

- tests/acl2/bp-run-class-tests: the five codes; per hypothesis of the
  separation theorem a counterexample (`:bogus` collides with the fenced
  code; one class, one code) and a must-fail; the fence among mixed
  evidence and the same run without it; connection-local words and a
  non-local word that fences; over the reachable attempting state of
  PRF-120's teeth (`*jo-st-a*`, attempt 2) each outcome's class, and as
  hypothesis removals the stale attempt 1 and the pending state
  `*jo-st-p*`. The other PRF-120 hypotheses (issued, delivery-uncertain,
  fenced, token bound) are not separately witnessed here; PRF-120's teeth
  witness them for the step itself.
- tests/acl2/bp-node-host-tests: mixed article and session evidence.
- tests/acl2/bp-node-profile-tests: the 128-row round trip, a trailing
  octet and another format refused; zero rows and 2^24 + 1 rows open
  nothing, nor does a missing configuration (must-fail each); a lowering
  write refused; replay of the two durable kind-5 rows of the
  family-replay teeth under a one-row profile answers
  `(:fault :held-beyond-profile)`, under two rows `:ready` with both held,
  and a duplicate row answers another fault.

Every must-fail's search is cut short on purpose (minimal theory); the
counterexample is the assert-event before it.

## Runs

| run | rev | manifest | result |
| --- | --- | --- | --- |
| r1 `run-20260926T020523Z-5cfa` | daf01b70 | `certify-20260926T020550Z-125371.json` | green: 12 books, 0 failures, max 7.38 s (bp-node-job-offer); bp-node-run-class 5.43, bp-run-class-tests 5.58, bp-node-host-tests 5.02, bp-run-class 0.22 |
| r2 `run-20260926T021835Z-3171` | 8fe1d3b4 | `certify-20260926T021928Z-141211.json` | 71 of 73 green, max 9.59 s (tests/acl2/bp-node-forwarding-teeth-tests; bp-fnbs-family-replay 5.63, bp-fnbs-replay-append 4.68, bp-node-run-class 5.33, bp-run-class-tests 5.38, bp-node-host-tests 4.88, host/bp-node-host 4.38, bp-node-profile 1.42). Red: bp-node-profile-replay (a statement predicate over the family-replay helpers declared guard-verified; those helpers are not) and its test book. |
| r3 `run-20260926T022427Z-f4d9` | bfb8a8d7 | `certify-20260926T022448Z-148750.json` | green: bp-node-profile-replay 4.62 s, bp-node-profile-tests 4.52 s |

Every book this lane changed or added is certified at its final bytes by r2
or r3 (bfb8a8d7 changed only bp-node-profile-replay after r2). Every book
is under 10 s at two jobs.

## Native (hbox, DTN developer image, /tank/fn/scratch/bp-lifecycle-3)

Script: `bp-lifecycle-3-2026-09-26/native.sh REV` (git archive of REV,
cache install of the dtn and default roots, both developer images, then the
modules under `systemd-run --scope -p MemoryMax=24G`). /tank/fn/node was
not touched.

At 3b40c74a (the class mapping, before the expectations moved): images
`fn-host-dtn-developer` 7542bf90..., `fn-host-developer` b391d10f...
(logs-3b40c74a/IMAGE-SHA256SUMS). Every failure was an expectation of the
old mapping, classified by line:
- test_bp_service_native 14 failures (e259cf43...): the first run of each
  C1 outage test and the resumes that contact the accept-then-close peer
  again: 3 -> 6 (a connection lost after it existed); the refused-port
  case 0 -> 7. The fence expectations (corrupt clock domain, legacy
  records, name gap and token mismatch, namespace bound, visible-final
  persistence cut) stayed 3 and passed.
- test_bp_contact_native 1 (63f0f214...), test_bp_contact_relay_native 1
  (1fcb5a63...), test_bp_node_native 2 (c5f156ab...): the sender's reading
  of a peer that fenced or a relay that cut: 3 -> 6.
- test_bp_app_native 2 (311d6610...): the sender's reading 3 -> 6, and one
  implementation defect found: the receiver's refused article no longer
  reached the exit code (0 for 1), because the tally's article counts
  were not evidence. Repaired in 8fe1d3b4 (`fn-bprc-with-articles`).
- test_bp_receive_integrity_native OK 4 (64aaf748...);
  test_bp_fragment_node_native OK 3, 1 skipped (2d4faf7d...).

At bfb8a8d7 (final): images `fn-host-dtn-developer` eb607919...,
core 5c37f09e...; `fn-host-developer` 37e1a419..., core cf345cef...
(logs-bfb8a8d7/IMAGE-SHA256SUMS). Every module green:

| module | result | log SHA-256 |
| --- | --- | --- |
| test_bp_service_native | OK 17 | 8ac2a593... |
| test_bp_contact_native | OK 2 | 389dab71... |
| test_bp_contact_relay_native | OK 1 | 8280bb57... |
| test_bp_app_native | OK 4 | eedcb8b2... |
| test_bp_node_native | OK 27 | 4d0c5bc5... |
| test_bp_receive_integrity_native | OK 4 | 83b87dae... |
| test_bp_fragment_node_native | OK 4, none skipped (SCN-067: 70 fragments across a SIGKILL under a 128-row profile, and the lowering write refused with exit 1) | fc37d711... |

Both campaigns' logs: `bp-lifecycle-3-2026-09-26/native-logs.tgz`
(48f2401d962d8584ac47dcd3d2fd3aac828e2be4649cf106f13a4af470be1b97).

## PKT-171's P5 items, retired and not

- Retired: the held-row capacity `*fn-bpn-machine-max-jobs*` (64) and the
  machine's held-octet budget `*fn-bpn-machine-max-octets*` (16 MiB) are
  the node profile's fields; they remain in books/bp-node-machine.lisp only
  as the default profile.
- Not retired (PKT-276): `*fn-bpa-max-octets*` (65,538, the ADU record),
  `*fn-bpb-max-input*` (1 MiB, the bundle decoder), and
  `*fn-bpnf-max-held-image*` (131,072, one held image) are still constants.
  They sit inside the codec books (bp-adu, bp-bundle, bp-fnbs-codec and its
  invariants, bp-limits' `fn-bpn-limits-compose`) whose recognizers and
  round-trip theorems name them; moving them is the codec half of P5 and
  was not started here.

## PKT-276: what this lane found and did not finish

1. **SCN-077 (10 MiB through 4 KiB fragments) is blocked**, in order, by
   the sender's ADU record (`*fn-bpa-max-octets*` 65,538), the bundle
   decoder (`*fn-bpb-max-input*` 1 MiB) and the held image of the
   reassembled bundle (`*fn-bpnf-max-held-image*` 131,072); the Store's
   article bound is the operator's already (P1). Held rows and octets no
   longer block it. Default recommendation: PKT-171's (the ADU record
   admits the profile's A, the bundle bound becomes a profile field, and
   kind 18 hands the ADU to the application in chunks rather than as one
   held image). Affected: bp-adu, bp-bundle, bp-fnbs-codec(-invariants),
   bp-fnbs-family-codec, bp-node-foundation, bp-node-fragment-plan,
   bp-node-receive-boundary, bp-limits.
2. **The Store profile's `max-bp-rows` field is not read.** The node's
   profile lives in the FNBS journal because `bp-service` and `bp-contact`
   run with no Store. Decision for ember: whether a `bp-node serve` with a
   Store should take its rows from the Store profile (one number for the
   operator) or keep the journal's (one number per journal). Default: keep
   the journal's and retire the Store field, since the Store never holds
   BP rows. Nothing else waits on it.
3. **The run class does not separate expiry, no-route, busy delivery or a
   clock-domain change** (mandate section 9's joins). Today expiry and
   no-route are 0 with the reason on stdout, a busy delivery is 0, and a
   clock-domain fence is 3 like any fence. Each is a further evidence word
   and class; the evidence record makes that additive.
4. **Replay's named verdict covers the served family replay only.** The
   older folds `fn-bpnf-replay-rows` (bp-fnbs-replay) and
   `fn-bpah-replay-rows` (bp-fnbs-delivery-replay) still answer
   `:kind-five-row` at the bound; neither is on the served recovery path
   (`fn-bpnf-family-recover-auto-event` is).
5. `bp decode` keeps its article-verdict codes (0, 1, 3); an article whose
   lifetime the clock cannot decide is 3 there.
6. No native case yet opens a journal whose rows exceed its profile (the
   ACL2 teeth witness the verdict on real kind-5 frames).

## Not done

- The codec half of P5 (item 1 above) and so SCN-077.
- A native `held-beyond-profile` case (item 6).
